package main

import (
	"flag"
	"fmt"
	"go/ast"
	"go/token"
	"math/big"
	"os"

	"golang.org/x/tools/go/exact"
	"golang.org/x/tools/go/loader"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
	"golang.org/x/tools/go/types"
)

var nodetype types.Type
var opfield int

var fieldstouched []big.Int
var names []string

var printDeductions = flag.Bool("deduce", false, "print various deductions based on constraints")
var printTypes = flag.Bool("types", false, "print final types")

func main() {
	flag.Parse()
	lconf := loader.Config{}
	lconf.Import("cmd/compile")
	lprog, err := lconf.Load()
	if err != nil {
		fatalln(err)
	}
	sprog := ssautil.CreateProgram(lprog, 0)
	sprog.BuildAll()
	findNodeType(sprog, lprog)
	var consts []*constraint
	for f := range ssautil.AllFunctions(sprog) {
		for _, b := range f.Blocks {
			for _, i := range b.Instrs {
				consts = generateConstraints(i, consts)
			}
		}
	}

	for _, c := range consts {
		findFieldAccesses(c)
	}
	if *printDeductions {
		for _, c := range consts {
			if len(c.accesses) == 0 {
				continue
			}
			fmt.Printf("%s\n", names[c.op])
			fmt.Printf("%s\n", lprog.Fset.Position(c.bound.Pos()))
			for _, a := range c.accesses {
				fmt.Printf("\t%s:%s\n", lprog.Fset.Position(a.Pos()), a.String())
			}
		}
	}
	if *printTypes {
		for _, c := range consts {
			set := &fieldstouched[c.op]
			for _, a := range c.accesses {

				findex := 0
				switch f := a.(type) {
				case *ssa.FieldAddr:
					findex = f.Field
				case *ssa.Field:
					findex = f.Field
				default:
					panic("not field or fieldaddr")
				}
				set.SetBit(set, findex, 1)
			}
		}
		for i, f := range fieldstouched {
			fmt.Printf("%s\n", names[i])
			printFields(&f)
		}
	}
}

func printFields(b *big.Int) {
	blen := b.BitLen()
	structtype := nodetype.Underlying().(*types.Struct)
	for i := 0; i < blen; i++ {
		if b.Bit(i) == 1 {
			fmt.Printf("\t%s\n", structtype.Field(i).Name())
		}
	}
}

func generateConstraints(i ssa.Instruction, consts []*constraint) []*constraint {
	switch field := i.(type) {
	case *ssa.Field:
		if field.X.Type() != nodetype || field.Field != opfield {
			return consts
		}
		for _, r := range *field.Referrers() {
			consts = findJumpsOnCmp(r, field, field.X, consts)
		}
	case *ssa.FieldAddr:
		if field.X.Type().Underlying().(*types.Pointer).Elem() != nodetype || field.Field != opfield {
			return consts
		}
		for _, r := range *field.Referrers() {
			if load, ok := r.(*ssa.UnOp); ok && load.Op == token.MUL {
				for _, r := range *load.Referrers() {
					consts = findJumpsOnCmp(r, load, field.X, consts)
				}
			}
			if store, ok := r.(*ssa.Store); ok {
				constval, _ := store.Val.(*ssa.Const)
				if constval == nil {
					continue
				}
				val := constval.Int64()
				consts = append(consts, &constraint{
					val:       field.X,
					op:        int(val),
					typedFrom: store.Block(),
					bound:     store,
				})
			}
		}
	}
	return consts
}

func findJumpsOnCmp(instr ssa.Instruction, load ssa.Value, base ssa.Value, consts []*constraint) []*constraint {
	binop := toCmp(instr)
	if binop == nil {
		return consts
	}
	op := binop.X
	if binop.X == load {
		op = binop.Y
	}
	constval, _ := op.(*ssa.Const)
	if constval == nil {
		return consts
	}
	val := constval.Int64()
	for _, r := range *binop.Referrers() {
		if jmp, _ := r.(*ssa.If); jmp != nil {
			bb := jmp.Block()
			var tblock *ssa.BasicBlock
			tblock = bb.Succs[0]
			if binop.Op == token.NEQ {
				tblock = bb.Succs[1]
			}
			if !bb.Dominates(tblock) {
				continue
			}
			consts = append(consts, &constraint{
				val:       base,
				op:        int(val),
				typedFrom: tblock,
				bound:     load.(ssa.Instruction),
			})
		}
	}
	return consts
}

func toCmp(r ssa.Instruction) *ssa.BinOp {
	binop, ok := r.(*ssa.BinOp)
	if !ok {
		return nil
	}
	if !isBoolean(binop.Type()) {
		return nil
	}
	if binop.Op != token.EQL && binop.Op != token.NEQ {
		return nil
	}
	return binop
}

func isBoolean(t types.Type) bool {
	tb, _ := t.Underlying().(*types.Basic)
	return tb != nil && tb.Kind() == types.Bool
}

type constraint struct {
	val       ssa.Value
	op        int
	typedFrom *ssa.BasicBlock
	bound     ssa.Instruction
	accesses  []ssa.Value
}

func findFieldAccesses(c *constraint) {
	for _, r := range *c.val.Referrers() {
		switch f := r.(type) {
		case *ssa.Field:
			if f.Field == opfield {
				continue
			}
		case *ssa.FieldAddr:
			if f.Field == opfield {
				continue
			}
		default:
			continue
		}
		if !c.typedFrom.Dominates(r.Block()) {
			continue
		}
		c.accesses = append(c.accesses, r.(ssa.Value))
	}
}

func findNodeType(sprog *ssa.Program, lprog *loader.Program) {
	pkg := sprog.ImportedPackage("cmd/compile/internal/gc")
	if pkg == nil {
		fatalln("could not find cmd/compile/internal/gc in ssa")
	}
	obj := pkg.Type("Node")
	if obj == nil {
		fatalln("could not find Node in ssa")
	}
	typ := obj.Type()
	structtype := typ.Underlying().(*types.Struct)
	numFields := structtype.NumFields()

	lpkg := lprog.Package("cmd/compile/internal/gc")

	cspecs := findTypeConsts(lpkg.Files)
	fieldstouched = make([]big.Int, len(cspecs))
	names = make([]string, len(cspecs))
	for _, s := range cspecs {
		decl := s.(*ast.ValueSpec)
		val, _ := exact.Int64Val(lpkg.Info.Defs[decl.Names[0]].(*types.Const).Val())
		names[val] = decl.Names[0].Name
	}

	for i := 0; i < numFields; i++ {
		f := structtype.Field(i)
		if f.Name() == "Op" {
			nodetype = typ
			opfield = i
			return
		}
	}
	fatalln("could not find Op field")
}

func findTypeConsts(files []*ast.File) []ast.Spec {
	for _, f := range files {
		for _, d := range f.Decls {
			gd, ok := d.(*ast.GenDecl)
			if !ok || gd.Tok != token.CONST {
				continue
			}
			decl := gd.Specs[0].(*ast.ValueSpec)
			if decl.Names[0].Name == "OXXX" {
				return gd.Specs
			}
		}
	}
	fatalln("could not find type consts")
	panic("unreachable")
}

func fatalf(s string, i ...interface{}) {
	fmt.Fprintf(os.Stdout, s, i...)
	os.Exit(1)
}
func fatalln(i ...interface{}) {
	fmt.Fprintln(os.Stdout, i...)
	os.Exit(1)
}
