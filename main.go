package main

import (
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

var fieldstouched = make([]big.Int, 300)
var names = make([]string, 300)

func main() {
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
	for i, b := range fieldstouched {
		fmt.Printf("%s\n", names[i])
		printFields(&b)
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
}

func findFieldAccesses(c *constraint) {
	set := &fieldstouched[c.op]
	for _, r := range *c.val.Referrers() {
		findex := 0
		switch f := r.(type) {
		case *ssa.Field:
			findex = f.Field
			if f.Field == opfield {
				continue
			}
		case *ssa.FieldAddr:
			findex = f.Field
			if f.Field == opfield {
				continue
			}
		default:
			continue
		}
		if !c.typedFrom.Dominates(r.Block()) {
			continue
		}
		set.SetBit(set, findex, 1)
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
	for _, f := range lpkg.Files {
		for _, d := range f.Decls {
			gd, ok := d.(*ast.GenDecl)
			if !ok || gd.Tok != token.CONST {
				continue
			}
			decl := gd.Specs[0].(*ast.ValueSpec)
			if decl.Names[0].Name != "OXXX" {
				continue
			}
			var val int64
			for _, s := range gd.Specs {
				decl := s.(*ast.ValueSpec)
				val, _ = exact.Int64Val(lpkg.Info.Defs[decl.Names[0]].(*types.Const).Val())
				names[val] = decl.Names[0].Name
			}
			fieldstouched = fieldstouched[:val]
			names = names[:val]
		}
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

func fatalf(s string, i ...interface{}) {
	fmt.Fprintf(os.Stdout, s, i...)
	os.Exit(1)
}
func fatalln(i ...interface{}) {
	fmt.Fprintln(os.Stdout, i...)
	os.Exit(1)
}
