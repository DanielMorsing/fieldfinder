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

var printDeductions = flag.Bool("deduce", false, "print various deductions based on constraints")
var printTypes = flag.Bool("types", false, "print final types")

type context struct {
	loaderprog    *loader.Program
	ssaprog       *ssa.Program
	constraints   []*constraint
	nodetype      types.Type
	opField       int
	opNames       []string
	fieldsTouched []big.Int
}

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
	ctx := &context{
		loaderprog: lprog,
		ssaprog:    sprog,
	}
	ctx.findNodeType()
	for f := range ssautil.AllFunctions(sprog) {
		for _, b := range f.Blocks {
			for _, i := range b.Instrs {
				ctx.generateConstraints(i)
			}
		}
	}

	for _, c := range ctx.constraints {
		ctx.findFieldAccesses(c)
	}
	if *printDeductions {
		for _, c := range ctx.constraints {
			if len(c.accesses) == 0 {
				continue
			}
			fmt.Printf("%s\n", ctx.opNames[c.op])
			fmt.Printf("%s\n", lprog.Fset.Position(c.bound.Pos()))
			for _, a := range c.accesses {
				fmt.Printf("\t%s:%s\n", lprog.Fset.Position(a.Pos()), a.String())
			}
		}
	}
	if *printTypes {
		for _, c := range ctx.constraints {
			set := &ctx.fieldsTouched[c.op]
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
		for i, f := range ctx.fieldsTouched {
			fmt.Printf("%s\n", ctx.opNames[i])
			ctx.printFields(&f)
		}
	}
}

func (ctx *context) findNodeType() {
	lpkg := ctx.loaderprog.Package("cmd/compile/internal/gc")
	typ := lpkg.Pkg.Scope().Lookup("Node").(*types.TypeName).Type()
	structtype := typ.Underlying().(*types.Struct)
	numFields := structtype.NumFields()
	for i := 0; i < numFields; i++ {
		f := structtype.Field(i)
		if f.Name() == "Op" {
			ctx.nodetype = typ
			ctx.opField = i
			break
		}
	}

	cspecs := findTypeConsts(lpkg.Files)
	ctx.fieldsTouched = make([]big.Int, len(cspecs))
	ctx.opNames = make([]string, len(cspecs))
	for _, s := range cspecs {
		decl := s.(*ast.ValueSpec)
		val, _ := exact.Int64Val(lpkg.Info.Defs[decl.Names[0]].(*types.Const).Val())
		ctx.opNames[val] = decl.Names[0].Name
	}
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

func (ctx *context) printFields(b *big.Int) {
	blen := b.BitLen()
	structtype := ctx.nodetype.Underlying().(*types.Struct)
	for i := 0; i < blen; i++ {
		if b.Bit(i) == 1 {
			fmt.Printf("\t%s\n", structtype.Field(i).Name())
		}
	}
}

type constraint struct {
	val       ssa.Value
	op        int
	typedFrom *ssa.BasicBlock
	bound     ssa.Instruction
	accesses  []ssa.Value
}

func (ctx *context) generateConstraints(i ssa.Instruction) {
	switch field := i.(type) {
	case *ssa.Field:
		if field.X.Type() != ctx.nodetype || field.Field != ctx.opField {
			return
		}
		for _, r := range *field.Referrers() {
			ctx.findJumpsOnCmp(r, field, field.X)
		}
	case *ssa.FieldAddr:
		if field.X.Type().Underlying().(*types.Pointer).Elem() != ctx.nodetype || field.Field != ctx.opField {
			return
		}
		for _, r := range *field.Referrers() {
			if load, ok := r.(*ssa.UnOp); ok && load.Op == token.MUL {
				for _, r := range *load.Referrers() {
					ctx.findJumpsOnCmp(r, load, field.X)
				}
			}
			if store, ok := r.(*ssa.Store); ok {
				constval, _ := store.Val.(*ssa.Const)
				if constval == nil {
					continue
				}
				val := constval.Int64()
				ctx.constraints = append(ctx.constraints, &constraint{
					val:       field.X,
					op:        int(val),
					typedFrom: store.Block(),
					bound:     store,
				})
			}
		}
	}
}

func (ctx *context) findJumpsOnCmp(instr ssa.Instruction, load ssa.Value, base ssa.Value) {
	binop := toCmp(instr)
	if binop == nil {
		return
	}
	op := binop.X
	if binop.X == load {
		op = binop.Y
	}
	constval, _ := op.(*ssa.Const)
	if constval == nil {
		return
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
			ctx.constraints = append(ctx.constraints, &constraint{
				val:       base,
				op:        int(val),
				typedFrom: tblock,
				bound:     load.(ssa.Instruction),
			})
		}
	}
	return
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

func (ctx *context) findFieldAccesses(c *constraint) {
	for _, r := range *c.val.Referrers() {
		switch f := r.(type) {
		case *ssa.Field:
			if f.Field == ctx.opField {
				continue
			}
		case *ssa.FieldAddr:
			if f.Field == ctx.opField {
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

func fatalf(s string, i ...interface{}) {
	fmt.Fprintf(os.Stdout, s, i...)
	os.Exit(1)
}
func fatalln(i ...interface{}) {
	fmt.Fprintln(os.Stdout, i...)
	os.Exit(1)
}
