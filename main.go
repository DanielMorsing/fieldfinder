package main

import (
	"fmt"
	"go/token"
	_ "math/big"
	"os"

	"golang.org/x/tools/go/loader"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
	"golang.org/x/tools/go/types"
)

var nodetype types.Type
var opfield int
var numFields int

func main() {
	lconf := loader.Config{}
	lconf.Import("cmd/compile")
	lprog, err := lconf.Load()
	if err != nil {
		fatalln(err)
	}
	sprog := ssautil.CreateProgram(lprog, 0)
	sprog.BuildAll()
	findNodeType(sprog)
	var consts []*constraint
	for f := range ssautil.AllFunctions(sprog) {
		for _, b := range f.Blocks {
			for _, i := range b.Instrs {
				consts = generateConstraints(i, consts)
			}
		}
	}
	c := consts[0]
	dumpFields(c)
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
	if binop.X != load {
		op = binop.Y
	}
	for _, r := range *binop.Referrers() {
		if jmp, _ := r.(*ssa.If); jmp != nil {
			bb := jmp.Block()
			var tblock *ssa.BasicBlock
			tblock = bb.Succs[0]
			if binop.Op == token.NEQ {
				tblock = bb.Succs[1]
			}
			consts = append(consts, &constraint{
				val:       base,
				op:        op,
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
	op        ssa.Value
	typedFrom *ssa.BasicBlock
}

func dumpFields(c *constraint) {
}

func findNodeType(sprog *ssa.Program) {
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
	numFields = structtype.NumFields()

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
