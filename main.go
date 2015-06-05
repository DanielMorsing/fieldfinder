package main

import (
	"fmt"
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
	for _, c := range consts {
		findFieldAccesses(c)
	}
	for i, b := range fieldstouched {
		fmt.Printf("%d\n", i)
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
	val, _ := exact.Int64Val(constval.Value)
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
	blocks := make(map[*ssa.BasicBlock]bool)
	blocks[c.typedFrom] = true
	blockAdded := true
	for blockAdded {
		blockAdded = false
		for bb := range blocks {
			for _, s := range bb.Succs {
				if !blocks[s] {
					blocks[s] = true
					blockAdded = true
				}
			}
		}
	}
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
		if !blocks[r.Block()] {
			continue
		}
		set.SetBit(set, findex, 1)
	}
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
	numFields := structtype.NumFields()
	fieldstouched = make([]big.Int, 300)

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
