package main

import (
	"fmt"
	"os"

	"golang.org/x/tools/go/loader"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
	"golang.org/x/tools/go/types"
)

func main() {
	lconf := loader.Config{}
	lconf.Import("cmd/compile")
	lprog, err := lconf.Load()
	if err != nil {
		fatalln(err)
	}
	sprog := ssautil.CreateProgram(lprog, 0)
	sprog.BuildAll()
	nodtyp := findNodeType(sprog)

}

func findNodeType(sprog *ssa.Program) types.Type {
	pkg := sprog.ImportedPackage("cmd/compile/internal/gc")
	if pkg == nil {
		fatalln("could not find cmd/compile/internal/gc in ssa")
	}
	typ := pkg.Type("Node")
	if pkg == nil {
		fatalln("could not find Node in ssa")
	}
	return typ.Type()
}

func fatalf(s string, i ...interface{}) {
	fmt.Fprintf(os.Stdout, s, i...)
	os.Exit(1)
}
func fatalln(i ...interface{}) {
	fmt.Fprintln(os.Stdout, i...)
	os.Exit(1)
}
