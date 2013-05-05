CompileScript.sml : compile.lem hol_lib.lem ../semantics/hol_lib.lem ../semantics/lib.lem ../semantics/ast.lem ../semantics/semanticPrimitives.lem ../semantics/smallStep.lem ../semantics/bigStep.lem bytecode/compilerLib.lem bytecode/bytecode.lem
	lem -extra_level auto -hol_lib hol_lib.lem -hol_lib ../semantics/hol_lib.lem \
		-i ../semantics/lib.lem -i ../semantics/ast.lem -i ../semantics/semanticPrimitives.lem -i ../semantics/smallStep.lem -i ../semantics/bigStep.lem \
		-i bytecode/compilerLib.lem -i bytecode/bytecode.lem -hol compile.lem &&\
sed -i '5 i open alistTheory' $@
