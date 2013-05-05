CompileScript.sml : hol_lib.lem ../semantics/hol_lib.lem ../semantics/lib.lem ../semantics/ast.lem ../semantics/semanticPrimitives.lem bytecode/compilerLib.lem bytecode/bytecode.lem compilerPrimitives.lem intLang.lem toIntLang.lem compile.lem
	lem -extra_level auto -hol_lib hol_lib.lem -hol_lib ../semantics/hol_lib.lem\
		-i ../semantics/lib.lem -i ../semantics/ast.lem -i ../semantics/semanticPrimitives.lem\
		-i bytecode/compilerLib.lem -i bytecode/bytecode.lem\
		-hol compilerPrimitives.lem -hol intLang.lem -hol toIntLang.lem -hol compile.lem &&\
sed -i '5 i open alistTheory' $@
