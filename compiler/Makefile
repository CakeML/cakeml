CompileScript.sml : compile.lem lib.lem ../semantics/hol_lib.lem ../semantics/lib.lem ../semantics/ast.lem ../semantics/semanticPrimitives.lem ../semantics/smallStep.lem ../semantics/bigStep.lem bytecode/bytecode.lem
	lem -extra_level auto -hol_lib lib.lem -hol_lib ../semantics/hol_lib.lem \
		-i ../semantics/lib.lem -i ../semantics/ast.lem -i ../semantics/semanticPrimitives.lem -i ../semantics/smallStep.lem -i ../semantics/bigStep.lem \
		-i bytecode/bytecode.lem -hol compile.lem &&\
sed -i 's/LEAST/$$LEAST/g' $@ &&\
sed -i 's/some/$$some/g' $@ &&\
sed -i 's/DOMSUB/$$\\\\/g' $@ &&\
sed -i '5 i open alistTheory state_transformerTheory' $@
