CompileScript.sml : compile.lem ../lib.lem lib.lem ../semantics/miniML.lem bytecode/bytecode.lem
	lem -extra_level auto -hol_lib ../lib.lem -hol_lib lib.lem ../semantics/miniML.lem bytecode/bytecode.lem -hol compile.lem && rm -f MiniMLScript.sml BytecodeScript.sml &&\
sed -i 's/LEAST/$$LEAST/g' $@ &&\
sed -i 's/DOMSUB/$$\\\\/g' $@ &&\
sed -i '5 i open alistTheory state_transformerTheory' $@
