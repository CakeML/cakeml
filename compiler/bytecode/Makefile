BytecodeScript.sml : bytecode.lem
	lem -extra_level auto -hol_lib ../hol_lib.lem -hol compilerLib.lem -hol $< &&\
sed -i 's/LEAST/$$LEAST/g' $@
