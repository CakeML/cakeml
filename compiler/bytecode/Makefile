BytecodeScript.sml : bytecode.lem
	lem -hol_lib ../lib.lem -hol bytecode.lem &&\
sed -i 's/Pmap \$$ map/fmap/g' $@ &&\
sed -i 's/LEAST/$$LEAST/g' $@ &&\
sed -i '4 i val _ = intLib.deprecate_int();' $@
