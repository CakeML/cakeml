CompileScript.sml : compile.lem ../semantics/lib.lem lib.lem ../semantics/miniML.lem bytecode/bytecode.lem
	lem -hol_lib ../semantics/lib.lem -hol_lib lib.lem ../semantics/miniML.lem bytecode/bytecode.lem -hol compile.lem && rm -f MiniMLScript.sml BytecodeScript.sml &&\
sed -i '/datatype/N;/sum = INL/d' $@ &&\
sed -i 's/Pmap \$$ map/fmap/g' $@ &&\
sed -i 's/LEAST/$$LEAST/g' $@ &&\
sed -i 's/(o_f)/($$o_f)/g' $@ &&\
sed -i 's/DOMSUB/$$\\\\/g' $@ &&\
sed -i 's/Hol \$$ Lib \$$ //g' $@ &&\
sed -i '/(\* Syntax \*)/,/(\* Semantics \*)/d' $@ &&\
sed -i '4 i open alistTheory CexpTypesTheory; val _ = intLib.deprecate_int();' $@
