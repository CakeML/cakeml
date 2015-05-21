all:
	gcc wrapper.c -Wno-implicit-function-declaration -o cake
zip:
	/bin/rm -f cakeml-v1.zip
	zip -r cakeml-v1.zip Makefile wrapper.c asm_code.s
