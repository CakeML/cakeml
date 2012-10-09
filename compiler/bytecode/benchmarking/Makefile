
NAME = bytecode_tester

all: 
	date '+#define NOW "%Y-%m-%d %H:%M:%S"' > wrapper.h
	gcc -O1 wrapper.c asm_exec.s -o $(NAME)
	/bin/rm -f wrapper.h

clean:
	/bin/rm -fR *.dSYM $(NAME)
