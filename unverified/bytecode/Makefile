YACC = bison
LEX = flex
CFLAGS = -O2 -Wall -pedantic -std=c99
#CFLAGS = -g -Wall -pedantic -std=c99
CC = gcc

all: cakeml-byte

lex.yy.c: bytecode.lex
	$(LEX) -o lex.yy.c bytecode.lex

bytecode.tab.c bytecode.tab.h: bytecode.yacc
	$(YACC) -d bytecode.yacc -o bytecode.tab.c

main.o: bytecode_inst.h main.c
	$(CC) $(CFLAGS) -c -o main.o main.c

bytecode.tab.o: bytecode.tab.c
	$(CC) $(CFLAGS) -c -o bytecode.tab.o bytecode.tab.c

decode.o: decode.c
	$(CC) $(CFLAGS) -c -o decode.o decode.c

lex.yy.o: lex.yy.c
	$(CC) $(CFLAGS) -c -o lex.yy.o lex.yy.c

cakeml-byte: main.o bytecode.tab.o lex.yy.o decode.o
	$(CC) $(CFLAGS) -o cakeml-byte lex.yy.o bytecode.tab.o decode.o main.o

clean:
	\rm -f lex.yy.c bytecode.tab.c bytecode.tab.h *.o cakeml-byte

dep: lex.yy.c bytecode.tab.c
	makedepend *.c

