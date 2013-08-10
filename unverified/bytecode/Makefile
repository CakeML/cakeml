YACC = bison
LEX = flex
CFLAGS = -g -Wall
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


# DO NOT DELETE

bytecode.tab.o: /usr/include/stdio.h /usr/include/_types.h
bytecode.tab.o: /usr/include/sys/_types.h /usr/include/sys/cdefs.h
bytecode.tab.o: /usr/include/machine/_types.h /usr/include/i386/_types.h
bytecode.tab.o: /usr/include/secure/_stdio.h /usr/include/secure/_common.h
bytecode.tab.o: /usr/include/stdlib.h /usr/include/Availability.h
bytecode.tab.o: /usr/include/AvailabilityInternal.h /usr/include/sys/wait.h
bytecode.tab.o: /usr/include/sys/signal.h /usr/include/sys/appleapiopts.h
bytecode.tab.o: /usr/include/machine/signal.h /usr/include/i386/signal.h
bytecode.tab.o: /usr/include/i386/_structs.h /usr/include/sys/_structs.h
bytecode.tab.o: /usr/include/machine/_structs.h /usr/include/sys/resource.h
bytecode.tab.o: /usr/include/machine/endian.h /usr/include/i386/endian.h
bytecode.tab.o: /usr/include/sys/_endian.h
bytecode.tab.o: /usr/include/libkern/_OSByteOrder.h
bytecode.tab.o: /usr/include/libkern/i386/_OSByteOrder.h
bytecode.tab.o: /usr/include/alloca.h /usr/include/machine/types.h
bytecode.tab.o: /usr/include/i386/types.h bytecode_inst.h
bytecode.tab.o: /usr/include/limits.h /usr/include/machine/limits.h
bytecode.tab.o: /usr/include/i386/limits.h /usr/include/i386/_limits.h
bytecode.tab.o: /usr/include/sys/syslimits.h /usr/include/stddef.h
decode.o: /usr/include/stdlib.h /usr/include/Availability.h
decode.o: /usr/include/AvailabilityInternal.h /usr/include/_types.h
decode.o: /usr/include/sys/_types.h /usr/include/sys/cdefs.h
decode.o: /usr/include/machine/_types.h /usr/include/i386/_types.h
decode.o: /usr/include/sys/wait.h /usr/include/sys/signal.h
decode.o: /usr/include/sys/appleapiopts.h /usr/include/machine/signal.h
decode.o: /usr/include/i386/signal.h /usr/include/i386/_structs.h
decode.o: /usr/include/sys/_structs.h /usr/include/machine/_structs.h
decode.o: /usr/include/sys/resource.h /usr/include/machine/endian.h
decode.o: /usr/include/i386/endian.h /usr/include/sys/_endian.h
decode.o: /usr/include/libkern/_OSByteOrder.h
decode.o: /usr/include/libkern/i386/_OSByteOrder.h /usr/include/alloca.h
decode.o: /usr/include/machine/types.h /usr/include/i386/types.h
decode.o: /usr/include/stdio.h /usr/include/secure/_stdio.h
decode.o: /usr/include/secure/_common.h /usr/include/inttypes.h
decode.o: /usr/include/stdint.h bytecode_inst.h /usr/include/limits.h
decode.o: /usr/include/machine/limits.h /usr/include/i386/limits.h
decode.o: /usr/include/i386/_limits.h /usr/include/sys/syslimits.h
lex.yy.o: /usr/include/stdio.h /usr/include/_types.h
lex.yy.o: /usr/include/sys/_types.h /usr/include/sys/cdefs.h
lex.yy.o: /usr/include/machine/_types.h /usr/include/i386/_types.h
lex.yy.o: /usr/include/secure/_stdio.h /usr/include/secure/_common.h
lex.yy.o: /usr/include/string.h /usr/include/secure/_string.h
lex.yy.o: /usr/include/errno.h /usr/include/sys/errno.h /usr/include/stdlib.h
lex.yy.o: /usr/include/Availability.h /usr/include/AvailabilityInternal.h
lex.yy.o: /usr/include/sys/wait.h /usr/include/sys/signal.h
lex.yy.o: /usr/include/sys/appleapiopts.h /usr/include/machine/signal.h
lex.yy.o: /usr/include/i386/signal.h /usr/include/i386/_structs.h
lex.yy.o: /usr/include/sys/_structs.h /usr/include/machine/_structs.h
lex.yy.o: /usr/include/sys/resource.h /usr/include/machine/endian.h
lex.yy.o: /usr/include/i386/endian.h /usr/include/sys/_endian.h
lex.yy.o: /usr/include/libkern/_OSByteOrder.h
lex.yy.o: /usr/include/libkern/i386/_OSByteOrder.h /usr/include/alloca.h
lex.yy.o: /usr/include/machine/types.h /usr/include/i386/types.h
lex.yy.o: bytecode.tab.h /usr/include/unistd.h /usr/include/sys/unistd.h
lex.yy.o: /usr/include/sys/select.h /usr/include/sys/_select.h
main.o: /usr/include/stdio.h /usr/include/_types.h /usr/include/sys/_types.h
main.o: /usr/include/sys/cdefs.h /usr/include/machine/_types.h
main.o: /usr/include/i386/_types.h /usr/include/secure/_stdio.h
main.o: /usr/include/secure/_common.h /usr/include/string.h
main.o: /usr/include/secure/_string.h /usr/include/stdlib.h
main.o: /usr/include/Availability.h /usr/include/AvailabilityInternal.h
main.o: /usr/include/sys/wait.h /usr/include/sys/signal.h
main.o: /usr/include/sys/appleapiopts.h /usr/include/machine/signal.h
main.o: /usr/include/i386/signal.h /usr/include/i386/_structs.h
main.o: /usr/include/sys/_structs.h /usr/include/machine/_structs.h
main.o: /usr/include/sys/resource.h /usr/include/machine/endian.h
main.o: /usr/include/i386/endian.h /usr/include/sys/_endian.h
main.o: /usr/include/libkern/_OSByteOrder.h
main.o: /usr/include/libkern/i386/_OSByteOrder.h /usr/include/alloca.h
main.o: /usr/include/machine/types.h /usr/include/i386/types.h
main.o: /usr/include/assert.h bytecode_inst.h /usr/include/limits.h
main.o: /usr/include/machine/limits.h /usr/include/i386/limits.h
main.o: /usr/include/i386/_limits.h /usr/include/sys/syslimits.h
