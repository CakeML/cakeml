CC = gcc

SRCS = $(wildcard *.S)

PROGS = $(patsubst %.S,cake_mips_%,$(SRCS))

all: mips

mips : $(PROGS)

cake_mips_% : %.S
	$(CC) $< ../ffi.c -g -o $@

clean:
	rm $(PROGS)
