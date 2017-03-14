CC = gcc

SRCS = $(wildcard *.S)

PROGS = $(patsubst %.S,cake_%,$(SRCS))

all: x64

x64 : $(PROGS)

cake_% : %.S
	$(CC) $< ../../../basis/basis_ffi.o -static -o $@

clean:
	rm $(PROGS)
