CC = gcc

SRCS = $(wildcard *.S)

PROGS = $(patsubst %.S,cake_x64_%,$(SRCS))

all: x64

x64 : $(PROGS)

cake_x64_% : %.S
	$(CC) $< ../ffi.c -g -o $@

clean:
	rm $(PROGS)
