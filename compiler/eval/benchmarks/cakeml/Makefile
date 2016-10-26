CC = gcc

SRCS = $(wildcard *.S)

PROGS = $(patsubst %.S,cake_%,$(SRCS))

all: $(PROGS)

cake_% : %.S
	$(CC) $< ffi.c -g -o $@

clean:
	rm $(PROGS)
