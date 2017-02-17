CC = gcc

FLAGS = -static -g -o
SRCS = $(wildcard *.S)

PROGS = $(patsubst %.S,cake_%,$(SRCS))

all: $(PROGS)

cake_% : %.S
	$(CC) $< ../../../compiler/bootstrap/io/io_ffi.c $(FLAGS) $@

clean:
	rm $(PROGS)
