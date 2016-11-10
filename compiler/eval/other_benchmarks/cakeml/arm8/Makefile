CC = gcc

SRCS = $(wildcard *.S)

PROGS = $(patsubst %.S,cake_arm8_%,$(SRCS))

all: arm8

arm8 : $(PROGS)

cake_arm8_% : %.S
	$(CC) $< ../ffi.c -g -o $@

clean:
	rm $(PROGS)
