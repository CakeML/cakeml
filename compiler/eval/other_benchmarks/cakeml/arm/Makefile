CC = gcc

SRCS = $(wildcard *.S)

PROGS = $(patsubst %.S,cake_arm_%,$(SRCS))

all: arm

arm : $(PROGS)

cake_arm_% : %.S
	$(CC) $< ../ffi.c -g -o $@

clean:
	rm $(PROGS)
