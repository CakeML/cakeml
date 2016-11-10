CC = riscv64-unknown-elf-gcc

SRCS = $(wildcard *.S)

PROGS = $(patsubst %.S,cake_riscv_%,$(SRCS))

all: riscv

riscv : $(PROGS)

cake_riscv_% : %.S
	$(CC) $< ../ffi.c -g -o $@

clean:
	rm $(PROGS)
