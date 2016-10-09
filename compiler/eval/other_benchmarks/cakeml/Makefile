CC = gcc
RISCVCC = riscv64-unknown-elf-gcc

SRCS = $(wildcard *.S)

RISCVPROGS = $(patsubst riscv_%.S,cake_riscv_%,$(SRCS))

all: $(RISCVPROGS)

cake_riscv_% : riscv_%.S
	$(RISCVCC) $< ffi.c -g -o $@

clean:
	rm $(RISCVPROGS)
