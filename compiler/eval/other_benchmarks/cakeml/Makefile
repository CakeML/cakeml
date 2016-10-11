CC = gcc
RISCVCC = riscv64-unknown-elf-gcc
MIPSCC = mips-linux-gnu-gcc-4.4 

SRCS = $(wildcard *.S)

RISCVPROGS = $(patsubst riscv_%.S,cake_riscv_%,$(SRCS))
ARM6PROGS = $(patsubst arm_%.S,cake_arm_%,$(SRCS))
ARM8PROGS = $(patsubst arm8_%.S,cake_arm8_%,$(SRCS))
X64PROGS = $(patsubst x64_%.S,cake_x64_%,$(SRCS))
MIPSPROGS = $(patsubst mips_%.S,cake_mips_%,$(SRCS))

riscv : $(RISCVPROGS)

arm6 : $(ARM6PROGS)

arm8 : $(ARM8PROGS)

x64 : $(X64PROGS)

mips : $(MIPSPROGS)

cake_riscv_% : riscv_%.S
	$(RISCVCC) $< ffi.c -g -o $@

cake_arm_% : arm_%.S
	$(CC) $< ffi.c -g -o $@

cake_arm8_% : arm8_%.S
	$(CC) $< ffi.c -g -o $@

cake_x64_% : x64_%.S
	$(CC) $< ffi.c -g -o $@

cake_mips_% : mips_%.S
	$(MIPSCC) $< ffi.c -g -o $@

clean:
	rm $(RISCVPROGS) $(ARM6PROGS) $(ARM8PROGS) $(X64PROGS) $(MIPSPROGS)
