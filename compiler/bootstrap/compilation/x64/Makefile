# This Makefile produces the CakeML compiler executable by linking the
# bootstrapped CakeML compiler with the implementation of the FFI primitives.
# It also includes rules for compiling CakeML programs with the CakeML compiler
# then similarly linking the resulting machine code with the FFI primitives to
# produce executables. It is designed to work on GNU/Linux, macOS, and Windows.

# To set the stack and heap sizes for CakeML programs, set the
# CML_STACK_SIZE and CML_HEAP_SIZE environment variables (or see basis_ffi.c)
# The unit of measure for both arguments is mebibytes (1024 * 1024 bytes).

OS ?= $(shell uname)

ifeq ($(OS),Windows_NT)
	PREF =
	SUFF = .exe
	EVALFLAG =
else
	PREF = ./
	SUFF =
	EVALFLAG = -DEVAL
endif

ifeq ($(OS),Darwin)
	# These options avoid linker warnings on macOS
	LDFLAGS += -Wl,-no_pie
endif

CFLAGS+=-O2
LDLIBS+=-lm
CMLS = $(wildcard *.cml)
CML_PROGS = $(patsubst %.cml,%.cake$(SUFF),$(CMLS))

# Links the CakeML compiler and compiles all the .cml files in this directory
all: cake$(SUFF)

# Linking the CakeML compiler

ifeq ($(OS),Darwin)
# The REPL writes freshly compiled code into the code buffer, which follows the
# compiler's code. macOS arm64 never lets __TEXT become writable, so the
# compiler's code (not the C code) is moved into its own segment, __CAKE,
# which is linked read/write/execute. basis_ffi.c makes it read/execute at
# startup and only makes pages writable while installing code.
cake: cake.S basis_ffi.c
	$(CC) $(CFLAGS) $(EVALFLAG) -c $< -o cake.o
	ld -r -rename_section __TEXT __text __CAKE __text cake.o -o cake_seg.o
	$(CC) $(CFLAGS) cake_seg.o basis_ffi.c $(LOADLIBES) $(EVALFLAG) -o $@ $(LDFLAGS) -Wl,-segprot,__CAKE,rwx,rwx $(LDLIBS)
	$(RM) cake.o cake_seg.o
else
cake$(SUFF): cake.S basis_ffi.c
	$(CC) $(CFLAGS) $< basis_ffi.c $(LOADLIBES) $(EVALFLAG) -o $@ $(LDFLAGS) $(LDLIBS)
endif

# The sexpr files used in the example rules below are included in the
# 64-bit compiler release packages.

# *UNVERIFIED* build with GC and stage tracing; regenerating the .S will take
# about five minutes

cake_verbose$(SUFF): cake-sexpr-64 basis_ffi.c cake$(SUFF)
	CML_STACK_SIZE=1000 CML_HEAP_SIZE=6000 $(PREF)cake$(SUFF) --sexp=true --exclude_prelude=true --skip_type_inference=true --emit_empty_ffi=true --reg_alg=0 < $< > $<.S
	$(CC) $(CFLAGS) -DDEBUG_FFI -o $@ $<.S basis_ffi.c $(LDFLAGS) $(LDLIBS)

# *UNVERIFIED* build of the compiler supporting 32-bit targets

cake_unverified32$(SUFF): cake-sexpr-32 basis_ffi.c cake$(SUFF)
	CML_STACK_SIZE=1000 CML_HEAP_SIZE=6000 $(PREF)cake$(SUFF) --sexp=true --exclude_prelude=true --skip_type_inference=true --reg_alg=0 < $< > $<.S
	$(CC) $(CFLAGS) -o $@ $<.S basis_ffi.c $(LDFLAGS) $(LDLIBS)

# Example of cross-compiling the compiler itself
RISCV_CC ?= riscv64-unknown-linux-gnu-cc
cake_riscv_host: cake-sexpr-64 basis_ffi.c cake$(SUFF)
	CML_STACK_SIZE=1000 CML_HEAP_SIZE=6000 $(PREF)cake$(SUFF) --sexp=true --exclude_prelude=true --skip_type_inference=true --target=riscv --reg_alg=0 < $< > $<.riscv.S
	$(RISCV_CC) $(CFLAGS) -o $@ $<.riscv.S basis_ffi.c $(LDFLAGS) $(LDLIBS)

# Using the CakeML compiler

# The conventions used here for extensions, namely,
# *.cml          # CakeML source program
# *.cake.S       # CakeML-generated machine-code
# *.cake$(SUFF)  # CakeML-generated executable
# are not required in general when using CakeML.
# (They are not used here for the compiler itself.)

%.cake.S : %.cml cake$(SUFF)
	$(PREF)cake$(SUFF) $(CAKEFLAGS) <$< >$@

%.cake$(SUFF) : %.cake.S basis_ffi.c
	$(CC) $< basis_ffi.c $(LOADLIBES) $(LDLIBS) -o $@ $(LDFLAGS) $(LDLIBS)

clean:
	$(RM) basis_ffi.o cake.o cake_seg.o cake$(SUFF) *.cake.o *.cake.S *.cake$(SUFF)
