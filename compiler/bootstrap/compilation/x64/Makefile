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
	EVALFLAG =
endif

CMLS = $(wildcard *.cml)
CML_PROGS = $(patsubst %.cml,%.cake$(SUFF),$(CMLS))

# Links the CakeML compiler and compiles all the .cml files in this directory
all: cake$(SUFF)

# Linking the CakeML compiler

cake$(SUFF): cake.S basis_ffi.c
	$(CC) $(LDFLAGS) $< basis_ffi.c $(LOADLIBES) $(LDLIBS) $(EVALFLAG) -o $@

# Note: While this Makefile is shared the sexpr files used in the example rules
# below are only included in the verified cake-x64-64.tar.gz release package

# *UNVERIFIED* build with GC and stage tracing; regenerating the .S will take
# about five minutes

cake_verbose$(SUFF): cake-sexpr-64 basis_ffi.c cake$(SUFF)
	CML_STACK_SIZE=1000 CML_HEAP_SIZE=6000 $(PREF)cake$(SUFF) --sexp=true --exclude_prelude=true --skip_type_inference=true --emit_empty_ffi=true --reg_alg=0 < $< > $<.S
	$(CC) $(CFLAGS) $(LDFLAGS) -DDEBUG_FFI -o $@ $<.S basis_ffi.c

# *UNVERIFIED* compiler supporting 32-bit targets; see cake-x64-32.tar.gz for a
# verified compiler

cake_unverified32$(SUFF): cake-sexpr-32 basis_ffi.c cake$(SUFF)
	CML_STACK_SIZE=1000 CML_HEAP_SIZE=6000 $(PREF)cake$(SUFF) --sexp=true --exclude_prelude=true --skip_type_inference=true --reg_alg=0 < $< > $<.S
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $<.S basis_ffi.c

# Example of cross-compiling the compiler itself
RISCV_CC ?= riscv64-unknown-linux-gnu-cc
cake_riscv_host: cake-sexpr-64 basis_ffi.c cake$(SUFF)
	CML_STACK_SIZE=1000 CML_HEAP_SIZE=6000 $(PREF)cake$(SUFF) --sexp=true --exclude_prelude=true --skip_type_inference=true --target=riscv --reg_alg=0 < $< > $<.riscv.S
	$(RISCV_CC) $(CFLAGS) $(LDFLAGS) -o $@ $<.riscv.S basis_ffi.c

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
	$(CC) $(LDFLAGS) $< basis_ffi.c $(LOADLIBES) $(LDLIBS) -o $@

clean:
	$(RM) basis_ffi.o cake.o cake$(SUFF) *.cake.o *.cake.S *.cake$(SUFF)
