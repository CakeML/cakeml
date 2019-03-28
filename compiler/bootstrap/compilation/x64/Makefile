# This Makefile produces the CakeML compiler executable by linking the
# bootstrapped CakeML compiler with the implementation of the FFI primitives.
# It also includes rules for compiling CakeML programs with the CakeML compiler
# then similarly linking the resulting machine code with the FFI primitives to
# produce executables. It is designed to work on GNU/Linux, macOS, and Windows.

# To set the stack and heap sizes for CakeML programs, use the
# --stack_size and --heap_size arguments to the CakeML compiler
# (provided on the command line or in the CAKEFLAGS variable). The unit of
# measure for both arguments is mebibytes (1024 * 1024 bytes).

# To set the stack and heap sizes for the CakeML compiler itself, edit the
# .space directives in cake.S.

# To support large stack and heap sizes, use -mcmodel=medium or -mcmodel=large.
# For example:
# CFLAGS += -mcmodel=medium

OS ?= $(shell uname)

ifeq ($(OS),Windows_NT)
	PREF =
	SUFF = .exe
else
	PREF = ./
	SUFF =
endif

ifeq ($(OS),Darwin)
	# These options avoid linker warnings on macOS
	LDFLAGS += -Wl,-no_pie
endif

CMLS = $(wildcard *.cml)
CML_PROGS = $(patsubst %.cml,%.cake$(SUFF),$(CMLS))

# Links the CakeML compiler and compiles all the .cml files in this directory
all: cake$(SUFF) $(CML_PROGS)

# Linking the CakeML compiler

cake$(SUFF): cake.o basis_ffi.o
	$(CC) $(LDFLAGS) $< basis_ffi.o $(LOADLIBES) $(LDLIBS) -o $@

# Using the CakeML compiler

# The conventions used here for extensions, namely,
# *.cml          # CakeML source program
# *.cake.S       # CakeML-generated machine-code
# *.cake$(SUFF)  # CakeML-generated executable
# are not required in general when using CakeML.
# (They are not used here for the compiler itself.)

%.cake.S : %.cml cake$(SUFF)
	$(PREF)cake$(SUFF) $(CAKEFLAGS) <$< >$@

%.cake$(SUFF) : %.cake.S basis_ffi.o
	$(CC) $(LDFLAGS) $< basis_ffi.o $(LOADLIBES) $(LDLIBS) -o $@

clean:
	$(RM) basis_ffi.o cake.o cake$(SUFF) *.cake.o *.cake.S *.cake$(SUFF)
