# To support large stack+heap, use -mcmodel=medium.
# CFLAGS += -mcmodel=medium

# To set the stack and heap available to the CakeML compiler,
# also edit the .space directives in cake.S.

# To set the stack and heap directives available to your own
# CakeML programs, use the --stack_size and --heap_size
# command-line arguments to the CakeML compiler. The unit of
# measure for both arguments is mebibytes (1024 * 1024 bytes).

UNAME_S := $(shell uname -s)

ifeq ($(UNAME_S),Darwin)
  EXTRA_FLAGS = -Wl,-no_pie
else
  EXTRA_FLAGS =
endif

# Build the CakeML compiler

cake: cake.o basis_ffi.o
	$(CC) $(CPPFLAGS) $(EXTRA_FLAGS) $< basis_ffi.o -o $@

# General rules for applying the CakeML compiler
# The options "-Wl,-no_pie" are to avoid linker warnings on Mac

%.cake.S : %.cml cake
	./cake $(CAKEFLAGS) <$< >$@

%.cake : %.cake.S
	$(CC) $(CPPFLAGS) $(EXTRA_FLAGS) $< basis_ffi.o -o $@

# Build the sexpr printed compiler.
# This may fail if heap/stack isn't set sufficiently high.
bootstrap.S: cake-sexpr-x64-32 cake
	./cake --sexp=true --exclude_prelude=true --skip_type_inference=true --emit_empty_ffi=true <$< >$@

bootstrap: bootstrap.o basis_ffi.o

clean:
	rm -f cake basis_ffi.o result.o cake.o result result.S bootstrap.S bootstrap.o bootstrap
