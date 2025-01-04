all: hi.cake$(SUFF)
.PHONY: all clean

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

CAKEOPT = --sexp=true

ifeq ($(OS),Darwin)
	# These options avoid linker warnings on macOS
	LDFLAGS += -Wl,-no_pie
	EVALFLAG =
endif

CFLAGS+=-O2
LDLIBS+=-lm

ARCH=x64
WORD_SIZE=64

%.cake.S: %.scm cake scheme_compiler$(SUFF)
	cat $< | $(PREF)scheme_compiler$(SUFF) | $(PREF)cake$(SUFF) $(CAKEOPT) > $@

%.cake$(SUFF) : %.cake.S ../../../basis/basis_ffi.c
	$(CC) $< ../../../basis/basis_ffi.c $(LOADLIBES) $(LDLIBS) -o $@ $(LDFLAGS)

scheme_compiler.S: ../compilation/scheme_compiler.S
	cp $< $@

scheme_compiler$(SUFF): scheme_compiler.S ../../../basis/basis_ffi.c
	$(CC) -o $@ scheme_compiler.S ../../../basis/basis_ffi.c $(LDLIBS)

cake.S:
	@if [ ! -f "../../bootstrap/compilation/x64/64/$(@F)" ] ; then $(MAKE) download ; else cp ../../bootstrap/compilation/x64/64/$(@F) $@ ; fi

download:
	@echo "$(red)Could not find \`cake.S\`. Downloading the latest version from CakeML's GitHub releases.$(reset)"
	curl -LO https://github.com/CakeML/cakeml/releases/latest/download/cake-$(ARCH)-$(WORD_SIZE).tar.gz
	@tar -zxf cake-$(ARCH)-$(WORD_SIZE).tar.gz --strip-components 1 cake-$(ARCH)-$(WORD_SIZE)/cake.S
	@rm cake-$(ARCH)-$(WORD_SIZE).tar.gz

cake$(SUFF): cake.S ../../../basis/basis_ffi.c
	$(CC) $(CFLAGS) $< ../../../basis/basis_ffi.c $(LOADLIBES) $(EVALFLAG) -o $@ $(LDFLAGS) $(LDLIBS)

clean:
	rm cake$(SUFF) cake.S scheme_compiler$(SUFF) scheme_compiler.S *.cake.S *.cake$(SUFF)
