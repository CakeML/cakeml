all: lib/scheme_interpreter lib/unverified_scheme_compiler
.PHONY: all clean

%.cake.S: %.scm lib/cake lib/unverified_scheme_compiler
	cat $< | ./lib/unverified_scheme_compiler | ./lib/cake $(CAKEOPT) > $@

%.cake: %.cake.S ../../../basis/basis_ffi.c
	$(CC) $^ $(LOADLIBES) $(LDLIBS) -o $@ $(LDFLAGS)

lib/scheme_interpreter: Interpreter.hs Scheme.hs
lib/unverified_scheme_compiler: Compiler.hs Scheme.hs
lib/scheme_interpreter lib/unverified_scheme_compiler:
	@mkdir -p $(@D)
	ghc $^ -main-is $(basename $<) -outputdir lib -o $@

CFLAGS+=-O2
LDLIBS+=-lm

ARCH=x64
WORD_SIZE=64

lib/cake.S:
	@mkdir -p $(@D)
	@if [ ! -f "../../bootstrap/compilation/x64/64/$(@F)" ] ; then $(MAKE) download ; else cp ../../bootstrap/compilation/x64/64/$(@F) $@ ; fi

download:
	@echo "$(red)Could not find \`cake.S\`. Downloading the latest version from CakeML's GitHub releases.$(reset)"
	curl -LO https://github.com/CakeML/cakeml/releases/latest/download/cake-$(ARCH)-$(WORD_SIZE).tar.gz
	@tar -zxf cake-$(ARCH)-$(WORD_SIZE).tar.gz -C lib --strip-components 1 cake-$(ARCH)-$(WORD_SIZE)/cake.S
	@rm cake-$(ARCH)-$(WORD_SIZE).tar.gz

lib/cake: lib/cake.S ../../../basis/basis_ffi.c
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $^ $(LOADLIBES) $(EVALFLAG) -o $@ $(LDFLAGS) $(LDLIBS)

clean:
	rm -rf lib *.cake.S *.cake
