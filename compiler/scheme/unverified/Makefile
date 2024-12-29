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

cake-$(ARCH)-$(WORD_SIZE).tar.gz:
	curl -LO https://github.com/CakeML/cakeml/releases/latest/download/cake-$(ARCH)-$(WORD_SIZE).tar.gz

lib/cake.S: cake-$(ARCH)-$(WORD_SIZE).tar.gz
	@mkdir -p $(@D)
	@tar -zxf cake-$(ARCH)-$(WORD_SIZE).tar.gz --directory $(@D) --strip-components 1 cake-x64-64/$(F@)

lib/cake: lib/cake.S ../../../basis/basis_ffi.c
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $^ $(LOADLIBES) $(EVALFLAG) -o $@ $(LDFLAGS) $(LDLIBS)

clean:
	rm -rf lib cake-$(ARCH)-$(WORD_SIZE).tar.gz *.cake.S *.cake
