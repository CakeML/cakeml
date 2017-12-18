CP ?= cp
CC ?= gcc
CAKECC = cake
CAKE_PREFIX ?= cake_
PATH_PREFIX ?= .
CAKE_FLAGS ?=
FLAGS ?= -g -o
BMS = $(wildcard *.sml)

BM_PROGS = $(patsubst %.sml,$(CAKE_PREFIX)%,$(BMS))

ASM_PROGS = $(patsubst %.sml,%.S,$(BMS))

all: benchmarks

cake.S : ../../../bootstrap/compilation/x64/64/cake.S
	$(CP) $< $@

basis_ffi.c : ../../../../basis/basis_ffi.c
	$(CP) $< $@

compiler : cake.S basis_ffi.c
	$(CC) $< basis_ffi.c $(FLAGS) $(CAKECC)

benchmarks : $(BM_PROGS)

$(CAKE_PREFIX)% : %.sml
	./$(CAKECC) $(CAKE_FLAGS) < $(basename $<).sml > $(basename $<).S
	$(CC) $(basename $<).S basis_ffi.c $(FLAGS) $(PATH_PREFIX)/$@

clean:
	rm $(BM_PROGS) $(ASM_PROGS)
