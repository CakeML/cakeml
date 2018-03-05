CP ?= cp
CC ?= gcc
CAKECC = cakemlc

FLAGS = -g -o
BMS = $(wildcard *.sml)

BM_PROGS_O4 = $(patsubst %.sml,cake_O4_%,$(BMS))

ASM_PROGS = $(patsubst %.sml,%.S,$(BMS))

all: $(CAKECC) benchmarks

$(CAKECC) : cake.S basis_ffi.c
	$(CC) $< basis_ffi.c $(FLAGS) $(CAKECC)

benchmarks : $(BM_PROGS_O4)

cake_O4_% : %.sml
	./$(CAKECC) < $(basename $<).sml > $(basename $<).S
	$(CC) $(basename $<).S basis_ffi.c $(FLAGS) $@

clean:
	rm $(BM_PROGS_O4) $(ASM_PROGS) $(CAKECC)
