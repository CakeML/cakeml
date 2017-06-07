CC = gcc
CAKECC = cakemlc

FLAGS = -g -o
BMS = $(wildcard *.sml)

BM_PROGS_O0 = $(patsubst %.sml,cake_O0_%,$(BMS))
BM_PROGS_O1 = $(patsubst %.sml,cake_O1_%,$(BMS))
BM_PROGS_O2 = $(patsubst %.sml,cake_O2_%,$(BMS))
BM_PROGS_O3 = $(patsubst %.sml,cake_O3_%,$(BMS))
BM_PROGS_O4 = $(patsubst %.sml,cake_O4_%,$(BMS))

ASM_PROGS = $(patsubst %.sml,%.S,$(BMS))

all: compiler benchmarks

compiler : cake.S
	$(CC) $< basis_ffi.c $(FLAGS) $(CAKECC)

benchmarks : $(BM_PROGS_O4)

cake_O0_% : %.sml
	./$(CAKECC) --no_multi --no_known --no_call --no_remove < $(basename $<).sml > $(basename $<).S
	$(CC) $(basename $<).S basis_ffi.c $(FLAGS) $@

cake_O1_% : %.sml
	./$(CAKECC) --no_known --no_call --no_remove < $(basename $<).sml > $(basename $<).S
	$(CC) $(basename $<).S basis_ffi.c $(FLAGS) $@

cake_O2_% : %.sml
	./$(CAKECC) --no_call --no_remove < $(basename $<).sml > $(basename $<).S
	$(CC) $(basename $<).S basis_ffi.c $(FLAGS) $@

cake_O3_% : %.sml
	./$(CAKECC) --no_remove < $(basename $<).sml > $(basename $<).S
	$(CC) $(basename $<).S basis_ffi.c $(FLAGS) $@

cake_O4_% : %.sml
	./$(CAKECC) --max_app=10 < $(basename $<).sml > $(basename $<).S
	$(CC) $(basename $<).S basis_ffi.c $(FLAGS) $@

clean:
	rm $(BM_PROGS_O0) $(BM_PROGS_O1) $(BM_PROGS_O2) $(BM_PROGS_O3) $(BM_PROGS_O4) $(ASM_PROGS) $(CAKECC)
