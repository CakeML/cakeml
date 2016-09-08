POLYC = polyc

SRCS = $(wildcard *.sml)

PROGS = $(patsubst %.sml,polyc_%,$(SRCS))

all: $(PROGS)

polyc_% : %.sml
	$(POLYC) -o $@ $<

clean:
	rm $(PROGS)
