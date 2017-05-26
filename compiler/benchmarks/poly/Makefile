POLYC = polyc
MLTON = mlton

SRCS = $(wildcard *.sml)

PROGSP = $(patsubst %.sml,polyc_%,$(SRCS))
PROGSM = $(patsubst %.sml,mlton_%,$(SRCS))

all: $(PROGSP) $(PROGSM)

polyc_% : %.sml
	$(POLYC) -o $@ $<

mlton_% : %.sml
	(sed '2d;1d;$$d' $< > temp.sml);cat temp.sml;	$(MLTON) -output $@ temp.sml ; rm temp.sml

clean:
	rm $(PROGSP) $(PROGSM)
