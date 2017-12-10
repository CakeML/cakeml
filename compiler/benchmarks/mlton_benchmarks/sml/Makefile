MLTON = mlton

SRCS = $(wildcard *.sml)

PROGSM = $(patsubst %.sml,mlton_%,$(SRCS))
PROGSMINF = $(patsubst %.sml,mlton_intinf_%,$(SRCS))

all: $(PROGSM) $(PROGSMINF)

mlton_% : %.sml
	$(MLTON) -output $@ $<

mlton_intinf_% : %.sml
	$(MLTON) -default-type intinf -output $@ $<

clean:
	rm $(PROGSM) $(PROGSMINF)
