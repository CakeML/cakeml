MLTON = mlton
MOSMLC = mosmlc

SRCS = $(wildcard *.sml)

PROGSM = $(patsubst %.sml,mlton_%,$(SRCS))
PROGSMINF = $(patsubst %.sml,mlton_intinf_%,$(SRCS))
PROGSMOS = $(patsubst %.sml,mosml_%,$(SRCS))

all: $(PROGSM) $(PROGSMINF) $(PROGSMOS)

mlton_% : %.sml
	$(MLTON) -output $@ $<

mlton_intinf_% : %.sml
	$(MLTON) -default-type intinf -output $@ $<

mosml_% : %.sml
	- $(MOSMLC) -orthodox -standalone -toplevel -o $@ $<

clean:
	$(RM) mlton_* mlton_intif_* mosml_* *.ui *.uo
