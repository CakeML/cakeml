OCAMLC = ocamlc
OCAMLOPT = ocamlopt

SRCS = $(wildcard *.ml)

PROGSC = $(patsubst %.ml,ocamlc_%,$(SRCS))
PROGSO = $(patsubst %.ml,ocamlopt_%,$(SRCS))

all: $(PROGSC) $(PROGSO)

ocamlc_% : %.ml
	- $(OCAMLC) -o $@ $<

ocamlopt_% : %.ml
	- $(OCAMLOPT) -o $@ $<

clean:
	$(RM) $(PROGSC) $(PROGSO) *.cmo *.cmx *.cmi *.o
