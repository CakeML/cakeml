FILES = $(basename $(wildcard *.ml))

all: $(FILES)

$(FILES): ../ocaml2cakeml $(addsuffix .ml, $(FILES))
	ocamlfind opt -o $@ $@.ml
	../ocaml2cakeml $@.ml > $@.cml
	[ -f $@-patch ] && ./$@-patch || :
	! grep -E "^Error:" $@.cml

clean:
	rm -f *.cmi *.cmx *.o *.cml *.out $(FILES)

TESTS = $(addsuffix .out, $(FILES))
CAKE = ~/cakeml-v1-beta/cake

%.out: %.cml % $(CAKE)
	cat $< | $(CAKE) > $@
	grep "error>" $@ || echo "Success"

test: $(TESTS) all

.PHONY: all clean test
