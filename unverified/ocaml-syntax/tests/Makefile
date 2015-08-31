#FILES = boyer countGraphs fib
FILES = $(basename $(wildcard *.ml))

all: $(FILES)

$(FILES): ../ocaml2cakeml
	ocamlfind opt -o $@ $@.ml
	../ocaml2cakeml $@.ml > $@.cml
	[ -f $@-patch ] && ./$@-patch || :

clean:
	rm -f *.cmi *.cmx *.o *.cml *.out $(FILES)

TESTS = $(addsuffix .out, $(FILES))
CAKE = ~/cakeml-v1-beta/cake

%.out: %.cml $(CAKE)
	cat $< | $(CAKE) > $@
	grep "error>" $@ || echo "Success"

%.cml: ../ocaml2cakeml
	../ocaml2cakeml $@.ml > $@.cml
	grep -E "^Error:" $@.cml
	[ -f $@-patch ] && ./$@-patch || :

test: $(TESTS) all
