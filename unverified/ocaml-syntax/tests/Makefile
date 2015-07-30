FILES = boyer countGraphs fib

all: $(FILES)

$(FILES):
	ocamlfind opt -o $@ $@.ml
	../ocaml2cakeml $@.ml > $@.cml
	[ -f $@-patch ] && ./$@-patch || :

clean:
	rm -f *.cmi *.cmx *.o *.cml $(FILES)
