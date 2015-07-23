FILES = boyer fib

all: $(FILES)

$(FILES):
	ocamlfind opt -o $@ $@.ml
	../ocaml2cakeml $@.ml > $@.cml

clean:
	rm -f *.cmi *.cmx *.o *.cml $(FILES)
