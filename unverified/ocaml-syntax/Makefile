FILES = formatted

all: $(FILES)

clean:
	rm -f *.cmi *.cmx *.o $(FILES)

formatted: preprocessor.ml formatDecl.ml formatted.ml
	ocamlfind opt -o formatted -package compiler-libs.common -package batteries -linkpkg patternZipper.ml preprocessor.ml formatDecl.ml formatted.ml
	touch ocaml2cakeml

.PHONY: all clean
