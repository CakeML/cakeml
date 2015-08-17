FILES = typedOCamlToCakeML formatted

all: $(FILES)

clean:
	rm -f *.cmi *.cmx *.o $(FILES)

typedOCamlToCakeML: preprocessor.ml typedOCamlToCakeML.ml
	ocamlfind opt -o typedOCamlToCakeML -package compiler-libs.common -package batteries -linkpkg preprocessor.ml typedOCamlToCakeML.ml
	touch ocaml2cakeml

formatted: preprocessor.ml formatDecl.ml formatted.ml
	ocamlfind opt -o formatted -package compiler-libs.common -package batteries -linkpkg preprocessor.ml formatDecl.ml formatted.ml
	touch ocaml2cakeml

.PHONY: all clean
