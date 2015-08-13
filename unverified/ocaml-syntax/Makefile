FILES = typedOCamlToCakeML formatted

all: $(FILES)

clean:
	rm -f *.cmi *.cmx *.o $(FILES)

typedOCamlToCakeML:
	ocamlfind opt -o typedOCamlToCakeML -package compiler-libs.common -package batteries -linkpkg preprocessor.ml typedOCamlToCakeML.ml

formatted:
	ocamlfind opt -o formatted -package compiler-libs.common -package batteries -linkpkg preprocessor.ml formatDecl.ml formatted.ml

.PHONY: all clean
