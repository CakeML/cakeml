HOLLIGHT ?= $(HOME)/hol-light

ast:
	ocamlopt -c ast.ml

ocamltop_j:
	exec ocamlmktop -o $@ -I +camlp5 nums.cma unix.cma camlp5o.cma $(HOLLIGHT)/pa_j.cmo
