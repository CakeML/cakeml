LEM_SOURCES = ../lib.lem ../semantics/ffi/ffi.lem ../semantics/ast.lem ../semantics/semanticPrimitives.lem ../semantics/typeSystem.lem

reference.pdf: reference.tex #lem-generated
	latexmk -pdf -shell-escape reference.tex

lem-generated: $(LEM_SOURCES)
	-mkdir lem-generated
	lem -tex -outdir lem-generated $(LEM_SOURCES)

clean:
	rm -rf lem-generated _minted-reference
	latexmk -C
