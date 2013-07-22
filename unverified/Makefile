SOURCES = ast.hs lex.hs main.hs parse.hs tokens.hs typecheck.hs unify.hs

cakeml_uv: $(SOURCES)
	ghc --make Main -o cakeml_uv

clean:
	rm -f *.o *.hi cakeml_uv

