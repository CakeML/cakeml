
LEM_SOURCES = ast semanticPrimitives bigStep typeSystem

lems:
	-mkdir lem-generated
	lem -tex -outdir lem-generated $(patsubst %,../semantics/%.lem,$(LEM_SOURCES))
