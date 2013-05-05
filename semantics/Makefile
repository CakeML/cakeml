LEM_SOURCES = lib.lem tokens.lem ast.lem elab.lem semanticPrimitives.lem smallStep.lem bigStep.lem typeSystem.lem altBigStep.lem

HOL_SOURCES = LibScript.sml TokensScript.sml AstScript.sml ElabScript.sml SemanticPrimitivesScript.sml SmallStepScript.sml BigStepScript.sml TypeSystemScript.sml AltBigStepScript.sml

$(HOL_SOURCES): $(LEM_SOURCES) hol_lib.lem
	lem -hol_lib hol_lib.lem -hol $(LEM_SOURCES)
	rm -f *ExtraScript.sml

clean:
	Holmake cleanAll
	rm -f $(HOL_SOURCES) *ExtraScript.sml
