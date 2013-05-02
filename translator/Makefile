LEM_DEPS = ../semantics/lib.lem ../semantics/tokens.lem ../semantics/ast.lem

LEM_SOURCES = print_ast.lem

HOL_SOURCES = Print_astScript.sml

$(HOL_SOURCES): $(LEM_SOURCES) ../semantics/hol_lib.lem $(LEM_DEPS)
	lem -hol_lib ../semantics/hol_lib.lem $(addprefix -i ,$(LEM_DEPS)) -hol $(LEM_SOURCES)
	rm -f *ExtraScript.sml

clean:
	Holmake cleanAll
	rm -f $(HOL_SOURCES) *ExtraScript.sml

