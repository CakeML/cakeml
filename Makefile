semantics/MiniMLScript.sml print_ast/Print_astScript.sml semantics/TokensScript.sml semantics/AstScript.sml: lib.lem print_ast/print_ast.lem semantics/miniML.lem semantics/tokens.lem semantics/ast.lem
	lem -hol_lib lib.lem -hol semantics/tokens.lem semantics/miniML.lem semantics/ast.lem print_ast/print_ast.lem
	mv Print_astScript.sml print_ast/
	mv MiniMLScript.sml semantics/
	mv TokensScript.sml semantics/
	mv AstScript.sml semantics/

clean:
	rm -f Print_astScript.sml MiniMLScript.sml TokensScript.sml print_ast/Print_astScript.sml semantics/MiniMLScript.sml semantics/TokensScript.sml semantics/AstScript.sml

test:
	cd compiler/emit; Holmake && ./selftest.exe
	cd compiler/correctness; Holmake
	cd hol-light; Holmake
