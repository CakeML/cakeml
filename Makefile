semantics/MiniMLScript.sml print_ast/Print_astScript.sml semantics/TokensScript.sml: lib.lem print_ast/print_ast.lem semantics/miniML.lem semantics/tokens.lem
	lem -hol_lib lib.lem -hol semantics/tokens.lem semantics/miniML.lem print_ast/print_ast.lem
	mv Print_astScript.sml print_ast/
	mv MiniMLScript.sml semantics/
	mv TokensScript.sml semantics/

clean:
	rm -f Print_astScript.sml MiniMLScript.sml TokensScript.sml print_ast/Print_astScript.sml semantics/MiniMLScript.sml semantics/TokensScript.sml
