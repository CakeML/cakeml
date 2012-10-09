semantics/MiniMLScript.sml print_ast/Print_astScript.sml: lib.lem print_ast/print_ast.lem semantics/miniML.lem
	lem -hol_lib lib.lem -hol semantics/miniML.lem print_ast/print_ast.lem
	mv Print_astScript.sml print_ast/
	mv MiniMLScript.sml semantics/

clean:
	rm -f Print_astScript.sml MiniMLScript.sml print_ast/Print_astScript.sml semantics/MiniMLScript.sml
