(*
  Definition of a compiler from Scheme to CakeML
*)
Theory scheme_compiler
Ancestors
  fromSexp simpleSexpParse scheme_ast scheme_parsing
  scheme_to_cake
Libs
  preamble

Definition cake_prog_to_string_def:
  cake_prog_to_string ast =
    print_sexp (listsexp (MAP decsexp ast))
End

Definition cake_for_err_def:
  cake_for_err err_msg =
    let err_str_ast = Lit (StrLit err_msg) in
      cake_prog_to_string (cake_print (err_str_ast))
End

Definition compile_def:
  compile (s:string) =
    case parse_to_ast s of
    | INL err_str => cake_for_err ("PARSE ERROR: " ++ err_str ++ "\n")
    | INR ast =>
      (case static_scope_check ast of
      | INL err_str => cake_for_err ("TYPE ERROR: " ++ err_str ++ "\n")
      | INR ast' =>
       (case codegen ast of
        | INL err_str => cake_for_err ("CODEGEN ERROR: " ++ err_str ++ "\n")
        | INR cake_prog => cake_prog_to_string cake_prog))
End

Definition main_function_def:
  main_function s = implode (compile (explode s))
End

