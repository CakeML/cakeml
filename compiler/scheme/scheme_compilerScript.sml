(*
  Definition of a compiler from Scheme to CakeML
*)
open preamble;
open fromSexpTheory simpleSexpParseTheory;
open scheme_astTheory
     scheme_parsingTheory
     scheme_to_cakeTheory;

val _ = new_theory "scheme_compiler";

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
       (case codegen ast of
        | INL err_str => cake_for_err ("CODEGEN ERROR: " ++ err_str ++ "\n")
        | INR cake_prog => cake_prog_to_string cake_prog)
End

(*
EVAL “compile "(print hi)"”
*)

Definition main_function_def:
  main_function s = implode (compile (explode s))
End

val _ = export_theory();
