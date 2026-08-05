(*
  Define a simple program as functions in HOL
*)
Theory example_funs
Ancestors
  misc mlstring

Definition main_function_def:
  main_function (s:mlstring) =
    implode (REVERSE (explode s))
End
