(*
  Translate HOL functions into CakeML code
*)
Theory example_funsProg
Ancestors
  misc example_funs
Libs
  preamble basis

val _ = translation_extends "basisProg";

val res = translate main_function_def;

val _ = type_of “main_function” = “:mlstring -> mlstring”
        orelse failwith "The main_function has the wrong type.";

Quote main = cakeml:
  print (main_function (TextIO.inputAll (TextIO.openStdIn ())));
End

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand

Definition example_funs_prog_def:
  example_funs_prog = ^prog
End
