(*
  Encoding program for testing
*)
open preamble basis miscTheory set_sepTheory listTheory lispProgTheory;
open (* for parsing: *) parsingTheory source_valuesTheory;

val _ = new_theory "testProg";

val _ = translation_extends "lispProg";

val _ = show_assums := true;


Definition main_function_def:
  main_function (s:mlstring) = List [strlit "test output: "; s]
End

val res = translate main_function_def;

val _ = type_of “main_function” = “:mlstring -> mlstring app_list”
        orelse failwith "The main_function has the wrong type.";

val main = process_topdecs
  `print_app_list (main_function (TextIO.inputAll TextIO.stdIn));`;

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand

Definition test_prog_def:
  test_prog = ^prog
End

val _ = export_theory();
