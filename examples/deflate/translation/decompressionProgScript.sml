(*
  Encoding program for simple decompression
*)
open preamble basis miscTheory set_sepTheory listTheory lispProgTheory;
open compressionTheory;
open (* for parsing: *) parsingTheory source_valuesTheory;

val _ = new_theory "decompressionProg";

val _ = translation_extends "lispProg";

val _ = show_assums := true;

val res = translate TAKE;
val res = translate DROP;

val res = translate ALOOKUP_SND_def;
val res = translate KEYLEN_def;
val res = translate decompr_def;

Definition parse_input_def:
  parse_input s = (explode s, [("xxxx", "b"); ("YYYYYY", "fg"); ("123", "e")] )
End

Definition main_function_def:
  main_function (s:mlstring) =
  let
    (text, tab) = parse_input s;
  in
    List [implode (decompr text tab)]
End

EVAL “main_function (implode "b")”;


val res = translate parse_input_def;
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

Definition decompression_prog_def:
  decompression_prog = ^prog
End

val _ = export_theory();
