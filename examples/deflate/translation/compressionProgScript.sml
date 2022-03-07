(*
  Encoding program for simple compression
*)
open preamble basis miscTheory set_sepTheory listTheory lispProgTheory arithmeticTheory numposrepTheory;
open compressionTheory;
open (* for parsing: *) parsingTheory source_valuesTheory;

val _ = new_theory "compressionProg";

val _ = translation_extends "lispProg";

val _ = show_assums := true;

val res = translate TAKE;
val res = translate DROP;
val res = translate LENGTH;

val res = translate ml_translatorTheory.MEMBER_def;
val res = translate (nub_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate FLAT;
val res = translate SNOC;
val res = translate GENLIST;
val res = translate DIV2_def;
val res = translate LOG2_def;
val res = translate PAD_LEFT;
val res = translate n2l_def;
val res = translate n2s_def;
val res = translate HEX_def;
val res = translate num_to_bin_string_def;
val res = translate PART_DEF;
val res = translate PARTITION_DEF;
val res = translate QSORT_DEF;
val res = translate ZIP_def;
val res = translate IS_PREFIX;

val res = translate find_match_def;
val res = translate tab_sub_def;
val res = translate base_keys_def;
val res = translate extract_fixed_substrings_def;
val res = translate extract_substrings_n;
val res = translate extract_keys_def;
val res = translate gen_fix_codes;
val res = translate create_fixed_dict_def;
val res = translate lorem_dict_def;
val res = translate FLIP_ALIST_def;

val res = translate compress_def;
val res = translate decompress_def;
val res = translate compress_main_def;

Definition main_function_def:
  main_function (s:mlstring) = List [implode (compress_main (explode s))]
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

Definition compression_prog_def:
  compression_prog = ^prog
End

val _ = export_theory();
