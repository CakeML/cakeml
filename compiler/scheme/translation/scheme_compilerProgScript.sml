(*
  Build a CakeML program implementing Scheme-to-Cake compiler
*)
open preamble basis;
open to_sexpProgTheory;
open scheme_astTheory;
open scheme_parsingTheory;
open scheme_to_cakeTheory;
open scheme_compilerTheory;

val _ = new_theory "scheme_compilerProg";

val _ = translation_extends "to_sexpProg";

(* parsing *)

val r = translate (delimits_next_def |> SRULE [MEMBER_INTRO]);
val r = translate (read_bool_def |> SRULE [MEMBER_INTRO]);
val r = translate read_num_def;
val r = translate read_word_def;
val r = translate end_line_def;
val r = translate (lex_def |> SRULE [MEMBER_INTRO]);
val r = translate lexer_def;
(*val r = translate scheme_valuesTheory.list_def;*)
(*val r = translate scheme_valuesTheory.name_def;*)
val r = translate scheme_valuesTheory.head_def;
(*val r = translate quote_def;*)
val r = translate parse_def;
val r = translate pair_to_list_def;
val r = translate cons_formals_def;
val r = translate cons_ast_def;
val r = translate parse_to_ast_def;

(* codegen *)

val r = translate locationTheory.unknown_loc_def;
val r = translate lit_to_val_def;
val r = translate cake_print_def;
val r = translate to_ml_vals_def;
val r = translate cons_list_def;
val r = translate proc_ml_def;
val r = translate letinit_ml_def;
val r = translate cps_transform_def;
val r = translate scheme_cont_def;
val r = translate exp_with_cont_def;
val r = translate scheme_basis_def;
val r = translate codegen_def;

(* top-level compiler *)

val r = translate cake_prog_to_string_def;
val r = translate cake_for_err_def;
val r = translate compile_def;
val r = translate main_function_def;

(* main function *)

val _ = type_of “main_function” = “:mlstring -> mlstring”
        orelse failwith "The main_function has the wrong type.";

val main = process_topdecs
           `print (main_function (TextIO.inputAll TextIO.stdIn));`;

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand;

Definition scheme_compiler_prog_def:
  scheme_compiler_prog = ^prog
End

val _ = export_theory ();
