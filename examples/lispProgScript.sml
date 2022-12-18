(*
  Parsing and pretty printing of s-expressions
*)
open preamble basis miscTheory set_sepTheory listTheory mlstringTheory;
open (* lisp: *) parsingTheory source_valuesTheory printingTheory;

val _ = new_theory "lispProg";

val _ = translation_extends "basisProg";

val _ = show_assums := true;

(* --- functions from source_valuesTheory --- *)

val res = translate name_def;
val res = translate head_def;
val res = translate tail_def;
val res = translate isNum_def;
val res = translate v2list_def;
val res = translate list_def;

(* --- functions from parsingTheory --- *)

val res = translate quote_def;
val res = translate parse_def;
val res = translate end_line_def;
val res = translate read_num_def;
val res = translate_no_ind (REWRITE_RULE [MEMBER_INTRO] lex_def);

Triviality lex_ind:
  lex_ind
Proof
  rewrite_tac [fetch "-" "lex_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]
  \\ gvs[MEMBER_def]
QED

val _ = update_precondition lex_ind;

val res = translate lexer_def;

Definition from_str_def:
  from_str s = head (parse (lexer s) (Num 0) [])
End

val res = translate from_str_def;

(* --- functions from printingTheory --- *)

val res = translate num2str_def;

Triviality num2str_side:
  ∀n. num2str_side n
Proof
  ho_match_mp_tac num2str_ind \\ rpt strip_tac
  \\ once_rewrite_tac [fetch "-" "num2str_side_def"] \\ rw []
  \\ ‘n MOD 10 < 10’ by fs [MOD_LESS, SF SFY_ss] \\ simp []
QED

val _ = update_precondition num2str_side;

val res = translate num2ascii_def;
val res = translate ascii_name_def;

Triviality ascii_name_side:
  ∀n. ascii_name_side n
Proof
  rw [fetch "-" "ascii_name_side_def"]
  \\ fs [Once num2ascii_def,AllCaseEqs()]
QED

val _ = update_precondition ascii_name_side;

val res = translate name2str_def;
val res = translate dest_quote_def;
val res = translate dest_list_def;
val res = translate newlines_def;
val res = translate v2pretty_def;
val res = translate get_size_def;
val res = translate get_next_size_def;
val res = translate annotate_def;
val res = translate remove_all_def;
val res = translate smart_remove_def;
val res = translate flatten_def;
val res = translate dropWhile_def;
val res = translate is_comment_def;
val res = translate v2str_def;
val res = translate vs2str_def;

val _ = export_theory();
