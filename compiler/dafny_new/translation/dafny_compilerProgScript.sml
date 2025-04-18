(*
  Translates the Dafny to CakeML compiler.
*)

open preamble
open ml_translatorLib
open dafny_to_cakemlProgTheory
open dafny_compilerTheory
open cfTacticsLib  (* process_topdecs *)
open dafny_transformProgTheory
open fromSexpTheory  (* listsexp *)
open stringTheory
open numposrepTheory
open simpleSexpTheory
open ml_translatorTheory
open simpleSexpParseTheory
open dafny_compilerAProgTheory

val _ = new_theory "dafny_compilerProg";

val _ = translation_extends "dafny_compilerAProg";

val r = translate dafny_compilerTheory.dfy_to_cml_def;
val r = translate dafny_compilerTheory.unpack_def;


(* --- *)

Triviality listsexp_alt:
  listsexp = FOLDR (λs1 s2. SX_CONS s1 s2) nil
Proof
  rpt(CHANGED_TAC(CONV_TAC (DEPTH_CONV ETA_CONV))) >> simp[listsexp_def]
QED

val _ = translate listsexp_alt;

(* --- *)

val _ = translate (fromSexpTheory.locnsexp_def |> SIMP_RULE list_ss []);  (* TODO is this necessary *)
val _ = translate fromSexpTheory.locssexp_def;

(* --- *)

val _ = translate HEX_def

Definition hex_alt_def:
  hex_alt x = if x < 16 then HEX x else #"0"
End

val _ = translate hex_alt_def

val _ = Q.prove(`!n. hex_alt_side n <=> T`,
 PURE_REWRITE_TAC[fetch "-" "hex_alt_side_def",fetch "-" "hex_side_def"] >>
 intLib.COOPER_TAC) |> update_precondition;

Definition num_to_hex_string_alt:
  num_to_hex_string_alt = n2s 16 hex_alt
End

Theorem num_to_hex_string_alt_intro:
  !n. num_to_hex_string n = num_to_hex_string_alt n
Proof
  simp[num_to_hex_string_def,num_to_hex_string_alt,n2s_def] >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  rw[] >>
  PURE_ONCE_REWRITE_TAC[numposrepTheory.n2l_def] >>
  rw[hex_alt_def]
QED

val _ = translate numposrepTheory.n2l_def;

val n2l_side_thm = Q.prove(`!n m. n2l_side n m <=> n <> 0`,
  strip_tac >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[fetch "-" "n2l_side_def"] >>
  rw[]) |> update_precondition

val  _ = translate n2s_def;

val n2s_side_thm = Q.prove(`!n f m. n2s_side n f m <=> n <> 0`,
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[fetch "-" "n2s_side_def"] >>
  rw[n2l_side_thm]) |> update_precondition

val _ = translate num_to_hex_string_alt;

val _ = translate num_to_hex_string_alt_intro;

(* --- *)

val r = translate fromSexpTheory.encode_control_def;

val _ = translate fromSexpTheory.SEXSTR_def;

val _ = translate fromSexpTheory.litsexp_def;
val litsexp_side_thm = Q.prove(`!v. litsexp_side v <=> T`,
  PURE_ONCE_REWRITE_TAC[fetch "-" "litsexp_side_def"] >> rw[] >>
                               intLib.COOPER_TAC) |> update_precondition

val _ = translate optsexp_def;
val _ = translate idsexp_def;
val _ = translate typesexp_def;

val _ = translate fromSexpTheory.patsexp_def;

val _ = translate opsexp_def;
val _ = translate lopsexp_def;
val _ = translate scsexp_def;
val _ = translate expsexp_def;

val _ = translate type_defsexp_def;

val _ = translate fromSexpTheory.decsexp_def;

val r = translate dafny_compilerTheory.cmlm_to_str_def;

val _ = ml_translatorLib.use_string_type true;

val r = translate dafny_compilerTheory.main_function_def;

val _ = type_of “main_function” = “:mlstring -> mlstring”
        orelse failwith "The main_function has the wrong type.";

val _ = r |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of \
                  \dafny_compilerTheory.main_function_def");

val main = process_topdecs
           ‘print (main_function (TextIO.inputAll TextIO.stdIn));’;

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand;

Definition dafny_compiler_prog_def:
  dafny_compiler_prog = ^prog
End

val _ = export_theory ();
