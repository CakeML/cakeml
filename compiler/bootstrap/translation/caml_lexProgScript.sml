(*
  Translation of the functions and types in caml_lexScript.sml
 *)

open preamble caml_lexTheory;
open basisProgTheory ml_translatorLib ml_translatorTheory;

val _ = new_theory "caml_lexProg";

val _ = translation_extends "basisProg";

(* -------------------------------------------------------------------------
 * Translator setup
 * ------------------------------------------------------------------------- *)

val RW = REWRITE_RULE
val RW1 = ONCE_REWRITE_RULE
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];
val dest_fun_type = dom_rng
val mk_fun_type = curry op -->;
fun list_mk_fun_type [ty] = ty
  | list_mk_fun_type (ty1::tys) =
      mk_fun_type ty1 (list_mk_fun_type tys)
  | list_mk_fun_type _ = fail()

val _ = add_preferred_thy "-";
(*val _ = add_preferred_thy "termination";*)

Theorem NOT_NIL_AND_LEMMA:
   (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

(* The token type takes a while. These types are to be used with functions
 * that are translated using HOL_STRING_TYPE, so we need to set
 * use_string_type.
 *)

val _ = ml_translatorLib.use_string_type true;

val r = register_type “:caml_lex$token”;

val r = translate isInt_PMATCH;
val r = translate destInt_PMATCH;
val r = translate isChar_PMATCH;
val r = translate destChar_PMATCH;
val r = translate isString_PMATCH;
val r = translate destString_PMATCH;
val r = translate isSymbol_PMATCH;
val r = translate destSymbol_PMATCH;
val r = translate isIdent_PMATCH;
val r = translate destIdent_PMATCH;

(* The rest of the lexer works on character lists.
 *)

val _ = ml_translatorLib.use_string_type false;

val r = translate unhex_alt_def;

Theorem unhex_alt_side[local]:
  ∀x. unhex_alt_side x
Proof
  Cases
  \\ rw [fetch "-" "unhex_alt_side_def", isHexDigit_def]
  \\ once_rewrite_tac [fetch "-" "unhex_side_def"]
  \\ SRW_TAC [DNF_ss] [] \\ gs []
QED

val _ = update_precondition unhex_alt_side;

val r = translate numposrepTheory.l2n_def;

Theorem l2n_side[local]:
  ∀b a. a ≠ 0 ⇒ l2n_side a b
Proof
  Induct \\ rw [Once (fetch "-" "l2n_side_def")]
QED

val _ = update_precondition l2n_side;

val r = translate hex2num_def;
val r = translate dec2num_def;
val r = translate bin2num_def;
val r = translate oct2num_def;

Theorem hex2num_side[local]:
  ∀x. hex2num_side x
Proof
  simp [fetch "-" "hex2num_side_def", fetch "-" "s2n_side_def", l2n_side]
QED

val _ = update_precondition hex2num_side;

Theorem oct2num_side[local]:
  ∀x. oct2num_side x
Proof
  simp [fetch "-" "oct2num_side_def", fetch "-" "s2n_side_def", l2n_side]
QED

val _ = update_precondition oct2num_side;

Theorem bin2num_side[local]:
  ∀x. bin2num_side x
Proof
  simp [fetch "-" "bin2num_side_def", fetch "-" "s2n_side_def", l2n_side]
QED

val _ = update_precondition bin2num_side;

Theorem dec2num_side[local]:
  ∀x. dec2num_side x
Proof
  simp [fetch "-" "dec2num_side_def", fetch "-" "s2n_side_def", l2n_side]
QED

val _ = update_precondition dec2num_side;

val r = translate scan_escseq_def;

Theorem scan_escseq_side[local]:
  ∀x y. scan_escseq_side x y
Proof
  rw [fetch "-" "scan_escseq_side_def"]
  >- (
    simp [hex2num_def, s2n_def, numposrepTheory.l2n_def, unhex_alt_def]
    \\ intLib.ARITH_TAC)
  \\ simp [oct2num_def, s2n_def, numposrepTheory.l2n_def, unhex_alt_def]
  \\ ‘isHexDigit v11 ∧ isHexDigit v9 ∧ isHexDigit v13’
    by (Cases_on ‘v11’ \\ Cases_on ‘v9’
        \\ gs [isHexDigit_def, isOctDigit_def])
  \\ gs []
  \\ ‘UNHEX v13 MOD 8 < 4’
    by (gs [LESS_OR_EQ, NUMERAL_LESS_THM]
        \\ Cases_on ‘v13’ \\ gs [UNHEX_def])
  \\ intLib.ARITH_TAC
QED

val _ = update_precondition scan_escseq_side;

val r = translate caml_lexTheory.next_sym_def;

Theorem next_sym_side[local]:
  ∀x y. next_sym_side x y
Proof
  ho_match_mp_tac next_sym_ind \\ rw []
  \\ simp [Once (fetch "-" "next_sym_side_def")]
QED

val _ = update_precondition next_sym_side;

val r = translate caml_lexTheory.lexer_fun_def;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val () = ml_translatorLib.clean_on_exit := true;

val _ = export_theory ();

