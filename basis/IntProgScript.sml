(*
  Module about the built-in integer tyoe. Note that CakeML uses
  arbitrary precision integers (the mathematical intergers).
*)
open preamble
     ml_translatorLib ml_progLib mlintTheory
     mlbasicsProgTheory basisFunctionsLib gcdTheory

val _ = new_theory"IntProg"

val _ = translation_extends "mlbasicsProg";

val _ = ml_prog_update (open_module "Int");

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "int" (Atapp [] (Short "int"))`` I);

val _ = trans "+" intSyntax.plus_tm;
val _ = trans "-" intSyntax.minus_tm;
val _ = trans "*" intSyntax.mult_tm;
val _ = trans "div" intSyntax.div_tm;
val _ = trans "mod" intSyntax.mod_tm;
val _ = trans "<" intSyntax.less_tm;
val _ = trans ">" intSyntax.great_tm;
val _ = trans "<=" intSyntax.leq_tm;
val _ = trans ">=" intSyntax.geq_tm;
val _ = trans "~" ``\i. - (i:int)``;

val _ = ml_prog_update open_local_block;

val result = translate zero_pad_def

val result = translate toChar_def
val tochar_side_def = definition"tochar_side_def";
val tochar_side = Q.prove(
  `∀x. tochar_side x <=> (~(x < 10) ==> x < 201)`,
  rw[tochar_side_def])
  |> update_precondition;

val result = translate simple_toChars_def

val simple_toChars_side = Q.prove(
  `∀x y z. simple_tochars_side x y z = T`,
  ho_match_mp_tac simple_toChars_ind \\ rw[]
  \\ rw[Once (theorem"simple_tochars_side_def")])
  |> update_precondition;

val _ = save_thm("toChars_ind",
   toChars_ind |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);
val _ = add_preferred_thy "-";
val result = translate
  (toChars_def |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);

val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["toString"];

val toString_v_thm = translate
  (toString_def |> REWRITE_RULE[maxSmall_DEC_def])
val tostring_side = Q.prove(
  `∀x. tostring_side x = T`,
  rw[definition"tostring_side_def"]
  \\ intLib.COOPER_TAC)
  |> update_precondition;

val toString_v_thm = toString_v_thm
  |> DISCH_ALL |> REWRITE_RULE [tostring_side,ml_translatorTheory.PRECONDITION_def]
  |> ml_translatorLib.remove_Eq_from_v_thm;

val Eval_NUM_toString = Q.prove(
  `!v. (INT --> STRING_TYPE) toString v ==>
       (NUM --> STRING_TYPE) num_to_str v`,
  simp [ml_translatorTheory.Arrow_def,
    ml_translatorTheory.AppReturns_def,num_to_str_def,
    ml_translatorTheory.NUM_def,PULL_EXISTS,FORALL_PROD]
  \\ rw [] \\ res_tac)
  |> (fn th => MATCH_MP th toString_v_thm)
  |> add_user_proved_v_thm;

val _ = ml_prog_update open_local_block;

val result = translate fromChar_unsafe_def;
val result = translate fromChars_range_unsafe_def;

val _ = save_thm("fromChars_unsafe_ind",
  fromChars_unsafe_ind |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);
val result = translate (fromChars_unsafe_def
  |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);

val result = translate fromString_unsafe_def;

val fromstring_unsafe_side_def = definition"fromstring_unsafe_side_def";
val fromchars_unsafe_side_def = theorem"fromchars_unsafe_side_def";
val fromchars_range_unsafe_side_def = theorem"fromchars_range_unsafe_side_def";

Theorem fromchars_unsafe_side_thm:
   ∀n s. n ≤ LENGTH s ⇒ fromchars_unsafe_side n (strlit s)
Proof
  completeInduct_on`n` \\ rw[]
  \\ rw[Once fromchars_unsafe_side_def,fromchars_range_unsafe_side_def]
QED

val fromString_unsafe_side = Q.prove(
  `∀x. fromstring_unsafe_side x = T`,
  Cases
  \\ rw[fromstring_unsafe_side_def]
  \\ Cases_on`s` \\ fs[mlstringTheory.substring_def]
  \\ simp_tac bool_ss [ONE,SEG_SUC_CONS,SEG_LENGTH_ID]
  \\ match_mp_tac fromchars_unsafe_side_thm
  \\ rw[]) |> update_precondition;

val result = translate fromChar_def;
val result = translate fromChars_range_def;

val _ = save_thm("fromChars_ind",
  fromChars_ind |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);
val result = translate (fromChars_def
  |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);

val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["fromString"];
val result = translate fromString_def;
val fromstring_side_def = definition"fromstring_side_def";
val fromchars_side_def = theorem"fromchars_side_def";
val fromchars_range_side_def = theorem"fromchars_range_side_def";

Theorem fromchars_side_thm:
   ∀n s. n ≤ LENGTH s ⇒ fromchars_side n (strlit s)
Proof
  completeInduct_on`n` \\ rw[]
  \\ rw[Once fromchars_side_def,fromchars_range_side_def]
QED

val fromString_side = Q.prove(
  `∀x. fromstring_side x = T`,
  Cases
  \\ rw[fromstring_side_def]
  \\ Cases_on`s` \\ fs[mlstringTheory.substring_def]
  \\ simp_tac bool_ss [ONE,SEG_SUC_CONS,SEG_LENGTH_ID]
  \\ match_mp_tac fromchars_side_thm
  \\ rw[]) |> update_precondition;

val _ = next_ml_names := ["fromNatString"];
val result = translate fromNatString_def;

(* GCD *)

val gcd_def = Define `
  gcd a b = if a = 0n then b else gcd (b MOD a) a`

val _ = delete_const "gcd"; (* keeps induction thm *)

val res = translate GCD_EFFICIENTLY;

val gcd_side = prove(
  ``!a b. gcd_side a b = T``,
  recInduct (theorem "gcd_ind") \\ rw []
  \\ once_rewrite_tac [theorem "gcd_side_def"]
  \\ fs [ADD1] \\ rw [] \\ fs [])
  |> update_precondition;

(* compare *)

val _ = (next_ml_names := ["compare"]);
val _ = translate mlintTheory.int_cmp_def;

val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
