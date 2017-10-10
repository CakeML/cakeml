open preamble
     ml_translatorLib ml_progLib mlintTheory
     mlbasicsProgTheory basisFunctionsLib gcdTheory

val _ = new_theory"mlintProg"

val _ = translation_extends "mlbasicsProg";

val _ = ml_prog_update (open_module "Int");

val _ = ml_prog_update (add_dec ``Dtabbrev unknown_loc [] "int" (Tapp [] TC_int)`` I);
val _ = trans "+" `(+):int->int->int`
val _ = trans "-" `(-):int->int->int`
val _ = trans "*" `int_mul`
val _ = trans "div" `(/):int->int->int`
val _ = trans "mod" `(%):int->int->int`
val _ = trans "<" `(<):int->int->bool`
val _ = trans ">" `(>):int->int->bool`
val _ = trans "<=" `(<=):int->int->bool`
val _ = trans ">=" `(>=):int->int->bool`
val _ = trans "~" `\i. - (i:int)`

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

val _ = next_ml_names := ["toString"];

val result = translate
  (toString_def |> REWRITE_RULE[maxSmall_DEC_def])
val tostring_side = Q.prove(
  `∀x. tostring_side x = T`,
  rw[definition"tostring_side_def"]
  \\ intLib.COOPER_TAC)
  |> update_precondition;

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

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
