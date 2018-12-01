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

val () = generate_sigs := true;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "int" (Atapp [] (Short "int"))`` I);

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

val fromchars_unsafe_side_thm = Q.store_thm("fromchars_unsafe_side_thm",
  `∀n s. n ≤ LENGTH s ⇒ fromchars_unsafe_side n (strlit s)`,
  completeInduct_on`n` \\ rw[]
  \\ rw[Once fromchars_unsafe_side_def,fromchars_range_unsafe_side_def]);

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

val _ = next_ml_names := ["fromString"];
val result = translate fromString_def;
val fromstring_side_def = definition"fromstring_side_def";
val fromchars_side_def = theorem"fromchars_side_def";
val fromchars_range_side_def = theorem"fromchars_range_side_def";

val fromchars_side_thm = Q.store_thm("fromchars_side_thm",
  `∀n s. n ≤ LENGTH s ⇒ fromchars_side n (strlit s)`,
  completeInduct_on`n` \\ rw[]
  \\ rw[Once fromchars_side_def,fromchars_range_side_def]);

val fromString_side = Q.prove(
  `∀x. fromstring_side x = T`,
  Cases
  \\ rw[fromstring_side_def]
  \\ Cases_on`s` \\ fs[mlstringTheory.substring_def]
  \\ simp_tac bool_ss [ONE,SEG_SUC_CONS,SEG_LENGTH_ID]
  \\ match_mp_tac fromchars_side_thm
  \\ rw[]) |> update_precondition;

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

val sigs = module_signatures [
  "+",
  "-",
  "*",
  "div",
  "mod",
  "<",
  ">",
  "<=",
  ">=",
  "~",
  "toString",
  "fromString",
  "gcd"
];

val _ = ml_prog_update (close_module (SOME sigs));

val _ = export_theory();
