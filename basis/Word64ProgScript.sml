(*
  Module about the built-in word64 type.
*)
Theory Word64Prog
Ancestors
  CharProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "CharProg";

(* Word64 module -- translated *)

val _ = ml_prog_update (open_module "Word64");

val () = generate_sigs := true;

val _ = ml_prog_update (add_dec
  ``Dtabbrev NoLocs [] «word» (Atapp [] (Short «word64»))`` I);

(* to/from int *)
val _ = trans "fromInt" ``n2w:num->word64``;
val _ = trans "toInt" ``w2n:word64->num``;
val _ = trans "toIntSigned" ``w2i:word64->int``;

(* bitwise operations *)
val _ = trans "andb" ``word_and:word64->word64->word64``;;
val _ = trans "orb" ``word_or:word64->word64->word64``;
val _ = trans "xorb" ``word_xor:word64->word64->word64``;

Theorem word_1comp_eq[local]:
    word_1comp w = word_xor w 0xFFFFFFFFFFFFFFFFw:word64
Proof
  fs []
QED

val _ = (next_ml_names := ["notb"]);
val _ = translate word_1comp_eq

(* arithmetic *)
val _ = trans "+" ``word_add:word64->word64->word64``;
val _ = trans "-" ``word_sub:word64->word64->word64``;
val _ = trans "=" ``(=):word64->word64->bool``;
val _ = trans "<" ``word_lo:word64->word64->bool``;
val _ = trans ">" ``word_hi:word64->word64->bool``;
val _ = trans "<=" ``word_ls:word64->word64->bool``;
val _ = trans ">=" ``word_hs:word64->word64->bool``;

(* shifts and rotates (the shift amount is a word) *)
val _ = trans "<<" ``word_lsl_bv:word64->word64->word64``;
val _ = trans ">>" ``word_lsr_bv:word64->word64->word64``;
val _ = trans "~>>" ``word_asr_bv:word64->word64->word64``;
val _ = trans "ror" ``word_ror_bv:word64->word64->word64``;

Definition concat_all_def:
  concat_all (a:word8) b c d e f g h =
    concat_word_list [a;b;c;d;e;f;g;h]:64 word
End

val concat_all_impl =
  REWRITE_RULE [concat_word_list_def, dimindex_8, ZERO_SHIFT, WORD_OR_CLAUSES] concat_all_def;

val _ = (next_ml_names := ["concatAll"]);
val _ = translate concat_all_impl;

val sigs = module_signatures ["fromInt", "toInt", "andb",
  "orb", "xorb", "notb", "+", "-", "<<", ">>", "~>>", "concatAll"];

val _ = ml_prog_update (close_module (SOME sigs));
