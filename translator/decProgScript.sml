(*
  Translation of CakeML source AST
*)

open preamble astTheory semanticPrimitivesTheory;
open terminationTheory ml_translatorLib ml_translatorTheory ml_progLib;

val _ = new_theory "decProg";

val _ = use_string_type true;

val _ = register_type ``:'a list``;
val _ = register_type ``:'a option``;
val _ = register_type ``:lit``;
val _ = register_type ``:('a,'b) id``;
val _ = register_type ``:ast_t``;
val _ = register_type ``:pat``;
val _ = register_type ``:opn``;
val _ = register_type ``:opb``;
val _ = register_type ``:opw``;
val _ = register_type ``:shift``;
val _ = register_type ``:word_size``;
val _ = register_type ``:fp_uop``;
val _ = register_type ``:fp_bop``;
val _ = register_type ``:fp_cmp``;
val _ = register_type ``:op``;
val _ = register_type ``:lop``;
val _ = register_type ``:exp``;
val _ = register_type ``:dec``;

val AST_LIT_TYPE_def = fetch "-" "AST_LIT_TYPE_def"
  |> SIMP_RULE (srw_ss()) [WORD_def,HOL_STRING_TYPE_def,CHAR_def,STRING_TYPE_def,
       INT_def,mlstringTheory.implode_def]

Theorem enc_lit_11[simp]:
  !i j. enc_lit i = enc_lit j <=> i = j
Proof
  Cases_on `i` \\ Cases_on `j` \\ fs [enc_lit_def]
QED

Theorem dec_lit_enc_lit[simp]:
  dec_lit (enc_lit l) = SOME l
Proof
  fs [dec_lit_def]
QED

Theorem AST_LIT_TYPE_eq_enc:
  !l v. AST_LIT_TYPE l v <=> enc_lit l = v
Proof
  Cases \\ fs [AST_LIT_TYPE_def,enc_lit_def,lit_type_num_def]
  \\ rw [] \\ eq_tac \\ rw []
QED

val _ = (print_asts := true);
val _ = export_theory();
