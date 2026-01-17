(*
  A module about the char type for the CakeML standard basis library.
*)
Theory CharProg
Ancestors
  RatProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "RatProg";

(* Char module -- translated *)

val _ = ml_prog_update (open_module "Char");

val () = generate_sigs := true;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] «char» (Atapp [] (Short «char»))`` I);

val _ = trans "ord" stringSyntax.ord_tm;
val _ = trans "chr" stringSyntax.chr_tm;
val _ = trans "=" “(=):char->char->bool”;
val _ = trans "<" stringSyntax.char_lt_tm;
val _ = trans ">" stringSyntax.char_gt_tm;
val _ = trans "<=" stringSyntax.char_le_tm;
val _ = trans ">=" stringSyntax.char_ge_tm;

val _ = next_ml_names := ["isSpace"];
val res = translate stringTheory.isSpace_def;

Definition fromByte_def:
  fromByte (w:word8) = CHR (w2n w)
End

val _ = next_ml_names := ["fromByte"];
val res = translate fromByte_def;

Theorem frombyte_side_thm[local]:
  frombyte_side v = T
Proof
  fs [fetch "-" "frombyte_side_def"]
  \\ qspec_then ‘v’ assume_tac w2n_lt
  \\ fs [dimword_def]
QED

val _ = update_precondition frombyte_side_thm;

Definition some_chars_vector_def:
  some_chars_vector = Vector (GENLIST (λn. SOME (CHR n)) 256)
End

Definition some_char_def:
  some_char c = regexp_compiler$sub some_chars_vector (ORD c)
End

Theorem some_char_thm:
  some_char c = SOME c
Proof
  Cases_on ‘c’
  \\ rewrite_tac [some_chars_vector_def,some_char_def,regexp_compilerTheory.sub_def]
  \\ full_simp_tac std_ss [ORD_CHR]
  \\ full_simp_tac std_ss [GSYM ORD_CHR]
  \\ full_simp_tac std_ss [EL_GENLIST]
QED

val _ = ml_prog_update open_local_block;

val res = translate (EVAL “some_chars_vector”);

val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["some"];
val res = translate some_char_def;

Theorem some_char_side_thm[local]:
  some_char_side v = T
Proof
  fs [fetch "-" "some_char_side_def"] \\ EVAL_TAC \\ fs [ORD_BOUND]
QED

val _ = update_precondition some_char_side_thm;

val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update (close_module NONE);
