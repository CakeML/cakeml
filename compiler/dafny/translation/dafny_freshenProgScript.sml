(*
  Translates definitions for the freshen pass.
*)
Theory dafny_freshenProg
Ancestors
  dafny_to_cakemlProg dafny_freshen
Libs
  preamble ml_translatorLib


val _ = translation_extends "dafny_to_cakemlProg";

val r = translate dafny_freshenTheory.lookup_def;
val r = translate dafny_freshenTheory.add_fresh_def;
val r = translate dafny_freshenTheory.map_add_fresh_def;
val r = translate dafny_freshenTheory.freshen_exp_def;
val r = translate dafny_freshenTheory.freshen_lhs_exp_def;
val r = translate dafny_freshenTheory.freshen_lhs_exps_def;
val r = translate dafny_freshenTheory.freshen_rhs_exp_def;
val r = translate dafny_freshenTheory.freshen_rhs_exps_def;
val r = translate dafny_freshenTheory.freshen_stmt_def;
val r = translate dafny_freshenTheory.freshen_member_def;
val r = translate dafny_freshenTheory.freshen_program_def;

