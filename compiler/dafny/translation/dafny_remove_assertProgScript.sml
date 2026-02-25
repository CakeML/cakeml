(*
  Translates definitions for removing assert.
*)
Theory dafny_remove_assertProg
Ancestors
  dafny_freshenProg dafny_remove_assert
Libs
  preamble ml_translatorLib


val _ = translation_extends "dafny_freshenProg";

val r = translate dafny_remove_assertTheory.remove_assert_stmt_def;
val r = translate dafny_remove_assertTheory.remove_assert_member_def;
val r = translate dafny_remove_assertTheory.remove_assert_def;
