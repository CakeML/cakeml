(*
  This is a simple example of applying the translator to a
  matcher for regular expressions.
*)
open HolKernel Parse boolLib bossLib; val _ = new_theory "example_regexp_matcher";

open arithmeticTheory listTheory sortingTheory regexpMatchTheory;

open ml_translatorLib ml_translatorTheory;

(* matcher -- recursion over a datatype *)

val _ = register_type ``:'a # 'b``;

val res = translate MEMBER_def
val res = translate (match_def |> REWRITE_RULE [MEMBER_INTRO])

val _ = export_theory();
