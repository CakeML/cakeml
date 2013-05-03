
open HolKernel Parse boolLib bossLib; val _ = new_theory "example_regexp_matcher";

open arithmeticTheory listTheory sortingTheory regexpMatchTheory;

open ml_translatorLib ml_translatorTheory;


(* matcher -- recursion over a datatype *)

val res = translate MEMBER_def
val res = translate (REWRITE_RULE [MEMBER_INTRO] match_def)

val _ = export_theory();

