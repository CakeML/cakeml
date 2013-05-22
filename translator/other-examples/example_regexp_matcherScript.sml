
open HolKernel Parse boolLib bossLib; val _ = new_theory "example_regexp_matcher";

open arithmeticTheory listTheory sortingTheory regexpMatchTheory;

open ml_translatorLib ml_translatorTheory;

val _ = (use_mem_intro := true);

(* matcher -- recursion over a datatype *)

val _ = register_type ``:'a # 'b``;

val res = translate MEMBER_def
val res = translate match_def

val _ = export_theory();
