
open HolKernel Parse boolLib bossLib; val _ = new_theory "example_regexp_matcher";

open ninetyOneTheory arithmeticTheory listTheory sortingTheory;
open regexpMatchTheory;

open ml_translatorLib;


(* matcher -- recursion over a datatype *)

val res = translate MEM
val res = translate match_def

val _ = export_theory();

