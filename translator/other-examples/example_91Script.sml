
open HolKernel Parse boolLib bossLib; val _ = new_theory "example_91";

open ninetyOneTheory arithmeticTheory listTheory sortingTheory;
open regexpMatchTheory;

open ml_translatorLib;


(* 91 -- easy *)

val res = translate N_def

val _ = export_theory();

