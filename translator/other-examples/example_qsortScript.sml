
open HolKernel Parse boolLib bossLib; val _ = new_theory "example_qsort";

open ninetyOneTheory arithmeticTheory listTheory sortingTheory;
open regexpMatchTheory;

open ml_translatorLib;

(* qsort *)

val res = translate APPEND;
val res = translate PART_DEF;
val res = translate PARTITION_DEF;
val res = translate QSORT_DEF;

val _ = export_theory();

