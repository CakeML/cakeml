(*
  This is a simple example of applying the translator to a
  functional version of quick sort.
*)
open HolKernel Parse boolLib bossLib;

open ninetyOneTheory arithmeticTheory listTheory sortingTheory;
open regexpMatchTheory;

open ml_translatorLib;

val _ = set_grammar_ancestry ["ninetyOne", "arithmetic", "list", "sorting",
                              "regexpMatch"];

val _ = new_theory "example_qsort";

(* qsort *)

val res = translate APPEND;
val res = translate PART_DEF;
val res = translate PARTITION_DEF;
val res = translate QSORT_DEF;

val _ = export_theory();
