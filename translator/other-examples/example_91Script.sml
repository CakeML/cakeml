(*
  This is a simple example of applying the translator to
  the 91 function.
*)
open HolKernel Parse boolLib bossLib;

open ninetyOneTheory arithmeticTheory listTheory sortingTheory;
open regexpMatchTheory;

open ml_translatorLib;

val _ = set_grammar_ancestry ["ninetyOne", "arithmetic", "list", "sorting",
                              "regexpMatch"];

val _ = new_theory "example_91";

(* 91 -- easy *)

val res = translate N_def

val _ = export_theory();
