(*
   Defines word test operation
*)

open HolKernel Parse boolLib bossLib;
open wordsTheory;

val _ = new_theory "words_extra"

val word_test_def = Define `
    word_test x y = (word_and x y = 0w)`

val _ = export_theory()
