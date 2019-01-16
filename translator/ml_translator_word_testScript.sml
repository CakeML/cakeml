(*
  Tests of word operation translation
 *)

open HolKernel Parse boolLib bossLib;

open listTheory pairTheory ml_translatorLib ml_translatorTheory;
open ml_progLib;
open wordsTheory;
open blastLib;
open words_extraTheory;

val _ = new_theory "ml_translator_word_test";

val word64_msb_thm = Q.prove(
  `!w. word_msb (w:word64) =
         ((w && 0x8000000000000000w) = 0x8000000000000000w)`,BBLAST_TAC);
val res = translate word64_msb_thm;

val word64_and_thm = Q.prove(
  `!(w:word64). (w && 0w) = 0w`,BBLAST_TAC);
val res = translate word64_and_thm;

val word_and_or = Define`word_and_or (w1:word64) (w2:word64) =
    word_or (word_and w1 w2) w1`
val res = translate word_and_or;

val word_and_or_plus1 = Define`word_and_or_plus1 (w1:word64) (w2:word64) =
    (word_and_or w1 w2) + 1w`
val res = translate word_and_or_plus1;

val word_eq_add = Define`word_eq_add (w1:word64) (w2:word64) = ((w1+w2) = (w2+1w))`
val res = translate word_eq_add;

val word_and_or_sub1 = Define`
    word_and_or_sub1 (w1:word64) (w2:word64) (w3:word64)
    = (word_and_or w1 w2) - w3`
val res = translate word_and_or_sub1;

val word_lsr_lsl = Define`word_lsl_lsr (w:word64) = word_lsr (word_lsl w 3) 3`
val res = translate word_lsr_lsl;

(* TODO fix *)
(* fails translation with `different constructors`, see ml_translatorLib *)
val word_lt_translation_test = Define`word_lt_translation_test (w1:word64) (w2:word64)
    = (w1 < w2)`
val res = translate word_lt_translation_test;

val word_lt_translation_test2 = Define`word_lt_translation_test (w1:word64) (w2:word64)
    = (w1 <+ w2) /\ (w1 < w2)`
val res = translate word_lt_translation_test2;



val _ = export_theory();
