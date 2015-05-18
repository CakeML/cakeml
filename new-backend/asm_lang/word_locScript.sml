open HolKernel Parse boolLib bossLib;
open wordsTheory;

val _ = new_theory "word_loc";

val _ = Datatype `
  word_loc = Word ('a word) | Loc num num `;

val _ = export_theory();
