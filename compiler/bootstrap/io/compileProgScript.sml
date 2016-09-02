open HolKernel Parse boolLib bossLib;
open preamble;
open std_preludeTheory std_preludeLib;

val _ = new_theory "compileProg"

val _ = translation_extends "std_prelude";

val compile_def = Define `
  compile str =
    MAP (\c. n2w (ORD c)) ("  Hello world!  " ++ REVERSE str) :word8 list`;

val res = translate compile_def

val _ = export_theory();
