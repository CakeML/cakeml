open HolKernel Parse boolLib bossLib;
open preamble;
open std_preludeTheory std_preludeLib;

val _ = new_theory "compileProg"

val _ = translation_extends "std_prelude";

val compile_def = Define `
  compile str = "  Hello world!  " ++ REVERSE str`;

val res = translate compile_def

val _ = export_theory();
