open HolKernel Parse boolLib bossLib;
open preamble;
open ioProgTheory ml_translatorLib;
open ioProgLib

val _ = new_theory "compileProg"

val _ = translation_extends "ioProg";

val compile_def = Define `
  compile str =
    MAP (\c. n2w (ORD c)) ("  Hello world!  " ++ REVERSE str) :word8 list`;

val res = translate compile_def

val th = ioProgLib.append_main_call "compile" ``compile``;

val _ = export_theory();
