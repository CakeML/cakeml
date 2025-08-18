(*
 Translates the definitions for the result monad.
*)
Theory result_monadProg
Ancestors
  dafny_astProg result_monad
Libs
  preamble ml_translatorLib


val _ = translation_extends "dafny_astProg";

val r = translate result_monadTheory.bind_def;
val r = translate result_monadTheory.result_mmap_def;
val r = translate result_monadTheory.result_mmap2_def;
val r = translate result_monadTheory.prefix_error_def;
val r = translate result_monadTheory.extend_path_def;

