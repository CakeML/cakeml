(*
 * Translates the definitions for Result monad.
 *)

open preamble ml_translatorLib
open dafny_astProgTheory
open result_monadTheory

val _ = new_theory "result_monadProg";

val _ = translation_extends "dafny_astProg";

val r = translate result_monadTheory.bind_def;
val r = translate result_monadTheory.result_mmap_def;

val _ = export_theory ();
