(*
 * Translates the definitions for Result monad.
 *)

open preamble ml_translatorLib
open cakeml_and_dafny_astProgTheory
open result_monadTheory

val _ = new_theory "result_monadProg";

val _ = translation_extends "cakeml_and_dafny_astProg";

val r = translate result_monadTheory.bind_def;
val r = translate result_monadTheory.result_mmap_def;

val _ = export_theory ();
