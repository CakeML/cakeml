(*
 * Program implementing the Dafny to CakeML compiler.
 *)

open preamble
open basis

val _ = new_theory "dafny_compilerProg";

val _ = translation_extends "basisProg";

val r = translate dafny_compilerTheory.main_def;

val _ = export_theory ();
