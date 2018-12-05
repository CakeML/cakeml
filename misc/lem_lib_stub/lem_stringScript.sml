(*
  This is a file that is required for Lem to work.
*)
open HolKernel Parse boolLib bossLib;
open stringTheory;

val _ = new_theory "lem_string";

val _ = export_theory ();
