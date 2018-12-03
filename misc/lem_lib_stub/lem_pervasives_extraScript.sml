(*
  This is a file that is required for Lem to work.
*)
open HolKernel Parse boolLib bossLib;
open intLib;

val _ = new_theory "lem_pervasives_extra";

val _ = export_theory ();
