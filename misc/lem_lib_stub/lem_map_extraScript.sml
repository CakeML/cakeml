(*
  This is a file that is required for Lem to work.
*)
open HolKernel Parse boolLib bossLib;

val _ = new_theory "lem_map_extra";

val _ = export_theory ();
