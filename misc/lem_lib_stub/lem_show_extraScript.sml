(*
  This is a file that is required for Lem to work.
*)
open HolKernel boolLib bossLib;

val _ = new_theory "lem_show_extra";

val _ = export_theory ();
