(*
  This is a file that is required for Lem to work.
*)
open HolKernel bossLib Parse

val _ = new_theory "lem_set_extra";

val _ = export_theory ();
