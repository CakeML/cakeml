(*
  This is a file that is required for Lem to work.
*)
open HolKernel Parse boolLib bossLib;
open intLib finite_mapTheory;

val _ = new_theory "lem_pervasives";

val _ = export_theory ();
