(*
  This is a simple example of applying the translator to
  a balanced binary tree from HOL.
*)
open HolKernel Parse boolLib bossLib; val _ = new_theory "example_balanced_bst";

open comparisonTheory balanced_mapTheory;

open ml_translatorLib ml_progLib;

val _ = register_type ``:('k,'v) balanced_map``;

val _ = translate lookup_def;
val _ = translate singleton_def;
val _ = translate ratio_def;
val _ = translate size_def;
val _ = translate delta_def;
val _ = translate balanceL_def;
val _ = translate balanceR_def;
val _ = translate insert_def;
val _ = translate num_cmp_def;

(* Code to print the source, unverified *)
(* taken from the tutorial
fun get_current_prog() =
let
  val state = get_ml_prog_state()
  val state_thm =
    state |> ml_progLib.remove_snocs
          |> ml_progLib.clean_state
          |> get_thm
  val current_prog =
    state_thm
    |> concl
    |> strip_comb |> #2
    |> el 3
in current_prog end

astPP.enable_astPP();
get_current_prog();
*)

val _ = export_theory();
