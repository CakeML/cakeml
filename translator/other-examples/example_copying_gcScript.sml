(*
  This is a simple example of applying the translator to an
  algorithm-level model of a copying garbage collector.
*)
open HolKernel Parse boolLib bossLib; val _ = new_theory "example_copying_gc";

open copying_gcTheory ml_translatorLib;

val res = translate getBLOCK_def;
val res = translate combinTheory.UPDATE_def;
val res = translate rel_move_def;
val res = translate rel_move_list_def;
val res = translate rel_gc_step_def;

val rel_gc_loop_thm = Q.prove(
  `rel_gc_loop z y =
     case y of (i,j,m,b,e,b2,e2) =>
       if i = j then (i,m)
       else if ¬(i < j ∧ j ≤ e) then (i,m)
       else
         let (i,j,m) = rel_gc_step z (i,j,m,b,e,b2,e2) in
         let (i,m) = rel_gc_loop z (i,j,m,b,e,b2,e2) in
           (i,m)`,
  PairCases_on `y` \\ fs [Once rel_gc_loop_def]);

val res = translate rel_gc_loop_thm;
val res = translate RANGE_def;
val res = translate CUT_def;
val res = translate rel_gc_def;

val _ = export_theory();
