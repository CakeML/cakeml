(*
  This is a simple example of applying the translator to an
  algorithm-level model of a copying garbage collector.
*)
Theory example_copying_gc
Ancestors
  copying_gc
Libs
  ml_translatorLib

val res = translate getBLOCK_def;
val res = translate combinTheory.UPDATE_def;
val res = translate rel_move_def;
val res = translate rel_move_list_def;
val res = translate rel_gc_step_def;

Triviality rel_gc_loop_thm:
  rel_gc_loop z y =
     case y of (i,j,m,b,e,b2,e2) =>
       if i = j then (i,m)
       else if ¬(i < j ∧ j ≤ e) then (i,m)
       else
         let (i,j,m) = rel_gc_step z (i,j,m,b,e,b2,e2) in
         let (i,m) = rel_gc_loop z (i,j,m,b,e,b2,e2) in
           (i,m)
Proof
  PairCases_on `y` \\ fs [Once rel_gc_loop_def]
QED

val res = translate rel_gc_loop_thm;
val res = translate RANGE_def;
val res = translate CUT_def;
val res = translate rel_gc_def;

