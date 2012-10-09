open HolKernel Parse boolLib bossLib; val _ = new_theory "example_copying_gc";

open copying_gcTheory ml_translatorLib;

val res = translate getBLOCK_def;
val res = translate combinTheory.UPDATE_def;
val res = translate rel_move_def;
val res = translate rel_move_list_def;
val res = translate rel_gc_step_def;
val res = translate rel_gc_loop_def;
val res = translate RANGE_def;
val res = translate CUT_def;
val res = translate rel_gc_def;

val _ = export_theory();

