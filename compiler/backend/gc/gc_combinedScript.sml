open preamble gc_sharedTheory copying_gcTheory gen_gcTheory gen_gc_partialTheory;
open data_to_wordTheory;

val _ = new_theory "gc_combined";

val _ = Datatype `
  gen_state = GenState num (num list)`;

val gc_combined_def = Define `
  gc_combined conf None (roots,heap,gs:gen_state) =
    (roots,heap,0,0,gs,T) /\
  gc_combined conf Simple (roots,heap,gs) =
    (let (roots,heap,a,c) = full_gc (roots,heap,conf.limit) in
       (roots,heap ++ heap_expand (conf.limit-a),a,conf.limit-a,gs,c)) /\
  gc_combined conf (Generational limits) (roots,heap,gs) =
    (let (roots,state) = gen_gc conf (roots,heap) in
       (roots, state.h1 ++ heap_expand state.n ++ state.r1,
        state.a, state.n, gs, state.ok))`

val _ = export_theory();
