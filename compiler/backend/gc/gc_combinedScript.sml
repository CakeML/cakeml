(*
  One function that can run any of the GC algorithms.
*)
open preamble gc_sharedTheory copying_gcTheory gen_gcTheory gen_gc_partialTheory;
open data_to_wordTheory;

val _ = new_theory "gc_combined";

val _ = Datatype `
  gen_state = GenState num (num list)`;

val make_partial_conf_def = Define `
  make_partial_conf (conf:'a gen_gc_conf) (GenState _ gen_starts) rs =
    <| limit := conf.limit
     ; isRef := conf.isRef
     ; gen_start := HD gen_starts
     ; refs_start := rs
     |>`;

val gc_combined_def = Define `
  gc_combined conf None (roots,heap,gs:gen_state,_,_) =
    (roots,heap,0,0,gs,T) /\
  gc_combined conf Simple (roots,heap,gs,_,_) =
    (let (roots,heap,a,c) = full_gc (roots,heap,conf.limit) in
       (roots,heap ++ heap_expand (conf.limit-a),a,conf.limit-a,gs,c)) /\
  gc_combined conf (Generational limits) (roots,heap,gs,rs,do_partial) =
    if do_partial then
      (let partial_conf = make_partial_conf conf gs rs in
       let (roots,state) = partial_gc partial_conf (roots,heap) in
         (roots, state.old ++ state.h1 ++ heap_expand state.n ++ state.r1,
          state.a, state.n, GenState 0 (MAP (K state.a) limits), state.ok))
    else
      (let (roots,state) = gen_gc conf (roots,heap) in
         (roots, state.h1 ++ heap_expand state.n ++ state.r1,
          state.a, state.n, GenState 0 (MAP (K state.a) limits), state.ok))`

val _ = export_theory();
