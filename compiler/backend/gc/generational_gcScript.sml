open preamble wordsTheory wordsLib integer_wordTheory gc_sharedTheory basic_gcTheory;

val _ = new_theory "generational_gc";

val gc_state_component_equality = DB.fetch "gc_shared" "gc_state_component_equality";

val _ = Datatype `
  gen_gc_conf =
    <| limit : num              (* size of heap *)
     ; isRef : ('a, 'b) heap_element -> bool
     ; gen_start : num          (* start of generation *)
     ; gen_end : num            (* end of generation *)
     ; refs_start : num         (* start of references, gen_end < refs_start *)
     |>`;

val gc_move_def = Define `
  (gc_move conf state (Data d) = (Data d, state)) /\
  (gc_move conf state (Pointer ptr d) =
     if ptr < conf.gen_start \/ conf.gen_end <= ptr then
       let (heap, ok) =  gc_forward_ptr ptr state.heap ptr d state.ok in
       (Pointer ptr d
       ,state with <| heap := heap; ok := ok |>) else
     case heap_lookup ptr state.heap of
     | SOME (DataElement xs l dd) =>
       let ok = state.ok /\ l+1 <= state.n in
       let n = state.n - (l + 1) in
        if conf.isRef (DataElement xs l dd) then
          (* put refs in r4 *)
          let r4 = (DataElement xs l dd) :: state.r4 in
          let (heap, c) = gc_forward_ptr ptr state.heap (state.a + n) d ok in
            (Pointer (state.a + n) d
            ,state with <| r4 := r4; n := n; heap := heap; ok := ok |>)
        else
          (* put data in h2 *)
          let h2 = state.h2 ++ [DataElement xs l dd] in
          let (heap,ok) = gc_forward_ptr ptr state.heap state.a d ok in
          let a = state.a + l + 1 in
            (Pointer state.a d
            ,state with <| h2 := h2; n := n; a := a; heap := heap; ok := ok |>)
     | SOME (ForwardPointer ptr _ l) => (Pointer ptr d,state)
     | _ => (Pointer ptr d, state with <| ok := F |>) )`;

val gc_move_consts = prove(
  ``!x x' state state'.
    (gc_move conf state x = (x',state')) ==>
    (state.h1 = state'.h1) /\
    (state.r3 = state'.r3) /\
    (state.r2 = state'.r2) /\
    (state.r1 = state'.r1)``,
  Cases
  \\ fs [gc_move_def]
  \\ ntac 4 strip_tac
  \\ Cases_on `n < conf.gen_start ∨ conf.gen_end ≤ n`
  THEN1
    (pairarg_tac \\ fs []
    \\ fs [gc_state_component_equality])
  \\ fs []
  \\ Cases_on `heap_lookup n state.heap`
  \\ fs [gc_state_component_equality]
  \\ Cases_on `x`
  \\ fs [LET_THM,gc_state_component_equality]
  \\ pairarg_tac
  \\ fs []
  \\ Cases_on `conf.isRef (DataElement l n' b)`
  \\ pairarg_tac
  \\ fs [gc_state_component_equality]);

val gc_move_list_def = Define `
  (gc_move_list conf state [] = ([], state)) /\
  (gc_move_list conf state (x::xs) =
    let (x,state) = gc_move conf state x in
    let (xs,state) = gc_move_list conf state xs in
      (x::xs,state))`;

val gc_move_list_consts = prove(
  ``!xs xs' state state'.
    (gc_move_list conf state xs = (xs',state')) ==>
    (state.h1 = state'.h1) /\
    (state.r3 = state'.r3) /\
    (state.r2 = state'.r2) /\
    (state.r1 = state'.r1)``,
  Induct
  \\ fs [gc_move_list_def,LET_THM]
  \\ ntac 5 strip_tac
  \\ pairarg_tac
  \\ fs []
  \\ pairarg_tac
  \\ fs []
  \\ rpt var_eq_tac
  \\ drule gc_move_consts
  \\ metis_tac []);

val gc_move_data_def = tDefine "gc_move_data"  `
  (gc_move_data conf state =
    case state.h2 of
    | [] => state
    | h::h2 =>
      if conf.limit < heap_length (state.h1 ++ h::h2) then state with <| ok := F |> else
       case h of
       | DataElement xs l d =>
         let (xs,state) = gc_move_list conf state xs in
         let h1 = state.h1 ++ [DataElement xs l d] in
         let h2 = TL state.h2 in
         let ok = state.ok /\ state.h2 <> [] /\ (HD state.h2 = h) in
           gc_move_data conf (state with <| h1 := h1; h2 := h2; ok := ok |>)
       | _ => state with <| ok := F |>)`
  (WF_REL_TAC `measure (\(conf,state). conf.limit - heap_length state.h1)`
  \\ rw [heap_length_def,el_length_def,SUM_APPEND]
  \\ imp_res_tac (GSYM gc_move_list_consts)
  \\ fs []
  \\ decide_tac)

val gc_move_refs_def = tDefine "gc_move_refs" `
  (* maybe more refs (r4 could have more) *)
  gc_move_refs conf state =
    case state.r2 of
    | [] => state with <| r3 := []; r1 := state.r3 ++ state.r1 |>
    | ref :: r2 =>
      case ref of
      | DataElement xs l d =>
        let (xs,state) = gc_move_list conf state xs in
        let r3 = state.r3 ++ [DataElement xs l d] in
          gc_move_refs conf (state with <| r2 := r2; r3 := r3 |>)
      | _ => state with <| ok := F |>`
  (WF_REL_TAC `measure (\(conf,state). heap_length state.r2)`
  \\ rw [heap_length_def,el_length_def,SUM_APPEND]
  \\ decide_tac);

(* The main gc loop *)
val gc_move_loop_def = Define `
  gc_move_loop conf state (clock : num) =
    if clock = 0 then state with <| ok := F |> else
      case (state.h2,state.r4) of
      | ([],[]) => state
      | (h2,[]) =>
        let state = gc_move_data conf state in
          gc_move_loop conf state (clock-1)
      | (h2,r4) =>
        let state = gc_move_refs conf (state with <| r2 := r4; r4 := [] |>) in
          gc_move_loop conf state (clock-1)`

val partial_gc_def = Define `
  partial_gc conf (roots,heap) =
    let ok0 = (heap_length heap = conf.limit) in
    case heap_segment (conf.gen_start,conf.refs_start) heap of
    | NONE => (roots,empty_state with <| ok := F |>)
    | SOME (old,current,refs) =>
      let n = heap_length current in
      let state = empty_state
          with <| heap := heap
                ; r2 := refs
                ; a := conf.gen_start; n := n |> in
        (* process roots: *)
      let (roots,state) = gc_move_list conf state roots in
        (* process references: *)
      let state = gc_move_refs conf state in
        (* process rest: *)
      let state = gc_move_loop conf state conf.limit in
      (* let ok = ok0 /\ state.ok /\ *)
      (*          (state.a = conf.gen_start + heap_length state.h1) /\ *)
      (*          (state.r = heap_length state.r1) /\ *)
      (*          (heap_length state.heap = conf.limit) /\ *)
      (*          (state.a + state.n + state.r = conf.limit) /\ *)
      (*          state.a + state.r <= conf.limit in *)
          (roots,state)`;

val full_gc_def = Define `
  full_gc conf (roots,heap) =
    partial_gc
      (conf with <| gen_start := 0; gen_end := conf.limit; refs_start := conf.limit |>)
      (roots,heap)`;

val _ = Datatype `
  data_sort = Protected 'a      (* actually a pointer to an older generation *)
            | Real 'b`;         (* a pointer to current generation/data *)

val to_basic_heap_address_def = Define `
  (to_basic_heap_address gen_start (Data a) = Data (Real a)) /\
  (to_basic_heap_address gen_start (Pointer ptr a) =
    if ptr < gen_start then
      Data (Protected (Pointer ptr a)) else
      Pointer (ptr - gen_start) (Real a))`;

val to_gen_heap_address_def = Define `
  (to_gen_heap_address gen_start (Data (Protected a)) = a) /\
  (to_gen_heap_address gen_start (Data (Real b)) = Data b) /\
  (to_gen_heap_address gen_start (Pointer ptr (Real a)) = Pointer (ptr + gen_start) a)`;

val to_basic_heap_element_def = Define `
  (to_basic_heap_element gen_start (Unused n) = Unused n) /\
  (to_basic_heap_element gen_start (ForwardPointer ptr a l) =
    ForwardPointer (ptr - gen_start) (Real a) l) /\
  (to_basic_heap_element gen_start (DataElement ptrs l d) =
    DataElement (MAP (to_basic_heap_address gen_start) ptrs) l d)`;

val to_basic_heap_def = Define `
  to_basic_heap gen_start heap =
    MAP (to_basic_heap_element gen_start) (heap_drop gen_start heap)`;

val to_basic_state_def = Define `
  to_basic_state gen_start state =
    empty_state with
    <| h1 := MAP (to_basic_heap_element gen_start) state.h1
     ; h2 := MAP (to_basic_heap_element gen_start) state.h2
     ; r4 := MAP (to_basic_heap_element gen_start) state.r4
     ; r3 := MAP (to_basic_heap_element gen_start) state.r3
     ; r2 := MAP (to_basic_heap_element gen_start) state.r2
     ; r1 := MAP (to_basic_heap_element gen_start) state.r1
     ; a := state.a - gen_start
     ; n := state.n
     ; ok := state.ok
     ; heap := to_basic_heap gen_start state.heap
     ; heap0 := to_basic_heap gen_start state.heap0
     |>`;

val roots_filter_def = Define `
  (roots_filter gen_start (Data a) = T) /\
  (roots_filter gen_start (Pointer ptr a) = ptr < gen_start)`;

val roots_shift_def = Define `
  (roots_shift gen_start (Data a) = Data (Real a)) /\
  (roots_shift gen_start (Pointer ptr a) = Pointer (ptr - gen_start) (Real a))`;

val to_basic_roots_def = Define `
  to_basic_roots gen_start roots =
    MAP (roots_shift gen_start) (FILTER (roots_filter gen_start) roots)`;

val simulation = prove
  ``(basic_gc conf
      (to_basic_roots conf.gen_start roots:'a heap_address list
      ,to_basic_heap conf.gen_start heap) = (roots',state')) ==>
    ?roots'' state''.
      (partial_gc conf (roots, heap) = (roots'',state'')) /\
      (roots' = to_basic_roots roots'') /\
      (state' = to_basic_state state'')``,
  cheat);

(*
- basic_gc_related
1 simulering: from_gen_..., m cheat
2 partial_gc_related, m antagande om pointers i fel riktigt (generationer)
 *)


val full_gc_related = store_thm("full_gc_related",
  ``roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) conf.limit ==>
    ?state f.
      (full_gc conf (roots:'a heap_address list,heap) =
         (ADDR_MAP (FAPPLY f) roots,state.h1,state.r1,state.a,state.r,T)) /\
      (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM f) /\
      gc_related f heap (state.h1 ++ heap_expand state.n ++ state.r1)``,
  cheat);


val _ = export_theory();
