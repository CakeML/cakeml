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

(* Pointers between current and old generations are correct *)
val heap_gen_ok_def = Define `
  heap_gen_ok heap conf =
    ?old current refs.
      (SOME (old, current, refs) = heap_segment (conf.gen_start, conf.gen_end) heap) /\
      (* old points only to itself and references *)
      (!ptr xs l d u. MEM (DataElement xs l d) old /\ MEM (Pointer ptr u) xs ==>
        (ptr < conf.gen_start \/ conf.gen_end <= ptr)) /\
      (* old contains no references *)
      (!el. MEM el old ==> ~ (conf.isRef el)) /\
      (* refs only contains references *)
      (!el. MEM el refs ==> conf.isRef el)`;

val _ = Datatype `
  data_sort = Protected 'a      (* actually a pointer to an older generation *)
            | Real 'b`;         (* a pointer to current generation/data *)

val to_basic_heap_address_def = Define `
  (to_basic_heap_address conf (Data a) = Data (Real a)) /\
  (to_basic_heap_address conf (Pointer ptr a) =
    if ptr < conf.gen_start then
      Data (Protected (Pointer ptr a))
    else if conf.refs_start <= ptr then
      Data (Protected (Pointer ptr a))
    else
      Pointer (ptr - conf.gen_start) (Real a))`;

val to_gen_heap_address_def = Define `
  (to_gen_heap_address gen_start (Data (Protected a)) = a) /\
  (to_gen_heap_address gen_start (Data (Real b)) = Data b) /\
  (to_gen_heap_address gen_start (Pointer ptr (Real a)) = Pointer (ptr + gen_start) a)`;

val to_basic_isRef_def = Define `
  (to_basic_isRef isRef (DataElement ptrs n d) =
    isRef (DataElement (MAP (to_gen_heap_address 0) ptrs) n d)) /\
  (to_basic_isRef isRef _ = F)`;

val to_basic_conf_def = Define `
  to_basic_conf (conf:('a,'b) gen_gc_conf) =
    <| limit := conf.limit
     ; isRef := to_basic_isRef conf.isRef |>
     : (('a heap_address, 'a) data_sort, 'b) basic_gc_conf`;

val to_basic_heap_element_def = Define `
  (to_basic_heap_element conf (Unused n) = Unused n) /\
  (to_basic_heap_element conf (ForwardPointer ptr a l) =
    ForwardPointer (ptr - conf.gen_start) (Real a) l) /\
  (to_basic_heap_element conf (DataElement ptrs l d) =
    DataElement (MAP (to_basic_heap_address conf) ptrs) l d)`;

val to_basic_heap_def = Define `
  to_basic_heap conf heap =
    MAP (to_basic_heap_element conf) (heap_drop conf.gen_start heap)`;

val to_basic_state_def = Define `
  to_basic_state conf state =
    empty_state with
    <| h1 := MAP (to_basic_heap_element conf) state.h1
     ; h2 := MAP (to_basic_heap_element conf) state.h2
     ; r4 := MAP (to_basic_heap_element conf) state.r4
     ; r3 := MAP (to_basic_heap_element conf) state.r3
     ; r2 := MAP (to_basic_heap_element conf) state.r2
     ; r1 := MAP (to_basic_heap_element conf) state.r1
     ; a := state.a - conf.gen_start
     ; n := state.n
     ; ok := state.ok
     ; heap := to_basic_heap conf state.heap
     ; heap0 := to_basic_heap conf state.heap0
     |>`;

val roots_shift_def = Define `
  (roots_shift gen_start (Data a) = Data (Real a)) /\
  (roots_shift gen_start (Pointer ptr a) =
    if ptr < gen_start then (Data (Protected (Pointer ptr a)))
    else Pointer (ptr - gen_start) (Real a))`;

val to_basic_roots_def = Define `
  to_basic_roots gen_start roots =
    MAP (roots_shift gen_start) roots`;

val r2r_filter_def = Define `
  (r2r_filter (Pointer _ _) = T) /\
  (r2r_filter _ = F)`;

val refs_to_roots_def = Define `
  (refs_to_roots [] = []) /\
  (refs_to_roots (DataElement ptrs _ _::refs) =
    (FILTER r2r_filter ptrs) ++ refs_to_roots refs) /\
  (refs_to_roots (_::refs) = refs_to_roots refs)`;

val (RootsRefs_def,RootsRefs_ind,RootsRefs_cases) = Hol_reln `
  (RootsRefs [] []) /\
  (!ptrs m b refs roots ptr a ptr' a'.
     RootsRefs (DataElement ptrs m b::refs) roots ==>
     RootsRefs (DataElement (Pointer ptr a::ptrs) m b::refs) (Pointer ptr' a'::roots)) /\
  (!ptrs m b refs roots a.
     RootsRefs (DataElement ptrs m b::refs) roots ==>
     RootsRefs (DataElement (Data a::ptrs) m b::refs) roots) /\
  (!refs roots m b.
     RootsRefs refs roots ==>
     RootsRefs (DataElement [] m b::refs) roots) /\
  (!ptrs m b refs a.
     RootsRefs (DataElement ptrs m b::refs) [] ==>
     RootsRefs (DataElement (Data a::ptrs) m b::refs) []) /\
  (!refs roots n.
     RootsRefs refs roots ==>
     RootsRefs (Unused n::refs) roots) /\
  (!refs roots.
     RootsRefs refs roots ==>
     RootsRefs (ForwardPointer _ _ _::refs) roots)`;

val RootsRefs_related = prove(
  ``!refs. RootsRefs refs (refs_to_roots refs)``,
  Induct
  >- (simp [refs_to_roots_def]
     \\ metis_tac [RootsRefs_cases])
  \\ Cases
  \\ simp [refs_to_roots_def]
  >- metis_tac [RootsRefs_cases]
  >- metis_tac [RootsRefs_cases]
  \\ Induct_on `l`
  \\ simp []
  >- metis_tac [RootsRefs_cases]
  \\ Cases
  >- (simp [r2r_filter_def]
     \\ metis_tac [RootsRefs_cases])
  \\ simp [r2r_filter_def]
  \\ metis_tac [RootsRefs_cases]);

val simulation = prove(
  ``!broots' bstate'.
    let bheap = to_basic_heap conf heap in
    let broots = to_basic_roots conf.gen_start roots ++
                 refs_to_roots (heap_drop conf.refs_start bheap) in
    (basic_gc (to_basic_conf conf) (broots,bheap) = (broots',bstate')) ==>
    ?roots' state'.
      (partial_gc conf (roots, heap) = (roots',state')) /\
      (TAKE (LENGTH roots) broots' = to_basic_roots conf.gen_start roots') /\
      (bstate' = to_basic_state conf state')(*  /\ *)
      (* (RootsRefs (heap_drop conf.refs_start state. (DROP (LENGTH roots) roots')) *)``,
  cheat);

(*
- basic_gc_related
1 simulering: from_gen_..., m cheat
2 partial_gc_related, m antagande om inga pointers i fel riktigt (generationer)
 *)

val fmap_fun_def = Define `
  fmap_fun (f:num |-> num) gen_start heap =
    FUN_FMAP (\n. if n < gen_start then n else $FAPPLY f (n - gen_start) + gen_start)
             ({n | n < gen_start /\ n IN heap_addresses 0 heap}
              UNION IMAGE (\n. n + gen_start) (FDOM f))`;

val fmap_fun_finite = store_thm("fmap_fun_finite[simp]",
  ``FINITE ({n | n < gen_start ∧ n ∈ heap_addresses 0 heap} ∪
           IMAGE (λn'. gen_start + n') (FDOM f))``,
  rewrite_tac [FINITE_UNION]
  \\ fs []
  \\ Induct_on `gen_start`
  \\ fs []
  \\ `{n | n < SUC gen_start ∧ n ∈ heap_addresses 0 heap} =
      if gen_start IN heap_addresses 0 heap
      then gen_start INSERT {n | n < gen_start ∧ n ∈ heap_addresses 0 heap}
      else {n | n < gen_start ∧ n ∈ heap_addresses 0 heap}` by all_tac
  >- (cheat)(* EXTENSION *)
  \\ fs []
  \\ rw []);

val addr_map_take = prove(
  ``!n f xs. TAKE n (ADDR_MAP f xs) = ADDR_MAP f (TAKE n xs)``,
  Induct
  >- fs [TAKE_def,ADDR_MAP_def]
  \\ Cases_on `xs`
  \\ fs [TAKE_def,ADDR_MAP_def]
  \\ Cases_on `h`
  \\ fs [TAKE_def,ADDR_MAP_def]);

val roots_ok_TL = prove(
    ``roots_ok (h::roots) heap ==> roots_ok roots heap``, cheat);

val fmap_fun_LESS_gen_start = prove(
  ``n IN heap_addresses 0 heap /\ n < gen_start ==>
    (fmap_fun f gen_start heap ' n = n)``,
  fs [fmap_fun_def,FUN_FMAP_DEF]);

val partial_gc_related = store_thm("partial_gc_related",
  ``roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) conf.limit /\
    heap_gen_ok heap conf ==>
    ?state f.
      (partial_gc conf (roots:'a heap_address list,heap) =
         (ADDR_MAP (FAPPLY f) roots,state)) /\
      (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM f) /\
      gc_related f heap (state.h1 ++ heap_expand state.n ++ state.r1)``,
  cheat);
  (* rpt strip_tac *)
  (* \\ mp_tac simulation *)
  (* \\ fs [] *)
  (* \\ strip_tac *)
  (* \\ qabbrev_tac `broots = to_basic_roots conf.gen_start roots ++ refs_to_roots (heap_drop conf.refs_start (to_basic_heap conf heap))` *)
  (* \\ qabbrev_tac `bheap = to_basic_heap conf heap` *)
  (* \\ qabbrev_tac `bconf = to_basic_conf conf` *)

  (* \\ `roots_ok broots bheap` by cheat *)
  (* \\ drule basic_gc_related *)
  (* \\ `heap_ok bheap bconf.limit` by cheat *)
  (* \\ disch_then drule *)
  (* \\ rpt strip_tac *)
  (* \\ first_x_assum drule *)
  (* \\ rpt strip_tac *)
  (* \\ fs [] *)
  (* \\ qexists_tac `fmap_fun f conf.gen_start heap` *)
  (* \\ rpt strip_tac *)

  (* >- (qunabbrev_tac `broots` *)
  (*    \\ fs [addr_map_take] *)
  (*    \\ qabbrev_tac `t = to_basic_roots conf.gen_start roots:('a heap_address, 'a) data_sort  heap_address list` *)
  (*    \\ `LENGTH roots = LENGTH t` by cheat *)
  (*    \\ fs [TAKE_LENGTH_APPEND] *)

  (*    \\ qpat_assum `ADDR_MAP _ _ = _` mp_tac *)
  (*    \\ qpat_assum `roots_ok _ _` kall_tac *)
  (*    \\ qpat_assum `roots_ok _ _` mp_tac *)

  (*    \\ qunabbrev_tac `t` *)
  (*    \\ rpt (pop_assum kall_tac) *)
  (*    \\ qspec_tac (`roots'`,`xs`) *)

  (*    \\ Induct_on `roots` *)
  (*    \\ fs [to_basic_roots_def] *)
  (*    \\ fs [ADDR_MAP_def] *)
  (*    \\ reverse Cases *)
  (*    >- cheat *)
  (*    \\ fs [ADDR_MAP_def] *)
  (*    \\ fs [roots_shift_def] *)
  (*    \\ Cases *)
  (*    >- rw [ADDR_MAP_def] *)
  (*    \\ IF_CASES_TAC *)
  (*    >- (rw [ADDR_MAP_def] *)
  (*       \\ Cases_on `h` *)
  (*       \\ fs [roots_shift_def] *)
  (*       \\ every_case_tac \\ fs [] *)
  (*       \\ imp_res_tac roots_ok_TL \\ fs [] *)
  (*       \\ rveq *)
  (*       \\ `n IN heap_addresses 0 heap` by cheat *)
  (*       \\ metis_tac [fmap_fun_LESS_gen_start] *)
  (*       ) *)
  (*       \\ fs [fmap_fun_def] *)

  (*       \\ fs [FUN_FMAP_DEF] *)

val full_gc_related = store_thm("full_gc_related",
  ``roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) conf.limit ==>
    ?state f.
      (full_gc conf (roots:'a heap_address list,heap) =
         (ADDR_MAP (FAPPLY f) roots,state)) /\
      (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM f) /\
      gc_related f heap (state.h1 ++ heap_expand state.n ++ state.r1)``,
  cheat);


val _ = export_theory();
