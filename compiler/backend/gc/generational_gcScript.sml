open preamble wordsTheory wordsLib integer_wordTheory gc_sharedTheory basic_gcTheory;

val _ = new_theory "generational_gc";

val gc_state_component_equality = DB.fetch "gc_shared" "gc_state_component_equality";

val _ = Datatype `
  gen_gc_conf =
    <| limit : num              (* size of heap *)
     ; isRef : 'a -> bool
     ; gen_start : num          (* start of generation *)
     ; gen_end : num            (* end of generation *)
     ; refs_start : num         (* start of references, gen_end < refs_start *)
     |>`;

val gc_move_def = Define `
  (gc_move conf state (Data d) = (Data d, state)) /\
  (gc_move conf state (Pointer ptr d) =
     if ptr < conf.gen_start \/ conf.refs_start <= ptr then
       (Pointer ptr d,state) else
     case heap_lookup ptr state.heap of
     | SOME (DataElement xs l dd) =>
       let ok = state.ok /\ l+1 <= state.n in
       let n = state.n - (l + 1) in
        if conf.isRef dd then
          let r4 = (DataElement xs l dd) :: state.r4 in
          let (heap,ok) = gc_forward_ptr ptr state.heap (state.a + n) d ok in
            (Pointer (state.a + n) d
            ,state with <| r4 := r4; n := n; heap := heap; ok := ok |>)
        else
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
    (state.old = state'.old) /\
    (state.h1 = state'.h1) /\
    (state.r3 = state'.r3) /\
    (state.r2 = state'.r2) /\
    (state.r1 = state'.r1)``,
  Cases
  \\ fs [gc_move_def]
  \\ ntac 3 strip_tac
  \\ IF_CASES_TAC >- fs [gc_state_component_equality]
  \\ strip_tac
  \\ fs []
  \\ Cases_on `heap_lookup n state.heap`
  \\ fs [gc_state_component_equality]
  \\ Cases_on `x`
  \\ fs [LET_THM,gc_state_component_equality]
  \\ pairarg_tac
  \\ fs []
  \\ Cases_on `conf.isRef b`
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
    (LENGTH xs = LENGTH xs') /\
    (state.old = state'.old) /\
    (state.h1 = state'.h1) /\
    (state.r3 = state'.r3) /\
    (state.r2 = state'.r2) /\
    (state.r1 = state'.r1)``,
  Induct
  \\ fs [gc_move_list_def,LET_THM]
  \\ ntac 5 strip_tac
  \\ pairarg_tac
  \\ Cases_on `xs'`
  \\ fs []
  \\ pairarg_tac \\ fs []
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

val gc_move_data_consts = prove(
  ``!state state'.
    (gc_move_data conf state = state') ==>
    (state.old = state'.old) /\
    (state.r1 = state'.r1)
  ``,
  cheat);
  (* rpt gen_tac *)
  (* \\ Induct_on `state.h2` \\ fs [] *)
  (* \\ once_rewrite_tac [gc_move_data_def] *)
  (* \\ rpt strip_tac *)
  (* \\ qpat_x_assum `_ = state.h2` (assume_tac o GSYM) *)
  (* \\ fs [] *)
  (* \\ Cases_on `conf.limit < heap_length (state.h1 ++ h::v)` \\ fs [] *)
  (* >- fs [gc_state_component_equality] *)
  (* \\ Cases_on `h` \\ fs [] *)
  (* >- fs [gc_state_component_equality] *)
  (* >- fs [gc_state_component_equality] *)
  (* \\ pairarg_tac \\ fs [] *)
  (* \\ drule gc_move_list_consts \\ strip_tac *)
  (* \\ res_tac *)


val gc_move_ref_list_def = Define `
  (gc_move_ref_list conf state [] = ([], state)) /\
  (gc_move_ref_list conf state (DataElement ptrs l d::xs) =
    let (ptrs', state) = gc_move_list conf state ptrs in
    let (xs,state) = gc_move_ref_list conf state xs in
      (DataElement ptrs' l d::xs,state)) /\
  (gc_move_ref_list conf state (x::xs) = (x::xs,state with ok := F))`;

val partial_gc_def = Define `
  partial_gc conf (roots,heap) =
    let ok0 = (heap_length heap = conf.limit) in
    case heap_segment (conf.gen_start,conf.refs_start) heap of
    | NONE => (roots,empty_state with <| ok := F |>)
    | SOME (old,current,refs) =>
      let n = heap_length current in
      let state = empty_state
          with <| heap := heap
                ; old := old
                ; r2 := refs
                ; a := conf.gen_start; n := n |> in
        (* process roots: *)
      let (roots,state) = gc_move_list conf state roots in
        (* process references: *)
      let (refs',state) = gc_move_ref_list conf state refs in
        (* process rest: *)
      let state = gc_move_data conf (state with r1 := refs') in
      (* let ok = ok0 /\ state.ok /\ *)
      (*          (state.a = conf.gen_start + heap_length state.h1) /\ *)
      (*          (state.r = heap_length state.r1) /\ *)
      (*          (heap_length state.heap = conf.limit) /\ *)
      (*          (state.a + state.n + state.r = conf.limit) /\ *)
      (*          state.a + state.r <= conf.limit in *)
      (roots,state)`;

(* Pointers between current and old generations are correct *)
val heap_gen_ok_def = Define `
  heap_gen_ok heap conf =
    ?old current refs.
      (SOME (old, current, refs) = heap_segment (conf.gen_start, conf.refs_start) heap) /\
      (* old points only to itself and references *)
      (!ptr xs l d u. MEM (DataElement xs l d) old /\ MEM (Pointer ptr u) xs ==>
        (ptr < conf.gen_start \/ conf.refs_start <= ptr)) /\
      (* old contains no references *)
      (!xs l d. MEM (DataElement xs l d) old ==> ~ (conf.isRef d)) /\
      (* refs only contains references *)
      (!xs l d. MEM (DataElement xs l d) refs ==> conf.isRef d)`;

val _ = Datatype `
  data_sort = Protected 'a      (* pointer to old generations *)
            | Real 'b`;         (* data or pointer to current generation *)

val to_basic_heap_address_def = Define `
  (to_basic_heap_address conf (Data a) = Data (Real a)) /\
  (to_basic_heap_address conf (Pointer ptr a) =
    if ptr < conf.gen_start then
      Data (Protected (Pointer ptr a))
    else if conf.refs_start <= ptr then
      Data (Protected (Pointer ptr a))
    else
      Pointer (ptr - conf.gen_start) (Real a))`;

(* val to_gen_heap_address_def = Define ` *)
(*   (to_gen_heap_address gen_start (Data (Protected a)) = a) /\ *)
(*   (to_gen_heap_address gen_start (Data (Real b)) = Data b) /\ *)
(*   (to_gen_heap_address gen_start (Pointer ptr (Real a)) = Pointer (ptr + gen_start) a)`; *)

val to_basic_conf_def = Define `
  to_basic_conf (conf:'a gen_gc_conf) =
    <| limit := conf.limit - conf.gen_start - (conf.limit - conf.refs_start)
     ; isRef := conf.isRef |>
     : 'a basic_gc_conf`;

val to_basic_heap_element_def = Define `
  (to_basic_heap_element conf (Unused n) = Unused n) /\
  (to_basic_heap_element conf (ForwardPointer ptr a l) =
    ForwardPointer (ptr - conf.gen_start) (Real a) l) /\
  (to_basic_heap_element conf (DataElement ptrs l d) =
    DataElement (MAP (to_basic_heap_address conf) ptrs) l d)`;

val to_basic_heap_list_def = Define `
  to_basic_heap_list conf heap =
    MAP (to_basic_heap_element conf) heap`;

val to_basic_heap_def = Define `
  to_basic_heap conf heap =
    to_basic_heap_list conf
        (heap_restrict conf.gen_start conf.refs_start heap)`;

val to_basic_state_def = Define `
  to_basic_state conf state =
    empty_state with
    <| h1 := to_basic_heap_list conf state.h1
     ; h2 := to_basic_heap_list conf state.h2
     ; r4 := []
     ; r3 := []
     ; r2 := []
     ; r1 := []
     ; a := state.a - conf.gen_start
     ; n := state.n
     ; ok := state.ok
     ; heap := to_basic_heap conf state.heap
     ; heap0 := to_basic_heap conf state.heap0
     |>`;

val to_basic_roots_def = Define `
  to_basic_roots conf roots =
    MAP (to_basic_heap_address conf) roots`;

(* val r2r_filter_def = Define ` *)
(*   (r2r_filter (Pointer _ _) = T) /\ *)
(*   (r2r_filter _ = F)`; *)

val refs_to_roots_def = Define `
  (refs_to_roots conf [] = []) /\
  (refs_to_roots conf (DataElement ptrs _ _::refs) =
    MAP (to_basic_heap_address conf) ptrs ++ refs_to_roots conf refs) /\
  (refs_to_roots conf (_::refs) = refs_to_roots conf refs)`;

(*

     GenGC     GC
inp    o ----> o
       |       |
       |       |
       v       v
out    o ----> o

last step: need a relation <---
 *)

val heap_element_is_ref_def = Define `
  (heap_element_is_ref conf (DataElement xs l d) = conf.isRef d) /\
  (heap_element_is_ref conf _ = F)`;

val gen_inv_def = Define `
  gen_inv (conf:'b gen_gc_conf) heap =
    conf.gen_start <= conf.refs_start /\
    conf.refs_start <= conf.limit /\
    ?heap_old heap_current heap_refs.
    (heap_segment (conf.gen_start,conf.refs_start) heap = SOME (heap_old,heap_current,heap_refs)) /\
    EVERY (λe. ¬heap_element_is_ref conf e) heap_old /\
    EVERY (λe. ¬heap_element_is_ref conf e) heap_current`;

(* always rewrite with gen_inv_def *)
val _ = augment_srw_ss [rewrites [gen_inv_def]];

val gc_move_simulation = prove(
  ``!ptr ptr' state state'.
      gen_inv conf state.heap /\
      (gc_move conf state ptr = (ptr', state')) ==>
      (gen_inv conf state'.heap) /\
      (basic_gc$gc_move
         (to_basic_conf conf)
         (to_basic_state conf state)
         (to_basic_heap_address conf ptr)
       = (to_basic_heap_address conf ptr', to_basic_state conf state'))``,
  reverse Cases
  \\ fs []
  \\ rpt gen_tac
  \\ strip_tac
  \\ fs [to_basic_heap_address_def]
  >- (fs [gc_move_def,basic_gcTheory.gc_move_def]
     \\ rveq
     \\ fs [to_basic_heap_address_def])
  \\ fs []
  \\ IF_CASES_TAC
  >- (fs [gc_move_def,basic_gcTheory.gc_move_def]
     \\ rveq
     \\ fs [to_basic_heap_address_def])
  \\ IF_CASES_TAC
  >- (fs [gc_move_def,basic_gcTheory.gc_move_def]
     \\ rveq
     \\ fs [to_basic_heap_address_def])
  \\ fs [gc_move_def,basic_gcTheory.gc_move_def]
  \\ strip_tac >- cheat
  \\ BasicProvers.TOP_CASE_TAC \\ fs []
  >- (`heap_lookup n state.heap = NONE` by all_tac
     >- (pop_assum mp_tac
        \\ fs [to_basic_state_def,to_basic_heap_def,heap_restrict_def]
        \\ fs [heap_lookup_def]
        \\ cheat
     )
     \\ cheat
  )
  \\ cheat
  );

val gc_move_list_simulation = prove(
  ``!conf state xs state' xs'.
    (gc_move_list conf state xs = (xs', state')) ==>
    (basic_gc$gc_move_list (to_basic_conf conf) (to_basic_state conf state)
                           (MAP (to_basic_heap_address conf) xs)
    = (MAP (to_basic_heap_address conf) xs', to_basic_state conf state'))``,
  cheat);

val gc_move_list_simulation = prove(
  ``!state0 roots0 roots1 state1.
    (gc_move_list conf state0 roots0 = (roots1,state1))
    ==>
    (gc_move_list (to_basic_conf conf)
      (to_basic_state conf state0) (to_basic_roots conf roots0) =
        (to_basic_roots conf roots1,to_basic_state conf state1))``,
  cheat);

val gc_move_list_APPEND = prove(
  ``!conf state0 xs ys roots' state'.
  (basic_gc$gc_move_list conf state0 (xs ++ ys) = (roots',state')) ==>
  ?roots1 roots2 state1.
  (basic_gc$gc_move_list conf state0 xs = (roots1,state1)) /\
  (basic_gc$gc_move_list conf state1 ys = (roots2,state')) /\
  (roots' = roots1 ++ roots2)``,
  cheat);

val heap_restrict_NIL = store_thm("heap_restrict_NIL[simp]",
  ``heap_restrict gen_start refs_start [] = []``,
  cheat);

val to_basic_heap_NIL = store_thm("to_basic_heap_NIL[simp]",
  ``to_basic_heap conf [] = []``,
  cheat);

val to_basic_heap_list_NIL = store_thm("to_basic_heap_list_NIL[simp]",
  ``to_basic_heap_list conf [] = []``,
  cheat);

val gc_move_list_refs_lemma = prove(
  ``!state state1.
    (gc_move_refs conf state = state1) ==>
    (gc_move_list (to_basic_conf conf) (to_basic_state conf state)
        (refs_to_roots conf state.r2) =
     (refs_to_roots conf state1.r1,to_basic_state conf state1))
  ``,
  cheat) |> SIMP_RULE std_ss [];

val partial_gc_simulation = prove(
  ``!roots heap0 roots1 state1 heap0_old heap0_current heap0_refs.
    (partial_gc conf (roots,heap0) = (roots1,state1)) /\
    heap_gen_ok heap0 conf /\
    conf.gen_start ≤ conf.refs_start ∧ conf.refs_start ≤ conf.limit /\
    (SOME (heap0_old,heap0_current,heap0_refs) =
      heap_segment (conf.gen_start,conf.refs_start) heap0) /\
    EVERY (\e. ~(heap_element_is_ref conf e)) (heap0_old ++ heap0_current) /\
    roots_ok roots heap0 /\
    heap_ok heap0 conf.limit ==>
    ?refs refs1.
    (refs = refs_to_roots conf heap0_refs) /\
    (refs1 = refs_to_roots conf state1.r1) /\
    (basic_gc (to_basic_conf conf)
              (to_basic_roots conf roots ++ refs,
               to_basic_heap_list conf heap0_current)
     = (to_basic_roots conf roots1 ++ refs1,
       to_basic_state conf state1))``,

  rpt strip_tac
  \\ fs []
  \\ fs [basic_gc_def]
  \\ pairarg_tac \\ fs []
  \\ qpat_x_assum `SOME _ = _` (assume_tac o GSYM)
  \\ fs [partial_gc_def]
  \\ pairarg_tac \\ fs []
  \\ rveq
  \\ drule gc_move_list_APPEND
  \\ strip_tac \\ fs []
  \\ rveq
  \\ drule gc_move_list_simulation
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac `gc_move_list _ s5`
  \\ qmatch_asmsub_abbrev_tac `basic_gc$gc_move_list _ s6 _ = (roots1,state1)`
  \\ `to_basic_state conf s5 = s6` by all_tac
  >- (unabbrev_all_tac
     \\ fs [to_basic_state_def,empty_state_def]
     \\ fs [to_basic_heap_def,to_basic_conf_def,heap_restrict_def]
     \\ drule heap_segment_IMP \\ fs [])
  \\ fs []
  \\ rveq
  (* \\ pop_assum kall_tac *)
  \\ qabbrev_tac `moved = gc_move_data conf (gc_move_refs conf state')`
  \\ qabbrev_tac `roots_refs = gc_move_refs conf state'`
  \\ `roots_refs.r1 = moved.r1` by all_tac
  >- (qpat_x_assum `Abbrev (moved = _)` mp_tac
     \\ rewrite_tac [markerTheory.Abbrev_def]
     \\ disch_then (assume_tac o GSYM)
     \\ drule gc_move_data_consts
     \\ strip_tac \\ rveq)
  \\ fs []
  \\ qspec_then `state'` mp_tac gc_move_list_refs_lemma
  (* nar assumptions pa gc_move_list_refs_lemma sa impl_tac *)
  \\ strip_tac
  \\ `state'.r2 = heap0_refs` by all_tac
  >- (qspecl_then [`roots`,`roots''`] mp_tac gc_move_list_consts
     \\ disch_then drule \\ strip_tac \\ fs []
     \\ unabbrev_all_tac
     \\ fs [gc_state_component_equality])
  \\ rveq
  \\ fs []
  \\ qunabbrev_tac `moved`
  \\ once_rewrite_tac [basic_gcTheory.gc_move_loop_def]

  \\ cheat);

val f_old_ptrs_def = Define `
  f_old_ptrs conf heap =
    {a | isSomeDataElement (heap_lookup a heap)
         /\ (a < conf.gen_start \/ conf.refs_start <= a)}`;

val heap_lookup_heap_length_NONE = prove(
  ``!heap. heap_lookup (heap_length heap) heap = NONE``,
  cheat);

val heap_lookup_heap_length_GT_NONE = prove(
  ``!heap x. heap_length heap < x ==> (heap_lookup x heap = NONE)``,
  cheat);

val f_old_ptrs_finite = store_thm("f_old_ptrs_finite[simp]",
  ``!heap conf.
    FINITE (f_old_ptrs conf heap)``,
  rpt strip_tac
  \\ match_mp_tac (MP_CANON SUBSET_FINITE)
  \\ qexists_tac `{a | isSomeDataElement (heap_lookup a heap)}`
  \\ reverse CONJ_TAC
  >- fs [f_old_ptrs_def,SUBSET_DEF]
  \\ qspec_tac (`heap`,`heap`)
  \\ ho_match_mp_tac SNOC_INDUCT
  \\ rw []
  >- fs [heap_lookup_def,isSomeDataElement_def]
  \\ reverse
     (`?y. FINITE y /\
          ({a | isSomeDataElement (heap_lookup a (SNOC x heap))} =
           y UNION {a | isSomeDataElement (heap_lookup a heap)})` by all_tac)
  >- fs []
  \\ fs [SNOC_APPEND]
  \\ fs [heap_lookup_APPEND]
  \\ Cases_on `x`
  \\ TRY (qexists_tac `{}`
     \\ fs []
     \\ fs [EXTENSION,heap_lookup_def]
     \\ rw [isSomeDataElement_def]
     \\ CCONTR_TAC
     \\ fs []
     \\ imp_res_tac heap_lookup_LESS
     \\ fs []
     \\ NO_TAC)
  \\ qexists_tac `{heap_length heap}`
  \\ fs []
  \\ fs [EXTENSION]
  \\ rw []
  \\ Cases_on `x = heap_length heap` \\ fs []
  \\ fs [heap_lookup_def,isSomeDataElement_def]
  \\ CCONTR_TAC
  \\ fs []
  \\ imp_res_tac heap_lookup_LESS);

val new_f_def = Define `
  new_f f conf heap =
    FUNION (FUN_FMAP I (f_old_ptrs conf heap))
           (FUN_FMAP (\a. conf.gen_start + f ' (a - conf.gen_start))
                     (IMAGE ((+) conf.gen_start) (FDOM f)))`;

val APPEND_LENGTH_IMP = prove(
  ``!a c b d.
    ((a ++ b) = (c ++ d)) /\ (LENGTH a = LENGTH c) ==>
    (a = c) /\ (b = d)``,
  Induct >- (Cases \\ fs [])
  \\ strip_tac
  \\ Cases \\ fs []
  \\ rpt strip_tac \\ res_tac);

val roots_ok_CONS = prove(
  ``!h t.
    roots_ok (h::t) heap ==>
    roots_ok t heap``,
  fs [roots_ok_def] \\ rpt strip_tac \\ res_tac);

val roots_ok_simulation = prove(
  ``!heap roots heap_old heap_current heap_refs (conf :'b gen_gc_conf).
    roots_ok roots (heap :('a,'b) heap_element list) /\
    (heap_segment (conf.gen_start,conf.refs_start) heap = SOME (heap_old,heap_current,heap_refs))
    ==>
    roots_ok
      (to_basic_roots conf roots ++ refs_to_roots conf heap_refs)
      (MAP (to_basic_heap_element conf) heap_current)``,
  cheat);

val heap_ok_simulation = prove(
  ``!heap heap_old heap_current heap_refs (conf :'b gen_gc_conf).
    heap_ok (heap :('a,'b) heap_element list) conf.limit /\
    (heap_segment (conf.gen_start,conf.refs_start) heap = SOME (heap_old,heap_current,heap_refs))
    ==>
    heap_ok
      (MAP (to_basic_heap_element conf) heap_current)
      (to_basic_conf conf).limit``,
  cheat);

val new_f_FDOM = prove(``
  x IN FDOM (new_f f conf heap) =
  if x < conf.gen_start ∨ conf.refs_start ≤ x then
  isSomeDataElement (heap_lookup x heap) else
  x IN (IMAGE ($+ conf.gen_start) (FDOM f))``,
  fs [new_f_def]
  \\ IF_CASES_TAC
  \\ fs [f_old_ptrs_def]
  \\
  cheat);

val new_f_FAPPLY = prove(
  ``x ∈ FDOM (new_f f conf heap) ==>
    (new_f f conf heap ' x =
    if x < conf.gen_start ∨ conf.refs_start ≤ x then
    x else
    conf.gen_start + f ' (x − conf.gen_start))``,
  fs [new_f_def]
  \\ strip_tac
  >- (fs [FUNION_DEF]
     \\ fs [FUN_FMAP_DEF]
     \\ fs [f_old_ptrs_def])
  \\ fs [FUNION_DEF]
  \\ fs []
  \\ IF_CASES_TAC
  >- (fs [FUN_FMAP_DEF]
     \\  fs [f_old_ptrs_def])
  \\ fs [FUN_FMAP_DEF]
  \\ fs [f_old_ptrs_def]
  \\ IF_CASES_TAC \\ fs []
  \\
  cheat);

val to_basic_heap_list_heap_length = store_thm("to_basic_heap_list_heap_length[simp]",
  ``heap_length (to_basic_heap_list conf h2) = heap_length h2``,
  rewrite_tac [to_basic_heap_list_def]
  \\ Induct_on `h2`
  \\ fs [heap_length_def]
  \\ Cases
  \\ fs [to_basic_heap_element_def]
  \\ fs [el_length_def]);

val isSomeDataElement_heap_lookup_heap_expand
  = store_thm("isSomeDataElement_heap_lookup_heap_expand[simp]",
  ``~isSomeDataElement (heap_lookup x (heap_expand n))``,
  rewrite_tac [heap_expand_def]
  \\ Cases_on `n` \\ fs []
  \\ fs [heap_lookup_def,isSomeDataElement_def]);

val isSomeDataElement_to_basic_heap_list
  = store_thm("isSomeDataElement_to_basic_heap_list[simp]",
  ``!n heap.
    isSomeDataElement (heap_lookup n (to_basic_heap_list conf heap))
    = isSomeDataElement (heap_lookup n heap)``,
  rewrite_tac [to_basic_heap_list_def]
  \\ Induct_on `heap`
  >- fs [heap_lookup_def,isSomeDataElement_def]
  \\ Cases \\ strip_tac
  \\ rpt
     (fs [heap_lookup_def,to_basic_heap_element_def]
     \\ IF_CASES_TAC >- fs [isSomeDataElement_def]
     \\ simp []
     \\ IF_CASES_TAC
     \\ fs [el_length_def]
     \\ fs [isSomeDataElement_def]));

val partial_gc_IMP = prove(
  ``!roots heap roots1 state1 heap_old heap_current heap_refs.
    (partial_gc conf (roots,heap) = (roots1,state1)) /\
    (heap_segment (conf.gen_start,conf.refs_start) heap =
      SOME (heap_old,heap_current,heap_refs)) ==>
    (state1.old = heap_old) /\
    (heap_length state1.r1 = heap_length heap_refs)
  ``,
  cheat);

val heap_lookup_old_IMP = prove(
  ``!i ys.
    (partial_gc conf (roots,heap) = (roots1,state1)) /\
    gen_inv conf heap /\
    (heap_lookup i heap = SOME (DataElement xs l d)) /\
    (i < conf.gen_start) ==>
    (heap_lookup i (state1.old ++ ys) = SOME (DataElement xs l d))``,
  fs [] \\ rpt strip_tac
  \\ drule partial_gc_IMP
  \\ fs [] \\ strip_tac \\ fs []
  \\ drule heap_segment_IMP
  \\ fs []
  \\ strip_tac
  \\ qpat_x_assum `_ = heap` (assume_tac o GSYM)
  \\ qpat_x_assum `_ = conf.gen_start` (assume_tac o GSYM)
  \\ fs []
  \\ rewrite_tac [GSYM APPEND_ASSOC]
  \\ drule LESS_IMP_heap_lookup
  \\ disch_then (qspec_then `heap_current ++ heap_refs` assume_tac)
  \\ fs []
  \\ drule LESS_IMP_heap_lookup
  \\ rewrite_tac [GSYM APPEND_ASSOC]
  \\ metis_tac []);

val heap_lookup_old_IMP_ALT = prove(
  ``!ys.
    (partial_gc conf (roots,heap) = (roots1,state1)) /\
    gen_inv conf heap /\
    isSomeDataElement (heap_lookup x heap) /\
    (x < conf.gen_start) ==>
    isSomeDataElement (heap_lookup x (state1.old ++ ys))``,
  metis_tac [isSomeDataElement_def,heap_lookup_old_IMP]);

val heap_lookup_refs_IMP = prove(
  ``(partial_gc conf (roots,heap) = (roots1,state1)) /\
    gen_inv conf heap /\
    (heap_lookup x heap = SOME (DataElement xs l d)) /\
    (conf.refs_start ≤ x)
    ==>
    (heap_lookup x (state1.old ++ state1.h1 ++ heap_expand state1.n ++ state1.r1) =
      SOME (DataElement (ADDR_MAP f xs) l d))
  ``,
    cheat);

val heap_lookup_refs_IMP_ALT = prove(
  ``(partial_gc conf (roots,heap) = (roots1,state1)) /\
    gen_inv conf heap /\
    isSomeDataElement (heap_lookup x heap) /\
    (conf.refs_start ≤ x)
    ==>
    isSomeDataElement (heap_lookup x (state1.old ++ state1.h1 ++ heap_expand state1.n ++ state1.r1))``,
    metis_tac [isSomeDataElement_def,heap_lookup_refs_IMP]);

val ADDR_MAP_ID = prove(
  ``(!x u. MEM (Pointer x u) xs ==> (x = f x))
    ==> (xs = ADDR_MAP f xs)``,
  Induct_on `xs`
  \\ fs [ADDR_MAP_def]
  \\ Cases
  \\ fs [ADDR_MAP_def]
  \\ metis_tac []);

val heap_lookup_IMP_MEM = store_thm("heap_lookup_IMP_MEM",
  ``!xs x i. (heap_lookup i xs = SOME x) ==> MEM x xs``,
  Induct
  \\ fs [heap_lookup_def]
  \\ Cases
  \\ rpt
     (rpt gen_tac
     \\ IF_CASES_TAC
     >- fs []
     \\ IF_CASES_TAC
     >- fs []
     \\ metis_tac []));

val MEM_heap_old = prove(
  ``!n m i x.
    (heap_segment (n,m) heap = SOME (heap_old,heap_current,heap_refs)) /\
    (n <= m) /\
    i < n /\
    (heap_lookup i heap = SOME x)
    ==>
    MEM x heap_old``,
  rpt strip_tac
  \\ drule heap_segment_IMP
  \\ disch_then drule
  \\ rpt strip_tac
  \\ rveq
  \\ fs []
  \\ drule LESS_IMP_heap_lookup
  \\ metis_tac [heap_lookup_IMP_MEM,GSYM APPEND_ASSOC]);

val partial_gc_IMP_heap_length = prove(
  ``(partial_gc conf (roots,heap) = (roots1,state1)) /\
    gen_inv conf heap ==>
    (heap_length state1.old = heap_length state.old) /\
    (heap_length state1.r1 = conf.limit - conf.refs_start) /\
    (heap_length (heap_drop conf.gen_start state1.h1) = heap_length state1.h1 - conf.gen_start)
  ``,
  cheat);

val FILTER_isForward_to_basic = prove(
  ``!xs.
    (FILTER isForwardPointer (to_basic_heap_list conf xs) = []) ==>
    (FILTER isForwardPointer xs = [])``,
  cheat);

val isSomeDataElement_to_basic = prove(
  ``!xs f x' n conf.
    isSomeDataElement (heap_lookup (f ' x') (to_basic_heap_list conf xs ++ heap_expand n))
    ==>
    isSomeDataElement (heap_lookup (f ' x') (xs ++ heap_expand n))``,
  cheat);

val partial_gc_related = store_thm("partial_gc_related",
  ``roots_ok roots heap /\
    heap_ok (heap:('a,'b) heap_element list) conf.limit /\
    heap_gen_ok heap conf /\
    gen_inv conf heap
    ==>
    ?state f.
      (partial_gc conf (roots:'a heap_address list,heap) =
         (ADDR_MAP (FAPPLY f) roots,state)) /\
      (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM f) /\
      (heap_ok (state.old ++ state.h1 ++ heap_expand state.n ++ state.r1) conf.limit) /\
      gc_related f heap (state.old ++ state.h1 ++ heap_expand state.n ++ state.r1)``,

  rpt strip_tac
  \\ fs []
  \\ Cases_on `partial_gc conf (roots,heap)` \\ fs []
  \\ rename1 `_ = (roots1,state1)`
  \\ drule partial_gc_simulation
  \\ fs []
  \\ strip_tac
  \\ drule roots_ok_simulation
  \\ disch_then drule \\ strip_tac
  \\ drule heap_ok_simulation
  \\ fs []
  (* \\ qispl_then [`heap`,`roots`,`heap_old`,`heap_current`,`heap_refs`,`conf`] *)
  (*      mp_tac heap_ok_simulation *)
  (* \\ ntac 2 (disch_then drule) *)
  \\ strip_tac
  \\ qabbrev_tac `basic_roots = to_basic_roots conf roots ++ refs_to_roots conf heap_refs`
  \\ qabbrev_tac `basic_heap = MAP (to_basic_heap_element conf) heap_current`
  \\ drule basic_gc_related
  \\ disch_then drule
  (* \\ qispl_then [`to_basic_conf conf`,`basic_roots`,`basic_heap`] mp_tac basic_gc_related *)
  \\ fs []
  \\ strip_tac \\ fs []
  \\ qexists_tac `new_f f conf heap`
  \\ fs [to_basic_heap_list_def]

  \\ strip_tac    (* (roots1 = ADDR_MAP ($' (new_f f conf heap)) roots) *)
  >- (fs [gc_related_def]
     \\ qunabbrev_tac `basic_roots`
     \\ fs [ADDR_MAP_APPEND]
     \\ qpat_x_assum `ADDR_MAP _ _ ++ _ = _` mp_tac
     \\ strip_tac
     \\ drule APPEND_LENGTH_IMP
     \\ impl_tac
     >- (fs [GSYM ADDR_MAP_LENGTH]
        \\ fs [to_basic_roots_def]
        \\ fs [partial_gc_def]
        \\ rfs []
        \\ pairarg_tac \\ fs []
        \\ drule gc_move_list_consts
        \\ metis_tac [])
     \\ strip_tac
     \\ pop_assum kall_tac
     \\ pop_assum mp_tac
     \\ simp [to_basic_roots_def]
     \\ qpat_x_assum `roots_ok _ _` kall_tac
     \\ qpat_x_assum `roots_ok _ _` mp_tac
     \\ qpat_x_assum `!ptr u. _ ==> ptr IN FDOM f` mp_tac
     \\ qspec_tac (`roots`, `roots`)
     \\ qspec_tac (`roots1`, `roots1`)
     \\ Induct
     >- (Cases
        \\ strip_tac
        >- fs [ADDR_MAP_def]
        \\ rpt strip_tac
        \\ fs [MAP]
        \\ Cases_on `to_basic_heap_address conf h`
        \\ fs [ADDR_MAP_def])
     \\ reverse Cases
     >- (Cases \\ ntac 2 strip_tac
        >- (fs [to_basic_heap_address_def]
           \\ rpt (IF_CASES_TAC >- fs [ADDR_MAP_def])
           \\ fs [ADDR_MAP_def])
        \\ Cases_on `h`
        \\ fs [to_basic_heap_address_def,ADDR_MAP_def]
        >- (rpt (IF_CASES_TAC >- fs [ADDR_MAP_def])
           \\ fs [ADDR_MAP_def])
        \\ rpt strip_tac
        \\ rveq
        \\ drule roots_ok_CONS
        \\ strip_tac
        \\ fs [to_basic_roots_def]
        \\ metis_tac [])
     \\ Cases
     \\ ntac 2 strip_tac
     \\ fs [ADDR_MAP_def]
     \\ reverse (Cases_on `h`)
     >- (fs [to_basic_heap_address_def]
        \\ rpt (IF_CASES_TAC >- fs [ADDR_MAP_def])
        \\ fs [ADDR_MAP_def])
     \\ fs [to_basic_heap_address_def,new_f_def]
     \\ qpat_x_assum `!ptr u. _` mp_tac
     \\ simp [to_basic_roots_def] \\ strip_tac
     \\ rw []
     \\ drule roots_ok_CONS
     \\ fs [ADDR_MAP_def]
     \\ fs [FUNION_DEF]
     \\ fs [FUN_FMAP_DEF]
     >- (`n ∈ f_old_ptrs conf heap` by all_tac
        >- fs [f_old_ptrs_def,roots_ok_def]
        \\ fs []
        \\ metis_tac [to_basic_roots_def])
     >- (`n ∈ f_old_ptrs conf heap` by all_tac
        >- fs [f_old_ptrs_def,roots_ok_def]
        \\ fs []
        \\ metis_tac [to_basic_roots_def])
     \\ `~(n' ∈ f_old_ptrs conf heap)` by all_tac
     >- fs [f_old_ptrs_def,roots_ok_def]
     \\ fs []
     \\ rveq
     \\ strip_tac
     \\ qispl_then [`(\a. conf.gen_start + f ' (a − conf.gen_start))`] mp_tac FUN_FMAP_DEF
     \\ disch_then (qspec_then `IMAGE ($+ conf.gen_start) (FDOM f)` mp_tac)
     \\ impl_tac
     >- (fs [IMAGE_FINITE,FDOM_FINITE])
     \\ fs []
     \\ disch_then (qspec_then `n'` mp_tac) \\ fs []
     \\ impl_tac
     >- (qexists_tac `n' − conf.gen_start`
        \\ fs []
        \\ first_x_assum match_mp_tac
        \\ fs [to_basic_roots_def,to_basic_heap_address_def]
        \\ metis_tac [])
     \\ fs []
     \\ strip_tac
     \\ fs [AND_IMP_INTRO]
     \\ first_x_assum match_mp_tac
     \\ fs []
     \\ rpt strip_tac
     \\ first_x_assum match_mp_tac
     \\ fs [to_basic_roots_def,to_basic_heap_address_def]
     \\ metis_tac [])

  \\ strip_tac (* ∀ptr u. MEM (Pointer ptr u) roots ⇒ ptr ∈ FDOM (new_f f conf heap) *)
  >- (rpt gen_tac
     \\ fs [new_f_def]
     \\ Cases_on `ptr < conf.gen_start`
     >- (fs [f_old_ptrs_def,roots_ok_def]
        \\ metis_tac [])
     \\ Cases_on `conf.refs_start ≤ ptr`
     >- (fs [f_old_ptrs_def,roots_ok_def]
        \\ metis_tac [])
     \\ fs [f_old_ptrs_def]
     \\ strip_tac
     \\ qexists_tac `ptr - conf.gen_start`
     \\ fs []
     \\ first_x_assum match_mp_tac
     \\ qunabbrev_tac `basic_roots`
     \\ fs [to_basic_roots_def]
     \\ fs [MEM_MAP]
     \\ qexists_tac `Real u`
     \\ disj1_tac
     \\ qexists_tac `Pointer ptr u`
     \\ fs []
     \\ fs [to_basic_heap_address_def])

  \\ strip_tac                  (* heap_ok *)
  >- (drule basic_gc_ok
     \\ disch_then drule
     \\ fs []
     \\ strip_tac
     \\ pop_assum mp_tac
     \\ simp [heap_ok_def]
     \\ strip_tac
     \\ fs [to_basic_conf_def]
     \\ strip_tac               (* heap_length *)
     >- (ntac 2 (first_x_assum kall_tac)
        \\ pop_assum mp_tac
        \\ drule heap_segment_IMP
        \\ fs [] \\ strip_tac \\ fs []
        \\ simp [heap_length_APPEND]
        \\ simp [to_basic_state_def]
        \\ drule partial_gc_IMP \\ fs []
        \\ strip_tac \\ fs []
        \\ fs [heap_length_heap_expand,heap_ok_def])
     \\ strip_tac               (* no ForwardPointers *)
     >- (fs [FILTER_APPEND]
        \\ pop_assum kall_tac
        \\ fs [to_basic_state_def]
        \\ drule FILTER_isForward_to_basic \\ strip_tac
        \\ fs []
        \\ rpt strip_tac
        >- (fs [heap_ok_def]
           \\ drule partial_gc_IMP
           \\ fs [] \\ strip_tac \\ fs []
           \\ drule heap_segment_IMP
           \\ fs [] \\ strip_tac
           \\ rveq
           \\ fs [FILTER_APPEND])
        >- (fs [heap_expand_def]
           \\ IF_CASES_TAC
           \\ fs [isForwardPointer_def])
        \\ fs [partial_gc_def] \\ rfs []
        \\ pairarg_tac \\ fs []
        \\ qpat_x_assum `gc_move_data _ _ = state1` (assume_tac o GSYM)
        \\ simp []              (* refs *)
        \\ cheat)
     \\ rpt gen_tac
     \\ rpt strip_tac
     >- (drule partial_gc_IMP
        \\ fs [] \\ strip_tac \\ fs []
        \\ fs [heap_ok_def]
        \\ cheat
       )
     \\ cheat)
  \\ fs [gc_related_def]

  \\ strip_tac                  (* INJ new_f *)
  >- (fs [INJ_DEF]
     \\ fs [new_f_FAPPLY]
     \\ fs [new_f_FDOM]
     \\ strip_tac
     >- (rpt strip_tac
        \\ Cases_on `x < conf.gen_start` \\ fs []
        >- (drule heap_lookup_old_IMP_ALT
           \\ fs [isSomeDataElement_def]
           \\ metis_tac [GSYM APPEND_ASSOC])
        \\ IF_CASES_TAC \\ fs []
        >- (drule heap_lookup_refs_IMP_ALT
           \\ fs [isSomeDataElement_def])
        \\ `(to_basic_state conf state1).r1 = []` by all_tac
        >- EVAL_TAC
        (* \\ strip_tac *)
        \\ fs []
        \\ qpat_x_assum `!x'. x' IN FDOM f ==> _` drule
        \\ drule heap_segment_IMP
        \\ fs [] \\ strip_tac \\ fs []
        \\ fs [to_basic_state_def]
        \\ strip_tac
        (* \\ qpat_x_assum `_ = state1.h1` (assume_tac o GSYM) *)
        (* \\ qpat_x_assum `heap_length h2 = _` kall_tac *)
        (* \\ qpat_x_assum `heap_length h3 = _` kall_tac *)
        \\ simp []
        \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
        \\ once_rewrite_tac [heap_lookup_APPEND]
        \\ fs [heap_length_APPEND]
        \\ IF_CASES_TAC
        \\ drule partial_gc_IMP
        \\ fs [] \\ strip_tac
        \\ fs []
        \\ once_rewrite_tac [heap_lookup_APPEND]
        \\ IF_CASES_TAC
        >- (cheat)              (* current heap *)
        \\ cheat                (* refs *)
        )
     \\ rpt gen_tac
     \\ IF_CASES_TAC \\ IF_CASES_TAC \\ fs []
     >- (cheat
       )
     >- cheat
     \\ rpt strip_tac
     \\ rveq \\ fs [])

  \\ fs [new_f_FAPPLY]
  \\ fs [new_f_FDOM]
  \\ rpt gen_tac
  \\ strip_tac
  \\ Cases_on `i < conf.gen_start` \\ fs []
  >- (drule heap_lookup_old_IMP
     \\ fs []
     \\ disch_then drule
     \\ fs []
     \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
     \\ strip_tac
     \\ fs [heap_gen_ok_def]
     \\ fs []
     \\ strip_tac
     >- (match_mp_tac ADDR_MAP_ID
        \\ rpt strip_tac
        \\ drule MEM_heap_old
        \\ fs []
        \\ ntac 2 (disch_then drule)
        \\ fs []
        \\ strip_tac
        \\ `x IN FDOM (new_f f conf heap)` by all_tac
        >- (fs [new_f_FDOM]
           \\ reverse IF_CASES_TAC
           >- (res_tac \\ fs [])
           \\ fs [heap_ok_def]
           \\ metis_tac [heap_lookup_IMP_MEM])
        \\ fs [new_f_FAPPLY]
        \\ IF_CASES_TAC \\ fs []
        \\ res_tac \\ fs [])
     \\ rpt strip_tac
     \\ drule MEM_heap_old
     \\ fs []
     \\ disch_then drule \\ fs []
     \\ strip_tac
     \\ IF_CASES_TAC
     >- (`MEM (DataElement xs l d) heap` by all_tac
        >- cheat
        \\ fs [heap_ok_def] \\ metis_tac [])
     \\ fs []
     \\ qexists_tac `ptr - conf.gen_start`
     \\ fs []
     \\ res_tac \\ fs [])

  \\ Cases_on `conf.refs_start ≤ i` \\ fs []
  >- (cheat                     (* hmm, vad skall handa har? *)
     )

  \\ fs [INJ_DEF]
  \\ qpat_x_assum `!x'. x' IN FDOM f ==> _` drule
  \\ fs [isSomeDataElement_def]
  \\ cheat
  );

(* val full_gc_related = store_thm("full_gc_related", *)
(*   ``roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) conf.limit ==> *)
(*     ?state f. *)
(*       (full_gc conf (roots:'a heap_address list,heap) = *)
(*          (ADDR_MAP (FAPPLY f) roots,state)) /\ *)
(*       (heap_ok (state.h1 ++ heap_expand state.n ++ state.r1) conf.limit) /\ *)
(*       (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM f) /\ *)
(*       gc_related f heap (state.h1 ++ heap_expand state.n ++ state.r1)``, *)
(*   cheat); *)


val _ = export_theory();
