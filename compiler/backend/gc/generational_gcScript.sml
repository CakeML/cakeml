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
        (* process roots from references: *)
      let state = gc_move_refs conf state in
        (* process rest: *)
      let state = gc_move_loop conf state conf.limit in
      (* let ok = ok0 /\ state.ok /\ *)
      (*          (state.a = conf.gen_start + heap_length state.h1) /\ *)
      (*          (state.r = heap_length state.r1) /\ *)
      (*          (heap_length state.heap = conf.limit) /\ *)
      (*          (state.a + state.n + state.r = conf.limit) /\ *)
      (*          state.a + state.r <= conf.limit in *)
      let state = state with <|h1 := old ++ state.h1|> in
      (roots,state)`; (* TODO: old? *)

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
      (!xs l d. MEM (DataElement xs l d) old ==> ~ (conf.isRef d)) /\
      (* refs only contains references *)
      (!xs l d. MEM (DataElement xs l d) refs ==> conf.isRef d)`;

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

(* val to_basic_isRef_def = Define ` *)
(*   (to_basic_isRef isRef d = *)
(*     isRef (DataElement (MAP (to_gen_heap_address 0) ptrs) n d)) /\ *)
(*   (to_basic_isRef isRef _ = F)`; *)

val to_basic_conf_def = Define `
  to_basic_conf (conf:'a gen_gc_conf) =
    <| limit := conf.limit
     ; isRef := conf.isRef |>
     : 'a basic_gc_conf`;

val to_basic_heap_element_def = Define `
  (to_basic_heap_element conf (Unused n) = Unused n) /\
  (to_basic_heap_element conf (ForwardPointer ptr a l) =
    ForwardPointer (ptr - conf.gen_start) (Real a) l) /\
  (to_basic_heap_element conf (DataElement ptrs l d) =
    DataElement (MAP (to_basic_heap_address conf) ptrs) l d)`;

val restrict_heap_def = Define `
  restrict_heap start end (heap:('a,'b) heap_element list) =
     case heap_segment (start,end) heap of
     | NONE => ARB
     | SOME (h1,h2,h3) => h2`;

val to_basic_heap_list_def = Define `
  to_basic_heap_list conf heap =
    MAP (to_basic_heap_element conf) heap`;

val to_basic_heap_def = Define `
  to_basic_heap conf heap =
    to_basic_heap_list conf
        (restrict_heap conf.gen_start conf.refs_start heap)`;

val to_basic_state_def = Define `
  to_basic_state conf state =
    empty_state with
    <| h1 := to_basic_heap_list conf state.h1
     ; h2 := to_basic_heap_list conf state.h2
     ; r4 := to_basic_heap_list conf state.r4
     ; r3 := to_basic_heap_list conf state.r3
     ; r2 := to_basic_heap_list conf state.r2
     ; r1 := to_basic_heap_list conf state.r1
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

(*

     GenGC     GC
inp    o ----> o
       |       |
       |       |
       v       v
out    o ----> o

last step: need a relation <---
 *)

val gen_inv_def = Define `
  gen_inv (conf:'b gen_gc_conf) heap =
    !h1 h2 h3 (* h10 h20 h30 *).
    (heap_segment (conf.gen_start,conf.refs_start) heap = SOME (h1,h2,h3))(*  /\ *)
    (* (heap_segment (conf.gen_start,conf.refs_start) state.heap0 = SOME (h10,h20,h30)) *)`;

(* val gc_forward_ptr_gen_inv = prove( *)
(*   ``!state state' conf n ptr a ok. *)
(*     gen_inv conf state /\ *)
(*     (gc_forward_ptr n state.heap ptr a state.ok = (heap',ok')) ==> *)
(*     gen_inv conf (state with <|heap:=heap';ok:=ok'|>)``, *)
(*   cheat); *)
(*   (* Induct_on `state.heap` *) *)
(*   (* \\ rw [] *) *)
(*   (* \\ qpat_x_assum `_ = state.heap` (assume_tac o GSYM) \\ fs [] *) *)
(*   (* \\ fs [gc_forward_ptr_def,gen_inv_def] *) *)
(*   (* \\ qpat_x_assum `_ = (heap',ok')` mp_tac *) *)
(*   (* \\ IF_CASES_TAC \\ fs [] *) *)
(*   (* >- (strip_tac *) *)
(*   (*    \\ qpat_x_assum `_ = heap'` (assume_tac o GSYM) \\ fs [] *) *)
(*   (*    \\ rpt strip_tac *) *)
(*   (*    \\ fs [heap_segment_def,heap_split_def,el_length_def] *) *)
(*   (*    \\ fs []) *) *)
(*   (* cheat); *) *)

val gc_move_heap_lookup_lemma = prove(
  ``!heap n conf.
    ¬(n < conf.gen_start) /\
    ¬(conf.refs_start ≤ n) /\
    (heap_lookup (n − conf.gen_start) (to_basic_state conf state).heap
     = OPTION_MAP ()) ==>
    (heap_lookup n state.heap = NONE)

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
  \\ ntac 4 strip_tac
  \\ fs [to_basic_heap_address_def]
  >- (fs [gc_move_def,basic_gcTheory.gc_move_def]
     \\ qpat_x_assum `Data a = _` (assume_tac o GSYM)
     \\ fs [to_basic_heap_address_def])
  \\ IF_CASES_TAC
  >- (fs [gc_move_def,basic_gcTheory.gc_move_def,gen_inv_def]
     \\ qpat_x_assum `_ = ptr'` (assume_tac o GSYM) \\ fs []
     \\ fs [to_basic_heap_address_def])
  \\ IF_CASES_TAC
  >- (fs [gc_move_def,basic_gcTheory.gc_move_def,gen_inv_def]
     \\ qpat_x_assum `_ = ptr'` (assume_tac o GSYM) \\ fs []
     \\ fs [to_basic_heap_address_def])
  \\ fs [gc_move_def,basic_gcTheory.gc_move_def,gen_inv_def]
  \\ strip_tac >- cheat
  \\ BasicProvers.TOP_CASE_TAC \\ fs []
  >- (`heap_lookup n state.heap = NONE` by all_tac
     >- (pop_assum mp_tac
        \\ Induct_on
        \\ fs [heap_lookup_def]
        \\
     )
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

val RootsRel = Hol_reln `
  (!a b. RootsRel [Pointer 12 a] [Pointer 13 b])`;

val StateRel = Hol_reln `
  (!conf. StateRel (to_basic_state conf empty_state) empty_state)`;

val simulation_thm = store_thm("simulation_thm",
  ``!roots heap conf.
      (SOME refs = OPTION_MAP (refs_to_roots o SND) (heap_split conf.refs_start state.heap)) /\
      (basic_gc (to_basic_conf conf)
                (to_basic_roots conf.gen_start roots ++ refs, to_basic_heap conf heap)
       = (bRoots',bState')) ==>
      ?roots' state'.
        (partial_gc conf (roots,heap) = (roots',state')) /\
        (StateRel bState' state') /\
        (RootsRel bRoots' roots')``,
  cheat);


(* val simulation = prove( *)
(*   ``!broots' bstate'. *)
(*     let bheap = to_basic_heap conf heap in *)
(*     let broots = to_basic_roots conf.gen_start roots ++ *)
(*                  refs_to_roots (heap_drop conf.refs_start bheap) in *)
(*     (basic_gc (to_basic_conf conf) (broots,bheap) = (broots',bstate')) ==> *)
(*     ?roots' state'. *)
(*       (partial_gc conf (roots, heap) = (roots',state')) /\ *)
(*       (TAKE (LENGTH roots) broots' = to_basic_roots conf.gen_start roots') /\ *)
(*       (bstate' = to_basic_state conf state')(*  /\ *) *)
(*       (* (RootsRefs (heap_drop conf.refs_start state. (DROP (LENGTH roots) roots')) *)``, *)
(*   cheat); *)

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

val partial_gc_simulation = prove(
  ``(partial_gc conf (roots,heap) = (roots1,state1)) /\
    roots_ok roots (heap:('a,'b) heap_element list) /\
    heap_ok heap conf.limit /\
    heap_gen_ok heap conf /\
    (SOME refs = OPTION_MAP (refs_to_roots o SND) (heap_split conf.refs_start heap)) ==>
    (basic_gc (to_basic_conf conf)
              (to_basic_roots conf.gen_start roots ++ MAP (to_basic_heap_address conf) refs,
               MAP (to_basic_heap_element conf) (restrict_heap conf.gen_start conf.refs_start heap))
     = (to_basic_roots conf.gen_start roots1, (* TODO: add refs roots *)
       to_basic_state conf state1))``,
  rpt strip_tac
  cheat);

val f_old_ptrs_def = Define `
  f_old_ptrs conf heap = {a | isSomeDataElement (heap_lookup a heap)
                              /\ (a < conf.gen_start \/ conf.refs_start <= a)}`;

val new_f_def = Define `
  new_f f conf heap =
    FUNION (FUN_FMAP I (f_old_ptrs conf heap))
           (FUN_FMAP (\a. conf.gen_start + f ' (a - conf.gen_start))
                     (IMAGE ((+) conf.gen_start) (FDOM f)))`;

val partial_gc_related = store_thm("partial_gc_related",
  ``roots_ok roots heap /\
    heap_ok (heap:('a,'b) heap_element list) conf.limit /\
    heap_gen_ok heap conf /\
    gen_inv conf heap ==>
    ?state f.
      (partial_gc conf (roots:'a heap_address list,heap) =
         (ADDR_MAP (FAPPLY f) roots,state)) /\
      (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM f) /\
      (heap_ok (state.h1 ++ heap_expand state.n ++ state.r1) conf.limit) /\
      gc_related f heap (state.h1 ++ heap_expand state.n ++ state.r1)``,

  rpt strip_tac
  \\ Cases_on `partial_gc conf (roots,heap)` \\ fs []
  \\ rename1 `_ = (roots1,state1)`
  \\ drule partial_gc_simulation
  \\ fs []
  \\ impl_tac
  >- cheat
  \\ strip_tac
  \\ qabbrev_tac `basic_roots = to_basic_roots conf.gen_start roots ++ MAP (to_basic_heap_address conf) refs`
  \\ qabbrev_tac `basic_heap = MAP (to_basic_heap_element conf) (restrict_heap conf.gen_start conf.refs_start heap)`
  (* \\ qispecl_then  *)
  \\ qspecl_then
      [`basic_roots`,`basic_heap`,`to_basic_conf conf`] mp_tac
      (basic_gc_related |> INST_TYPE [``:'a`` |-> ``:('a heap_address, 'a) data_sort``])
  \\ impl_tac
  >- cheat
  \\ strip_tac \\ fs []
  \\ qexists_tac `new_f f conf heap`
  \\

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
      (heap_ok (state.h1 ++ heap_expand state.n ++ state.r1) conf.limit) /\
      (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM f) /\
      gc_related f heap (state.h1 ++ heap_expand state.n ++ state.r1)``,
  cheat);


val _ = export_theory();
