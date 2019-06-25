(*
  The major collection of the generational copying garbage collector.
*)
open preamble wordsTheory wordsLib integer_wordTheory gc_sharedTheory;

val _ = new_theory "gen_gc";

val _ = ParseExtras.temp_loose_equality();

val gc_state_component_equality = DB.fetch "gc_shared" "gc_state_component_equality";

(* Copying GC which moves references to the end of the heap. This
   implementation is a pre-stage to the generational GC. *)

val _ = Datatype `
  gen_gc_conf =
    <| limit : num
     ; isRef : 'a -> bool
     |>`;

val gc_move_def = Define `
  (gc_move conf state (Data d) = (Data d, state)) /\
  (gc_move conf state (Pointer ptr d) =
     case heap_lookup ptr state.heap of
     | SOME (ForwardPointer ptr _ l) => (Pointer ptr d,state)
     | SOME (DataElement xs l dd) =>
       let ok = state.ok /\ l+1 <= state.n in
       let n = state.n - (l + 1) in
        if conf.isRef dd then
          (* put refs in r4 *)
          let r4 = (DataElement xs l dd) :: state.r4 in
          let (heap,ok) = gc_forward_ptr ptr state.heap (state.a + n) d ok in
            (Pointer (state.a + n) d
            ,state with <| r4 := r4; n := n; heap := heap; ok := ok |>)
        else
          (* put data in h2 *)
          let h2 = state.h2 ++ [DataElement xs l dd] in
          let (heap,ok) = gc_forward_ptr ptr state.heap state.a d ok in
          let a = state.a + l + 1 in
            (Pointer state.a d
            ,state with <| h2 := h2; n := n; a := a; heap := heap; ok := ok |>)
     | _ => (Pointer ptr d, state with <| ok := F |>))`;


val gc_move_IMP = prove(
  ``!x x' state state'.
    (gc_move conf state x = (x',state')) ==>
    (state.h1 = state'.h1) /\
    (state.r3 = state'.r3) /\
    (state.r2 = state'.r2) /\
    (state.r1 = state'.r1) /\
    (IS_PREFIX state'.h2 state.h2) /\
    (IS_SUFFIX state'.r4 state.r4)``,
  Cases
  \\ fs [gc_move_def]
  (* \\ ntac 3 strip_tac *)
  (* \\ fs [] *)
  \\ Cases_on `heap_lookup n state.heap`
  \\ fs [gc_state_component_equality]
  \\ Cases_on `x`
  \\ fs [LET_THM,gc_state_component_equality]
  \\ IF_CASES_TAC
  \\ pairarg_tac
  \\ fs []
  \\ rw [IS_SUFFIX_compute]);

val gc_move_list_def = Define `
  (gc_move_list conf state [] = ([], state)) /\
  (gc_move_list conf state (x::xs) =
    let (x,state) = gc_move conf state x in
    let (xs,state) = gc_move_list conf state xs in
      (x::xs,state))`;

Theorem gc_move_list_IMP:
   !xs xs' state state'.
    (gc_move_list conf state xs = (xs',state')) ==>
    (state.h1 = state'.h1) /\
    (state.r3 = state'.r3) /\
    (state.r2 = state'.r2) /\
    (state.r1 = state'.r1) /\
    (IS_PREFIX state'.h2 state.h2) /\
    (IS_SUFFIX state'.r4 state.r4)
Proof
  Induct
  \\ fs [gc_move_list_def,LET_THM]
  \\ ntac 5 strip_tac
  \\ pairarg_tac
  \\ fs []
  \\ pairarg_tac
  \\ fs []
  \\ rpt var_eq_tac
  \\ drule gc_move_IMP
  \\ strip_tac
  \\ fs [IS_SUFFIX_compute]
  \\ metis_tac [IS_PREFIX_TRANS]
QED

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
  \\ imp_res_tac (GSYM gc_move_list_IMP)
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
(* Runs a clock to simplify the termination argument *)
val gc_move_loop_def = Define `
  gc_move_loop conf state (clock :num) =
    case state.r4 of
    | [] =>
      (case state.h2 of
       | [] => state
       | (h::h2) =>
         let state = gc_move_data conf state in
         if clock = 0 then state with <| ok := F |>
         else gc_move_loop conf state (clock-1))
    | (h::r4) =>
      let state = gc_move_refs conf (state with <| r2 := state.r4; r4 := [] |>) in
      if clock = 0 then state with <| ok := F |>
      else gc_move_loop conf state (clock-1)`;

val gen_gc_def = Define `
  gen_gc conf (roots,heap) =
    let state = empty_state
        with <| heap := heap
              ; n := conf.limit
              ; ok := (heap_length heap = conf.limit) |> in
    let (roots,state) = gc_move_list conf state roots in
    let state = gc_move_loop conf state conf.limit in
      (roots,state)`;

(* Do we point to something that is fully processed? I.e. all children
are also copied. *)
val is_final_def = Define `
  is_final conf state ptr =
    let h1end = heap_length (state.h1) in
    let r3start = state.a + state.n + heap_length state.r4 in
    let r3end = r3start + heap_length state.r3 in
    let r1start = r3end + heap_length state.r2 in
    ptr < h1end \/
    r1start <= ptr \/
    (r3start <= ptr /\ ptr < r3end)`;

val gc_inv_def = Define `
  gc_inv conf state (heap0:('a, 'b) heap_element list)
                    (roots0:'a heap_address list) =
    let heap' = state.h1 ++ state.h2 ++
                heap_expand state.n ++
                state.r4 ++ state.r3 ++ state.r2 ++ state.r1 in
      (* lengths *)
    (heap_length (state.h1 ++ state.h2) = state.a) /\
    (state.a + state.n + heap_length (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) = conf.limit) /\
    (heap_length (FILTER (\h. ~(isForwardPointer h)) state.heap) = state.n) /\
    ((heap_length state.heap) = conf.limit) /\
      (* ---- *)
    state.ok /\
    heap_ok heap0 conf.limit /\
    heaps_similar heap0 state.heap /\
      (* ---- *)
    EVERY isDataElement state.h1 /\ EVERY isDataElement state.h2 /\
    EVERY isDataElement state.r1 /\ EVERY isDataElement state.r2 /\
    EVERY isDataElement state.r3 /\ EVERY isDataElement state.r4 /\
      (* ---- *)
    (!x l d. MEM (DataElement x l d) (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) ==>
          conf.isRef d) /\
      (* ---- *)
    BIJ (heap_map1 state.heap) (FDOM (heap_map 0 state.heap))
        (heap_addresses 0 (state.h1 ++ state.h2) UNION
         heap_addresses (state.a + state.n)
           (state.r4 ++ state.r3 ++ state.r2 ++ state.r1)) /\
      (* ---- *)
    !i j.
      (FLOOKUP (heap_map 0 state.heap) i = SOME j) ==>
      ?xs l d.
        (heap_lookup i heap0 = SOME (DataElement xs l d)) /\
        (heap_lookup j heap' =
          SOME (DataElement
                 (if is_final conf state j
                   then ADDR_MAP (heap_map1 state.heap) xs
                   else xs)
                 l d)) /\
        reachable_addresses roots0 heap0 i /\
        !ptr d.
          MEM (Pointer ptr d) xs /\ is_final conf state j ==>
          ptr IN FDOM (heap_map 0 state.heap)`;

val full_simp = full_simp_tac std_ss

val heap_map_ForwardPointer_lemma = prove(
  ``!ptr.
      heap_map 0 (ha ++ ForwardPointer ptr a l::hb) =
      heap_map 0 (ha ++ DataElement ys l d::hb) |+ (heap_length ha,ptr)``,
  strip_tac
  \\ fs [heap_map_APPEND,heap_map_def]
  \\ fs [heap_length_def,el_length_def]
  \\ fs [heap_map_def,SUM_APPEND]
  \\ fs [GSYM fmap_EQ_THM,heap_map_APPEND]
  \\ fs [EXTENSION] \\ strip_tac THEN1 metis_tac []
  \\ fs [FUNION_DEF,FAPPLY_FUPDATE_THM] \\ strip_tac
  \\ Cases_on `x = SUM (MAP el_length ha)` \\ full_simp_tac std_ss []
  \\ fs [GSYM heap_length_def]
  \\ fs [FDOM_heap_map]);

val isSomeDataOrForward_lemma = prove(
  ``!ha ptr.
      isSomeDataOrForward (heap_lookup ptr (ha ++ DataElement ys l d::hb)) <=>
      isSomeDataOrForward (heap_lookup ptr (ha ++ ForwardPointer a u l::hb))``,
  Induct \\ full_simp_tac std_ss [APPEND,heap_lookup_def]
  \\ SRW_TAC [] [] \\ full_simp_tac std_ss []
  \\ EVAL_TAC \\ full_simp_tac std_ss [el_length_def]);

val isSomeDataOrForward_lemma_expanded =
  isSomeDataOrForward_lemma
  |> SIMP_RULE std_ss [isSomeDataOrForward_def,isSomeDataElement_def,isSomeForwardPointer_def];

val NOT_IN_heap_addresses = prove(
  ``!xs n. ~(n + heap_length xs IN heap_addresses n xs)``,
  Induct \\ full_simp_tac (srw_ss()) [heap_addresses_def,APPEND,heap_length_def]
  \\ full_simp_tac (srw_ss()) [EXTENSION] \\ rpt strip_tac
  \\ full_simp_tac std_ss [ADD_ASSOC]
  THEN1 (Cases_on `h` \\ EVAL_TAC \\ decide_tac) \\ metis_tac []);

(* val NOT_IN_heap_addresses = *)
(*   NOT_IN_heap_addresses_general |> Q.SPECL [`xs`,`0`] |> SIMP_RULE std_ss []; *)

val NOT_IN_heap_addresses_less = prove(
  ``!xs m n. (m < n) ==> ~(m IN heap_addresses n xs)``,
  Induct \\ rw [] \\ fs [heap_addresses_def]);

val NOT_IN_heap_addresses_gt = prove(
  ``!xs m n p.
    (heap_length xs + p <= m) ==>
    ~(m IN heap_addresses p xs)``,
  Induct
  \\ rw []
  \\ fs [heap_addresses_def]
  \\ fs [heap_length_def]
  \\ qsuff_tac `p < m` >- decide_tac
  \\ `1 <= el_length h` by fs [el_length_GT_0]
  \\ decide_tac);

val heap_length_CONS = prove(
  ``!x xs. heap_length (x::xs) = el_length x + heap_length xs``,
  fs [heap_length_def]);

Theorem heap_lookup_LENGTH:
   !xs x ys l. (heap_length xs = l) ==> (heap_lookup l (xs ++ x::ys) = SOME x)
Proof
  Induct
  >- fs [heap_length_def,heap_lookup_def]
  \\ fs [heap_length_CONS]
  \\ fs [heap_lookup_def,el_length_NOT_0]
QED

Theorem heap_lookup_APPEND:
   !j xs ys.
    heap_lookup j (xs ++ ys) =
      if j < heap_length xs
      then heap_lookup j xs
      else heap_lookup (j - heap_length xs) ys
Proof
  Induct_on `xs`
  \\ fs [heap_length_def,heap_lookup_def]
  \\ rpt strip_tac
  \\ IF_CASES_TAC \\ fs []
  >- (rw [] \\ fs [el_length_NOT_0])
  \\ IF_CASES_TAC \\ fs []
  \\ IF_CASES_TAC \\ fs []
QED

val IMP_if_equal = prove(
  ``!b1 b2 x1 x2 y1 y2.
    (b1 = b2) /\ (b1 ==> (x1 = x2)) /\ (~b1 ==> (y1 = y2)) ==>
    ((if b1 then x1 else y1) = if b2 then x2 else y2)``,
  rw []);

val heap_length_heap_expand = prove(
  ``!l. heap_length (heap_expand l) = l``,
  simp [heap_length_def, heap_expand_def]
  \\ Cases
  \\ simp []
  \\ simp [el_length_def]);

val ADDR_MAP_EQ = prove(
  ``!xs. (!p d. MEM (Pointer p d) xs ==> (f p = g p)) ==>
         (ADDR_MAP f xs = ADDR_MAP g xs)``,
  Induct \\ TRY (Cases_on `h`) \\ full_simp_tac (srw_ss()) [ADDR_MAP_def]
  \\ metis_tac []);

val heaps_similar_lemma = prove(
  ``!ha heap0 hb ptr ys l d a l.
      heaps_similar heap0 (ha ++ [DataElement ys l d] ++ hb) ==>
      heaps_similar heap0 (ha ++ [ForwardPointer ptr a l] ++ hb)``,
  full_simp_tac std_ss [heaps_similar_def,APPEND,GSYM APPEND_ASSOC]
  \\ rpt strip_tac
  \\ imp_res_tac LIST_REL_SPLIT2 \\ fs[]
  \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ match_mp_tac EVERY2_APPEND_suff
  \\ fs[isForwardPointer_def,el_length_def]
  \\ rw[el_length_def,isDataElement_def]);

Theorem gc_move_thm:
   !x state.
       gc_inv conf state heap0 roots0 /\
       (!ptr u. (x = Pointer ptr u) ==>
                isSomeDataOrForward (heap_lookup ptr state.heap) /\
                reachable_addresses roots0 heap0 ptr) ==>
       ?state'.
         (gc_move conf state x =
         (ADDR_APPLY (heap_map1 state'.heap) x,state')) /\
         (!ptr u. (x = Pointer ptr u) ==> ptr IN FDOM (heap_map 0 state'.heap)) /\
         (!ptr. isSomeDataOrForward (heap_lookup ptr state.heap) =
                isSomeDataOrForward (heap_lookup ptr state'.heap)) /\
         ((heap_map 0 state.heap) SUBMAP (heap_map 0 state'.heap)) /\
         gc_inv conf state' heap0 roots0
Proof
  Cases_on `x`
  \\ fs [gc_move_def,ADDR_APPLY_def]
  \\ rpt strip_tac
  \\ fs [isSomeDataOrForward_def,isSomeForwardPointer_def,isSomeDataElement_def]
  >- (imp_res_tac heap_lookup_FLOOKUP
      \\ full_simp [heap_map1_def,FLOOKUP_DEF] \\ metis_tac [ADD_CLAUSES])
  \\ fs [isSomeDataElement_def]
  \\ imp_res_tac heap_lookup_SPLIT
  \\ rw []
  \\ pairarg_tac
  \\ simp []
  \\ full_simp [gc_forward_ptr_thm]
  \\ simp [heap_map1_def]
  (* isRef *)
  >-
    (qabbrev_tac `r = state.a + (state.n − (l + 1))`
    \\ qabbrev_tac `rheap = state.r4 ++ state.r3 ++ state.r2 ++ state.r1`
    \\ qabbrev_tac `lheap = state.h1 ++ state.h2`
    \\ assume_tac (heap_map_ForwardPointer_lemma |> Q.SPEC `r`)
    \\ `l+1 <= state.n` by (fs [gc_inv_def]
       \\ qpat_assum `_ = state.n` (assume_tac o GSYM)
       \\ full_simp []
       \\ simp [FILTER_APPEND,heap_length_APPEND,
               isForwardPointer_def,heap_length_def,el_length_def,SUM_APPEND])
    \\ assume_tac NOT_IN_heap_map
    \\ qpat_assum `_ = heap` (assume_tac o GSYM)
    \\ full_simp []
    \\ rpt strip_tac
    >- fs []
    >- fs []
    >- metis_tac [isSomeDataOrForward_lemma_expanded]
    \\ full_simp [gc_inv_def,LET_THM] \\ simp [gc_state_component_equality]
    \\ full_simp []
    \\ rpt strip_tac \\ TRY (unabbrev_all_tac \\ fs [] \\ NO_TAC)
    >-                          (* lengths: heap_length = conf.limit *)
      (unabbrev_all_tac
      \\ qpat_x_assum `_ = conf.limit` kall_tac
      \\ qpat_assum `_ = conf.limit` (assume_tac o GSYM)
      \\ full_simp [GSYM (EVAL ``[DataElement ys l d] ++ state.r4 ++ state.r3 ++ state.r2 ++ state.r1``)]
      \\ simp [heap_length_APPEND]
      \\ simp [heap_length_def]
      \\ fs [GSYM heap_length_def,el_length_def])
    >-                          (* lengths *)
      (qpat_x_assum `_ = state.n` mp_tac
      \\ simp [FILTER_APPEND,heap_length_APPEND,
               isForwardPointer_def,heap_length_def,el_length_def,SUM_APPEND])
    >-                          (* lengths *)
      (qpat_x_assum `_ = conf.limit` mp_tac
      \\ once_rewrite_tac [CONS_APPEND]
      \\ simp [heap_length_APPEND]
      \\ simp [heap_length_def,el_length_def])
    >-                          (* heaps_similar *)
      (qpat_x_assum `heaps_similar _ _` mp_tac
      \\ once_rewrite_tac [CONS_APPEND]
      \\ simp []
      \\ strip_tac
      \\ drule heaps_similar_lemma
      \\ fs [])
    >- fs [isDataElement_def]
    >- (unabbrev_all_tac \\ metis_tac [MEM_APPEND])
    >- (unabbrev_all_tac \\ metis_tac [MEM_APPEND])
    >- (unabbrev_all_tac \\ metis_tac [MEM_APPEND])
    >- (unabbrev_all_tac \\ metis_tac [MEM_APPEND])
    >-                          (* BIJ *)
      (qabbrev_tac `heap' = ha ++ DataElement ys l d::hb`
      \\ `~(r IN heap_addresses 0 lheap)` by
        (unabbrev_all_tac
        \\ qpat_x_assum `_ = state.a` (assume_tac o GSYM)
        \\ simp []
        \\ `heap_length lheap <= state.n + heap_length lheap − (l + 1)` by decide_tac
        \\ fs [NOT_IN_heap_addresses_gt])
      \\ `~(r IN heap_addresses (state.a + state.n) rheap)` by
        (unabbrev_all_tac
        \\ `state.a + (state.n − (l + 1)) < state.a + state.n` by decide_tac
        \\ fs [NOT_IN_heap_addresses_less])
      \\ `heap_addresses r (DataElement ys l d::rheap) =
          (r INSERT heap_addresses (state.a + state.n) rheap)` by (unabbrev_all_tac
         \\ once_rewrite_tac [CONS_APPEND]
         \\ simp [heap_addresses_APPEND]
         \\ simp [heap_length_APPEND]
         \\ simp [heap_addresses_def]
         \\ simp [UNION_COMM]
         \\ simp [GSYM INSERT_SING_UNION]
         \\ simp [heap_length_def] \\ simp [el_length_def])
      \\ once_rewrite_tac [UNION_COMM]
      \\ simp [INSERT_UNION_EQ]
      \\ `(λa'. (heap_map 0 heap' |+ (heap_length ha,r)) ' a') =
           ((heap_length ha =+ r) (\a. heap_map 0 heap' ' a))` by simp [FUN_EQ_THM,APPLY_UPDATE_THM,FAPPLY_FUPDATE_THM]
      \\ drule BIJ_UPDATE
      \\ disch_then drule
      \\ simp [IN_UNION]
      \\ ntac 2 (disch_then drule)
      \\ simp [UNION_COMM,heap_map1_def])
    \\ Cases_on `i = heap_length ha`
    \\ qpat_abbrev_tac `state' = state with <|r4 := _; n := _; ok := T; heap := _ |>`
    >-                          (* YES *)
      (`j = r` by full_simp [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
      \\ simp []
      \\ `~(is_final conf state' r)` by (simp [is_final_def]
         \\ unabbrev_all_tac
         \\ simp [gc_state_component_equality] \\ simp []
         \\ rpt strip_tac
         >- (qpat_x_assum `_ = state.a` (assume_tac o GSYM)
            \\ simp []
            \\ simp [heap_length_APPEND])
         >- (first_x_assum mp_tac \\ simp []
            \\ once_rewrite_tac [CONS_APPEND]
            \\ simp [heap_length_APPEND]
            \\ simp [heap_length_def]
            \\ simp [el_length_def])
         >- (once_rewrite_tac [CONS_APPEND]
            \\ simp [heap_length_APPEND]
            \\ simp [heap_length_def]
            \\ simp [el_length_def]))
      \\ simp []
      \\ `heap_lookup (heap_length ha) heap0 = SOME (DataElement ys l d)` by (imp_res_tac heap_similar_Data_IMP
         \\ simp []
         \\ simp [heap_lookup_PREFIX])
      \\ simp []
      \\ `heap_length (lheap ++ heap_expand (state.n − (l + 1))) = r` by (unabbrev_all_tac
         \\ qpat_x_assum `_ = state.a` (assume_tac o GSYM)
         \\ simp []
         \\ simp [heap_length_APPEND]
         \\ simp [heap_length_heap_expand])
      \\ drule heap_lookup_LENGTH
      \\ disch_then (qspec_then `DataElement ys l d` mp_tac)
      \\ disch_then (qspec_then `rheap` mp_tac) \\ unabbrev_all_tac
      \\ once_rewrite_tac [CONS_APPEND]
      \\ fs [])
      (* NO *)
    >- (`FLOOKUP (heap_map 0 (ha ++ DataElement ys l d::hb)) i = SOME j` by fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
       \\ qpat_x_assum `!i j:num. _` (mp_tac o Q.SPECL [`i`,`j`])
       \\ fs [] \\ strip_tac
       \\ fs []
       \\ `heap_lookup j (lheap ++ heap_expand state.n ++ state.r4 ++ state.r3 ++ state.r2 ++ state.r1)
         = heap_lookup j (lheap ++ heap_expand (state.n − (l + 1)) ++ DataElement ys l d::state.r4 ++ state.r3 ++ state.r2 ++ state.r1)` by
                (Cases_on `j = heap_length (lheap ++ heap_expand (state.n − (l + 1)))`
          >- (sg `F` \\ fs []
             \\ qpat_x_assum `heap_lookup _ _ = SOME _` mp_tac
             \\ simp_tac std_ss [GSYM APPEND_ASSOC]
             \\ once_rewrite_tac [heap_lookup_APPEND]
             \\ IF_CASES_TAC \\ simp []
             >- fs [heap_length_APPEND]
             \\ simp [heap_length_APPEND]
             \\ simp_tac std_ss [GSYM APPEND_ASSOC]
             \\ once_rewrite_tac [heap_lookup_APPEND]
             \\ simp [heap_length_heap_expand]
             \\ simp [heap_expand_def]
             \\ simp [heap_lookup_def])
          \\ once_rewrite_tac [CONS_APPEND]
          \\ rewrite_tac [APPEND_ASSOC]
          \\ ntac 4
             (once_rewrite_tac [heap_lookup_APPEND]
             \\ match_mp_tac IMP_if_equal
             \\ strip_tac
             >- (fs [heap_length_APPEND,heap_length_heap_expand]
                \\ simp [heap_length_def,el_length_def]
                \\ unabbrev_all_tac
                \\ simp [])
             \\ reverse strip_tac
             >- (fs [heap_length_APPEND,heap_length_heap_expand]
                \\ simp [heap_length_def,el_length_def]
                \\ unabbrev_all_tac
                \\ simp [])
             \\ strip_tac)
          \\ rewrite_tac [GSYM APPEND_ASSOC]
          \\ once_rewrite_tac [heap_lookup_APPEND]
          \\ IF_CASES_TAC \\ simp []
          \\ Cases_on `j - state.a = 0`
          >- (simp []
             \\ sg `F` \\ fs []
             \\ qpat_x_assum `heap_lookup _ _ = SOME _` mp_tac
             \\ rewrite_tac [GSYM APPEND_ASSOC]
             \\ once_rewrite_tac [heap_lookup_APPEND]
             \\ fs []
             \\ simp [heap_expand_def]
             \\ simp [heap_lookup_def])
          \\ simp [heap_expand_def]
          \\ rw [heap_lookup_def]
          \\ unabbrev_all_tac
          \\ fs [el_length_def]
          \\ pop_assum mp_tac
          \\ IF_CASES_TAC \\ fs []
          \\ fs [heap_length_APPEND,heap_length_heap_expand])
       \\ fs []
       \\ `is_final conf state j = is_final conf state' j` by (simp [is_final_def]
          \\ unabbrev_all_tac
          \\ simp [heap_length_CONS,el_length_def])
       \\ strip_tac
       >- (match_mp_tac IMP_if_equal
          \\ simp []
          \\ strip_tac
          \\ simp [heap_map1_def]
          \\ qpat_x_assum `heap_map 0 _ = heap_map 0 _ |+ _` mp_tac
          \\ once_rewrite_tac [CONS_APPEND]
          \\ simp [APPEND_ASSOC]
          \\ strip_tac \\ simp []
          (* \\ res_tac \\ fs [] *)
          \\ match_mp_tac ADDR_MAP_EQ
          \\ simp [FAPPLY_FUPDATE_THM]
          \\ metis_tac [])
       \\ pop_assum (assume_tac o GSYM)
       \\ simp []
       \\ rpt strip_tac
       \\ res_tac
       \\ simp []))
    (* ~isRef *)
  \\ qabbrev_tac `rheap = state.r4 ++ state.r3 ++ state.r2 ++ state.r1`
  \\ qabbrev_tac `lheap = state.h1 ++ state.h2`
  \\ qpat_abbrev_tac `state' = state with <| h2 := _; a := _; n := _; ok := ok; heap := _ |>`
  \\ assume_tac (heap_map_ForwardPointer_lemma |> Q.SPEC `state.a`)
  \\ `l+1 <= state.n` by (fs [gc_inv_def]
     \\ qpat_assum `_ = state.n` (assume_tac o GSYM)
     \\ full_simp []
     \\ simp [FILTER_APPEND,heap_length_APPEND,
             isForwardPointer_def,heap_length_def,el_length_def,SUM_APPEND])
  \\ assume_tac NOT_IN_heap_map
  \\ qpat_assum `_ = heap` (assume_tac o GSYM)
  \\ full_simp []
  \\ rpt strip_tac
  >- fs []
  >- fs []
  >- metis_tac [isSomeDataOrForward_lemma_expanded]
  \\ full_simp [gc_inv_def,LET_THM] \\ simp [gc_state_component_equality]
  \\ full_simp []
  \\ rpt strip_tac \\ TRY (unabbrev_all_tac \\ fs [gc_state_component_equality] \\ NO_TAC)
  >- (unabbrev_all_tac
     \\ simp [gc_state_component_equality]
     \\ simp [heap_length_APPEND,heap_length_def,el_length_def])
  >- (unabbrev_all_tac
     \\ simp [gc_state_component_equality]
     \\ qpat_x_assum `_ = state.n` mp_tac
     \\ simp [FILTER_APPEND,heap_length_APPEND,
             isForwardPointer_def,heap_length_def,el_length_def,SUM_APPEND])
  >- (unabbrev_all_tac
     \\ simp [gc_state_component_equality]
     \\ qpat_x_assum `_ = conf.limit` mp_tac
     \\ simp [heap_length_APPEND,heap_length_def,el_length_def])
  >- (unabbrev_all_tac
     \\ simp [gc_state_component_equality]
     \\ qpat_x_assum `heaps_similar _ _` mp_tac
     \\ once_rewrite_tac [CONS_APPEND]
     \\ simp [] \\ strip_tac
     \\ drule heaps_similar_lemma
     \\ fs [])
  >- (unabbrev_all_tac
     \\ simp [gc_state_component_equality]
     \\ fs [isDataElement_def])
  >- (unabbrev_all_tac
     \\ qpat_x_assum `!x l' dl'. MEM _ _ ==> _` (qspecl_then [`x`,`l'`,`d'`] assume_tac)
     \\ fs [MEM_APPEND])
  >- (unabbrev_all_tac
     \\ qpat_x_assum `!x l' dl'. MEM _ _ ==> _` (qspecl_then [`x`,`l'`,`d'`] assume_tac)
     \\ fs [MEM_APPEND])
  >- (unabbrev_all_tac
     \\ qpat_x_assum `!x l' dl'. MEM _ _ ==> _` (qspecl_then [`x`,`l'`,`d'`] assume_tac)
     \\ fs [MEM_APPEND])
  >- (unabbrev_all_tac
     \\ qpat_x_assum `!x l' dl'. MEM _ _ ==> _` (qspecl_then [`x`,`l'`,`d'`] assume_tac)
     \\ fs [MEM_APPEND])
  >- (qabbrev_tac `heap' = ha ++ DataElement ys l d::hb` (* BIJ *)
     \\ simp [gc_state_component_equality]
     \\ `~(state.a IN heap_addresses 0 lheap)` by (unabbrev_all_tac
        \\ qpat_x_assum `_ = state.a` (assume_tac o GSYM)
        \\ simp []
        \\ fs [NOT_IN_heap_addresses_gt])
     \\ `~(state.a IN heap_addresses (state.a + state.n) rheap)` by (unabbrev_all_tac
        \\ qpat_x_assum `_ = state.a` (assume_tac o GSYM)
        \\ simp []
        \\ fs [NOT_IN_heap_addresses_less])
     \\ `heap_addresses state.a [DataElement ys l d]
         = state.a INSERT {}` by simp [heap_addresses_def]
     \\ `(λa'. (heap_map 0 heap' |+ (heap_length ha,state.a)) ' a') =
           ((heap_length ha =+ state.a) (\a. heap_map 0 heap' ' a))` by simp [FUN_EQ_THM,APPLY_UPDATE_THM,FAPPLY_FUPDATE_THM]
     \\ unabbrev_all_tac \\ simp [gc_state_component_equality]
     \\ simp [heap_map1_def]
     \\ drule BIJ_UPDATE
     \\ simp [heap_map1_def]
     \\ disch_then drule
     \\ simp [IN_UNION]
     \\ ntac 2 (disch_then drule)
     \\ `heap_addresses 0 (state.h1 ++ state.h2 ++ [DataElement ys l d]) =
         heap_addresses 0 (state.h1 ++ state.h2) UNION {state.a}` by simp [heap_addresses_APPEND]
     \\ simp [UNION_COMM]
     \\ once_rewrite_tac [GSYM UNION_ASSOC]
     \\ simp [GSYM INSERT_SING_UNION])
  \\ Cases_on `i = heap_length ha`
  >- (`j = state.a` by (unabbrev_all_tac \\ fs [gc_state_component_equality]
        \\ rfs []
        \\ fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM])
     \\ simp []
     \\ `~(is_final conf state' state.a)` by (simp [is_final_def]
        \\ unabbrev_all_tac \\ simp [gc_state_component_equality]
        \\ qpat_x_assum `heap_length _ = state.a` (assume_tac o GSYM)
        \\ simp []
        \\ fs [heap_length_APPEND])
     \\ simp []
     \\ `heap_lookup (heap_length ha) heap0 = SOME (DataElement ys l d)` by (imp_res_tac heap_similar_Data_IMP
        \\ simp [heap_lookup_PREFIX])
     \\ simp []
     \\ Q.UNABBREV_TAC `state'` \\ fs [gc_state_component_equality]
     (* \\ qpat_x_assum `heap_length _ = state.a` (assume_tac o GSYM) *)
     (* \\ simp [] *)
     \\ ntac 5 (once_rewrite_tac [GSYM APPEND_ASSOC])
     \\ once_rewrite_tac [GSYM CONS_APPEND]
     \\ qpat_x_assum `heap_length _ = state.a` (assume_tac)
     \\ drule heap_lookup_LENGTH
     \\ simp [])
  \\ `FLOOKUP (heap_map 0 (ha ++ DataElement ys l d::hb)) i = SOME j` by (Q.UNABBREV_TAC `state'` \\ fs [gc_state_component_equality]
     \\ rfs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM])
  \\ qpat_x_assum `! i j:num. _` (mp_tac o Q.SPECL [`i`,`j`])
  \\ fs [] \\ strip_tac \\ fs []
  (* \\ Q.UNABBREV_TAC `state'` \\ fs [gc_state_component_equality] *)
  \\ `heap_lookup j (lheap ++ heap_expand state.n ++ state.r4 ++ state.r3 ++ state.r2 ++ state.r1)
     = heap_lookup j (state'.h1 ++ state'.h2 ++ heap_expand state'.n ++ state'.r4 ++ state'.r3 ++ state'.r2 ++ state'.r1)` by (Cases_on `j = heap_length lheap`
     >- (unabbrev_all_tac \\ fs []
        \\ sg `F` \\ fs []
        \\ qpat_x_assum `heap_lookup _ _ = SOME _` mp_tac
        \\ simp_tac std_ss [GSYM APPEND_ASSOC]
        \\ once_rewrite_tac [heap_lookup_APPEND]
        \\ IF_CASES_TAC \\ simp []
        >- fs [heap_length_APPEND]
        \\ qpat_x_assum `_ = state.a` (mp_tac o GSYM)
        \\ fs [heap_length_APPEND]
        \\ strip_tac \\ simp []
        \\ simp_tac std_ss [GSYM APPEND_ASSOC]
        \\ once_rewrite_tac [heap_lookup_APPEND]
        \\ simp []
        \\ simp [heap_lookup_def,heap_expand_def])
     \\ qpat_x_assum `heap_lookup _ _ = SOME _` (assume_tac o GSYM)
     \\ Q.UNABBREV_TAC `state'` \\ fs [gc_state_component_equality]
     \\ ntac 4
        (once_rewrite_tac [heap_lookup_APPEND]
        \\ match_mp_tac IMP_if_equal
        \\ strip_tac
        >- (fs [heap_length_APPEND,heap_length_heap_expand]
           \\ simp [heap_length_def,el_length_def])
        \\ reverse strip_tac
        >- (fs [heap_length_APPEND,heap_length_heap_expand]
           \\ simp [heap_length_def,el_length_def])
        \\ strip_tac)
     \\ rewrite_tac [GSYM APPEND_ASSOC]
     \\ once_rewrite_tac [heap_lookup_APPEND]
     \\ match_mp_tac IMP_if_equal
     \\ simp []
     \\ strip_tac
     \\ Cases_on `j - state.a = 0`
     >- (simp []
        \\ sg `F`
        \\ qpat_x_assum `SOME _ = heap_lookup _ _` (mp_tac o GSYM)
        \\ rewrite_tac [GSYM APPEND_ASSOC]
        \\ once_rewrite_tac [heap_lookup_APPEND]
        \\ fs [])
     \\ unabbrev_all_tac
     \\ sg `F`
     \\ simp []
     \\ qpat_x_assum `SOME (DataElement _ _ _) = heap_lookup _ _` (mp_tac o GSYM)
     \\ fs []
     \\ once_rewrite_tac [heap_lookup_APPEND] \\ simp []
     \\ once_rewrite_tac [heap_lookup_APPEND] \\ simp []
     \\ once_rewrite_tac [heap_lookup_APPEND] \\ simp []
     \\ once_rewrite_tac [heap_lookup_APPEND] \\ simp []
     \\ once_rewrite_tac [heap_lookup_APPEND] \\ simp []
     \\ fs [heap_expand_def]
     \\ fs [heap_lookup_def])
  \\ fs []
  \\ `is_final conf state j = is_final conf state' j` by (simp [is_final_def]
     \\ unabbrev_all_tac \\ fs [gc_state_component_equality])
  \\ simp []
  \\ strip_tac
  >- (match_mp_tac IMP_if_equal
     \\ simp []
     \\ strip_tac
     \\ simp [heap_map1_def]
     \\ unabbrev_all_tac \\ fs [gc_state_component_equality]
     \\ qpat_x_assum `heap_map 0 _ = heap_map 0 _ |+ _` mp_tac
     \\ once_rewrite_tac [CONS_APPEND]
     \\ simp [APPEND_ASSOC]
     \\ strip_tac \\ simp []
     (* \\ res_tac \\ fs [] *)
     \\ match_mp_tac ADDR_MAP_EQ
     \\ simp [FAPPLY_FUPDATE_THM]
     \\ metis_tac [])
   \\ pop_assum (assume_tac o GSYM)
   \\ simp []
   \\ unabbrev_all_tac \\ fs [gc_state_component_equality]
   \\ rpt strip_tac
   \\ res_tac
   \\ simp []
QED

Theorem gc_move_ALT:
   gc_move conf state y =
     let (y', state') = gc_move conf (state with <| h2 := []; r4 := [] |>) y in
       (y', state' with <| h2 := state.h2 ++ state'.h2; r4 := state'.r4 ++ state.r4 |>)
Proof
  reverse (Cases_on `y`) \\ fs [gc_move_def]
  THEN1 fs [LET_THM,gc_state_component_equality]
  \\ fs []
  \\ TRY (BasicProvers.TOP_CASE_TAC)
    THEN1 fs [LET_THM,gc_state_component_equality]
  \\ BasicProvers.TOP_CASE_TAC
  \\ TRY (fs [LET_THM,gc_state_component_equality] \\ NO_TAC)
  \\ rw []
  \\ rw []
  \\ unabbrev_all_tac
  \\ pairarg_tac \\ fs []
  \\ fs [gc_state_component_equality]
QED

val gc_move_list_thm = prove(
  ``!xs state.
    gc_inv conf state heap0 roots0 /\
    (!ptr u. MEM (Pointer ptr u) (xs:'a heap_address list) ==>
             isSomeDataOrForward (heap_lookup ptr state.heap) /\
             reachable_addresses roots0 heap0 ptr) ==>
    ?state'.
      (gc_move_list conf state xs =
        (ADDR_MAP (heap_map1 state'.heap) xs,state')) /\
      (!ptr u. MEM (Pointer ptr u) xs ==> ptr IN FDOM (heap_map 0 state'.heap)) /\
      (!ptr. isSomeDataOrForward (heap_lookup ptr state.heap) =
             isSomeDataOrForward (heap_lookup ptr state'.heap)) /\
      ((heap_map 0 state.heap) SUBMAP (heap_map 0 state'.heap)) /\
      gc_inv conf state' heap0 roots0``,
  Induct
  THEN1 fs [gc_move_list_def,ADDR_MAP_def,MEM,SUBMAP_REFL]
  \\ fs [MEM,gc_move_list_def,LET_THM]
  \\ rpt strip_tac
  \\ mp_tac gc_move_thm
  \\ disch_then (mp_tac o Q.SPECL [`h`, `state`])
  \\ rpt strip_tac
  \\ rfs []
  \\ qpat_assum `!state : ('a,'b) gc_state. _` (qspec_then `state'` mp_tac)
  \\ rpt strip_tac
  \\ rfs []
  \\ `∀ptr u. MEM (Pointer ptr u) xs ==>
              isSomeDataOrForward (heap_lookup ptr state'.heap) /\
             reachable_addresses roots0 heap0 ptr` by
    (rpt strip_tac
    \\ metis_tac [])
  \\ res_tac
  \\ qexists_tac `state''`
  \\ rpt strip_tac
  THEN1
    (Cases_on `h`
    \\ fs [ADDR_APPLY_def,ADDR_MAP_def,SUBMAP_DEF,heap_map1_def])
  \\ fs [SUBMAP_DEF,heap_map1_def]
  \\ metis_tac []);

Theorem gc_move_list_ALT:
   !ys state.
      gc_move_list conf state ys =
        let (ys', state') = gc_move_list conf (state with <| h2 := []; r4 := [] |>) ys in
        (ys',state' with <| h2 := state.h2 ++ state'.h2; r4 := state'.r4 ++ state.r4 |>)
Proof
  once_rewrite_tac [EQ_SYM_EQ]
  \\ Induct
  THEN1 fs [gc_move_list_def,LET_DEF,gc_state_component_equality]
  \\ once_rewrite_tac [gc_move_list_def]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once gc_move_ALT]
  \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ ntac 3 (pop_assum mp_tac)
  \\ qpat_x_assum `!x._` (fn th => once_rewrite_tac [GSYM th])
  \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ rw [] \\ fs []
QED

val gc_move_list_APPEND_lemma = prove(
  ``!ys state.
      (gc_move_list conf state ys = (ys', state')) ==>
        (?h2' r4'. (state'.h2 = state.h2 ++ h2') /\ (state'.r4 = r4' ++ state.r4))``,
  once_rewrite_tac [gc_move_list_ALT]
  \\ rw [LET_THM]
  \\ pairarg_tac \\ fs []
  \\ rw []);

val heap_addresses_APPEND = prove(
  ``!xs ys n. heap_addresses n (xs ++ ys) =
              heap_addresses n xs UNION heap_addresses (n + heap_length xs) ys``,
  Induct \\ full_simp_tac (srw_ss()) [APPEND,heap_addresses_def,heap_length_def]
  \\ full_simp_tac (srw_ss()) [EXTENSION,DISJ_ASSOC,ADD_ASSOC]);

val heap_addresses_APPEND_IN = prove(
  ``!xs ys n j.
      j IN heap_addresses n (xs ++ ys) ==>
      j IN heap_addresses n xs \/ j IN heap_addresses (n + heap_length xs) ys``,
  fs [heap_addresses_APPEND]);

val GREATER_IMP_heap_lookup = prove(
  ``!ys xs j .
    (heap_length (xs ++ ys) <= j + heap_length ys) ==>
    (heap_lookup j (xs ++ ys) = heap_lookup (j - heap_length xs) ys)``,
  fs [heap_length_APPEND,NOT_LESS_IMP_heap_lookup]);

Theorem heap_lookup_IMP_MEM:
   !x n y. (heap_lookup n x = SOME y) ==> MEM y x
Proof
  Induct
  \\ once_rewrite_tac [heap_lookup_def] \\ fs []
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem heaps_similar_lemma:
   !h1 h2 ptr.
      heaps_similar h1 h2 /\ isSomeDataElement (heap_lookup ptr h1) ==>
      isSomeDataOrForward (heap_lookup ptr h2)
Proof
  Induct
  \\ once_rewrite_tac [heap_lookup_def]
  \\ fs [isSomeDataElement_def,PULL_EXISTS]
  \\ rpt strip_tac
  \\ every_case_tac \\ fs []
  \\ rveq \\ fs [el_length_def,heaps_similar_def] \\ rveq
  \\ once_rewrite_tac [heap_lookup_def] \\ fs []
  THEN1
   (fs [isSomeDataOrForward_def,isSomeDataElement_def]
    \\ fs [isSomeForwardPointer_def]
    \\ Cases_on `isForwardPointer h` \\ fs []
    \\ Cases_on `h` \\ fs [isForwardPointer_def])
  \\ metis_tac []
QED

Theorem BIJ_IMP_FLOOKUP_SOME:
   !s h j.
      BIJ (heap_map1 h) (FDOM (heap_map 0 h)) s /\ j IN s ==>
      ?i. FLOOKUP (heap_map 0 h) i = SOME j
Proof
  fs [heap_map1_def,BIJ_DEF,SURJ_DEF,FLOOKUP_DEF]
QED

val heap_lookup_IMP_heap_addresses_GEN = prove(
  ``!xs n x j. (heap_lookup j xs = SOME x) ==> n + j IN heap_addresses n xs``,
  Induct \\ full_simp_tac std_ss [MEM,heap_lookup_def,heap_addresses_def]
  \\ SRW_TAC [] [] \\ res_tac
  \\ pop_assum (mp_tac o Q.SPEC `n + el_length h`)
  \\ `n + el_length h + (j - el_length h) = n + j` by decide_tac
  \\ metis_tac []);

(* in gc_inv or prove lemma here *)
val pointers_ok = prove(
  ``!state xs l d ptr u.
      gc_inv conf state heap0 roots0 /\
      (MEM (DataElement xs l d) state.h2 \/ MEM (DataElement xs l d) state.r2) /\
      MEM (Pointer ptr u) xs ==>
      isSomeDataOrForward (heap_lookup ptr state.heap)``,
  once_rewrite_tac [METIS_PROVE [] ``(b \/ c) <=> (~b ==> c)``]
  \\ fs [gc_inv_def]
  \\ rpt strip_tac
  \\ qabbrev_tac `heap1 = (state.h1 ++ state.h2 ++ heap_expand state.n ++
               state.r4 ++ state.r3 ++ state.r2 ++ state.r1)`
  \\ `?j. ~is_final conf state j /\
          (heap_lookup j heap1 = SOME (DataElement xs l d)) /\
          j IN heap_addresses (heap_length state.h1) state.h2 UNION
               heap_addresses (state.a + state.n + heap_length state.r4 +
                               heap_length state.r3) state.r2` by
   (Cases_on `MEM (DataElement xs l d) state.h2` \\ fs []
    THEN1
     (drule MEM_IMP_heap_lookup \\ strip_tac
      \\ drule heap_lookup_IMP_heap_addresses_GEN \\ strip_tac
      \\ qexists_tac `heap_length state.h1 + j` \\ fs []
      \\ qunabbrev_tac `heap1` \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ imp_res_tac heap_lookup_LESS
      \\ ntac 2 (pop_assum mp_tac)
      \\ rewrite_tac [heap_lookup_APPEND] \\ simp []
      \\ fs [is_final_def,heap_length_APPEND])
    THEN1
     (drule MEM_IMP_heap_lookup \\ strip_tac
      \\ drule heap_lookup_IMP_heap_addresses_GEN \\ strip_tac
      \\ qexists_tac `state.a + state.n + heap_length state.r4 +
                        heap_length state.r3 + j` \\ fs []
      \\ qunabbrev_tac `heap1`
      \\ full_simp_tac std_ss [APPEND_ASSOC]
      \\ imp_res_tac heap_lookup_LESS
      \\ ntac 2 (pop_assum mp_tac)
      \\ once_rewrite_tac [heap_lookup_APPEND]
      \\ fs [heap_length_heap_expand,heap_length_APPEND]
      \\ once_rewrite_tac [heap_lookup_APPEND]
      \\ fs [heap_length_heap_expand,heap_length_APPEND]
      \\ fs [is_final_def,heap_length_APPEND]))
  \\ `?i. FLOOKUP (heap_map 0 state.heap) i = SOME j` by
   (match_mp_tac BIJ_IMP_FLOOKUP_SOME \\ asm_exists_tac
    \\ fs [heap_addresses_APPEND,heap_length_APPEND] \\ NO_TAC)
  \\ first_x_assum drule
  \\ fs [] \\ strip_tac \\ fs [heap_ok_def]
  \\ `isSomeDataElement (heap_lookup ptr heap0)` by metis_tac [heap_lookup_IMP_MEM]
  \\ imp_res_tac heaps_similar_lemma \\ fs []);

Theorem IMP_reachable_addresses:
   !i ptr u xs l d.
      reachable_addresses roots0 heap0 i /\ MEM (Pointer ptr u) xs /\
      (heap_lookup i heap0 = SOME (DataElement xs l d)) ==>
      reachable_addresses roots0 heap0 ptr
Proof
  fs [reachable_addresses_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ once_rewrite_tac [RTC_CASES_RTC_TWICE]
  \\ asm_exists_tac \\ fs []
  \\ match_mp_tac RTC_SINGLE
  \\ fs [gc_edge_def]
  \\ asm_exists_tac \\ fs []
QED

Theorem gc_move_data_thm:
   !conf state.
      gc_inv conf state heap0 roots0 /\
      (state.r3 = []) /\ (state.r2 = []) ==>
      ?state'.
        (gc_move_data conf state = state') /\
        ((heap_map 0 state.heap) SUBMAP (heap_map 0 state'.heap)) /\
        gc_inv conf state' heap0 roots0 /\
        (state'.h2 = []) /\ (state'.r3 = []) /\ (state'.r2 = [])
Proof
  recInduct (theorem "gc_move_data_ind")
  \\ rpt strip_tac
  \\ once_rewrite_tac [gc_move_data_def]
  \\ Cases_on `state.h2` \\ fs []
  \\ once_rewrite_tac [CONS_APPEND] \\ fs []
  \\ IF_CASES_TAC \\ rewrite_tac []
  >- (sg `F` \\ fs []
     \\ qpat_x_assum `!xs . _` kall_tac
     \\ fs [gc_inv_def]
     \\ fs [heap_length_APPEND]
     \\ fs [heap_length_def])
  \\ Cases_on `h` \\ fs []
  >- fs [gc_inv_def,isDataElement_def]
  >- fs [gc_inv_def,isDataElement_def]
  \\ fs []
  \\ `¬(conf.limit < heap_length (state.h1 ++ DataElement l n b::t))` by (once_rewrite_tac [CONS_APPEND] \\ asm_rewrite_tac [APPEND_ASSOC])
  \\ fs []
  \\ pairarg_tac \\ fs []
  \\ qpat_x_assum `_ ==> _` mp_tac
  \\ `∀ptr u. MEM (Pointer ptr u) l ⇒
        isSomeDataOrForward (heap_lookup ptr state.heap) ∧
        reachable_addresses roots0 heap0 ptr` by
       (drule pointers_ok \\ rw [] \\ fs [] THEN1 metis_tac []
        \\ rpt strip_tac \\ qpat_x_assum `!x1 x2 x3. bbb` kall_tac
        \\ full_simp_tac std_ss [gc_inv_def,LET_THM]
        \\ `?i. FLOOKUP (heap_map 0 state.heap) i = SOME (heap_length state.h1)` by
         (full_simp_tac std_ss [FLOOKUP_DEF,BIJ_DEF,SURJ_DEF,heap_map1_def,LET_DEF]
          \\ qpat_x_assum `!xx.bbb` kall_tac
          \\ fs [heap_addresses_APPEND,heap_addresses_def])
        \\ first_x_assum drule
        \\ `~(is_final conf state (heap_length state.h1))` by
             (fs [is_final_def,heap_length_APPEND]
              \\ fs [heap_length_def,el_length_def])
        \\ fs [] \\ strip_tac
        \\ match_mp_tac IMP_reachable_addresses \\ asm_exists_tac \\ fs []
        \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
        \\ full_simp_tac std_ss [heap_lookup_APPEND,heap_length_def,
             el_length_def,SUM,MAP] \\ fs []
        \\ rfs [heap_lookup_def] \\ rveq \\ fs [] \\ asm_exists_tac \\ fs [])
  \\ reverse impl_tac
  >- (fs []
     \\ strip_tac
     \\ qsuff_tac `heap_map 0 state.heap ⊑ heap_map 0 state'.heap`
     >- metis_tac [SUBMAP_TRANS]
     \\ qpat_x_assum `gc_inv _ _ _ _` kall_tac
     \\ drule gc_move_list_thm
     \\ disch_then (qspec_then `l` mp_tac)
     \\ fs []
     \\ impl_tac \\ fs [])
  \\ fs []
  \\ drule gc_move_list_thm
  \\ disch_then (qspec_then `l` mp_tac)
  \\ fs []
  \\ impl_tac \\ fs []
  \\ strip_tac
  \\ qpat_x_assum `gc_inv conf state heap0 roots0` kall_tac
  \\ drule gc_move_list_IMP
  \\ strip_tac
  \\ fs [gc_inv_def]
  \\ `?t'. state'.h2 = DataElement l n b::t'` by (rfs []
     \\ Cases_on `state'.h2`
     \\ fs []
     \\ fs [])
  \\ rpt strip_tac
  \\ TRY (fs [] \\ NO_TAC)
  >- fs [heap_length_APPEND,heap_length_def,el_length_def]
  >- rfs []
  >- fs [isDataElement_def]
  >- (qpat_x_assum `!x l d. _ ==> conf.isRef d` (qspecl_then [`x`,`l'`,`d`] assume_tac) \\ fs [])
  >- (qpat_x_assum `!x l d. _ ==> conf.isRef d` (qspecl_then [`x`,`l'`,`d`] assume_tac) \\ fs [])
  >- (qpat_x_assum `BIJ _ _ _` mp_tac
     \\ asm_rewrite_tac []
     \\ simp []
     \\ once_rewrite_tac [CONS_APPEND]
     \\ simp []
     \\ match_mp_tac (METIS_PROVE [] ``(b = b1) ==> b ==> b1``)
     \\ AP_TERM_TAC
     \\ AP_THM_TAC
     \\ AP_TERM_TAC
     \\ simp [heap_addresses_APPEND]
     \\ simp [heap_addresses_def]
     \\ AP_TERM_TAC
     \\ fs [heap_length_APPEND,heap_length_def,el_length_def])
  \\ qpat_abbrev_tac `state'' = state' with <|h1 := _;h2 := _;ok := _|>`
  \\ qpat_x_assum `!i j:num._` (qspecl_then [`i`,`j`] assume_tac)
  \\ rfs []
  \\ Cases_on `j = heap_length state'.h1` \\ fs []
  >- (`is_final conf state'' (heap_length state'.h1)` by (unabbrev_all_tac
        \\ simp [is_final_def,heap_length_APPEND,heap_length_def]
        \\ simp [el_length_def,SUM_APPEND])
     \\ `~(is_final conf state' (heap_length state'.h1))` by (simp [is_final_def,heap_length_APPEND,heap_length_def]
        \\ qpat_x_assum `_ = state'.a` (assume_tac o GSYM) \\ simp []
        \\ simp [heap_length_APPEND,heap_length_def]
        \\ fs [el_length_def])
     \\ qpat_x_assum `heap_lookup (heap_length state'.h1) _ = _` mp_tac
     \\ simp []
     \\ once_rewrite_tac [CONS_APPEND] \\ simp []
     \\ rewrite_tac [GSYM APPEND_ASSOC,GSYM CONS_APPEND]
     \\ fs [heap_lookup_PREFIX]
     \\ strip_tac \\ fs [])
  \\ qpat_x_assum `heap_lookup j _ = _` mp_tac
  \\ once_rewrite_tac [CONS_APPEND] \\ simp []
  \\ `heap_length [DataElement (ADDR_MAP (heap_map1 state'.heap) l) n b] = heap_length [DataElement l n b]` by fs [heap_length_def,el_length_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC]
  \\ once_rewrite_tac [heap_lookup_APPEND]
  \\ IF_CASES_TAC
  >- (simp [] \\ strip_tac
     \\ `is_final conf state'' j = is_final conf state' j` by (unabbrev_all_tac
        \\ fs [is_final_def,heap_length_def,el_length_def,SUM_APPEND])
     \\ simp [] \\ fs [])
  \\ rewrite_tac []
  \\ once_rewrite_tac [heap_lookup_APPEND]
  \\ IF_CASES_TAC
  >- (simp [] \\ strip_tac
     \\ sg `F`
     \\ fs [heap_lookup_def])
  \\ asm_rewrite_tac []
  \\ simp [] \\ strip_tac
  \\ `is_final conf state'' j = is_final conf state' j` by (unabbrev_all_tac
     \\ fs [is_final_def,heap_length_def,el_length_def,SUM_APPEND])
  \\ simp [] \\ fs []
QED

Theorem gc_move_refs_lemma:
   !state l n b xs' t state'.
      gc_inv conf state heap0 roots0 /\
      (state.r2 = DataElement l n b::t) /\
      (gc_move_list conf state l = (xs',state')) /\
      (∀ptr u. MEM (Pointer ptr u) l ⇒
        isSomeDataOrForward (heap_lookup ptr state.heap) /\
        reachable_addresses roots0 heap0 ptr)
      ==>
      gc_inv conf
        (state' with <|r3 := state'.r3 ++ [DataElement xs' n b]; r2 := t|>)
        heap0 roots0
Proof
  rpt strip_tac
  \\ drule gc_move_list_thm
  \\ disch_then (qspec_then `l` mp_tac)
  \\ fs []
  \\ impl_tac \\ fs []
  \\ strip_tac
  \\ qpat_x_assum `gc_inv conf state heap0 roots0` kall_tac
  \\ drule gc_move_list_IMP
  \\ strip_tac
  \\ fs []
  \\ fs [gc_inv_def]
  \\ rfs []
  \\ rpt strip_tac
  \\ TRY (fs [] \\ NO_TAC)
  >- fs [heap_length_APPEND,heap_length_def,el_length_def]
  >- fs [isDataElement_def]
  >- metis_tac []
  >- metis_tac []
  >- metis_tac []
  >- metis_tac []
  >- (qpat_x_assum `BIJ _ _ _` mp_tac
     \\ once_rewrite_tac [CONS_APPEND]
     \\ simp []
     \\ match_mp_tac (METIS_PROVE [] ``(b = b1) ==> b ==> b1``)
     \\ AP_TERM_TAC
     \\ AP_TERM_TAC
     \\ simp [heap_addresses_APPEND]
     \\ simp [GSYM UNION_ASSOC]
     \\ AP_TERM_TAC
     \\ AP_TERM_TAC
     \\ simp [heap_length_APPEND]
     \\ `heap_length [DataElement (ADDR_MAP (heap_map1 state'.heap) l) n b] = heap_length [DataElement l n b]` by simp [heap_length_def,el_length_def]
     \\ simp []
     \\ AP_THM_TAC
     \\ AP_TERM_TAC
     \\ simp [heap_addresses_def])
  \\ qpat_abbrev_tac `state'' = state' with <|r3:=_;r2:=_|>`
  \\ qpat_x_assum `!i j:num._` (qspecl_then [`i`,`j`] assume_tac)
  \\ rfs []
  \\ Cases_on `j = heap_length (state'.h1 ++ state'.h2 ++ heap_expand state'.n ++ state'.r4 ++ state'.r3)`
  >- (`is_final conf state'' j` by (unabbrev_all_tac
        \\ simp [is_final_def,heap_length_APPEND]
        \\ simp [heap_length_heap_expand]
        \\ simp [heap_length_def,el_length_def,SUM_APPEND])
     \\ `~(is_final conf state' j)` by (qpat_x_assum `_ = state'.a` mp_tac
        \\ simp [is_final_def,heap_length_APPEND,heap_length_heap_expand]
        \\ strip_tac
        \\ simp [heap_length_def,el_length_def])
     \\ qpat_x_assum `heap_lookup j _ = _` mp_tac
     \\ once_rewrite_tac [CONS_APPEND] \\ simp []
     \\ rewrite_tac [GSYM APPEND_ASSOC,GSYM CONS_APPEND]
     \\ rewrite_tac [APPEND_ASSOC]
     \\ qpat_x_assum `heap_lookup i heap0 = _` kall_tac
     \\ rewrite_tac [heap_lookup_PREFIX]
     \\ simp []
     \\ strip_tac \\ fs [])
  \\ qpat_x_assum `heap_lookup j _ = _` mp_tac
  \\ once_rewrite_tac [CONS_APPEND]
  \\ `heap_length [DataElement (ADDR_MAP (heap_map1 state'.heap) l) n b] = heap_length [DataElement l n b]` by simp [heap_length_def,el_length_def]
  \\ simp []
  \\ rewrite_tac [GSYM APPEND_ASSOC,GSYM CONS_APPEND]
  \\ rewrite_tac [APPEND_ASSOC]
  \\ once_rewrite_tac [heap_lookup_APPEND]
  \\ IF_CASES_TAC
  >- (simp [] \\ strip_tac
     \\ `is_final conf state'' j = is_final conf state' j` by (unabbrev_all_tac
        \\ fs [is_final_def]
        \\ fs [heap_length_heap_expand,heap_length_APPEND])
     \\ fs [] \\ fs [])
  \\ rewrite_tac []
  \\ once_rewrite_tac [CONS_APPEND]
  \\ once_rewrite_tac [heap_lookup_APPEND]
  \\ IF_CASES_TAC
  >- (simp [] \\ fs [heap_lookup_def])
  \\ asm_rewrite_tac []
  \\ simp [] \\ strip_tac
  \\ `is_final conf state'' j = is_final conf state' j` by (unabbrev_all_tac
     \\ fs [is_final_def]
     \\ once_rewrite_tac [CONS_APPEND]
     \\ fs [heap_length_heap_expand,heap_length_APPEND]
     \\ fs [heap_length_def])
  \\ simp [] \\ fs []
QED

Theorem gc_move_refs_thm:
   !conf state.
      gc_inv conf state heap0 roots0 ==>
      ?state'.
        (gc_move_refs conf state = state') /\
        ((heap_map 0 state.heap) SUBMAP (heap_map 0 state'.heap)) /\
        gc_inv conf state' heap0 roots0 /\
        (state'.r3 = []) /\ (state'.r2 = []) /\
        (0 < heap_length state.r3 ==> heap_length state.r1 < heap_length state'.r1)
Proof
  recInduct (theorem "gc_move_refs_ind")
  \\ rpt strip_tac
  \\ once_rewrite_tac [gc_move_refs_def]
  \\ Cases_on `state.r2` \\ fs []
  >- (fs [gc_inv_def]
     \\ reverse strip_tac
     >- fs [heap_length_APPEND]
     \\ strip_tac >- metis_tac []
     \\ rw []
     \\ qpat_x_assum `!i j._` (qspecl_then [`i`,`j`] mp_tac)
     \\ fs [] \\ strip_tac \\ fs []
     \\ qpat_abbrev_tac `state' = state with <|r3 := _;r1 := _|>`
     \\ `is_final conf state' j = is_final conf state j` by (unabbrev_all_tac
        \\ simp [is_final_def,heap_length_def,el_length_def])
     \\ fs [] \\ fs [])
  \\ Cases_on `h` \\ fs []
  >- fs [gc_inv_def,isDataElement_def]
  >- fs [gc_inv_def,isDataElement_def]
  \\ pairarg_tac \\ fs []
  \\ qpat_x_assum `_ ==> _` mp_tac
  \\ `∀ptr u. MEM (Pointer ptr u) l ⇒
         isSomeDataOrForward (heap_lookup ptr state.heap) /\
         reachable_addresses roots0 heap0 ptr` by
       (drule pointers_ok \\ rw [] \\ fs [] THEN1 metis_tac []
        \\ rpt strip_tac \\ qpat_x_assum `!x1 x2 x3. bbb` kall_tac
        \\ full_simp_tac std_ss [gc_inv_def,LET_THM]
        \\ `?i. FLOOKUP (heap_map 0 state.heap) i =
                SOME (state.a + state.n + heap_length (state.r4 ++ state.r3))` by
         (full_simp_tac std_ss [FLOOKUP_DEF,BIJ_DEF,SURJ_DEF,heap_map1_def,LET_DEF]
          \\ qpat_x_assum `!xx.bbb` kall_tac
          \\ fs [heap_addresses_APPEND,heap_addresses_def])
        \\ first_x_assum drule
        \\ qabbrev_tac `kk = (state.a + state.n + heap_length (state.r4 ⧺ state.r3))`
        \\ `~(is_final conf state kk)` by
             (fs [is_final_def,heap_length_APPEND,Abbr`kk`]
              \\ fs [heap_length_def,el_length_def])
        \\ fs [] \\ strip_tac
        \\ match_mp_tac IMP_reachable_addresses \\ asm_exists_tac \\ fs []
        \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,heap_length_APPEND]
        \\ full_simp_tac std_ss [heap_lookup_APPEND,heap_length_def,
             el_length_def,SUM,MAP,Abbr`kk`]
        \\ full_simp_tac std_ss [GSYM heap_length_def,heap_length_heap_expand]
        \\ ntac 2 (pop_assum mp_tac) \\ fs []
        \\ rfs [heap_lookup_def] \\ rveq \\ fs []
        \\ rw [] \\ asm_exists_tac \\ fs [])
  \\ reverse impl_tac
  >- (fs []
     \\ `0 < heap_length (state'.r3 ++ [DataElement xs' n b])` by fs [heap_length_APPEND,heap_length_def,el_length_def]
     \\ fs []
     \\ qsuff_tac `heap_map 0 state.heap ⊑ heap_map 0 state'.heap /\
                   (0 < heap_length state.r3 ==> heap_length state.r1 <= heap_length state'.r1)`
     >- (ntac 2 strip_tac
        \\ strip_tac >- metis_tac [SUBMAP_TRANS]
        \\ strip_tac \\ fs [])
     \\ reverse strip_tac
     >- (strip_tac
        \\ drule gc_move_list_IMP
        \\ strip_tac \\ fs [])
     \\ drule gc_move_list_thm
     \\ disch_then (qspec_then `l` mp_tac)
     \\ fs []
     \\ impl_tac
     \\ fs [])
  \\ fs []
  \\ drule gc_move_refs_lemma
  \\ ntac 3 (disch_then drule) \\ fs []
QED

val gc_move_list_heap_length = prove(
  ``!conf state state' xs ys.
      (gc_move_list conf state xs = (ys,state')) ==>
      (heap_length state.h1 <= heap_length state'.h1) /\
      (heap_length state.r1 <= heap_length state'.r1)``,
  ntac 6 strip_tac
  \\ drule gc_move_list_IMP
  \\ fs []);

val gc_move_data_heap_length = prove(
  ``!conf state state'.
      Abbrev (state' = gc_move_data conf state) ==>
      heap_length state.h1 <= heap_length state'.h1 ∧
      heap_length state.r1 <= heap_length state'.r1``,
  rewrite_tac [markerTheory.Abbrev_def]
  \\ recInduct (theorem "gc_move_data_ind")
  \\ ntac 4 strip_tac
  \\ once_rewrite_tac [gc_move_data_def]
  \\ Cases_on `state.h2` \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `h` \\ fs []
  \\ pairarg_tac \\ fs []
  \\ drule gc_move_list_IMP
  \\ strip_tac \\ strip_tac
  \\ fs []
  \\ qsuff_tac `heap_length state''.h1 <= heap_length (state''.h1 ++ [DataElement xs' n b])`
  >- decide_tac
  \\ fs [heap_length_APPEND]);

val gc_move_refs_heap_length = prove(
  ``!conf state state'.
      (gc_move_refs conf state = state') ==>
      heap_length state.h1 <= heap_length state'.h1 ∧
      heap_length state.r1 <= heap_length state'.r1``,
  recInduct (theorem "gc_move_refs_ind")
  \\ ntac 4 strip_tac
  \\ disch_then (mp_tac o GSYM)
  \\ once_rewrite_tac [gc_move_refs_def]
  \\ Cases_on `state.r2` \\ fs [heap_length_APPEND]
  \\ Cases_on `h` \\ fs []
  \\ pairarg_tac \\ fs []
  \\ drule gc_move_list_IMP
  \\ strip_tac \\ strip_tac
  \\ fs []);

val gc_move_loop_gc_inv = prove(
  ``!conf state h t.
      gc_inv conf state heap0 roots0 /\ (state.r2 = []) /\ (state.r4 = h::t) /\
      (state.r3 = []) ==>
      gc_inv conf (state with <|r2 := h::t; r4 := []|>) heap0 roots0``,
  rpt strip_tac
  \\ fs [gc_inv_def]
  \\ strip_tac
  >- fs []
  \\ qpat_x_assum `state.a + _ = conf.limit` mp_tac
  \\ qpat_x_assum `BIJ _ _ _` mp_tac
  \\ qpat_x_assum `!i j. _` mp_tac
  \\ once_rewrite_tac [CONS_APPEND]
  \\ rewrite_tac [APPEND_ASSOC]
  \\ rpt strip_tac \\ TRY (fs [] \\ NO_TAC)
  \\ qpat_x_assum `!i j. _` (qspecl_then [`i`,`j`] mp_tac)
  \\ fs []
  \\ strip_tac \\ fs []
  \\ `is_final conf state j = is_final conf (state with <|r4 := []; r2 := h::t|>) j` by fs [is_final_def,heap_length_def]
  \\ fs [] \\ fs []);

val reachable_addresses_gc_inv_r4 = prove(
  ``gc_inv conf state heap roots0 /\
    (state.r4 = DataElement l n b::t) /\ MEM (Pointer ptr u) l ==>
    reachable_addresses roots0 heap ptr``,
  rw [gc_inv_def] \\ fs []
  \\ `?i. FLOOKUP (heap_map 0 state.heap) i = SOME (state.a + state.n)` by
   (full_simp_tac std_ss [FLOOKUP_DEF,BIJ_DEF,SURJ_DEF,heap_map1_def,LET_DEF]
    \\ qpat_x_assum `!xx.bbb` kall_tac
    \\ fs [heap_addresses_APPEND,heap_addresses_def])
  \\ first_x_assum drule
  \\ `~(is_final conf state (state.a + state.n))` by
       (fs [is_final_def,heap_length_APPEND]
        \\ fs [heap_length_def,el_length_def])
  \\ fs [] \\ strip_tac
  \\ match_mp_tac IMP_reachable_addresses \\ asm_exists_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,heap_length_APPEND]
  \\ full_simp_tac std_ss [heap_lookup_APPEND,heap_length_def,
       el_length_def,SUM,MAP]
  \\ full_simp_tac std_ss [GSYM heap_length_def,heap_length_heap_expand]
  \\ ntac 2 (pop_assum mp_tac) \\ fs []
  \\ rfs [heap_lookup_def] \\ rveq \\ fs []
  \\ rw [] \\ asm_exists_tac \\ fs []);

Theorem gc_move_loop_thm:
   !conf state clock.
      conf.limit <= clock + heap_length state.h1 + heap_length state.r1 /\
      (state.r2 = []) /\ (state.r3 = []) /\
      gc_inv conf state heap roots0 ==>
        ?state'.
          (gc_move_loop conf state clock = state') /\
          ((heap_map 0 state.heap) SUBMAP (heap_map 0 state'.heap)) /\
          gc_inv conf state' heap roots0 /\
          (state'.h2 = []) /\
          (state'.r4 = []) /\
          (state'.r3 = []) /\
          (state'.r2 = [])
Proof
  recInduct (theorem "gc_move_loop_ind")
  \\ rpt strip_tac
  \\ once_rewrite_tac [gc_move_loop_def]
  \\ Cases_on `state.r4` \\ fs []
  >- (Cases_on `state.h2` \\ fs []
     \\ IF_CASES_TAC
     >- (sg `F`
        \\ fs [gc_inv_def]
        \\ fs [heap_length_APPEND,heap_length_CONS]
        \\ assume_tac
           (el_length_GT_0 |> Q.INST_TYPE [`:'a` |-> `:'b`,`:'b` |-> `:'a`] |> Q.SPEC `h`)
        \\ decide_tac)
     \\ fs []
     \\ qpat_x_assum `_ ==> _` mp_tac
     \\ reverse impl_tac
     >- (rpt strip_tac \\ fs []
        \\ qsuff_tac `heap_map 0 state.heap ⊑ heap_map 0 (gc_move_data conf state).heap`
        >- metis_tac [SUBMAP_TRANS]
        \\ qpat_x_assum `gc_inv _ _ _ _` kall_tac
        \\ drule gc_move_data_thm
        \\ rpt strip_tac
        \\ fs [])
     \\ drule gc_move_data_thm
     \\ rpt strip_tac \\ rfs []
     \\ qpat_x_assum `gc_inv _ _ _ _` mp_tac
     \\ once_rewrite_tac [gc_move_data_def]
     \\ simp []
     \\ IF_CASES_TAC
     >- simp [gc_inv_def]
     \\ Cases_on `h`
     >- simp [gc_inv_def]
     >- simp [gc_inv_def]
     \\ simp []
     \\ pairarg_tac
     \\ simp []
     \\ strip_tac
     \\ qpat_abbrev_tac `state'' = gc_move_data conf _`
     \\ qsuff_tac `heap_length state.h1 < heap_length state''.h1 /\ heap_length state.r1 <= heap_length state''.r1`
     >- decide_tac
     \\ drule gc_move_data_heap_length \\ fs []
     \\ drule gc_move_list_heap_length \\ fs []
     \\ fs [heap_length_APPEND]
     \\ fs [heap_length_def,el_length_def])
  \\ IF_CASES_TAC
  >- (sg `F`
     \\ fs [gc_inv_def]
     \\ fs [heap_length_APPEND,heap_length_CONS]
     \\ assume_tac (el_length_GT_0 |> Q.INST_TYPE [`:'a` |-> `:'b`,`:'b` |-> `:'a`] |> Q.SPEC `h`)
     \\ decide_tac)
  \\ fs []
  \\ drule gc_move_loop_gc_inv
  \\ fs [] \\ strip_tac
  \\ qpat_x_assum `_ ==> _` mp_tac
  \\ reverse impl_tac
  >- (rpt strip_tac \\ fs []
     \\ `heap_map 0 state.heap ⊑
         heap_map 0 (state with <|r4 := []; r2 := h::t|>).heap` by
            fs [gc_state_component_equality]
     \\ qsuff_tac `heap_map 0 (state with <|r4 := []; r2 := h::t|>).heap ⊑
                   heap_map 0 (gc_move_refs conf (state with <|r4 := []; r2 := h::t|>)).heap`
     >- metis_tac [SUBMAP_TRANS]
     \\ qpat_x_assum `gc_inv _ _ _ _` kall_tac
     \\ drule gc_move_refs_thm
     \\ rpt strip_tac
     \\ fs [])
  \\ drule gc_move_refs_thm
  \\ rpt strip_tac \\ rfs []
  \\ qsuff_tac `heap_length state.h1 <= heap_length state'.h1 /\ heap_length state.r1 < heap_length state'.r1`
  >- decide_tac
  \\ drule gc_move_refs_heap_length
  \\ strip_tac
  \\ strip_tac
  >- fs [gc_state_component_equality]
  \\ qsuff_tac `heap_length (state with <|r4 := []; r2 := h::t|>).r1 < heap_length state'.r1`
  >- fs [gc_state_component_equality]
  \\ qpat_x_assum `gc_move_refs _ _ = _` mp_tac
  \\ once_rewrite_tac [gc_move_refs_def]
  \\ Cases_on `(state with <|r4 := []; r2 := h::t|>).r2`
  >- fs [gc_state_component_equality]
  \\ fs []
  \\ rpt var_eq_tac
  \\ Cases_on `h` \\ fs []
  \\ qpat_x_assum `gc_inv conf state' heap _` kall_tac
  \\ qpat_x_assum `gc_inv _ _ _ _` mp_tac
  >- (simp [gc_inv_def] \\ strip_tac
     \\ fs [isDataElement_def])
  >- (simp [gc_inv_def] \\ strip_tac
     \\ fs [isDataElement_def])
  \\ strip_tac
  \\ pairarg_tac \\ fs []
  \\ strip_tac
  \\ qabbrev_tac `state1 = state'' with <|r3 := state''.r3 ++ [DataElement xs' n b]; r2 := t|>`
  \\ qsuff_tac `heap_length state1.r1 < heap_length state'.r1`
  >- (drule gc_move_list_IMP
     \\ strip_tac
     \\ unabbrev_all_tac
     \\ fs [gc_state_component_equality])
  \\ qsuff_tac `gc_inv conf state1 heap roots0`
  >- (strip_tac
     \\ drule gc_move_refs_thm
     \\ fs []
     \\ qsuff_tac `0 < heap_length state1.r3`
     >- fs []
     \\ unabbrev_all_tac
     \\ fs [gc_state_component_equality,heap_length_APPEND]
     \\ fs [heap_length_def,el_length_def])
  \\ drule gc_move_list_thm
  \\ disch_then (qspec_then `l` mp_tac)
  \\ impl_tac
  >- (drule pointers_ok
     \\ fs [] \\ rw [] THEN1 metis_tac []
     \\ imp_res_tac reachable_addresses_gc_inv_r4 \\ fs [])
  \\ fs []
  \\ strip_tac
  \\ qpat_x_assum `gc_inv _ _ _ _` kall_tac
  \\ drule (gc_move_list_IMP)
  \\ disch_then (mp_tac o GSYM)
  \\ unabbrev_all_tac
  \\ strip_tac
  \\ drule gc_move_refs_lemma
  \\ disch_then (qspecl_then [`l`,`n`,`b`,`xs'`,`t`,`state''`] mp_tac)
  \\ simp [gc_state_component_equality]
  \\ disch_then match_mp_tac
  \\ rw []
  \\ drule pointers_ok
  \\ fs [] \\ rw [] THEN1 metis_tac []
  \\ imp_res_tac reachable_addresses_gc_inv_r4 \\ fs []
QED

Theorem gc_inv_init:
   heap_ok heap conf.limit ==>
    gc_inv conf (empty_state with <| heap := heap; n := conf.limit;
                                     ok := (heap_length heap = conf.limit) |>) heap roots
Proof
  fs [heap_ok_def,gc_inv_def,empty_state_def,LET_THM]
  \\ rw []
  >- fs [FILTER_LEMMA]
  >- res_tac
  >- fs [heaps_similar_REFL]
  >- rw [heap_addresses_def,heap_map_EMPTY]
  \\ fs [heap_expand_def]
  \\ rw [heap_lookup_def]
  \\ imp_res_tac heap_map_EMPTY
  \\ fs [FLOOKUP_DEF]
QED

Theorem gen_gc_thm:
   !conf roots heap.
    roots_ok roots heap /\ heap_ok heap conf.limit ==>
    ?state.
      (gen_gc conf (roots,heap) =
      (ADDR_MAP (heap_map1 state.heap) roots,state)) /\
      (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM (heap_map 0 state.heap)) /\
      gc_inv conf state heap roots /\
      (state.h2 = []) /\
      (state.r4 = []) /\
      (state.r3 = []) /\
      (state.r2 = [])
Proof
  rpt strip_tac
  \\ imp_res_tac gc_inv_init
  \\ first_x_assum (qspec_then `roots` assume_tac)
  \\ fs [gen_gc_def]
  \\ pairarg_tac \\ fs []
  \\ drule gc_move_list_thm
  \\ disch_then (qspec_then `roots` mp_tac)
  \\ impl_tac
  >- (fs [roots_ok_def,isSomeDataOrForward_def,reachable_addresses_def]
      \\ metis_tac [RTC_RULES])
  \\ strip_tac \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ qispl_then [`conf`,`state`,`conf.limit`] mp_tac (gc_move_loop_thm
          |> Q.INST [`roots0`|->`roots`])
  \\ drule gc_move_list_IMP
  \\ simp [empty_state_def,gc_state_component_equality]
  \\ disch_then (mp_tac o GSYM)
  \\ strip_tac
  \\ impl_tac >- fs []
  \\ fs []
  \\ strip_tac
  \\ strip_tac
  >- (match_mp_tac ADDR_MAP_EQ
     \\ rpt strip_tac
     \\ fs [heap_map1_def,SUBMAP_DEF]
     \\ metis_tac [])
  \\ fs [heap_ok_def]
  \\ fs [heap_map1_def,SUBMAP_DEF]
  \\ metis_tac []
QED

Theorem LESS_IMP_heap_lookup:
   !xs j ys. j < heap_length xs ==> (heap_lookup j (xs ++ ys) = heap_lookup j xs)
Proof
  Induct \\ full_simp_tac (srw_ss()) [heap_length_def,heap_lookup_def]
  \\ SRW_TAC [] [] \\ `j - el_length h < SUM (MAP el_length xs)` by decide_tac
  \\ full_simp_tac std_ss []
QED

val heap_lookup_IMP_heap_addresses = save_thm("heap_lookup_IMP_heap_addresses",
    heap_lookup_IMP_heap_addresses_GEN
      |> Q.SPECL [`xs`,`0`]
      |> SIMP_RULE std_ss []
      |> GEN_ALL);

Theorem gen_gc_LENGTH:
   roots_ok roots heap /\
    heap_ok (heap:('a,'b) heap_element list) conf.limit ==>
    ?roots' state.
      (gen_gc conf (roots:'a heap_address list,heap) =
        (roots',state))
Proof
  rw []
  \\ imp_res_tac gen_gc_thm
  \\ fs []
  \\ rpt strip_tac
  \\ fs [gen_gc_def,gc_inv_def,LET_THM]
QED

val heap_lookup_AND_APPEND_IMP = prove(
  ``!xs n ys d d1.
      (heap_lookup n xs = SOME d) /\
      (heap_lookup n (xs++ys) = SOME d1) ==> (d1 = d)``,
  Induct
  \\ Induct_on `n`
  \\ fs [heap_lookup_def]
  \\ rpt strip_tac
  \\ res_tac);

val heap_lookup_AND_PREPEND_IMP = prove(
  ``!n xs ys d d1.
      (heap_lookup n ys = SOME d) /\
      (heap_lookup (heap_length xs + n) (xs++ys) = SOME d1) ==>
      (d1 = d)``,
  Induct
  \\ Induct
  \\ fs [heap_lookup_def,heap_length_def]
  THEN1 (rw [] \\ fs [])
  THEN1
    (rpt strip_tac
    \\ fs [el_length_NOT_0]
    \\ res_tac)
  THEN1 (rpt strip_tac \\ fs [])
  \\ rpt strip_tac
  \\ Induct_on `ys`
  \\ rpt strip_tac
  \\ fs []
  \\ res_tac
  \\ fs []);

val MEM_heap_expand_FALSE = prove(
  ``!n. ~(MEM (DataElement xs l d) (heap_expand n))``,
  Cases \\ fs [MEM,heap_expand_def]);

val FILTER_isForward_heap_expand_lemma = prove(
  ``!n. FILTER isForwardPointer (heap_expand n) = []``,
  fs [FILTER,heap_expand_def,isForwardPointer_def]
  \\ Cases
  \\ fs [isForwardPointer_def]);

val heap_lookup_CONS_IMP = prove(
  ``(heap_lookup j ys = SOME z) ==>
    (heap_lookup (j + heap_length [x]) (x::ys) = SOME z)``,
  fs [heap_lookup_def]
  \\ strip_tac
  \\ IF_CASES_TAC
  >- (Cases_on `x` \\ fs [heap_length_def,el_length_def])
  \\ IF_CASES_TAC
  \\ fs [heap_length_def,el_length_def]);

val heap_lookup_PREPEND_EXTEND = prove(
  ``!xs j ys z.
    (heap_lookup j ys = SOME z) ==>
    (heap_lookup (heap_length xs + j) (xs ++ ys) = SOME z)``,
  ho_match_mp_tac SNOC_INDUCT \\ strip_tac
  >- fs [heap_length_def]
  \\ fs [SNOC_APPEND]
  \\ fs [heap_length_APPEND]
  \\ ntac 2 strip_tac
  \\ rpt gen_tac
  \\ fs []
  \\ pop_assum (qspecl_then [`j + heap_length [x]`,`[x]++ys`] assume_tac)
  \\ strip_tac
  \\ qsuff_tac `heap_lookup (j + heap_length [x]) ([x] ++ ys) = SOME z`
  >- fs []
  \\ fs [APPEND]
  \\ fs [heap_lookup_CONS_IMP]);

Theorem gen_gc_ok:
   !conf roots heap.
    roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) conf.limit ==>
    ?state roots' heap'.
      (heap' = state.h1 ++ heap_expand state.n ++ state.r1) /\
      (gen_gc conf (roots:'a heap_address list,heap) =
        (roots',state)) /\
      state.ok /\
      (state.a = heap_length state.h1) /\
      roots_ok roots' heap' /\
      heap_ok heap' conf.limit
Proof
  rpt strip_tac
  \\ drule gen_gc_thm
  \\ disch_then drule
  \\ strip_tac
  \\ fs [gc_inv_def]
  \\ rpt strip_tac
  >- (fs [roots_ok_def,isSomeDataElement_def]
     \\ rpt strip_tac
     \\ fs [heap_map1_def]
     \\ imp_res_tac MEM_ADDR_MAP
     \\ res_tac
     \\ (`FLOOKUP (heap_map 0 state.heap) y = SOME ptr` by fs [FLOOKUP_DEF])
     \\ metis_tac [])
  \\ fs [heap_ok_def]
  \\ simp [heap_length_APPEND]
  \\ fs [heap_length_heap_expand]
  \\ strip_tac
  >- (fs [FILTER_APPEND]
     \\ fs [FILTER_isForward_heap_expand_lemma]
     \\ fs [EVERY_isDataElement_IMP_LEMMA])
  \\ `heap_length (state.h1 ++ heap_expand state.n) = state.a + state.n` by fs [heap_length_APPEND,heap_length_heap_expand]
  \\ rpt strip_tac
  >- (`?j. heap_lookup j state.h1 = SOME (DataElement xs l d)` by metis_tac [MEM_IMP_heap_lookup,MEM_APPEND]
     \\ `?i. (FLOOKUP (heap_map 0 state.heap) i = SOME j)` by (drule heap_lookup_IMP_heap_addresses
        \\ fs [BIJ_DEF,SURJ_DEF,heap_map1_def,FLOOKUP_DEF])
     \\ drule heap_lookup_EXTEND
     \\ disch_then (qspec_then `heap_expand state.n ++ state.r1` assume_tac)
     \\ fs []
     \\ res_tac
     \\ rveq
     \\ `is_final conf state j` by (simp [is_final_def,LET_THM]
        \\ imp_res_tac heap_lookup_LESS \\ fs [])
     \\ fs []
     \\ rveq
     \\ drule MEM_ADDR_MAP \\ strip_tac
     \\ fs [heap_map1_def,FLOOKUP_DEF]
     \\ res_tac \\ rfs []
     \\ rveq
     \\ res_tac
     \\ fs [isSomeDataElement_def])
  >- fs [MEM_heap_expand_FALSE]
  \\ `?j. heap_lookup j state.r1 = SOME (DataElement xs l d)` by metis_tac [MEM_IMP_heap_lookup,MEM_APPEND]
  \\ `?i. (FLOOKUP (heap_map 0 state.heap) i = SOME (state.a + state.n + j))` by (drule heap_lookup_IMP_heap_addresses_GEN
     \\ disch_then (qspec_then `state.a + state.n` assume_tac)
     \\ fs [BIJ_DEF,SURJ_DEF,heap_map1_def,FLOOKUP_DEF])
  \\ drule heap_lookup_PREPEND_EXTEND
  \\ disch_then (qspec_then `state.h1 ++ heap_expand state.n` mp_tac)
  \\ strip_tac \\ rfs []
  \\ res_tac
  \\ rveq
  \\ `is_final conf state (state.a + state.n + j)` by simp [is_final_def,LET_THM,heap_length_def]
  \\ fs []
  \\ rveq
  \\ drule MEM_ADDR_MAP \\ strip_tac
  \\ fs [heap_map1_def,FLOOKUP_DEF]
  \\ res_tac \\ rfs []
  \\ rveq
  \\ res_tac
  \\ fs [isSomeDataElement_def]
QED

val IN_heap_addresses_LESS = prove(
  ``!heap n k. n IN heap_addresses k heap ==> k <= n /\ n < k + heap_length heap``,
  Induct
  \\ fs [heap_addresses_def,heap_length_def]
  \\ rpt strip_tac
  \\ rpt var_eq_tac
  \\ res_tac
  \\ qspec_then `h` assume_tac el_length_NOT_0
  \\ decide_tac);

Theorem heap_lookup_EXTEND:
   !xs n ys x. (heap_lookup n xs = SOME x) ==>
                (heap_lookup n (xs ++ ys) = SOME x)
Proof
  Induct \\ full_simp_tac (srw_ss()) [heap_lookup_def] \\ SRW_TAC [] []
QED

Theorem gen_gc_related:
   !conf roots heap.
    roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) conf.limit ==>
    ?state f.
      (gen_gc conf (roots:'a heap_address list,heap) =
         (ADDR_MAP (FAPPLY f) roots,state)) /\
      (FDOM f = reachable_addresses roots heap) /\
      (heap_length (state.h1 ++ state.r1) =
       heap_length (heap_filter (FDOM f) heap)) /\
      gc_related f heap (state.h1 ++ heap_expand state.n ++ state.r1)
Proof
  rpt strip_tac
  \\ drule gen_gc_thm
  \\ disch_then drule
  \\ strip_tac \\ fs []
  \\ qexists_tac `heap_map 0 state.heap`
  \\ `(FAPPLY (heap_map 0 state.heap)) = heap_map1 state.heap` by fs [heap_map1_def,FUN_EQ_THM]
  \\ fs []
  \\ fs [gc_related_def,gc_inv_def,BIJ_DEF]
  \\ conj_asm1_tac
  THEN1
   (fs [EXTENSION] \\ rpt strip_tac
    \\ CONV_TAC (RAND_CONV (REWRITE_CONV [IN_DEF]))
    \\ rw [] \\ eq_tac \\ rw []
    THEN1 (fs [FLOOKUP_DEF] \\ metis_tac [])
    \\ fs [reachable_addresses_def]
    \\ rename [`RTC _ a1 a2`]
    \\ `a1 ∈ FDOM (heap_map 0 state.heap)` by res_tac
    \\ pop_assum mp_tac \\ pop_assum mp_tac
    \\ qspec_tac (`a2`,`a2`)
    \\ qspec_tac (`a1`,`a1`)
    \\ ho_match_mp_tac RTC_INDUCT
    \\ fs [] \\ rw []
    \\ first_x_assum match_mp_tac
    \\ fs [FLOOKUP_DEF]
    \\ fs [gc_edge_def]
    \\ pop_assum mp_tac
    \\ rename [`b1 IN _ ==> b2 IN _`]
    \\ strip_tac
    \\ qpat_x_assum `!i. _ => _` drule
    \\ fs [] \\ strip_tac \\ first_x_assum irule
    \\ fs [is_final_def] \\ CCONTR_TAC
    \\ fs [GSYM NOT_LESS] \\ fs [NOT_LESS]
    \\ rfs [heap_lookup_APPEND,heap_length_APPEND,heap_length_heap_expand]
    \\ rfs [] \\ fs [] \\ fs [heap_expand_def,heap_lookup_def])
  \\ strip_tac THEN1
   (qsuff_tac `heap_length (state.h1 ⧺ state.r1) =
       heap_length (heap_filter (heap_addresses 0 state.h1 ∪
              heap_addresses (state.a + state.n) state.r1)
           (state.h1 ++ heap_expand state.n ++ state.r1))`
    THEN1
     (fs [] \\ strip_tac
      \\ match_mp_tac (GEN_ALL heap_length_heap_filter_eq)
      \\ fs [FLOOKUP_DEF,BIJ_DEF] \\ asm_exists_tac \\ fs []
      \\ fs [FINITE_heap_addresses]
      \\ conj_tac THEN1 (metis_tac [FDOM_FINITE])
      \\ rw [] \\ res_tac \\ fs [])
    \\ qpat_x_assum `_ = state.a` (assume_tac o GSYM) \\ fs []
    \\ fs [heap_filter_def]
    \\ rewrite_tac [GSYM APPEND_ASSOC]
    \\ rewrite_tac [heap_filter_aux_APPEND,ADD_CLAUSES,
         heap_filter_aux_heap_addresses_UNION]
    \\ fs [heap_length_heap_expand]
    \\ rewrite_tac [heap_filter_aux_APPEND,ADD_CLAUSES,
         heap_filter_aux_heap_addresses_UNION]
    \\ fs [heap_length_APPEND,DECIDE ``(n=n+k:num)<=>(k=0)``]
    \\ rw [heap_expand_def] \\ fs [heap_filter_aux_def]
    \\ rw [heap_length_def,el_length_def]
    \\ imp_res_tac IN_heap_addresses_LESS \\ fs [heap_length_def]
    \\ once_rewrite_tac [UNION_COMM]
    \\ rewrite_tac [GSYM heap_length_def,heap_filter_aux_heap_addresses_UNION])
  \\ pop_assum kall_tac
  \\ rpt strip_tac
  >-
    (fs [INJ_DEF]
    \\ rpt strip_tac
    \\ `(FLOOKUP (heap_map 0 state.heap) x = SOME (heap_map1 state.heap x))` by fs [FLOOKUP_DEF,heap_map1_def]
    \\ res_tac \\ fs [isSomeDataElement_def])
  >- (`(FLOOKUP (heap_map 0 state.heap) i = SOME (heap_map1 state.heap i))` by fs [FLOOKUP_DEF]
    \\ res_tac \\ fs []
    \\ fs [isSomeDataElement_def])
  >-
    (`(FLOOKUP (heap_map 0 state.heap) i = SOME (heap_map1 state.heap i))` by fs [FLOOKUP_DEF]
    \\ res_tac \\ fs []
    \\ `is_final conf state (heap_map1 state.heap i)` by
      (simp [is_final_def,LET_THM]
      \\ fs [INJ_DEF,SURJ_DEF]
      \\ res_tac
      \\ fs [] \\ rpt var_eq_tac \\ fs []
      \\ drule IN_heap_addresses_LESS
      \\ simp [heap_length_def])
    \\ fs [])
  \\ `(FLOOKUP (heap_map 0 state.heap) i = SOME (heap_map1 state.heap i))` by fs [FLOOKUP_DEF]
  \\ res_tac \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ `is_final conf state (heap_map1 state.heap i)` by
    (simp [is_final_def,LET_THM]
    \\ fs [INJ_DEF,SURJ_DEF]
    \\ res_tac \\ fs [] \\ rpt var_eq_tac \\ fs []
    \\ drule IN_heap_addresses_LESS \\ strip_tac
    \\ simp [heap_length_def])
  \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ qpat_assum `!ptr d. _ ==> _ ` (qspecl_then [`ptr`, `u`] assume_tac)
  \\ fs []
QED

Theorem gc_forward_ptr_ok:
   !heap n a d c x. (gc_forward_ptr n heap a d c = (x,T)) ==> c
Proof
  Cases_on `c` \\ fs []
  \\ Induct
  \\ simp_tac std_ss [Once gc_forward_ptr_def]
  \\ rpt strip_tac
  \\ every_case_tac \\ fs [] \\ fs []
  \\ pairarg_tac \\ fs [] \\ rfs []
QED

Theorem gc_move_ok:
   (gc_move conf state x = (x',state')) /\ state'.ok ==> state.ok
Proof
  Cases_on `x`
  \\ fs [gc_move_def]
  \\ Cases_on `heap_lookup n state.heap`
  \\ fs []
  \\ rpt strip_tac
  \\ fs [gc_state_component_equality]
  \\ Cases_on `x`
  \\ fs [gc_state_component_equality,LET_THM]
  \\ pairarg_tac
  \\ Cases_on `conf.isRef b` \\ fs []
  \\ TRY pairarg_tac
  \\ fs [gc_state_component_equality]
  \\ rpt var_eq_tac
  \\ imp_res_tac gc_forward_ptr_ok
QED

Theorem gc_move_list_ok:
    !xs xs' state state'.
       (gc_move_list conf state xs = (xs',state')) /\ state'.ok ==>
       state.ok
Proof
  Induct \\ fs [gc_move_list_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ res_tac \\ fs [] \\ imp_res_tac gc_move_ok
QED

Theorem gc_move_data_ok:
    !conf s. (gc_move_data conf s).ok ==> s.ok
Proof
  recInduct (fetch "-" "gc_move_data_ind") \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [gc_move_data_def]
  \\ rpt (CASE_TAC \\ simp_tac (srw_ss()) [LET_THM])
  \\ pairarg_tac \\ fs [] \\ strip_tac \\ res_tac
  \\ imp_res_tac gc_move_list_ok
QED

Theorem gc_move_data_h2:
    !conf s. (gc_move_data conf s).ok ==>
              ((gc_move_data conf s).h2 = [])
Proof
  recInduct (fetch "-" "gc_move_data_ind") \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [gc_move_data_def]
  \\ rpt (CASE_TAC \\ simp_tac (srw_ss()) [LET_THM])
  \\ asm_rewrite_tac []
  \\ ntac 2 (pop_assum mp_tac)
  \\ simp_tac bool_ss [APPEND,GSYM APPEND_ASSOC]
  \\ pairarg_tac \\ fs [] \\ rpt strip_tac \\ res_tac
QED

Theorem gc_move_refs_ok:
    !conf s. (gc_move_refs conf s).ok ==> s.ok
Proof
  recInduct (fetch "-" "gc_move_refs_ind") \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [gc_move_refs_def]
  \\ rpt (CASE_TAC \\ simp_tac (srw_ss()) [LET_THM])
  \\ pairarg_tac \\ fs [] \\ strip_tac \\ res_tac
  \\ imp_res_tac gc_move_list_ok
QED

Theorem gc_move_loop_ok:
   !conf s c. (gc_move_loop conf s c).ok ==> s.ok
Proof
  recInduct (fetch "-" "gc_move_loop_ind") \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [gc_move_loop_def]
  \\ every_case_tac \\ fs []
  \\ strip_tac \\ res_tac
  \\ imp_res_tac gc_move_refs_ok
  \\ imp_res_tac gc_move_data_ok \\ fs []
QED

Theorem gc_move_list_length:
    !xs xs' state state'.
       (gc_move_list conf state xs = (xs',state')) ==>
       (LENGTH xs' = LENGTH xs)
Proof
  Induct \\ fs [gc_move_list_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ res_tac \\ fs []
QED

Theorem gen_gc_LENGTH:
   (gen_gc c (xs,heap) = (ys,s)) ==> (LENGTH ys = LENGTH xs)
Proof
  fs [gen_gc_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ imp_res_tac gc_move_list_length
  \\ rw [] \\ fs []
QED

Theorem gen_gc_a:
   (gen_gc c (xs,heap) = (ys,s1)) /\ s1.ok /\
    roots_ok xs heap /\ heap_ok heap c.limit ==>
    (s1.a = heap_length s1.h1)
Proof
  strip_tac \\ imp_res_tac gen_gc_thm
  \\ fs [] \\ rveq \\ fs [] \\ fs [gc_inv_def]
QED

val _ = export_theory();
