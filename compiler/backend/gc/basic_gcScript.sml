open preamble wordsTheory wordsLib integer_wordTheory gc_sharedTheory;

val _ = new_theory "basic_gc";

val gc_state_component_equality = DB.fetch "gc_shared" "gc_state_component_equality";

(* Copying GC which moves references to the end of the heap. This
implementation is a pre-stage to the generational GC. *)

val _ = Datatype `
  basic_gc_conf =
    <| limit : num
     ; isRef : ('a, 'b) heap_element -> bool
     |>`;

val gc_move_def = Define `
  (gc_move conf state (Data d) = (Data d, state)) /\
  (gc_move conf state (Pointer ptr d) =
     case heap_lookup ptr state.heap of
     | SOME (ForwardPointer ptr _ l) => (Pointer ptr d,state)
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
     | _ => (Pointer ptr d, state with <| ok := F |>))`;


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
  \\ fs []
  \\ Cases_on `heap_lookup n state.heap`
  \\ fs [gc_state_component_equality]
  \\ Cases_on `x`
  \\ fs [LET_THM,gc_state_component_equality]
  \\ Cases_on `conf.isRef (DataElement l n' b)`
  \\ pairarg_tac
  \\ fs []
  \\ TRY pairarg_tac
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
(* Runs a clock to simplify the termination argument *)
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

val basic_gc_def = Define `
  basic_gc conf (roots,heap) =
    let ok0 = (heap_length heap = conf.limit) in
      let state = empty_state
          with <| heap := heap
                ; n := conf.limit |> in
        (* move roots: *)
      let (roots,state) = gc_move_list conf state roots in
        (* move heap: *)
      let state = gc_move_loop conf state conf.limit in
      (* let ok = ok0 /\ state.ok /\ *)
      (*          (state.a = heap_length state.h1) /\ *)
      (*          (heap_length state.heap = conf.limit) in *)
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
  gc_inv conf state heap0 =
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
    (!el. MEM el (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) ==>
          conf.isRef el) /\
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
        !ptr d.
          MEM (Pointer ptr d) xs /\ is_final conf state j ==>
          ptr IN FDOM (heap_map 0 state.heap)`;

val heap_lookup_FLOOKUP = prove(
  ``!heap n k ptr u l.
      (heap_lookup n heap = SOME (ForwardPointer ptr u l)) ==>
      (FLOOKUP (heap_map k heap) (n+k) = SOME ptr)``,
  Induct
  \\ full_simp_tac std_ss [heap_lookup_def]
  \\ SRW_TAC [] []
     THEN1 (full_simp_tac (srw_ss()) [heap_map_def,FLOOKUP_DEF])
  \\ res_tac
  \\ pop_assum (ASSUME_TAC o Q.SPEC `k + el_length h`)
  \\ `n - el_length h + (k + el_length h) = n + k` by decide_tac
  \\ full_simp_tac std_ss []
  \\ Cases_on `h`
  \\ full_simp_tac std_ss [heap_map_def,el_length_def]
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,ADD_ASSOC,FAPPLY_FUPDATE_THM])
  |> Q.SPECL [`heap`,`n`,`0`]
  |> SIMP_RULE std_ss [];

val heap_lookup_SPLIT = store_thm("heap_lookup_SPLIT",
  ``!heap n x. (heap_lookup n heap = SOME x) ==>
               ?ha hb. (heap = ha ++ x::hb) /\ (n = heap_length ha)``,
  Induct \\ full_simp_tac std_ss [heap_lookup_def] \\ SRW_TAC [] []
  THEN1 (Q.LIST_EXISTS_TAC [`[]`,`heap`] \\ full_simp_tac (srw_ss()) [heap_length_def])
  \\ res_tac \\ Q.LIST_EXISTS_TAC [`h::ha`,`hb`]
  \\ full_simp_tac (srw_ss()) [heap_length_def] \\ decide_tac);


val gc_forward_ptr_thm = store_thm("gc_forward_ptr_thm",
  ``!ha. gc_forward_ptr (heap_length ha) (ha ++ DataElement ys l d::hb) a u c =
         (ha ++ ForwardPointer a u l::hb,c)``,
  Induct
  \\ fs [gc_forward_ptr_def,heap_length_def,APPEND,el_length_def,isDataElement_def,LET_DEF]
  \\ SRW_TAC [] []
  \\ Cases_on `h`
  \\ full_simp_tac std_ss [el_length_def]
  \\ decide_tac);

val full_simp = full_simp_tac std_ss

val heap_map_APPEND = prove(
  ``!xs n ys. (heap_map n (xs ++ ys)) =
              FUNION (heap_map n xs) (heap_map (n + heap_length xs) ys)``,
  Induct \\ TRY (Cases_on `h`) \\ full_simp_tac (srw_ss())
     [APPEND,heap_map_def,FUNION_DEF,FUNION_FEMPTY_1,heap_length_def,ADD_ASSOC]
  \\ full_simp_tac std_ss [FUNION_FUPDATE_1,el_length_def,ADD_ASSOC]);

val FDOM_heap_map = prove(
  ``!xs n. ~(n + heap_length xs IN FDOM (heap_map n xs))``,
  Induct \\ TRY (Cases_on `h`)
  \\ full_simp_tac (srw_ss()) [heap_map_def,heap_length_def,ADD_ASSOC]
  \\ rpt strip_tac \\ full_simp_tac std_ss [el_length_def,ADD_ASSOC]
  \\ TRY decide_tac \\ metis_tac [])
  |> Q.SPECL [`xs`,`0`] |> SIMP_RULE std_ss [];

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

val IN_heap_map_IMP = prove(
  ``!heap n k. n IN FDOM (heap_map k heap) ==> k <= n``,
  Induct
  \\ TRY (Cases_on `h`)
  \\ fs [heap_map_def]
  \\ rpt strip_tac
  \\ res_tac
  \\ fs [heap_length_def,el_length_def]
  \\ decide_tac);

val NOT_IN_heap_map = prove(
  ``!ha n. ~(n + heap_length ha IN FDOM (heap_map n (ha ++ DataElement ys l d::hb)))``,
  Induct
  \\ full_simp_tac (srw_ss()) [heap_map_def,APPEND,heap_length_def]
  \\ rpt strip_tac
  \\ imp_res_tac IN_heap_map_IMP
  \\ full_simp_tac std_ss [ADD_ASSOC]
  \\ res_tac
  THEN1 (full_simp_tac std_ss [el_length_def] \\ decide_tac)
  \\ Cases_on `h`
  \\ full_simp_tac std_ss [heap_map_def]
  \\ res_tac
  \\ full_simp_tac (srw_ss()) [el_length_def,ADD_ASSOC]
  \\ res_tac
  \\ decide_tac)
  |> Q.SPECL [`ha`,`0`] |> SIMP_RULE std_ss []

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

val heap_length_APPEND = store_thm("heap_length_APPEND",
  ``heap_length (xs ++ ys) = heap_length xs + heap_length ys``,
  SRW_TAC [] [heap_length_def,SUM_APPEND]);

val cons_append_lemma = prove(
  ``!x xs. x :: xs = [x] ++ xs``,
  rw []);

val heaps_similar_lemma = prove(
  ``!ha heap0 hb ptr ys l d a l.
      heaps_similar heap0 (ha ++ [DataElement ys l d] ++ hb) ==>
      heaps_similar heap0 (ha ++ [ForwardPointer ptr a l] ++ hb)``,
  full_simp_tac std_ss [heaps_similar_def,APPEND,GSYM APPEND_ASSOC]
  \\ rpt strip_tac
  \\ imp_res_tac EVERY2_SPLIT \\ full_simp_tac std_ss []
  \\ imp_res_tac LIST_REL_LENGTH
  \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ full_simp_tac std_ss [EVERY2_APPEND,LIST_REL_def]
  \\ EVAL_TAC \\ full_simp_tac std_ss [isForwardPointer_def]
  \\ qpat_assum `DataElement ys l d = y` (mp_tac o GSYM)
  \\ full_simp_tac (srw_ss()) [el_length_def]);

val heaps_similar_IMP_heap_length = prove(
  ``!xs ys. heaps_similar xs ys ==> (heap_length xs = heap_length ys)``,
  Induct \\ Cases_on `ys`
  \\ full_simp_tac (srw_ss()) [heaps_similar_def,heap_length_def]
  \\ rpt strip_tac \\ Cases_on `isForwardPointer h`
  \\ full_simp_tac std_ss []);

val heap_similar_Data_IMP = prove(
  ``heaps_similar heap0 (ha ++ DataElement ys l d::hb) ==>
    ?ha0 hb0. (heap0 = ha0 ++ DataElement ys l d::hb0) /\
              (heap_length ha = heap_length ha0)``,
  rpt strip_tac \\ full_simp_tac std_ss [heaps_similar_def]
  \\ imp_res_tac EVERY2_SPLIT \\ full_simp_tac std_ss [isForwardPointer_def]
  \\ pop_assum (ASSUME_TAC o GSYM) \\ full_simp_tac std_ss []
  \\ Q.LIST_EXISTS_TAC [`ys1`,`ys2`] \\ full_simp_tac std_ss []
  \\ `heaps_similar ys1 ha` by full_simp_tac std_ss [heaps_similar_def]
  \\ full_simp_tac std_ss [heaps_similar_IMP_heap_length]);


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

val el_length_NOT_0 = prove(
  ``!el. el_length el <> 0``,
  Cases \\ fs [el_length_def]);

val NOT_IN_heap_addresses_gt = prove(
  ``!xs m n. (heap_length xs <= m) ==> ~(m IN heap_addresses 0 xs)``,
  Induct
  \\ rw []
  \\ fs [heap_addresses_def]
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [cons_append_lemma]
  \\ simp [heap_length_APPEND]
  \\ rpt strip_tac
  >- (fs [heap_length_def]
     \\ fs [el_length_NOT_0])
  \\ `(m - heap_length [h]) IN heap_addresses 0 xs` by cheat
  \\ `heap_length xs <= (m - heap_length [h])` by cheat
  \\ res_tac
  );

val heap_addresses_APPEND = prove(
  ``!a h1 h2.
    heap_addresses a (h1 ++ h2) =
    heap_addresses a h1 UNION heap_addresses (a + heap_length h1) h2``,
  Induct_on `h1`
  THEN1 fs [heap_addresses_def,heap_length_def]
  \\ fs [heap_addresses_def]
  \\ rpt strip_tac
  \\ fs [INSERT_UNION_EQ,heap_length_def]);



val heap_lookup_PREFIX = store_thm("heap_lookup_PREFIX",
  ``!xs. (heap_lookup (heap_length xs) (xs ++ x::ys) = SOME x)``,
  Induct \\ full_simp_tac (srw_ss()) [heap_lookup_def,APPEND,heap_length_def]
  \\ SRW_TAC [] [] \\ Cases_on `h`
  \\ full_simp_tac std_ss [el_length_def] \\ decide_tac);


val gc_move_thm = prove(
  ``!x state.
       gc_inv conf state heap0 /\
       (!ptr u. (x = Pointer ptr u) ==> isSomeDataOrForward (heap_lookup ptr state.heap)) ==>
       ?state'.
         (gc_move conf state x =
         (ADDR_APPLY (heap_map1 state'.heap) x,state')) /\
         (!ptr u. (x = Pointer ptr u) ==> ptr IN FDOM (heap_map 0 state'.heap)) /\
         (!ptr. isSomeDataOrForward (heap_lookup ptr state.heap) =
                isSomeDataOrForward (heap_lookup ptr state'.heap)) /\
         ((heap_map 0 state.heap) SUBMAP (heap_map 0 state'.heap)) /\
         gc_inv conf state' heap0``,

  Cases_on `x`
  \\ fs [gc_move_def,ADDR_APPLY_def]
  \\ rpt strip_tac
  \\ fs [isSomeDataOrForward_def,isSomeForwardPointer_def,isSomeDataElement_def]
  >- (imp_res_tac heap_lookup_FLOOKUP
     \\ fs [heap_map1_def,FLOOKUP_DEF])
  \\ fs [isSomeDataElement_def]
  \\ imp_res_tac heap_lookup_SPLIT
  \\ rw []

  (* isRef *)
  >-
    (pairarg_tac
    \\ simp []
    \\ full_simp [gc_forward_ptr_thm]
    \\ simp [heap_map1_def]
    \\ qabbrev_tac `r = state.a + (state.n − (l + 1))`
    \\ qabbrev_tac `rheap = state.r4 ++ state.r3 ++ state.r2 ++ state.r1`
    \\ qabbrev_tac `lheap = state.h1 ++ state.h2`
    \\ assume_tac (heap_map_ForwardPointer_lemma |> Q.SPEC `r`)
    \\ `~(heap_length ha IN FDOM (heap_map 0 (ha ++ DataElement ys l d::hb)))` by all_tac
    >- full_simp_tac std_ss [NOT_IN_heap_map]
    \\ qpat_assum `_ = heap` (assume_tac o GSYM)
    \\ simp []
    \\ rpt strip_tac
    >- metis_tac [isSomeDataOrForward_lemma_expanded]
    \\ `l+1 <= state.n` by all_tac
    >- cheat                    (* simple *)
    \\ full_simp [gc_inv_def,LET_THM] \\ simp [gc_state_component_equality]
    \\ full_simp []
    \\ rpt strip_tac
    \\ TRY (unabbrev_all_tac \\ fs [] \\ NO_TAC)
    >-                          (* lengths: heap_length = conf.limit *)
      (unabbrev_all_tac
      \\ qpat_assum `_ = conf.limit` kall_tac
      \\ qpat_assum `_ = conf.limit` (mp_tac o GSYM)
      \\ qpat_assum `_ = state.a` (assume_tac o GSYM)
      \\ full_simp [GSYM (EVAL ``[DataElement ys l d] ++ state.r4 ++ state.r3 ++ state.r2 ++ state.r1``)]
      \\ simp [heap_length_APPEND]
      \\ simp [heap_length_def]
      \\ fs [GSYM heap_length_def,el_length_def])
    >-                          (* lengths *)
      (qpat_assum `_ = state.n` mp_tac
      \\ simp [FILTER_APPEND,heap_length_APPEND,
               isForwardPointer_def,heap_length_def,el_length_def,SUM_APPEND])
    >-                          (* lengths *)
      (qpat_assum `_ = conf.limit` mp_tac
      \\ once_rewrite_tac [cons_append_lemma]
      \\ simp [heap_length_APPEND]
      \\ simp [heap_length_def,el_length_def])
    >-                          (* heaps_similar *)
      (qpat_assum `heaps_similar _ _` mp_tac
      \\ once_rewrite_tac [cons_append_lemma]
      \\ simp []
      \\ strip_tac
      \\ drule heaps_similar_lemma
      \\ fs [])
    >- fs [isDataElement_def]
    >-                          (* BIJ *)
      (qabbrev_tac `heap' = ha ++ DataElement ys l d::hb`
      \\ `~(r IN heap_addresses 0 lheap)` by all_tac
      >-
        (unabbrev_all_tac
        \\ qpat_assum `_ = state.a` (assume_tac o GSYM)
        \\ simp []
        \\ `heap_length lheap <= state.n + heap_length lheap − (l + 1)` by decide_tac
        \\ fs [NOT_IN_heap_addresses_gt])
      \\ `~(r IN heap_addresses (state.a + state.n) rheap)` by all_tac
      >-
        (unabbrev_all_tac
        \\ `state.a + (state.n − (l + 1)) < state.a + state.n` by decide_tac
        \\ fs [NOT_IN_heap_addresses_less])
      \\ `heap_addresses r (DataElement ys l d::rheap) =
          (r INSERT heap_addresses (state.a + state.n) rheap)` by all_tac
      >-
        (unabbrev_all_tac
        \\ once_rewrite_tac [cons_append_lemma]
        \\ simp [heap_addresses_APPEND]
        \\ simp [heap_length_APPEND]
        \\ simp [heap_addresses_def]
        \\ simp [UNION_COMM]
        \\ simp [GSYM INSERT_SING_UNION]
        \\ simp [heap_length_def] \\ simp [el_length_def])
      \\ once_rewrite_tac [UNION_COMM]
      \\ simp [INSERT_UNION_EQ]
      \\ `(λa'. (heap_map 0 heap' |+ (heap_length ha,r)) ' a') =
          ((heap_length ha =+ r) (\a. heap_map 0 heap' ' a))` by all_tac
      >- simp [FUN_EQ_THM,APPLY_UPDATE_THM,FAPPLY_FUPDATE_THM]
      \\ drule BIJ_UPDATE
      \\ disch_then drule
      \\ simp [IN_UNION]
      \\ ntac 2 (disch_then drule)
      \\ simp [UNION_COMM,heap_map1_def])
    \\ Cases_on `i = heap_length ha`
    >-                          (* yes *)
      (`j = r` by all_tac
      >- full_simp [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
      \\ simp []
      \\ qpat_abbrev_tac `st = state with <|r4 := _; n := _; ok := T; heap := _ |>`
      \\ rename1
      \\ `~(is_final conf (state with
              <|r4 := DataElement ys l d::state.r4;
                n := state.n − (l + 1); ok := T;
                heap := ha ++ ForwardPointer r a l::hb|>) r)` by all_tac
      >- cheat
      \\ simp []
      \\ imp_res_tac heap_similar_Data_IMP
      \\ simp [heap_lookup_PREFIX]
      \\ cheat
      )
    \\ cheat)
  \\ cheat);

val gc_move_ALT = store_thm("gc_move_ALT",
  ``gc_move conf state y =
     let (y', state') = gc_move conf (state with <| h2 := []; r4 := [] |>) y in
       (y', state' with <| h2 := state.h2 ++ state'.h2; r4 := state'.r4 ++ state.r4 |>)``,
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
  \\ fs [gc_state_component_equality]);

val gc_move_list_thm = prove(
  ``!xs state.
    gc_inv conf state heap0 /\
    (!ptr u. MEM (Pointer ptr u) (xs:'a heap_address list) ==>
             isSomeDataOrForward (heap_lookup ptr state.heap)) ==>
    ?state'.
      (gc_move_list conf state xs =
        (ADDR_MAP (heap_map1 state'.heap) xs,state')) /\
      (!ptr u. MEM (Pointer ptr u) xs ==> ptr IN FDOM (heap_map 0 state'.heap)) /\
      (!ptr. isSomeDataOrForward (heap_lookup ptr state.heap) =
             isSomeDataOrForward (heap_lookup ptr state'.heap)) /\
      ((heap_map 0 state.heap) SUBMAP (heap_map 0 state'.heap)) /\
      gc_inv conf state' heap0``,
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
              isSomeDataOrForward (heap_lookup ptr state'.heap)` by all_tac
  THEN1
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

val gc_move_list_ALT = store_thm("gc_move_list_ALT",
  ``!ys state.
      gc_move_list conf state ys =
        let (ys', state') = gc_move_list conf (state with <| h2 := []; r4 := [] |>) ys in
        (ys',state' with <| h2 := state.h2 ++ state'.h2; r4 := state'.r4 ++ state.r4 |>)``,
  Induct
  THEN1 fs [gc_move_list_def,LET_DEF,gc_state_component_equality]
  \\ pop_assum (assume_tac o GSYM)
  \\ once_rewrite_tac [gc_move_list_def]
  \\ once_rewrite_tac [gc_move_ALT]
  \\ rpt strip_tac
  \\ fs []
  \\ pairarg_tac \\ fs [] \\ pop_assum mp_tac
  \\ pairarg_tac \\ fs []
  \\ rpt strip_tac
  \\ rpt var_eq_tac
  \\ qpat_assum `!state. _` (fn th => once_rewrite_tac [GSYM th])
  \\ fs []
  \\ rpt (pairarg_tac \\ fs [] \\ pop_assum mp_tac));

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

val LESS_IMP_heap_lookup = store_thm("LESS_IMP_heap_lookup",
  ``!xs j ys. j < heap_length xs ==> (heap_lookup j (xs ++ ys) = heap_lookup j xs)``,
  Induct \\ full_simp_tac (srw_ss()) [heap_length_def,heap_lookup_def]
  \\ SRW_TAC [] [] \\ `j - el_length h < SUM (MAP el_length xs)` by decide_tac
  \\ full_simp_tac std_ss []);

val NOT_LESS_IMP_heap_lookup = store_thm("NOT_LESS_IMP_heap_lookup",
  ``!xs j ys. ~(j < heap_length xs) ==>
              (heap_lookup j (xs ++ ys) = heap_lookup (j - heap_length xs) ys)``,
  Induct \\ full_simp_tac (srw_ss()) [heap_length_def,heap_lookup_def]
  \\ SRW_TAC [] [SUB_PLUS]
  THEN1 (Cases_on `h` \\ full_simp_tac std_ss [el_length_def] \\ `F` by decide_tac)
  THEN1 (Cases_on `h` \\ full_simp_tac std_ss [el_length_def] \\ `F` by decide_tac));

val GREATER_IMP_heap_lookup = prove(
  ``!ys xs j .
    (heap_length (xs ++ ys) <= j + heap_length ys) ==>
    (heap_lookup j (xs ++ ys) = heap_lookup (j - heap_length xs) ys)``,
  fs [heap_length_APPEND,NOT_LESS_IMP_heap_lookup]);

val heap_similar_Data_IMP_DataOrForward = prove(
  ``!heap0 heap1 ptr.
      heaps_similar heap0 heap1 /\ isSomeDataElement (heap_lookup ptr heap0) ==>
      isSomeDataOrForward (heap_lookup ptr heap1)``,
  Induct \\ Cases_on `heap1` \\ full_simp_tac (srw_ss()) [heaps_similar_def]
  \\ full_simp_tac std_ss [heap_lookup_def]
  THEN1 (full_simp_tac (srw_ss()) [isSomeDataElement_def,isSomeDataOrForward_def])
  \\ rpt GEN_TAC \\ Cases_on `ptr = 0` \\ full_simp_tac std_ss [] THEN1
   (Cases_on `isForwardPointer h` \\ full_simp_tac std_ss []
    \\ rpt strip_tac \\ Cases_on `h`
    \\ full_simp_tac (srw_ss()) [isSomeDataElement_def,isSomeDataOrForward_def,
         isDataElement_def,isForwardPointer_def,isSomeForwardPointer_def])
  \\ strip_tac \\ `(el_length h = el_length h')` by metis_tac []
  \\ full_simp_tac std_ss [] \\ SRW_TAC [] [] \\ full_simp_tac std_ss []
  THEN1 full_simp_tac std_ss [isSomeDataElement_def]
  \\ full_simp_tac std_ss [] \\ res_tac);

val gc_move_data_thm = prove(
  ``!conf state.
      gc_inv conf state heap0 /\
      (state.r3 = []) /\ (state.r2 = []) ==>
      ?state'.
        (gc_move_data conf state = state') /\
        ((heap_map 0 state.heap) SUBMAP (heap_map 0 state'.heap)) /\
        gc_inv conf state' heap0 /\
        (state'.h2 = [])``,

  recInduct (theorem "gc_move_data_ind")
  \\ rpt strip_tac
  \\ once_rewrite_tac [gc_move_data_def]
  \\ BasicProvers.TOP_CASE_TAC  (* state.h2 *)
  >- fs []                      (* = [] *)
  \\ `isDataElement h` by all_tac
  >- (qpat_assum `gc_inv _ _ _` mp_tac
     \\ simp [gc_inv_def]
     \\ pairarg_tac
     \\ fs [])
  \\ `~(conf.limit < heap_length (state.h1 ++ h::t))` by all_tac
  >- (qpat_assum `gc_inv _ _ _` mp_tac
     \\ simp [gc_inv_def])
  \\ full_simp []
  \\ fs [isDataElement_def]
  \\ pairarg_tac \\ simp []
  \\

  cheat);

val gc_move_refs_thm = prove(
  ``!state.
      gc_inv conf state heap0 ==>
      ?state'.
        (gc_move_refs conf state = state') /\
        ((heap_map 0 state.heap) SUBMAP (heap_map 0 state'.heap)) /\
        gc_inv conf state' heap0``,
  cheat);

val gc_move_loop_thm = prove(
  ``!n state.
      conf.limit <= n + LENGTH state.h1 + LENGTH state.r1 /\
      (* (state.r2 = []) /\ (state.r3 = []) /\ *)
      gc_inv conf state heap ==>
        ?state'.
          (gc_move_loop conf state n = state') /\
          ((heap_map 0 state.heap) SUBMAP (heap_map 0 state'.heap)) /\
          gc_inv conf state' heap /\
          (state'.h2 = []) /\
          (state'.r4 = []) /\
          (state'.r3 = []) /\
          (state'.r2 = [])``,
  cheat);


val FILTER_LEMMA = prove(
  ``!heap. (FILTER isForwardPointer heap = []) ==>
           (FILTER (\h. ~isForwardPointer h) heap = heap)``,
  Induct \\ full_simp_tac (srw_ss()) [] \\ SRW_TAC [] []);

val heaps_similar_REFL = prove(
  ``!xs. (FILTER isForwardPointer xs = []) ==> heaps_similar xs xs``,
  Induct \\ full_simp_tac (srw_ss()) [heaps_similar_def] \\ SRW_TAC [] []);

val heap_map_EMPTY = prove(
  ``!xs n. (FILTER isForwardPointer xs = []) ==> (FDOM (heap_map n xs) = {})``,
  Induct \\ TRY (Cases_on `h`)
  \\ full_simp_tac (srw_ss()) [heap_map_def,isForwardPointer_def]);

val FILTER_LEMMA = prove(
  ``!heap. (FILTER isForwardPointer heap = []) ==>
           (FILTER (\h. ~isForwardPointer h) heap = heap)``,
  Induct \\ full_simp_tac (srw_ss()) [] \\ SRW_TAC [] []);

val heaps_similar_REFL = prove(
  ``!xs. (FILTER isForwardPointer xs = []) ==> heaps_similar xs xs``,
  Induct \\ full_simp_tac (srw_ss()) [heaps_similar_def] \\ SRW_TAC [] []);

val heap_map_EMPTY = prove(
  ``!xs n. (FILTER isForwardPointer xs = []) ==> (FDOM (heap_map n xs) = {})``,
  Induct \\ TRY (Cases_on `h`)
  \\ full_simp_tac (srw_ss()) [heap_map_def,isForwardPointer_def]);

val gc_inv_init = prove(
  ``heap_ok heap conf.limit ==>
    gc_inv conf (empty_state with <| heap := heap; n := conf.limit |>) heap``,
  fs [heap_ok_def,gc_inv_def,empty_state_def,LET_THM]
  \\ rw []
  THEN1 (fs [heap_length_def])
  THEN1 (fs [heap_length_def])
  THEN1 fs [FILTER_LEMMA]
  THEN1 res_tac
  THEN1 fs [heaps_similar_REFL]
  THEN1 rw [heap_addresses_def,heap_map_EMPTY]
  \\ fs [heap_expand_def]
  \\ rw [heap_lookup_def]
  \\ imp_res_tac heap_map_EMPTY
  \\ fs [FLOOKUP_DEF]);

(* val gc_inv_imp_n = prove( *)
(*   ``gc_inv conf state heap ==> *)
(*     (state.n = conf.limit − state.a − state.r) /\ *)
(*     (state.a + state.n + state.r = conf.limit)``, *)
(*   fs [gc_inv_def,LET_THM] *)
(*   \\ strip_tac *)
(*   \\ decide_tac); *)

val ADDR_MAP_EQ = prove(
  ``!xs. (!p d. MEM (Pointer p d) xs ==> (f p = g p)) ==>
         (ADDR_MAP f xs = ADDR_MAP g xs)``,
  Induct \\ TRY (Cases_on `h`) \\ full_simp_tac (srw_ss()) [ADDR_MAP_def]
  \\ metis_tac []);

val basic_gc_thm = store_thm("basic_gc_thm",
  ``roots_ok roots heap /\ heap_ok (heap : ('a,'b) heap_element list) conf.limit ==>
      ?state.
        (basic_gc conf (roots : 'a heap_address list,heap) =
          (ADDR_MAP (heap_map1 state.heap) roots,state)) /\
        (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM (heap_map 0 state.heap)) /\
        gc_inv conf state heap /\
        (state.h2 = []) /\
        (state.r4 = []) /\
        (state.r3 = []) /\
        (state.r2 = [])``,
  rpt strip_tac
  \\ imp_res_tac gc_inv_init
  \\ fs [basic_gc_def]
  \\ pairarg_tac
  \\ fs []
  \\ drule gc_move_list_thm
  \\ disch_then (qspec_then `roots` mp_tac)
  \\ impl_tac
  THEN1 (fs [roots_ok_def,isSomeDataOrForward_def] \\ metis_tac [])
  \\ strip_tac \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ mp_tac (Q.SPECL [`conf.limit`,`state`] gc_move_loop_thm)
  \\ fs []
  \\ strip_tac
  \\ fs []
  \\ rpt strip_tac
  THEN1
    (match_mp_tac ADDR_MAP_EQ
    \\ rpt strip_tac
    \\ fs [heap_map1_def,SUBMAP_DEF]
    \\ metis_tac [])
  \\ TRY (fs [heap_ok_def,gc_inv_def,LET_THM] \\ NO_TAC)
  \\ fs [heap_map1_def,SUBMAP_DEF]
  \\ metis_tac []);

val MEM_ADDR_MAP = prove(
  ``!xs f ptr u. MEM (Pointer ptr u) (ADDR_MAP f xs) ==>
                 ?y. MEM (Pointer y u) xs /\ (f y = ptr)``,
  Induct \\ TRY (Cases_on `h`) \\ full_simp_tac (srw_ss()) [ADDR_MAP_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [] \\ res_tac \\ metis_tac []);

val heap_length_heap_expand = store_thm("heap_length_heap_expand",
  ``!n. heap_length (heap_expand n) = n``,
  Cases \\ EVAL_TAC \\ full_simp_tac (srw_ss()) [el_length_def,ADD1,SUM_ACC_DEF]);

val EVERY_isDataElement_IMP_LEMMA = prove(
  ``!heap2. EVERY isDataElement heap2 ==> (FILTER isForwardPointer heap2 = [])``,
  Induct \\ full_simp_tac (srw_ss()) [isDataElement_def] \\ rpt strip_tac
  \\ full_simp_tac (srw_ss()) [isForwardPointer_def]);

val heap_lookup_LESS = store_thm("heap_lookup_LESS",
  ``!xs n. (heap_lookup n xs = SOME x) ==> n < heap_length xs``,
  Induct \\ full_simp_tac std_ss [heap_lookup_def] \\ SRW_TAC [] []
  \\ res_tac \\ Cases_on `h` \\ full_simp_tac (srw_ss())
      [heap_length_def,el_length_def] \\ decide_tac);

val LESS_IMP_heap_lookup = store_thm("LESS_IMP_heap_lookup",
  ``!xs j ys. j < heap_length xs ==> (heap_lookup j (xs ++ ys) = heap_lookup j xs)``,
  Induct \\ full_simp_tac (srw_ss()) [heap_length_def,heap_lookup_def]
  \\ SRW_TAC [] [] \\ `j - el_length h < SUM (MAP el_length xs)` by decide_tac
  \\ full_simp_tac std_ss []);

val isSome_heap_looukp_IMP_APPEND = prove(
  ``!xs ptr. isSomeDataElement (heap_lookup ptr xs) ==>
             isSomeDataElement (heap_lookup ptr (xs ++ ys))``,
  full_simp_tac std_ss [isSomeDataElement_def] \\ rpt strip_tac
  \\ imp_res_tac heap_lookup_LESS \\ imp_res_tac LESS_IMP_heap_lookup
  \\ full_simp_tac (srw_ss()) []);

val MEM_IMP_heap_lookup = store_thm("MEM_IMP_heap_lookup",
  ``!xs x. MEM x xs ==> ?j. (heap_lookup j xs = SOME x)``,
  Induct \\ full_simp_tac std_ss [MEM,heap_lookup_def,heap_addresses_def]
  \\ SRW_TAC [] [] \\ res_tac THEN1 metis_tac []
  \\ qexists_tac `j + el_length h` \\ full_simp_tac std_ss [] \\ SRW_TAC [] []
  \\ Cases_on `h` \\ full_simp_tac std_ss [el_length_def] \\ `F` by decide_tac);

val heap_lookup_IMP_heap_addresses_GEN = prove(
  ``!xs n x j. (heap_lookup j xs = SOME x) ==> n + j IN heap_addresses n xs``,
  Induct \\ full_simp_tac std_ss [MEM,heap_lookup_def,heap_addresses_def]
  \\ SRW_TAC [] [] \\ res_tac
  \\ pop_assum (mp_tac o Q.SPEC `n + el_length h`)
  \\ `n + el_length h + (j - el_length h) = n + j` by decide_tac
  \\ metis_tac []);

val heap_lookup_IMP_heap_addresses =
    heap_lookup_IMP_heap_addresses_GEN
      |> Q.SPECL [`xs`,`0`]
      |> SIMP_RULE std_ss []
      |> GEN_ALL;

val basic_gc_LENGTH = store_thm("basic_gc_LENGTH",
  ``roots_ok roots heap /\
    heap_ok (heap:('a,'b) heap_element list) conf.limit ==>
    ?roots' state.
      (basic_gc conf (roots:'a heap_address list,heap) =
        (roots',state))``,
  rw []
  \\ imp_res_tac basic_gc_thm
  \\ fs []
  \\ rpt strip_tac
  \\ fs [basic_gc_def,gc_inv_def,LET_THM]);

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

val basic_gc_ok = store_thm("basic_gc_ok",
  ``roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) conf.limit ==>
    ?roots' state.
      let heap' = state.h1 ++ heap_expand state.n ++ state.r1 in
      (basic_gc conf (roots:'a heap_address list,heap) =
        (roots',state)) /\
      state.ok /\
      (* state.a + state.r <= conf.limit /\ *)
      roots_ok roots' heap' /\
      heap_ok heap' conf.limit``,
  rpt strip_tac
  \\ mp_tac basic_gc_thm
  \\ fs [LET_THM]
  \\ strip_tac
  \\ qexists_tac `ADDR_MAP (heap_map1 state.heap) roots`
  \\ qexists_tac `state`
  \\ fs [gc_inv_def,LET_THM]
  \\ rpt strip_tac
  THEN1
    (fs [roots_ok_def,isSomeDataElement_def]
    \\ rpt strip_tac
    \\ fs [heap_map1_def]
    \\ imp_res_tac MEM_ADDR_MAP
    \\ res_tac
    \\ (`FLOOKUP (heap_map 0 state.heap) y = SOME ptr` by
      fs [FLOOKUP_DEF])
    \\ metis_tac [])
  \\ fs [heap_ok_def]
  \\ rpt strip_tac
  THEN1
    fs [SUM_APPEND,heap_length_heap_expand,heap_length_APPEND]
  THEN1
    (fs [FILTER_APPEND,EVERY_isDataElement_IMP_LEMMA]
    \\ fs [FILTER_isForward_heap_expand_lemma])
  THEN1                           (* in h1 heap *)
    (`?j. heap_lookup j state.h1 = SOME (DataElement xs l d)` by all_tac
    THEN1 metis_tac [MEM_IMP_heap_lookup,MEM_APPEND]
    \\ `?i. (FLOOKUP (heap_map 0 state.heap) i = SOME j)` by all_tac
    THEN1
      (imp_res_tac heap_lookup_IMP_heap_addresses
      \\ fs [BIJ_DEF,SURJ_DEF,heap_map1_def,FLOOKUP_DEF])
    \\ res_tac
    \\ `is_final conf state j` by all_tac
    THEN1
      (simp [is_final_def,LET_THM]
      \\ imp_res_tac heap_lookup_LESS
      \\ fs [])
    \\ fs []
    \\ full_simp [GSYM APPEND_ASSOC]
    \\ imp_res_tac heap_lookup_AND_APPEND_IMP
    \\ fs [] \\ rpt var_eq_tac \\ fs []
    \\ ntac 2 (pop_assum kall_tac)
    \\ drule MEM_ADDR_MAP \\ strip_tac \\ var_eq_tac
    \\ res_tac \\ rfs []
    \\ rpt var_eq_tac \\ fs []
    \\ fs [heap_map1_def,FLOOKUP_DEF]
    \\ qpat_assum `!ii:num. _ ==> _` drule
    \\ strip_tac
    \\ res_tac
    \\ fs [isSomeDataElement_def])
  THEN1                           (* in Unused heap *)
    fs [MEM_heap_expand_FALSE]
  THEN1                           (* in r1 heap *)
    (`?j. heap_lookup j state.r1 =
          SOME (DataElement xs l d)` by all_tac
    THEN1 metis_tac [MEM_IMP_heap_lookup,MEM_APPEND]
    \\ `state.a + state.n = heap_length (state.h1 ++ heap_expand state.n)` by all_tac
    >- simp [heap_length_APPEND,heap_length_heap_expand]
    \\ `is_final conf state (state.a + state.n + j)` by all_tac
    >- simp [is_final_def,LET_THM,heap_length_def]
    \\ fs []
    \\ `?i. (FLOOKUP (heap_map 0 state.heap) i = SOME (state.a + state.n + j))` by all_tac
    >-
      (imp_res_tac heap_lookup_IMP_heap_addresses_GEN
      \\ pop_assum (qspecl_then [`state.a + state.n`] mp_tac)
      \\ simp []
      \\ strip_tac
      \\ fs [BIJ_DEF,SURJ_DEF,heap_map1_def,FLOOKUP_DEF])
    \\ res_tac
    \\ rfs []
    \\ cheat));
    (* \\ imp_res_tac heap_lookup_AND_PREPEND_IMP *)
    (* \\ fs [] \\ rpt var_eq_tac \\ fs [] *)
    (* \\ ntac 2 (pop_assum kall_tac) *)
    (* \\ pop_assum (qspec_then `[]` assume_tac) *)
    (* \\ disch_then (qspec_then `[]` assume_tac) *)
    (* \\ simp [] *)
    (* \\ strip_tac *)
    (* (* \\ *) *)
    (* \\ drule MEM_ADDR_MAP *)
    (* \\ strip_tac \\ var_eq_tac *)
    (* \\ res_tac *)
    (* \\ rfs [] *)
    (* \\ rpt var_eq_tac \\ fs [] *)
    (* \\ fs [heap_map1_def,FLOOKUP_DEF] *)
    (* \\ qpat_assum `!i':num. _ ==> _` drule *)
    (* \\ strip_tac *)
    (* \\ res_tac *)
    (* \\ fs [isSomeDataElement_def])); *)

val gc_related_def = Define `
  gc_related (f:num|->num) heap1 heap2 =
    INJ (FAPPLY f) (FDOM f) { a | isSomeDataElement (heap_lookup a heap2) } /\
    !i xs l d.
      i IN FDOM f /\ (heap_lookup i heap1 = SOME (DataElement xs l d)) ==>
      (heap_lookup (f ' i) heap2 = SOME (DataElement (ADDR_MAP (FAPPLY f) xs) l d)) /\
      !ptr u. MEM (Pointer ptr u) xs ==> ptr IN FDOM f`;

val IN_heap_addresses_LESS = prove(
  ``!heap n k. n IN heap_addresses k heap ==> k <= n /\ n < k + heap_length heap``,
  Induct
  \\ fs [heap_addresses_def,heap_length_def]
  \\ rpt strip_tac
  \\ rpt var_eq_tac
  \\ res_tac
  \\ qspec_then `h` assume_tac el_length_NOT_0
  \\ decide_tac);

val heap_lookup_EXTEND = store_thm("heap_lookup_EXTEND",
  ``!xs n ys x. (heap_lookup n xs = SOME x) ==>
                (heap_lookup n (xs ++ ys) = SOME x)``,
  Induct \\ full_simp_tac (srw_ss()) [heap_lookup_def] \\ SRW_TAC [] []);

val basic_gc_related = store_thm("basic_gc_related",
  ``!roots heap conf.
    roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) conf.limit ==>
    ?state f.
      (basic_gc conf (roots:'a heap_address list,heap) =
         (ADDR_MAP (FAPPLY f) roots,state)) /\
      (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM f) /\
      gc_related f heap (state.h1 ++ heap_expand state.n ++ state.r1)``,
  rpt strip_tac
  \\ mp_tac basic_gc_thm
  \\ fs []
  \\ rpt strip_tac \\ fs []
  (* \\ qexists_tac `state` *)
  \\ qexists_tac `heap_map 0 state.heap`
  \\ `(FAPPLY (heap_map 0 state.heap)) = heap_map1 state.heap` by all_tac
  THEN1
    fs [heap_map1_def,FUN_EQ_THM]
  \\ fs [gc_related_def,gc_inv_def,BIJ_DEF]
  \\ rpt strip_tac
  THEN1
    metis_tac []
  THEN1
    (fs [INJ_DEF]
    \\ rpt strip_tac
    \\ `(FLOOKUP (heap_map 0 state.heap) x = SOME (heap_map1 state.heap x))` by all_tac
    THEN1
      fs [FLOOKUP_DEF,heap_map1_def]
    \\ res_tac
    \\ fs []
    \\ imp_res_tac heap_lookup_LESS
    \\ drule heap_lookup_EXTEND \\ disch_then (qspec_then `[]` assume_tac)
    \\ fs []
    \\ fs [isSomeDataElement_def])
  THEN1
    (`(FLOOKUP (heap_map 0 state.heap) i = SOME (heap_map1 state.heap i))` by all_tac
    >- fs [FLOOKUP_DEF]
    \\ res_tac \\ fs []
    \\ `is_final conf state (heap_map1 state.heap i)` by all_tac
    >-
      (simp [is_final_def,LET_THM]
      \\ fs [INJ_DEF,SURJ_DEF]
      \\ res_tac
      \\ fs [] \\ rpt var_eq_tac \\ fs []
      \\ drule IN_heap_addresses_LESS
      \\ simp [heap_length_def])
    \\ fs [])
  \\ `(FLOOKUP (heap_map 0 state.heap) i = SOME (heap_map1 state.heap i))` by all_tac
  >- fs [FLOOKUP_DEF]
  \\ res_tac \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ `is_final conf state (heap_map1 state.heap i)` by all_tac
  THEN1
    (simp [is_final_def,LET_THM]
    \\ fs [INJ_DEF,SURJ_DEF]
    \\ res_tac \\ fs [] \\ rpt var_eq_tac \\ fs []
    \\ drule IN_heap_addresses_LESS \\ strip_tac
    \\ simp [heap_length_def])
  \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ qpat_assum `!ptr d. _ ==> _ ` (qspecl_then [`ptr`, `u`] assume_tac)
  \\ fs []);

val gc_forward_ptr_ok = store_thm("gc_forward_ptr_ok",
  ``!heap n a d c x. (gc_forward_ptr n heap a d c = (x,T)) ==> c``,
  Induct
  \\ simp_tac std_ss [Once gc_forward_ptr_def]
  \\ rpt strip_tac
  \\ Cases_on `n = 0`
  \\ full_simp_tac std_ss []
  \\ Cases_on `n < el_length h`
  \\ full_simp_tac std_ss []
  \\ Cases_on `gc_forward_ptr (n - el_length h) heap a d c`
  \\ full_simp_tac std_ss [LET_DEF]
  \\ Cases_on `r`
  \\ full_simp_tac std_ss []
  \\ res_tac);

val gc_move_ok = store_thm("gc_move_ok",
  ``(gc_move conf state x = (x',state')) /\ state'.ok ==>
    state.ok(*  /\ *)
    (* ((state.a = b + heap_length state.h2) ==> (state'.a = b + heap_length state'.h2)) /\ *)
    (* ((state.r = c + heap_length state.r4) ==> (state'.r = c + heap_length state'.r4)) *)``,
  Cases_on `x`
  \\ fs [gc_move_def]
  \\ Cases_on `heap_lookup n state.heap`
  \\ fs []
  \\ rpt strip_tac
  \\ fs [gc_state_component_equality]
  \\ Cases_on `x`
  \\ fs [gc_state_component_equality,LET_THM]
  \\ pairarg_tac
  \\ Cases_on `conf.isRef (DataElement l n' b)` \\ fs []
  \\ TRY pairarg_tac
  \\ fs [gc_state_component_equality]
  \\ rpt var_eq_tac
  \\ imp_res_tac gc_forward_ptr_ok);

val gc_move_list_ok = store_thm("gc_move_list_ok",
  ``!xs xs' state state'.
      (gc_move_list conf state xs = (xs',state')) /\ state'.ok ==>
      state.ok (* /\ *)
      (* ((state.a = b + heap_length state.h2) ==> (state'.a = b + heap_length state'.h2)) /\ *)
      (* ((state.r = c + heap_length state.r4) ==> (state'.r = c + heap_length state'.r4)) *)``,
  Induct
  \\ fs [gc_move_list_def]
  \\ rpt strip_tac
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ qpat_assum `!xs'. _` (qspecl_then [`xs''`, `state''`,`state'`] mp_tac)
  \\ strip_tac
  \\ res_tac
  \\ fs []
  \\ drule gc_move_ok \\ strip_tac \\ fs []);

val _ = export_theory();
