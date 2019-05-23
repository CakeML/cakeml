(*
  The minor collection of the generational copying garbage collector.
*)
open preamble wordsTheory wordsLib integer_wordTheory gc_sharedTheory gen_gcTheory;

val _ = new_theory "gen_gc_partial";

val _ = ParseExtras.temp_loose_equality();

val gc_state_component_equality = DB.fetch "gc_shared" "gc_state_component_equality";

val _ = Datatype `
  gen_gc_partial_conf =
    <| limit : num              (* size of heap *)
     ; isRef : 'a -> bool
     ; gen_start : num          (* start of generation *)
     ; refs_start : num         (* start of references *)
     |>`;

val gc_move_def = Define `
  (gc_move conf state (Data d) = (Data d, state)) /\
  (gc_move conf state (Pointer ptr d) =
     let ok = (state.ok /\ (ptr < heap_length state.heap)) in
     (if ptr < conf.gen_start \/ conf.refs_start <= ptr then
        (Pointer ptr d,state with <| ok := ok |>) else
      case heap_lookup ptr state.heap of
        | SOME (DataElement xs l dd) =>
          (let ok = ok /\ l+1 <= state.n /\ ~(conf.isRef dd) in
           let n = state.n - (l + 1) in
           let h2 = state.h2 ++ [DataElement xs l dd] in
           let (heap,ok) = gc_forward_ptr ptr state.heap state.a d ok in
           let a = state.a + l + 1 in
             (Pointer state.a d
             ,state with <| h2 := h2; n := n; a := a; heap := heap; ok := ok |>))
        | SOME (ForwardPointer ptr _ l) => (Pointer ptr d,state)
        | _ => (Pointer ptr d, state with <| ok := F |>)))`;

Theorem gc_move_IMP:
   !x x' state state1.
    (gc_move conf state x = (x',state1)) ==>
    (state1.old = state.old) /\
    (state1.h1 = state.h1) /\
    (state1.r4 = state.r4) /\
    (state1.r3 = state.r3) /\
    (state1.r2 = state.r2) /\
    (state1.r1 = state.r1)
Proof
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
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [gc_state_component_equality]
QED

val gc_move_list_def = Define `
  (gc_move_list conf state [] = ([], state)) /\
  (gc_move_list conf state (x::xs) =
    let (x,state) = gc_move conf state x in
    let (xs,state) = gc_move_list conf state xs in
      (x::xs,state))`;

Theorem gc_move_list_IMP:
   !xs xs' state state1.
    (gc_move_list conf state xs = (xs',state1)) ==>
    (LENGTH xs = LENGTH xs') /\
    (state1.old = state.old) /\
    (state1.h1 = state.h1) /\
    (state1.r4 = state.r4) /\
    (state1.r3 = state.r3) /\
    (state1.r2 = state.r2) /\
    (state1.r1 = state.r1)
Proof
  Induct
  \\ fs [gc_move_list_def,LET_THM]
  \\ ntac 5 strip_tac
  \\ pairarg_tac
  \\ Cases_on `xs'`
  \\ fs []
  \\ pairarg_tac \\ fs []
  \\ rpt var_eq_tac
  \\ drule gc_move_IMP
  \\ metis_tac []
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

Theorem gc_move_data_IMP:
   !conf state state1.
    (gc_move_data conf state = state1) ==>
    (state1.old = state.old) /\
    (state1.r1 = state.r1) /\
    (state1.r2 = state.r2) /\
    (state1.r3 = state.r3) /\
    (state1.r4 = state.r4)
Proof
  recInduct (fetch "-" "gc_move_data_ind")
  \\ rpt gen_tac
  \\ strip_tac
  \\ once_rewrite_tac [gc_move_data_def]
  \\ CASE_TAC
  \\ IF_CASES_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  \\ pairarg_tac \\ fs []
  \\ rfs []
  \\ drule gc_move_list_IMP
  \\ strip_tac \\ fs []
QED

val gc_move_ref_list_def = Define `
  (gc_move_ref_list conf state [] = ([], state)) /\
  (gc_move_ref_list conf state (DataElement ptrs l d::xs) =
    let (ptrs', state) = gc_move_list conf state ptrs in
    let (xs,state) = gc_move_ref_list conf state xs in
      (DataElement ptrs' l d::xs,state)) /\
  (gc_move_ref_list conf state (x::xs) = (x::xs,state with ok := F))`;

val gc_move_ref_list_IMP = prove (
  ``!conf state refs state1 refs1.
    (gc_move_ref_list conf state refs = (refs1,state1)) ==>
    (state1.old = state.old) /\
    (state1.r1 = state.r1) /\
    (state1.r2 = state.r2) /\
    (heap_length refs = heap_length refs1) /\
    (!ptr.
       isSomeDataElement (heap_lookup ptr refs) ==>
       isSomeDataElement (heap_lookup ptr refs1))
  ``,
  recInduct (theorem "gc_move_ref_list_ind")
  \\ once_rewrite_tac [gc_move_ref_list_def] \\ fs []
  \\ rpt gen_tac
  \\ strip_tac
  \\ rpt gen_tac
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ rveq
  \\ drule gc_move_list_IMP
  \\ strip_tac \\ rveq
  \\ fs []
  \\ fs [heap_length_def,el_length_def]
  \\ simp [heap_lookup_def]
  \\ strip_tac
  \\ IF_CASES_TAC \\ fs []
  >- simp [isSomeDataElement_def]
  \\ IF_CASES_TAC \\ fs [el_length_def]);

val partial_gc_def = Define `
  partial_gc conf (roots,heap) =
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
      let state = gc_move_data conf (state with <|r1 := refs';r2 := []|>) in
        (roots,state)`;

val partial_gc_IMP = prove(
  ``!roots heap roots1 state1 heap_old heap_current heap_refs.
    (partial_gc conf (roots,heap) = (roots1,state1)) /\
    (heap_segment (conf.gen_start,conf.refs_start) heap =
      SOME (heap_old,heap_current,heap_refs)) ==>
    (state1.old = heap_old) /\
    (heap_length state1.r1 = heap_length heap_refs) /\
    (LENGTH roots = LENGTH roots1) /\
    (!ptr.
       isSomeDataElement (heap_lookup ptr heap_refs) ==>
       isSomeDataElement (heap_lookup ptr state1.r1))``,
  rpt gen_tac
  \\ strip_tac
  \\ fs [partial_gc_def]
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ rveq \\ fs [SIMP_RULE std_ss [] gc_move_data_IMP]
  \\ strip_tac \\ fs []
  \\ rveq
  \\ drule gc_move_ref_list_IMP \\ strip_tac
  \\ drule gc_move_list_IMP
  \\ strip_tac \\ fs []);

(* Pointers between current and old generations are correct *)
val heap_gen_ok_def = Define `
  heap_gen_ok heap conf <=>
    ?old current refs.
      conf.gen_start <= conf.refs_start /\ conf.refs_start <= conf.limit /\
      EVERY isDataElement old /\
      EVERY isDataElement refs /\
      (SOME (old, current, refs) = heap_segment (conf.gen_start, conf.refs_start) heap) /\
      (* old points only to itself and references *)
      (!ptr xs l d u. MEM (DataElement xs l d) old /\ MEM (Pointer ptr u) xs ==>
        (ptr < conf.gen_start \/ conf.refs_start <= ptr)) /\
      (* old contains no references *)
      (!xs l d. MEM (DataElement xs l d) old ==> ~ (conf.isRef d)) /\
      (* old contains no references *)
      (!xs l d. MEM (DataElement xs l d) current ==> ~ (conf.isRef d)) /\
      (* refs only contains references *)
      (!xs l d. MEM (DataElement xs l d) refs ==> conf.isRef d)`;

val _ = Datatype `
  data_sort = Protected 'a      (* pointer to old generations *)
            | Real 'b`;         (* data or pointer to current generation *)

val to_gen_heap_address_def = Define `
  (to_gen_heap_address conf (Data a) = Data (Real a)) /\
  (to_gen_heap_address conf (Pointer ptr a) =
    if ptr < conf.gen_start then
      Data (Protected (Pointer ptr a))
    else if conf.refs_start <= ptr then
      Data (Protected (Pointer ptr a))
    else
      Pointer (ptr - conf.gen_start) (Real a))`;

val to_gen_conf_def = Define `
  to_gen_conf (conf:'a gen_gc_partial_conf) =
    <| limit := conf.limit - conf.gen_start - (conf.limit - conf.refs_start)
     ; isRef := conf.isRef |>
     : 'a gen_gc_conf`;

val to_gen_heap_element_def = Define `
  (to_gen_heap_element conf (Unused n) = Unused n) /\
  (to_gen_heap_element conf (ForwardPointer ptr a l) =
    ForwardPointer (ptr - conf.gen_start) (Real a) l) /\
  (to_gen_heap_element conf (DataElement ptrs l d) =
    DataElement (MAP (to_gen_heap_address conf) ptrs) l d)`;

val to_gen_heap_list_def = Define `
  to_gen_heap_list conf heap =
    MAP (to_gen_heap_element conf) heap`;

val to_gen_heap_list_heap_length = prove(
  ``!xs.
    heap_length (to_gen_heap_list conf xs) = heap_length xs``,
  Induct
  \\ fs [to_gen_heap_list_def]
  \\ Cases
  \\ fs [heap_length_def,to_gen_heap_element_def,el_length_def]);

val to_gen_heap_def = Define `
  to_gen_heap conf heap =
    to_gen_heap_list conf
        (heap_restrict conf.gen_start conf.refs_start heap)`;

val to_gen_state_def = Define `
  to_gen_state conf state =
    empty_state with
    <| h1 := to_gen_heap_list conf state.h1
     ; h2 := to_gen_heap_list conf state.h2
     ; r4 := []
     ; r3 := []
     ; r2 := []
     ; r1 := []
     ; a := state.a - conf.gen_start
     ; n := state.n
     ; ok := state.ok
     ; heap := to_gen_heap conf state.heap
     ; heap0 := to_gen_heap conf state.heap0
     |>`;

val to_gen_roots_def = Define `
  to_gen_roots conf roots =
    MAP (to_gen_heap_address conf) roots`;

val refs_to_roots_def = Define `
  (refs_to_roots conf [] = []) /\
  (refs_to_roots conf (DataElement ptrs _ _::refs) =
    MAP (to_gen_heap_address conf) ptrs ++ refs_to_roots conf refs) /\
  (refs_to_roots conf (_::refs) = refs_to_roots conf refs)`;

val (RootsRefs_def,RootsRefs_ind,RootsRefs_cases) = Hol_reln `
  (RootsRefs [] []) /\
  (!ptrs m b refs roots ptr a.
     RootsRefs (DataElement ptrs m b::refs) roots ==>
     RootsRefs (DataElement (Pointer ptr a::ptrs) m b::refs) (Pointer ptr a::roots)) /\
  (!ptrs m b refs roots a.
     RootsRefs (DataElement ptrs m b::refs) roots ==>
     RootsRefs (DataElement (Data a::ptrs) m b::refs) (Data a::roots)) /\
  (!refs roots m b.
     RootsRefs refs roots ==>
     RootsRefs (DataElement [] m b::refs) roots) /\
  (!refs roots n.
     RootsRefs refs roots ==>
     RootsRefs (Unused n::refs) roots) /\
  (!refs roots.
     RootsRefs refs roots ==>
     RootsRefs (ForwardPointer _ _ _::refs) roots)`;

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
  gen_inv (conf:'b gen_gc_partial_conf) heap =
    conf.gen_start <= conf.refs_start /\
    conf.refs_start <= conf.limit /\
    ?heap_old heap_current heap_refs.
      (heap_segment (conf.gen_start,conf.refs_start) heap =
        SOME (heap_old,heap_current,heap_refs)) /\
      EVERY (λe. ¬heap_element_is_ref conf e) heap_old /\
      EVERY (λe. ¬heap_element_is_ref conf e) heap_current /\
      EVERY isDataElement heap_refs /\
      (!n a d.
         MEM (ForwardPointer n a d) heap ==>
         conf.gen_start <= n /\ n < conf.refs_start) /\
      EVERY isDataElement heap_old /\
      !xs l d ptr u.
        MEM (DataElement xs l d) heap_old /\ MEM (Pointer ptr u) xs ==>
        ptr < conf.gen_start \/ conf.refs_start <= ptr`;

val has_old_ptr_def = Define `
  has_old_ptr conf hs ptr <=>
    ?xs l d u.
      MEM (DataElement xs l d) hs /\ MEM (Pointer ptr u) xs /\
      (ptr < conf.gen_start ∨ conf.refs_start ≤ ptr)`;

val has_old_ptr_APPEND = prove(
  ``!xs ys. has_old_ptr conf (xs++ys) =
            has_old_ptr conf xs UNION has_old_ptr conf ys``,
  fs[EXTENSION,IN_UNION] \\ fs [IN_DEF,has_old_ptr_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ metis_tac []);

val has_old_ptr_CONS =
  has_old_ptr_APPEND |> Q.SPEC `[x]` |> SIMP_RULE std_ss [APPEND]

val all_old_ptrs_def = Define `
  all_old_ptrs conf xs ptr <=>
    ?u. MEM (Pointer ptr u) xs /\
        (ptr < conf.gen_start ∨ conf.refs_start ≤ ptr)`

Theorem has_old_ptr_simp[simp]:
   has_old_ptr conf [DataElement xs x1 x2] = all_old_ptrs conf xs
Proof
  fs [has_old_ptr_def,FUN_EQ_THM,all_old_ptrs_def]
QED

val sim_inv_def = Define `
  sim_inv conf (heap0:('a,'b) heap_element list) (state:('a,'b)gc_state) <=>
    gen_inv conf state.heap /\
    conf.gen_start <= state.a /\
    state.a + state.n <= conf.refs_start /\
    (conf.gen_start + heap_length (state.h1 ++ state.h2) + state.n = conf.refs_start) /\
    (conf.refs_start <= conf.gen_start ==> (state.h1 = []) /\ (state.h2 = [])) /\
    has_old_ptr conf (state.heap ++ state.h1 ++ state.h2 ++ state.r1)
      SUBSET has_old_ptr conf heap0`;

Theorem heap_length_to_gen_heap_list[simp]:
   !h2. heap_length (to_gen_heap_list conf h2) = heap_length h2
Proof
  rewrite_tac [to_gen_heap_list_def]
  \\ Induct
  \\ fs [heap_length_def]
  \\ Cases
  \\ fs [to_gen_heap_element_def]
  \\ fs [el_length_def]
QED

Theorem el_length_not_zero[simp]:
   !x. el_length x <> 0
Proof
  Cases \\ EVAL_TAC \\ fs []
QED

Theorem heap_split_length:
   !h1 h2. heap_split (heap_length h1) (h1 ++ h2) = SOME (h1,h2)
Proof
  Induct
  THEN1 (fs [heap_length_def,heap_split_def]
         \\ Cases_on `h2` \\ fs [heap_split_def])
  \\ fs [heap_length_def] \\ fs [GSYM heap_length_def]
  \\ fs [heap_split_def]
QED

val heap_segment_length = prove(
  ``heap_segment (heap_length h1, heap_length h1 + heap_length h2)
      (h1 ++ h2 ++ h3) = SOME (h1,h2,h3)``,
  fs [heap_segment_def]
  \\ rewrite_tac [heap_split_length,GSYM APPEND_ASSOC]
  \\ fs [heap_split_length]);

val gc_move_simulation = prove(
  ``!ptr ptr' state state' ptr1' state1'.
      (gc_move conf state ptr = (ptr', state')) /\
      (!ptr' u. (ptr = Pointer ptr' u) ==>  ptr' < heap_length state.heap) /\
      (heap_length state.heap = conf.limit) /\
      sim_inv conf heap0 state /\
      (gen_gc$gc_move
         (to_gen_conf conf)
         (to_gen_state conf state)
         (to_gen_heap_address conf ptr) = (ptr1', state1')) /\ state1'.ok ==>
      sim_inv conf heap0 state' /\
      ((ptr1', state1')
       = (to_gen_heap_address conf ptr', to_gen_state conf state')) /\
      all_old_ptrs conf [ptr'] SUBSET all_old_ptrs conf [ptr]``,
  reverse Cases
  \\ fs [sim_inv_def]
  \\ rpt gen_tac
  \\ strip_tac
  \\ fs [to_gen_heap_address_def]
  >- (fs [gc_move_def,gen_gcTheory.gc_move_def]
     \\ rveq
     \\ fs [to_gen_heap_address_def]
     \\ metis_tac [])
  \\ fs []
  \\ Cases_on `n < conf.gen_start` \\ fs []
  >- (fs [gc_move_def,gen_gcTheory.gc_move_def]
     \\ rveq
     \\ `conf.gen_start <= conf.limit` by fs[gen_inv_def]
     \\ fs [to_gen_heap_address_def,to_gen_state_def]
     \\ metis_tac [])
  \\ Cases_on `conf.refs_start <= n` \\ fs []
  >- (fs [gc_move_def,gen_gcTheory.gc_move_def]
     \\ rveq
     \\ fs [to_gen_heap_address_def,IS_SOME_EXISTS]
     \\ fs[to_gen_state_def])
  \\ fs [gc_move_def,gen_gcTheory.gc_move_def]
  \\ `heap_lookup (n − conf.gen_start) (to_gen_state conf state).heap =
      case heap_lookup n state.heap of
      | NONE => NONE
      | SOME y => SOME (to_gen_heap_element conf y)` by
   (fs [gen_inv_def] \\ fs [heap_restrict_def]
    \\ drule heap_segment_IMP \\ fs []
    \\ disch_then (strip_assume_tac o GSYM)
    \\ fs [heap_length_APPEND]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ fs [heap_lookup_APPEND,to_gen_state_def,to_gen_heap_def]
    \\ fs [heap_restrict_def]
    \\ qmatch_goalsub_rename_tac `heap_lookup i (_ _ h1)`
    \\ qspec_tac (`i`,`i`)
    \\ qspec_tac (`h1`,`h1`)
    \\ Induct \\ fs [heap_lookup_def,to_gen_heap_list_def]
    \\ `!h:('a,'b) heap_element.
         el_length (to_gen_heap_element conf h) = el_length h` by
           (Cases \\ EVAL_TAC) \\ fs []
    \\ rw [] \\ fs [] \\ rfs [] \\ NO_TAC)
  \\ fs []
  \\ Cases_on `heap_lookup n state.heap` \\ fs []
  THEN1 (fs [] \\ rveq
         \\ fs [to_gen_heap_address_def,to_gen_state_def,gen_inv_def]
         \\ metis_tac [])
  \\ Cases_on `x` \\ fs [to_gen_heap_element_def]
  THEN1 (rveq \\ fs [to_gen_heap_address_def,to_gen_state_def,gen_inv_def]
         \\ metis_tac [])
  THEN1
   (rveq \\ fs [to_gen_heap_address_def,to_gen_state_def]
    \\ rfs [to_gen_heap_def,heap_restrict_def,gen_inv_def]
    \\ rfs [] \\ imp_res_tac heap_lookup_IMP_MEM
    \\ fs [to_gen_heap_list_def,MEM_MAP]
    \\ res_tac \\ fs []
    \\ fs [SUBSET_DEF,IN_DEF,all_old_ptrs_def])
  \\ fs [EVAL ``(to_gen_conf conf).isRef b``]
  \\ `~conf.isRef b` by
   (fs [gen_inv_def]
    \\ drule heap_segment_IMP \\ fs []
    \\ disch_then (strip_assume_tac o GSYM)
    \\ fs [heap_length_APPEND]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ fs [heap_lookup_APPEND,to_gen_state_def,to_gen_heap_def]
    \\ rfs []
    \\ drule heap_lookup_IMP_MEM
    \\ rw [] \\ fs [EVERY_MEM] \\ res_tac
    \\ fs [heap_element_is_ref_def] \\ NO_TAC)
  \\ fs [EVAL ``(to_gen_state conf state).ok``,
         EVAL ``(to_gen_state conf state).a``,
         EVAL ``(to_gen_state conf state).n``]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs [to_gen_heap_address_def]
  \\ simp [to_gen_state_def,empty_state_def,
       gc_sharedTheory.gc_state_component_equality]
  \\ fs [to_gen_heap_list_def,to_gen_heap_element_def]
  \\ fs [gen_inv_def]
  \\ drule heap_segment_IMP \\ fs []
  \\ disch_then (strip_assume_tac o GSYM) \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ full_simp_tac std_ss [heap_lookup_APPEND]
  \\ rfs [heap_length_APPEND,to_gen_state_def,to_gen_heap_def,heap_restrict_def]
  \\ fs [] \\ rfs []
  \\ drule heap_lookup_SPLIT
  \\ strip_tac \\ fs [] \\ rveq
  \\ `n = heap_length ha + heap_length heap_old` by fs []
  \\ fs [] \\ rveq
  \\ `gc_forward_ptr (heap_length (heap_old ++ ha))
         ((heap_old ++ ha) ++ DataElement l n' b::(hb ++ heap_refs))
         state.a a (state.ok ∧ n' + 1 ≤ state.n) = (heap',ok')` by
    (fs [heap_length_APPEND]
     \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND] \\ NO_TAC)
  \\ full_simp_tac std_ss [gc_forward_ptr_thm] \\ rveq
  \\ `gc_forward_ptr (heap_length (to_gen_heap_list conf ha))
         (to_gen_heap_list conf ha ++
          DataElement (MAP (to_gen_heap_address conf) l) n' b ::
          to_gen_heap_list conf hb)
         (state.a − heap_length heap_old) (Real a)
         (state.ok ∧ n' + 1 ≤ state.n) = (heap,T)` by
    (fs [heap_length_APPEND,heap_length_to_gen_heap_list]
     \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND,
          to_gen_heap_list_def,MAP_APPEND,MAP,to_gen_heap_element_def] \\ NO_TAC)
  \\ full_simp_tac std_ss [gc_forward_ptr_thm] \\ rveq
  \\ rpt (qpat_x_assum `_ = (_,T)` kall_tac)
  \\ qmatch_goalsub_abbrev_tac `heap_segment xx yy`
  \\ `heap_segment xx yy = SOME
       (heap_old,ha++ForwardPointer state.a a n'::hb,heap_refs)` by
   (unabbrev_all_tac
    \\ asm_rewrite_tac [GSYM heap_segment_length]
    \\ fs [heap_length_def,el_length_def,SUM_APPEND]
    \\ AP_TERM_TAC \\ fs [] \\ NO_TAC)
  \\ fs [] \\ fs [to_gen_heap_list_def,to_gen_heap_element_def]
  \\ simp [heap_element_is_ref_def]
  \\ reverse conj_tac THEN1
   (fs [all_old_ptrs_def,SUBSET_DEF,IN_DEF])
  \\ rewrite_tac [CONJ_ASSOC]
  \\ reverse conj_tac THEN1
   (unabbrev_all_tac \\ fs [has_old_ptr_def,SUBSET_DEF,IN_DEF]
    \\ metis_tac [])
  \\ reverse conj_tac THEN1
   (fs [heap_length_APPEND]
    \\ fs [heap_length_def,el_length_def])
  \\ reverse conj_tac THEN1 metis_tac []
  \\ unabbrev_all_tac
  \\ fs [heap_length_APPEND]
  \\ fs [heap_length_def,el_length_def]
  \\ fs [GSYM heap_length_def]
  \\ rw [] \\ fs [] \\ metis_tac []);

Theorem gc_forward_ptr_heap_length:
    !n h m a ok h' ok'. (gc_forward_ptr n h m a ok = (h',ok')) ==> (heap_length h = heap_length h')
Proof
  Induct_on `h`
  >> rpt strip_tac
  >> qpat_x_assum `gc_forward_ptr _ _ _ _ _ = _` (assume_tac o GSYM)
  >> fs[gc_forward_ptr_def,heap_length_def]
  >> every_case_tac
  >> fs[el_length_def]
  >> Cases_on `gc_forward_ptr (n − el_length h') h m a ok`
  >> fs[] >> metis_tac[]
QED

Theorem gc_move_heap_length:
   (gc_move conf state h = (x,state')) ==> (heap_length state.heap = heap_length state'.heap)
Proof
  Cases_on `h`
  >> rpt strip_tac
  >> first_x_assum (assume_tac o GSYM)
  >> fs[gc_move_def]
  >> every_case_tac
  >> fs[pairTheory.ELIM_UNCURRY]
  >> rfs[]
  >> metis_tac[pair_CASES,gc_forward_ptr_heap_length,FST]
QED

Theorem gc_move_list_heap_length:
   !h x state state'. (gc_move_list conf state h = (x,state')) ==> (heap_length state.heap = heap_length state'.heap)
Proof
  Induct_on `h`
  >> rpt strip_tac
  >> first_x_assum (assume_tac o GSYM)
  >> fs[gc_move_list_def]
  >> ntac 2 (pairarg_tac >> fs[])
  >> metis_tac[gc_move_heap_length]
QED

Theorem gc_move_ref_list_heap_length:
   !h x state state'.
   (gc_move_ref_list conf state h = (x,state'))
    ==> (heap_length state.heap = heap_length state'.heap)
Proof
  Induct >- fs[gc_move_ref_list_def] >> Cases
  >> rpt strip_tac
  >> first_x_assum (assume_tac o GSYM)
  >> fs[gc_move_ref_list_def]
  >> ntac 2 (pairarg_tac >> fs[])
  >> metis_tac[gc_move_list_heap_length]
QED

Theorem gc_move_ok':
   (gc_move conf state x = (x',state')) /\ state'.ok ==> state.ok
Proof
  Cases_on `x`
  \\ fs [gc_move_def]
  \\ every_case_tac \\ fs []
  \\ strip_tac \\ fs [] \\ rveq \\ fs []
  \\ pairarg_tac \\ fs []
  \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ imp_res_tac gc_forward_ptr_ok
QED

Theorem gc_move_ok:
   (gc_move conf state x = (x',state')) /\ state'.ok /\ (!ptr' u. (x = Pointer ptr' u) ==>  ptr' < heap_length state.heap) ==> state.ok
Proof
  rw [] \\ imp_res_tac gc_move_ok'
QED

Theorem gc_move_list_ok':
    !xs xs' state state'.
     (gc_move_list conf state xs = (xs',state')) /\ state'.ok ==>
       state.ok
Proof
  Induct \\ fs [gc_move_list_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ res_tac \\ imp_res_tac gc_move_ok'
QED

Theorem gc_move_list_ok:
    !xs xs' state state'.
     (gc_move_list conf state xs = (xs',state')) /\ state'.ok
       /\ (∀ptr' u. MEM (Pointer ptr' u) xs ⇒ ptr' < heap_length state.heap)
      ==>
       state.ok
Proof
  rw [] \\ imp_res_tac gc_move_list_ok'
QED

Theorem gc_move_ref_list_ok':
    !xs xs' state state'.
     (gc_move_ref_list conf state xs = (xs',state')) /\ state'.ok ==>
       state.ok
Proof
  Induct \\ fs [gc_move_ref_list_def]
  \\ Cases \\ fs [gc_move_ref_list_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ res_tac \\ imp_res_tac gc_move_list_ok'
QED

Theorem gc_move_data_ok':
   !conf state state'.
     (gc_move_data conf state = state') /\ state'.ok ==>
       state.ok
Proof
  recInduct (fetch "-" "gc_move_data_ind")
  \\ rpt gen_tac \\ strip_tac
  \\ once_rewrite_tac [gc_move_data_def]
  \\ gen_tac \\ TOP_CASE_TAC \\ IF_CASES_TAC
  THEN1 (rpt (pop_assum kall_tac) \\ strip_tac \\ rveq \\ fs [])
  \\ CASE_TAC \\ TRY (rpt (pop_assum kall_tac) \\ strip_tac
                      \\ rveq \\ fs [] \\ NO_TAC)
  \\ simp_tac (srw_ss()) [LET_THM]
  \\ pairarg_tac \\ asm_rewrite_tac []
  \\ simp_tac (srw_ss()) [] \\ CCONTR_TAC
  \\ qpat_x_assum `!x._` mp_tac \\ fs []
  \\ CCONTR_TAC \\ fs []
  \\ imp_res_tac gc_move_list_ok' \\ fs []
QED

val gc_move_list_simulation = prove(
  ``!ptr ptr' state state' ptr1' state1'.
      (gc_move_list conf state ptr = (ptr', state')) /\
      sim_inv conf heap0 state /\
      (∀ptr' u. MEM (Pointer ptr' u) ptr ⇒ ptr' < heap_length state.heap) ∧
      (heap_length state.heap = conf.limit) /\
      (gen_gc$gc_move_list
         (to_gen_conf conf)
         (to_gen_state conf state)
         (MAP (to_gen_heap_address conf) ptr) = (ptr1', state1')) /\ state1'.ok ==>
      sim_inv conf heap0 state' /\
      ((ptr1', state1')
       = (MAP (to_gen_heap_address conf) ptr', to_gen_state conf state')) /\
      all_old_ptrs conf ptr' SUBSET all_old_ptrs conf ptr``,
  Induct
  \\ fs [gc_move_list_def,gen_gcTheory.gc_move_list_def]
  \\ rpt gen_tac \\ rpt (disch_then assume_tac)
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ fs []
  \\ imp_res_tac gen_gcTheory.gc_move_list_ok
  \\ drule gc_move_simulation \\ fs []
  \\ strip_tac \\ fs [] \\ rveq
  \\ first_x_assum drule
  \\ fs [] \\ strip_tac
  \\ fs [SUBSET_DEF,IN_DEF,all_old_ptrs_def]
  \\ `heap_length state''.heap = conf.limit`
       by(drule gc_move_heap_length >> fs[])
  \\ fs[]
  \\ `(∀ptr' u. set ptr (Pointer ptr' u) ⇒ ptr' < conf.limit)` by metis_tac[]
  \\ first_x_assum drule
  \\ metis_tac []);

val gc_move_list_APPEND = prove(
  ``!conf state0 xs ys roots' state'.
      (gen_gc$gc_move_list conf state0 (xs ++ ys) = (roots',state')) ==>
      ?roots1 roots2 state1.
        (gen_gc$gc_move_list conf state0 xs = (roots1,state1)) /\
        (gen_gc$gc_move_list conf state1 ys = (roots2,state')) /\
        (roots' = roots1 ++ roots2)``,
  Induct_on `xs` \\ fs [gen_gcTheory.gc_move_list_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ res_tac \\ fs [] \\ rveq \\ fs []);

Theorem heap_restrict_NIL[simp]:
   heap_restrict gen_start refs_start [] = []
Proof
  rewrite_tac [heap_restrict_def]
  \\ fs [heap_segment_def]
  \\ fs [heap_split_def]
  \\ every_case_tac \\ fs []
  \\ fs [heap_split_def] \\ rveq \\ fs []
QED

Theorem to_gen_heap_NIL[simp]:
   to_gen_heap conf [] = []
Proof
  rewrite_tac [to_gen_heap_def]
  \\ fs [heap_restrict_def,to_gen_heap_list_def]
QED

Theorem to_gen_heap_list_NIL[simp]:
   to_gen_heap_list conf [] = []
Proof
  rewrite_tac [to_gen_heap_list_def]
  \\ fs []
QED

val gc_move_data_r1 = prove(
  ``!refs state conf.
      (gc_move_data conf (state with r1 := refs)).r1 = refs``,
  rpt gen_tac
  \\ qmatch_goalsub_abbrev_tac `moved.r1 = _`
  \\ fs [markerTheory.Abbrev_def]
  \\ pop_assum (assume_tac o GSYM)
  \\ fs []
  \\ drule gc_move_data_IMP
  \\ strip_tac
  \\ fs []);

val gc_move_ref_list_simulation = prove(
  ``!conf state refs0 heap0 state1 state1' refs1 refs1'.
    (gc_move_ref_list conf (state : ('b,'a) gc_state) (refs0 : ('b,'a) heap_element list)
      = (refs1,state1)) /\
    (gc_move_list (to_gen_conf conf)
                  (to_gen_state conf state)
                  (refs_to_roots conf refs0)
      = (refs1',state1')) /\ state1'.ok /\
    sim_inv conf heap0 state /\
    (∀ptrs l d ptr' u. MEM (Pointer ptr' u) ptrs /\ MEM (DataElement ptrs l d) refs0 ⇒ ptr' < heap_length state.heap) ∧
    (heap_length state.heap = conf.limit) /\
    EVERY isDataElement refs0
    ==>
    sim_inv conf heap0 state1 /\
    (refs1' = refs_to_roots conf refs1) /\
    (state1' = to_gen_state conf state1) /\
    has_old_ptr conf refs1 SUBSET has_old_ptr conf refs0``,
  recInduct (theorem "gc_move_ref_list_ind")
  \\ strip_tac
  >- (rpt gen_tac
     \\ once_rewrite_tac [gc_move_ref_list_def]
     \\ simp [refs_to_roots_def]
     \\ once_rewrite_tac [gen_gcTheory.gc_move_list_def]
     \\ strip_tac \\ rveq
     \\ simp [refs_to_roots_def]
     \\ fs [])
  \\ reverse strip_tac
  >- fs [EVERY_DEF,isDataElement_def]
  \\ rpt gen_tac
  \\ strip_tac
  \\ rpt gen_tac
  \\ once_rewrite_tac [gc_move_ref_list_def]
  \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ strip_tac \\ rveq
  \\ drule gc_move_list_simulation
  \\ asm_rewrite_tac []
  \\ strip_tac
  \\ qpat_x_assum `_ = (refs1',state1')` mp_tac
  \\ asm_rewrite_tac [refs_to_roots_def]
  \\ strip_tac
  \\ drule gc_move_list_APPEND
  \\ strip_tac
  \\ rveq
  \\ imp_res_tac gen_gcTheory.gc_move_list_ok
  \\ asm_rewrite_tac []
  \\ drule gc_move_list_heap_length \\ DISCH_TAC
  \\ `(∀ptr' u. MEM (Pointer ptr' u) ptrs ⇒ ptr' < conf.limit)` by metis_tac[]
  \\ first_x_assum drule
  \\ DISCH_TAC
  \\ first_x_assum drule
  \\ asm_rewrite_tac []
  \\ simp_tac std_ss []
  \\ strip_tac \\ rveq
  \\ simp_tac std_ss [APPEND_11]
  \\ fs [] \\ first_x_assum drule
  \\ fs [has_old_ptr_CONS]
  \\ fs [has_old_ptr_def,all_old_ptrs_def,SUBSET_DEF,IN_DEF]
  \\ metis_tac []);

val gc_move_list_r1 = prove(
  ``!s0 xs ys s1. (gc_move_list conf s0 xs = (ys,s1)) ==> (s1.r1 = s0.r1)``,
  Induct_on `xs` \\ fs [gc_move_list_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ fs []
  \\ res_tac \\ fs [] \\ rveq
  \\ Cases_on `h` \\ fs [gc_move_def]
  \\ every_case_tac \\ fs [] \\ rveq \\ fs []
  \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ fs []
  \\ rveq \\ fs []);

val gc_move_data_r1 = prove(
  ``(gc_move_data conf (state' with r1 := refs') = state1) ==>
    (state1.r1 = refs')``,
  qabbrev_tac `s0 = state' with r1 := refs'`
  \\ `s0.r1 = refs'` by fs [Abbr `s0`]
  \\ rveq \\ pop_assum kall_tac
  \\ qspec_tac (`state1`,`s1`)
  \\ qspec_tac (`s0`,`s0`)
  \\ qspec_tac (`conf`,`conf`)
  \\ ho_match_mp_tac (fetch "-" "gc_move_data_ind")
  \\ rw [] \\ once_rewrite_tac [gc_move_data_def]
  \\ rpt (CASE_TAC \\ fs [])
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ pairarg_tac \\ fs []
  \\ drule gc_move_list_r1 \\ fs []);

val el_length_to_gen_heap_element = prove(
  ``!h. el_length (to_gen_heap_element conf h) = el_length h``,
  Cases \\ EVAL_TAC);

val to_gen_heap_address_11 = prove(
  ``!x y.
      (to_gen_heap_address conf x = to_gen_heap_address conf y) ==> (x = y)``,
  Cases \\ Cases_on `y` \\ fs [to_gen_heap_address_def]
  \\ rw [] \\ fs []);

val MAP_to_gen_heap_address_11 = prove(
  ``!x y.
      (MAP (to_gen_heap_address conf) x = MAP (to_gen_heap_address conf) y)
      <=> (x = y)``,
  Induct \\ Cases_on `y` \\ fs []
  \\ rw [] \\ fs [] \\ metis_tac [to_gen_heap_address_11]);

val gc_forward_ptr_data_pres = Q.prove(
   `!x a ptr d ok x' ok'.
   (gc_forward_ptr a x ptr d ok = (x',ok'))
   ==> (MEM (DataElement xs l dd) x
        = (MEM (DataElement xs l dd) x' \/ (heap_lookup a x = SOME(DataElement xs l dd))))`,
  Induct
  >> rw[gc_forward_ptr_def] >> rpt strip_tac
  >> fs[heap_lookup_def]
  >- metis_tac[]
  >> pairarg_tac
  >> fs[]
  >> qpat_x_assum `_::_ = _` (assume_tac o GSYM)
  >> fs[] >> metis_tac[]);

val gc_move_data_pres = Q.prove(
  `(gc_move conf state x = (x1,state1))
   ==> (MEM (DataElement xs l dd) (state1.heap++state1.h2)
        = MEM (DataElement xs l dd) (state.heap++state.h2))`,
  Cases_on `x` >> rw[gc_move_def] >> rpt strip_tac
  >> fs[] >> every_case_tac >> fs[] >> TRY(pairarg_tac >> fs[]) >>
  qpat_x_assum `_ = (y:('a,'b) gc_state)` (assume_tac o GSYM) >> fs[]
  >> drule gc_forward_ptr_data_pres >> strip_tac >> fs[] >> metis_tac[]);

val gc_move_list_data_pres = Q.prove(
  `!x conf state x1 state1 xs l dd.
   (gc_move_list conf state x = (x1,state1))
   ==> (MEM (DataElement xs l dd) (state1.heap++state1.h2)
        = MEM (DataElement xs l dd) (state.heap++state.h2))`,
  Induct_on `x` >> rw[gc_move_list_def] >> fs[]
  >> pairarg_tac >> fs[] >> pairarg_tac >> fs[]
  >> qpat_x_assum `_ = (y:('a,'b) gc_state)` (assume_tac o GSYM)
  >> fs[] >> drule gc_move_data_pres >> strip_tac >> fs[]
  >> metis_tac[]);

val gc_move_ref_list_data_pres = Q.prove(
  `!x conf state x1 state1 xs l dd.
   (gc_move_ref_list conf state x = (x1,state1))
   ==> (MEM (DataElement xs l dd) (state1.heap++state1.h2)
        = MEM (DataElement xs l dd) (state.heap++state.h2))`,
  Induct_on `x` >> rw[gc_move_ref_list_def] >> fs[]
  >> Induct_on `h` >> rw[gc_move_ref_list_def] >> rpt strip_tac
  >> fs[]
  >> pairarg_tac >> fs[] >> pairarg_tac >> fs[]
  >> fs[] >> drule gc_move_list_data_pres >> strip_tac >> fs[]
  >> metis_tac[]);

val gc_move_data_simulation = prove(
  ``!conf state heap0 state' ptr1' state1'.
      (gc_move_data conf state = state') /\
      sim_inv conf heap0 state /\
      (∀ptrs l d ptr' u. MEM (Pointer ptr' u) ptrs /\ MEM (DataElement ptrs l d) (state.h2++state.heap) ⇒ ptr' < heap_length state.heap) /\
      (heap_length state.heap = conf.limit) /\
      (gen_gc$gc_move_data
         (to_gen_conf conf)
         (to_gen_state conf state) = state1') /\ state1'.ok ==>
      sim_inv conf heap0 state' /\
      (state1' = to_gen_state conf state')``,
  recInduct (fetch "-" "gc_move_data_ind")
  \\ rpt gen_tac \\ rpt (disch_then assume_tac) \\ rpt gen_tac
  \\ once_rewrite_tac [gc_move_data_def,gen_gcTheory.gc_move_data_def]
  \\ TOP_CASE_TAC \\ fs []
  THEN1
   (fs [EVAL ``(to_gen_state conf state).h2``]
    \\ strip_tac \\ rveq \\ fs [])
  \\ fs [EVAL ``(to_gen_state conf state).h2``]
  \\ qpat_abbrev_tac `xx = (to_gen_conf conf).limit < _`
  \\ Cases_on `xx` \\ fs []
  THEN1 (rw [] \\ fs [])
  \\ unabbrev_all_tac
  \\ IF_CASES_TAC THEN1
   (fs [to_gen_conf_def,heap_length_APPEND]
    \\ fs [heap_length_def,el_length_def]
    \\ fs [to_gen_conf_def,GSYM heap_length_def]
    \\ fs [GSYM to_gen_heap_list_def,heap_length_to_gen_heap_list,
           to_gen_state_def,el_length_to_gen_heap_element])
  \\ Cases_on `h` \\ fs [to_gen_heap_element_def]
  THEN1 (rw [] \\ fs [])
  THEN1 (rw [] \\ fs [])
  \\ rpt (pairarg_tac \\ fs [])
  \\ strip_tac \\ rveq
  \\ imp_res_tac gc_move_data_ok \\ fs []
  \\ drule gc_move_list_simulation
  \\ fs [] \\ strip_tac \\ rveq
  \\ `(∀ptr' u. MEM (Pointer ptr' u) l ⇒ ptr' < conf.limit)` by metis_tac[]
  \\ first_x_assum drule \\ DISCH_TAC \\ fs[] \\ rveq
  \\ rename1 `(to_gen_state conf state3).h2`
  \\ Cases_on `state3.h2`
  THEN1 fs [to_gen_state_def]
  \\ fs [EVAL ``(to_gen_state conf state3).h2``]
  \\ Cases_on `h` \\ fs [to_gen_heap_element_def] \\ rveq
  \\ fs [MAP_to_gen_heap_address_11] \\ rveq
  \\ first_x_assum (qspec_then `heap0` mp_tac)
  \\ impl_tac THEN1
   (qpat_x_assum `(gc_move_data (to_gen_conf conf) _).ok` mp_tac
    \\ fs [to_gen_state_def,gc_state_component_equality]
    \\ simp [to_gen_heap_list_def,to_gen_heap_element_def]
    \\ strip_tac \\ fs [sim_inv_def,has_old_ptr_def]
    \\ fs [heap_length_APPEND]
    \\ drule gc_move_list_heap_length \\ DISCH_TAC
    \\ fs [heap_length_def,el_length_def]
    \\ fs [has_old_ptr_APPEND,has_old_ptr_CONS]
    \\ imp_res_tac SUBSET_TRANS \\ fs []
    \\ drule gc_move_list_data_pres \\ strip_tac \\ fs[] \\ rfs[] \\ metis_tac[])
  \\ fs [] \\ once_rewrite_tac [EQ_SYM_EQ] \\ fs []
  \\ rw [] \\ AP_TERM_TAC
  \\ fs [to_gen_state_def,gc_state_component_equality]
  \\ simp [to_gen_heap_list_def,to_gen_heap_element_def]);

val gc_move_with_refs = prove(
  ``!l. (gc_move conf (state with r1 := refs) l =
         let (xs,s) = gc_move conf state l in (xs,s with r1 := refs))
``,
  Cases
  \\ fs [gc_move_def]
  \\ rpt (fs [] \\ TOP_CASE_TAC)
  \\ ntac 2 (pairarg_tac \\ fs []));

val gc_move_with_refs' = prove(
  ``!l. (gc_move conf (state with <|r2 := []; r1 := refs |>) l =
         let (xs,s) = gc_move conf state l in (xs,s with <|r2 := []; r1 := refs |>))
``,
  Cases
  \\ fs [gc_move_def]
  \\ rpt (fs [] \\ TOP_CASE_TAC)
  \\ ntac 2 (pairarg_tac \\ fs []));

val gc_move_list_with_refs = prove(
  ``!l state.
      (gc_move_list conf (state with r1 := refs) l =
      let (xs,s) = gc_move_list conf state l in (xs,s with r1 := refs))``,
  Induct \\ fs [gc_move_list_def,gc_move_with_refs]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ fs [] \\ rveq
  \\ rfs [] \\ fs []);

val gc_move_list_with_refs' = prove(
  ``!l state.
      (gc_move_list conf (state with <|r2 := [] ; r1 := refs |>) l =
       let (xs,s) = gc_move_list conf state l in (xs,s with <|r2 := []; r1 := refs|>))``,
  Induct \\ fs [gc_move_list_def,gc_move_with_refs']
  \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ fs [] \\ rveq
  \\ rfs [] \\ fs []);

val gc_move_data_with_refs = prove(
  ``!conf state refs.
      (gc_move_data conf (state with r1 := refs) =
      (gc_move_data conf state) with r1 := refs)
   ``,
  recInduct (fetch "-" "gc_move_data_ind") \\ rw []
  \\ once_rewrite_tac [gc_move_data_def]
  \\ rpt (fs [] \\ TOP_CASE_TAC)
  \\ fs [gc_move_list_with_refs]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ ntac 2 (pairarg_tac \\ fs []));

val gc_move_data_with_refs' = prove(
  ``!conf state refs.
     (gc_move_data conf (state with <|r2 := []; r1 := refs|>) =
     (gc_move_data conf state) with <|r2 := []; r1 := refs|>)
   ``,
  recInduct (fetch "-" "gc_move_data_ind") \\ rw []
  \\ once_rewrite_tac [gc_move_data_def]
  \\ rpt (fs [] \\ TOP_CASE_TAC)
  \\ fs [gc_move_list_with_refs']
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ ntac 2 (pairarg_tac \\ fs []));

val gc_move_data_h2 = prove(
  ``!conf state.
      (gc_move_data conf state).ok ==>
      ((gc_move_data conf state).h2 = [])``,
  ho_match_mp_tac (fetch "-" "gc_move_data_ind")
  \\ rpt gen_tac \\ strip_tac
  \\ once_rewrite_tac [gc_move_data_def]
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []);

val gc_move_ref_list_heap_length = Q.prove(
  `!h x state state'. (gc_move_ref_list conf state h = (x,state')) ==> (heap_length state.heap = heap_length state'.heap)`,
  Induct_on `h`
  >> rpt strip_tac
  >> first_x_assum (assume_tac o GSYM)
  >> fs[gc_move_ref_list_def]
  >> Cases_on `h'`
  >> fs[gc_move_ref_list_def]
  >> pairarg_tac >> fs[]
  >> pairarg_tac >> fs[]
  >> metis_tac[gc_move_list_heap_length]);

val gc_move_data_r1 = Q.prove(`(gc_move_data conf state).r1 = state.r1`,
  metis_tac[gc_move_data_IMP]);

val partial_gc_simulation = prove(
  ``!conf roots heap0 roots1 state1 heap0_old heap0_current heap0_refs
     new_roots new_state.
      (partial_gc conf (roots,heap0) = (roots1,state1)) /\
      heap_gen_ok heap0 conf /\
      conf.gen_start ≤ conf.refs_start ∧ conf.refs_start ≤ conf.limit /\
      (heap_segment (conf.gen_start,conf.refs_start) heap0
        = SOME (heap0_old,heap0_current,heap0_refs)) /\
      EVERY (\e. ~(heap_element_is_ref conf e)) (heap0_old ++ heap0_current) /\
      EVERY isDataElement heap0_refs /\
      roots_ok roots heap0 /\
      (gen_gc (to_gen_conf conf)
        (to_gen_roots conf roots ++ refs_to_roots conf heap0_refs,
         to_gen_heap_list conf heap0_current) = (new_roots,new_state)) /\
      heap_ok heap0 conf.limit /\ new_state.ok ==>
      (new_roots = to_gen_roots conf roots1 ++ refs_to_roots conf state1.r1) /\
      (new_state = to_gen_state conf state1) /\
      sim_inv conf heap0 state1 /\ (state1.h2 = []) /\ state1.ok``,
  rpt gen_tac
  \\ rpt (disch_then assume_tac)
  \\ fs [gen_gc_def]
  \\ pairarg_tac \\ fs []
  \\ fs [partial_gc_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ drule gc_move_list_APPEND
  \\ strip_tac \\ fs []
  \\ rveq
  \\ drule (GEN_ALL gc_move_list_simulation)
  \\ disch_then (qspec_then `heap0` mp_tac)
  \\ qpat_abbrev_tac `xx = sim_inv _ _ _`
  \\ `xx` by
   (unabbrev_all_tac \\ fs [sim_inv_def,empty_state_def,gen_inv_def]
    \\ fs [heap_gen_ok_def]
    \\ drule heap_segment_IMP \\ fs []
    \\ strip_tac \\ rveq \\ fs [heap_length_APPEND]
    \\ reverse conj_tac THEN1 metis_tac []
    \\ fs [heap_ok_def,FILTER_EQ_NIL,EVERY_MEM]
    \\ rw [] \\ res_tac \\ fs [isForwardPointer_def] \\ NO_TAC)
  \\ asm_rewrite_tac [] \\ qunabbrev_tac `xx`
  \\ qmatch_asmsub_abbrev_tac `gen_gc_partial$gc_move_list _ stateA`
  \\ qmatch_asmsub_abbrev_tac `gen_gc$gc_move_list _ stateB _ = (roots1,state1)`
  \\ `stateB = to_gen_state conf stateA` by (unabbrev_all_tac
     \\ simp [to_gen_state_def,empty_state_def]
     \\ simp [to_gen_conf_def,to_gen_heap_def]
     \\ simp [heap_restrict_def]
     \\ drule heap_segment_IMP
     \\ simp [heap_length_APPEND])
  \\ fs [to_gen_roots_def]
  \\ impl_tac THEN1
  ( rpt strip_tac
    >- (fs[roots_ok_def] >> first_x_assum drule >> DISCH_TAC
        >> fs[isSomeDataElement_def]
        >> drule heap_lookup_LESS >> DISCH_TAC
        >> qunabbrev_tac `stateA` >> fs[])
    >- (qunabbrev_tac `stateA` >> fs[heap_ok_def])
    >> imp_res_tac gc_move_loop_ok \\ fs []
    \\ imp_res_tac gen_gcTheory.gc_move_list_ok \\ fs [])
  \\ strip_tac \\ rveq \\ fs [APPEND_11]
  \\ drule gc_move_ref_list_simulation
  \\ disch_then (qspec_then `heap0` mp_tac)
  \\ fs [] \\ impl_tac
  THEN1 (imp_res_tac gen_gcTheory.gc_move_loop_ok \\ fs []
         >> fs[heap_ok_def] >> drule gc_move_list_heap_length >> DISCH_THEN(assume_tac o GSYM)
         >> qunabbrev_tac `stateA` >> fs[heap_ok_def]
         >> rpt strip_tac >> drule heap_segment_IMP >> DISCH_THEN(assume_tac o GSYM)
         >> rfs[] >> `MEM (DataElement ptrs l d) heap0` by fs[]
         >> first_x_assum drule >> DISCH_TAC >> first_x_assum drule >> DISCH_TAC
         >> fs [isSomeDataElement_def] >> drule heap_lookup_LESS >> fs[])
  \\ strip_tac \\ rveq
  \\ fs [SIMP_RULE std_ss [] (GEN_ALL gc_move_data_r1)]
  \\ once_rewrite_tac [gc_move_loop_def]
  \\ fs [EVAL ``(to_gen_state conf state'').r4``]
  \\ fs [EVAL ``(to_gen_state conf state'').h2``]
  \\ fs [EVAL ``(to_gen_conf conf).limit``]
  \\ `has_old_ptr conf refs' SUBSET has_old_ptr conf heap0` by
   (match_mp_tac SUBSET_TRANS \\ asm_exists_tac \\ fs []
    \\ simp [SUBSET_DEF,IN_DEF]
    \\ simp [has_old_ptr_def]
    \\ drule heap_segment_IMP \\ fs []
    \\ strip_tac \\ rveq \\ fs [] \\ metis_tac [])
  \\ Cases_on `state''.h2` \\ fs []
  THEN1
   (once_rewrite_tac [gc_move_data_def] \\ fs []
    \\ simp [to_gen_state_def]
    \\ fs [sim_inv_def,has_old_ptr_APPEND]
    \\ imp_res_tac gc_move_loop_ok
    \\ fs [to_gen_state_def])
  \\ IF_CASES_TAC THEN1 fs [sim_inv_def]
  \\ qpat_x_assum `(gc_move_loop _ _ _).ok` mp_tac
  \\ simp [Once gc_move_loop_def]
  \\ fs [EVAL ``(to_gen_state conf state'').r4``]
  \\ fs [EVAL ``(to_gen_state conf state'').h2``]
  \\ strip_tac \\ drule gen_gcTheory.gc_move_loop_ok
  \\ qpat_abbrev_tac `s5 = gen_gc$gc_move_data _ _`
  \\ strip_tac
  \\ `s5.h2 = []` by metis_tac [gen_gcTheory.gc_move_data_h2]
  \\ drule (gc_move_data_simulation
            |> SIMP_RULE std_ss [] |> GEN_ALL)
  \\ fs [] \\ strip_tac \\ rveq
  \\ `sim_inv conf heap0 (gc_move_data conf state'') ∧
   (s5 = to_gen_state conf (gc_move_data conf state''))`
     by(first_x_assum MATCH_MP_TAC
        \\ drule gc_move_list_heap_length \\ DISCH_THEN (assume_tac o GSYM)
        \\ drule gc_move_ref_list_heap_length \\ DISCH_THEN (assume_tac o GSYM)
        \\ `heap_length heap0 = conf.limit` by fs[heap_ok_def]
        \\ qunabbrev_tac `stateA` \\ fs[]
        \\ rpt strip_tac
        \\ drule gc_move_list_data_pres \\ disch_then(qspecl_then [`ptrs`,`l`,`d`] assume_tac)
        \\ drule gc_move_ref_list_data_pres \\ disch_then(qspecl_then [`ptrs`,`l`,`d`] assume_tac)
        \\ fs[empty_state_def]
        \\ `MEM (DataElement ptrs l d) heap0` by rfs[]
        \\ `isSomeDataElement (heap_lookup ptr' heap0)` by metis_tac[heap_ok_def]
        \\ metis_tac[isSomeDataElement_def,heap_lookup_LESS])
  \\ once_rewrite_tac [gc_move_loop_def]
  \\ fs [EVAL ``(to_gen_state conf state'').r4``,gc_move_data_with_refs']
  \\ simp [to_gen_state_def]
  \\ fs [sim_inv_def]
  \\ fs [has_old_ptr_APPEND,gc_move_data_r1]
  \\ conj_tac
  THEN1 (match_mp_tac gc_move_data_h2 \\ fs [EVAL ``(to_gen_state c s).ok``])
  \\ drule gen_gcTheory.gc_move_loop_ok
  \\ fs [to_gen_state_def]);

val f_old_ptrs_def = Define `
  f_old_ptrs conf heap =
    {a | isSomeDataElement (heap_lookup a heap)
         /\ (a < conf.gen_start \/ conf.refs_start <= a)}`;

Theorem f_old_ptrs_finite[simp]:
   !heap conf.
    FINITE (f_old_ptrs conf heap)
Proof
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
     (sg `?y. FINITE y /\
          ({a | isSomeDataElement (heap_lookup a (SNOC x heap))} =
           y UNION {a | isSomeDataElement (heap_lookup a heap)})`)
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
  \\ imp_res_tac heap_lookup_LESS
QED

val f_old_ptrs_finite_open = save_thm("f_old_ptrs_finite_open[simp]",
  f_old_ptrs_finite |> SIMP_RULE std_ss [f_old_ptrs_def]);

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

val roots_ok_APPEND = prove(
  ``!left right heap.
    roots_ok (left ++ right) heap ==>
    roots_ok left heap /\
    roots_ok right heap
  ``,
  fs [roots_ok_def] \\ rpt strip_tac \\ res_tac);

val roots_ok_CONS = prove(
  ``!h t.
    roots_ok (h::t) heap ==>
    roots_ok t heap``,
  metis_tac [CONS_APPEND,roots_ok_APPEND]);

Theorem isSomeDataElement_to_gen_heap_list[simp]:
   !n heap.
    isSomeDataElement (heap_lookup n (to_gen_heap_list conf heap))
    = isSomeDataElement (heap_lookup n heap)
Proof
  rewrite_tac [to_gen_heap_list_def]
  \\ Induct_on `heap`
  >- fs [heap_lookup_def,isSomeDataElement_def]
  \\ Cases \\ strip_tac
  \\ rpt
     (fs [heap_lookup_def,to_gen_heap_element_def]
     \\ IF_CASES_TAC >- fs [isSomeDataElement_def]
     \\ simp []
     \\ IF_CASES_TAC
     \\ fs [el_length_def]
     \\ fs [isSomeDataElement_def])
QED

val isSomeDataElement_to_gen_heap_element = save_thm("isSomeDataElement_to_gen_heap_element",
  isSomeDataElement_to_gen_heap_list |> SIMP_RULE std_ss [to_gen_heap_list_def]);

val MEM_refs_to_roots_IMP_MEM = prove(
  ``!heap_refs.
    MEM (Pointer ptr u) (refs_to_roots conf heap_refs) ==>
    ?xs l d ptr' u'.
    MEM (DataElement xs l d) heap_refs /\
    MEM (Pointer ptr' u') xs /\
    (ptr = ptr' - conf.gen_start) /\
    (u = Real u') /\
    (conf.gen_start <= ptr') /\
    (ptr' < conf.refs_start)
  ``,
  Induct \\ fs [refs_to_roots_def]
  \\ Cases \\ fs [refs_to_roots_def]
  \\ reverse strip_tac
  >- metis_tac []
  \\ qexists_tac `l` \\ qexists_tac `n` \\ qexists_tac `b`
  \\ simp []
  \\ pop_assum mp_tac
  \\ qspec_tac (`l`,`xs`)
  \\ Induct \\ fs []
  \\ Cases \\ fs [to_gen_heap_address_def]
  \\ IF_CASES_TAC \\ fs [] >- metis_tac []
  \\ IF_CASES_TAC \\ fs [] >- metis_tac []
  \\ reverse strip_tac \\ rveq
  >- metis_tac []
  \\ qexists_tac `n` \\ qexists_tac `a`
  \\ fs []);

val MEM_to_gen_roots_IMP_MEM = prove(
  ``!roots.
    MEM (Pointer ptr u) (to_gen_roots conf roots)
    ==>
    ?ptr' u'.
    MEM (Pointer ptr' u') roots /\
    (ptr = ptr' - conf.gen_start) /\
    (u = Real u') /\
    (conf.gen_start <= ptr') /\
    (ptr' < conf.refs_start)
  ``,
  Induct \\ fs [to_gen_roots_def]
  \\ Cases \\ fs [to_gen_heap_address_def]
  \\ IF_CASES_TAC \\ fs []
  >- metis_tac []
  \\ IF_CASES_TAC \\ fs []
  >- metis_tac []
  \\ reverse strip_tac \\ rveq
  >- metis_tac []
  \\ qexists_tac `n` \\ qexists_tac `a`
  \\ strip_tac \\ fs []);

val roots_ok_simulation = prove(
  ``!roots heap heap_old heap_current heap_refs (conf :'b gen_gc_partial_conf).
    roots_ok roots (heap :('a,'b) heap_element list) /\
    heap_ok heap conf.limit /\
    (heap_segment (conf.gen_start,conf.refs_start) heap = SOME (heap_old,heap_current,heap_refs)) /\
    (conf.gen_start ≤ conf.refs_start)
    ==>
    roots_ok
      (to_gen_roots conf roots ++ refs_to_roots conf heap_refs)
      (MAP (to_gen_heap_element conf) heap_current)
  ``,
  rpt strip_tac
  \\ drule heap_segment_IMP
  \\ simp [] \\ strip_tac \\ rveq
  \\ simp [roots_ok_def]
  \\ rpt strip_tac
  >- (fs [roots_ok_def]
     \\ drule MEM_to_gen_roots_IMP_MEM
     \\ strip_tac \\ rveq
     \\ first_x_assum drule
     \\ rewrite_tac [heap_lookup_APPEND]
     \\ fs []
     \\ simp [isSomeDataElement_to_gen_heap_element])
  \\ drule MEM_refs_to_roots_IMP_MEM
  \\ strip_tac \\ rveq
  \\ fs [heap_ok_def]
  \\ qpat_x_assum `!xs. _` (qspecl_then [`xs`,`l`,`d`] mp_tac) \\ simp []
  \\ disch_then drule
  \\ rewrite_tac [heap_lookup_APPEND]
  \\ fs []
  \\ simp [isSomeDataElement_to_gen_heap_element]);

val heap_length_to_gen_heap_element = save_thm("heap_length_to_gen_heap_element[simp]",
  heap_length_to_gen_heap_list |> SIMP_RULE std_ss [to_gen_heap_list_def]);

val MEM_to_gen_heap_IMP_MEM = prove(
  ``!heap_current xs l d ptr u.
    MEM (DataElement xs l d) (MAP (to_gen_heap_element conf) heap_current) /\
    MEM (Pointer ptr u) xs
    ==>
    ?xs' u' ptr'.
    MEM (DataElement xs' l d) heap_current /\
    MEM (Pointer ptr' u') xs' /\
    (xs = MAP (to_gen_heap_address conf) xs') /\
    (ptr = ptr' - conf.gen_start) /\
    (u = Real u') /\
    (ptr' < conf.refs_start) /\
    (conf.gen_start <= ptr')
  ``,
  Induct \\ fs []
  \\ Cases \\ fs [to_gen_heap_element_def]
  \\ rpt gen_tac \\ simp []
  \\ reverse strip_tac
  >- metis_tac []
  \\ rveq
  \\ qexists_tac `l` \\ simp []
  \\ pop_assum mp_tac
  \\ qspec_tac (`l`,`xs`)
  \\ Induct \\ fs []
  \\ Cases \\ simp [to_gen_heap_address_def]
  \\ IF_CASES_TAC \\ simp []
  >- metis_tac []
  \\ IF_CASES_TAC \\ simp []
  >- metis_tac []
  \\ reverse strip_tac \\ rveq \\ simp []
  >- metis_tac []
  \\ qexists_tac `n`
  \\ fs []);

val heap_ok_simulation = prove(
  ``!heap heap_old heap_current heap_refs (conf :'b gen_gc_partial_conf).
    heap_ok (heap :('a,'b) heap_element list) conf.limit /\
    (heap_segment (conf.gen_start,conf.refs_start) heap = SOME (heap_old,heap_current,heap_refs)) /\
    (conf.gen_start ≤ conf.refs_start) /\
    (conf.refs_start ≤ conf.limit)
    ==>
    heap_ok
      (MAP (to_gen_heap_element conf) heap_current)
      (to_gen_conf conf).limit``,
  rpt strip_tac
  \\ drule heap_segment_IMP \\ simp []
  \\ strip_tac \\ rveq
  \\ fs [heap_ok_def]
  \\ fs [to_gen_conf_def]
  \\ rpt strip_tac
  >- fs [heap_length_APPEND]
  >- (fs [FILTER_APPEND]
     \\ qpat_x_assum `FILTER _ heap_current = []` mp_tac
     \\ qspec_tac (`heap_current`,`heaps`)
     \\ Induct
     \\ fs []
     \\ Cases \\ fs [isForwardPointer_def,to_gen_heap_element_def])
  \\ drule MEM_to_gen_heap_IMP_MEM \\ simp []
  \\ disch_then drule
  \\ strip_tac \\ rveq
  \\ qpat_x_assum `!xs. _` (qspecl_then [`xs'`,`l`,`d`] mp_tac)
  \\ simp []
  \\ disch_then drule
  \\ rewrite_tac [GSYM APPEND_ASSOC]
  \\ rewrite_tac [Once heap_lookup_APPEND] \\ fs []
  \\ drule heap_segment_IMP \\ simp []
  \\ rewrite_tac [Once heap_lookup_APPEND] \\ fs [heap_length_APPEND]
  \\ simp [isSomeDataElement_to_gen_heap_element]);

val new_f_FDOM = prove(``
  (∀i. i ∈ FDOM f ⇒ isSomeDataElement (heap_lookup (i + conf.gen_start) heap)) ==>
  (x IN FDOM (new_f f conf heap) =
  if x < conf.gen_start ∨ conf.refs_start ≤ x then
  isSomeDataElement (heap_lookup x heap) else
  x IN (IMAGE ($+ conf.gen_start) (FDOM f)))``,
  strip_tac
  \\ fs [new_f_def]
  \\ simp [f_old_ptrs_def]
  \\ reverse IF_CASES_TAC
  >- simp []
  \\ simp []
  \\ eq_tac
  \\ rw []
  \\ fs []);

val new_f_FAPPLY = prove(
  ``(x ∈ FDOM (new_f f conf heap)) /\
    (∀i. i ∈ FDOM f ⇒ isSomeDataElement (heap_lookup (i + conf.gen_start) heap)) ==>
    (new_f f conf heap ' x =
    if x < conf.gen_start ∨ conf.refs_start ≤ x then
    x else
    conf.gen_start + f ' (x − conf.gen_start))``,
  strip_tac
  \\ drule new_f_FDOM
  \\ simp []
  \\ strip_tac
  \\ simp [new_f_def]
  \\ IF_CASES_TAC
  >- (fs [FUNION_DEF,f_old_ptrs_def]
     \\ fs [FUN_FMAP_DEF])
  \\ fs [FUNION_DEF,f_old_ptrs_def]
  \\ fs [FUN_FMAP_DEF]);

Theorem isSomeDataElement_heap_lookup_heap_expand[simp]:
   ~isSomeDataElement (heap_lookup x (heap_expand n))
Proof
  rewrite_tac [heap_expand_def]
  \\ Cases_on `n` \\ fs []
  \\ fs [heap_lookup_def,isSomeDataElement_def]
QED

val heap_lookup_heap_expand = isSomeDataElement_heap_lookup_heap_expand
  |> SIMP_RULE std_ss [isSomeDataElement_def];

val heap_lookup_old_IMP = prove(
  ``!i ys.
    (partial_gc conf (roots,heap) = (roots1,state1)) /\
    gen_inv conf heap /\
    (heap_lookup i heap = SOME (DataElement xs l d)) /\
    (i < conf.gen_start) ==>
    (heap_lookup i (state1.old ++ ys) = SOME (DataElement xs l d))``,
  fs [] \\ rpt strip_tac \\ fs [gen_inv_def]
  \\ drule partial_gc_IMP
  \\ fs [] \\ strip_tac
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
  ``!x.
    (partial_gc conf (roots,heap) = (roots1,state1)) /\
    gen_inv conf heap /\
    (heap_lookup x heap = SOME (DataElement xs l d)) /\
    (heap_length (state1.old ++ state1.h1 ++ heap_expand state1.n) = conf.refs_start) /\
    (conf.refs_start ≤ x)
    ==>
    ?xs1.
    (heap_lookup x (state1.old ++ state1.h1 ++ heap_expand state1.n ++ state1.r1) =
      SOME (DataElement xs1 l d))
  ``,
  rpt strip_tac
  \\ fs [gen_inv_def]
  \\ drule heap_segment_IMP \\ simp []
  \\ strip_tac
  \\ rveq
  \\ fs [partial_gc_def]
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ drule gc_move_list_IMP \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac `gc_move_list _ state0 _ = _`
  \\ qpat_x_assum `heap_lookup _ _ = _` mp_tac
  \\ `heap_length (heap_old ++ heap_current) = conf.refs_start` by simp [heap_length_APPEND]
  \\ once_rewrite_tac [heap_lookup_APPEND]
  \\ fs []
  \\ qpat_x_assum `gc_move_ref_list _ _ _ = _` mp_tac
  \\ drule gc_move_data_IMP \\ fs []
  \\ strip_tac
  \\ fs []
  \\ qspec_tac (`x - conf.refs_start`, `ptr`)
  \\ qspec_tac (`state`,`state`)
  \\ qspec_tac (`state'`,`state'`)
  \\ qspec_tac (`refs'`,`refs'`)
  \\ qspec_tac (`heap_refs`,`heap_refs`)
  \\ Induct
  >- simp [gc_move_ref_list_def]
  \\ Cases \\ simp [gc_move_ref_list_def]
  \\ rpt gen_tac
  \\ pairarg_tac \\ simp []
  \\ pairarg_tac \\ simp []
  \\ strip_tac
  \\ rveq
  \\ fs [heap_lookup_def]
  \\ IF_CASES_TAC \\ fs []
  \\ simp [el_length_def]
  \\ simp [heap_lookup_def]
  \\ strip_tac
  \\ qpat_x_assum `!refs state state' ptr. _ ==> __` drule
  \\ fs []);

val heap_lookup_refs_IMP_ALT = prove(
  ``(partial_gc conf (roots,heap) = (roots1,state1)) /\
    gen_inv conf heap /\
    isSomeDataElement (heap_lookup x heap) /\
    (heap_length (state1.old ++ state1.h1 ++ heap_expand state1.n) = conf.refs_start) /\
    (conf.refs_start ≤ x)
    ==>
    isSomeDataElement (heap_lookup x (state1.old ++ state1.h1 ++ heap_expand state1.n ++ state1.r1))
  ``,
  metis_tac [isSomeDataElement_def,heap_lookup_refs_IMP]);

val ADDR_MAP_ID = prove(
  ``(!x u. MEM (Pointer x u) xs ==> (x = f x))
    ==> (xs = ADDR_MAP f xs)``,
  Induct_on `xs`
  \\ fs [ADDR_MAP_def]
  \\ Cases
  \\ fs [ADDR_MAP_def]
  \\ metis_tac []);

val MEM_heap_old = prove(
  ``!n m i x.
    (heap_segment (n,m) heap = SOME (heap_old,heap_current,heap_refs)) /\
    (n <= m) /\
    i < n /\
    (heap_lookup i heap = SOME x)
    ==>
    MEM x heap_old``,
  rpt strip_tac \\ drule heap_segment_IMP
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ drule LESS_IMP_heap_lookup
  \\ metis_tac [heap_lookup_IMP_MEM,GSYM APPEND_ASSOC]);

val FILTER_isForward_to_gen = prove(
  ``!xs.
    (FILTER isForwardPointer (to_gen_heap_list conf xs) = []) ==>
    (FILTER isForwardPointer xs = [])``,
  Induct
  \\ fs [to_gen_heap_list_def]
  \\ Cases
  \\ fs [to_gen_heap_element_def,isForwardPointer_def]);

val isSomeData_to_gen_heap_IMP = prove(
  ``!xs ptr conf ys l d.
    (heap_lookup ptr (to_gen_heap_list conf xs) = SOME (DataElement ys l d))
    ==>
    isSomeDataElement (heap_lookup ptr xs)``,
  Induct
  \\ fs [to_gen_heap_list_def,heap_lookup_def]
  \\ Cases \\ fs [to_gen_heap_element_def] \\ rpt gen_tac
  >- (IF_CASES_TAC \\ fs [el_length_def]
     \\ strip_tac
     \\ metis_tac [])
  >- (IF_CASES_TAC \\ fs [el_length_def]
     \\ strip_tac
     \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs [el_length_def]
  >- simp [isSomeDataElement_def]
  \\ strip_tac
  \\ metis_tac []);

val refs_to_roots_APPEND = prove(
  ``!xs ys.
    refs_to_roots conf (xs ++ ys) = refs_to_roots conf xs ++ refs_to_roots conf ys``,
  Induct
  \\ fs [refs_to_roots_def]
  \\ Cases \\ fs [refs_to_roots_def]);

val gc_move_refs_isForwardPointer = prove(
  ``∀refs refs1 state1 state.
    (gc_move_ref_list conf state refs = (refs1,state1)) ∧
    (FILTER isForwardPointer refs = []) ⇒
    (FILTER isForwardPointer refs1 = [])
  ``,
  Induct
  >- (rpt strip_tac
     \\ fs [gc_move_ref_list_def]
     \\ rveq \\ fs [])
  \\ Cases
  \\ fs [gc_move_ref_list_def]
  \\ fs [isForwardPointer_def]
  \\ strip_tac
  \\ rveq
  \\ rpt strip_tac
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ rveq
  \\ simp [FILTER] \\ fs [isForwardPointer_def]
  \\ res_tac);

Theorem el_length_to_gen_heap_element[simp]:
   el_length (to_gen_heap_element conf h) = el_length h
Proof
  Cases_on `h` \\ fs [to_gen_heap_element_def,el_length_def]
QED

val to_gen_heap_element_isSomeData = prove(
  ``!xs n.
    isSomeDataElement (heap_lookup n (MAP (to_gen_heap_element (conf : 'b gen_gc_partial_conf)) (xs:('a,'b) heap_element list))) ==>
    isSomeDataElement (heap_lookup n xs)``,
  Induct
  >- (fs [] \\ rw []
     \\ fs [heap_lookup_def]
     \\ fs [isSomeDataElement_def])
  \\ gen_tac
  \\ fs []
  \\ fs [heap_lookup_def]
  \\ strip_tac
  \\ IF_CASES_TAC \\ fs []
  >- (Cases_on `h`
     \\ fs [to_gen_heap_element_def,isSomeDataElement_def])
  \\ IF_CASES_TAC \\ fs []
  >- (fs [isSomeDataElement_def])
  \\ fs [el_length_to_gen_heap_element]
  \\ fs []);

val heap_lookup_GT_FALSE = prove(
  ``!xs n.
    ¬(n < heap_length xs) ==>
    ~(isSomeDataElement (heap_lookup n xs))``,
  Induct
  >- (fs [heap_lookup_def,isSomeDataElement_def])
  \\ fs [heap_lookup_def,heap_length_def]
  \\ rpt gen_tac
  \\ IF_CASES_TAC \\ fs []
  \\ metis_tac [el_length_NOT_0]);

val heap_lookup_to_gen_heap_element = prove(
  ``!heap_current i.
      isSomeDataElement
        (heap_lookup i (MAP (to_gen_heap_element conf) heap_current)) =
      isSomeDataElement (heap_lookup i heap_current)``,
  Induct THEN1 fs [heap_lookup_def,isSomeDataElement_def]
  \\ fs [heap_lookup_def] \\ rw []
  \\ Cases_on `h` \\ fs [to_gen_heap_element_def,isSomeDataElement_def]);

val partial_gc_heap_length_lemma = prove (
  ``!roots'.
    (partial_gc conf (roots,heap) = (roots1,state1)) /\
    (gen_gc (to_gen_conf conf) (gen_roots,gen_heap) =
      (roots',to_gen_state conf state1)) /\
    (heap_segment (conf.gen_start,conf.refs_start) heap = SOME (heap_old,heap_current,heap_refs)) /\
    (conf.gen_start ≤ conf.refs_start) /\
    (conf.refs_start ≤ conf.limit) /\
    roots_ok gen_roots gen_heap /\
    heap_ok gen_heap (to_gen_conf conf).limit
    ==>
    (heap_length (state1.old ++ state1.h1 ++ heap_expand state1.n) = conf.refs_start)
  ``,
  rpt strip_tac
  \\ rewrite_tac [GSYM APPEND_ASSOC]
  \\ once_rewrite_tac [heap_length_APPEND]
  \\ fs [partial_gc_def] \\ rfs []
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ drule gc_move_data_IMP
  \\ strip_tac \\ fs []
  \\ drule gc_move_ref_list_IMP
  \\ strip_tac \\ fs []
  \\ drule gc_move_list_IMP
  \\ strip_tac \\ fs []
  \\ drule gen_gc_thm
  \\ disch_then drule
  \\ strip_tac
  \\ rveq
  \\ `state'' = to_gen_state conf state1` by fs []
  \\ drule heap_segment_IMP \\ fs []
  \\ strip_tac
  \\ fs []
  \\ `heap_length (state1.h1 ++ heap_expand state1.n) = heap_length (to_gen_heap_list conf state1.h1 ++ heap_expand state1.n)` by (fs [heap_length_APPEND]
     \\ fs [heap_length_heap_expand])
  \\ `heap_length (to_gen_heap_list conf state1.h1 ++ heap_expand state1.n) = conf.refs_start - conf.gen_start` by (fs [gc_inv_def]
     \\ rewrite_tac [heap_length_APPEND]
     \\ qpat_x_assum `_ = (to_gen_state conf state1).a` mp_tac
     \\ qpat_x_assum `_ = (to_gen_conf conf).limit` kall_tac
     \\ qpat_x_assum `_ = (to_gen_conf conf).limit` mp_tac
     \\ rewrite_tac [to_gen_state_def]
     \\ rewrite_tac [empty_state_def,gc_state_component_equality]
     \\ simp [gc_state_component_equality]
     \\ fs [to_gen_conf_def]
     \\ simp [heap_length_heap_expand])
  \\ rveq
  \\ fs []);

val gc_move_ref_list_isSomeDataElement = prove (
  ``!refs ptr state state1 refs1.
    (gc_move_ref_list conf state refs = (refs1,state1)) /\
    isSomeDataElement (heap_lookup ptr refs) ==>
    isSomeDataElement (heap_lookup ptr refs1)
  ``,
  Induct
  >- fs [heap_lookup_def,isSomeDataElement_def]
  \\ Cases
  \\ fs [gc_move_ref_list_def]
  \\ ntac 3 gen_tac
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ strip_tac
  \\ rveq
  \\ fs [heap_lookup_def]
  \\ IF_CASES_TAC \\ simp []
  >- fs [isSomeDataElement_def]
  \\ IF_CASES_TAC \\ fs [el_length_def]
  \\ res_tac);

val ptr_Real_lemma = prove(
  ``!ys ptr. MEM (Pointer ptr u) ys /\
    (conf.gen_start <= ptr) /\
    (ptr < conf.refs_start)
    ==>
    MEM (Pointer (ptr − conf.gen_start) (Real u)) (MAP (to_gen_heap_address conf) ys)
  ``,
  gen_tac
  \\ fs [Once MEM_SPLIT]
  \\ rpt strip_tac
  \\ rveq
  \\ fs [MAP_APPEND]
  \\ fs [to_gen_heap_address_def]);

val partial_gc_refs_isSomeDataElement_isSomeDataElement = prove(
  ``!ptr heap state1 heap_current heap_refs.
    (partial_gc conf (roots,heap)
     = (roots1,state1)) /\
    (heap_segment (conf.gen_start,conf.refs_start) heap = SOME (state1.old,heap_current,heap_refs)) /\
    isSomeDataElement (heap_lookup ptr heap_refs)
    ==>
    isSomeDataElement (heap_lookup ptr state1.r1)
  ``,
  rpt strip_tac
  \\ fs [partial_gc_def]
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ drule gc_move_data_IMP
  \\ strip_tac \\ rveq
  \\ fs [gc_state_component_equality]
  \\ qpat_x_assum `isSomeDataElement _` mp_tac
  \\ qpat_x_assum `gc_move_ref_list _ _ _ = _` mp_tac
  \\ qspec_tac (`state`,`state0`)
  \\ qspec_tac (`state'`,`state1`)
  \\ qspec_tac (`ptr`,`ptr0`)
  \\ qspec_tac (`refs'`,`refs1`)
  \\ qspec_tac (`heap_refs`,`refs0`)
  \\ Induct
  \\ fs [gc_move_ref_list_def]
  \\ Cases
  \\ fs [gc_move_ref_list_def]
  \\ rpt gen_tac
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ rveq
  \\ fs [heap_lookup_def]
  \\ IF_CASES_TAC \\ simp []
  >- fs [isSomeDataElement_def]
  \\ IF_CASES_TAC \\ fs [el_length_def]
  \\ first_x_assum match_mp_tac
  \\ metis_tac []);

val isSomeData_to_gen_heap_IMP_isSomeData = prove (
  ``!heap ptr.
    isSomeDataElement (heap_lookup ptr (to_gen_heap_list conf heap ++ heap_expand state1.n)) ==>
    isSomeDataElement (heap_lookup ptr (heap ++ heap_expand state1.n))
  ``,
  Induct
  \\ fs [heap_lookup_def,to_gen_heap_list_def]
  \\ Cases \\ strip_tac
  >- (IF_CASES_TAC \\ simp []
     >- fs [to_gen_heap_element_def,isSomeDataElement_def]
     \\ IF_CASES_TAC \\ simp [] >- simp [isSomeDataElement_def])
  >- (IF_CASES_TAC \\ simp []
     >- fs [to_gen_heap_element_def,isSomeDataElement_def]
     \\ IF_CASES_TAC \\ simp [] >- simp [isSomeDataElement_def])
  \\ IF_CASES_TAC \\ simp []
  >- simp [isSomeDataElement_def]
  \\ IF_CASES_TAC \\ simp []
  \\ simp [isSomeDataElement_def]);

val refs_root_IMP_isSomeData = prove(
  ``!(state1 : ('a,'b) gc_state) (conf : 'b gen_gc_partial_conf) refs.
    MEM (DataElement xs l d) refs /\
    MEM (Pointer ptr u) xs /\
    roots_ok (refs_to_roots conf refs)
      (to_gen_heap_list conf state1.h1 ++ heap_expand state1.n) /\
    (ptr < conf.refs_start) /\
    ~(ptr < conf.gen_start)
    ==>
    isSomeDataElement (heap_lookup (ptr − conf.gen_start) (state1.h1 ++ heap_expand state1.n))
  ``,
  ntac 2 gen_tac \\ Induct \\ fs []
  \\ Cases \\ fs [refs_to_roots_def]
  \\ reverse strip_tac \\ rveq \\ fs []
  >- (drule roots_ok_APPEND \\ strip_tac
     \\ fs [])
  \\ qpat_x_assum `MEM _ _` mp_tac \\ simp [MEM_SPLIT]
  \\ strip_tac \\ rveq
  \\ fs [MAP]
  \\ qpat_x_assum `roots_ok _ _` mp_tac
  \\ rewrite_tac [GSYM APPEND_ASSOC]
  \\ strip_tac
  \\ drule roots_ok_APPEND \\ strip_tac
  \\ drule roots_ok_APPEND \\ strip_tac
  \\ qpat_x_assum `roots_ok [_] _` mp_tac
  \\ simp [roots_ok_def]
  \\ simp [to_gen_heap_address_def]
  \\ metis_tac [isSomeData_to_gen_heap_IMP_isSomeData]);

val ADDR_MAP_APPEND_LENGTH_IMP = prove(
  ``!(roots : 'a heap_address list) (heap_refs : ('a,'b) heap_element list) (f : num |-> num) roots1 (r1 : ('a,'b) heap_element list) (conf : 'b gen_gc_partial_conf).
    (ADDR_MAP ($' f) (to_gen_roots conf roots ++ refs_to_roots conf heap_refs) =
       to_gen_roots conf roots1 ++ refs_to_roots conf r1) /\
    (LENGTH roots = LENGTH roots1)
    ==>
    (ADDR_MAP ($' f) (to_gen_roots conf roots) = to_gen_roots conf roots1) /\
    (ADDR_MAP ($' f) (refs_to_roots conf heap_refs) = refs_to_roots conf r1)
  ``,
  Induct \\ rpt gen_tac
  >- (simp [to_gen_roots_def]
     \\ simp [ADDR_MAP_def]
     \\ Cases_on `roots1`
     \\ fs [])
  \\ fs [to_gen_roots_def]
  \\ Cases_on `roots1`
  \\ fs []
  \\ strip_tac
  \\ Cases_on `h`
  \\ fs [to_gen_heap_address_def]
  >- (IF_CASES_TAC
     \\ fs [ADDR_MAP_def]
     >- (first_x_assum drule \\ fs [])
     \\ IF_CASES_TAC \\ fs [ADDR_MAP_def]
     \\ first_x_assum drule \\ fs [])
  \\ fs [ADDR_MAP_def]
  \\ first_x_assum drule \\ fs []);

val heap_lookup_by_f_isSomeData_lemma = prove(
  ``!h1 x xs (state1 : ('a,'b) gc_state) (heap : ('a,'b) heap_element list) conf.
    (heap_lookup x
      (MAP (to_gen_heap_element conf) h1 ++ heap_expand state1.n) =
      SOME (DataElement (ADDR_MAP ($' f) (MAP (to_gen_heap_address conf) xs)) l d)) /\
    (∀u ptr.
       MEM (Pointer ptr u) xs ⇒
       isSomeDataElement (heap_lookup ptr heap)) /\
    (∀ptr u.
       MEM (Pointer ptr u) (MAP (to_gen_heap_address conf) xs) ⇒
       ptr ∈ FDOM f)
    ==>
    (heap_lookup x (h1 ++ heap_expand state1.n ++ state1.r1) =
      SOME (DataElement (ADDR_MAP ($' (new_f f conf heap)) xs) l d))
  ``,
  Induct
  >- (rpt strip_tac \\ fs [MAP]
     \\ fs [heap_lookup_heap_expand])
  \\ rpt gen_tac
  \\ fs [MAP]
  \\ fs [heap_lookup_def]
  \\ reverse IF_CASES_TAC \\ fs []
  >- (rpt strip_tac
     \\ metis_tac [])
  \\ qpat_x_assum `!x. _` kall_tac
  \\ Cases_on `h` \\ fs [to_gen_heap_element_def]
  \\ rw []
  \\ ntac 3 (pop_assum mp_tac)
  \\ qspec_tac (`l'`,`left`)
  \\ qspec_tac (`xs`,`right`)
  \\ Induct \\ fs []
  >- (Cases \\ fs [ADDR_MAP_def,MAP,to_gen_heap_address_def])
  \\ Cases_on `left`
  >- (Cases
     \\ fs [to_gen_heap_address_def,ADDR_MAP_def]
     \\ IF_CASES_TAC \\ fs [ADDR_MAP_def]
     \\ IF_CASES_TAC \\ fs [ADDR_MAP_def])
  \\ fs [MAP]
  \\ Cases \\ Cases_on `h` \\ fs [to_gen_heap_address_def]
  >- (IF_CASES_TAC \\ IF_CASES_TAC
     >- (fs [ADDR_MAP_def] \\ reverse (rw [])
        >- metis_tac []
        \\ simp [new_f_def,f_old_ptrs_def]
        \\ pop_assum kall_tac
        \\ pop_assum (qspecl_then [`a`,`n`] assume_tac)
        \\ fs []
        \\ simp [FUNION_DEF]
        \\ simp [FUN_FMAP_DEF])
     >- (IF_CASES_TAC \\ fs [ADDR_MAP_def])
     >- (IF_CASES_TAC \\ fs [ADDR_MAP_def]
        \\ IF_CASES_TAC \\ fs [ADDR_MAP_def]
        \\ reverse (rw [])
        >- metis_tac []
        \\ simp [new_f_def,f_old_ptrs_def]
        \\ pop_assum kall_tac
        \\ pop_assum (qspecl_then [`a`,`n`] assume_tac)
        \\ fs []
        \\ simp [FUNION_DEF]
        \\ simp [FUN_FMAP_DEF])
     \\ IF_CASES_TAC \\ fs [ADDR_MAP_def]
     \\ IF_CASES_TAC \\ fs [ADDR_MAP_def]
     \\ reverse (rw [])
     >- metis_tac []
     \\ simp [new_f_def,f_old_ptrs_def] \\ fs []
     \\ simp [FUNION_DEF]
     \\ pop_assum (qspecl_then [`n − conf.gen_start`,`Real a`] assume_tac)
     \\ fs []
     \\ `n IN IMAGE ($+ conf.gen_start) (FDOM f)` by (fs [] \\ qexists_tac `n - conf.gen_start` \\ fs [])
     \\ simp [FUN_FMAP_DEF])
  >- (IF_CASES_TAC \\ fs [ADDR_MAP_def]
     \\ IF_CASES_TAC \\ fs [ADDR_MAP_def])
  >- (IF_CASES_TAC \\ fs [ADDR_MAP_def]
     \\ IF_CASES_TAC \\ fs [ADDR_MAP_def])
  \\ fs [ADDR_MAP_def]
  \\ rw []
  \\ metis_tac []);

val similar_ptr_def = Define `
  (similar_ptr conf (Pointer p1 d1) (Pointer p2 d2) <=> (d2 = d1)) /\
  (similar_ptr conf x1 x2 = (x1 = x2))`

val similar_data_def = Define `
  (similar_data conf (DataElement xs1 l1 d1) (DataElement xs2 l2 d2) <=>
    (l2 = l1) /\ (d2 = d1) /\ LIST_REL (similar_ptr conf) xs1 xs2) /\
  (similar_data conf x y = (x = y))`;

val LENGTH_ADDR_MAP = prove(
  ``!xs. LENGTH (ADDR_MAP f xs) = LENGTH xs``,
  Induct \\ fs [LENGTH,ADDR_MAP_def]
  \\ Cases \\ fs [LENGTH,ADDR_MAP_def]);

val heap_lookup_similar_data_IMP = prove(
  ``!h1 h2 n.
      LIST_REL (similar_data conf) h1 h2 /\
      (heap_lookup n h1 = SOME (DataElement xs1 l d)) /\
      (ADDR_MAP ($FAPPLY f) (refs_to_roots conf h1) = refs_to_roots conf h2) ==>
      ?xs2. (heap_lookup n h2 = SOME (DataElement xs2 l d)) /\
            (ADDR_MAP ($' f) (MAP (to_gen_heap_address conf) xs1) =
               MAP (to_gen_heap_address conf) xs2)``,
  Induct THEN1 fs [heap_lookup_def]
  \\ fs [heap_lookup_def,PULL_EXISTS]
  \\ rpt gen_tac
  \\ Cases_on `n = 0` \\ fs []
  THEN1
   (strip_tac \\ rveq
    \\ Cases_on `y` \\ fs [similar_data_def] \\ rveq
    \\ fs [refs_to_roots_def,ADDR_MAP_APPEND]
    \\ qmatch_assum_abbrev_tac `ys1 ++ ys2 = ts1 ++ ts2`
    \\ qsuff_tac `LENGTH ys1 = LENGTH ts1`
    THEN1 metis_tac [APPEND_11_LENGTH]
    \\ unabbrev_all_tac \\ fs [LENGTH_ADDR_MAP]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [])
  \\ Cases_on `h` \\ Cases_on `y` \\ fs [similar_data_def]
  \\ strip_tac \\ rveq
  \\ fs [el_length_def]
  \\ first_x_assum match_mp_tac \\ fs []
  \\ fs [refs_to_roots_def,ADDR_MAP_APPEND]
  \\ qmatch_assum_abbrev_tac `ys1 ++ ys2 = ts1 ++ ts2`
  \\ qsuff_tac `LENGTH ys1 = LENGTH ts1`
  THEN1 metis_tac [APPEND_11_LENGTH]
  \\ unabbrev_all_tac \\ fs [LENGTH_ADDR_MAP]
  \\ imp_res_tac LIST_REL_LENGTH \\ fs []);

val new_f_old_parts = prove(
  ``n IN FDOM (new_f f conf heap) /\
    (∀i. i ∈ FDOM f ⇒
         isSomeDataElement (heap_lookup (i + conf.gen_start) heap)) /\
    (n < conf.gen_start \/ conf.refs_start ≤ n) ==>
    (new_f f conf heap ' n = n)``,
  fs [new_f_FAPPLY]);

val gc_move_list_similar = prove(
  ``!xs state1 ys state2.
      (gc_move_list conf state1 xs = (ys,state2)) ==>
      LIST_REL (similar_ptr conf) xs ys``,
  Induct \\ fs [gc_move_list_def]
  \\ rw[] \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ res_tac \\ fs []
  \\ Cases_on `h` \\ fs [gc_move_def]
  \\ every_case_tac \\ fs []
  \\ rw[] \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ fs [similar_ptr_def]);

val gc_move_ref_list_similar = prove(
  ``!heap_refs state refs' state' conf.
      (gc_move_ref_list conf state heap_refs = (refs',state')) ==>
      LIST_REL (similar_data conf) heap_refs refs'``,
  Induct \\ fs [gc_move_ref_list_def]
  \\ Cases
  \\ fs [gc_move_ref_list_def,similar_data_def]
  \\ TRY (rw [] \\ match_mp_tac EVERY2_refl \\ fs []
          \\ Cases \\ fs [similar_data_def]
          \\ rw [] \\ match_mp_tac EVERY2_refl \\ fs []
          \\ Cases \\ fs [similar_ptr_def] \\ NO_TAC)
  \\ rw[] \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ fs [] \\ res_tac \\ fs []
  \\ fs [similar_data_def]
  \\ imp_res_tac gc_move_list_similar \\ fs []);

val IMP_gen_inv = prove(
  ``heap_ok (heap:('a,'b) heap_element list) conf.limit /\
    heap_gen_ok heap conf ==>
    gen_inv conf heap``,
  fs [gen_inv_def,heap_gen_ok_def] \\ strip_tac \\ fs []
  \\ qpat_x_assum `SOME _ = _` (assume_tac o GSYM) \\ fs []
  \\ fs [EVERY_MEM] \\ rpt strip_tac
  THEN1 (Cases_on `e` \\ fs [heap_element_is_ref_def] \\ res_tac)
  THEN1 (Cases_on `e` \\ fs [heap_element_is_ref_def] \\ res_tac)
  THEN1
   (fs [heap_ok_def,FILTER_EQ_NIL]
    \\ fs [EVERY_MEM] \\ res_tac \\ fs [isForwardPointer_def])
  THEN1
   (fs [heap_ok_def,FILTER_EQ_NIL]
    \\ fs [EVERY_MEM] \\ res_tac \\ fs [isForwardPointer_def])
  \\ first_x_assum match_mp_tac
  \\ asm_exists_tac \\ fs []
  \\ asm_exists_tac \\ fs []);

Theorem partial_gc_related:
   roots_ok roots heap /\
    heap_ok (heap:('a,'b) heap_element list) conf.limit /\
    heap_gen_ok heap conf
    ==>
    ?state f.
      (partial_gc conf (roots:'a heap_address list,heap) =
         (ADDR_MAP (FAPPLY f) roots,state)) /\
      (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM f) /\
      (heap_ok
        (state.old ++ state.h1 ++ heap_expand state.n ++ state.r1) conf.limit) /\
      gc_related f heap (state.old ++ state.h1 ++ heap_expand state.n ++ state.r1) /\
      state.ok
Proof
  rpt strip_tac
  \\ `gen_inv conf heap` by (match_mp_tac IMP_gen_inv \\ fs [])
  \\ fs [gen_inv_def]
  \\ Cases_on `partial_gc conf (roots,heap)` \\ fs []
  \\ rename1 `_ = (roots1,state1)`
  \\ drule partial_gc_simulation
  \\ fs []
  \\ qpat_abbrev_tac `xx = gen_gc _ _`
  \\ `?x1 x2. xx = (x1,x2)` by (Cases_on `xx` \\ fs [])
  \\ unabbrev_all_tac \\ fs []
  \\ drule roots_ok_simulation
  \\ disch_then drule \\ simp [] \\ strip_tac
  \\ drule heap_ok_simulation
  \\ fs [] \\ strip_tac
  \\ impl_tac THEN1
   (drule gen_gc_ok
    \\ disch_then drule
    \\ fs [to_gen_heap_list_def])
  \\ strip_tac \\ rveq
  \\ `∀xs l d ptr u.
         (MEM (DataElement xs l d) state1.h1 ∨
          MEM (DataElement xs l d) state1.r1) ∧ MEM (Pointer ptr u) xs ∧
         (ptr < conf.gen_start ∨ conf.refs_start ≤ ptr) ⇒
         isSomeDataElement
           (heap_lookup ptr
              (state1.old ++ state1.h1 ++ heap_expand state1.n ++
               state1.r1))` by
   (fs [METIS_PROVE [] ``b\/c<=>(~b ==> c)``] \\ rw []
    \\ fs [sim_inv_def]
    \\ `has_old_ptr conf heap ptr` by
     (fs [SUBSET_DEF,IN_DEF]
      \\ first_x_assum match_mp_tac
      \\ fs [has_old_ptr_def] \\ fs [IN_DEF] \\ metis_tac [])
    \\ pop_assum mp_tac
    \\ fs [has_old_ptr_def] \\ strip_tac
    \\ Cases_on `ptr < conf.gen_start` \\ fs [] THEN1
     (drule partial_gc_IMP \\ fs [] \\ strip_tac \\ rveq
      \\ drule heap_segment_IMP \\ fs [heap_length_APPEND] \\ strip_tac \\ rveq
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ once_rewrite_tac [heap_lookup_APPEND]
      \\ reverse IF_CASES_TAC THEN1 fs []
      \\ qpat_x_assum `heap_ok _ _` kall_tac
      \\ qpat_x_assum `heap_ok _ _` mp_tac
      \\ simp [heap_ok_def]
      \\ rename1 `MEM (DataElement xs4 l4 d4) _`
      \\ strip_tac \\ pop_assum (qspecl_then [`xs4`,`l4`,`d4`,`ptr`,`u'`] mp_tac)
      \\ simp []
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ once_rewrite_tac [heap_lookup_APPEND]
      \\ simp [] \\ fs [])
    \\ drule partial_gc_IMP \\ fs [] \\ strip_tac \\ rveq
    \\ `heap_length (state1.old ++ state1.h1 ++ heap_expand state1.n) =
        conf.refs_start` by
     (fs [heap_length_APPEND,heap_length_heap_expand]
      \\ drule heap_segment_IMP \\ fs [heap_length_APPEND] \\ strip_tac \\ rveq
      \\ fs [heap_length_APPEND] \\ NO_TAC)
    \\ once_rewrite_tac [heap_lookup_APPEND]
    \\ simp [] \\ first_x_assum match_mp_tac
    \\ qpat_x_assum `heap_ok _ _` kall_tac
    \\ qpat_x_assum `heap_ok _ _` mp_tac
    \\ simp [heap_ok_def]
    \\ rename1 `MEM (DataElement xs4 l4 d4) _`
    \\ strip_tac \\ pop_assum (qspecl_then [`xs4`,`l4`,`d4`,`ptr`,`u'`] mp_tac)
    \\ drule heap_segment_IMP \\ fs [heap_length_APPEND] \\ strip_tac \\ rveq
    \\ once_rewrite_tac [heap_lookup_APPEND]
    \\ simp [heap_length_APPEND]
    \\ qpat_x_assum `_ = conf.refs_start` (fn th => simp [GSYM th]))
 \\ qabbrev_tac
       `gen_roots = to_gen_roots conf roots ++ refs_to_roots conf heap_refs`
  \\ qabbrev_tac
       `gen_heap = MAP (to_gen_heap_element conf) heap_current`
  \\ drule gen_gc_related
  \\ disch_then drule
  \\ fs []
  \\ strip_tac \\ fs []
  \\ pop_assum mp_tac
  \\ `!ptr u. MEM (Pointer ptr u) gen_roots ==> ptr IN FDOM f` by
       (fs [reachable_addresses_def,IN_DEF]
        \\ metis_tac [RTC_RULES])
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ pop_assum kall_tac
  \\ ntac 2 strip_tac
  \\ qexists_tac `new_f f conf heap`
  \\ fs [to_gen_heap_list_def]
  \\ rveq
  \\ drule partial_gc_heap_length_lemma
  \\ disch_then drule
  \\ fs []
  \\ strip_tac
  \\ strip_tac    (* (roots1 = ADDR_MAP ($' (new_f f conf heap)) roots) *)
  >- (fs [gc_related_def]
     \\ qunabbrev_tac `gen_roots`
     \\ fs [ADDR_MAP_APPEND]
     \\ qpat_x_assum `ADDR_MAP _ _ ++ _ = _` mp_tac
     \\ strip_tac
     \\ drule APPEND_LENGTH_IMP
     \\ impl_tac
     >- (fs [GSYM ADDR_MAP_LENGTH]
        \\ fs [to_gen_roots_def]
        \\ fs [partial_gc_def]
        \\ rfs []
        \\ pairarg_tac \\ fs []
        \\ pairarg_tac \\ fs []
        \\ drule gc_move_list_IMP
        \\ metis_tac [])
     \\ strip_tac
     \\ pop_assum kall_tac
     \\ pop_assum mp_tac
     \\ simp [to_gen_roots_def]
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
        \\ Cases_on `to_gen_heap_address conf h`
        \\ fs [ADDR_MAP_def])
     \\ reverse Cases
     >- (Cases \\ ntac 2 strip_tac
        >- (fs [to_gen_heap_address_def]
           \\ rpt (IF_CASES_TAC >- fs [ADDR_MAP_def])
           \\ fs [ADDR_MAP_def])
        \\ Cases_on `h`
        \\ fs [to_gen_heap_address_def,ADDR_MAP_def]
        >- (rpt (IF_CASES_TAC >- fs [ADDR_MAP_def])
           \\ fs [ADDR_MAP_def])
        \\ rpt strip_tac
        \\ rveq
        \\ drule roots_ok_CONS
        \\ strip_tac
        \\ fs [to_gen_roots_def]
        \\ metis_tac [])
     \\ Cases
     \\ ntac 2 strip_tac
     \\ fs [ADDR_MAP_def]
     \\ reverse (Cases_on `h`)
     >- (fs [to_gen_heap_address_def]
        \\ rpt (IF_CASES_TAC >- fs [ADDR_MAP_def])
        \\ fs [ADDR_MAP_def])
     \\ fs [to_gen_heap_address_def,new_f_def]
     \\ qpat_x_assum `!ptr u. _` mp_tac
     \\ simp [to_gen_roots_def] \\ strip_tac
     \\ rw []
     \\ drule roots_ok_CONS
     \\ fs [ADDR_MAP_def]
     \\ fs [FUNION_DEF]
     \\ fs [FUN_FMAP_DEF]
     >- (`n ∈ f_old_ptrs conf heap` by fs [f_old_ptrs_def,roots_ok_def]
        \\ fs []
        \\ metis_tac [to_gen_roots_def])
     >- (`n ∈ f_old_ptrs conf heap` by fs [f_old_ptrs_def,roots_ok_def]
        \\ fs []
        \\ metis_tac [to_gen_roots_def])
     \\ `~(n' ∈ f_old_ptrs conf heap)` by fs [f_old_ptrs_def,roots_ok_def]
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
        \\ fs [to_gen_roots_def,to_gen_heap_address_def]
        \\ metis_tac [])
     \\ fs []
     \\ strip_tac
     \\ fs [AND_IMP_INTRO]
     \\ first_x_assum match_mp_tac
     \\ fs []
     \\ rpt strip_tac
     \\ first_x_assum match_mp_tac
     \\ fs [to_gen_roots_def,to_gen_heap_address_def]
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
     \\ qunabbrev_tac `gen_roots`
     \\ fs [to_gen_roots_def]
     \\ fs [MEM_MAP]
     \\ qexists_tac `Real u`
     \\ disj1_tac
     \\ qexists_tac `Pointer ptr u`
     \\ fs []
     \\ fs [to_gen_heap_address_def])
  \\ `heap_ok (state1.old ++ state1.h1 ++ heap_expand state1.n ++ state1.r1) conf.limit` by (drule gen_gc_thm
     \\ disch_then drule
     \\ fs []
     \\ strip_tac
     \\ drule gen_gc_ok
     \\ disch_then drule
     \\ fs []
     \\ strip_tac
     \\ pop_assum mp_tac
     \\ simp [heap_ok_def]
     \\ strip_tac
     \\ fs [to_gen_conf_def]
     \\ strip_tac               (* heap_length *)
     >- (ntac 2 (first_x_assum kall_tac)
        \\ pop_assum mp_tac
        \\ drule heap_segment_IMP
        \\ fs [] \\ strip_tac \\ fs []
        \\ simp [heap_length_APPEND]
        \\ simp [to_gen_state_def]
        \\ drule partial_gc_IMP \\ fs []
        \\ strip_tac \\ fs []
        \\ fs [heap_length_heap_expand,heap_ok_def])
     \\ strip_tac               (* no ForwardPointers *)
     >- (fs [FILTER_APPEND]
        \\ pop_assum kall_tac
        \\ fs [to_gen_state_def]
        \\ drule FILTER_isForward_to_gen \\ strip_tac
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
        \\ fs [partial_gc_def] \\ rfs [] (*  *)
        \\ pairarg_tac \\ fs []
        \\ pairarg_tac \\ fs []
        \\ drule gc_move_data_IMP
        \\ strip_tac \\ fs []
        \\ rveq
        \\ fs []
        \\ drule gc_move_refs_isForwardPointer
        \\ impl_tac
        >- (fs [heap_ok_def]
           \\ drule heap_segment_IMP
           \\ fs []
           \\ strip_tac
           \\ qpat_x_assum `_ = heap` (assume_tac o GSYM)
           \\ fs []
           \\ fs [FILTER_APPEND])
        \\ fs [])
     \\ rpt gen_tac
     \\ strip_tac
     (* MEM old *)
     >- (drule partial_gc_IMP
        \\ fs [] \\ strip_tac \\ fs []
        \\ qpat_x_assum `heap_ok _ _` kall_tac
        \\ qpat_x_assum `heap_ok _ _` mp_tac
        \\ simp [heap_ok_def]
        \\ strip_tac
        \\ drule heap_segment_IMP \\ simp [] \\ strip_tac
        \\ rveq
        \\ qpat_x_assum `!xs l d ptr u. MEM _ _ /\ _ ==> _` drule
        \\ disch_then drule
        \\ strip_tac
        >- (qpat_x_assum `!xs. _` mp_tac
           \\ rewrite_tac [GSYM APPEND_ASSOC]
           \\ simp [heap_lookup_APPEND]
           \\ disch_then (qspecl_then [`xs`,`l`,`d`,`ptr`,`u`] mp_tac)
           \\ simp [])
        \\ qpat_x_assum `!xs l d ptr u. _` (qspecl_then [`xs`,`l`,`d`,`ptr`,`u`] mp_tac)
        \\ simp [MEM_APPEND]
        \\ once_rewrite_tac [heap_lookup_APPEND]
        \\ simp []
        \\ drule partial_gc_refs_isSomeDataElement_isSomeDataElement
        \\ disch_then drule
        \\ metis_tac [])
     (* MEM state1.h1 *)
     >- (`MEM (DataElement (MAP (to_gen_heap_address conf) xs) l d) (to_gen_state conf state1).h1` by (ntac 2 (pop_assum mp_tac)
           \\ simp [to_gen_state_def,to_gen_heap_list_def]
           \\ qspec_tac (`state1.h1`,`h1`)
           \\ Induct \\ fs []
           \\ Cases \\ fs [to_gen_heap_element_def]
           \\ strip_tac \\ rveq
           \\ fs []
           \\ metis_tac [])
        \\ drule partial_gc_IMP \\ fs [] \\ strip_tac \\ fs []
        \\ drule heap_segment_IMP \\ fs [] \\ strip_tac \\ rveq
        \\ qpat_x_assum `!xs' l' d' ptr' u'. (MEM _ state1.h1 \/ _) /\ _ ==> _` mp_tac
        \\ disch_then (qspecl_then [`xs`,`l`,`d`] mp_tac)
        \\ simp []
        \\ disch_then drule
        \\ once_rewrite_tac [heap_lookup_APPEND]
        \\ reverse IF_CASES_TAC \\ fs []
        \\ rewrite_tac [GSYM APPEND_ASSOC]
        \\ once_rewrite_tac [heap_lookup_APPEND]
        \\ IF_CASES_TAC \\ fs []
        \\ fs [to_gen_state_def]
        \\ qpat_x_assum `!xs. _` (qspecl_then [`MAP (to_gen_heap_address conf) xs`,`l`,`d`] mp_tac)
        \\ fs [] \\ strip_tac
        \\ qpat_x_assum `MEM (Pointer _ _) xs` mp_tac \\ simp [MEM_SPLIT]
        \\ strip_tac \\ rveq
        \\ qpat_x_assum `MEM _ _` mp_tac
        \\ qpat_x_assum `!ptr. _` mp_tac
        \\ simp [to_gen_heap_address_def]
        \\ ntac 2 strip_tac
        \\ rfs []
        \\ fs []
        \\ qpat_x_assum `!ptr. _` (qspecl_then [`ptr - conf.gen_start`,`Real u`] assume_tac)
        \\ fs []
        \\ drule isSomeData_to_gen_heap_IMP_isSomeData \\ fs [])
     >- (fs [heap_expand_def] \\ Cases_on `state1.n` \\ fs [])
     (* MEM state1.r1 *)
     \\ qpat_x_assum `_ = ADDR_MAP _ _` (assume_tac o GSYM)
     \\ fs []
     \\ qpat_x_assum `roots_ok _ _` mp_tac
     \\ simp [to_gen_state_def] \\ strip_tac
     \\ qunabbrev_tac `gen_roots`
     \\ qpat_x_assum `!xs' l' d' ptr' u'. (MEM _ state1.h1 \/ _) /\ _ ==> _` mp_tac
     \\ disch_then (qspecl_then [`xs`,`l`,`d`] mp_tac) \\ simp []
     \\ disch_then drule
     \\ drule partial_gc_IMP \\ fs [] \\ strip_tac \\ fs []
     \\ drule heap_segment_IMP \\ fs [] \\ strip_tac \\ rveq
     \\ once_rewrite_tac [heap_lookup_APPEND]
     \\ reverse IF_CASES_TAC \\ fs []
     \\ rewrite_tac [GSYM APPEND_ASSOC]
     \\ once_rewrite_tac [heap_lookup_APPEND]
     \\ IF_CASES_TAC \\ fs []
     \\ drule roots_ok_APPEND
     \\ strip_tac
     \\ drule refs_root_IMP_isSomeData \\ simp [])
  \\ fs []
  \\ fs [gc_related_def]
  \\ `∀i. i ∈ FDOM f ⇒ isSomeDataElement (heap_lookup (i + conf.gen_start) heap)` by (rpt strip_tac
     \\ res_tac
     \\ qunabbrev_tac `gen_heap`
     \\ drule heap_segment_IMP
     \\ fs [] \\ strip_tac
     \\ rveq
     \\ rewrite_tac [GSYM APPEND_ASSOC]
     \\ once_rewrite_tac [heap_lookup_APPEND]
     \\ IF_CASES_TAC
     >- decide_tac
     \\ fs []
     \\ once_rewrite_tac [heap_lookup_APPEND]
     \\ IF_CASES_TAC
     >- (qpat_x_assum `isSomeDataElement _` mp_tac
        \\ fs [heap_lookup_to_gen_heap_element])
     \\ fs [heap_lookup_to_gen_heap_element]
     \\ fs [heap_lookup_GT_FALSE])
  \\ strip_tac
  (* INJ new_f *)
  >- (fs [INJ_DEF] \\ strip_tac
     >- (fs [new_f_FAPPLY]
        \\ fs [new_f_FDOM]
        \\ rpt strip_tac
        \\ Cases_on `x < conf.gen_start` \\ fs []
        >- (drule heap_lookup_old_IMP_ALT
           \\ fs [isSomeDataElement_def,gen_inv_def]
           \\ metis_tac [GSYM APPEND_ASSOC])
        \\ IF_CASES_TAC \\ fs []
        >- (drule heap_lookup_refs_IMP_ALT
           \\ fs [gen_inv_def]
           \\ impl_tac \\ fs []
           \\ metis_tac [])
        \\ `(to_gen_state conf state1).r1 = []` by EVAL_TAC
        \\ fs []
        \\ qpat_x_assum `!x'. x' IN FDOM f ==> _` mp_tac
        \\ qpat_x_assum `!x'. x' IN FDOM f ==> _` drule
        \\ strip_tac \\ strip_tac
        \\ drule heap_segment_IMP
        \\ fs [] \\ strip_tac \\ fs []
        \\ fs [to_gen_state_def]
        \\ simp []
        \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
        \\ once_rewrite_tac [heap_lookup_APPEND]
        \\ fs [heap_length_APPEND]
        \\ IF_CASES_TAC
        \\ drule partial_gc_IMP
        \\ fs [] \\ strip_tac
        \\ fs []
        \\ rewrite_tac [GSYM APPEND_ASSOC]
        \\ once_rewrite_tac [heap_lookup_APPEND]
        \\ IF_CASES_TAC
        >- (qpat_x_assum `isSomeDataElement (heap_lookup _ _)` mp_tac
           \\ unabbrev_all_tac
           (* \\ strip_tac *)
           (* \\ simp [isSomeDataElement_to_gen_heap_element] *)
           (* \\ simp [isSomeDataElement_def] *)
           \\ simp [Once isSomeDataElement_def]
           \\ strip_tac
           \\ qpat_x_assum `!i xs l d. i IN FDOM f /\ _ ==> _` drule
           \\ disch_then drule
           \\ rewrite_tac [heap_lookup_APPEND]
           \\ reverse IF_CASES_TAC
           >- (rewrite_tac [heap_expand_def] \\ Cases_on `state1.n` \\ simp [heap_lookup_def])
           \\ strip_tac
           \\ drule isSomeData_to_gen_heap_IMP
           \\ simp [])
        (* current heap *)
        \\ `heap_length (state1.h1 ++ heap_expand state1.n) = heap_length (to_gen_heap_list conf state1.h1 ++ heap_expand state1.n)` by (fs [heap_length_APPEND]
           \\ fs [heap_expand_def]
           \\ IF_CASES_TAC \\ fs []
           \\ fs [heap_length_def,el_length_def])
        \\ unabbrev_all_tac
        \\ qpat_x_assum `!i xs l d. i IN FDOM f /\ _ ==> _` drule
        \\ fs [isSomeDataElement_def]
        \\ rewrite_tac [Once heap_lookup_APPEND]
        \\ simp []
        \\ simp [heap_expand_def]
        \\ IF_CASES_TAC
        \\ fs [heap_lookup_def])
     \\ fs [new_f_FAPPLY]
     \\ fs [new_f_FDOM]
     \\ rpt gen_tac
     \\ IF_CASES_TAC \\ IF_CASES_TAC \\ fs []
     \\ TRY (rpt strip_tac \\ rveq \\ fs [] \\ NO_TAC)
     \\ unabbrev_all_tac
     \\ simp [isSomeDataElement_def]
     \\ strip_tac
     \\ fs []
     \\ rveq
     \\ strip_tac
     \\ rveq
     \\ rpt strip_tac
     \\ qpat_x_assum `!i. i IN FDOM f ==> _` kall_tac
     \\ qpat_x_assum `!i. i IN FDOM f ==> _` drule
     \\ simp [isSomeDataElement_def]
     \\ rpt strip_tac
     \\ first_x_assum drule
     \\ disch_then drule
     \\ strip_tac
     \\ pop_assum kall_tac
     \\ pop_assum mp_tac
     \\ simp []
     \\ fs [to_gen_state_def]
     \\ drule heap_segment_IMP
     \\ fs [] \\ strip_tac \\ rveq
     \\ `heap_length heap_current = conf.refs_start - conf.gen_start` by fs [heap_length_APPEND]
     \\ `heap_length (to_gen_heap_list conf state1.h1 ++ heap_expand state1.n) = conf.refs_start - conf.gen_start` by
        (drule gen_gc_thm
        \\ disch_then drule
        \\ fs [] \\ strip_tac \\ fs []
        \\ fs [gc_inv_def]
        \\ rewrite_tac [heap_length_APPEND]
        \\ rewrite_tac [heap_length_to_gen_heap_list]
        \\ asm_rewrite_tac []
        \\ rewrite_tac [heap_length_heap_expand]
        \\ simp []
        \\ simp [to_gen_conf_def])
     \\ match_mp_tac (heap_lookup_GT_FALSE |> SIMP_RULE std_ss [isSomeDataElement_def])
     \\ fs [])
  \\ strip_tac
  >- (fs [new_f_FDOM]
     \\ strip_tac
     \\ IF_CASES_TAC \\ fs []
     \\ strip_tac
     \\ metis_tac [])
  \\ rpt gen_tac
  \\ fs [new_f_FAPPLY]
  \\ fs [new_f_FDOM]
  \\ Cases_on `i < conf.gen_start` \\ fs []
  >- (strip_tac
     \\ drule heap_lookup_old_IMP
     \\ fs [gen_inv_def,GSYM PULL_FORALL,GSYM AND_IMP_INTRO]
     \\ fs [AND_IMP_INTRO]
     \\ impl_tac THEN1 metis_tac []
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
        \\ `x IN FDOM (new_f f conf heap)` by (fs [new_f_FDOM]
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
     >- (`MEM (DataElement xs l d) heap` by (drule heap_segment_IMP \\ fs []
           \\ rveq
           \\ metis_tac [MEM_APPEND])
        \\ fs [heap_ok_def] \\ metis_tac [])
     \\ fs []
     \\ qexists_tac `ptr - conf.gen_start`
     \\ fs []
     \\ res_tac \\ fs [])
  \\ Cases_on `conf.refs_start ≤ i` \\ fs []
  >- (
     strip_tac
     \\ once_rewrite_tac [heap_lookup_APPEND]
     \\ IF_CASES_TAC \\ fs []
     \\ `heap_lookup (i - conf.refs_start) heap_refs = SOME (DataElement xs l d)` by (drule heap_segment_IMP
        \\ fs [] \\ strip_tac
        \\ rveq
        \\ qpat_x_assum `heap_lookup i _ = _` mp_tac
        \\ once_rewrite_tac [heap_lookup_APPEND]
        \\ simp [heap_length_APPEND])
     \\ unabbrev_all_tac
     \\ drule partial_gc_IMP
     \\ simp []
     \\ strip_tac
     \\ drule ADDR_MAP_APPEND_LENGTH_IMP
     \\ simp [] \\ strip_tac
     \\ rpt (disch_then assume_tac)
     \\ fs [ADDR_MAP_APPEND]
     \\ `LIST_REL (similar_data conf) heap_refs state1.r1` by
      (rfs [partial_gc_def]
       \\ pairarg_tac \\ fs []
       \\ pairarg_tac \\ fs []
       \\ imp_res_tac gc_move_data_r1 \\ fs []
       \\ imp_res_tac gc_move_ref_list_similar
       \\ asm_rewrite_tac [] \\ fs[gc_move_data_with_refs']
       \\ rveq \\ fs[] \\ NO_TAC)
     \\ drule (GEN_ALL heap_lookup_similar_data_IMP)
     \\ rpt (disch_then drule)
     \\ strip_tac \\ fs []
     \\ reverse conj_asm2_tac THEN1
      (rpt strip_tac
       \\ qpat_x_assum `heap_ok heap conf.limit` mp_tac
       \\ simp [heap_ok_def]
       \\ imp_res_tac heap_lookup_IMP_MEM \\ fs []
       \\ strip_tac
       \\ pop_assum drule
       \\ disch_then drule \\ fs [METIS_PROVE [] ``b\/c<=>(~b==>c)``]
       \\ rpt strip_tac
       \\ qexists_tac `ptr - conf.gen_start` \\ fs []
       \\ first_x_assum match_mp_tac
       \\ qpat_x_assum `MEM _ heap_refs` mp_tac
       \\ qspec_tac (`heap_refs`,`heap_refs`)
       \\ Induct \\ fs [refs_to_roots_def]
       \\ strip_tac \\ Cases_on `DataElement xs l d = h` \\ rveq
       THEN1
        (fs [refs_to_roots_def,MEM_MAP]
         \\ qexists_tac `Real u` \\ fs [] \\ strip_tac
         \\ disj1_tac \\ qexists_tac `Pointer ptr u`  \\ fs []
         \\ fs [to_gen_heap_address_def])
       \\ fs [] \\ Cases_on `h`
       \\ fs [refs_to_roots_def] \\ metis_tac [])
     \\ `!ptr u. MEM (Pointer ptr u) xs ==>
                 ptr IN FDOM (new_f f conf heap)` by
      (rpt strip_tac \\ fs [new_f_FDOM] \\ first_x_assum drule \\ fs [] \\ NO_TAC)
     \\ pop_assum mp_tac
     \\ pop_assum kall_tac
     \\ pop_assum mp_tac
     \\ qspec_tac (`xs2`,`xs2`)
     \\ qspec_tac (`xs`,`xs`)
     \\ Induct THEN1 (Cases \\ fs [ADDR_MAP_def])
     \\ reverse Cases THEN1
      (Cases \\ fs [to_gen_heap_address_def,ADDR_MAP_def]
       \\ Cases_on `h` \\ fs [to_gen_heap_address_def,ADDR_MAP_def]
       \\ rw [] \\ fs [] \\ metis_tac [])
     \\ fs [to_gen_heap_address_def,ADDR_MAP_def]
     \\ IF_CASES_TAC \\ fs []
     THEN1
      (Cases \\ fs [ADDR_MAP_def]
       \\ Cases_on `h` \\ fs [to_gen_heap_address_def]
       \\ rw [] \\ fs []
       \\ `n IN FDOM (new_f f conf heap)` by metis_tac []
       \\ rpt strip_tac
       \\ drule (GEN_ALL new_f_old_parts) \\ fs []
       \\ TRY (disch_then drule)
       \\ metis_tac[])
     \\ IF_CASES_TAC \\ fs []
     THEN1
      (Cases \\ fs [ADDR_MAP_def]
       \\ Cases_on `h` \\ fs [to_gen_heap_address_def]
       \\ rw [] \\ fs []
       \\ `n IN FDOM (new_f f conf heap)` by metis_tac []
       \\ rpt strip_tac
       \\ drule (GEN_ALL new_f_old_parts) \\ fs []
       \\ TRY (disch_then drule)
       \\ metis_tac[])
     \\ Cases \\ fs [ADDR_MAP_def]
     \\ Cases_on `h` \\ fs [to_gen_heap_address_def]
     \\ reverse (rw [] \\ fs []) THEN1 metis_tac[]
     \\ `n IN FDOM (new_f f conf heap)` by metis_tac []
     \\ drule (GEN_ALL new_f_FAPPLY) \\ fs [])
  \\ strip_tac
  \\ rveq
  \\ fs []
  \\ fs [INJ_DEF]
  \\ qpat_x_assum `!i. i IN FDOM f ==> isSomeDataElement _` kall_tac
  \\ qpat_x_assum `!i. i IN FDOM f ==> isSomeDataElement _` drule
  \\ fs [isSomeDataElement_def]
  \\ strip_tac
  \\ first_x_assum drule
  \\ fs []
  \\ strip_tac
  \\ rewrite_tac [GSYM APPEND_ASSOC]
  \\ once_rewrite_tac [heap_lookup_APPEND]
  \\ `heap_length state1.old = conf.gen_start` by (drule partial_gc_IMP
     \\ disch_then drule
     \\ strip_tac
     \\ rveq
     \\ drule heap_segment_IMP
     \\ strip_tac \\ fs [])
  \\ fs []
  \\ fs [to_gen_state_def]
  \\ fs [to_gen_heap_list_def]
  \\ `(l = l') /\ (d = d') /\ (ys = MAP (to_gen_heap_address conf) xs)` by (rveq
     \\ qunabbrev_tac `gen_heap`
     \\ drule heap_segment_IMP
     \\ fs [] \\ strip_tac
     \\ rveq
     \\ qpat_x_assum `heap_lookup (x + conf.gen_start) _ = _` mp_tac
     \\ rewrite_tac [GSYM APPEND_ASSOC]
     \\ once_rewrite_tac [heap_lookup_APPEND]
     \\ fs []
     \\ qpat_x_assum `heap_lookup x _ = _` mp_tac
     \\ qspec_tac (`x`,`x`)
     \\ qspec_tac (`heap_current`,`heap`)
     \\ Induct
     >- fs [MAP,heap_lookup_def]
     \\ strip_tac
     \\ fs [heap_lookup_def]
     \\ strip_tac
     \\ IF_CASES_TAC \\ fs []
     >- (Cases_on `h` \\ fs [to_gen_heap_element_def]
        \\ rw [])
     \\ fs []
     \\ metis_tac [])
  \\ rveq
  \\ CONJ_TAC
  >- (fs [heap_ok_def]
     \\ ntac 4 (pop_assum mp_tac)
     \\ drule heap_lookup_IMP_MEM
     \\ strip_tac
     \\ ntac 4 strip_tac
     \\ drule heap_lookup_by_f_isSomeData_lemma
     \\ res_tac
     \\ disch_then drule
     \\ disch_then drule
     \\ fs [])
  \\ fs [heap_ok_def]
  \\ rpt strip_tac
  \\ IF_CASES_TAC
  >- (pop_assum mp_tac
     \\ fs []
     \\ imp_res_tac heap_lookup_IMP_MEM
     \\ res_tac
     \\ fs [isSomeDataElement_def])
  \\ qexists_tac `ptr - conf.gen_start`
  \\ fs []
  \\ first_x_assum match_mp_tac
  \\ qexists_tac `Real u`
  \\ qpat_x_assum `MEM _ _` mp_tac
  \\ simp [Once MEM_SPLIT]
  \\ strip_tac
  \\ fs []
  \\ simp [to_gen_heap_address_def]
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

Theorem gc_move_ref_list_length:
    !xs xs' state state'.
       (gc_move_ref_list conf state xs = (xs',state')) ==>
       (LENGTH xs' = LENGTH xs)
Proof
  Induct THEN1 fs [gc_move_ref_list_def]
  \\ Cases \\ fs [gc_move_ref_list_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ res_tac \\ fs []
QED

Theorem gc_move_ref_list_heap_length':
    !xs xs' state state'.
       (gc_move_ref_list conf state xs = (xs',state')) ==>
       (heap_length xs' = heap_length xs)
Proof
  Induct THEN1 fs [gc_move_ref_list_def]
  \\ Cases \\ fs [gc_move_ref_list_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ res_tac \\ fs [heap_length_def,el_length_def]
QED

val has_bad_ref_def = Define `
  has_bad_ref c s <=>
    (?xs l d. MEM (DataElement xs l d) (s.h1 ++ s.h2) /\ c.isRef d)
    \/
    ?xs l d n.
      c.gen_start <= n /\ n < c.refs_start /\
      (heap_lookup n s.heap = SOME (DataElement xs l d)) /\ c.isRef d`;

val balanced_state_def = Define `
  balanced_state c s <=>
    (heap_length (FILTER isForwardPointer s.heap)
     = heap_length s.h1 + heap_length s.h2) /\
    (case heap_segment (c.gen_start, c.refs_start) s.heap of
     | NONE => F
     | SOME (old,curr,refs) =>
        heap_length (FILTER isDataElement s.r1) +
        heap_length (FILTER isDataElement s.r2) +
        heap_length (FILTER isDataElement s.old) <=
        heap_length (FILTER isDataElement old) +
        heap_length (FILTER isDataElement refs))`

val simple_rel_def = Define `
  simple_rel c s1 s2 <=>
    (s2.old = s1.old) /\
    (heap_length (s2.h1 ++ s2.h2 ++ heap_expand s2.n) =
     heap_length (s1.h1 ++ s1.h2 ++ heap_expand s1.n)) /\
    ((s1.a = c.gen_start + heap_length s1.h1 + heap_length s1.h2) ==>
     (s2.a = c.gen_start + heap_length s2.h1 + heap_length s2.h2)) /\
    (EVERY isDataElement s1.h1 ==> EVERY isDataElement s2.h1) /\
    (heap_length (FILTER isDataElement s1.heap ++ s1.h1 ++ s1.h2) =
     heap_length (FILTER isDataElement s2.heap ++ s2.h1 ++ s2.h2)) /\
    (heap_length (FILTER isForwardPointer s1.heap) +
     heap_length (FILTER isDataElement s1.heap) =
     heap_length (FILTER isForwardPointer s2.heap) +
     heap_length (FILTER isDataElement s2.heap)) /\
    (balanced_state c s1 ==> balanced_state c s2) /\
    (has_bad_ref c s2 ==> has_bad_ref c s1)`;

val simple_rel_refl = prove(
  ``simple_rel c x x``,
  fs [simple_rel_def]);

val simple_rel_trans = prove(
  ``simple_rel c x1 x2 /\ simple_rel c x2 x3 ==> simple_rel c x1 x3``,
  fs [simple_rel_def]);

val gc_forward_ptr_lookup_DataElement = prove(
  ``!hs n x a heap n1.
      (gc_forward_ptr n hs x a T = (heap,T)) /\
      (heap_lookup n1 heap = SOME (DataElement xs l' d)) ==>
      (heap_lookup n1 hs = SOME (DataElement xs l' d))``,
  Induct \\ fs [gc_forward_ptr_def]
  \\ rpt gen_tac \\ IF_CASES_TAC \\ fs []
  THEN1
   (rw [] \\ fs [heap_lookup_def]
    \\ rw [] \\ fs [] \\ fs [el_length_def]
    \\ `0 < el_length h` by
         (Cases_on `h` \\ fs [el_length_def]) \\ fs [])
  \\ IF_CASES_TAC \\ fs [] \\ pairarg_tac \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ fs [heap_lookup_def] \\ rw [] \\ fs []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ asm_exists_tac \\ fs []);

val gc_forward_ptr_APPEND = prove(
  ``!x0 n a1 a x1 heap1.
      (gc_forward_ptr n (x0 ++ x1) a1 a T = (heap1,T)) ==>
      if n < heap_length x0 then
        ?y0. (gc_forward_ptr n x0 a1 a T = (y0,T)) /\
             (heap1 = y0 ++ x1)
      else
        ?y1. (gc_forward_ptr (n - heap_length x0) x1 a1 a T = (y1,T)) /\
             (heap1 = x0 ++ y1)``,
  Induct \\ fs [gc_forward_ptr_def]
  \\ rpt gen_tac
  \\ Cases_on `n = 0` \\ fs []
  THEN1 (Cases_on `h` \\ fs [heap_length_def,el_length_def])
  \\ IF_CASES_TAC \\ fs []
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ first_x_assum drule
  \\ fs [heap_length_def]
  \\ Cases_on `n < SUM (MAP el_length x0) + el_length h` \\ fs []
  \\ strip_tac \\ fs []);

val gc_forward_ptr_APPEND_APPEND = prove(
  ``(gc_forward_ptr n (x0 ++ x1 ++ x2) a1 a T = (heap1,T)) /\
    heap_length x0 ≤ n /\  n < heap_length (x0 ++ x1) ==>
    ?y. (heap1 = x0 ++ y ++ x2) /\ (heap_length y = heap_length x1)``,
  strip_tac
  \\ drule gc_forward_ptr_APPEND
  \\ fs [heap_length_APPEND] \\ strip_tac \\ rveq
  \\ drule gc_forward_ptr_APPEND \\ fs [] \\ strip_tac \\ rveq
  \\ imp_res_tac gc_forward_ptr_heap_length
  \\ fs [heap_length_APPEND]);

val heap_segment_gc_forward_ptr = prove(
  ``(heap_segment (k,l) heap = SOME (x0,x1,x2)) /\
    (gc_forward_ptr n heap a1 a T = (heap1,T)) /\
    k <= n /\ n < l ==>
    ?y. (heap_segment (k,l) heap1 = SOME (x0,y,x2))``,
  strip_tac
  \\ drule heap_segment_IMP \\ strip_tac \\ fs []
  \\ rveq \\ fs []
  \\ drule gc_forward_ptr_APPEND_APPEND \\ fs []
  \\ strip_tac \\ fs []
  \\ simp [heap_segment_def]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,heap_split_APPEND_if]
  \\ fs [heap_split_0,heap_length_APPEND]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,heap_split_APPEND_if]
  \\ fs []);

Theorem gc_move_inv:
    !xs xs' s1 s2.
       (gc_move c s1 xs = (xs',s2)) /\ s2.ok ==>
       simple_rel c s1 s2
Proof
  Cases \\ fs [gc_move_def,simple_rel_def]
  \\ rpt gen_tac \\ every_case_tac \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ TRY (fs [has_bad_ref_def,balanced_state_def] \\ NO_TAC)
  \\ pairarg_tac \\ fs []
  \\ rveq \\ fs [] \\ rfs []
  \\ imp_res_tac gc_forward_ptr_ok \\ fs []
  \\ fs [heap_length_APPEND,heap_length_heap_expand]
  \\ fs [heap_length_def,el_length_def]
  \\ rpt (conj_tac THEN1
   (drule heap_lookup_SPLIT \\ strip_tac \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ fs [gc_forward_ptr_thm] \\ rveq \\ fs []
    \\ fs [FILTER_APPEND,isDataElement_def,el_length_def,
           SUM_APPEND,isForwardPointer_def]))
  \\ conj_tac
  THEN1
   (fs [balanced_state_def,heap_length_def,SUM_APPEND,el_length_def] \\ rw []
    THEN1
     (drule heap_lookup_SPLIT \\ strip_tac \\ fs []
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ fs [gc_forward_ptr_thm] \\ rveq \\ fs []
      \\ fs [balanced_state_def,heap_length_def,SUM_APPEND,el_length_def,
             FILTER_APPEND,isDataElement_def,isForwardPointer_def])
    \\ pop_assum mp_tac \\ TOP_CASE_TAC
    \\ fs [GSYM NOT_LESS] \\ fs [NOT_LESS]
    \\ PairCases_on `x` \\ fs []
    \\ drule (GEN_ALL heap_segment_gc_forward_ptr)
    \\ disch_then drule \\ fs []
    \\ strip_tac \\ fs [])
  \\ fs [has_bad_ref_def]
  \\ strip_tac
  THEN1 metis_tac []
  THEN1 metis_tac []
  THEN1 metis_tac []
  \\ CCONTR_TAC \\ fs [GSYM IMP_DISJ_THM]
  \\ pop_assum drule \\ fs []
  \\ drule (GEN_ALL gc_forward_ptr_lookup_DataElement)
  \\ disch_then drule \\ fs []
QED

Theorem gc_move_list_inv:
    !xs xs' s1 s2.
       (gc_move_list c s1 xs = (xs',s2)) /\ s2.ok ==>
       simple_rel c s1 s2
Proof
  Induct THEN1 (fs [gc_move_list_def,simple_rel_def])
  \\ fs [gc_move_list_def]
  \\ rpt gen_tac \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ strip_tac \\ rveq
  \\ imp_res_tac gc_move_list_ok'
  \\ drule gc_move_inv \\ fs []
  \\ strip_tac
  \\ res_tac \\ fs []
  \\ imp_res_tac simple_rel_trans
QED

Theorem gc_move_ref_list_inv:
    !xs xs' s1 s2.
       (gc_move_ref_list c s1 xs = (xs',s2)) /\ s2.ok ==>
       simple_rel c s1 s2
Proof
  Induct THEN1 (fs [gc_move_ref_list_def,simple_rel_def])
  \\ fs [gc_move_ref_list_def]
  \\ rpt gen_tac \\ every_case_tac \\ fs []
  \\ Cases_on `h` \\ fs [gc_move_ref_list_def]
  \\ strip_tac \\ rveq \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ imp_res_tac gc_move_ref_list_ok'
  \\ drule gc_move_list_inv \\ fs []
  \\ strip_tac \\ res_tac \\ fs []
  \\ imp_res_tac simple_rel_trans
QED

Theorem gc_move_data_inv:
    !c s1 s2.
       (gen_gc_partial$gc_move_data c s1 = s2) /\ s2.ok ==>
       simple_rel c s1 s2
Proof
  recInduct (fetch "-" "gc_move_data_ind")
  \\ rpt gen_tac \\ strip_tac
  \\ once_rewrite_tac [gc_move_data_def]
  \\ rpt (TOP_CASE_TAC \\ fs [simple_rel_refl])
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ fs [] \\ rfs []
  \\ imp_res_tac (SIMP_RULE std_ss [] gc_move_data_ok')
  \\ fs [] \\ drule gc_move_list_inv
  \\ qmatch_assum_abbrev_tac `simple_rel _ t1 t2`
  \\ fs [] \\ strip_tac
  \\ Cases_on `state'.h2` \\ fs [] \\ rveq
  \\ qsuff_tac `simple_rel conf state' t1`
  THEN1
   (strip_tac
    \\ match_mp_tac (GEN_ALL simple_rel_trans) \\ asm_exists_tac \\ fs []
    \\ match_mp_tac (GEN_ALL simple_rel_trans) \\ asm_exists_tac \\ fs [])
  \\ fs [simple_rel_def]
  \\ qunabbrev_tac `t1` \\ fs []
  \\ fs [heap_length_def,el_length_def,SUM_APPEND,isDataElement_def]
  \\ fs [GSYM heap_length_def,heap_length_heap_expand]
  \\ conj_tac THEN1
    (fs [balanced_state_def,heap_length_def,el_length_def,SUM_APPEND])
  \\ simp [has_bad_ref_def] \\ metis_tac []
QED

Theorem LIST_REL_similar_data_IMP:
   !xs ys. LIST_REL (similar_data cc) xs ys ==>
            (heap_length xs = heap_length ys) /\
            (heap_length (FILTER isDataElement xs) =
             heap_length (FILTER isDataElement ys))
Proof
  Induct \\ Cases_on `ys` \\ fs [heap_length_def]
  \\ rw[] \\ res_tac \\ fs []
  \\ Cases_on `h` \\ Cases_on `h'` \\ fs [similar_data_def,isDataElement_def]
  \\ rveq \\ fs [] \\ fs [el_length_def]
QED

Theorem partial_gc_IMP:
   (partial_gc c (roots,heap) = (roots1,state1)) /\ state1.ok ==>
    (state1.a = c.gen_start + heap_length state1.h1) /\
    (LENGTH roots1 = LENGTH roots) /\
    (heap_length state1.old = c.gen_start) /\
    (heap_length (state1.old ++ state1.h1 ++ heap_expand state1.n) =
     c.refs_start) /\
    ((FILTER isForwardPointer heap = []) ==>
     heap_length (FILTER isDataElement (state1.old ++ state1.h1 ++ state1.r1)) <=
     heap_length (FILTER isDataElement heap)) /\
    EVERY isDataElement state1.h1 /\
    ?curr refs. (heap_segment (c.gen_start, c.refs_start) heap =
                   SOME (state1.old,curr,refs)) /\
                EVERY2 (similar_data c) refs state1.r1 /\
                (!xs l d. MEM (DataElement xs l d) state1.h1 /\
                          c.isRef d ==>
                          ?xs l d. MEM (DataElement xs l d) curr /\ c.isRef d)
Proof
  fs [partial_gc_def] \\ CASE_TAC \\ fs []
  THEN1 (CCONTR_TAC \\ rw [] \\ fs [] \\ rveq \\ fs [])
  \\ CASE_TAC \\ CASE_TAC
  \\ rpt (pairarg_tac \\ fs []) \\ strip_tac \\ rveq \\ fs []
  \\ `?s4. gc_move_data c (state' with <|r2 := []; r1 := refs'|>) = s4` by fs []
  \\ fs [] \\ rename1 `_ = SOME (old,curr,refs)`
  \\ `s4.r1 = refs'` by (rveq \\ fs [gc_move_data_r1] \\ NO_TAC) \\ fs []
  \\ drule gc_move_ref_list_similar \\ fs [] \\ disch_then assume_tac
  \\ drule gc_move_list_length \\ fs [] \\ disch_then kall_tac
  \\ drule gc_move_data_inv \\ fs []
  \\ drule gc_move_data_ok' \\ fs [] \\ strip_tac
  \\ drule gc_move_ref_list_inv \\ fs []
  \\ drule gc_move_ref_list_ok' \\ fs [] \\ strip_tac
  \\ drule gc_move_list_inv \\ fs []
  \\ strip_tac
  \\ qmatch_assum_abbrev_tac `simple_rel c t1 _`
  \\ rpt (disch_then assume_tac)
  \\ `(state'.r1 = []) /\ (state'.r2 = refs)` by
   (drule gc_move_list_IMP \\ drule gc_move_ref_list_IMP
    \\ unabbrev_all_tac \\ fs [empty_state_def] \\ NO_TAC)
  \\ `simple_rel c t1 s4` by
   (rpt (match_mp_tac (GEN_ALL simple_rel_trans) \\ asm_exists_tac \\ fs [])
    \\ rpt (match_mp_tac (GEN_ALL simple_rel_trans |> ONCE_REWRITE_RULE [CONJ_COMM])
            \\ asm_exists_tac \\ fs [])
    \\ simp [simple_rel_def,has_bad_ref_def,balanced_state_def]
    \\ drule LIST_REL_similar_data_IMP \\ fs [] \\ NO_TAC)
  \\ pop_assum mp_tac
  \\ rpt (qpat_x_assum `simple_rel _ _ _` kall_tac) \\ strip_tac
  \\ fs [simple_rel_def]
  \\ fs [heap_length_def,SUM_APPEND]
  \\ fs [GSYM heap_length_def,heap_length_heap_expand]
  \\ qpat_x_assum `s4.r1 = refs'` (assume_tac o GSYM)
  \\ imp_res_tac heap_segment_IMP \\ fs []
  \\ rveq \\ fs []
  \\ `s4.h2 = []` by metis_tac [gc_move_data_h2]
  \\ rfs [empty_state_def]
  \\ fs [] \\ qunabbrev_tac `t1` \\ fs []
  \\ fs [heap_length_def,SUM_APPEND]
  \\ fs [GSYM heap_length_def,heap_length_heap_expand]
  \\ reverse (rpt strip_tac) THEN1
   (`has_bad_ref c s4` by
         (fs [has_bad_ref_def] \\ disj1_tac \\ asm_exists_tac \\ fs [] \\ NO_TAC)
    \\ qpat_x_assum `has_bad_ref c _ ==> _` mp_tac
    \\ impl_tac THEN1 fs []
    \\ simp [has_bad_ref_def]
    \\ strip_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ full_simp_tac std_ss [heap_lookup_APPEND]
    \\ rfs [] \\ imp_res_tac heap_lookup_MEM
    \\ asm_exists_tac \\ fs [])
  \\ `heap_length (FILTER isDataElement (old ++ curr ++ state'.r2)) =
      heap_length (FILTER isDataElement s4.heap) +
      heap_length (FILTER isForwardPointer s4.heap)` by (fs [] \\ NO_TAC)
  \\ fs [heap_length_def,SUM_APPEND]
  \\ fs [GSYM heap_length_def,heap_length_heap_expand]
  \\ fs [FILTER_APPEND,heap_length_APPEND]
  \\ qpat_x_assum `_ = heap_length curr` (assume_tac o GSYM) \\ fs []
  \\ qpat_x_assum `_ = heap_length s4.h1 + heap_length (FILTER _ _)`
       (fn th => fs [GSYM th] \\ assume_tac (GSYM th)) \\ fs []
  \\ drule LIST_REL_similar_data_IMP \\ fs []
  \\ disch_then kall_tac
  \\ fs [GSYM FILTER_EQ_ID]
  \\ drule (DECIDE ``(m = n1+n2:num) ==> (n2 = m - n1)``)
  \\ simp_tac std_ss []
  \\ disch_then kall_tac \\ fs []
  \\ `balanced_state c s4` by
    (first_x_assum match_mp_tac \\ simp [balanced_state_def,FILTER_APPEND]
     \\ NO_TAC)
  \\ fs [balanced_state_def] \\ rfs []
  \\ qpat_x_assum `_ = heap_length s4.h1` (fn th => fs [GSYM th])
  \\ match_mp_tac (DECIDE ``!k. k+n<=m+k:num ==> n<=m``)
  \\ qexists_tac `heap_length (FILTER isDataElement s4.heap)`
  \\ `s4.r2 = []` by
   (drule gc_move_ref_list_IMP \\ fs []
    \\ drule gc_move_list_IMP \\ fs []
    \\ drule gc_move_data_IMP \\ fs [])
  \\ asm_rewrite_tac [] \\ fs [] \\ rfs []
  \\ every_case_tac \\ fs []
  \\ drule heap_segment_IMP
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ strip_tac \\ fs [FILTER_APPEND,heap_length_APPEND]
QED

val _ = export_theory();
