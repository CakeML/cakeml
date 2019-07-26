(*
  The straightforward non-generational copying garbage collector.
*)
open preamble gc_sharedTheory wordsTheory wordsLib integer_wordTheory;

val _ = new_theory "copying_gc";

val _ = ParseExtras.temp_loose_equality();

(* The GC is a copying collector which moves elements *)

val gc_move_def = Define `
  (gc_move (Data d,h2,a,n,heap,c,limit) = (Data d,h2,a,n,heap,c)) /\
  (gc_move (Pointer ptr d,h2,a,n,heap,c,limit) =
     case heap_lookup ptr heap of
     | SOME (DataElement xs l dd) =>
         let c = c /\ l+1 <= n /\ (a + n = limit) in
         let n = n - (l+1) in
         let h2 = h2 ++ [DataElement xs l dd] in
         let (heap,c) = gc_forward_ptr ptr heap a d c in
           (Pointer a d,h2,a + (l+1),n,heap,c)
     | SOME (ForwardPointer ptr _ l) => (Pointer ptr d,h2,a,n,heap,c)
     | _ => (ARB,h2,a,n,heap,F))`

val gc_move_list_def = Define `
  (gc_move_list ([],h2,a,n,heap,c,limit) = ([],h2,a,n,heap,c)) /\
  (gc_move_list (x::xs,h2,a,n,heap,c,limit) =
     let (x,h2,a,n,heap,c) = gc_move (x,h2,a,n,heap,c,limit) in
     let (xs,h2,a,n,heap,c) = gc_move_list (xs,h2,a,n,heap,c,limit) in
       (x::xs,h2,a,n,heap,c))`;

val gc_move_loop_def = tDefine "gc_move_loop" `
  (gc_move_loop (h1,[],a,n,heap,c,limit) = (h1,a,n,heap,c)) /\
  (gc_move_loop (h1,h::h2,a,n,heap,c,limit) =
     if limit < heap_length (h1 ++ h::h2) then (h1,a,n,heap,F) else
       case h of
       | DataElement xs l d =>
          let (xs,h2,a,n,heap,c) = gc_move_list (xs,h::h2,a,n,heap,c,limit) in
          let c = c /\ h2 <> [] /\ (HD h2 = h) in
          let h2 = TL h2 in
          let h1 = h1 ++ [DataElement xs l d] in
            gc_move_loop (h1,h2,a,n,heap,c,limit)
       | _ => (h1,a,n,heap,F))`
  (WF_REL_TAC `measure (\(h1,h2,a,n,heap,c,limit). limit - heap_length h1)`
   \\ SRW_TAC [] [heap_length_def,el_length_def,SUM_APPEND] \\ decide_tac);

val full_gc_def = Define `
  full_gc (roots,heap,limit) =
    let c0 = (heap_length heap = limit) in
    let (roots,h2,a,n,heap,c) = gc_move_list (roots,[],0,limit,heap,T,limit) in
    let (heap,a,n,temp,c) = gc_move_loop ([],h2,a,n,heap,c,limit) in
    let c = (c /\ (a = heap_length heap) /\ (heap_length temp = limit) /\
             c0 /\ (n = limit - a) /\ a <= limit) in
      (roots,heap,a,c)`;

(* Invariant *)

val _ = augment_srw_ss [rewrites [LIST_REL_def]];

val gc_inv_def = Define `
  gc_inv (h1,h2,a,n,heap,c,limit) (heap0:('a, 'b) heap_element list)
                                  (roots0:'a heap_address list) =
    (a + n = limit) /\
    (a = heap_length (h1 ++ h2)) /\
    (n = heap_length (FILTER (\h. ~(isForwardPointer h)) heap)) /\ c /\
    (heap_length heap = limit) /\
    (* the initial heap is well-formed *)
    heap_ok heap0 limit /\
    (* the initial heap is related to the current heap *)
    heaps_similar heap0 heap /\
    (* the new heap consists of only DataElements *)
    EVERY isDataElement h1 /\ EVERY isDataElement h2 /\
    (* the forward pointers consitute a bijection into the new heap *)
    BIJ (heap_map1 heap) (FDOM (heap_map 0 heap)) (heap_addresses 0 (h1 ++ h2)) /\
    !i j. (FLOOKUP (heap_map 0 heap) i = SOME j) ==>
          ?xs l d. (heap_lookup i heap0 = SOME (DataElement xs l d)) /\
                   (heap_lookup j (h1++h2) =
                     SOME (DataElement (if j < heap_length h1 then
                                          ADDR_MAP (heap_map1 heap) xs else xs) l d)) /\
                   reachable_addresses roots0 heap0 i /\
                   !ptr d. MEM (Pointer ptr d) xs /\ j < heap_length h1 ==>
                           ptr IN FDOM (heap_map 0 heap)`;

(* Invariant maintained *)

val DRESTRICT_heap_map = Q.prove(
  `!heap k. n < k ==> (DRESTRICT (heap_map k heap) (COMPL {n}) = heap_map k heap)`,
  simp_tac (srw_ss()) [GSYM fmap_EQ_THM,DRESTRICT_DEF,EXTENSION] \\ rpt strip_tac
  \\ Cases_on `x IN FDOM (heap_map k heap)` \\ full_simp_tac std_ss []
  \\ rpt (pop_assum mp_tac)  \\ Q.SPEC_TAC (`k`,`k`) \\ Q.SPEC_TAC (`heap`,`heap`)
  \\ Induct \\ full_simp_tac (srw_ss()) [heap_map_def]
  \\ Cases \\ full_simp_tac (srw_ss()) [heap_map_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss []
  \\ metis_tac [DECIDE ``n<k ==> n < k + m:num``,DECIDE ``n<k ==> n < k + m+1:num``]);

val IN_FRANGE = Q.prove(
  `!heap n. MEM (ForwardPointer ptr d l) heap ==> ptr IN FRANGE (heap_map n heap)`,
  Induct \\ full_simp_tac std_ss [MEM] \\ rpt strip_tac
  \\ Cases_on `h` \\ full_simp_tac (srw_ss()) [heap_map_def,FRANGE_FUPDATE]
  \\ `n < n + n0 + 1` by decide_tac \\ full_simp_tac std_ss [DRESTRICT_heap_map]);

val heap_addresses_SNOC = Q.prove(
  `!xs n x.
      heap_addresses n (xs ++ [x]) =
      heap_addresses n xs UNION {heap_length xs + n}`,
  Induct \\ full_simp_tac (srw_ss()) [heap_addresses_def,APPEND,heap_length_def]
  \\ full_simp_tac (srw_ss()) [EXTENSION] \\ rpt strip_tac
  \\ full_simp_tac std_ss [AC ADD_COMM ADD_ASSOC,DISJ_ASSOC]);

val NOT_IN_heap_addresses = Q.prove(
  `!xs n. ~(n + heap_length xs IN heap_addresses n xs)`,
  Induct \\ full_simp_tac (srw_ss()) [heap_addresses_def,APPEND,heap_length_def]
  \\ full_simp_tac (srw_ss()) [EXTENSION] \\ rpt strip_tac
  \\ full_simp_tac std_ss [ADD_ASSOC]
  THEN1 (Cases_on `h` \\ EVAL_TAC \\ decide_tac) \\ metis_tac [])
  |> Q.SPECL [`xs`,`0`] |> SIMP_RULE std_ss [];

val gc_move_thm = Q.prove(
  `gc_inv (h1,h2,a,n,heap:('a,'b) heap_element list,c,limit) heap0 roots0 /\
    (!ptr u. (x = Pointer ptr u) ==> isSomeDataOrForward (heap_lookup ptr heap) /\
                                     reachable_addresses roots0 heap0 ptr) ==>
    ?x3 h23 a3 n3 heap3 c3.
      (gc_move (x:'a heap_address,h2,a,n,heap,c,limit) = (ADDR_APPLY (heap_map1 heap3) x,h23,a3,n3,heap3,c3)) /\
      (!ptr u. (x = Pointer ptr u) ==> ptr IN FDOM (heap_map 0 heap3)) /\
      (!ptr. isSomeDataOrForward (heap_lookup ptr heap) =
             isSomeDataOrForward (heap_lookup ptr heap3)) /\
      ((heap_map 0 heap) SUBMAP (heap_map 0 heap3)) /\
      gc_inv (h1,h23,a3,n3,heap3,c3,limit) heap0 roots0`,
  Cases_on `x` \\ simp_tac (srw_ss()) [gc_move_def,ADDR_APPLY_def]
  \\ simp_tac std_ss [Once isSomeDataOrForward_def] \\ rpt strip_tac
  \\ full_simp_tac (srw_ss()) [isSomeForwardPointer_def] THEN1
   (full_simp_tac (srw_ss()) [ADDR_APPLY_def] \\ imp_res_tac heap_lookup_FLOOKUP
    \\ full_simp_tac std_ss [FLOOKUP_DEF,heap_map1_def])
  \\ full_simp_tac (srw_ss()) [isSomeDataElement_def,LET_DEF]
  \\ imp_res_tac heap_lookup_SPLIT \\ full_simp_tac std_ss []
  \\ full_simp_tac (srw_ss()) [gc_forward_ptr_thm]
  \\ `heap_map 0 (ha ++ [ForwardPointer a a' l] ++ hb) =
      heap_map 0 (ha ++ DataElement ys l d::hb) |+ (heap_length ha,a)` by
   (once_rewrite_tac [GSYM (EVAL ``[x] ++ xs``)]
    \\ simp_tac std_ss [APPEND_NIL,APPEND_ASSOC]
    \\ full_simp_tac std_ss [heap_map_APPEND]
    \\ full_simp_tac (srw_ss()) [heap_length_def,el_length_def]
    \\ full_simp_tac (srw_ss()) [heap_map_def,SUM_APPEND]
    \\ full_simp_tac (srw_ss()) [GSYM fmap_EQ_THM,heap_map_APPEND]
    \\ full_simp_tac (srw_ss()) [EXTENSION] \\ strip_tac THEN1 metis_tac []
    \\ full_simp_tac (srw_ss()) [FUNION_DEF,FAPPLY_FUPDATE_THM] \\ strip_tac
    \\ Cases_on `x = SUM (MAP el_length ha)` \\ full_simp_tac std_ss []
    \\ full_simp_tac std_ss [GSYM heap_length_def]
    \\ full_simp_tac std_ss [FDOM_heap_map])
  \\ `~(heap_length ha IN FDOM (heap_map 0 (ha ++ DataElement ys l d::hb)))`
       by full_simp_tac std_ss [NOT_IN_heap_map]
  \\ strip_tac THEN1 (full_simp_tac (srw_ss()) [heap_map1_def])
  \\ strip_tac THEN1 (full_simp_tac (srw_ss()) [])
  \\ strip_tac THEN1 metis_tac [isSomeDataOrForward_lemma]
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [SUBMAP_DEF,FAPPLY_FUPDATE_THM]
    \\ SRW_TAC [] [] \\ full_simp_tac std_ss [])
  \\ full_simp_tac std_ss [gc_inv_def,heap_map1_def]
  \\ Q.ABBREV_TAC `ff = heap_map 0 (ha ++ DataElement ys l d::hb)`
  \\ rpt (strip_tac THEN1
   (full_simp_tac (srw_ss()) [heap_length_def,FILTER_APPEND,FILTER_APPEND,
      isForwardPointer_def,SUM_APPEND,el_length_def] \\ decide_tac))
  \\ strip_tac THEN1 (metis_tac [heaps_similar_lemma])
  \\ strip_tac
  THEN1 (full_simp_tac std_ss [EVERY_APPEND] \\ EVAL_TAC \\ full_simp_tac std_ss [])
  \\ full_simp_tac std_ss [APPEND_ASSOC,heap_addresses_SNOC]
  \\ full_simp_tac std_ss [FDOM_FUPDATE]
  \\ strip_tac THEN1
   (`(heap_addresses 0 (h1 ++ h2) UNION {heap_length (h1 ++ h2)}) =
     (heap_length (h1 ++ h2) INSERT heap_addresses 0 (h1 ++ h2))` by (full_simp_tac (srw_ss()) [EXTENSION] \\ metis_tac [])
    \\ `~(heap_length (h1 ++ h2) IN heap_addresses 0 (h1 ++ h2))` by
          full_simp_tac std_ss [NOT_IN_heap_addresses]
    \\ imp_res_tac BIJ_UPDATE
    \\ `(\a'. (ff |+ (heap_length ha,heap_length (h1 ++ h2))) ' a') =
        ((heap_length ha =+ heap_length (h1 ++ h2)) (\a. ff ' a))` by
     (full_simp_tac std_ss [FUN_EQ_THM,APPLY_UPDATE_THM,FAPPLY_FUPDATE_THM]
      \\ SRW_TAC [] []) \\ full_simp_tac std_ss [])
  \\ ntac 3 strip_tac
  \\ Cases_on `i = heap_length ha` THEN1
   (`j = heap_length (h1 ++ h2)` by full_simp_tac std_ss [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
    \\ full_simp_tac std_ss []
    \\ `heap_lookup (heap_length ha) heap0 = SOME (DataElement ys l d)` by
     (imp_res_tac heap_similar_Data_IMP
      \\ full_simp_tac std_ss [heap_lookup_PREFIX])
    \\ full_simp_tac (srw_ss()) [heap_lookup_PREFIX]
    \\ `~(heap_length (h1 ++ h2) < heap_length h1)` by (full_simp_tac (srw_ss()) [heap_length_def,SUM_APPEND] \\ decide_tac)
    \\ full_simp_tac std_ss [])
  \\ `FLOOKUP ff i = SOME j` by full_simp_tac (srw_ss()) [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
  \\ qpat_x_assum `!i j:num. bbb` (mp_tac o Q.SPECL [`i`,`j`])
  \\ full_simp_tac std_ss [] \\ strip_tac
  \\ full_simp_tac (srw_ss()) []
  \\ imp_res_tac heap_lookup_EXTEND
  \\ full_simp_tac (srw_ss()) []
  \\ SRW_TAC [] [] \\ full_simp_tac std_ss []
  \\ res_tac \\ fs []
  \\ match_mp_tac ADDR_MAP_EQ
  \\ full_simp_tac std_ss [FAPPLY_FUPDATE_THM] \\ metis_tac []);

val gc_move_list_thm = Q.prove(
  `!xs h2 a n heap c.
    gc_inv (h1,h2,a,n,heap:('a,'b) heap_element list,c,limit) heap0 roots0 /\
    (!ptr u. MEM (Pointer ptr u) (xs:'a heap_address list) ==>
             isSomeDataOrForward (heap_lookup ptr heap) /\
             reachable_addresses roots0 heap0 ptr) ==>
    ?h23 a3 n3 heap3 c3.
      (gc_move_list (xs,h2,a,n,heap,c,limit) = (ADDR_MAP (heap_map1 heap3) xs,h23,a3,n3,heap3,c3)) /\
      (!ptr u. MEM (Pointer ptr u) xs ==> ptr IN FDOM (heap_map 0 heap3)) /\
      (!ptr. isSomeDataOrForward (heap_lookup ptr heap) =
             isSomeDataOrForward (heap_lookup ptr heap3)) /\
      ((heap_map 0 heap) SUBMAP (heap_map 0 heap3)) /\
      gc_inv (h1,h23,a3,n3,heap3,c3,limit) heap0 roots0`,
  Induct THEN1 (full_simp_tac std_ss [gc_move_list_def,ADDR_MAP_def,MEM,SUBMAP_REFL])
  \\ full_simp_tac std_ss [MEM,gc_move_list_def,LET_DEF] \\ rpt strip_tac
  \\ Q.ABBREV_TAC `x = h` \\ pop_assum (K all_tac)
  \\ mp_tac gc_move_thm \\ full_simp_tac std_ss []
  \\ match_mp_tac IMP_IMP \\ strip_tac THEN1 (rw [] \\ fs [])
  \\ strip_tac \\ full_simp_tac std_ss []
  \\ first_assum (mp_tac o Q.SPECL [`h23`,`a3`,`n3`,`heap3`,`c3`])
  \\ match_mp_tac IMP_IMP \\ strip_tac THEN1 (rw [] \\ fs [] \\ metis_tac [])
  \\ full_simp_tac std_ss [] \\ strip_tac \\ full_simp_tac std_ss []
  \\ imp_res_tac SUBMAP_TRANS \\ full_simp_tac std_ss []
  \\ strip_tac THEN1
   (Cases_on `x` \\ full_simp_tac (srw_ss()) [ADDR_APPLY_def,ADDR_MAP_def]
    \\ full_simp_tac std_ss [heap_map1_def,SUBMAP_DEF])
  \\ full_simp_tac std_ss [SUBMAP_DEF] \\ metis_tac []);

val APPEND_NIL_LEMMA = METIS_PROVE [APPEND_NIL] ``?xs1. xs = xs ++ xs1:'a list``

Theorem gc_move_ALT:
   gc_move (ys,xs,a,n,heap,c,limit) =
      let (ys,xs1,x) = gc_move (ys,[],a,n,heap,c,limit) in
        (ys,xs++xs1,x)
Proof
  Cases_on `ys` \\ simp_tac (srw_ss()) [gc_move_def] \\ rpt strip_tac
  \\ Cases_on `heap_lookup n' heap` \\ simp_tac (srw_ss()) [LET_DEF]
  \\ Cases_on `x` \\ simp_tac (srw_ss()) [LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ full_simp_tac std_ss []
QED

Theorem gc_move_list_ALT:
   !ys xs a n heap c limit ys3 xs3 a3 n3 heap3 c3.
      gc_move_list (ys,xs,a,n,heap,c,limit) =
        let (ys,xs1,x) = gc_move_list (ys,[],a,n,heap,c,limit) in
          (ys,xs++xs1,x)
Proof
  Induct \\ simp_tac std_ss [gc_move_list_def,LET_DEF,APPEND_NIL]
  \\ simp_tac std_ss [Once gc_move_ALT,LET_DEF]
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ full_simp_tac std_ss [LET_DEF] \\ rpt strip_tac
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ full_simp_tac std_ss [APPEND_ASSOC]
QED

val gc_move_list_APPEND_lemma = Q.prove(
  `!ys xs a n heap c limit ys3 xs3 a3 n3 heap3 c3.
      (gc_move_list (ys,xs,a,n,heap,c,limit) = (ys3,xs3,a3,n3,heap3,c3)) ==>
      (?xs1. xs3 = xs ++ xs1)`,
  once_rewrite_tac [gc_move_list_ALT] \\ full_simp_tac std_ss [LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ full_simp_tac std_ss [APPEND_ASSOC] \\ metis_tac []);

val gc_move_loop_thm = Q.prove(
  `!h1 h2 a n heap c.
      gc_inv (h1,h2,a,n,heap:('a,'b) heap_element list,c,limit) heap0 roots0 ==>
      ?h13 a3 n3 heap3 c3.
        (gc_move_loop (h1,h2,a,n,heap,c,limit) = (h13,a3,n3,heap3,c3)) /\
      ((heap_map 0 heap) SUBMAP (heap_map 0 heap3)) /\
      gc_inv (h13,[],a3,n3,heap3,c3,limit) heap0 roots0`,
  completeInduct_on `limit - heap_length h1` \\ rpt strip_tac
  \\ full_simp_tac std_ss [PULL_FORALL] \\ Cases_on `h2`
  \\ full_simp_tac std_ss [gc_move_loop_def,SUBMAP_REFL]
  \\ `isDataElement h` by full_simp_tac (srw_ss()) [gc_inv_def]
  \\ full_simp_tac std_ss [isDataElement_def]
  \\ `~(limit <= heap_length h1)` by
   (full_simp_tac (srw_ss()) [gc_inv_def,heap_length_def,SUM_APPEND]
    \\ full_simp_tac std_ss [el_length_def] \\ decide_tac)
  \\ `~(limit < heap_length (h1 ++ DataElement ys l d::t))` by
   (full_simp_tac (srw_ss()) [gc_inv_def,heap_length_def,SUM_APPEND]
    \\ full_simp_tac std_ss [el_length_def] \\ decide_tac)
  \\ full_simp_tac (srw_ss()) []
  \\ qspecl_then [`ys`,`DataElement ys l d::t`,`a`,`n`,`heap`,`c`] mp_tac
        gc_move_list_thm
  \\ impl_tac THEN1
   (conj_tac THEN fs []
    \\ rpt strip_tac \\ qpat_x_assum `!x1 x2 x3. bbb` (K all_tac)
    \\ full_simp_tac std_ss [gc_inv_def]
    \\ `?i. FLOOKUP (heap_map 0 heap) i = SOME (heap_length h1)` by
     (full_simp_tac std_ss [FLOOKUP_DEF,BIJ_DEF,SURJ_DEF,heap_map1_def]
      \\ qpat_x_assum `!xx.bbb` (K all_tac) \\ qpat_x_assum `!xx.bbb` match_mp_tac
      \\ full_simp_tac (srw_ss()) [heap_addresses_APPEND,heap_addresses_def])
    \\ res_tac \\ `~(heap_length h1 < heap_length h1)` by decide_tac
    \\ imp_res_tac NOT_LESS_IMP_heap_lookup
    \\ full_simp_tac (srw_ss()) [heap_lookup_def]
    \\ full_simp_tac std_ss [heap_ok_def]
    \\ imp_res_tac heap_lookup_MEM \\ res_tac
    \\ imp_res_tac heap_similar_Data_IMP_DataOrForward
    \\ rveq
    \\ fs [reachable_addresses_def]
    \\ asm_exists_tac \\ fs []
    \\ once_rewrite_tac [RTC_CASES_RTC_TWICE]
    \\ asm_exists_tac \\ fs []
    \\ match_mp_tac RTC_SINGLE
    \\ fs [gc_edge_def]
    \\ asm_exists_tac \\ fs [])
  \\ full_simp_tac std_ss [] \\ strip_tac \\ full_simp_tac std_ss [LET_DEF]
  \\ imp_res_tac gc_move_list_APPEND_lemma
  \\ full_simp_tac (srw_ss()) [] \\ full_simp_tac std_ss [AND_IMP_INTRO]
  \\ qpat_x_assum `!limit h1 h2. bbb` (mp_tac o Q.SPECL [`limit`,
       `h1 ++ [DataElement (ADDR_MAP (heap_map1 (heap3:('a,'b) heap_element list)) ys) l d]`,`t ++ xs1`,
       `a3`,`n3`,`heap3`,`c3`]) \\ full_simp_tac std_ss []
  \\ match_mp_tac IMP_IMP \\ reverse strip_tac
  THEN1 (rpt strip_tac \\ full_simp_tac std_ss [] \\ imp_res_tac SUBMAP_TRANS)
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [heap_length_def,el_length_def,SUM_APPEND] \\ decide_tac)
  \\ full_simp_tac std_ss [gc_inv_def,EVERY_DEF,EVERY_APPEND]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ strip_tac
  THEN1 (full_simp_tac (srw_ss()) [heap_length_def,SUM_APPEND,el_length_def])
  \\ strip_tac THEN1 (full_simp_tac (srw_ss()) [isDataElement_def])
  \\ strip_tac THEN1
   (full_simp_tac std_ss [heap_addresses_APPEND,heap_addresses_def,el_length_def])
  \\ rpt strip_tac
  \\ qpat_x_assum `!i j:num. bbb` (mp_tac o Q.SPECL [`i`,`j`])
  \\ full_simp_tac std_ss [] \\ strip_tac \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `j < heap_length h1` THEN1
   (imp_res_tac LESS_IMP_heap_lookup \\ full_simp_tac (srw_ss()) []
    \\ full_simp_tac (srw_ss()) [heap_length_def,SUM_APPEND]
    \\ rw [] \\ res_tac \\ `F` by decide_tac)
  \\ imp_res_tac NOT_LESS_IMP_heap_lookup \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [heap_lookup_def]
  \\ Cases_on `j <= heap_length h1` \\ full_simp_tac (srw_ss()) [] THEN1
   (full_simp_tac std_ss [heap_length_APPEND] \\ SRW_TAC [] []
    \\ full_simp_tac (srw_ss()) [heap_length_def,el_length_def]
    \\ res_tac \\ `F` by decide_tac)
  \\ full_simp_tac std_ss [el_length_def]
  \\ `0 < l+1` by decide_tac \\ full_simp_tac std_ss []
  \\ Cases_on `j < heap_length h1 + (l + 1)` \\ full_simp_tac (srw_ss()) []
  \\ full_simp_tac std_ss [heap_length_APPEND]
  \\ full_simp_tac (srw_ss()) [heap_length_def,el_length_def]);

val gc_inv_init = Q.prove(
  `gc_inv ([],[],0,limit,heap,T,limit) heap roots = heap_ok heap limit`,
  full_simp_tac std_ss [gc_inv_def] \\ Cases_on `heap_ok heap limit`
  \\ full_simp_tac (srw_ss()) [heap_addresses_def,heap_length_def]
  \\ full_simp_tac std_ss [heap_ok_def]
  \\ imp_res_tac FILTER_LEMMA \\ full_simp_tac std_ss [heap_length_def]
  \\ full_simp_tac (srw_ss()) [heaps_similar_REFL,heap_map_EMPTY,FLOOKUP_DEF]
  \\ full_simp_tac (srw_ss()) [BIJ_DEF,INJ_DEF,SURJ_DEF]);

Theorem full_gc_thm:
   roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) limit ==>
    ?heap2 a2 heap3.
      (full_gc (roots:'a heap_address list,heap,limit) =
         (ADDR_MAP (heap_map1 heap3) roots,heap2,a2,T)) /\
      (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM (heap_map 0 heap3)) /\
      gc_inv (heap2,[],a2,limit - a2,heap3,T,limit) heap roots
Proof
  simp_tac std_ss [Once (GSYM gc_inv_init)]
  \\ rpt strip_tac \\ full_simp_tac std_ss [full_gc_def]
  \\ mp_tac (Q.SPECL [`roots`,`[]`,`0`,`limit`,`heap`,`T`] gc_move_list_thm |> Q.INST [`h1`|->`[]`,`heap0`|->`heap`,`roots0`|->`roots`])
  \\ full_simp_tac std_ss [gc_inv_init] \\ match_mp_tac IMP_IMP \\ strip_tac THEN1
   (full_simp_tac std_ss [roots_ok_def] \\ rpt strip_tac \\ res_tac
    \\ full_simp_tac (srw_ss()) [isSomeDataOrForward_def,isSomeDataElement_def]
    \\ fs [reachable_addresses_def] \\ asm_exists_tac \\ fs [])
  \\ strip_tac \\ full_simp_tac std_ss [LET_DEF]
  \\ mp_tac (Q.SPECL [`[]`,`h23`,`a3`,`n3`,`heap3`,`c3`] gc_move_loop_thm |> Q.INST [`heap0`|->`heap`,`roots0`|->`roots`])
  \\ full_simp_tac std_ss [] \\ strip_tac \\ full_simp_tac std_ss []
  \\ qexists_tac `heap3'` \\ full_simp_tac std_ss []
  \\ `c3'` by full_simp_tac std_ss [gc_inv_def] \\ full_simp_tac std_ss []
  \\ `n3' = limit - a3'` by (full_simp_tac std_ss [gc_inv_def] \\ decide_tac)
  \\ `!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM (heap_map 0 heap3')` by
        (full_simp_tac std_ss [SUBMAP_DEF,heap_map1_def] \\ metis_tac [])
  \\ full_simp_tac std_ss [] \\ reverse (rpt strip_tac)
  THEN1 metis_tac []
  THEN1 (full_simp_tac std_ss [gc_inv_def,APPEND_NIL] \\ decide_tac)
  THEN1 (full_simp_tac std_ss [heap_ok_def] \\ decide_tac)
  THEN1 (full_simp_tac std_ss [gc_inv_def,APPEND_NIL] \\ decide_tac)
  THEN1 (full_simp_tac std_ss [gc_inv_def,APPEND_NIL] \\ decide_tac)
  \\ match_mp_tac ADDR_MAP_EQ
  \\ full_simp_tac std_ss [] \\ rpt strip_tac \\ res_tac
  \\ full_simp_tac std_ss [SUBMAP_DEF,heap_map1_def]
QED

val heap_lookup_IMP_heap_addresses = Q.prove(
  `!xs n x j. (heap_lookup j xs = SOME x) ==> n + j IN heap_addresses n xs`,
  Induct \\ full_simp_tac std_ss [MEM,heap_lookup_def,heap_addresses_def]
  \\ SRW_TAC [] [] \\ res_tac
  \\ pop_assum (mp_tac o Q.SPEC `n + el_length h`)
  \\ `n + el_length h + (j - el_length h) = n + j` by decide_tac
  \\ metis_tac []) |> Q.SPECL [`xs`,`0`] |> SIMP_RULE std_ss [] |> GEN_ALL;

Theorem full_gc_LENGTH:
   roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) limit ==>
    ?roots2 heap2 a2.
      (full_gc (roots:'a heap_address list,heap,limit) =
      (roots2,heap2,heap_length heap2,T))
Proof
  rpt strip_tac \\ mp_tac full_gc_thm \\ full_simp_tac std_ss []
  \\ rpt strip_tac \\ full_simp_tac std_ss [gc_inv_def,APPEND_NIL]
QED

Theorem full_gc_ok:
   roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) limit ==>
    ?roots2 heap2 a2.
      (full_gc (roots:'a heap_address list,heap,limit) = (roots2,heap2,a2,T)) /\
      a2 <= limit /\ roots_ok roots2 (heap2 ++ heap_expand (limit - a2)) /\
      heap_ok (heap2 ++ heap_expand (limit - a2)) limit
Proof
  rpt strip_tac \\ mp_tac full_gc_thm \\ full_simp_tac std_ss [] \\ strip_tac
  \\ full_simp_tac std_ss [] \\ full_simp_tac std_ss [gc_inv_def]
  \\ full_simp_tac std_ss [APPEND_NIL] \\ strip_tac THEN1 decide_tac
  \\ simp_tac std_ss [roots_ok_def,heap_ok_def]
  \\ rpt strip_tac THEN1
   (imp_res_tac MEM_ADDR_MAP \\ res_tac \\ full_simp_tac std_ss [heap_map1_def]
    \\ `FLOOKUP (heap_map 0 heap3) y = SOME ptr` by full_simp_tac std_ss [FLOOKUP_DEF]
    \\ res_tac \\ full_simp_tac (srw_ss()) [isSomeDataElement_def]
    \\ imp_res_tac heap_lookup_EXTEND \\ full_simp_tac (srw_ss()) [])
  THEN1
   (full_simp_tac std_ss [heap_length_APPEND,heap_length_heap_expand] \\ decide_tac)
  THEN1
   (full_simp_tac std_ss [FILTER_APPEND,EVERY_isDataElement_IMP_LEMMA,APPEND]
    \\ Cases_on `(heap_length (FILTER (\h. ~isForwardPointer h) heap3))`
    \\ full_simp_tac (srw_ss()) [heap_expand_def,isForwardPointer_def])
  \\ reverse (full_simp_tac std_ss [MEM_APPEND]) THEN1
   (Cases_on `(heap_length (FILTER (\h. ~isForwardPointer h) heap3))`
    \\ full_simp_tac (srw_ss()) [heap_expand_def,isForwardPointer_def])
  \\ `?j. heap_lookup j heap2 = SOME (DataElement xs l d)` by
         metis_tac [MEM_IMP_heap_lookup]
  \\ `?i. (FLOOKUP (heap_map 0 heap3) i = SOME j)` by
   (imp_res_tac heap_lookup_IMP_heap_addresses
    \\ full_simp_tac std_ss [BIJ_DEF,SURJ_DEF,heap_map1_def,FLOOKUP_DEF]
    \\ res_tac \\ full_simp_tac std_ss [])
  \\ res_tac
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ full_simp_tac (srw_ss()) []
  \\ strip_tac \\ `j < heap_length heap2` by (imp_res_tac heap_lookup_LESS)
  \\ full_simp_tac std_ss [] \\ strip_tac
  \\ imp_res_tac MEM_ADDR_MAP
  \\ `y IN FDOM (heap_map 0 heap3)` by res_tac
  \\ `(FLOOKUP (heap_map 0 heap3) y = SOME (heap_map1 heap3 y))` by full_simp_tac std_ss [FLOOKUP_DEF,heap_map1_def]
  \\ pop_assum mp_tac \\ full_simp_tac std_ss [] \\ strip_tac
  \\ qpat_x_assum `!i j:num. bbb` (mp_tac o Q.SPECL [`y`,`ptr`])
  \\ full_simp_tac std_ss [] \\ strip_tac
  \\ match_mp_tac isSome_heap_looukp_IMP_APPEND \\ full_simp_tac std_ss []
  \\ full_simp_tac (srw_ss()) [isSomeDataElement_def]
QED

Theorem full_gc_related:
   roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) limit ==>
    ?heap2 a2 f.
      (full_gc (roots:'a heap_address list,heap,limit) =
         (ADDR_MAP (FAPPLY f) roots,heap2,a2,T)) /\
      (FDOM f = reachable_addresses roots heap) /\
      (heap_length heap2 = heap_length (heap_filter (FDOM f) heap)) /\
      gc_related f heap (heap2 ++ heap_expand (limit - a2))
Proof
  strip_tac \\ mp_tac full_gc_thm \\ asm_simp_tac std_ss []
  \\ rpt strip_tac \\ full_simp_tac std_ss []
  \\ qexists_tac `heap_map 0 heap3`
  \\ `(FAPPLY (heap_map 0 heap3)) = heap_map1 heap3` by (full_simp_tac std_ss [heap_map1_def,FUN_EQ_THM])
  \\ full_simp_tac std_ss [gc_related_def,gc_inv_def,BIJ_DEF]
  \\ conj_asm1_tac
  THEN1
   (fs [EXTENSION] \\ rpt strip_tac
    \\ CONV_TAC (RAND_CONV (REWRITE_CONV [IN_DEF]))
    \\ rw [] \\ eq_tac \\ rw []
    THEN1 (fs [FLOOKUP_DEF] \\ metis_tac [])
    \\ fs [reachable_addresses_def]
    \\ rename [`RTC _ a1 a2`]
    \\ `a1 ∈ FDOM (heap_map 0 heap3)` by res_tac
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
    \\ reverse conj_tac THEN1 metis_tac []
    \\ fs [heap_map1_def,INJ_DEF,SURJ_DEF]
    \\ qpat_x_assum `!x. _` kall_tac
    \\ first_x_assum drule
    \\ metis_tac [heap_addresses_LESS_heap_length,ADD_0,ADD_COMM])
  \\ strip_tac THEN1
   (simp [Once (GSYM heap_length_heap_filter)]
    \\ match_mp_tac (GEN_ALL heap_length_heap_filter_eq)
    \\ fs [FLOOKUP_DEF,BIJ_DEF] \\ asm_exists_tac \\ fs []
    \\ fs [FINITE_heap_addresses]
    \\ conj_tac THEN1 (metis_tac [FDOM_FINITE])
    \\ rw [] \\ res_tac \\ fs [])
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [INJ_DEF] \\ rpt strip_tac
    \\ `(FLOOKUP (heap_map 0 heap3) x = SOME (heap_map1 heap3 x))` by full_simp_tac (srw_ss()) [FLOOKUP_DEF,heap_map1_def]
    \\ res_tac \\ full_simp_tac std_ss []
    \\ imp_res_tac heap_lookup_LESS
    \\ imp_res_tac heap_lookup_EXTEND \\ full_simp_tac std_ss []
    \\ full_simp_tac (srw_ss()) [isSomeDataElement_def])
  \\ ntac 3 strip_tac
  >- (`(FLOOKUP (heap_map 0 heap3) i = SOME (heap_map1 heap3 i))` by fs [FLOOKUP_DEF]
      \\ res_tac \\ fs []
      \\ fs [isSomeDataElement_def])
  \\ ntac 3 strip_tac
  \\ `(FLOOKUP (heap_map 0 heap3) i = SOME (heap_map1 heap3 i))`
       by full_simp_tac std_ss [FLOOKUP_DEF]
  \\ res_tac \\ full_simp_tac (srw_ss()) [APPEND_NIL]
  \\ imp_res_tac heap_lookup_LESS \\ imp_res_tac heap_lookup_EXTEND
  \\ full_simp_tac std_ss [] \\ metis_tac []
QED

(* Lemmas about ok and a *)

Theorem gc_move_ok:
   (gc_move (x,h2,a,n,heap,c,limit) = (x',h2',a',n',heap',T)) ==>
    c /\
    ((a = b + heap_length h2) ==> (a' = b + heap_length h2'))
Proof
  simp_tac std_ss [Once EQ_SYM_EQ] \\ Cases_on `x`
  \\ full_simp_tac std_ss [gc_move_def]
  \\ Cases_on `heap_lookup n'' heap` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `x` \\ full_simp_tac (srw_ss()) [LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ full_simp_tac std_ss []
  \\ rpt strip_tac \\ imp_res_tac gc_forward_ptr_ok
  \\ rpt (pop_assum mp_tac)
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ full_simp_tac std_ss []
  \\ full_simp_tac (srw_ss()) [heap_length_APPEND,heap_length_def,
       el_length_def,ADD_ASSOC]
QED

Theorem gc_move_list_ok:
   !xs h2 a n heap c limit xs' h2' a' n' heap' c'.
      (gc_move_list (xs,h2,a,n,heap,c,limit) = (xs',h2',a',n',heap',T)) ==>
      c /\
      ((a = b + heap_length h2) ==> (a' = b + heap_length h2'))
Proof
  Induct \\ simp_tac std_ss [gc_move_list_def] \\ rpt strip_tac
  THENL [all_tac, pop_assum mp_tac]
  \\ pop_assum mp_tac
  \\ `? x' h2' a' n' heap' c'. gc_move (h,h2,a,n,heap,c,limit) =
       (x',h2',a',n',heap',c')` by metis_tac [PAIR]
  \\ pop_assum (fn th => ASSUME_TAC th THEN once_rewrite_tac [th])
  \\ simp_tac std_ss [LET_DEF]
  \\ `? xs1 h21 a1 n1 heap1 c1. gc_move_list (xs,h2'',a'',n'',heap'',c',limit) =
       (xs1,h21,a1,n1,heap1,c1)` by metis_tac [PAIR]
  \\ pop_assum (fn th => ASSUME_TAC th THEN once_rewrite_tac [th])
  \\ simp_tac std_ss [LET_DEF]
  \\ Cases_on `c1` \\ simp_tac std_ss [] \\ `c'` by metis_tac []
  \\ pop_assum mp_tac \\ Cases_on `c'` \\ simp_tac std_ss []
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ simp_tac std_ss [] \\ res_tac
  \\ imp_res_tac gc_move_ok \\ metis_tac []
QED

val th =
  fetch "-" "gc_move_loop_ind" |> Q.SPEC `(\(h1,h2,a,n,heap,c,limit).
     !xs' h1' a' n' heap' c'.
       (gc_move_loop (h1,h2,a,n,heap,c,limit) = (h1',a',n',heap',T)) ==>
       c)`

val lemma = prove(th |> concl |> dest_imp |> fst,
  rpt strip_tac \\ simp_tac std_ss [gc_move_loop_def]
  \\ rpt strip_tac \\ pop_assum mp_tac
  \\ Cases_on `limit < heap_length (h1 ++ h::h2)`
  \\ asm_rewrite_tac [] \\ simp_tac std_ss []
  \\ Cases_on `h` \\ simp_tac (srw_ss()) []
  \\ `?x1 x2 x3 x4 x5 x6.
        gc_move_list (l,DataElement l n'' b::h2,a,n,heap,c,limit) =
          (x1,x2,x3,x4,x5,x6)` by metis_tac [PAIR]
  \\ asm_rewrite_tac [] \\ simp_tac std_ss [LET_DEF]
  \\ qpat_x_assum `!xs.bbb` mp_tac
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV (srw_ss()) []))
  \\ asm_rewrite_tac [] \\ simp_tac std_ss [LET_DEF] \\ rpt strip_tac
  \\ res_tac \\ full_simp_tac std_ss [] \\ imp_res_tac gc_move_list_ok)

val th = MP th lemma |> SIMP_RULE std_ss []
         |> Q.SPECL [`h1`,`h2`,`a`,`n`,`heap`,`c`,`limit`,`h1'`,`a'`,`n'`,`heap'`]

val gc_move_loop_ok = save_thm("gc_move_loop_ok",th);

Theorem gc_move_list_IMP_LENGTH:
   !l5 h a n heap c k xs ys a1 xs1 heap1 c1.
      (gc_move_list (l5,h,a,n,heap,c,k) =
        (xs,ys,a1,xs1,heap1,c1)) ==> (LENGTH xs = LENGTH l5)
Proof
  Induct \\ fs [gc_move_list_def,LET_THM] \\ rw []
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[] \\ rw []
  \\ res_tac \\ fs []
QED

Theorem full_gc_IMP_LENGTH:
   (full_gc (xs,heap,limit) = (roots2,heap2,h,T)) ==>
    (LENGTH roots2 = LENGTH xs)
Proof
  fs [full_gc_def,LET_THM]
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ imp_res_tac gc_move_list_IMP_LENGTH \\ fs []
QED

Theorem gc_move_IMP_isDataElement:
   !l5 h a n heap c k xs ys a1 xs1 heap1 c1.
      EVERY isDataElement h /\
      (gc_move (l5,h,a,n,heap,c,k) =
        (xs,ys,a1,xs1,heap1,c1)) ==>
      EVERY isDataElement ys
Proof
  Cases \\ fs [gc_move_def]
  \\ rw [] \\ every_case_tac \\ fs []
  \\ pairarg_tac \\ fs [] \\ rw [] \\ fs [isDataElement_def]
QED

Theorem gc_move_list_IMP_isDataElement:
   !l5 h a n heap c k xs ys a1 xs1 heap1 c1.
      EVERY isDataElement h /\
      (gc_move_list (l5,h,a,n,heap,c,k) =
        (xs,ys,a1,xs1,heap1,c1)) ==>
      EVERY isDataElement ys
Proof
  Induct \\ fs [gc_move_list_def,LET_THM] \\ rw []
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[] \\ rw []
  \\ imp_res_tac gc_move_IMP_isDataElement
  \\ res_tac \\ fs []
QED

Theorem gc_move_loop_IMP_isDataElement:
   !h1 h2 a n heap c limit h1' a' n' heap' c'.
      EVERY isDataElement h1 /\
      EVERY isDataElement h2 /\
      (gc_move_loop (h1,h2,a,n,heap,c,limit) = (h1',a',n',heap',T)) ==>
      EVERY isDataElement h1'
Proof
  recInduct (fetch "-" "gc_move_loop_ind") \\ rw []
  \\ fs [gc_move_loop_def]
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rfs [] \\ fs [isDataElement_def]
  \\ imp_res_tac gc_move_loop_ok \\ fs []
  \\ imp_res_tac gc_move_list_IMP_isDataElement \\ fs []
  \\ Cases_on `h2'` \\ fs [isDataElement_def]
QED

Theorem full_gc_IMP_isDataElement:
   (full_gc (roots,heap,limit) = (roots1,heap1,a,T)) ==>
    EVERY isDataElement heap1
Proof
  fs [full_gc_def]
  \\ rpt (pairarg_tac \\ fs []) \\ strip_tac \\ rveq \\ fs []
  \\ imp_res_tac gc_move_list_IMP_isDataElement \\ fs []
  \\ imp_res_tac gc_move_loop_IMP_isDataElement \\ fs []
QED

val _ = export_theory();
