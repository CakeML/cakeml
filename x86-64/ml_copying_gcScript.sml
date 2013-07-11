open HolKernel boolLib bossLib Parse; val _ = new_theory "ml_copying_gc";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open wordsTheory wordsLib integer_wordTheory;

open BytecodeTheory;

val _ = set_fixity "=" (Infix(NONASSOC, 100));

infix \\ val op \\ = op THEN;

(* The ML heap is represented as a list of heap_elements. *)

val _ = Hol_datatype `
  heap_address = Pointer of num | Data of 'a`;

val _ = Hol_datatype `
  heap_element = Unused of num
               | ForwardPointer of num => num
               | DataElement of ('a heap_address) list => num => 'b`;

(* The heap is accessed using the following lookup function. *)

val el_length_def = Define `
  (el_length (Unused l) = l+1) /\
  (el_length (ForwardPointer n l) = l+1) /\
  (el_length (DataElement xs l data) = l+1)`;

val heap_lookup_def = Define `
  (heap_lookup a [] = NONE) /\
  (heap_lookup a (x::xs) =
     if a = 0 then SOME x else
     if a < el_length x then NONE else heap_lookup (a - el_length x) xs)`;

(* The heap is well-formed if heap_ok *)

val isDataElement_def = Define `
  isDataElement x = ?ys l d. x = DataElement ys l d`;

val isSomeDataElement_def = Define `
  isSomeDataElement x = ?ys l d. x = SOME (DataElement ys l d)`;

val heap_length_def = Define `
  heap_length heap = SUM (MAP el_length heap)`;

val roots_ok_def = Define `
  roots_ok roots heap =
    !ptr. MEM (Pointer ptr) roots ==> isSomeDataElement (heap_lookup ptr heap)`;

val isForwardPointer_def = Define `
  (isForwardPointer (ForwardPointer n l) = T) /\
  (isForwardPointer _ = F)`;

val heap_ok_def = Define `
  heap_ok heap limit =
    (heap_length heap = limit) /\
    (FILTER isForwardPointer heap = []) /\
    (!ptr xs l d. MEM (DataElement xs l d) heap /\ MEM (Pointer ptr) xs ==>
                  isSomeDataElement (heap_lookup ptr heap))`;

(* The GC is a copying collector which moves elements *)

val gc_forward_ptr_def = Define `
  (gc_forward_ptr a [] ptr c = ([],F)) /\
  (gc_forward_ptr a (x::xs) ptr c =
     if a = 0 then
       (ForwardPointer ptr ((el_length x)-1) :: xs, isDataElement x /\ c) else
     if a < el_length x then (x::xs,F) else
       let (xs,c) = gc_forward_ptr (a - el_length x) xs ptr c in
         (x::xs,c))`;

val gc_move_def = Define `
  (gc_move (Data d,h2,a,n,heap,c,limit) = (Data d,h2,a,n,heap,c)) /\
  (gc_move (Pointer ptr,h2,a,n,heap,c,limit) =
     case heap_lookup ptr heap of
     | SOME (DataElement xs l dd) =>
         let c = c /\ l+1 <= n /\ (a + n = limit) in
         let n = n - (l+1) in
         let h2 = h2 ++ [DataElement xs l dd] in
         let (heap,c) = gc_forward_ptr ptr heap a c in
           (Pointer a,h2,a + (l+1),n,heap,c)
     | SOME (ForwardPointer ptr l) => (Pointer ptr,h2,a,n,heap,c)
     | _ => (ARB,h2,a,n,heap,F))`

val gc_move_list_def = Define `
  (gc_move_list ([],h2,a,n,heap,c,limit) = ([],h2,a,n,heap,c)) /\
  (gc_move_list (x::xs,h2,a,n,heap,c,limit) =
     let (x,h2,a,n,heap,c) = gc_move (x,h2,a,n,heap,c,limit) in
     let (xs,h2,a,n,heap,c) = gc_move_list (xs,h2,a,n,heap,c,limit) in
       (x::xs,h2,a,n,heap,c))`;

val SUM_APPEND = prove(
  ``!xs ys. SUM (xs ++ ys) = SUM xs + SUM ys``,
  Induct \\ SRW_TAC [] [ADD_ASSOC]);

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
   \\ SRW_TAC [] [heap_length_def,el_length_def,SUM_APPEND] \\ DECIDE_TAC);

val heap_expand_def = Define `
  heap_expand n = if n = 0 then [] else [Unused (n-1)]`;

val full_gc_def = Define `
  full_gc (roots,heap,limit) =
    let (roots,h2,a,n,heap,c) = gc_move_list (roots,[],0,limit,heap,T,limit) in
    let (heap,a,n,temp,c) = gc_move_loop ([],h2,a,n,heap,c,limit) in
    let c = c /\ (a = heap_length heap) /\ (heap_length temp = limit) /\
                 (n = limit - a) in
      (roots,heap,a,c)`;

(* Invariant *)

val heap_map_def = Define `
  (heap_map a [] = FEMPTY) /\
  (heap_map a (ForwardPointer ptr l::xs) =
     heap_map (a + l + 1) xs |+ (a,ptr)) /\
  (heap_map a (x::xs) = heap_map (a + el_length x) xs)`;

val heap_map1_def = Define `
  heap_map1 heap = (\a. heap_map 0 heap ' a)`;

val heap_addresses_def = Define `
  (heap_addresses a [] = {}) /\
  (heap_addresses a (x::xs) = a INSERT heap_addresses (a + el_length x) xs)`;

val ADDR_MAP_def = Define `
  (ADDR_MAP f [] = []) /\
  (ADDR_MAP f (Data x::xs) = Data x :: ADDR_MAP f xs) /\
  (ADDR_MAP f (Pointer a::xs) = Pointer (f a) :: ADDR_MAP f xs)`;

val ADDR_APPLY_def = Define `
  (ADDR_APPLY f (Pointer x) = Pointer (f x)) /\
  (ADDR_APPLY f (Data y) = Data y)`;

val isSomeForwardPointer_def = Define `
  isSomeForwardPointer x = ?ptr l. x = SOME (ForwardPointer ptr l)`;

val isSomeDataOrForward_def = Define `
  isSomeDataOrForward x = isSomeForwardPointer x \/ isSomeDataElement x`;

val EVERY2_def = Define `
  (EVERY2 f [] [] = T) /\
  (EVERY2 f [] (y::ys) = F) /\
  (EVERY2 f (x::xs) [] = F) /\
  (EVERY2 f (x::xs) (y::ys) = f x y /\ EVERY2 f xs ys)`;

val _ = augment_srw_ss [rewrites [EVERY2_def]];

val heaps_similar_def = Define `
  heaps_similar heap0 heap =
    EVERY2 (\h0 h. if isForwardPointer h then
                     (el_length h = el_length h0) /\ isDataElement h0
                   else (h = h0)) heap0 heap`

val gc_inv_def = Define `
  gc_inv (h1,h2,a,n,heap,c,limit) heap0 =
    (a + n = limit) /\
    (a = heap_length (h1 ++ h2)) /\
    (n = heap_length (FILTER ( \ h. ~(isForwardPointer h)) heap)) /\ c /\
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
                   !ptr. MEM (Pointer ptr) xs /\ j < heap_length h1 ==>
                         ptr IN FDOM (heap_map 0 heap)`;

(* Invariant maintained *)

val heap_lookup_MEM = prove(
  ``!heap n x. (heap_lookup n heap = SOME x) ==> MEM x heap``,
  Induct \\ FULL_SIMP_TAC std_ss [heap_lookup_def] \\ SRW_TAC [] []
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []);

val DRESTRICT_heap_map = prove(
  ``!heap k. n < k ==> (DRESTRICT (heap_map k heap) (COMPL {n}) = heap_map k heap)``,
  SIMP_TAC (srw_ss()) [GSYM fmap_EQ_THM,DRESTRICT_DEF,EXTENSION] \\ REPEAT STRIP_TAC
  \\ Cases_on `x IN FDOM (heap_map k heap)` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT (POP_ASSUM MP_TAC)  \\ Q.SPEC_TAC (`k`,`k`) \\ Q.SPEC_TAC (`heap`,`heap`)
  \\ Induct \\ FULL_SIMP_TAC (srw_ss()) [heap_map_def]
  \\ Cases \\ FULL_SIMP_TAC (srw_ss()) [heap_map_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [DECIDE ``n<k ==> n < k + m:num``,DECIDE ``n<k ==> n < k + m+1:num``]);

val IN_FRANGE = prove(
  ``!heap n. MEM (ForwardPointer ptr l) heap ==> ptr IN FRANGE (heap_map n heap)``,
  Induct \\ FULL_SIMP_TAC std_ss [MEM] \\ REPEAT STRIP_TAC
  \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss()) [heap_map_def,FRANGE_FUPDATE]
  \\ `n < n + n0 + 1` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss [DRESTRICT_heap_map]);

val heap_lookup_SPLIT = store_thm("heap_lookup_SPLIT",
  ``!heap n x. (heap_lookup n heap = SOME x) ==>
               ?ha hb. (heap = ha ++ x::hb) /\ (n = heap_length ha)``,
  Induct \\ FULL_SIMP_TAC std_ss [heap_lookup_def] \\ SRW_TAC [] []
  THEN1 (Q.LIST_EXISTS_TAC [`[]`,`heap`] \\ FULL_SIMP_TAC (srw_ss()) [heap_length_def])
  \\ RES_TAC \\ Q.LIST_EXISTS_TAC [`h::ha`,`hb`]
  \\ FULL_SIMP_TAC (srw_ss()) [heap_length_def] \\ DECIDE_TAC);

val gc_forward_ptr_thm = store_thm("gc_forward_ptr_thm",
  ``!ha. gc_forward_ptr (heap_length ha) (ha ++ DataElement ys l d::hb) a c =
         (ha ++ ForwardPointer a l::hb,c)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [gc_forward_ptr_def,heap_length_def,APPEND,
    el_length_def,isDataElement_def,LET_DEF] \\ SRW_TAC [] []
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [el_length_def] \\ DECIDE_TAC);

val heap_lookup_FLOOKUP = prove(
  ``!heap n k.
      (heap_lookup n heap = SOME (ForwardPointer ptr l)) ==>
      (FLOOKUP (heap_map k heap) (n+k) = SOME ptr)``,
  Induct \\ FULL_SIMP_TAC std_ss [heap_lookup_def] \\ SRW_TAC [] []
  THEN1 (FULL_SIMP_TAC (srw_ss()) [heap_map_def,FLOOKUP_DEF])
  \\ RES_TAC \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `k + el_length h`)
  \\ `n - el_length h + (k + el_length h) = n + k` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [heap_map_def,el_length_def]
  \\ FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF,ADD_ASSOC,FAPPLY_FUPDATE_THM])
  |> Q.SPECL [`heap`,`n`,`0`] |> SIMP_RULE std_ss [];

val IN_heap_map_IMP = prove(
  ``!heap n k. n IN FDOM (heap_map k heap) ==> k <= n``,
  Induct \\ TRY (Cases_on `h`) \\ FULL_SIMP_TAC (srw_ss()) [heap_map_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [heap_length_def,el_length_def] \\ DECIDE_TAC);

val NOT_IN_heap_map = prove(
  ``!ha n. ~(n + heap_length ha IN FDOM (heap_map n (ha ++ DataElement ys l d::hb)))``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [heap_map_def,APPEND,heap_length_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC IN_heap_map_IMP
  \\ FULL_SIMP_TAC std_ss [ADD_ASSOC] \\ RES_TAC
  THEN1 (FULL_SIMP_TAC std_ss [el_length_def] \\ DECIDE_TAC)
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [heap_map_def]
  \\ RES_TAC \\ FULL_SIMP_TAC (srw_ss()) [el_length_def,ADD_ASSOC] \\ RES_TAC
  \\ DECIDE_TAC) |> Q.SPECL [`ha`,`0`] |> SIMP_RULE std_ss []

val isSomeDataOrForward_lemma = prove(
  ``!ha ptr.
      isSomeDataOrForward (heap_lookup ptr (ha ++ DataElement ys l d::hb)) <=>
      isSomeDataOrForward (heap_lookup ptr (ha ++ [ForwardPointer a l] ++ hb))``,
  Induct \\ FULL_SIMP_TAC std_ss [APPEND,heap_lookup_def]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [el_length_def]);

val FILTER_APPEND = prove(
  ``!xs ys p. FILTER p (xs ++ ys) = FILTER p xs ++ FILTER p ys``,
  Induct \\ SRW_TAC [] [FILTER]);

val EVERY2_SPLIT = prove(
  ``!xs1 zs.
      EVERY2 P zs (xs1 ++ x::xs2) ==>
      ?ys1 y ys2. (zs = ys1 ++ y::ys2) /\ EVERY2 P ys1 xs1 /\
                  EVERY2 P ys2 xs2 /\ P y x``,
  Induct \\ FULL_SIMP_TAC std_ss [APPEND]
  \\ Cases_on `zs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  THEN1 (REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`[]`,`h`,`t`] \\ SRW_TAC [] [])
  \\ Q.LIST_EXISTS_TAC [`h::ys1`,`y`,`ys2`] \\ FULL_SIMP_TAC (srw_ss()) []);

val EVERY2_SPLIT_ALT = prove(
  ``!xs1 zs.
      EVERY2 P (xs1 ++ x::xs2) zs ==>
      ?ys1 y ys2. (zs = ys1 ++ y::ys2) /\ EVERY2 P xs1 ys1 /\
                  EVERY2 P xs2 ys2 /\ P x y``,
  Induct \\ FULL_SIMP_TAC std_ss [APPEND]
  \\ Cases_on `zs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  THEN1 (Q.LIST_EXISTS_TAC [`[]`] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Q.LIST_EXISTS_TAC [`h::ys1`,`y`,`ys2`] \\ FULL_SIMP_TAC (srw_ss()) []);

val EVERY2_APPEND = prove(
  ``!xs ts.
      (LENGTH xs = LENGTH ts) ==>
      (EVERY2 P (xs ++ ys) (ts ++ us) = EVERY2 P xs ts /\ EVERY2 P ys us)``,
  Induct \\ Cases_on `ts` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,CONJ_ASSOC]);

val EVERY2_IMP_LENGTH = prove(
  ``!xs ys. EVERY2 P xs ys ==> (LENGTH xs = LENGTH ys)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,CONJ_ASSOC]);

val heaps_similar_IMP_heap_length = prove(
  ``!xs ys. heaps_similar xs ys ==> (heap_length xs = heap_length ys)``,
  Induct \\ Cases_on `ys`
  \\ FULL_SIMP_TAC (srw_ss()) [heaps_similar_def,heap_length_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `isForwardPointer h`
  \\ FULL_SIMP_TAC std_ss []);

val heap_similar_Data_IMP = prove(
  ``heaps_similar heap0 (ha ++ DataElement ys l d::hb) ==>
    ?ha0 hb0. (heap0 = ha0 ++ DataElement ys l d::hb0) /\
              (heap_length ha = heap_length ha0)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [heaps_similar_def]
  \\ IMP_RES_TAC EVERY2_SPLIT \\ FULL_SIMP_TAC std_ss [isForwardPointer_def]
  \\ POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`ys1`,`ys2`] \\ FULL_SIMP_TAC std_ss []
  \\ `heaps_similar ys1 ha` by FULL_SIMP_TAC std_ss [heaps_similar_def]
  \\ FULL_SIMP_TAC std_ss [heaps_similar_IMP_heap_length]);

val heaps_similar_lemma = prove(
  ``!ha heap0.
      heaps_similar heap0 (ha ++ DataElement ys l d::hb) ==>
      heaps_similar heap0 (ha ++ [ForwardPointer (heap_length (h1 ++ h2)) l] ++ hb)``,
  FULL_SIMP_TAC std_ss [heaps_similar_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC EVERY2_SPLIT \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC EVERY2_IMP_LENGTH
  \\ FULL_SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [EVERY2_APPEND,EVERY2_def]
  \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [isForwardPointer_def]
  \\ Q.PAT_ASSUM `DataElement ys l d = y` (MP_TAC o GSYM)
  \\ FULL_SIMP_TAC (srw_ss()) [el_length_def]);

val heap_addresses_SNOC = prove(
  ``!xs n x.
      heap_addresses n (xs ++ [x]) =
      heap_addresses n xs UNION {heap_length xs + n}``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [heap_addresses_def,APPEND,heap_length_def]
  \\ FULL_SIMP_TAC (srw_ss()) [EXTENSION] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC,DISJ_ASSOC]);

val NOT_IN_heap_addresses = prove(
  ``!xs n. ~(n + heap_length xs IN heap_addresses n xs)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [heap_addresses_def,APPEND,heap_length_def]
  \\ FULL_SIMP_TAC (srw_ss()) [EXTENSION] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [ADD_ASSOC]
  THEN1 (Cases_on `h` \\ EVAL_TAC \\ DECIDE_TAC) \\ METIS_TAC [])
  |> Q.SPECL [`xs`,`0`] |> SIMP_RULE std_ss [];

val BIJ_UPDATE = prove(
  ``BIJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
    BIJ ((x =+ y) f) (x INSERT s) (y INSERT t)``,
  SIMP_TAC std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_INSERT,APPLY_UPDATE_THM]
  \\ METIS_TAC []);

val INJ_UPDATE = prove(
  ``INJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
    INJ ((x =+ y) f) (x INSERT s) (y INSERT t)``,
  SIMP_TAC std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_INSERT,APPLY_UPDATE_THM]
  \\ METIS_TAC []);

val heap_lookup_PREFIX = prove(
  ``!xs. (heap_lookup (heap_length xs) (xs ++ x::ys) = SOME x)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [heap_lookup_def,APPEND,heap_length_def]
  \\ SRW_TAC [] [] \\ Cases_on `h`
  \\ FULL_SIMP_TAC std_ss [el_length_def] \\ DECIDE_TAC);

val heap_lookup_EXTEND = prove(
  ``!xs n ys x. (heap_lookup n xs = SOME x) ==>
                (heap_lookup n (xs ++ ys) = SOME x)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [heap_lookup_def] \\ SRW_TAC [] []);

val ADDR_MAP_EQ = prove(
  ``!xs. (!p. MEM (Pointer p) xs ==> (f p = g p)) ==>
         (ADDR_MAP f xs = ADDR_MAP g xs)``,
  Induct \\ TRY (Cases_on `h`) \\ FULL_SIMP_TAC (srw_ss()) [ADDR_MAP_def]);

val heap_map_APPEND = prove(
  ``!xs n ys. (heap_map n (xs ++ ys)) =
              FUNION (heap_map n xs) (heap_map (n + heap_length xs) ys)``,
  Induct \\ TRY (Cases_on `h`) \\ FULL_SIMP_TAC (srw_ss())
     [APPEND,heap_map_def,FUNION_DEF,FUNION_FEMPTY_1,heap_length_def,ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [FUNION_FUPDATE_1,el_length_def,ADD_ASSOC]);

val FDOM_heap_map = prove(
  ``!xs n. ~(n + heap_length xs IN FDOM (heap_map n xs))``,
  Induct \\ TRY (Cases_on `h`)
  \\ FULL_SIMP_TAC (srw_ss()) [heap_map_def,heap_length_def,ADD_ASSOC]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [el_length_def,ADD_ASSOC]
  \\ TRY DECIDE_TAC \\ METIS_TAC [])
  |> Q.SPECL [`xs`,`0`] |> SIMP_RULE std_ss [];

val gc_move_thm = prove(
  ``gc_inv (h1,h2,a,n,heap:('a,'b) heap_element list,c,limit) heap0 /\
    (!ptr. (x = Pointer ptr) ==> isSomeDataOrForward (heap_lookup ptr heap)) ==>
    ?x3 h23 a3 n3 heap3 c3.
      (gc_move (x:'a heap_address,h2,a,n,heap,c,limit) = (ADDR_APPLY (heap_map1 heap3) x,h23,a3,n3,heap3,c3)) /\
      (!ptr. (x = Pointer ptr) ==> ptr IN FDOM (heap_map 0 heap3)) /\
      (!ptr. isSomeDataOrForward (heap_lookup ptr heap) =
             isSomeDataOrForward (heap_lookup ptr heap3)) /\
      ((heap_map 0 heap) SUBMAP (heap_map 0 heap3)) /\
      gc_inv (h1,h23,a3,n3,heap3,c3,limit) heap0``,
  Cases_on `x` \\ SIMP_TAC (srw_ss()) [gc_move_def,ADDR_APPLY_def]
  \\ SIMP_TAC std_ss [Once isSomeDataOrForward_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [isSomeForwardPointer_def] THEN1
   (FULL_SIMP_TAC (srw_ss()) [ADDR_APPLY_def] \\ IMP_RES_TAC heap_lookup_FLOOKUP
    \\ FULL_SIMP_TAC std_ss [FLOOKUP_DEF,heap_map1_def])
  \\ FULL_SIMP_TAC (srw_ss()) [isSomeDataElement_def,LET_DEF]
  \\ IMP_RES_TAC heap_lookup_SPLIT \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [gc_forward_ptr_thm]
  \\ `heap_map 0 (ha ++ [ForwardPointer a l] ++ hb) =
      heap_map 0 (ha ++ DataElement ys l d::hb) |+ (heap_length ha,a)` by
   (ONCE_REWRITE_TAC [GSYM (EVAL ``[x] ++ xs``)]
    \\ SIMP_TAC std_ss [APPEND_NIL,APPEND_ASSOC]
    \\ FULL_SIMP_TAC std_ss [heap_map_APPEND]
    \\ FULL_SIMP_TAC (srw_ss()) [heap_length_def,el_length_def]
    \\ FULL_SIMP_TAC (srw_ss()) [heap_map_def,SUM_APPEND]
    \\ FULL_SIMP_TAC (srw_ss()) [GSYM fmap_EQ_THM,heap_map_APPEND]
    \\ FULL_SIMP_TAC (srw_ss()) [EXTENSION] \\ STRIP_TAC THEN1 METIS_TAC []
    \\ FULL_SIMP_TAC (srw_ss()) [FUNION_DEF,FAPPLY_FUPDATE_THM] \\ STRIP_TAC
    \\ Cases_on `x = SUM (MAP el_length ha)` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [GSYM heap_length_def]
    \\ FULL_SIMP_TAC std_ss [FDOM_heap_map])
  \\ `~(heap_length ha IN FDOM (heap_map 0 (ha ++ DataElement ys l d::hb)))`
       by FULL_SIMP_TAC std_ss [NOT_IN_heap_map]
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC (srw_ss()) [heap_map1_def])
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC (srw_ss()) [])
  \\ STRIP_TAC THEN1 METIS_TAC [isSomeDataOrForward_lemma]
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [SUBMAP_DEF,FAPPLY_FUPDATE_THM]
    \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [gc_inv_def,heap_map1_def]
  \\ Q.ABBREV_TAC `ff = heap_map 0 (ha ++ DataElement ys l d::hb)`
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [heap_length_def,FILTER_APPEND,FILTER_APPEND,
      isForwardPointer_def,SUM_APPEND,el_length_def] \\ DECIDE_TAC)
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [heap_length_def,FILTER_APPEND,FILTER_APPEND,
      isForwardPointer_def,SUM_APPEND,el_length_def] \\ DECIDE_TAC)
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [heap_length_def,FILTER_APPEND,FILTER_APPEND,
      isForwardPointer_def,SUM_APPEND,el_length_def] \\ DECIDE_TAC)
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [heap_length_def,FILTER_APPEND,FILTER_APPEND,
      isForwardPointer_def,SUM_APPEND,el_length_def] \\ DECIDE_TAC)
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [heap_length_def,FILTER_APPEND,FILTER_APPEND,
      isForwardPointer_def,SUM_APPEND,el_length_def] \\ DECIDE_TAC)
  \\ STRIP_TAC THEN1 (METIS_TAC [heaps_similar_lemma])
  \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [EVERY_APPEND] \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC,heap_addresses_SNOC]
  \\ FULL_SIMP_TAC std_ss [FDOM_FUPDATE]
  \\ STRIP_TAC THEN1
   (`(heap_addresses 0 (h1 ++ h2) UNION {heap_length (h1 ++ h2)}) =
     (heap_length (h1 ++ h2) INSERT heap_addresses 0 (h1 ++ h2))` by ALL_TAC
    THEN1 (FULL_SIMP_TAC (srw_ss()) [EXTENSION] \\ METIS_TAC [])
    \\ `~(heap_length (h1 ++ h2) IN heap_addresses 0 (h1 ++ h2))` by
          FULL_SIMP_TAC std_ss [NOT_IN_heap_addresses]
    \\ IMP_RES_TAC BIJ_UPDATE
    \\ `(\a'. (ff |+ (heap_length ha,heap_length (h1 ++ h2))) ' a') =
        ((heap_length ha =+ heap_length (h1 ++ h2)) (\a. ff ' a))` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [FUN_EQ_THM,APPLY_UPDATE_THM,FAPPLY_FUPDATE_THM]
      \\ SRW_TAC [] []) \\ FULL_SIMP_TAC std_ss [])
  \\ NTAC 3 STRIP_TAC
  \\ Cases_on `i = heap_length ha` THEN1
   (`j = heap_length (h1 ++ h2)` by ALL_TAC
    THEN1 FULL_SIMP_TAC std_ss [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
    \\ FULL_SIMP_TAC std_ss []
    \\ `heap_lookup (heap_length ha) heap0 = SOME (DataElement ys l d)` by
     (IMP_RES_TAC heap_similar_Data_IMP
      \\ FULL_SIMP_TAC std_ss [heap_lookup_PREFIX])
    \\ FULL_SIMP_TAC (srw_ss()) [heap_lookup_PREFIX]
    \\ `~(heap_length (h1 ++ h2) < heap_length h1)` by ALL_TAC
    THEN1 (FULL_SIMP_TAC (srw_ss()) [heap_length_def,SUM_APPEND] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [])
  \\ `FLOOKUP ff i = SOME j` by ALL_TAC
  THEN1 FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
  \\ Q.PAT_ASSUM `!i j. bbb` (MP_TAC o Q.SPECL [`i`,`j`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC heap_lookup_EXTEND
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC ADDR_MAP_EQ
  \\ FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM] \\ METIS_TAC []);

val gc_move_list_thm = prove(
  ``!xs h2 a n heap c.
    gc_inv (h1,h2,a,n,heap:('a,'b) heap_element list,c,limit) heap0 /\
    (!ptr. MEM (Pointer ptr) (xs:'a heap_address list) ==> isSomeDataOrForward (heap_lookup ptr heap)) ==>
    ?h23 a3 n3 heap3 c3.
      (gc_move_list (xs,h2,a,n,heap,c,limit) = (ADDR_MAP (heap_map1 heap3) xs,h23,a3,n3,heap3,c3)) /\
      (!ptr. MEM (Pointer ptr) xs ==> ptr IN FDOM (heap_map 0 heap3)) /\
      (!ptr. isSomeDataOrForward (heap_lookup ptr heap) =
             isSomeDataOrForward (heap_lookup ptr heap3)) /\
      ((heap_map 0 heap) SUBMAP (heap_map 0 heap3)) /\
      gc_inv (h1,h23,a3,n3,heap3,c3,limit) heap0``,
  Induct THEN1 (FULL_SIMP_TAC std_ss [gc_move_list_def,ADDR_MAP_def,MEM,SUBMAP_REFL])
  \\ FULL_SIMP_TAC std_ss [MEM,gc_move_list_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Q.ABBREV_TAC `x = h` \\ POP_ASSUM (K ALL_TAC)
  \\ MP_TAC gc_move_thm \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `!h2 a. bbb` (MP_TAC o Q.SPECL [`h23`,`a3`,`n3`,`heap3`,`c3`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC SUBMAP_TRANS \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1
   (Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [ADDR_APPLY_def,ADDR_MAP_def]
    \\ FULL_SIMP_TAC std_ss [heap_map1_def,SUBMAP_DEF])
  \\ FULL_SIMP_TAC std_ss [SUBMAP_DEF] \\ METIS_TAC []);

val PULL_FORALL = METIS_PROVE [] ``(b ==> !x. P x) = !x. b ==> P x``

val APPEND_NIL_LEMMA = METIS_PROVE [APPEND_NIL] ``?xs1. xs = xs ++ xs1:'a list``

val gc_move_ALT = store_thm("gc_move_ALT",
  ``gc_move (ys,xs,a,n,heap,c,limit) =
      let (ys,xs1,x) = gc_move (ys,[],a,n,heap,c,limit) in
        (ys,xs++xs1,x)``,
  Cases_on `ys` \\ SIMP_TAC (srw_ss()) [gc_move_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `heap_lookup n' heap` \\ SIMP_TAC (srw_ss()) [LET_DEF]
  \\ Cases_on `x` \\ SIMP_TAC (srw_ss()) [LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FULL_SIMP_TAC std_ss []);

val gc_move_list_ALT = store_thm("gc_move_list_ALT",
  ``!ys xs a n heap c limit ys3 xs3 a3 n3 heap3 c3.
      gc_move_list (ys,xs,a,n,heap,c,limit) =
        let (ys,xs1,x) = gc_move_list (ys,[],a,n,heap,c,limit) in
          (ys,xs++xs1,x)``,
  Induct \\ SIMP_TAC std_ss [gc_move_list_def,LET_DEF,APPEND_NIL]
  \\ SIMP_TAC std_ss [Once gc_move_ALT,LET_DEF]
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]);

val gc_move_list_APPEND_lemma = prove(
  ``!ys xs a n heap c limit ys3 xs3 a3 n3 heap3 c3.
      (gc_move_list (ys,xs,a,n,heap,c,limit) = (ys3,xs3,a3,n3,heap3,c3)) ==>
      (?xs1. xs3 = xs ++ xs1)``,
  ONCE_REWRITE_TAC [gc_move_list_ALT] \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC] \\ METIS_TAC []);

val IMP_IMP = METIS_PROVE [] ``b /\ (b1 ==> b2) ==> (b ==> b1) ==> b2``

val heap_addresses_APPEND = prove(
  ``!xs ys n. heap_addresses n (xs ++ ys) =
              heap_addresses n xs UNION heap_addresses (n + heap_length xs) ys``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [APPEND,heap_addresses_def,heap_length_def]
  \\ FULL_SIMP_TAC (srw_ss()) [EXTENSION,DISJ_ASSOC,ADD_ASSOC]);

val LESS_IMP_heap_lookup = prove(
  ``!xs j ys. j < heap_length xs ==> (heap_lookup j (xs ++ ys) = heap_lookup j xs)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [heap_length_def,heap_lookup_def]
  \\ SRW_TAC [] [] \\ `j - el_length h < SUM (MAP el_length xs)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []);

val NOT_LESS_IMP_heap_lookup = prove(
  ``!xs j ys. ~(j < heap_length xs) ==>
              (heap_lookup j (xs ++ ys) = heap_lookup (j - heap_length xs) ys)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [heap_length_def,heap_lookup_def]
  \\ SRW_TAC [] [SUB_PLUS]
  THEN1 (Cases_on `h` \\ FULL_SIMP_TAC std_ss [el_length_def] \\ `F` by DECIDE_TAC)
  THEN1 (Cases_on `h` \\ FULL_SIMP_TAC std_ss [el_length_def] \\ `F` by DECIDE_TAC));

val heap_length_APPEND = store_thm("heap_length_APPEND",
  ``heap_length (xs ++ ys) = heap_length xs + heap_length ys``,
  SRW_TAC [] [heap_length_def,SUM_APPEND]);

val heap_similar_Data_IMP_DataOrForward = prove(
  ``!heap0 heap1 ptr.
      heaps_similar heap0 heap1 /\ isSomeDataElement (heap_lookup ptr heap0) ==>
      isSomeDataOrForward (heap_lookup ptr heap1)``,
  Induct \\ Cases_on `heap1` \\ FULL_SIMP_TAC (srw_ss()) [heaps_similar_def]
  \\ FULL_SIMP_TAC std_ss [heap_lookup_def]
  THEN1 (FULL_SIMP_TAC (srw_ss()) [isSomeDataElement_def,isSomeDataOrForward_def])
  \\ REPEAT GEN_TAC \\ Cases_on `ptr = 0` \\ FULL_SIMP_TAC std_ss [] THEN1
   (Cases_on `isForwardPointer h` \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC \\ Cases_on `h`
    \\ FULL_SIMP_TAC (srw_ss()) [isSomeDataElement_def,isSomeDataOrForward_def,
         isDataElement_def,isForwardPointer_def,isSomeForwardPointer_def])
  \\ STRIP_TAC \\ `(el_length h = el_length h')` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [] \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []
  THEN1 FULL_SIMP_TAC std_ss [isSomeDataElement_def]
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC);

val gc_move_loop_thm = prove(
  ``!h1 h2 a n heap c.
      gc_inv (h1,h2,a,n,heap:('a,'b) heap_element list,c,limit) heap0 ==>
      ?h13 a3 n3 heap3 c3.
        (gc_move_loop (h1,h2,a,n,heap,c,limit) = (h13,a3,n3,heap3,c3)) /\
      ((heap_map 0 heap) SUBMAP (heap_map 0 heap3)) /\
      gc_inv (h13,[],a3,n3,heap3,c3,limit) heap0``,
  completeInduct_on `limit - heap_length h1` \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ Cases_on `h2`
  \\ FULL_SIMP_TAC std_ss [gc_move_loop_def,SUBMAP_REFL]
  \\ `isDataElement h` by FULL_SIMP_TAC (srw_ss()) [gc_inv_def]
  \\ FULL_SIMP_TAC std_ss [isDataElement_def]
  \\ `~(limit <= heap_length h1)` by ALL_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [gc_inv_def,heap_length_def,SUM_APPEND]
    \\ FULL_SIMP_TAC std_ss [el_length_def] \\ DECIDE_TAC)
  \\ `~(limit < heap_length (h1 ++ DataElement ys l d::t))` by ALL_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [gc_inv_def,heap_length_def,SUM_APPEND]
    \\ FULL_SIMP_TAC std_ss [el_length_def] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ `!ptr. MEM (Pointer ptr) (ys:'a heap_address list) ==>
            isSomeDataOrForward (heap_lookup ptr heap)` by ALL_TAC THEN1
   (REPEAT STRIP_TAC \\ Q.PAT_ASSUM `!x1 x2 x3. bbb` (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [gc_inv_def]
    \\ `?i. FLOOKUP (heap_map 0 heap) i = SOME (heap_length h1)` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [FLOOKUP_DEF,BIJ_DEF,SURJ_DEF,heap_map1_def]
      \\ Q.PAT_ASSUM `!xx.bbb` (K ALL_TAC) \\ Q.PAT_ASSUM `!xx.bbb` MATCH_MP_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [heap_addresses_APPEND,heap_addresses_def])
    \\ RES_TAC \\ `~(heap_length h1 < heap_length h1)` by DECIDE_TAC
    \\ IMP_RES_TAC NOT_LESS_IMP_heap_lookup
    \\ FULL_SIMP_TAC (srw_ss()) [heap_lookup_def]
    \\ FULL_SIMP_TAC std_ss [heap_ok_def]
    \\ IMP_RES_TAC heap_lookup_MEM \\ RES_TAC
    \\ IMP_RES_TAC heap_similar_Data_IMP_DataOrForward)
  \\ MP_TAC (Q.SPECL [`ys`,`DataElement ys l d::t`,`a`,`n`,`heap`,`c`] gc_move_list_thm)
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ IMP_RES_TAC gc_move_list_APPEND_lemma
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
  \\ Q.PAT_ASSUM `!limit h1 h2. bbb` (MP_TAC o Q.SPECL [`limit`,
       `h1 ++ [DataElement (ADDR_MAP (heap_map1 (heap3:('a,'b) heap_element list)) ys) l d]`,`t ++ xs1`,
       `a3`,`n3`,`heap3`,`c3`]) \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IMP_IMP \\ REVERSE STRIP_TAC
  THEN1 (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC SUBMAP_TRANS)
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [heap_length_def,el_length_def,SUM_APPEND] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [gc_inv_def,EVERY_DEF,EVERY_APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [heap_length_def,SUM_APPEND,el_length_def])
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC (srw_ss()) [isDataElement_def])
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [heap_addresses_APPEND,heap_addresses_def,el_length_def])
  \\ REPEAT STRIP_TAC
  \\ Q.PAT_ASSUM `!i j. bbb` (MP_TAC o Q.SPECL [`i`,`j`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `j < heap_length h1` THEN1
   (IMP_RES_TAC LESS_IMP_heap_lookup \\ FULL_SIMP_TAC (srw_ss()) []
    \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) [heap_length_def,SUM_APPEND]
    \\ `F` by DECIDE_TAC)
  \\ IMP_RES_TAC NOT_LESS_IMP_heap_lookup \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [heap_lookup_def]
  \\ Cases_on `j <= heap_length h1` \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (FULL_SIMP_TAC std_ss [heap_length_APPEND] \\ SRW_TAC [] []
    \\ FULL_SIMP_TAC (srw_ss()) [heap_length_def,el_length_def] \\ `F` by DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [el_length_def]
  \\ `0 < l+1` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `j < heap_length h1 + (l + 1)` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [heap_length_APPEND]
  \\ FULL_SIMP_TAC (srw_ss()) [heap_length_def,el_length_def]);

val FILTER_LEMMA = prove(
  ``!heap. (FILTER isForwardPointer heap = []) ==>
           (FILTER (\h. ~isForwardPointer h) heap = heap)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] []);

val heaps_similar_REFL = prove(
  ``!xs. (FILTER isForwardPointer xs = []) ==> heaps_similar xs xs``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [heaps_similar_def] \\ SRW_TAC [] []);

val heap_map_EMPTY = prove(
  ``!xs n. (FILTER isForwardPointer xs = []) ==> (FDOM (heap_map n xs) = {})``,
  Induct \\ TRY (Cases_on `h`)
  \\ FULL_SIMP_TAC (srw_ss()) [heap_map_def,isForwardPointer_def]);

val gc_inv_init = prove(
  ``gc_inv ([],[],0,limit,heap,T,limit) heap = heap_ok heap limit``,
  FULL_SIMP_TAC std_ss [gc_inv_def] \\ Cases_on `heap_ok heap limit`
  \\ FULL_SIMP_TAC (srw_ss()) [heap_addresses_def,heap_length_def]
  \\ FULL_SIMP_TAC std_ss [heap_ok_def]
  \\ IMP_RES_TAC FILTER_LEMMA \\ FULL_SIMP_TAC std_ss [heap_length_def]
  \\ FULL_SIMP_TAC (srw_ss()) [heaps_similar_REFL,heap_map_EMPTY,FLOOKUP_DEF]
  \\ FULL_SIMP_TAC (srw_ss()) [BIJ_DEF,INJ_DEF,SURJ_DEF]);

val full_gc_thm = prove(
  ``roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) limit ==>
    ?heap2 a2 heap3.
      (full_gc (roots:'a heap_address list,heap,limit) =
         (ADDR_MAP (heap_map1 heap3) roots,heap2,a2,T)) /\
      (!ptr. MEM (Pointer ptr) roots ==> ptr IN FDOM (heap_map 0 heap3)) /\
      gc_inv (heap2,[],a2,limit - a2,heap3,T,limit) heap``,
  SIMP_TAC std_ss [Once (GSYM gc_inv_init)]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [full_gc_def]
  \\ MP_TAC (Q.SPECL [`roots`,`[]`,`0`,`limit`,`heap`,`T`] gc_move_list_thm |> Q.INST [`h1`|->`[]`,`heap0`|->`heap`])
  \\ FULL_SIMP_TAC std_ss [] \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [roots_ok_def] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [isSomeDataOrForward_def,isSomeDataElement_def])
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ MP_TAC (Q.SPECL [`[]`,`h23`,`a3`,`n3`,`heap3`,`c3`] gc_move_loop_thm |> Q.INST [`heap0`|->`heap`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `heap3'` \\ FULL_SIMP_TAC std_ss []
  \\ `c3'` by FULL_SIMP_TAC std_ss [gc_inv_def] \\ FULL_SIMP_TAC std_ss []
  \\ `n3' = limit - a3'` by (FULL_SIMP_TAC std_ss [gc_inv_def] \\ DECIDE_TAC)
  \\ `!ptr. MEM (Pointer ptr) roots ==> ptr IN FDOM (heap_map 0 heap3')` by ALL_TAC
  THEN1 FULL_SIMP_TAC std_ss [SUBMAP_DEF,heap_map1_def]
  \\ FULL_SIMP_TAC std_ss [] \\ REVERSE (REPEAT STRIP_TAC)
  THEN1 (FULL_SIMP_TAC std_ss [gc_inv_def,APPEND_NIL])
  THEN1 (FULL_SIMP_TAC std_ss [gc_inv_def,APPEND_NIL])
  \\ MATCH_MP_TAC ADDR_MAP_EQ
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [SUBMAP_DEF,heap_map1_def]);

val MEM_ADDR_MAP = prove(
  ``!xs f ptr. MEM (Pointer ptr) (ADDR_MAP f xs) ==>
               ?y. MEM (Pointer y) xs /\ (f y = ptr)``,
  Induct \\ TRY (Cases_on `h`) \\ FULL_SIMP_TAC (srw_ss()) [ADDR_MAP_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ METIS_TAC []);

val heap_length_heap_expand = prove(
  ``!n. heap_length (heap_expand n) = n``,
  Cases \\ EVAL_TAC \\ FULL_SIMP_TAC (srw_ss()) [el_length_def,ADD1]);

val EVERY_isDataElement_IMP_LEMMA = prove(
  ``!heap2. EVERY isDataElement heap2 ==> (FILTER isForwardPointer heap2 = [])``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [isDataElement_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [isForwardPointer_def]);

val heap_lookup_LESS = prove(
  ``!xs n. (heap_lookup n xs = SOME x) ==> n < heap_length xs``,
  Induct \\ FULL_SIMP_TAC std_ss [heap_lookup_def] \\ SRW_TAC [] []
  \\ RES_TAC \\ Cases_on `h` \\ FULL_SIMP_TAC (srw_ss())
      [heap_length_def,el_length_def] \\ DECIDE_TAC);

val isSome_heap_looukp_IMP_APPEND = prove(
  ``!xs ptr. isSomeDataElement (heap_lookup ptr xs) ==>
             isSomeDataElement (heap_lookup ptr (xs ++ ys))``,
  FULL_SIMP_TAC std_ss [isSomeDataElement_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC heap_lookup_LESS \\ IMP_RES_TAC LESS_IMP_heap_lookup
  \\ FULL_SIMP_TAC (srw_ss()) []);

val MEM_IMP_heap_lookup = prove(
  ``!xs x. MEM x xs ==> ?j. (heap_lookup j xs = SOME x)``,
  Induct \\ FULL_SIMP_TAC std_ss [MEM,heap_lookup_def,heap_addresses_def]
  \\ SRW_TAC [] [] \\ RES_TAC THEN1 METIS_TAC []
  \\ Q.EXISTS_TAC `j + el_length h` \\ FULL_SIMP_TAC std_ss [] \\ SRW_TAC [] []
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [el_length_def] \\ `F` by DECIDE_TAC);

val heap_lookup_IMP_heap_addresses = prove(
  ``!xs n x j. (heap_lookup j xs = SOME x) ==> n + j IN heap_addresses n xs``,
  Induct \\ FULL_SIMP_TAC std_ss [MEM,heap_lookup_def,heap_addresses_def]
  \\ SRW_TAC [] [] \\ RES_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPEC `n + el_length h`)
  \\ `n + el_length h + (j - el_length h) = n + j` by DECIDE_TAC
  \\ METIS_TAC []) |> Q.SPECL [`xs`,`0`] |> SIMP_RULE std_ss [] |> GEN_ALL;

val full_gc_LENGTH = prove(
  ``roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) limit ==>
    ?roots2 heap2 a2.
      (full_gc (roots:'a heap_address list,heap,limit) =
      (roots2,heap2,heap_length heap2,T))``,
  REPEAT STRIP_TAC \\ MP_TAC full_gc_thm \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [gc_inv_def,APPEND_NIL]);

val full_gc_ok = prove(
  ``roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) limit ==>
    ?roots2 heap2 a2.
      (full_gc (roots:'a heap_address list,heap,limit) = (roots2,heap2,a2,T)) /\
      a2 <= limit /\ roots_ok roots2 (heap2 ++ heap_expand (limit - a2)) /\
      heap_ok (heap2 ++ heap_expand (limit - a2)) limit``,
  REPEAT STRIP_TAC \\ MP_TAC full_gc_thm \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [gc_inv_def]
  \\ FULL_SIMP_TAC std_ss [APPEND_NIL] \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ SIMP_TAC std_ss [roots_ok_def,heap_ok_def]
  \\ REPEAT STRIP_TAC THEN1
   (IMP_RES_TAC MEM_ADDR_MAP \\ RES_TAC \\ FULL_SIMP_TAC std_ss [heap_map1_def]
    \\ `FLOOKUP (heap_map 0 heap3) y = SOME ptr` by ALL_TAC
    THEN1 FULL_SIMP_TAC std_ss [FLOOKUP_DEF]
    \\ RES_TAC \\ FULL_SIMP_TAC (srw_ss()) [isSomeDataElement_def]
    \\ IMP_RES_TAC heap_lookup_EXTEND \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1
   (FULL_SIMP_TAC std_ss [heap_length_APPEND,heap_length_heap_expand] \\ DECIDE_TAC)
  THEN1
   (FULL_SIMP_TAC std_ss [FILTER_APPEND,EVERY_isDataElement_IMP_LEMMA,APPEND]
    \\ Cases_on `(heap_length (FILTER (\h. ~isForwardPointer h) heap3))`
    \\ FULL_SIMP_TAC (srw_ss()) [heap_expand_def,isForwardPointer_def])
  \\ REVERSE (FULL_SIMP_TAC std_ss [MEM_APPEND]) THEN1
   (Cases_on `(heap_length (FILTER (\h. ~isForwardPointer h) heap3))`
    \\ FULL_SIMP_TAC (srw_ss()) [heap_expand_def,isForwardPointer_def])
  \\ `?j. heap_lookup j heap2 = SOME (DataElement xs l d)` by
         METIS_TAC [MEM_IMP_heap_lookup]
  \\ `?i. (FLOOKUP (heap_map 0 heap3) i = SOME j)` by ALL_TAC THEN1
   (IMP_RES_TAC heap_lookup_IMP_heap_addresses
    \\ FULL_SIMP_TAC std_ss [BIJ_DEF,SURJ_DEF,heap_map1_def,FLOOKUP_DEF]
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ RES_TAC \\ NTAC 2 (POP_ASSUM MP_TAC) \\ FULL_SIMP_TAC (srw_ss()) []
  \\ STRIP_TAC \\ `j < heap_length heap2` by (IMP_RES_TAC heap_lookup_LESS)
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ IMP_RES_TAC MEM_ADDR_MAP
  \\ `y IN FDOM (heap_map 0 heap3)` by RES_TAC
  \\ `(FLOOKUP (heap_map 0 heap3) y = SOME (heap_map1 heap3 y))` by ALL_TAC
  THEN1 FULL_SIMP_TAC std_ss [FLOOKUP_DEF,heap_map1_def]
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ Q.PAT_ASSUM `!i j. bbb` (MP_TAC o Q.SPECL [`y`,`ptr`])
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ MATCH_MP_TAC isSome_heap_looukp_IMP_APPEND \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [isSomeDataElement_def]);

val gc_related_def = Define `
  gc_related (f:num|->num) heap1 heap2 =
    INJ (FAPPLY f) (FDOM f) { a | isSomeDataElement (heap_lookup a heap2) } /\
    !i xs l d.
      i IN FDOM f /\ (heap_lookup i heap1 = SOME (DataElement xs l d)) ==>
      (heap_lookup (f ' i) heap2 = SOME (DataElement (ADDR_MAP (FAPPLY f) xs) l d)) /\
      !ptr. MEM (Pointer ptr) xs ==> ptr IN FDOM f`;

val full_gc_related = prove(
  ``roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) limit ==>
    ?heap2 a2 f.
      (full_gc (roots:'a heap_address list,heap,limit) =
         (ADDR_MAP (FAPPLY f) roots,heap2,a2,T)) /\
      (!ptr. MEM (Pointer ptr) roots ==> ptr IN FDOM f) /\
      gc_related f heap (heap2 ++ heap_expand (limit - a2))``,
  STRIP_TAC \\ MP_TAC full_gc_thm \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `heap_map 0 heap3`
  \\ `(FAPPLY (heap_map 0 heap3)) = heap_map1 heap3` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [heap_map1_def,FUN_EQ_THM])
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [gc_related_def,gc_inv_def,BIJ_DEF]
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [INJ_DEF] \\ REPEAT STRIP_TAC
    \\ `(FLOOKUP (heap_map 0 heap3) x = SOME (heap_map1 heap3 x))` by ALL_TAC
    THEN1 FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF,heap_map1_def]
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC heap_lookup_LESS
    \\ IMP_RES_TAC heap_lookup_EXTEND \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [isSomeDataElement_def])
  \\ NTAC 5 STRIP_TAC
  \\ `(FLOOKUP (heap_map 0 heap3) i = SOME (heap_map1 heap3 i))` by ALL_TAC
  THEN1 FULL_SIMP_TAC std_ss [FLOOKUP_DEF]
  \\ RES_TAC \\ FULL_SIMP_TAC (srw_ss()) [APPEND_NIL]
  \\ IMP_RES_TAC heap_lookup_LESS \\ IMP_RES_TAC heap_lookup_EXTEND
  \\ FULL_SIMP_TAC std_ss []);

(* refinement invariant *)

val small_int_def = Define `
  small_int i = 0 <= i /\ (i:int) < & (2 ** 62)`;

val mw_def = tDefine "mw" `
  mw n = if n = 0 then []:'a word list else
           n2w (n MOD dimword (:'a)) :: mw (n DIV dimword(:'a))`
   (WF_REL_TAC `measure I`
    \\ SIMP_TAC std_ss [MATCH_MP DIV_LT_X ZERO_LT_dimword,ONE_LT_dimword]
    \\ DECIDE_TAC);

val _ = Hol_datatype `tag = BlockTag of num | RefTag | NumTag of bool`;

val DataOnly_def = Define `
  DataOnly b xs = DataElement [] (LENGTH xs) (NumTag b,xs)`;

val BlockRep_def = Define `
  BlockRep tag xs = DataElement xs (LENGTH xs) (BlockTag tag,[])`;

val bc_value_size_LEMMA = prove(
  ``!vs v. MEM v vs ==> bc_value_size v <= bc_value1_size vs``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [bc_value_size_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val _ = type_abbrev("ml_el",``:('a word, tag # ('b word list)) heap_element``);
val _ = type_abbrev("ml_heap",``:('a,'b) ml_el list``);

val EVERY2_cong = store_thm("EVERY2_cong",
  ``!l1 l1' l2 l2' P P'.
      (l1 = l1') /\ (l2 = l2') /\
      (!x y. MEM x l1' /\ MEM y l2' ==> (P x y = P' x y)) ==>
      (EVERY2 P l1 l2 = EVERY2 P' l1' l2')``,
  Induct \\ Cases_on `l2'` \\ SIMP_TAC (srw_ss()) [EVERY2_def] \\ METIS_TAC[])
val _ = DefnBase.export_cong "EVERY2_cong"

val bc_value_inv_def = tDefine "bc_value_inv" `
  (bc_value_inv (Number i) (x,f,heap:('a,'b) ml_heap) =
     if small_int i then (x = Data ((2w * n2w (Num i)):'a word)) else
       ?ptr. (x = Pointer ptr) /\
             (heap_lookup ptr heap =
                SOME (DataOnly (i < 0) ((mw (Num i)):'b word list)))) /\
  (bc_value_inv (CodePtr n) (x,f,heap) =
     (x = Data (n2w n)) /\ n < dimword (:'a)) /\
  (bc_value_inv (RefPtr n) (x,f,heap) =
     (x = Pointer (f ' n)) /\ n IN FDOM f) /\
  (bc_value_inv (Block n vs) (x,f,heap) =
     if vs = [] then (x = Data ((2w * n2w n + 1w):'a word)) /\ (n < 2 ** 62) else
       ?ptr xs.
         EVERY2 (\v x. bc_value_inv v (x,f,heap)) vs xs /\
         (x = Pointer ptr) /\
         (heap_lookup ptr heap =
            SOME (BlockRep n xs))) /\
  (bc_value_inv (StackPtr n) (x,f,heap) = F)`
 (WF_REL_TAC `measure (bc_value_size o FST)` \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC bc_value_size_LEMMA \\ DECIDE_TAC);

val get_refs_def = tDefine "get_refs" `
  (get_refs (Number _) = []) /\
  (get_refs (CodePtr _) = []) /\
  (get_refs (RefPtr p) = [p]) /\
  (get_refs (Block tag vs) = FLAT (MAP get_refs vs))`
 (WF_REL_TAC `measure (bc_value_size)` \\ REPEAT STRIP_TAC \\ Induct_on `vs`
  \\ SRW_TAC [] [bc_value_size_def] \\ RES_TAC \\ DECIDE_TAC);

val ref_edge_def = Define `
  ref_edge refs x y = x IN FDOM refs /\ MEM y (get_refs (refs ' x))`;

val reachable_refs_def = Define `
  reachable_refs roots refs t =
    ?x r. MEM x roots /\ MEM r (get_refs x) /\ RTC (ref_edge refs) r t`;

val RefBlock_def = Define `
  RefBlock x = DataElement [x] 1 (RefTag,[])`;

val bc_ref_inv_def = Define `
  bc_ref_inv n refs (f,heap) =
    n IN FDOM f /\ n IN FDOM refs /\
    ?y. (heap_lookup (FAPPLY f n) heap = SOME (RefBlock y)) /\
        bc_value_inv (FAPPLY refs n) (y,f,heap)`;

val bc_stack_ref_inv_def = Define `
  bc_stack_ref_inv stack (refs:num|->bc_value) (roots, heap) =
    ?f. INJ (FAPPLY f) (FDOM f) { a | isSomeDataElement (heap_lookup a heap) } /\
        FDOM f SUBSET FDOM refs /\
        EVERY2 (\v x. bc_value_inv v (x,f,heap)) stack roots /\
        !n. reachable_refs stack refs n ==> bc_ref_inv n refs (f,heap)`;

val unused_space_inv_def = Define `
  unused_space_inv ptr l heap =
    l <> 0 ==> (heap_lookup ptr heap = SOME (Unused (l-1)))`;

val abs_ml_inv_def = Define `
  abs_ml_inv stack refs (roots,heap,a,sp) limit =
    roots_ok roots heap /\ heap_ok heap limit /\
    unused_space_inv a sp heap /\
    bc_stack_ref_inv stack refs (roots,heap)`;

(* Prove refinement is maintained past GC calls *)

val LENGTH_ADDR_MAP = prove(
  ``!xs f. LENGTH (ADDR_MAP f xs) = LENGTH xs``,
  Induct \\ TRY (Cases_on `h`) \\ SRW_TAC [] [ADDR_MAP_def]);

val PULL_EXISTS = METIS_PROVE [] ``(((?x. P x) ==> Q) = !x. P x ==> Q) /\
                                   ((?x. P x) /\ Q = ?x. P x /\ Q)``

val MEM_IMP_bc_value_size = prove(
  ``!l a. MEM a l ==> bc_value_size a < 1 + bc_value1_size l``,
  Induct \\ FULL_SIMP_TAC std_ss [MEM,bc_value_size_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ DECIDE_TAC);

val EL_ADDR_MAP = prove(
  ``!xs n f.
      n < LENGTH xs ==> (EL n (ADDR_MAP f xs) = ADDR_APPLY f (EL n xs))``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [] \\ Cases_on `n` \\ Cases_on `h`
  \\ FULL_SIMP_TAC (srw_ss()) [ADDR_MAP_def,ADDR_APPLY_def]);

val EVERY2_EVERY = prove(
  ``!xs ys f.
      EVERY2 f xs ys <=>
      (LENGTH xs = LENGTH ys) /\ EVERY (UNCURRY f) (ZIP (xs,ys))``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);

val bc_value_inv_related = prove(
  ``!w x f.
      gc_related g heap1 heap2 /\
      (!ptr. (x = Pointer ptr) ==> ptr IN FDOM g) /\
      bc_value_inv w (x,f,heap1) ==>
      bc_value_inv w (ADDR_APPLY (FAPPLY g) x,g f_o_f f,heap2) /\
      EVERY (\n. f ' n IN FDOM g) (get_refs w)``,
  completeInduct_on `bc_value_size w` \\ NTAC 5 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ Cases_on `w` THEN1
   (FULL_SIMP_TAC std_ss [bc_value_inv_def,get_refs_def,EVERY_DEF]
    \\ Cases_on `small_int i`
    \\ FULL_SIMP_TAC (srw_ss()) [ADDR_APPLY_def,DataOnly_def]
    \\ FULL_SIMP_TAC std_ss [gc_related_def] \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [ADDR_MAP_def])
  THEN1
   (FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ Cases_on `l = []` \\ FULL_SIMP_TAC std_ss []
    THEN1 (FULL_SIMP_TAC (srw_ss()) [get_refs_def,ADDR_APPLY_def])
    \\ FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ FULL_SIMP_TAC std_ss [gc_related_def] \\ RES_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [] \\ NTAC 2 (POP_ASSUM MP_TAC)
    \\ FULL_SIMP_TAC std_ss [LENGTH_ADDR_MAP] \\ STRIP_TAC
    \\ REVERSE STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [get_refs_def,EVERY_MEM,MEM_FLAT,PULL_EXISTS,MEM_MAP]
      \\ FULL_SIMP_TAC std_ss [bc_value_size_def] \\ REPEAT STRIP_TAC
      \\ Q.MATCH_ASSUM_RENAME_TAC `MEM k (get_f a)` []
      \\ IMP_RES_TAC MEM_IMP_bc_value_size
      \\ `bc_value_size a < 1 + (n + bc_value1_size l)` by DECIDE_TAC
      \\ `?l1 l2. l = l1 ++ a::l2` by METIS_TAC [MEM_SPLIT]
      \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC EVERY2_SPLIT_ALT
      \\ FULL_SIMP_TAC std_ss [MEM_APPEND,MEM]
      \\ RES_TAC \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [EVERY2_EVERY,LENGTH_ADDR_MAP,EVERY_MEM,FORALL_PROD]
    \\ Q.PAT_ASSUM `LENGTH l = LENGTH xs` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [MEM_ZIP,LENGTH_ADDR_MAP,PULL_EXISTS]
    \\ STRIP_TAC \\ STRIP_TAC
    \\ Q.MATCH_ASSUM_RENAME_TAC `t < LENGTH xs` [] \\ RES_TAC
    \\ `MEM (EL t l) l` by (FULL_SIMP_TAC std_ss [MEM_EL] \\ METIS_TAC [])
    \\ `MEM (EL t xs) xs` by (FULL_SIMP_TAC std_ss [MEM_EL] \\ METIS_TAC [])
    \\ `(!ptr. (EL t xs = Pointer ptr) ==> ptr IN FDOM g)` by METIS_TAC []
    \\ `bc_value_size (EL t l)  < bc_value_size (Block n l)` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [bc_value_size_def]
      \\ IMP_RES_TAC MEM_IMP_bc_value_size \\ DECIDE_TAC)
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [EL_ADDR_MAP])
  THEN1
    (FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def,ADDR_APPLY_def,get_refs_def])
  THEN1
    (FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def,ADDR_APPLY_def]
     \\ `n IN FDOM (g f_o_f f)` by ALL_TAC \\ ASM_SIMP_TAC std_ss []
     \\ FULL_SIMP_TAC (srw_ss()) [f_o_f_DEF,get_refs_def])
  THEN1
    (FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def]));

val bc_ref_inv_related = prove(
  ``gc_related g heap1 heap2 /\
    bc_ref_inv n refs (f,heap1) /\ (f ' n) IN FDOM g ==>
    bc_ref_inv n refs (g f_o_f f,heap2)``,
  FULL_SIMP_TAC std_ss [bc_ref_inv_def] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [f_o_f_DEF,gc_related_def,RefBlock_def] \\ RES_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ Q.EXISTS_TAC `ADDR_APPLY (FAPPLY g) y`
  \\ STRIP_TAC
  THEN1 (Cases_on `y` \\ FULL_SIMP_TAC std_ss [ADDR_MAP_def,ADDR_APPLY_def])
  \\ `gc_related g heap1 heap2` by ALL_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [gc_related_def] \\ METIS_TAC [])
  \\ IMP_RES_TAC bc_value_inv_related \\ METIS_TAC []);

val RTC_lemma = prove(
  ``!r n. RTC (ref_edge refs) r n ==>
          (!m. RTC (ref_edge refs) r m ==> bc_ref_inv m refs (f,heap)) /\
          gc_related g heap heap2 /\
          f ' r IN FDOM g ==> f ' n IN FDOM g``,
  HO_MATCH_MP_TAC RTC_INDUCT \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `bb ==> bbb` MATCH_MP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC \\ Q.PAT_ASSUM `!x.bb` MATCH_MP_TAC \\ METIS_TAC [RTC_CASES1])
  \\ `RTC (ref_edge refs) r r' /\ RTC (ref_edge refs) r r` by METIS_TAC [RTC_CASES1]
  \\ RES_TAC \\ Q.PAT_ASSUM `!x.bb` (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [bc_ref_inv_def,RefBlock_def]
  \\ `!ptr. MEM (Pointer ptr) [y] ==> ptr IN FDOM g` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [gc_related_def] \\ RES_TAC)
  \\ FULL_SIMP_TAC std_ss [MEM]
  \\ POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ])
  \\ `EVERY (\n. f ' n IN FDOM g) (get_refs (refs ' r))` by ALL_TAC
  THEN1 (IMP_RES_TAC bc_value_inv_related)
  \\ FULL_SIMP_TAC std_ss [ref_edge_def,EVERY_MEM]);

val reachable_refs_lemma = prove(
  ``gc_related g heap heap2 /\
    EVERY2 (\v x. bc_value_inv v (x,f,heap)) stack roots /\
    (!n. reachable_refs stack refs n ==> bc_ref_inv n refs (f,heap)) /\
    (!ptr. MEM (Pointer ptr) roots ==> ptr IN FDOM g) ==>
    (!n. reachable_refs stack refs n ==> n IN FDOM f /\ (f ' n) IN FDOM g)``,
  NTAC 3 STRIP_TAC \\ FULL_SIMP_TAC std_ss [reachable_refs_def,PULL_EXISTS]
  \\ `?xs1 xs2. stack = xs1 ++ x::xs2` by METIS_TAC [MEM_SPLIT]
  \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC EVERY2_SPLIT_ALT
  \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND]
  \\ `EVERY (\n. f ' n IN FDOM g) (get_refs x)` by METIS_TAC [bc_value_inv_related]
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM] \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `n IN FDOM f` by FULL_SIMP_TAC std_ss [bc_ref_inv_def]
  \\ FULL_SIMP_TAC std_ss []
  \\ `bc_ref_inv r refs (f,heap)` by METIS_TAC [RTC_REFL]
  \\ `(!m. RTC (ref_edge refs) r m ==> bc_ref_inv m refs (f,heap))` by ALL_TAC
  THEN1 METIS_TAC [] \\ IMP_RES_TAC RTC_lemma);

val bc_stack_ref_inv_related = prove(
  ``gc_related g heap1 heap2 /\
    bc_stack_ref_inv stack refs (roots,heap1) /\
    (!ptr. MEM (Pointer ptr) roots ==> ptr IN FDOM g) ==>
    bc_stack_ref_inv stack refs (ADDR_MAP (FAPPLY g) roots,heap2)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_stack_ref_inv_def]
  \\ Q.EXISTS_TAC `g f_o_f f` \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [INJ_DEF,gc_related_def,f_o_f_DEF])
  THEN1 (FULL_SIMP_TAC (srw_ss()) [f_o_f_DEF,SUBSET_DEF])
  THEN1
   (FULL_SIMP_TAC std_ss [ONCE_REWRITE_RULE [CONJ_COMM] EVERY2_EVERY,
      LENGTH_ADDR_MAP,EVERY_MEM,MEM_ZIP,PULL_EXISTS] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [MEM_ZIP,PULL_EXISTS]
    \\ `MEM (EL n roots) roots` by (FULL_SIMP_TAC std_ss [MEM_EL] \\ METIS_TAC [])
    \\ `(!ptr. (EL n roots = Pointer ptr) ==> ptr IN FDOM g)` by METIS_TAC []
    \\ IMP_RES_TAC bc_value_inv_related \\ IMP_RES_TAC EL_ADDR_MAP
    \\ FULL_SIMP_TAC std_ss [])
  \\ MATCH_MP_TAC bc_ref_inv_related \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC [reachable_refs_lemma]);

val full_gc_thm = store_thm("full_gc_thm",
  ``abs_ml_inv stack refs (roots,heap,a,sp) limit ==>
    ?roots2 heap2 a2.
      (full_gc (roots,heap,limit) = (roots2,heap2,a2,T)) /\
      abs_ml_inv stack refs
        (roots2,heap2 ++ heap_expand (limit - a2),a2,limit - a2) limit /\
      (heap_length heap2 = a2)``,
  SIMP_TAC std_ss [abs_ml_inv_def,GSYM CONJ_ASSOC]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC full_gc_related \\ NTAC 3 (POP_ASSUM (K ALL_TAC))
  \\ `heap_length heap2 = a2` by ALL_TAC
  THEN1 (IMP_RES_TAC full_gc_LENGTH \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ `unused_space_inv a2 (limit - a2) (heap2 ++ heap_expand (limit - a2))` by
   (FULL_SIMP_TAC std_ss [unused_space_inv_def] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [heap_expand_def]
    \\ METIS_TAC [heap_lookup_PREFIX])
  \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC THEN1
   (Q.PAT_ASSUM `full_gc (roots,heap,limit) = xxx` (ASSUME_TAC o GSYM)
    \\ IMP_RES_TAC full_gc_ok \\ NTAC 3 (POP_ASSUM (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ MATCH_MP_TAC (GEN_ALL bc_stack_ref_inv_related) \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `heap` \\ FULL_SIMP_TAC std_ss []);

(* Write to unused heap space is fine, e.g. cons *)

val heap_store_def = Define `
  (heap_store a y [] = ([],F)) /\
  (heap_store a y (x::xs) =
    if a = 0 then (y ++ xs, el_length x = heap_length y) else
    if a < el_length x then (x::xs,F) else
      let (xs,c) = heap_store (a - el_length x) y xs in
        (x::xs,c))`

val isUnused_def = Define `
  isUnused x = ?k. x = Unused k`;

val isSomeUnused_def = Define `
  isSomeUnused x = ?k. x = SOME (Unused k)`;

val heap_store_unused_def = Define `
  heap_store_unused a sp x xs =
    if (heap_lookup a xs = SOME (Unused (sp-1))) /\ el_length x <= sp then
      heap_store a (heap_expand (sp - el_length x) ++ [x]) xs
    else (xs,F)`;

val heap_store_lemma = store_thm("heap_store_lemma",
  ``!xs y x ys.
      heap_store (heap_length xs) y (xs ++ x::ys) =
      (xs ++ y ++ ys, heap_length y = el_length x)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [heap_length_def,heap_store_def,LET_DEF]
  THEN1 DECIDE_TAC \\ REPEAT STRIP_TAC
  \\ `el_length h <> 0` by (Cases_on `h` \\ FULL_SIMP_TAC std_ss [el_length_def])
  \\ `~(el_length h + SUM (MAP el_length xs) < el_length h)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []);

val heap_store_rel_def = Define `
  heap_store_rel heap heap2 =
    (!ptr. isSomeDataElement (heap_lookup ptr heap) ==>
           (heap_lookup ptr heap2 = heap_lookup ptr heap))`;

val isSomeDataElement_heap_lookup_lemma1 = prove(
  ``isSomeDataElement (heap_lookup n (Unused k :: xs)) =
    k < n /\ isSomeDataElement (heap_lookup (n-(k+1)) xs)``,
  SRW_TAC [] [heap_lookup_def,isSomeDataElement_def,el_length_def,NOT_LESS]
  THEN1 (DISJ1_TAC \\ DECIDE_TAC)
  \\ `k < n` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []);

val isSomeDataElement_heap_lookup_lemma2 = prove(
  ``isSomeDataElement (heap_lookup n (heap_expand k ++ xs)) =
    k <= n /\ isSomeDataElement (heap_lookup (n-k) xs)``,
  SRW_TAC [] [heap_expand_def,isSomeDataElement_heap_lookup_lemma1]
  \\ IMP_RES_TAC (DECIDE ``sp <> 0 ==> (sp - 1 + 1 = sp:num)``)
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `isSomeDataElement (heap_lookup (n - k) xs)`
  \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val isSomeDataElement_heap_lookup_lemma3 = prove(
  ``n <> 0 ==>
    (isSomeDataElement (heap_lookup n (x::xs)) =
     el_length x <= n /\ isSomeDataElement (heap_lookup (n - el_length x) xs))``,
  SRW_TAC [] [heap_expand_def,heap_lookup_def,isSomeDataElement_def]
  THEN1 (DISJ1_TAC \\ DECIDE_TAC)
  \\ `el_length x <= n` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []);

val IMP_heap_store_unused = prove(
  ``unused_space_inv a sp (heap:('a,'b) heap_element list) /\ el_length x <= sp ==>
    ?heap2. (heap_store_unused a sp x heap = (heap2,T)) /\
            unused_space_inv a (sp - el_length x) heap2 /\
            (heap_lookup (a + sp - el_length x) heap2 = SOME x) /\
            ~isSomeDataElement (heap_lookup (a + sp - el_length x) heap) /\
            (heap_length heap2 = heap_length heap) /\
            (~isForwardPointer x ==>
             (FILTER isForwardPointer heap2 = FILTER isForwardPointer heap)) /\
            (!xs l d.
               MEM (DataElement xs l d) heap2 = (x = DataElement xs l d) \/
                                                MEM (DataElement xs l d) heap) /\
            (isDataElement x ==>
             ({a | isSomeDataElement (heap_lookup a heap2)} =
               a + sp - el_length x INSERT {a | isSomeDataElement (heap_lookup a heap)})) /\
            heap_store_rel heap heap2``,
  REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [heap_store_unused_def,heap_store_rel_def]
  \\ `sp <> 0` by (Cases_on `x` \\ FULL_SIMP_TAC std_ss [el_length_def] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [unused_space_inv_def]
  \\ IMP_RES_TAC heap_lookup_SPLIT \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [heap_store_lemma]
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [heap_length_def,SUM_APPEND,el_length_def]
    \\ FULL_SIMP_TAC std_ss [GSYM heap_length_def,heap_length_heap_expand]
    \\ DECIDE_TAC)
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss
      [heap_expand_def,APPEND,GSYM APPEND_ASSOC,heap_lookup_PREFIX])
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
    \\ `heap_length ha + sp - el_length x =
        heap_length (ha ++ heap_expand (sp - el_length x))` by
     (FULL_SIMP_TAC std_ss [heap_length_APPEND,heap_length_heap_expand] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [heap_lookup_PREFIX])
  \\ STRIP_TAC THEN1
   (`~(heap_length ha + sp - el_length x < heap_length ha)` by DECIDE_TAC
    \\ IMP_RES_TAC NOT_LESS_IMP_heap_lookup
    \\ FULL_SIMP_TAC std_ss []
    \\ `heap_length ha + sp - el_length x - heap_length ha =
        sp - el_length x` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [heap_lookup_def]
    \\ SRW_TAC [] [isSomeDataElement_def,el_length_def]
    \\ REVERSE (FULL_SIMP_TAC std_ss []) THEN1 (`F` by DECIDE_TAC)
    \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss [el_length_def]
    \\ `F` by DECIDE_TAC)
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [heap_length_APPEND,heap_length_heap_expand,
      heap_length_def,el_length_def] \\ DECIDE_TAC)
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [FILTER_APPEND,FILTER,isForwardPointer_def,APPEND_NIL]
    \\ SRW_TAC [] [heap_expand_def,isForwardPointer_def])
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [MEM_APPEND,MEM,heap_expand_def]
    \\ Cases_on `sp <= el_length x` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ METIS_TAC [])
  \\ STRIP_TAC THEN1
   (REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [EXTENSION]
    \\ STRIP_TAC \\ Q.ABBREV_TAC `y = x'` \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `y = heap_length ha + sp - el_length x`
    \\ FULL_SIMP_TAC std_ss [] THEN1
     (ONCE_REWRITE_TAC [GSYM APPEND_ASSOC] \\ SIMP_TAC std_ss [APPEND]
      \\ `(heap_length ha + sp - el_length x) =
          heap_length (ha ++ heap_expand (sp - el_length x))` by
       (FULL_SIMP_TAC std_ss [heap_length_APPEND,heap_length_heap_expand]
        \\ DECIDE_TAC)
      \\ FULL_SIMP_TAC std_ss [heap_lookup_PREFIX]
      \\ FULL_SIMP_TAC (srw_ss()) [isDataElement_def,isSomeDataElement_def])
    \\ Cases_on `y < heap_length ha`
    THEN1 (FULL_SIMP_TAC std_ss [LESS_IMP_heap_lookup,GSYM APPEND_ASSOC])
    \\ IMP_RES_TAC NOT_LESS_IMP_heap_lookup
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ FULL_SIMP_TAC std_ss [isSomeDataElement_heap_lookup_lemma1,
         isSomeDataElement_heap_lookup_lemma2]
    \\ `0 < el_length x` by
         (Cases_on `x` \\ FULL_SIMP_TAC std_ss [el_length_def] \\ DECIDE_TAC)
    \\ REVERSE (Cases_on `sp <= el_length x + (y - heap_length ha)`)
    \\ FULL_SIMP_TAC std_ss []
    THEN1 (CCONTR_TAC \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ `0 < y - heap_length ha` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ `y - heap_length ha - (sp - el_length x) <> 0` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND,isSomeDataElement_heap_lookup_lemma3]
    \\ REVERSE (Cases_on `el_length x <= y - heap_length ha - (sp - el_length x)`)
    \\ FULL_SIMP_TAC std_ss []
    THEN1 (CCONTR_TAC \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ `sp < 1 + (y - heap_length ha)` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [SUB_SUB]
    \\ IMP_RES_TAC (DECIDE ``sp <> 0 ==> (sp - 1 + 1 = sp:num)``)
    \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC (DECIDE  ``n <= sp ==> (y - m + n - sp - n = y - m - sp:num)``)
    \\ FULL_SIMP_TAC std_ss [])
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [isSomeDataElement_def]
  \\ Cases_on `ptr < heap_length ha`
  THEN1 (IMP_RES_TAC LESS_IMP_heap_lookup \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC])
  \\ IMP_RES_TAC NOT_LESS_IMP_heap_lookup \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
  \\ POP_ASSUM (K ALL_TAC) \\ Q.PAT_ASSUM `xxx = SOME yyy` MP_TAC
  \\ SIMP_TAC std_ss [Once heap_lookup_def] \\ SRW_TAC [] []
  \\ `~(ptr - heap_length ha < heap_length (heap_expand (sp - el_length x) ++ [x]))` by
   (FULL_SIMP_TAC (srw_ss()) [heap_length_APPEND,heap_length_heap_expand,
      el_length_def,heap_length_def] \\ DECIDE_TAC)
  \\ IMP_RES_TAC NOT_LESS_IMP_heap_lookup \\ POP_ASSUM (K ALL_TAC)
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
  \\ `heap_length (heap_expand (sp - el_length x) ++ [x]) = sp` by
   (FULL_SIMP_TAC (srw_ss()) [heap_length_APPEND,heap_length_heap_expand,
      el_length_def,heap_length_def] \\ DECIDE_TAC)
  \\ `el_length (Unused (sp - 1)) = sp` by
   (FULL_SIMP_TAC (srw_ss()) [heap_length_APPEND,heap_length_heap_expand,
      el_length_def,heap_length_def] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []);

val heap_store_rel_lemma = prove(
  ``heap_store_rel h1 h2 /\ (heap_lookup n h1 = SOME (DataElement ys l d)) ==>
    (heap_lookup n h2 = SOME (DataElement ys l d))``,
  SIMP_TAC std_ss [heap_store_rel_def,isSomeDataElement_def] \\ METIS_TAC []);

(* Lemmas about ok and a *)

val gc_forward_ptr_ok = store_thm("gc_forward_ptr_ok",
  ``!heap n a c x. (gc_forward_ptr n heap a c = (x,T)) ==> c``,
  Induct \\ SIMP_TAC std_ss [Once gc_forward_ptr_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `n=0` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `n < el_length h` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `gc_forward_ptr (n - el_length h) heap a c`
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ Cases_on `r`
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC);

val gc_move_ok = store_thm("gc_move_ok",
  ``(gc_move (x,h2,a,n,heap,c,limit) = (x',h2',a',n',heap',T)) ==>
    c /\
    ((a = b + heap_length h2) ==> (a' = b + heap_length h2'))``,
  SIMP_TAC std_ss [Once EQ_SYM_EQ] \\ Cases_on `x`
  \\ FULL_SIMP_TAC std_ss [gc_move_def]
  \\ Cases_on `heap_lookup n'' heap` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC gc_forward_ptr_ok
  \\ REPEAT (POP_ASSUM MP_TAC)
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [heap_length_APPEND,heap_length_def,
       el_length_def,ADD_ASSOC]);

val gc_move_list_ok = store_thm("gc_move_list_ok",
  ``!xs h2 a n heap c limit xs' h2' a' n' heap' c'.
      (gc_move_list (xs,h2,a,n,heap,c,limit) = (xs',h2',a',n',heap',T)) ==>
      c /\
      ((a = b + heap_length h2) ==> (a' = b + heap_length h2'))``,
  Induct \\ SIMP_TAC std_ss [gc_move_list_def] \\ REPEAT STRIP_TAC
  THENL [ALL_TAC, POP_ASSUM MP_TAC]
  \\ POP_ASSUM MP_TAC
  \\ `? x' h2' a' n' heap' c'. gc_move (h,h2,a,n,heap,c,limit) =
       (x',h2',a',n',heap',c')` by METIS_TAC [PAIR]
  \\ POP_ASSUM (fn th => ASSUME_TAC th THEN ONCE_REWRITE_TAC [th])
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ `? xs1 h21 a1 n1 heap1 c1. gc_move_list (xs,h2'',a'',n'',heap'',c',limit) =
       (xs1,h21,a1,n1,heap1,c1)` by METIS_TAC [PAIR]
  \\ POP_ASSUM (fn th => ASSUME_TAC th THEN ONCE_REWRITE_TAC [th])
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `c1` \\ SIMP_TAC std_ss [] \\ `c'` by METIS_TAC []
  \\ POP_ASSUM MP_TAC \\ Cases_on `c'` \\ SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [] \\ RES_TAC
  \\ IMP_RES_TAC gc_move_ok \\ METIS_TAC []);

val th =
  fetch "-" "gc_move_loop_ind" |> Q.SPEC `(\(h1,h2,a,n,heap,c,limit).
     !xs' h1' a' n' heap' c'.
       (gc_move_loop (h1,h2,a,n,heap,c,limit) = (h1',a',n',heap',T)) ==>
       c)`

val lemma = prove(th |> concl |> dest_imp |> fst,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [gc_move_loop_def]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ Cases_on `limit < heap_length (h1 ++ h::h2)`
  \\ ASM_REWRITE_TAC [] \\ SIMP_TAC std_ss []
  \\ Cases_on `h` \\ SIMP_TAC (srw_ss()) []
  \\ `?x1 x2 x3 x4 x5 x6.
        gc_move_list (l,DataElement l n'' b::h2,a,n,heap,c,limit) =
          (x1,x2,x3,x4,x5,x6)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC [] \\ SIMP_TAC std_ss [LET_DEF]
  \\ Q.PAT_ASSUM `!xs.bbb` MP_TAC
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV (srw_ss()) []))
  \\ ASM_REWRITE_TAC [] \\ SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC gc_move_list_ok)

val th = MP th lemma |> SIMP_RULE std_ss []
         |> Q.SPECL [`h1`,`h2`,`a`,`n`,`heap`,`c`,`limit`,`h1'`,`a'`,`n'`,`heap'`]

val gc_move_loop_ok = save_thm("gc_move_loop_ok",th);

(* cons *)

val EVERY2_APPEND_IMP = prove(
  ``!xs1 xs2 ys.
      EVERY2 P (xs1 ++ xs2) ys ==>
      ?ys1 ys2. (ys = ys1 ++ ys2) /\ EVERY2 P xs1 ys1 /\ EVERY2 P xs2 ys2``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ METIS_TAC [EVERY2_def,APPEND]);

val INJ_SUBSET = prove(
  ``!x y z. INJ f x y /\ y SUBSET z ==> INJ f x z``,
  FULL_SIMP_TAC (srw_ss()) [INJ_DEF,SUBSET_DEF]);

val bc_value_inv_SUBMAP = prove(
  ``!w x.
      f SUBMAP f1 /\ heap_store_rel heap heap1 /\
      bc_value_inv w (x,f,heap) ==>
      bc_value_inv w (x,f1,heap1) ``,
  completeInduct_on `bc_value_size w` \\ NTAC 3 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ Cases_on `w` THEN1
   (FULL_SIMP_TAC std_ss [bc_value_inv_def,DataOnly_def] \\ SRW_TAC [] []
    \\ IMP_RES_TAC heap_store_rel_lemma \\ FULL_SIMP_TAC std_ss [])
  THEN1 (FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ Cases_on `l = []` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [EVERY2_EVERY,LENGTH_ADDR_MAP,EVERY_MEM,FORALL_PROD]
    \\ Q.PAT_ASSUM `LENGTH l = LENGTH xs` ASSUME_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [MEM_ZIP,LENGTH_ADDR_MAP,PULL_EXISTS]
    \\ IMP_RES_TAC heap_store_rel_lemma \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (srw_ss()) [MEM_ZIP,LENGTH_ADDR_MAP,PULL_EXISTS]
    \\ REPEAT STRIP_TAC
    \\ Q.MATCH_ASSUM_RENAME_TAC `t < LENGTH xs` [] \\ RES_TAC
    \\ `MEM (EL t l) l` by (FULL_SIMP_TAC std_ss [MEM_EL] \\ METIS_TAC [])
    \\ `bc_value_size (EL t l) < bc_value_size (Block n l)` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [bc_value_size_def]
      \\ IMP_RES_TAC MEM_IMP_bc_value_size \\ DECIDE_TAC) \\ RES_TAC)
  THEN1 (FULL_SIMP_TAC std_ss [bc_value_inv_def])
  THEN1 (FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def,SUBMAP_DEF])
  THEN1 (FULL_SIMP_TAC std_ss [bc_value_inv_def]));

val EVERY2_LENGTH = prove(
  ``!xs ys. EVERY2 P xs ys ==> (LENGTH xs = LENGTH ys)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) []);

val cons_thm = store_thm("cons_thm",
  ``abs_ml_inv (xs ++ stack) refs (roots,heap,a,sp) limit /\
    LENGTH xs < sp /\ xs <> [] ==>
    ?rs roots2 heap2.
      (roots = rs ++ roots2) /\ (LENGTH rs = LENGTH xs) /\
      (heap_store_unused a sp (BlockRep tag rs) heap = (heap2,T)) /\
      abs_ml_inv ((Block tag xs)::stack) refs
                 (Pointer (a + sp - el_length (BlockRep tag rs))::roots2,heap2,a,
                  sp-el_length (BlockRep tag rs)) limit``,
  SIMP_TAC std_ss [abs_ml_inv_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_stack_ref_inv_def,EVERY2_def]
  \\ IMP_RES_TAC EVERY2_APPEND_IMP \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`ys1`,`ys2`] \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC EVERY2_LENGTH \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `unused_space_inv a sp heap` (fn th =>
    MATCH_MP (IMP_heap_store_unused |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> GEN_ALL) th
    |> ASSUME_TAC)
  \\ POP_ASSUM (MP_TAC o Q.SPEC `(BlockRep tag ys1)`) \\ MATCH_MP_TAC IMP_IMP
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [BlockRep_def,el_length_def] \\ DECIDE_TAC)
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [roots_ok_def,MEM,BlockRep_def]
    \\ REVERSE (REPEAT STRIP_TAC \\ RES_TAC) THEN1 METIS_TAC [heap_store_rel_def]
    \\ FULL_SIMP_TAC (srw_ss()) [el_length_def,isSomeDataElement_def])
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [roots_ok_def,MEM,BlockRep_def,heap_ok_def,
      isForwardPointer_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ REPEAT STRIP_TAC \\ METIS_TAC [heap_store_rel_def])
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [el_length_def,BlockRep_def])
  \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1
   (MATCH_MP_TAC INJ_SUBSET
    \\ Q.EXISTS_TAC `{a | isSomeDataElement (heap_lookup a heap)}`
    \\ FULL_SIMP_TAC (srw_ss()) [isDataElement_def,BlockRep_def])
  \\ REPEAT STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def]
    \\ FULL_SIMP_TAC std_ss [BlockRep_def,el_length_def]
    \\ Q.EXISTS_TAC `ys1` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS]
    \\ `f SUBMAP f` by FULL_SIMP_TAC std_ss [SUBMAP_REFL]
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ IMP_RES_TAC bc_value_inv_SUBMAP)
  THEN1
   (FULL_SIMP_TAC std_ss [EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS]
    \\ `f SUBMAP f` by FULL_SIMP_TAC std_ss [SUBMAP_REFL]
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ IMP_RES_TAC bc_value_inv_SUBMAP)
  \\ `reachable_refs (xs++stack) refs n` by ALL_TAC THEN1
   (POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [reachable_refs_def]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [MEM] THEN1
     (NTAC 2 (POP_ASSUM MP_TAC) \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]
      \\ FULL_SIMP_TAC std_ss [MEM_APPEND] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [MEM_APPEND] \\ METIS_TAC [])
  \\ RES_TAC \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [bc_ref_inv_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [RefBlock_def]
  \\ IMP_RES_TAC heap_store_rel_lemma \\ FULL_SIMP_TAC (srw_ss()) []
  \\ `f SUBMAP f` by FULL_SIMP_TAC std_ss [SUBMAP_REFL]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ IMP_RES_TAC bc_value_inv_SUBMAP)

val cons_thm_EMPTY = store_thm("cons_thm_EMPTY",
  ``abs_ml_inv stack refs (roots,heap:('a,'b) ml_heap,a,sp) limit /\
    tag < 2 ** 62 ==>
    abs_ml_inv ((Block tag [])::stack) refs
                (Data (2w * n2w tag + 1w)::roots,heap,a,sp) limit``,
  SIMP_TAC std_ss [abs_ml_inv_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [bc_stack_ref_inv_def,EVERY2_def]
  \\ FULL_SIMP_TAC (srw_ss()) [roots_ok_def,MEM]
  \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def]
  \\ REPEAT STRIP_TAC \\ `reachable_refs stack refs n` by ALL_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [reachable_refs_def]
  \\ Cases_on `x = Block tag []` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [get_refs_def] \\ METIS_TAC []);

(* update ref *)

val reachable_refs_UPDATE = prove(
  ``reachable_refs (x::RefPtr ptr::stack) (refs |+ (ptr,x)) n ==>
    reachable_refs (x::RefPtr ptr::stack) refs n``,
  FULL_SIMP_TAC std_ss [reachable_refs_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `?m. MEM m (get_refs x) /\ RTC (ref_edge refs) m n` THEN1
   (FULL_SIMP_TAC std_ss [] \\ Q.LIST_EXISTS_TAC [`x`,`m`]
    \\ FULL_SIMP_TAC std_ss [MEM])
  \\ FULL_SIMP_TAC std_ss [] \\ Q.LIST_EXISTS_TAC [`x'`,`r`]
  \\ FULL_SIMP_TAC std_ss [METIS_PROVE [] ``~b \/ c = b ==> c``]
  \\ FULL_SIMP_TAC std_ss [RTC_eq_NRC]
  \\ Q.ABBREV_TAC `k = n'` \\ POP_ASSUM (K ALL_TAC) \\ Q.EXISTS_TAC `k`
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Q.SPEC_TAC (`r`,`r`) \\ Induct_on `k`
  \\ FULL_SIMP_TAC std_ss [NRC]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
  \\ Q.EXISTS_TAC `z` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [ref_edge_def]
  \\ REVERSE (Cases_on `r = ptr`)
  \\ FULL_SIMP_TAC (srw_ss()) [FDOM_FUPDATE,FAPPLY_FUPDATE_THM]
  \\ METIS_TAC []);

val isRefBlock_def = Define `
  isRefBlock x = ?p. x = RefBlock p`;

val RefBlock_inv_def = Define `
  RefBlock_inv heap heap2 =
    (!n x. (heap_lookup n heap = SOME x) /\ ~(isRefBlock x) ==>
           (heap_lookup n heap2 = SOME x)) /\
    (!n x. (heap_lookup n heap2 = SOME x) /\ ~(isRefBlock x) ==>
           (heap_lookup n heap = SOME x))`;

val heap_store_RefBlock_thm = prove(
  ``!ha. heap_store (heap_length ha) [RefBlock x] (ha ++ RefBlock y::hb) =
           (ha ++ RefBlock x::hb,T)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [heap_store_def,heap_length_def]
  THEN1 FULL_SIMP_TAC std_ss [RefBlock_def,el_length_def] \\ STRIP_TAC
  \\ `~(el_length h + SUM (MAP el_length ha) < el_length h) /\ el_length h <> 0` by
       (Cases_on `h` \\ FULL_SIMP_TAC std_ss [el_length_def] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [LET_DEF]);

val heap_lookup_RefBlock_lemma = prove(
  ``(heap_lookup n (ha ++ RefBlock y::hb) = SOME x) =
      if n < heap_length ha then
        (heap_lookup n ha = SOME x)
      else if n = heap_length ha then
        (x = RefBlock y)
      else if heap_length ha + 2 <= n then
        (heap_lookup (n - heap_length ha - 2) hb = SOME x)
      else F``,
  Cases_on `n < heap_length ha` \\ FULL_SIMP_TAC std_ss [LESS_IMP_heap_lookup]
  \\ FULL_SIMP_TAC std_ss [NOT_LESS_IMP_heap_lookup]
  \\ FULL_SIMP_TAC std_ss [heap_lookup_def]
  \\ Cases_on `n <= heap_length ha` \\ FULL_SIMP_TAC std_ss []
  THEN1 (`heap_length ha = n` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ `heap_length ha <> n` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `0 < el_length (RefBlock y)` by FULL_SIMP_TAC std_ss [el_length_def,RefBlock_def]
  \\ FULL_SIMP_TAC std_ss [] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss [el_length_def,RefBlock_def,NOT_LESS]
  \\ DISJ1_TAC \\ DECIDE_TAC);

val heap_store_RefBlock = prove(
  ``(heap_lookup n heap = SOME (RefBlock y)) ==>
    ?heap2. (heap_store n [RefBlock h] heap = (heap2,T)) /\
            RefBlock_inv heap heap2 /\
            (heap_lookup n heap2 = SOME (RefBlock h)) /\
            (heap_length heap2 = heap_length heap) /\
            (FILTER isForwardPointer heap2 = FILTER isForwardPointer heap) /\
            (!xs l d.
               MEM (DataElement xs l d) heap2 ==> (DataElement xs l d = RefBlock h) \/
                                                  MEM (DataElement xs l d) heap) /\
            (!a. isSomeDataElement (heap_lookup a heap2) =
                 isSomeDataElement (heap_lookup a heap)) /\
            !m x. m <> n /\ (heap_lookup m heap = SOME x) ==>
                  (heap_lookup m heap2 = SOME x)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC heap_lookup_SPLIT
  \\ FULL_SIMP_TAC std_ss [heap_store_RefBlock_thm]
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [RefBlock_inv_def]
    \\ FULL_SIMP_TAC std_ss [heap_lookup_RefBlock_lemma]
    \\ FULL_SIMP_TAC std_ss [isRefBlock_def] \\ METIS_TAC [])
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [heap_lookup_PREFIX])
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC (srw_ss())
       [heap_length_APPEND,heap_length_def,RefBlock_def,el_length_def])
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [FILTER_APPEND,FILTER,isForwardPointer_def,RefBlock_def])
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [MEM,MEM_APPEND,RefBlock_def] \\ METIS_TAC [])
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [isSomeDataElement_def,heap_lookup_RefBlock_lemma]
    \\ FULL_SIMP_TAC std_ss [RefBlock_def] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [isSomeDataElement_def,heap_lookup_RefBlock_lemma]
  \\ METIS_TAC []);

val NOT_isRefBlock = prove(
  ``~(isRefBlock (DataOnly x y)) /\
    ~(isRefBlock (DataElement xs (LENGTH xs) (BlockTag n,[])))``,
  SIMP_TAC (srw_ss()) [isRefBlock_def,DataOnly_def,RefBlock_def]);

val bc_value_inv_Ref = prove(
  ``RefBlock_inv heap heap2 ==>
    !x h f. (bc_value_inv x (h,f,heap2) = bc_value_inv x (h,f,heap))``,
  STRIP_TAC \\ completeInduct_on `bc_value_size x` \\ NTAC 3 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ Cases_on `x` THEN1
   (FULL_SIMP_TAC std_ss [bc_value_inv_def] \\ SRW_TAC [] []
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [RefBlock_inv_def]
    \\ METIS_TAC [NOT_isRefBlock])
  THEN1 (FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ Cases_on `l = []` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [EVERY2_EVERY,LENGTH_ADDR_MAP,EVERY_MEM,FORALL_PROD]
    \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
    THEN1
     (Q.PAT_ASSUM `LENGTH l = LENGTH xs` ASSUME_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [MEM_ZIP,LENGTH_ADDR_MAP,PULL_EXISTS]
      \\ `heap_lookup ptr heap =
           SOME (DataElement xs (LENGTH xs) (BlockTag n,[]))` by
              METIS_TAC [RefBlock_inv_def,NOT_isRefBlock]
      \\ FULL_SIMP_TAC (srw_ss()) [MEM_ZIP]
      \\ REPEAT STRIP_TAC
      \\ Q.MATCH_ASSUM_RENAME_TAC `t < LENGTH xs` [] \\ RES_TAC
      \\ `MEM (EL t l) l` by (FULL_SIMP_TAC std_ss [MEM_EL] \\ METIS_TAC [])
      \\ `bc_value_size (EL t l) < bc_value_size (Block n l)` by ALL_TAC THEN1
       (FULL_SIMP_TAC std_ss [bc_value_size_def]
        \\ IMP_RES_TAC MEM_IMP_bc_value_size \\ DECIDE_TAC) \\ RES_TAC
      \\ FULL_SIMP_TAC std_ss [])
    THEN1
     (Q.PAT_ASSUM `LENGTH l = LENGTH xs` ASSUME_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [MEM_ZIP,LENGTH_ADDR_MAP,PULL_EXISTS]
      \\ `heap_lookup ptr heap2 =
           SOME (DataElement xs (LENGTH xs) (BlockTag n,[]))` by
              METIS_TAC [RefBlock_inv_def,NOT_isRefBlock]
      \\ FULL_SIMP_TAC (srw_ss()) [MEM_ZIP]
      \\ REPEAT STRIP_TAC
      \\ Q.MATCH_ASSUM_RENAME_TAC `t < LENGTH xs` [] \\ RES_TAC
      \\ `MEM (EL t l) l` by (FULL_SIMP_TAC std_ss [MEM_EL] \\ METIS_TAC [])
      \\ `bc_value_size (EL t l) < bc_value_size (Block n l)` by ALL_TAC THEN1
       (FULL_SIMP_TAC std_ss [bc_value_size_def]
        \\ IMP_RES_TAC MEM_IMP_bc_value_size \\ DECIDE_TAC) \\ RES_TAC
      \\ FULL_SIMP_TAC std_ss []))
  THEN1 (FULL_SIMP_TAC std_ss [bc_value_inv_def])
  THEN1 (FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def,SUBMAP_DEF])
  THEN1 (FULL_SIMP_TAC std_ss [bc_value_inv_def]));

val update_ref_thm = store_thm("update_ref_thm",
  ``abs_ml_inv (x::(RefPtr ptr)::stack) refs (roots,heap,a,sp) limit ==>
    ?p r roots2 heap2.
      (roots = r :: Pointer p :: roots2) /\
      (heap_store p [RefBlock r] heap = (heap2,T)) /\
      abs_ml_inv (x::(RefPtr ptr)::stack) (refs |+ (ptr,x)) (roots,heap2,a,sp) limit``,
  SIMP_TAC std_ss [abs_ml_inv_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_stack_ref_inv_def]
  \\ Cases_on `roots` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def]
  \\ `reachable_refs (x::RefPtr ptr::stack) refs ptr` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [reachable_refs_def] \\ Q.EXISTS_TAC `RefPtr ptr`
    \\ FULL_SIMP_TAC (srw_ss()) [get_refs_def])
  \\ RES_TAC \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [Once bc_ref_inv_def]
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC heap_store_RefBlock \\ POP_ASSUM (MP_TAC o SPEC_ALL)
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [roots_ok_def])
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [heap_ok_def] \\ REPEAT STRIP_TAC \\ RES_TAC THEN1
     (POP_ASSUM MP_TAC \\ FULL_SIMP_TAC (srw_ss()) [RefBlock_def]
      \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [roots_ok_def,MEM]) \\ RES_TAC)
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [unused_space_inv_def] \\ REPEAT STRIP_TAC
    \\ RES_TAC \\ Cases_on `a = f ' ptr` \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (srw_ss()) [RefBlock_def])
  \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss []
  \\ MP_TAC bc_value_inv_Ref
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF])
  \\ Cases_on `n = ptr` \\ FULL_SIMP_TAC (srw_ss()) [bc_ref_inv_def]
  THEN1 (Q.EXISTS_TAC `h` \\ FULL_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM]
  \\ `reachable_refs (x::RefPtr ptr::stack) refs n` by ALL_TAC
  THEN1 IMP_RES_TAC reachable_refs_UPDATE \\ RES_TAC
  \\ `f ' n <> f ' ptr` by ALL_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [INJ_DEF] \\ REPEAT STRIP_TAC \\ RES_TAC)
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [RefBlock_def]);

(* new ref *)

val new_ref_thm = store_thm("new_ref_thm",
  ``abs_ml_inv (x::stack) refs (roots,heap,a,sp) limit /\
    ~(ptr IN FDOM refs) /\ 2 <= sp ==>
    ?p r roots2 heap2.
      (roots = r :: roots2) /\
      (heap_store_unused a sp (RefBlock r) heap = (heap2,T)) /\
      abs_ml_inv (x::(RefPtr ptr)::stack) (refs |+ (ptr,x))
                 (r::Pointer (a+sp-2)::roots2,heap2,a,sp-2) limit``,
  SIMP_TAC std_ss [abs_ml_inv_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_stack_ref_inv_def]
  \\ Cases_on `roots` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ `el_length (RefBlock h) <= sp` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [el_length_def,RefBlock_def])
  \\ Q.PAT_ASSUM `unused_space_inv a sp heap` (fn th =>
    MATCH_MP (IMP_heap_store_unused |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> GEN_ALL) th
    |> ASSUME_TAC)
  \\ POP_ASSUM (MP_TAC o Q.SPEC `RefBlock h`) \\ MATCH_MP_TAC IMP_IMP
  \\ STRIP_TAC THEN1 FULL_SIMP_TAC std_ss [RefBlock_def,el_length_def]
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `unused_space_inv a (sp - 2) heap2` by ALL_TAC
  THEN1 FULL_SIMP_TAC std_ss [RefBlock_def,el_length_def]
  \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [roots_ok_def,MEM,heap_store_rel_def] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [RefBlock_def,el_length_def]
    \\ FULL_SIMP_TAC (srw_ss()) [isSomeDataElement_def])
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [heap_ok_def,RefBlock_def,isForwardPointer_def]
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REPEAT STRIP_TAC THEN1
     (POP_ASSUM MP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
      \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC (srw_ss()) [roots_ok_def,MEM]
      \\ METIS_TAC [heap_store_rel_def])
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [heap_store_rel_def])
  \\ `~(ptr IN FDOM f)` by (FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] \\ METIS_TAC [])
  \\ Q.EXISTS_TAC `f |+ (ptr,a+sp-2)`
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [FDOM_FUPDATE]
    \\ `(FAPPLY (f |+ (ptr,a + sp - 2))) = (ptr =+ (a+sp-2)) (FAPPLY f)` by
     (FULL_SIMP_TAC std_ss [FUN_EQ_THM,FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM]
      \\ METIS_TAC []) \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC (METIS_PROVE [] ``!y. (x = y) /\ f y ==> f x``)
    \\ Q.EXISTS_TAC `(a + sp - 2) INSERT {a | isSomeDataElement (heap_lookup a heap)}`
    \\ STRIP_TAC
    THEN1 (FULL_SIMP_TAC (srw_ss()) [RefBlock_def,isDataElement_def,el_length_def])
    \\ MATCH_MP_TAC INJ_UPDATE \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [RefBlock_def,el_length_def])
  \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF,FDOM_FUPDATE] \\ METIS_TAC [])
  \\ Q.ABBREV_TAC `f1 = f |+ (ptr,a + sp - 2)`
  \\ `f SUBMAP f1` by ALL_TAC THEN1
   (Q.UNABBREV_TAC `f1` \\ FULL_SIMP_TAC (srw_ss()) [SUBMAP_DEF,FAPPLY_FUPDATE_THM]
    \\ METIS_TAC [])
  \\ STRIP_TAC THEN1
   (STRIP_TAC THEN1 METIS_TAC [bc_value_inv_SUBMAP] \\ STRIP_TAC THEN1
     (Q.UNABBREV_TAC `f1`
      \\ SIMP_TAC (srw_ss()) [bc_value_inv_def,FAPPLY_FUPDATE_THM,FDOM_FUPDATE])
    \\ FULL_SIMP_TAC std_ss [EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS]
    \\ Q.PAT_ASSUM `LENGTH stack = LENGTH t` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS]
    \\ REPEAT STRIP_TAC \\ METIS_TAC [bc_value_inv_SUBMAP])
  \\ REPEAT STRIP_TAC
  \\ Cases_on `n = ptr` THEN1
   (Q.UNABBREV_TAC `f1` \\ ASM_SIMP_TAC (srw_ss()) [bc_ref_inv_def,FDOM_FUPDATE,
      FAPPLY_FUPDATE_THM] \\ FULL_SIMP_TAC std_ss [el_length_def,RefBlock_def]
    \\ SIMP_TAC (srw_ss()) [] \\ METIS_TAC [bc_value_inv_SUBMAP])
  \\ `reachable_refs (x::RefPtr ptr::stack) refs n` by ALL_TAC
  THEN1 IMP_RES_TAC reachable_refs_UPDATE
  \\ Q.PAT_ASSUM `reachable_refs (x::RefPtr ptr::stack) (refs |+ (ptr,x)) n` (K ALL_TAC)
  \\ `reachable_refs (x::stack) refs n` by ALL_TAC THEN1
    (FULL_SIMP_TAC std_ss [reachable_refs_def] \\ REVERSE (Cases_on `x' = RefPtr ptr`)
     THEN1 (FULL_SIMP_TAC std_ss [MEM] \\ METIS_TAC [])
     \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM]
     \\ Q.PAT_ASSUM `RTC (ref_edge refs) r n` MP_TAC
     \\ ONCE_REWRITE_TAC [RTC_CASES1]
     \\ `r <> n` by FULL_SIMP_TAC std_ss [] \\ ASM_SIMP_TAC std_ss []
     \\ FULL_SIMP_TAC std_ss [ref_edge_def])
  \\ RES_TAC \\ Q.UNABBREV_TAC `f1` \\ FULL_SIMP_TAC std_ss [bc_ref_inv_def]
  \\ ASM_SIMP_TAC (srw_ss()) [FDOM_FUPDATE,FAPPLY_FUPDATE_THM]
  \\ `isSomeDataElement (heap_lookup (f ' n) heap)` by ALL_TAC THEN1
    (FULL_SIMP_TAC std_ss [RefBlock_def] \\ EVAL_TAC \\ SIMP_TAC (srw_ss()) [])
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC (srw_ss()) [RefBlock_def]
  \\ FULL_SIMP_TAC std_ss [RefBlock_def] \\ IMP_RES_TAC heap_store_rel_lemma
  \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC (srw_ss()) []
  \\ METIS_TAC [bc_value_inv_SUBMAP]);

(* deref *)

val heap_el_def = Define `
  (heap_el (Pointer a) n heap =
    case heap_lookup a heap of
    | SOME (DataElement xs l d) =>
        if n < LENGTH xs then (EL n xs,T) else (ARB,F)
    | _ => (ARB,F)) /\
  (heap_el _ _ _ = (ARB,F))`;

val deref_thm = store_thm("deref_thm",
  ``abs_ml_inv (RefPtr ptr::stack) refs (roots,heap,a,sp) limit ==>
    ?r roots2 y.
      (roots = r :: roots2) /\ (heap_el r 0 heap = (y,T)) /\ ptr IN FDOM refs /\
      abs_ml_inv (refs ' ptr::RefPtr ptr::stack) refs (y::roots,heap,a,sp) limit``,
  FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `roots` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def]
  \\ FULL_SIMP_TAC std_ss [bc_value_inv_def]
  \\ `reachable_refs (RefPtr ptr::stack) refs ptr` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [reachable_refs_def,MEM] \\ Q.EXISTS_TAC `RefPtr ptr`
    \\ ASM_SIMP_TAC (srw_ss()) [get_refs_def])
  \\ RES_TAC \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [Once bc_ref_inv_def] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [heap_el_def,RefBlock_def]
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [roots_ok_def,heap_ok_def]
    \\ IMP_RES_TAC heap_lookup_MEM
    \\ STRIP_TAC \\ ONCE_REWRITE_TAC [MEM] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [RefBlock_def]
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [MEM])
  \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ Q.PAT_ASSUM `!xx.bbb` MATCH_MP_TAC
  \\ Q.PAT_ASSUM `reachable_refs (RefPtr ptr::stack) refs ptr` (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [reachable_refs_def]
  \\ REVERSE (Cases_on `x = refs ' ptr`)
  THEN1 (FULL_SIMP_TAC std_ss [MEM] \\ METIS_TAC [])
  \\ Q.EXISTS_TAC `RefPtr ptr` \\ SIMP_TAC std_ss [MEM,get_refs_def]
  \\ ONCE_REWRITE_TAC [RTC_CASES1] \\ DISJ2_TAC
  \\ Q.EXISTS_TAC `r` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [ref_edge_def]);

(* el *)

val el_thm = store_thm("el_thm",
  ``abs_ml_inv (Block n xs::stack) refs (roots,heap,a,sp) limit /\ i < LENGTH xs ==>
    ?r roots2 y.
      (roots = r :: roots2) /\ (heap_el r i heap = (y,T)) /\
      abs_ml_inv (EL i xs::Block n xs::stack) refs (y::roots,heap,a,sp) limit``,
  FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `roots` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def]
  \\ FULL_SIMP_TAC std_ss [bc_value_inv_def]
  \\ `xs <> []` by (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [GSYM LENGTH_NIL,LENGTH])
  \\ FULL_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC (srw_ss()) [heap_el_def,BlockRep_def]
  \\ IMP_RES_TAC EVERY2_LENGTH \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [roots_ok_def,heap_ok_def] \\ ONCE_REWRITE_TAC [MEM]
    \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ IMP_RES_TAC heap_lookup_MEM
    \\ FULL_SIMP_TAC std_ss [BlockRep_def]
    \\ `MEM (Pointer ptr') xs'` by ALL_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [MEM_EL] \\ METIS_TAC [])
  \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS])
  \\ REPEAT STRIP_TAC
  \\ Q.PAT_ASSUM `!xx.bbb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [reachable_refs_def]
  \\ REVERSE (Cases_on `x = EL i xs`)
  THEN1 (FULL_SIMP_TAC std_ss [MEM] \\ METIS_TAC [])
  \\ Q.LIST_EXISTS_TAC [`Block n xs`,`r`]
  \\ ASM_SIMP_TAC std_ss [MEM]
  \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]
  \\ Q.EXISTS_TAC `EL i xs` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [MEM_EL] \\ Q.EXISTS_TAC `i`
  \\ FULL_SIMP_TAC std_ss []);

(* pop *)

val pop_thm = store_thm("pop_thm",
  ``abs_ml_inv (xs ++ stack) refs (rs ++ roots,heap,a,sp) limit /\
    (LENGTH xs = LENGTH rs) ==>
    abs_ml_inv (stack) refs (roots,heap,a,sp) limit``,
  FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [roots_ok_def,MEM_APPEND]
  \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC EVERY2_APPEND \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [reachable_refs_def,MEM_APPEND] \\ METIS_TAC []);

(* permute stack *)

val EVERY2_MAP_FST_SND = prove(
  ``!xs. EVERY2 P (MAP FST xs) (MAP SND xs) = EVERY (\(x,y). P x y) xs``,
  Induct \\ SRW_TAC [] [EVERY2_def] \\ Cases_on `h` \\ SRW_TAC [] []);

val abs_ml_inv_stack_permute = store_thm("abs_ml_inv_stack_permute",
  ``!xs ys.
      abs_ml_inv (MAP FST xs ++ stack) refs (MAP SND xs ++ roots,heap,a,sp) limit /\
      set ys SUBSET set xs ==>
      abs_ml_inv (MAP FST ys ++ stack) refs (MAP SND ys ++ roots,heap,a,sp) limit``,
  FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [roots_ok_def]
  THEN1 (FULL_SIMP_TAC std_ss [MEM_APPEND,SUBSET_DEF,MEM_MAP] \\ METIS_TAC [])
  \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [EVERY2_APPEND,LENGTH_MAP]
  \\ FULL_SIMP_TAC std_ss [EVERY2_MAP_FST_SND]
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM,SUBSET_DEF]
  \\ FULL_SIMP_TAC std_ss [reachable_refs_def,MEM_APPEND,MEM_MAP]
  \\ METIS_TAC []);

(* duplicate *)

val duplicate_thm = store_thm("duplicate_thm",
  ``abs_ml_inv (xs ++ stack) refs (rs ++ roots,heap,a,sp) limit /\
    (LENGTH xs = LENGTH rs) ==>
    abs_ml_inv (xs ++ xs ++ stack) refs (rs ++ rs ++ roots,heap,a,sp) limit``,
  FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [roots_ok_def] THEN1 METIS_TAC [MEM_APPEND]
  \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC EVERY2_APPEND \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [reachable_refs_def,MEM_APPEND] \\ METIS_TAC []);

val duplicate1_thm = save_thm("duplicate1_thm",
  duplicate_thm |> Q.INST [`xs`|->`[x1]`,`rs`|->`[r1]`]
                |> SIMP_RULE std_ss [LENGTH,APPEND]);

(* move *)

val IMP_EVERY2_APPEND = prove(
  ``!xs1 ys1. EVERY2 P xs1 ys1 /\ EVERY2 P xs2 ys2 ==>
              EVERY2 P (xs1 ++ xs2) (ys1 ++ ys2)``,
  Induct \\ Cases_on `ys1` \\ FULL_SIMP_TAC (srw_ss()) [EVERY2_def] \\ METIS_TAC []);

val EVERY2_APPEND_IMP = prove(
  ``EVERY2 P (xs1 ++ xs2) (ys1 ++ ys2) ==>
    (LENGTH xs1 = LENGTH ys1) ==> EVERY2 P xs1 ys1 /\ EVERY2 P xs2 ys2``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC EVERY2_LENGTH \\ IMP_RES_TAC EVERY2_APPEND);

val move_thm = store_thm("move_thm",
  ``!xs1 rs1 xs2 rs2 xs3 rs3.
      abs_ml_inv (xs1 ++ xs2 ++ xs3 ++ stack) refs (rs1 ++ rs2 ++ rs3 ++ roots,heap,a,sp) limit /\
      (LENGTH xs1 = LENGTH rs1) /\ (LENGTH xs2 = LENGTH rs2) /\ (LENGTH xs3 = LENGTH rs3) ==>
      abs_ml_inv (xs1 ++ xs3 ++ xs2 ++ stack) refs (rs1 ++ rs3 ++ rs2 ++ roots,heap,a,sp) limit``,
  REPEAT GEN_TAC
  \\ FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [roots_ok_def] THEN1 METIS_TAC [MEM_APPEND]
  \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1
   (NTAC 5 (IMP_RES_TAC EVERY2_APPEND_IMP \\ REPEAT (POP_ASSUM MP_TAC)
    \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,AC ADD_COMM ADD_ASSOC]
    \\ REPEAT STRIP_TAC)
    \\ NTAC 5 (MATCH_MP_TAC IMP_EVERY2_APPEND \\ FULL_SIMP_TAC std_ss []))
  \\ FULL_SIMP_TAC std_ss [reachable_refs_def,MEM_APPEND] \\ METIS_TAC []);

(* splits *)

val EVERY2_APPEND1 = prove(
  ``!xs1 xs2 ys.
      EVERY2 P (xs1 ++ xs2) ys ==>
      ?ys1 ys2. (ys = ys1 ++ ys2) /\ (LENGTH xs1 = LENGTH ys1) /\ EVERY2 P xs2 ys2``,
  Induct THEN1
   (FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `[]` \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`h::ys1`,`ys2`] \\ FULL_SIMP_TAC (srw_ss()) []);

val split1_thm = store_thm("split1_thm",
  ``abs_ml_inv (xs1 ++ stack) refs (roots,heap,a,sp) limit ==>
    ?rs1 roots1. (roots = rs1 ++ roots1) /\ (LENGTH rs1 = LENGTH xs1)``,
  FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,GSYM APPEND_ASSOC]
  \\ REPEAT STRIP_TAC \\ NTAC 5 (IMP_RES_TAC EVERY2_APPEND1) \\ METIS_TAC []);

val split2_thm = store_thm("split2_thm",
  ``abs_ml_inv (xs1 ++ xs2 ++ stack) refs (roots,heap,a,sp) limit ==>
    ?rs1 rs2 roots1. (roots = rs1 ++ rs2 ++ roots1) /\
      (LENGTH rs1 = LENGTH xs1) /\ (LENGTH rs2 = LENGTH xs2)``,
  FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,GSYM APPEND_ASSOC]
  \\ REPEAT STRIP_TAC \\ NTAC 5 (IMP_RES_TAC EVERY2_APPEND1) \\ METIS_TAC []);

val split3_thm = store_thm("split3_thm",
  ``abs_ml_inv (xs1 ++ xs2 ++ xs3 ++ stack) refs (roots,heap,a,sp) limit ==>
    ?rs1 rs2 rs3 roots1. (roots = rs1 ++ rs2 ++ rs3 ++ roots1) /\
      (LENGTH rs1 = LENGTH xs1) /\ (LENGTH rs2 = LENGTH xs2) /\
      (LENGTH rs3 = LENGTH xs3)``,
  FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,GSYM APPEND_ASSOC]
  \\ REPEAT STRIP_TAC \\ NTAC 5 (IMP_RES_TAC EVERY2_APPEND1) \\ METIS_TAC []);

val LESS_EQ_LENGTH = store_thm("LESS_EQ_LENGTH",
  ``!xs k. k <= LENGTH xs ==> ?ys1 ys2. (xs = ys1 ++ ys2) /\ (LENGTH ys1 = k)``,
  Induct \\ Cases_on `k` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,LENGTH_NIL,APPEND]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `h::ys1` \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND]
  \\ SRW_TAC [] [ADD1]);

val LESS_LENGTH = store_thm("LESS_LENGTH",
  ``!xs k. k < LENGTH xs ==> ?ys1 y ys2. (xs = ys1 ++ y::ys2) /\ (LENGTH ys1 = k)``,
  Induct \\ Cases_on `k` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,LENGTH_NIL,APPEND]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss [CONS_11]
  \\ Q.EXISTS_TAC `h::ys1` \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND]
  \\ SRW_TAC [] [ADD1]);

val _ = export_theory();
