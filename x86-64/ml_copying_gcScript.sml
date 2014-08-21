open HolKernel boolLib bossLib Parse;
val _ = new_theory "ml_copying_gc";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open wordsTheory wordsLib integer_wordTheory;

open bytecodeTheory;

val _ = set_fixity "=" (Infix(NONASSOC, 100));

infix \\ val op \\ = op THEN;

(* TODO: move *)

val FILTER_APPEND = rich_listTheory.FILTER_APPEND

val EVERY2_SPLIT = store_thm("EVERY2_SPLIT",
  ``!xs1 zs.
      EVERY2 P zs (xs1 ++ x::xs2) ==>
      ?ys1 y ys2. (zs = ys1 ++ y::ys2) /\ EVERY2 P ys1 xs1 /\
                  EVERY2 P ys2 xs2 /\ P y x``,
  Induct \\ FULL_SIMP_TAC std_ss [APPEND]
  \\ Cases_on `zs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`h::ys1`,`y`,`ys2`] \\ FULL_SIMP_TAC (srw_ss()) []);

val EVERY2_SPLIT_ALT = store_thm("EVERY2_SPLIT_ALT",
  ``!xs1 zs.
      EVERY2 P (xs1 ++ x::xs2) zs ==>
      ?ys1 y ys2. (zs = ys1 ++ y::ys2) /\ EVERY2 P xs1 ys1 /\
                  EVERY2 P xs2 ys2 /\ P x y``,
  Induct \\ FULL_SIMP_TAC std_ss [APPEND]
  \\ Cases_on `zs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`h::ys1`,`y`,`ys2`] \\ FULL_SIMP_TAC (srw_ss()) []);

val EVERY2_APPEND = store_thm("EVERY2_APPEND",
  ``!xs ts.
      (LENGTH xs = LENGTH ts) ==>
      (EVERY2 P (xs ++ ys) (ts ++ us) = EVERY2 P xs ts /\ EVERY2 P ys us)``,
  Induct \\ Cases_on `ts` \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,CONJ_ASSOC]);

val EVERY2_IMP_LENGTH = listTheory.LIST_REL_LENGTH

val BIJ_UPDATE = prove(
  ``BIJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
    BIJ ((x =+ y) f) (x INSERT s) (y INSERT t)``,
  SIMP_TAC std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_INSERT,APPLY_UPDATE_THM]
  \\ METIS_TAC []);

val INJ_UPDATE = store_thm("INJ_UPDATE",
  ``INJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
    INJ ((x =+ y) f) (x INSERT s) (y INSERT t)``,
  SIMP_TAC std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_INSERT,APPLY_UPDATE_THM]
  \\ METIS_TAC []);

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

val _ = augment_srw_ss [rewrites [LIST_REL_def]];

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

val heap_lookup_MEM = store_thm("heap_lookup_MEM",
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
  \\ FULL_SIMP_TAC std_ss [EVERY2_APPEND,LIST_REL_def]
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

val heap_lookup_PREFIX = store_thm("heap_lookup_PREFIX",
  ``!xs. (heap_lookup (heap_length xs) (xs ++ x::ys) = SOME x)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [heap_lookup_def,APPEND,heap_length_def]
  \\ SRW_TAC [] [] \\ Cases_on `h`
  \\ FULL_SIMP_TAC std_ss [el_length_def] \\ DECIDE_TAC);

val heap_lookup_EXTEND = store_thm("heap_lookup_EXTEND",
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

val heap_addresses_APPEND = prove(
  ``!xs ys n. heap_addresses n (xs ++ ys) =
              heap_addresses n xs UNION heap_addresses (n + heap_length xs) ys``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [APPEND,heap_addresses_def,heap_length_def]
  \\ FULL_SIMP_TAC (srw_ss()) [EXTENSION,DISJ_ASSOC,ADD_ASSOC]);

val LESS_IMP_heap_lookup = store_thm("LESS_IMP_heap_lookup",
  ``!xs j ys. j < heap_length xs ==> (heap_lookup j (xs ++ ys) = heap_lookup j xs)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [heap_length_def,heap_lookup_def]
  \\ SRW_TAC [] [] \\ `j - el_length h < SUM (MAP el_length xs)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []);

val NOT_LESS_IMP_heap_lookup = store_thm("NOT_LESS_IMP_heap_lookup",
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

val IMP_IMP = miscLib.IMP_IMP
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

val full_gc_thm = store_thm("full_gc_thm",
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

val heap_length_heap_expand = store_thm("heap_length_heap_expand",
  ``!n. heap_length (heap_expand n) = n``,
  Cases \\ EVAL_TAC \\ FULL_SIMP_TAC (srw_ss()) [el_length_def,ADD1,SUM_ACC_DEF]);

val EVERY_isDataElement_IMP_LEMMA = prove(
  ``!heap2. EVERY isDataElement heap2 ==> (FILTER isForwardPointer heap2 = [])``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [isDataElement_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [isForwardPointer_def]);

val heap_lookup_LESS = store_thm("heap_lookup_LESS",
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

val MEM_IMP_heap_lookup = store_thm("MEM_IMP_heap_lookup",
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

val full_gc_LENGTH = store_thm("full_gc_LENGTH",
  ``roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) limit ==>
    ?roots2 heap2 a2.
      (full_gc (roots:'a heap_address list,heap,limit) =
      (roots2,heap2,heap_length heap2,T))``,
  REPEAT STRIP_TAC \\ MP_TAC full_gc_thm \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [gc_inv_def,APPEND_NIL]);

val full_gc_ok = store_thm("full_gc_ok",
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

val full_gc_related = store_thm("full_gc_related",
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

val _ = export_theory();
