(*
  Types, functions and lemmas that are shared between GC definitions
*)
open preamble wordsTheory wordsLib integer_wordTheory;

val _ = new_theory "gc_shared";

val _ = ParseExtras.temp_loose_equality();

(* The ML heap is represented as a list of heap_elements. *)

val _ = Datatype `
  heap_address = Pointer num 'a | Data 'a`;

val _ = Datatype `
  heap_element = Unused num
               | ForwardPointer num 'a num
               | DataElement (('a heap_address) list) num 'b`;


val _ = Datatype `
  gc_state =
    <| old : ('a, 'b) heap_element list (* old generations *)
     ; h1 : ('a, 'b) heap_element list (* final left heap *)
     ; h2 : ('a, 'b) heap_element list (* not updated left heap *)
     ; r4 : ('a, 'b) heap_element list (* not updated right heap *)
     ; r3 : ('a, 'b) heap_element list (* temp. final right heap *)
     ; r2 : ('a, 'b) heap_element list (* temp. not updated right heap *)
     ; r1 : ('a, 'b) heap_element list (* final right heap *)
     ; a : num                         (* gen_start + heap_length (h1 ++ h2) *)
     ; n : num                         (* unused heap space *)
     ; ok : bool                       (* OK *)
     ; heap : ('a, 'b) heap_element list (* old heap (w/ fwd pointers) *)
     ; heap0 : ('a, 'b) heap_element list (* old heap *)
     |>`;

val empty_state_def = Define `
  empty_state =
    <| old := []
     ; h1 := []
     ; h2 := []
     ; r4 := []
     ; r3 := []
     ; r2 := []
     ; r1 := []
     ; a := 0
     ; n := 0
     (* ; r := 0 *)
     ; ok := T
     ; heap := []
     ; heap0 := []
     |>`;

(* The heap is accessed using the following lookup function. *)

val el_length_def = Define `
  (el_length (Unused l) = l+1) /\
  (el_length (ForwardPointer n d l) = l+1) /\
  (el_length (DataElement xs l data) = l+1)`;

Theorem el_length_NOT_0:
   !el. el_length el <> 0
Proof
  Cases \\ fs [el_length_def]
QED

Theorem el_length_GT_0:
   !el. 1 <= el_length el
Proof
  Cases \\ fs [el_length_def]
QED

val heap_length_def = Define `
  heap_length heap = SUM (MAP el_length heap)`;

Theorem heap_length_NIL[simp]:
   heap_length [] = 0
Proof
  fs [heap_length_def]
QED

Theorem heap_length_GTE:
   !heap. 0 <= heap_length heap
Proof
  fs [heap_length_def]
QED

Theorem heap_length_APPEND:
   heap_length (xs ++ ys) = heap_length xs + heap_length ys
Proof
  SRW_TAC [] [heap_length_def,SUM_APPEND]
QED

val heap_lookup_def = Define `
  (heap_lookup a [] = NONE) /\
  (heap_lookup a (x::xs) =
     if a = 0 then SOME x else
     if a < el_length x then NONE else heap_lookup (a - el_length x) xs)`;

Theorem heap_lookup_MEM:
   !heap n x. (heap_lookup n heap = SOME x) ==> MEM x heap
Proof
  Induct \\ full_simp_tac std_ss [heap_lookup_def] \\ SRW_TAC [] []
  \\ res_tac \\ full_simp_tac std_ss []
QED

Theorem MEM_IMP_heap_lookup:
   !xs x. MEM x xs ==> ?j. (heap_lookup j xs = SOME x)
Proof
  Induct \\ full_simp_tac std_ss [MEM,heap_lookup_def]
  \\ SRW_TAC [] [] \\ res_tac THEN1 metis_tac []
  \\ qexists_tac `j + el_length h` \\ full_simp_tac std_ss [] \\ SRW_TAC [] []
  \\ Cases_on `h` \\ full_simp_tac std_ss [el_length_def] \\ `F` by decide_tac
QED

Theorem heap_lookup_LESS:
   !xs n. (heap_lookup n xs = SOME x) ==> n < heap_length xs
Proof
  Induct \\ full_simp_tac std_ss [heap_lookup_def] \\ SRW_TAC [] []
  \\ res_tac \\ Cases_on `h` \\ full_simp_tac (srw_ss())
      [heap_length_def,el_length_def] \\ decide_tac
QED

val heap_split_def = Define `
  (heap_split a [] = if a = 0 then SOME ([],[]) else NONE) /\
  (heap_split a (el::heap) =
    if a = 0 then SOME ([],el::heap) else
    if a < el_length el then NONE else
    case heap_split (a - el_length el) heap of
    | NONE => NONE
    | SOME (h1,h2) =>
      SOME (el::h1,h2))`;

Theorem heap_lookup_SPLIT:
   !heap n x. (heap_lookup n heap = SOME x) ==>
               ?ha hb. (heap = ha ++ x::hb) /\ (n = heap_length ha)
Proof
  Induct \\ full_simp_tac std_ss [heap_lookup_def] \\ SRW_TAC [] []
  THEN1 (Q.LIST_EXISTS_TAC [`[]`,`heap`] \\ full_simp_tac (srw_ss()) [heap_length_def])
  \\ res_tac \\ Q.LIST_EXISTS_TAC [`h::ha`,`hb`]
  \\ full_simp_tac (srw_ss()) [heap_length_def] \\ decide_tac
QED

val heap_drop_def = Define `
  heap_drop n (heap:('a,'b) heap_element list) =
    case heap_split n heap of
    | NONE => ARB
    | SOME (h1,h2) => h2`

val heap_take_def = Define `
  heap_take n (heap:('a,'b) heap_element list) =
    case heap_split n heap of
    | NONE => ARB
    | SOME (h1,h2) => h1`

Theorem heap_split_heap_length:
   !heap h1 h2 a.
    (heap_split a heap = SOME (h1,h2))
    ==>
    (heap_length h1 = a) /\
    (heap_length (h1 ++ h2) = heap_length heap) /\
    (h1 ++ h2 = heap)
Proof
  Induct
  \\ fs [heap_split_def]
  \\ rpt gen_tac
  \\ IF_CASES_TAC
  >- (strip_tac
     \\ fs []
     \\ rveq
     \\ fs [heap_length_def,el_length_def])
  \\ IF_CASES_TAC
  \\ fs []
  \\ BasicProvers.TOP_CASE_TAC
  \\ BasicProvers.TOP_CASE_TAC
  \\ strip_tac
  \\ rveq \\ fs []
  \\ first_x_assum drule
  \\ fs []
  \\ strip_tac
  \\ fs [heap_length_def]
QED

val heap_segment_def = Define `
  heap_segment (a, b) heap =
    case heap_split a heap of
    | NONE => NONE
    | SOME (h1,heap') =>
      if b < a then NONE else
      case heap_split (b - heap_length h1) heap' of
      | NONE => NONE
      | SOME (h2,h3) => SOME (h1,h2,h3)`;

Theorem heap_segment_IMP:
   !heap a b h1 h2 h3.
    (heap_segment (a,b) heap = SOME (h1,h2,h3)) ==>
    (h1 ++ h2 ++ h3 = heap) /\
    (heap_length h1 = a) /\
    (heap_length (h1 ++ h2) = b) /\
    (heap_length h3 = (heap_length heap - b))
Proof
  rpt gen_tac
  \\ fs [heap_segment_def]
  \\ Cases_on `heap_split a heap` \\ fs []
  \\ Cases_on `x` \\ fs []
  \\ Cases_on `heap_split (b − heap_length q) r` \\ fs []
  \\ Cases_on `x` \\ fs []
  \\ strip_tac
  \\ rveq \\ fs []
  \\ drule heap_split_heap_length
  \\ qpat_x_assum `heap_split _ _ = _` kall_tac
  \\ drule heap_split_heap_length
  \\ fs []
  \\ strip_tac \\ strip_tac
  \\ rveq
  \\ fs []
  \\ fs [heap_length_APPEND]
QED

val heap_restrict_def = Define `
  heap_restrict start end (heap:('a,'b) heap_element list) =
     case heap_segment (start,end) heap of
     | NONE => []
     | SOME (h1,h2,h3) => h2`;

(* The heap is well-formed if heap_ok *)

val isDataElement_def = Define `
  isDataElement x = ?ys l d. x = DataElement ys l d`;

val isSomeDataElement_def = Define `
  isSomeDataElement x = ?ys l d. x = SOME (DataElement ys l d)`;

val isSomeForwardPointer_def = Define `
  isSomeForwardPointer x = ?ptr d l. x = SOME (ForwardPointer ptr d l)`;

val isSomeDataOrForward_def = Define `
  isSomeDataOrForward x = isSomeForwardPointer x \/ isSomeDataElement x`;

val roots_ok_def = Define `
  roots_ok roots heap =
    !ptr u. MEM (Pointer ptr u) roots ==> isSomeDataElement (heap_lookup ptr heap)`;

val isForwardPointer_def = Define `
  (isForwardPointer (ForwardPointer n d l) = T) /\
  (isForwardPointer _ = F)`;

val heap_ok_def = Define `
  heap_ok heap limit =
    (heap_length heap = limit) /\
    (* no forward pointers *)
    (FILTER isForwardPointer heap = []) /\
    (* all pointers in DataElements point to some DataElement *)
    (!xs l d ptr u. MEM (DataElement xs l d) heap /\ MEM (Pointer ptr u) xs ==>
                    isSomeDataElement (heap_lookup ptr heap))`;

val gc_forward_ptr_def = Define `
  (* replace cell at a with a forwardpointer to ptr *)
  (gc_forward_ptr a [] ptr d ok = ([],F)) /\
  (gc_forward_ptr a (x::xs) ptr d ok =
     if a = 0 then
       (ForwardPointer ptr d ((el_length x)-1) :: xs, isDataElement x /\ ok) else
     if a < el_length x then (x::xs,F) else
       let (xs,ok) = gc_forward_ptr (a - el_length x) xs ptr d ok in
         (x::xs,ok))`;

Theorem gc_forward_ptr_ok:
   !heap n a c x. (gc_forward_ptr n heap a d c = (x,T)) ==> c
Proof
  Induct \\ simp_tac std_ss [Once gc_forward_ptr_def] \\ rpt strip_tac
  \\ Cases_on `n = 0` \\ full_simp_tac std_ss []
  \\ Cases_on `n < el_length h` \\ full_simp_tac std_ss []
  \\ Cases_on `gc_forward_ptr (n - el_length h) heap a d c`
  \\ full_simp_tac std_ss [LET_DEF] \\ Cases_on `r`
  \\ full_simp_tac std_ss [] \\ res_tac
QED

Theorem gc_forward_ptr_thm:
   !ha. gc_forward_ptr (heap_length ha) (ha ++ DataElement ys l d::hb) a u c =
         (ha ++ ForwardPointer a u l::hb,c)
Proof
  Induct \\ full_simp_tac (srw_ss()) [gc_forward_ptr_def,heap_length_def,APPEND,
    el_length_def,isDataElement_def,LET_DEF] \\ SRW_TAC [] []
  \\ Cases_on `h` \\ full_simp_tac std_ss [el_length_def] \\ decide_tac
QED

(*Theorem gc_forward_ptr_ok:
   !heap n a ok x. (gc_forward_ptr n heap a d ok = (x,T)) ==> ok
Proof
  Induct
  >- simp [gc_forward_ptr_def]
  \\ once_rewrite_tac [gc_forward_ptr_def]
  \\ ntac 5 strip_tac
  \\ IF_CASES_TAC
  >- (once_rewrite_tac [PAIR_EQ] \\ strip_tac \\ fs [])
  \\ IF_CASES_TAC
  >- metis_tac [PAIR_EQ]
  \\ rewrite_tac [LET_THM]
  \\ pairarg_tac
  \\ asm_rewrite_tac []
  \\ DISCH_TAC
  \\ fs []
  \\ qpat_x_assum `!n a ok x. _` (qspecl_then [`n - el_length h`,`a`,`ok`,`xs`] assume_tac)
  \\ fs []
QED*)

val heap_expand_def = Define `
  heap_expand n = if n = 0 then [] else [Unused (n-1)]`;

val heap_map_def = Define `
  (heap_map a [] = FEMPTY) /\
  (heap_map a (ForwardPointer ptr d l::xs) =
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
  (ADDR_MAP f (Pointer a d::xs) = Pointer (f a) d :: ADDR_MAP f xs)`;

Theorem ADDR_MAP_EQ:
   !xs. (!p d. MEM (Pointer p d) xs ==> (f p = g p)) ==>
         (ADDR_MAP f xs = ADDR_MAP g xs)
Proof
  Induct \\ TRY (Cases_on `h`) \\ full_simp_tac (srw_ss()) [ADDR_MAP_def]
  \\ metis_tac []
QED

Theorem ADDR_MAP_LENGTH:
   !xs f. LENGTH xs = LENGTH (ADDR_MAP f xs)
Proof
  Induct \\ fs [ADDR_MAP_def]
  \\ Cases \\ fs [ADDR_MAP_def]
QED

Theorem ADDR_MAP_APPEND:
   !h1 h2 f.
    ADDR_MAP f (h1 ++ h2) = ADDR_MAP f h1 ++ ADDR_MAP f h2
Proof
  Induct >- fs [ADDR_MAP_def]
  \\ Cases \\ fs [ADDR_MAP_def]
QED

val ADDR_APPLY_def = Define `
  (ADDR_APPLY f (Pointer x d) = Pointer (f x) d) /\
  (ADDR_APPLY f (Data y) = Data y)`;

val heap_lookup_FLOOKUP = save_thm("heap_lookup_FLOOKUP",Q.prove(
  `!heap n k.
      (heap_lookup n heap = SOME (ForwardPointer ptr u l)) ==>
      (FLOOKUP (heap_map k heap) (n+k) = SOME ptr)`,
  Induct \\ full_simp_tac std_ss [heap_lookup_def] \\ SRW_TAC [] []
  THEN1 (full_simp_tac (srw_ss()) [heap_map_def,FLOOKUP_DEF])
  \\ res_tac \\ pop_assum (ASSUME_TAC o Q.SPEC `k + el_length h`)
  \\ `n - el_length h + (k + el_length h) = n + k` by decide_tac
  \\ full_simp_tac std_ss []
  \\ Cases_on `h` \\ full_simp_tac std_ss [heap_map_def,el_length_def]
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,ADD_ASSOC,FAPPLY_FUPDATE_THM])
  |> Q.SPECL [`heap`,`n`,`0`] |> SIMP_RULE std_ss []);

val _ = augment_srw_ss [rewrites [LIST_REL_def]];

val heaps_similar_def = Define `
  heaps_similar heap0 heap =
    EVERY2 (\h0 h. if isForwardPointer h then
                     (el_length h = el_length h0) /\ isDataElement h0
                   else (h = h0)) heap0 heap`

Theorem IN_heap_map_IMP:
   !heap n k. n IN FDOM (heap_map k heap) ==> k <= n
Proof
  Induct \\ TRY (Cases_on `h`) \\ full_simp_tac (srw_ss()) [heap_map_def]
  \\ rpt strip_tac \\ res_tac
  \\ full_simp_tac (srw_ss()) [heap_length_def,el_length_def] \\ decide_tac
QED

val NOT_IN_heap_map = save_thm("NOT_IN_heap_map", Q.prove(
  `!ha n. ~(n + heap_length ha IN FDOM (heap_map n (ha ++ DataElement ys l d::hb)))`,
  Induct \\ full_simp_tac (srw_ss()) [heap_map_def,APPEND,heap_length_def]
  \\ rpt strip_tac \\ imp_res_tac IN_heap_map_IMP
  \\ full_simp_tac std_ss [ADD_ASSOC] \\ res_tac
  THEN1 (full_simp_tac std_ss [el_length_def] \\ decide_tac)
  \\ Cases_on `h` \\ full_simp_tac std_ss [heap_map_def]
  \\ res_tac \\ full_simp_tac (srw_ss()) [el_length_def,ADD_ASSOC] \\ res_tac
  \\ decide_tac) |> Q.SPECL [`ha`,`0`] |> SIMP_RULE std_ss [])

Theorem isSomeDataOrForward_lemma:
   !ha ptr.
      isSomeDataOrForward (heap_lookup ptr (ha ++ DataElement ys l d::hb)) <=>
      isSomeDataOrForward (heap_lookup ptr (ha ++ [ForwardPointer a u l] ++ hb))
Proof
  Induct \\ full_simp_tac std_ss [APPEND,heap_lookup_def]
  \\ SRW_TAC [] [] \\ full_simp_tac std_ss []
  \\ EVAL_TAC \\ full_simp_tac std_ss [el_length_def]
QED

Theorem heaps_similar_IMP_heap_length:
   !xs ys. heaps_similar xs ys ==> (heap_length xs = heap_length ys)
Proof
  Induct \\ Cases_on `ys`
  \\ full_simp_tac (srw_ss()) [heaps_similar_def,heap_length_def]
  \\ rpt strip_tac \\ Cases_on `isForwardPointer h`
  \\ full_simp_tac std_ss []
QED

Theorem heap_similar_Data_IMP:
   heaps_similar heap0 (ha ++ DataElement ys l d::hb) ==>
    ?ha0 hb0. (heap0 = ha0 ++ DataElement ys l d::hb0) /\
              (heap_length ha = heap_length ha0)
Proof
  rpt strip_tac \\ full_simp_tac std_ss [heaps_similar_def]
  \\ imp_res_tac LIST_REL_SPLIT2 \\ fs[isForwardPointer_def]
  \\ Q.LIST_EXISTS_TAC [`ys1`,`xs`] \\ full_simp_tac std_ss []
  \\ `heaps_similar ys1 ha` by full_simp_tac std_ss [heaps_similar_def]
  \\ full_simp_tac std_ss [heaps_similar_IMP_heap_length]
QED

Theorem heaps_similar_lemma:
   !ha heap0.
      heaps_similar heap0 (ha ++ DataElement ys l d::hb) ==>
      heaps_similar heap0 (ha ++ [ForwardPointer (heap_length (h1 ++ h2)) u l] ++ hb)
Proof
  full_simp_tac std_ss [heaps_similar_def] \\ rpt strip_tac
  \\ imp_res_tac LIST_REL_SPLIT2 \\ fs[]
  \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ match_mp_tac EVERY2_APPEND_suff
  \\ fs[isForwardPointer_def,el_length_def]
  \\ rw[el_length_def,isDataElement_def]
QED

Theorem heap_lookup_PREFIX:
   !xs. (heap_lookup (heap_length xs) (xs ++ x::ys) = SOME x)
Proof
  Induct \\ full_simp_tac (srw_ss()) [heap_lookup_def,APPEND,heap_length_def]
  \\ SRW_TAC [] [] \\ Cases_on `h`
  \\ full_simp_tac std_ss [el_length_def] \\ decide_tac
QED

Theorem heap_lookup_EXTEND:
   !xs n ys x. (heap_lookup n xs = SOME x) ==>
                (heap_lookup n (xs ++ ys) = SOME x)
Proof
  Induct \\ full_simp_tac (srw_ss()) [heap_lookup_def] \\ SRW_TAC [] []
QED

Theorem heap_map_APPEND:
   !xs n ys. (heap_map n (xs ++ ys)) =
              FUNION (heap_map n xs) (heap_map (n + heap_length xs) ys)
Proof
  Induct \\ TRY (Cases_on `h`) \\ full_simp_tac (srw_ss())
     [APPEND,heap_map_def,FUNION_DEF,FUNION_FEMPTY_1,heap_length_def,ADD_ASSOC]
  \\ full_simp_tac std_ss [FUNION_FUPDATE_1,el_length_def,ADD_ASSOC]
QED

val FDOM_heap_map = save_thm("FDOM_heap_map", Q.prove(
  `!xs n. ~(n + heap_length xs IN FDOM (heap_map n xs))`,
  Induct \\ TRY (Cases_on `h`)
  \\ full_simp_tac (srw_ss()) [heap_map_def,heap_length_def,ADD_ASSOC]
  \\ rpt strip_tac \\ full_simp_tac std_ss [el_length_def,ADD_ASSOC]
  \\ TRY decide_tac \\ metis_tac [])
  |> Q.SPECL [`xs`,`0`] |> SIMP_RULE std_ss []);

Theorem heap_addresses_APPEND:
   !xs ys n. heap_addresses n (xs ++ ys) =
              heap_addresses n xs UNION heap_addresses (n + heap_length xs) ys
Proof
  Induct \\ full_simp_tac (srw_ss()) [APPEND,heap_addresses_def,heap_length_def]
  \\ full_simp_tac (srw_ss()) [EXTENSION,DISJ_ASSOC,ADD_ASSOC]
QED

Theorem LESS_IMP_heap_lookup:
   !xs j ys. j < heap_length xs ==> (heap_lookup j (xs ++ ys) = heap_lookup j xs)
Proof
  Induct \\ full_simp_tac (srw_ss()) [heap_length_def,heap_lookup_def]
  \\ SRW_TAC [] [] \\ `j - el_length h < SUM (MAP el_length xs)` by decide_tac
  \\ full_simp_tac std_ss []
QED

Theorem NOT_LESS_IMP_heap_lookup:
   !xs j ys. ~(j < heap_length xs) ==>
              (heap_lookup j (xs ++ ys) = heap_lookup (j - heap_length xs) ys)
Proof
  Induct \\ full_simp_tac (srw_ss()) [heap_length_def,heap_lookup_def]
  \\ SRW_TAC [] [SUB_PLUS]
  THEN1 (Cases_on `h` \\ full_simp_tac std_ss [el_length_def] \\ `F` by decide_tac)
  THEN1 (Cases_on `h` \\ full_simp_tac std_ss [el_length_def] \\ `F` by decide_tac)
QED

Theorem heap_similar_Data_IMP_DataOrForward:
   !heap0 heap1 ptr.
      heaps_similar heap0 heap1 /\ isSomeDataElement (heap_lookup ptr heap0) ==>
      isSomeDataOrForward (heap_lookup ptr heap1)
Proof
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
  \\ full_simp_tac std_ss [] \\ res_tac
QED

Theorem FILTER_LEMMA:
   !heap. (FILTER isForwardPointer heap = []) ==>
           (FILTER (\h. ~isForwardPointer h) heap = heap)
Proof
  Induct \\ full_simp_tac (srw_ss()) [] \\ SRW_TAC [] []
QED

Theorem heaps_similar_REFL:
   !xs. (FILTER isForwardPointer xs = []) ==> heaps_similar xs xs
Proof
  Induct \\ full_simp_tac (srw_ss()) [heaps_similar_def] \\ SRW_TAC [] []
QED

Theorem heap_map_EMPTY:
   !xs n. (FILTER isForwardPointer xs = []) ==> (FDOM (heap_map n xs) = {})
Proof
  Induct \\ TRY (Cases_on `h`)
  \\ full_simp_tac (srw_ss()) [heap_map_def,isForwardPointer_def]
QED

Theorem MEM_ADDR_MAP:
   !xs f ptr u. MEM (Pointer ptr u) (ADDR_MAP f xs) ==>
                 ?y. MEM (Pointer y u) xs /\ (f y = ptr)
Proof
  Induct \\ TRY (Cases_on `h`) \\ full_simp_tac (srw_ss()) [ADDR_MAP_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [] \\ res_tac \\ metis_tac []
QED

Theorem heap_length_heap_expand:
   !n. heap_length (heap_expand n) = n
Proof
  Cases \\ EVAL_TAC \\ full_simp_tac (srw_ss()) [el_length_def,ADD1,SUM_ACC_DEF]
QED

Theorem EVERY_isDataElement_IMP_LEMMA:
   !heap2. EVERY isDataElement heap2 ==> (FILTER isForwardPointer heap2 = [])
Proof
  Induct \\ full_simp_tac (srw_ss()) [isDataElement_def] \\ rpt strip_tac
  \\ full_simp_tac (srw_ss()) [isForwardPointer_def]
QED

Theorem isSome_heap_looukp_IMP_APPEND:
   !xs ptr. isSomeDataElement (heap_lookup ptr xs) ==>
             isSomeDataElement (heap_lookup ptr (xs ++ ys))
Proof
  full_simp_tac std_ss [isSomeDataElement_def] \\ rpt strip_tac
  \\ imp_res_tac heap_lookup_LESS \\ imp_res_tac LESS_IMP_heap_lookup
  \\ full_simp_tac (srw_ss()) []
QED

Theorem heap_split_APPEND_if:
   !h1 n h2. heap_split n (h1 ++ h2) =
  if n < heap_length h1 then
    case heap_split n h1 of
        NONE => NONE
      | SOME(h1',h2') => SOME(h1',h2'++h2)
  else
    case heap_split (n - heap_length h1) h2 of
        NONE => NONE
      | SOME(h1',h2') => SOME(h1++h1',h2')
Proof
  Induct >> fs[heap_split_def] >> rpt strip_tac
  >- (Cases_on `heap_split n h2` >> fs[] >> Cases_on `x` >> fs[])
  >> IF_CASES_TAC >- (fs[heap_length_def] >> Cases_on `h` >> fs[el_length_def])
  >> IF_CASES_TAC >- fs[heap_length_def]
  >> IF_CASES_TAC >- (fs[heap_length_def] >> every_case_tac >> fs[])
  >> fs[heap_length_def] >> every_case_tac >> fs[]
QED

Theorem heap_split_0[simp]:
   heap_split 0 h = SOME ([],h)
Proof
  Cases_on `h` \\ fs [heap_split_def]
QED

(* --- *)

val gc_related_def = Define `
  gc_related (f:num|->num) heap1 heap2 =
    INJ (FAPPLY f) (FDOM f) { a | isSomeDataElement (heap_lookup a heap2) } /\
    (!i. i IN FDOM f ==> isSomeDataElement (heap_lookup i heap1)) /\
    !i xs l d.
      i IN FDOM f /\ (heap_lookup i heap1 = SOME (DataElement xs l d)) ==>
      (heap_lookup (f ' i) heap2 = SOME (DataElement (ADDR_MAP (FAPPLY f) xs) l d)) /\
      !ptr u. MEM (Pointer ptr u) xs ==> ptr IN FDOM f`;

(* an edge in the heap *)

val gc_edge_def = Define `
  gc_edge heap x y <=>
    ?xs l d t. (heap_lookup x heap = SOME (DataElement xs l d)) /\
               MEM (Pointer y t) xs`;

val reachable_addresses_def = Define `
  reachable_addresses roots heap y =
    ?t x. MEM (Pointer x t) roots /\ RTC (gc_edge heap) x y`

Theorem heap_addresses_LESS_heap_length:
   ∀heap n k. k ∈ heap_addresses n heap ⇒ k < n + heap_length heap
Proof
  Induct \\ fs [heap_addresses_def,heap_length_def]
  \\ rw [] THEN1 (Cases_on `h` \\ fs [el_length_def])
  \\ res_tac \\ fs []
QED

Theorem heap_addresses_LESS:
   ∀heap n k. k ∈ heap_addresses n heap ==> n <= k
Proof
  Induct \\ fs [heap_addresses_def,heap_length_def]
  \\ rw [] \\ fs [] \\ res_tac \\ fs []
QED

Theorem FINITE_heap_addresses:
   !xs n. FINITE (heap_addresses n xs)
Proof
  Induct \\ fs [heap_addresses_def]
QED

Theorem CARD_heap_addresses:
   !xs n. CARD (heap_addresses n xs) = LENGTH xs
Proof
  Induct \\ fs [heap_addresses_def]
  \\ fs [CARD_INSERT,FINITE_heap_addresses]
  \\ rw [] \\ imp_res_tac heap_addresses_LESS \\ fs []
  \\ Cases_on `h` \\ fs [el_length_def]
QED

val heap_filter_aux_def = Define `
  (heap_filter_aux n P [] = []) /\
  (heap_filter_aux n P (x::xs) =
     (if n IN P then [x] else []) ++ heap_filter_aux (n + el_length x) P xs)`;

val heap_filter_def = Define `
  heap_filter = heap_filter_aux 0`;

Theorem heap_filter_EMPTY:
   !heap. heap_filter ∅ heap = []
Proof
  fs [heap_filter_def] \\ qspec_tac (`0n`,`n`)
  \\ Induct_on `heap` \\ fs [heap_filter_aux_def]
QED

val heap_length_heap_filter_INSERT = prove(
  ``!heap.
      ~(e IN s) ==>
      (heap_length (heap_filter (e INSERT s) heap) =
       heap_length (heap_filter {e} heap) + heap_length (heap_filter s heap))``,
  fs [heap_filter_def]
  \\ qspec_tac (`0n`,`n:num`)
  \\ Induct_on `heap` \\ fs [heap_filter_aux_def,heap_length_def]
  \\ rpt strip_tac \\ fs [SUM_APPEND] \\ rw [] \\ fs []);

val heap_filter_aux_ADD_SING = prove(
  ``!k n e heap.
      heap_filter_aux (k+n) {e+n} heap = heap_filter_aux k {e} heap``,
  Induct_on `heap`
  \\ fs [heap_filter_aux_def] \\ rw []
  \\ first_x_assum (qspecl_then [`k+el_length h`,`n`,`e`] mp_tac)
  \\ fs []) |> Q.SPEC `0` |> SIMP_RULE std_ss [];

val heap_filter_aux_SING_ZERO = prove(
  ``!heap n. 0 < n ==> (heap_filter_aux n {0} heap = [])``,
  Induct \\ fs [heap_filter_aux_def]);

val heap_lookup_IMP_heap_filter = prove(
  ``!heap e x. (heap_lookup e heap = SOME x) ==> (heap_filter {e} heap = [x])``,
  Induct \\ fs [heap_lookup_def] \\ rw []
  \\ fs [heap_filter_def,heap_filter_aux_def]
  \\ fs [NOT_LESS]
  THEN1
   (match_mp_tac heap_filter_aux_SING_ZERO
    \\ Cases_on `h` \\ EVAL_TAC \\ fs [])
  \\ fs [LESS_EQ_EXISTS] \\ rveq \\ fs []
  \\ fs [heap_filter_aux_ADD_SING]);

Theorem heap_length_heap_filter_eq:
   !s t f heap heap2.
      BIJ f s t /\ FINITE s /\ FINITE t /\
      (!i. i IN s ==>
           ?xs xs2 l d d.
             (heap_lookup i heap = SOME (DataElement xs l d)) /\
             (heap_lookup (f i) heap2 = SOME (DataElement xs2 l d))) ==>
      (heap_length (heap_filter t heap2) = heap_length (heap_filter s heap))
Proof
  strip_tac
  \\ Cases_on `FINITE s` \\ fs []
  \\ pop_assum mp_tac
  \\ qspec_tac (`s`,`s`)
  \\ ho_match_mp_tac FINITE_INDUCT \\ rw [heap_filter_EMPTY]
  \\ fs [BIJ_INSERT] \\ rfs []
  \\ `~(f e IN (t DELETE f e)) /\ FINITE (t DELETE f e)` by fs []
  \\ `t = f e INSERT (t DELETE f e)` by (fs [EXTENSION] \\ metis_tac [])
  \\ qabbrev_tac `t1 = t DELETE f e` \\ pop_assum kall_tac
  \\ rveq \\ fs []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once heap_length_heap_filter_INSERT]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once heap_length_heap_filter_INSERT]
  \\ match_mp_tac (DECIDE ``(m1=n1)/\(m2=n2) ==> (m1+m2=n1+n2:num)``)
  \\ conj_tac
  THEN1 (first_x_assum match_mp_tac \\ asm_exists_tac \\ fs [])
  \\ first_x_assum (qspec_then `e` mp_tac) \\ fs []
  \\ strip_tac \\ fs []
  \\ imp_res_tac heap_lookup_IMP_heap_filter
  \\ fs [] \\ EVAL_TAC
QED

val heap_length_heap_filter_aux = prove(
  ``!n heap x.
       heap_length (heap_filter_aux n (x UNION heap_addresses n heap) heap) =
       heap_length heap``,
  Induct_on `heap`
  \\ fs [heap_length_def,heap_filter_aux_def]
  \\ fs [heap_addresses_def] \\ rw []
  \\ first_x_assum (qspecl_then [`n + el_length h`,`n INSERT x`] (assume_tac o GSYM))
  \\ fs []
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ rw [EXTENSION] \\ eq_tac \\ rw [] \\ fs []);

Theorem heap_length_heap_filter:
   !heap.
      heap_length (heap_filter (heap_addresses 0 heap) heap) =
      heap_length heap
Proof
  fs [heap_filter_def]
  \\ metis_tac [heap_length_heap_filter_aux,UNION_EMPTY]
QED

Theorem heap_filter_aux_APPEND:
   !xs ys n s.
      heap_filter_aux n s (xs ++ ys) =
      heap_filter_aux n s xs ++ heap_filter_aux (n + heap_length xs) s ys
Proof
  Induct \\ fs [heap_filter_aux_def,heap_length_def]
QED

Theorem heap_filter_aux_heap_addresses_UNION:
   !xs n s. heap_filter_aux n (heap_addresses n xs UNION s) xs = xs
Proof
  Induct \\ fs [heap_filter_aux_def,heap_addresses_def] \\ rw []
  \\ `(n INSERT heap_addresses (n + el_length h) xs) ∪ s =
      heap_addresses (n + el_length h) xs ∪ (n INSERT s)` by
        (fs [EXTENSION] \\ metis_tac []) \\ fs []
QED

val _ = export_theory();
