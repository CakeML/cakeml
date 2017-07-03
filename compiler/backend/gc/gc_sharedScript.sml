open preamble wordsTheory wordsLib integer_wordTheory;

val _ = new_theory "gc_shared";

val _ = ParseExtras.temp_loose_equality();

(* TODO: move *)

val EVERY2_SPLIT = store_thm("EVERY2_SPLIT",
  ``!xs1 zs.
      EVERY2 P zs (xs1 ++ x::xs2) ==>
      ?ys1 y ys2. (zs = ys1 ++ y::ys2) /\ EVERY2 P ys1 xs1 /\
                  EVERY2 P ys2 xs2 /\ P y x``,
  Induct \\ full_simp_tac std_ss [APPEND]
  \\ Cases_on `zs` \\ full_simp_tac (srw_ss()) []
  \\ rpt strip_tac \\ res_tac \\ full_simp_tac std_ss []
  \\ Q.LIST_EXISTS_TAC [`h::ys1`,`y`,`ys2`] \\ full_simp_tac (srw_ss()) []);

val EVERY2_SPLIT_ALT = store_thm("EVERY2_SPLIT_ALT",
  ``!xs1 zs.
      EVERY2 P (xs1 ++ x::xs2) zs ==>
      ?ys1 y ys2. (zs = ys1 ++ y::ys2) /\ EVERY2 P xs1 ys1 /\
                  EVERY2 P xs2 ys2 /\ P x y``,
  Induct \\ full_simp_tac std_ss [APPEND]
  \\ Cases_on `zs` \\ full_simp_tac (srw_ss()) []
  \\ rpt strip_tac \\ res_tac \\ full_simp_tac std_ss []
  \\ Q.LIST_EXISTS_TAC [`h::ys1`,`y`,`ys2`] \\ full_simp_tac (srw_ss()) []);

val EVERY2_APPEND = store_thm("EVERY2_APPEND",
  ``!xs ts.
      (LENGTH xs = LENGTH ts) ==>
      (EVERY2 P (xs ++ ys) (ts ++ us) = EVERY2 P xs ts /\ EVERY2 P ys us)``,
  Induct \\ Cases_on `ts` \\ full_simp_tac (srw_ss()) [LENGTH,CONJ_ASSOC]);

val BIJ_UPDATE = store_thm("BIJ_UPDATE",
  ``!f s t x y. BIJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
    BIJ ((x =+ y) f) (x INSERT s) (y INSERT t)``,
  simp_tac std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_INSERT,APPLY_UPDATE_THM]
  \\ metis_tac []);

val INJ_UPDATE = store_thm("INJ_UPDATE",
  ``INJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
    INJ ((x =+ y) f) (x INSERT s) (y INSERT t)``,
  simp_tac std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_INSERT,APPLY_UPDATE_THM]
  \\ metis_tac []);

(* Types, functions and lemmas that are shared between GC definitions
*)

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

val el_length_NOT_0 = store_thm("el_length_NOT_0",
  ``!el. el_length el <> 0``,
  Cases \\ fs [el_length_def]);

val el_length_GT_0 = store_thm("el_length_GT_0",
  ``!el. 1 <= el_length el``,
  Cases \\ fs [el_length_def]);

val heap_length_def = Define `
  heap_length heap = SUM (MAP el_length heap)`;

val heap_length_NIL = store_thm("heap_length_NIL[simp]",
  ``heap_length [] = 0``,
  fs [heap_length_def]);

val heap_length_GTE = store_thm("heap_length_GTE",
  ``!heap. 0 <= heap_length heap``,
  fs [heap_length_def])

val heap_length_APPEND = Q.store_thm("heap_length_APPEND",
  `heap_length (xs ++ ys) = heap_length xs + heap_length ys`,
  SRW_TAC [] [heap_length_def,SUM_APPEND]);

val heap_lookup_def = Define `
  (heap_lookup a [] = NONE) /\
  (heap_lookup a (x::xs) =
     if a = 0 then SOME x else
     if a < el_length x then NONE else heap_lookup (a - el_length x) xs)`;

val heap_lookup_MEM = Q.store_thm("heap_lookup_MEM",
  `!heap n x. (heap_lookup n heap = SOME x) ==> MEM x heap`,
  Induct \\ full_simp_tac std_ss [heap_lookup_def] \\ SRW_TAC [] []
  \\ res_tac \\ full_simp_tac std_ss []);

val MEM_IMP_heap_lookup = Q.store_thm("MEM_IMP_heap_lookup",
  `!xs x. MEM x xs ==> ?j. (heap_lookup j xs = SOME x)`,
  Induct \\ full_simp_tac std_ss [MEM,heap_lookup_def]
  \\ SRW_TAC [] [] \\ res_tac THEN1 metis_tac []
  \\ qexists_tac `j + el_length h` \\ full_simp_tac std_ss [] \\ SRW_TAC [] []
  \\ Cases_on `h` \\ full_simp_tac std_ss [el_length_def] \\ `F` by decide_tac);

val heap_lookup_LESS = Q.store_thm("heap_lookup_LESS",
  `!xs n. (heap_lookup n xs = SOME x) ==> n < heap_length xs`,
  Induct \\ full_simp_tac std_ss [heap_lookup_def] \\ SRW_TAC [] []
  \\ res_tac \\ Cases_on `h` \\ full_simp_tac (srw_ss())
      [heap_length_def,el_length_def] \\ decide_tac);

val heap_split_def = Define `
  (heap_split a [] = if a = 0 then SOME ([],[]) else NONE) /\
  (heap_split a (el::heap) =
    if a = 0 then SOME ([],el::heap) else
    if a < el_length el then NONE else
    case heap_split (a - el_length el) heap of
    | NONE => NONE
    | SOME (h1,h2) =>
      SOME (el::h1,h2))`;

val heap_lookup_SPLIT = Q.store_thm("heap_lookup_SPLIT",
  `!heap n x. (heap_lookup n heap = SOME x) ==>
               ?ha hb. (heap = ha ++ x::hb) /\ (n = heap_length ha)`,
  Induct \\ full_simp_tac std_ss [heap_lookup_def] \\ SRW_TAC [] []
  THEN1 (Q.LIST_EXISTS_TAC [`[]`,`heap`] \\ full_simp_tac (srw_ss()) [heap_length_def])
  \\ res_tac \\ Q.LIST_EXISTS_TAC [`h::ha`,`hb`]
  \\ full_simp_tac (srw_ss()) [heap_length_def] \\ decide_tac);

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

val heap_split_heap_length = store_thm("heap_split_heap_length",
  ``!heap h1 h2 a.
    (heap_split a heap = SOME (h1,h2))
    ==>
    (heap_length h1 = a) /\
    (heap_length (h1 ++ h2) = heap_length heap) /\
    (h1 ++ h2 = heap)``,
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
  \\ fs [heap_length_def]);

val heap_segment_def = Define `
  heap_segment (a, b) heap =
    case heap_split a heap of
    | NONE => NONE
    | SOME (h1,heap') =>
      if b < a then NONE else
      case heap_split (b - heap_length h1) heap' of
      | NONE => NONE
      | SOME (h2,h3) => SOME (h1,h2,h3)`;

val heap_segment_IMP = store_thm("heap_segment_IMP",
  ``!heap a b h1 h2 h3.
    (heap_segment (a,b) heap = SOME (h1,h2,h3)) ==>
    (h1 ++ h2 ++ h3 = heap) /\
    (heap_length h1 = a) /\
    (heap_length (h1 ++ h2) = b) /\
    (heap_length h3 = (heap_length heap - b))``,
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
  \\ fs [heap_length_APPEND]);

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

val gc_forward_ptr_ok = Q.store_thm("gc_forward_ptr_ok",
  `!heap n a c x. (gc_forward_ptr n heap a d c = (x,T)) ==> c`,
  Induct \\ simp_tac std_ss [Once gc_forward_ptr_def] \\ rpt strip_tac
  \\ Cases_on `n = 0` \\ full_simp_tac std_ss []
  \\ Cases_on `n < el_length h` \\ full_simp_tac std_ss []
  \\ Cases_on `gc_forward_ptr (n - el_length h) heap a d c`
  \\ full_simp_tac std_ss [LET_DEF] \\ Cases_on `r`
  \\ full_simp_tac std_ss [] \\ res_tac);

val gc_forward_ptr_thm = Q.store_thm("gc_forward_ptr_thm",
  `!ha. gc_forward_ptr (heap_length ha) (ha ++ DataElement ys l d::hb) a u c =
         (ha ++ ForwardPointer a u l::hb,c)`,
  Induct \\ full_simp_tac (srw_ss()) [gc_forward_ptr_def,heap_length_def,APPEND,
    el_length_def,isDataElement_def,LET_DEF] \\ SRW_TAC [] []
  \\ Cases_on `h` \\ full_simp_tac std_ss [el_length_def] \\ decide_tac);

(*val gc_forward_ptr_ok = store_thm("gc_forward_ptr_ok",
  ``!heap n a ok x. (gc_forward_ptr n heap a d ok = (x,T)) ==> ok``,
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
  \\ fs []);*)

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

val ADDR_MAP_EQ = store_thm("ADDR_MAP_EQ",
  ``!xs. (!p d. MEM (Pointer p d) xs ==> (f p = g p)) ==>
         (ADDR_MAP f xs = ADDR_MAP g xs)``,
  Induct \\ TRY (Cases_on `h`) \\ full_simp_tac (srw_ss()) [ADDR_MAP_def]
  \\ metis_tac []);

val ADDR_MAP_LENGTH = store_thm("ADDR_MAP_LENGTH",
  ``!xs f. LENGTH xs = LENGTH (ADDR_MAP f xs)``,
  Induct \\ fs [ADDR_MAP_def]
  \\ Cases \\ fs [ADDR_MAP_def]);

val ADDR_MAP_APPEND = store_thm("ADDR_MAP_APPEND",
  ``!h1 h2 f.
    ADDR_MAP f (h1 ++ h2) = ADDR_MAP f h1 ++ ADDR_MAP f h2``,
  Induct >- fs [ADDR_MAP_def]
  \\ Cases \\ fs [ADDR_MAP_def]);

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

val IN_heap_map_IMP = Q.store_thm("IN_heap_map_IMP",
  `!heap n k. n IN FDOM (heap_map k heap) ==> k <= n`,
  Induct \\ TRY (Cases_on `h`) \\ full_simp_tac (srw_ss()) [heap_map_def]
  \\ rpt strip_tac \\ res_tac
  \\ full_simp_tac (srw_ss()) [heap_length_def,el_length_def] \\ decide_tac);

val NOT_IN_heap_map = save_thm("NOT_IN_heap_map", Q.prove(
  `!ha n. ~(n + heap_length ha IN FDOM (heap_map n (ha ++ DataElement ys l d::hb)))`,
  Induct \\ full_simp_tac (srw_ss()) [heap_map_def,APPEND,heap_length_def]
  \\ rpt strip_tac \\ imp_res_tac IN_heap_map_IMP
  \\ full_simp_tac std_ss [ADD_ASSOC] \\ res_tac
  THEN1 (full_simp_tac std_ss [el_length_def] \\ decide_tac)
  \\ Cases_on `h` \\ full_simp_tac std_ss [heap_map_def]
  \\ res_tac \\ full_simp_tac (srw_ss()) [el_length_def,ADD_ASSOC] \\ res_tac
  \\ decide_tac) |> Q.SPECL [`ha`,`0`] |> SIMP_RULE std_ss [])

val isSomeDataOrForward_lemma = Q.store_thm("isSomeDataOrForward_lemma",
  `!ha ptr.
      isSomeDataOrForward (heap_lookup ptr (ha ++ DataElement ys l d::hb)) <=>
      isSomeDataOrForward (heap_lookup ptr (ha ++ [ForwardPointer a u l] ++ hb))`,
  Induct \\ full_simp_tac std_ss [APPEND,heap_lookup_def]
  \\ SRW_TAC [] [] \\ full_simp_tac std_ss []
  \\ EVAL_TAC \\ full_simp_tac std_ss [el_length_def]);

val heaps_similar_IMP_heap_length = Q.store_thm("heaps_similar_IMP_heap_length",
  `!xs ys. heaps_similar xs ys ==> (heap_length xs = heap_length ys)`,
  Induct \\ Cases_on `ys`
  \\ full_simp_tac (srw_ss()) [heaps_similar_def,heap_length_def]
  \\ rpt strip_tac \\ Cases_on `isForwardPointer h`
  \\ full_simp_tac std_ss []);

val heap_similar_Data_IMP = Q.store_thm("heap_similar_Data_IMP",
  `heaps_similar heap0 (ha ++ DataElement ys l d::hb) ==>
    ?ha0 hb0. (heap0 = ha0 ++ DataElement ys l d::hb0) /\
              (heap_length ha = heap_length ha0)`,
  rpt strip_tac \\ full_simp_tac std_ss [heaps_similar_def]
  \\ imp_res_tac EVERY2_SPLIT \\ full_simp_tac std_ss [isForwardPointer_def]
  \\ pop_assum (ASSUME_TAC o GSYM) \\ full_simp_tac std_ss []
  \\ Q.LIST_EXISTS_TAC [`ys1`,`ys2`] \\ full_simp_tac std_ss []
  \\ `heaps_similar ys1 ha` by full_simp_tac std_ss [heaps_similar_def]
  \\ full_simp_tac std_ss [heaps_similar_IMP_heap_length]);

val heaps_similar_lemma = Q.store_thm("heaps_similar_lemma",
  `!ha heap0.
      heaps_similar heap0 (ha ++ DataElement ys l d::hb) ==>
      heaps_similar heap0 (ha ++ [ForwardPointer (heap_length (h1 ++ h2)) u l] ++ hb)`,
  full_simp_tac std_ss [heaps_similar_def] \\ rpt strip_tac
  \\ imp_res_tac EVERY2_SPLIT \\ full_simp_tac std_ss []
  \\ imp_res_tac LIST_REL_LENGTH
  \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ full_simp_tac std_ss [EVERY2_APPEND,LIST_REL_def]
  \\ EVAL_TAC \\ full_simp_tac std_ss [isForwardPointer_def]
  \\ qpat_x_assum `DataElement ys l d = y` (mp_tac o GSYM)
  \\ full_simp_tac (srw_ss()) [el_length_def]);

val heap_lookup_PREFIX = Q.store_thm("heap_lookup_PREFIX",
  `!xs. (heap_lookup (heap_length xs) (xs ++ x::ys) = SOME x)`,
  Induct \\ full_simp_tac (srw_ss()) [heap_lookup_def,APPEND,heap_length_def]
  \\ SRW_TAC [] [] \\ Cases_on `h`
  \\ full_simp_tac std_ss [el_length_def] \\ decide_tac);

val heap_lookup_EXTEND = Q.store_thm("heap_lookup_EXTEND",
  `!xs n ys x. (heap_lookup n xs = SOME x) ==>
                (heap_lookup n (xs ++ ys) = SOME x)`,
  Induct \\ full_simp_tac (srw_ss()) [heap_lookup_def] \\ SRW_TAC [] []);

val heap_map_APPEND = Q.store_thm("heap_map_APPEND",
  `!xs n ys. (heap_map n (xs ++ ys)) =
              FUNION (heap_map n xs) (heap_map (n + heap_length xs) ys)`,
  Induct \\ TRY (Cases_on `h`) \\ full_simp_tac (srw_ss())
     [APPEND,heap_map_def,FUNION_DEF,FUNION_FEMPTY_1,heap_length_def,ADD_ASSOC]
  \\ full_simp_tac std_ss [FUNION_FUPDATE_1,el_length_def,ADD_ASSOC]);

val FDOM_heap_map = save_thm("FDOM_heap_map", Q.prove(
  `!xs n. ~(n + heap_length xs IN FDOM (heap_map n xs))`,
  Induct \\ TRY (Cases_on `h`)
  \\ full_simp_tac (srw_ss()) [heap_map_def,heap_length_def,ADD_ASSOC]
  \\ rpt strip_tac \\ full_simp_tac std_ss [el_length_def,ADD_ASSOC]
  \\ TRY decide_tac \\ metis_tac [])
  |> Q.SPECL [`xs`,`0`] |> SIMP_RULE std_ss []);

val heap_addresses_APPEND = Q.store_thm("heap_addresses_APPEND",
  `!xs ys n. heap_addresses n (xs ++ ys) =
              heap_addresses n xs UNION heap_addresses (n + heap_length xs) ys`,
  Induct \\ full_simp_tac (srw_ss()) [APPEND,heap_addresses_def,heap_length_def]
  \\ full_simp_tac (srw_ss()) [EXTENSION,DISJ_ASSOC,ADD_ASSOC]);

val LESS_IMP_heap_lookup = Q.store_thm("LESS_IMP_heap_lookup",
  `!xs j ys. j < heap_length xs ==> (heap_lookup j (xs ++ ys) = heap_lookup j xs)`,
  Induct \\ full_simp_tac (srw_ss()) [heap_length_def,heap_lookup_def]
  \\ SRW_TAC [] [] \\ `j - el_length h < SUM (MAP el_length xs)` by decide_tac
  \\ full_simp_tac std_ss []);

val NOT_LESS_IMP_heap_lookup = Q.store_thm("NOT_LESS_IMP_heap_lookup",
  `!xs j ys. ~(j < heap_length xs) ==>
              (heap_lookup j (xs ++ ys) = heap_lookup (j - heap_length xs) ys)`,
  Induct \\ full_simp_tac (srw_ss()) [heap_length_def,heap_lookup_def]
  \\ SRW_TAC [] [SUB_PLUS]
  THEN1 (Cases_on `h` \\ full_simp_tac std_ss [el_length_def] \\ `F` by decide_tac)
  THEN1 (Cases_on `h` \\ full_simp_tac std_ss [el_length_def] \\ `F` by decide_tac));

val heap_similar_Data_IMP_DataOrForward = Q.store_thm("heap_similar_Data_IMP_DataOrForward",
  `!heap0 heap1 ptr.
      heaps_similar heap0 heap1 /\ isSomeDataElement (heap_lookup ptr heap0) ==>
      isSomeDataOrForward (heap_lookup ptr heap1)`,
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

val FILTER_LEMMA = Q.store_thm("FILTER_LEMMA",
  `!heap. (FILTER isForwardPointer heap = []) ==>
           (FILTER (\h. ~isForwardPointer h) heap = heap)`,
  Induct \\ full_simp_tac (srw_ss()) [] \\ SRW_TAC [] []);

val heaps_similar_REFL = Q.store_thm("heaps_similar_REFL",
  `!xs. (FILTER isForwardPointer xs = []) ==> heaps_similar xs xs`,
  Induct \\ full_simp_tac (srw_ss()) [heaps_similar_def] \\ SRW_TAC [] []);

val heap_map_EMPTY = Q.store_thm("heap_map_EMPTY",
  `!xs n. (FILTER isForwardPointer xs = []) ==> (FDOM (heap_map n xs) = {})`,
  Induct \\ TRY (Cases_on `h`)
  \\ full_simp_tac (srw_ss()) [heap_map_def,isForwardPointer_def]);

val MEM_ADDR_MAP = Q.store_thm("MEM_ADDR_MAP",
  `!xs f ptr u. MEM (Pointer ptr u) (ADDR_MAP f xs) ==>
                 ?y. MEM (Pointer y u) xs /\ (f y = ptr)`,
  Induct \\ TRY (Cases_on `h`) \\ full_simp_tac (srw_ss()) [ADDR_MAP_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [] \\ res_tac \\ metis_tac []);

val heap_length_heap_expand = Q.store_thm("heap_length_heap_expand",
  `!n. heap_length (heap_expand n) = n`,
  Cases \\ EVAL_TAC \\ full_simp_tac (srw_ss()) [el_length_def,ADD1,SUM_ACC_DEF]);

val EVERY_isDataElement_IMP_LEMMA = Q.store_thm("EVERY_isDataElement_IMP_LEMMA",
  `!heap2. EVERY isDataElement heap2 ==> (FILTER isForwardPointer heap2 = [])`,
  Induct \\ full_simp_tac (srw_ss()) [isDataElement_def] \\ rpt strip_tac
  \\ full_simp_tac (srw_ss()) [isForwardPointer_def]);

val isSome_heap_looukp_IMP_APPEND = Q.store_thm("isSome_heap_looukp_IMP_APPEND",
  `!xs ptr. isSomeDataElement (heap_lookup ptr xs) ==>
             isSomeDataElement (heap_lookup ptr (xs ++ ys))`,
  full_simp_tac std_ss [isSomeDataElement_def] \\ rpt strip_tac
  \\ imp_res_tac heap_lookup_LESS \\ imp_res_tac LESS_IMP_heap_lookup
  \\ full_simp_tac (srw_ss()) []);

val heap_split_APPEND_if = Q.store_thm("heap_split_APPEND_if",
  `!h1 n h2. heap_split n (h1 ++ h2) =
  if n < heap_length h1 then
    case heap_split n h1 of
        NONE => NONE
      | SOME(h1',h2') => SOME(h1',h2'++h2)
  else
    case heap_split (n - heap_length h1) h2 of
        NONE => NONE
      | SOME(h1',h2') => SOME(h1++h1',h2')`,
  Induct >> fs[heap_split_def] >> rpt strip_tac
  >- (Cases_on `heap_split n h2` >> fs[] >> Cases_on `x` >> fs[])
  >> IF_CASES_TAC >- (fs[heap_length_def] >> Cases_on `h` >> fs[el_length_def])
  >> IF_CASES_TAC >- fs[heap_length_def]
  >> IF_CASES_TAC >- (fs[heap_length_def] >> every_case_tac >> fs[])
  >> fs[heap_length_def] >> every_case_tac >> fs[]);

val heap_split_0 = store_thm("heap_split_0[simp]",
  ``heap_split 0 h = SOME ([],h)``,
  Cases_on `h` \\ fs [heap_split_def]);

(* --- *)

val gc_related_def = Define `
  gc_related (f:num|->num) heap1 heap2 =
    INJ (FAPPLY f) (FDOM f) { a | isSomeDataElement (heap_lookup a heap2) } /\
    (!i. i IN FDOM f ==> isSomeDataElement (heap_lookup i heap1)) /\
    !i xs l d.
      i IN FDOM f /\ (heap_lookup i heap1 = SOME (DataElement xs l d)) ==>
      (heap_lookup (f ' i) heap2 = SOME (DataElement (ADDR_MAP (FAPPLY f) xs) l d)) /\
      !ptr u. MEM (Pointer ptr u) xs ==> ptr IN FDOM f`;

val _ = export_theory();
