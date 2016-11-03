open preamble wordsTheory wordsLib integer_wordTheory;

val _ = new_theory "gc_shared";

(* Types, functions and lemmas that are shared between GC definitions
*)

val _ = Datatype `
  heap_address = Pointer num 'a | Data 'a`;

val _ = Datatype `
  heap_element = Unused num
               | ForwardPointer num 'a num
               | DataElement (('a heap_address) list) num 'b`;


val _ = Datatype `
  gc_state =
    <| h1 : ('a, 'b) heap_element list (* final left heap *)
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
    <| h1 := []
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

val heap_lookup_def = Define `
  (heap_lookup a [] = NONE) /\
  (heap_lookup a (x::xs) =
     if a = 0 then SOME x else
     if a < el_length x then NONE else heap_lookup (a - el_length x) xs)`;

val heap_take_def = Define `
  (heap_take a [] = NONE) /\
  (heap_take a (el::heap) =
    if a = 0 then SOME [] else
    if a < el_length el then NONE else
    case heap_take (a - el_length el) heap of
    | NONE => NONE
    | SOME h => SOME (el::h))`;

val heap_drop_def = Define `
  (heap_drop 0 heap = heap) /\
  (heap_drop a (el::heap) =
    if a < el_length el then ARB else
    heap_drop (a - el_length el) heap)`;

val heap_split_def = Define `
  (heap_split a [] = NONE) /\
  (heap_split a (el::heap) =
    if a = 0 then SOME ([],el::heap) else
    if a < el_length el then NONE else
    case heap_split (a - el_length el) heap of
    | NONE => NONE
    | SOME (h1,h2) =>
      SOME (el::h1,h2))`;

val heap_segment_def = Define `
  heap_segment (a, b) heap =
    case heap_split a heap of
    | NONE => NONE
    | SOME (h1,heap') =>
      case heap_split (b - heap_length h1) heap' of
      | NONE => NONE
      | SOME (h2,h3) => SOME (h1,h2,h3)`;

val isDataElement_def = Define `
  isDataElement x = ?ys l d. x = DataElement ys l d`;

val isSomeDataElement_def = Define `
  isSomeDataElement x = ?ys l d. x = SOME (DataElement ys l d)`;

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
    (!ptr xs l d u. MEM (DataElement xs l d) heap /\ MEM (Pointer ptr u) xs ==>
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

val ADDR_APPLY_def = Define `
  (ADDR_APPLY f (Pointer x d) = Pointer (f x) d) /\
  (ADDR_APPLY f (Data y) = Data y)`;

val isSomeForwardPointer_def = Define `
  isSomeForwardPointer x = ?ptr d l. x = SOME (ForwardPointer ptr d l)`;

val isSomeDataOrForward_def = Define `
  isSomeDataOrForward x = isSomeForwardPointer x \/ isSomeDataElement x`;

val _ = augment_srw_ss [rewrites [LIST_REL_def]];

val heaps_similar_def = Define `
  heaps_similar heap0 heap =
    EVERY2 (\h0 h. if isForwardPointer h then
                     (el_length h = el_length h0) /\ isDataElement h0
                   else (h = h0)) heap0 heap`
(*  *)


val gc_related_def = Define `
  gc_related (f:num|->num) heap1 heap2 =
    INJ (FAPPLY f) (FDOM f) { a | isSomeDataElement (heap_lookup a heap2) } /\
    !i xs l d.
      i IN FDOM f /\ (heap_lookup i heap1 = SOME (DataElement xs l d)) ==>
      (heap_lookup (f ' i) heap2 = SOME (DataElement (ADDR_MAP (FAPPLY f) xs) l d)) /\
      !ptr u. MEM (Pointer ptr u) xs ==> ptr IN FDOM f`;


(* Lemmas, TODO: placed somewhere else? *)

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

val _ = export_theory();
