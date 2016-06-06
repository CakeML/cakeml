open preamble wordsTheory wordsLib integer_wordTheory;

val _ = new_theory "gc_copying_record";

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

val BIJ_UPDATE = prove(
  ``!f s t x y. BIJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
    BIJ ((x =+ y) f) (x INSERT s) (y INSERT t)``,
  simp_tac std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_INSERT,APPLY_UPDATE_THM]
  \\ metis_tac []);

val INJ_UPDATE = store_thm("INJ_UPDATE",
  ``INJ f s t /\ ~(x IN s) /\ ~(y IN t) ==>
    INJ ((x =+ y) f) (x INSERT s) (y INSERT t)``,
  simp_tac std_ss [BIJ_DEF,SURJ_DEF,INJ_DEF,IN_INSERT,APPLY_UPDATE_THM]
  \\ metis_tac []);

(* The ML heap is represented as a list of heap_elements. *)

val _ = Datatype `
  heap_address = Pointer num 'a | Data 'a`;

val _ = Datatype `
  heap_element = Unused num
               | ForwardPointer num 'a num
               | DataElement (('a heap_address) list) num 'b`;

(* references in DataElement *)


val _ = Datatype `
  gc_state =
    <| h1 : ('a, 'b) heap_element list (* final left heap *)
     ; h2 : ('a, 'b) heap_element list (* not updated left heap *)

     ; r4 : ('a, 'b) heap_element list (* not updated right heap *)
     ; r3 : ('a, 'b) heap_element list (* temp. final right heap *)
     ; r2 : ('a, 'b) heap_element list (* temp. not updated right heap *)
     ; r1 : ('a, 'b) heap_element list (* final right heap *)

     ; a : num                         (* heap_length (og ++ h1 ++ h2) *)
     ; n : num                         (* unused heap space *)
     ; r : num                         (* heap_length (r4 ++ r3 ++ r2 ++ r1) *)

     ; ok : bool                       (* OK *)
     ; heap : ('a, 'b) heap_element list (* old heap (w/ fwd pointers) *)
     |>`;

val empty_state_def = Define `
  empty_state =
    <| (* old := [] *)
     (* ;  *)h1 := []
     ; h2 := []
     ; r4 := []
     ; r3 := []
     ; r2 := []
     ; r1 := []
     ; a := 0
     ; n := 0
     ; r := 0
     ; ok := T
     ; heap := []
     |>`;

val _ = Datatype `
  gc_conf =
    <| limit : num              (* size of heap *)
     ; isRef : ('a, 'b) heap_element -> bool
     ; gen_start : num          (* start of generation *)
     ; gen_end : num            (* end of generation *)
     ; refs_start : num         (* start of references, gen_end < refs_start *)
     |>`;


(* The heap is accessed using the following lookup function. *)
val el_length_def = Define `
  (el_length (Unused l) = l+1) /\
  (el_length (ForwardPointer n d l) = l+1) /\
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

(* roots are ok if they are a pointer they point to some DataElement *)
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

(* The GC is a copying collector which moves elements *)

val gc_forward_ptr_def = Define `
  (* replace cell at a with a forwardpointer to ptr *)
  (gc_forward_ptr a [] ptr d ok = ([],F)) /\
  (gc_forward_ptr a (x::xs) ptr d ok =
     if a = 0 then
       (ForwardPointer ptr d ((el_length x)-1) :: xs, isDataElement x /\ ok) else
     if a < el_length x then (x::xs,F) else
       let (xs,ok) = gc_forward_ptr (a - el_length x) xs ptr d ok in
         (x::xs,ok))`;

val gc_move_def = Define `
  (gc_move conf state (Data d) = (Data d, state)) /\
  (gc_move conf state (Pointer ptr d) =
     if ptr < conf.gen_start \/ conf.gen_end <= ptr then
       (Pointer ptr d, state) else
     case heap_lookup ptr state.heap of
     | SOME (DataElement xs l dd) =>
       let ok = state.ok /\ l+1 <= state.n /\ (state.a + state.n + state.r = conf.limit) in
       let n = state.n - (l + 1) in
        if conf.isRef (DataElement xs l dd) then
          (* put refs in r4 *)
          let r4 = (DataElement xs l dd) :: state.r4 in
          let r = state.r + (l + 1) in
          let (heap, c) = gc_forward_ptr ptr state.heap (state.a + n) d ok in
            (Pointer (state.a + n) d
            ,state with <| r4 := r4; n := n; r := r; heap := heap; ok := ok |>)
        else
          (* put data in h2 *)
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
  \\ ntac 4 strip_tac
  \\ Cases_on `n < conf.gen_start ∨ conf.gen_end ≤ n` \\ fs []
  \\ Cases_on `heap_lookup n state.heap`
  \\ fs [theorem "gc_state_component_equality"]
  \\ Cases_on `x`
  \\ fs [LET_THM,theorem "gc_state_component_equality"]
  \\ pairarg_tac
  \\ fs []
  \\ Cases_on `conf.isRef (DataElement l n' b)`
  \\ pairarg_tac
  \\ fs [theorem "gc_state_component_equality"]);

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

(* The main gc loop, calls gc_move_data and gc_move_ref *)
val gc_move_loop_def = Define `
  gc_move_loop conf state (clock : num) =
      case (state.h2,state.r4) of
      | ([],[]) => state
      | (h2,[]) =>
        let state = gc_move_data conf state in
          if clock = 0 then state with <| ok := F |> else
          gc_move_loop conf state (clock-1)
      | (h2,r4) =>
        let state = gc_move_refs conf (state with <| r2 := r4; r4 := [] |>) in
          if clock = 0 then state with <| ok := F |> else
          gc_move_loop conf state (clock-1)`

val partial_gc_def = Define `
  partial_gc conf (roots,heap) =
    let ok0 = (heap_length heap = conf.limit) in
    case heap_segment (conf.gen_start,conf.refs_start) heap of
    | NONE => (roots,ARB,ARB,ARB,ARB,F)
    | SOME (old,current,refs) =>
      let r = heap_length refs in
      let n = heap_length current in
      let state = empty_state
          with <| heap := heap
                ; r2 := refs
                ; a := conf.gen_start; n := n; r := r |> in
        (* process roots: *)
      let (roots,state) = gc_move_list conf state roots in
        (* process references: *)
      let state = gc_move_refs conf state in
        (* process rest: *)
      let state = gc_move_loop conf state conf.limit in
      let ok = ok0 /\ state.ok /\
               (state.a = conf.gen_start + heap_length state.h1) /\
               (state.r = heap_length state.r1) /\
               (heap_length state.heap = conf.limit) /\
               (state.a + state.n + state.r = conf.limit) /\
               state.a + state.r <= conf.limit in
          (roots,state.h1,state.r1,state.a,state.r,ok)`;

val full_gc_def = Define `
  full_gc conf (roots,heap) =
    partial_gc
      (conf with <| gen_start := 0; gen_end := conf.limit; refs_start := conf.limit |>)
      (roots,heap)`;

(* Invariant *)

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

(* Do we point to something that is fully processed? I.e. all children
are also copied. *)
val is_final_def = Define `
  is_final conf state ptr =
    let h1end = conf.gen_start + heap_length (state.h1) in
    let r3start = state.a + state.n + heap_length state.r4 in
    let r3end = r3start + heap_length state.r3 in
    let r1start = r3end + heap_length state.r2 in
    ptr < h1end \/
    r1start <= ptr \/
    (r3start <= ptr /\ ptr < r3end)`;

val heap_split_fst_def = Define `
  heap_split_fst split heap =
    OPTION_MAP FST (heap_split split heap)`;

val gc_inv_def = Define `
  gc_inv conf state heap0 =
    ?old old0.
    let heap' = old ++ state.h1 ++ state.h2 ++
                heap_expand state.n ++
                state.r4 ++ state.r3 ++ state.r2 ++ state.r1 in
    (SOME old = heap_split_fst conf.gen_start state.heap) /\
    (SOME old0 = heap_split_fst conf.gen_start heap0) /\
      (* lengths *)
    (heap_length old = conf.gen_start) /\
    (heap_length (old ++ state.h1 ++ state.h2) = state.a) /\
    (* (conf.gen_start + heap_length (state.h1 ++ state.h2) = state.a) /\ *)
    (heap_length (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) = state.r) /\
    (heap_length (FILTER (\h. ~(isForwardPointer h)) state.heap)
      = state.n + conf.gen_start + conf.refs_start) /\
    (state.r + state.a + state.n = conf.limit) /\
    ((heap_length state.heap) = conf.limit) /\
      (* ---- *)
    state.ok /\
    heap_ok heap0 conf.limit /\
    heaps_similar heap0 state.heap /\
      (* ---- *)
    EVERY isDataElement old /\
    EVERY isDataElement state.h1 /\ EVERY isDataElement state.h2 /\
    EVERY isDataElement state.r1 /\ EVERY isDataElement state.r2 /\
    EVERY isDataElement state.r3 /\ EVERY isDataElement state.r4 /\
      (* ---- *)
    (old0 = old) /\
    (!el. MEM el (state.r4 ++ state.r3 ++ state.r2 ++ state.r1) ==>
          conf.isRef el) /\
      (* ---- *)
    BIJ (heap_map1 state.heap) (FDOM (heap_map 0 state.heap))
        (heap_addresses conf.gen_start (state.h1 ++ state.h2) UNION
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

(* Invariant maintained *)

val heap_lookup_MEM = store_thm("heap_lookup_MEM",
  ``!heap n x. (heap_lookup n heap = SOME x) ==> MEM x heap``,
  Induct \\ full_simp_tac std_ss [heap_lookup_def] \\ SRW_TAC [] []
  \\ res_tac \\ fs []);

val DRESTRICT_heap_map = prove(
  ``!heap k. n < k ==> (DRESTRICT (heap_map k heap) (COMPL {n}) = heap_map k heap)``,
  simp_tac (srw_ss()) [GSYM fmap_EQ_THM,DRESTRICT_DEF,EXTENSION] \\ rpt strip_tac
  \\ Cases_on `x IN FDOM (heap_map k heap)` \\ full_simp_tac std_ss []
  \\ rpt (pop_assum mp_tac)  \\ Q.SPEC_TAC (`k`,`k`) \\ Q.SPEC_TAC (`heap`,`heap`)
  \\ Induct \\ full_simp_tac (srw_ss()) [heap_map_def]
  \\ Cases \\ full_simp_tac (srw_ss()) [heap_map_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss []
  \\ metis_tac [DECIDE ``n<k ==> n < k + m:num``,DECIDE ``n<k ==> n < k + m+1:num``]);

val IN_FRANGE = prove(
  ``!heap n. MEM (ForwardPointer ptr d l) heap ==> ptr IN FRANGE (heap_map n heap)``,
  Induct \\ full_simp_tac std_ss [MEM] \\ rpt strip_tac
  \\ Cases_on `h` \\ full_simp_tac (srw_ss()) [heap_map_def,FRANGE_FUPDATE]
  \\ `n < n + n0 + 1` by decide_tac \\ full_simp_tac std_ss [DRESTRICT_heap_map]);

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

val gc_forward_ptr_thm2 = prove(
  ``!ha hb ys l d a u c .
    gc_forward_ptr (heap_length ha) (ha ++ [DataElement ys l d] ++ hb) a u c =
      (ha ++ [ForwardPointer a u l] ++ hb,c)``,
  Induct
  \\ fs [heap_length_def,gc_forward_ptr_def,el_length_def,isDataElement_def]
  \\ rw []
  \\ Cases_on `h`
  \\ fs [heap_length_def,el_length_def]);


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

val heap_addresses_SNOC = prove(
  ``!xs n x.
      heap_addresses n (xs ++ [x]) =
      heap_addresses n xs UNION {heap_length xs + n}``,
  Induct \\ full_simp_tac (srw_ss()) [heap_addresses_def,APPEND,heap_length_def]
  \\ full_simp_tac (srw_ss()) [EXTENSION] \\ rpt strip_tac
  \\ full_simp_tac std_ss [AC ADD_COMM ADD_ASSOC,DISJ_ASSOC]);

val NOT_IN_heap_addresses_general = prove(
  ``!xs n. ~(n + heap_length xs IN heap_addresses n xs)``,
  Induct \\ full_simp_tac (srw_ss()) [heap_addresses_def,APPEND,heap_length_def]
  \\ full_simp_tac (srw_ss()) [EXTENSION] \\ rpt strip_tac
  \\ full_simp_tac std_ss [ADD_ASSOC]
  THEN1 (Cases_on `h` \\ EVAL_TAC \\ decide_tac) \\ metis_tac []);

val NOT_IN_heap_addresses =
  NOT_IN_heap_addresses_general |> Q.SPECL [`xs`,`0`] |> SIMP_RULE std_ss [];

val NOT_IN_heap_addresses_less = prove(
  ``!xs m n. (m < n) ==> ~(m IN heap_addresses n xs)``,
  Induct \\ rw [] \\ fs [heap_addresses_def]);

val heap_lookup_PREFIX = store_thm("heap_lookup_PREFIX",
  ``!xs. (heap_lookup (heap_length xs) (xs ++ x::ys) = SOME x)``,
  Induct \\ full_simp_tac (srw_ss()) [heap_lookup_def,APPEND,heap_length_def]
  \\ SRW_TAC [] [] \\ Cases_on `h`
  \\ full_simp_tac std_ss [el_length_def] \\ decide_tac);

val heap_lookup_PREFIX_ALT = prove(
  ``!xs x ys. (heap_lookup (heap_length xs) (xs ++ [x] ++ ys) = SOME x)``,
  Induct \\ fs [heap_lookup_def,APPEND,heap_length_def]
  \\ rw [] \\ Cases_on `h` \\ fs [el_length_def]);

val heap_lookup_EXTEND = store_thm("heap_lookup_EXTEND",
  ``!xs n ys x. (heap_lookup n xs = SOME x) ==>
                (heap_lookup n (xs ++ ys) = SOME x)``,
  Induct \\ full_simp_tac (srw_ss()) [heap_lookup_def] \\ SRW_TAC [] []);

(* val heap_lookup_MODIFY = prove( *)
(*   ``!xs n m el ys x l d. *)
(*     (el <> DataElement x l d) /\ *)
(*     (heap_lookup n (xs ++ heap_expand m ++ ys) = SOME (DataElement x l d)) ==> *)
(*     (heap_lookup n (xs ++ [el] ++ heap_expand (m - el_length el) ++ ys) = *)
(*       SOME (DataElement x l d))`` *)
(* Induct \\ fs [heap_lookup_def,heap_expand_def] *)
(* rpt strip_tac *)


(* Cases_on `n < m` *)
(* fs [] *)
(* THEN1 *)


val ADDR_MAP_EQ = prove(
  ``!xs. (!p d. MEM (Pointer p d) xs ==> (f p = g p)) ==>
         (ADDR_MAP f xs = ADDR_MAP g xs)``,
  Induct \\ TRY (Cases_on `h`) \\ full_simp_tac (srw_ss()) [ADDR_MAP_def]
  \\ metis_tac []);

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

val el_length_GT_0 = prove(
  ``!e. el_length e > 0``,
  Cases \\ fs [el_length_def]);

val APPEND_CONS_LEMMA = prove(
  ``!xs y ys. xs ++ [y] ++ ys = xs ++ y::ys``,
  fs [EVAL ``[y] ++ ys``]);

val heap_length_APPEND = store_thm("heap_length_APPEND",
  ``heap_length (xs ++ ys) = heap_length xs + heap_length ys``,
  SRW_TAC [] [heap_length_def,SUM_APPEND]);

val heap_split_less_FST = prove(
  ``!ha el hb n left.
    (n < heap_length ha) /\
    (* ~(heap_length ha < n) /\ *)
    (heap_split_fst n (ha ++ el::hb) = SOME left) ==>
    (heap_split_fst n ha = SOME left)``,
  Induct
  \\ fs [heap_length_def]
  \\ fs [heap_split_fst_def,heap_split_def]
  \\ rpt strip_tac
  \\ Cases_on `n = 0`
  \\ fs []
  THEN1
    (qpat_assum `_ = z` (assume_tac o GSYM)
    \\ fs [])
  fs []

    rpt strip_tac
    fs [heap_split_fst_def]


  \\ fs [heap_split_fst_def,heap_split_def]
  THEN1
    Induct
    \\ fs [heap_split_def]
  \\ rw []
  \\ fs [heap_split_def]

  \\ rw [heap_length_def]
  rw []
    );


  \\ `n <= heap_length ha` by decide_tac

  Induct
  \\ fs [heap_split_def,heap_length_def]
  \\ Induct_on `n`
  \\ fs [heap_split_def]
  \\ rw []
  \\ cheat);

val EVERY_isDataElement_heap_lookup = prove(
  ``!heap n d.
      EVERY isDataElement heap /\
      (heap_lookup n heap = SOME d) ==>
      isSomeDataElement (SOME d)``,
  Induct
  \\ simp [heap_lookup_def]
  \\ Cases_on `n`
  \\ fs [isSomeDataElement_def,isDataElement_def]
  \\ rw []
  \\ metis_tac []);

val isSomeDataOrForward_lemma_expanded =
  isSomeDataOrForward_lemma
  |> SIMP_RULE std_ss [isSomeDataOrForward_def,isSomeDataElement_def,isSomeForwardPointer_def];

val heap_split_length_lemma = prove(
  ``!heap split h1.
    (heap_split_fst split heap = SOME h1) ==>
    (heap_length h1 = split)``,
  Induct
  THEN1 fs [heap_split_fst_def,heap_split_def,heap_length_def]
  \\ fs [heap_split_fst_def,heap_split_def]
  \\ rw []
  THEN1 fs [heap_length_def]
  \\ Cases_on `heap_split (split − el_length h) heap`
  \\ fs []
  \\ `x = (h1,h2)` by cheat     (* split_pair_case_tac *)
  \\ fs []
  \\ qpat_assum `_ = z` (assume_tac o GSYM)
  \\ fs []
  \\ qpat_assum `!split h1. _` (qspecl_then [`split - el_length h`,`h1`] mp_tac)
  \\ simp [heap_length_def]);

val heap_length_heap_split_same_lemma = prove(
  ``!heap1 heap2 split.
    heap_length heap1 <= split /\
    (heap_length heap1 = heap_length heap2) ==>
    (heap_length (FST (heap_split split heap1)) = heap_length (FST (heap_split split heap2)))``,
  cheat);

val heap_addresses_APPEND = prove(
  ``!a h1 h2.
    heap_addresses a (h1 ++ h2) =
    heap_addresses a h1 UNION heap_addresses (a + heap_length h1) h2``,
  Induct_on `h1`
  THEN1 fs [heap_addresses_def,heap_length_def]
  \\ fs [heap_addresses_def]
  \\ rpt strip_tac
  \\ fs [INSERT_UNION_EQ,heap_length_def]);

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
\\ Cases_on `n < conf.gen_start \/ conf.gen_end <= n`
(* outside generation, no changes *)
(* two cases: we find a forwardpointer, but that is impossible; we
find a dataelement-->simple *)
THEN1
  cheat
\\ rpt strip_tac
\\ fs [isSomeDataOrForward_def,isSomeForwardPointer_def,isSomeDataElement_def]
(* ForwardPointer *)
THEN1
  (imp_res_tac heap_lookup_FLOOKUP
  \\ fs [heap_map1_def,FLOOKUP_DEF])
(* DataElement *)
\\ fs [isSomeDataElement_def,LET_THM]
\\ imp_res_tac heap_lookup_SPLIT
\\ rw []
(* \\ qpat_assum `_ = heap` (fn th => assume_tac (GSYM th)) *)
THEN1                           (* isRef *)
  cheat

THEN1                           (* ~isRef *)
  (pairarg_tac
  \\ simp []
  \\ `heap_length (heap_split_fst conf.gen_start (ha ++ DataElement ys l d::hb)) =
        conf.gen_start` by all_tac
  THEN1
    (`conf.gen_start <= heap_length (ha ++ DataElement ys l d::hb)` by simp [heap_length_APPEND]
    \\ drule heap_split_length_lemma
    \\ simp [])
  \\ full_simp_tac std_ss [gc_forward_ptr_thm]
  \\ `heap_map 0 (ha ++ ForwardPointer state.a a l::hb) =
     heap_map 0 (ha ++ DataElement ys l d::hb) |+ (heap_length ha,state.a)` by all_tac
  THEN1
    (fs [heap_map_APPEND,heap_map_def]
    \\ fs [heap_length_def,el_length_def]
    \\ fs [heap_map_def,SUM_APPEND]
    \\ fs [GSYM fmap_EQ_THM,heap_map_APPEND]
    \\ fs [EXTENSION] \\ strip_tac THEN1 metis_tac []
    \\ fs [FUNION_DEF,FAPPLY_FUPDATE_THM] \\ strip_tac
    \\ Cases_on `x = SUM (MAP el_length ha)` \\ full_simp_tac std_ss []
    \\ fs [GSYM heap_length_def]
    \\ fs [FDOM_heap_map])
  \\ `~(heap_length ha IN FDOM (heap_map 0 (ha ++ DataElement ys l d::hb)))` by all_tac
  THEN1 full_simp_tac std_ss [NOT_IN_heap_map]
  \\ qpat_assum `_ = heap` (assume_tac o GSYM)
  \\ simp []
  \\ rpt strip_tac
  \\ TRY (fs [heap_map1_def] \\ NO_TAC)
  THEN1
    metis_tac [isSomeDataOrForward_lemma_expanded]
  \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [gc_inv_def,LET_THM]
  \\ fs [theorem "gc_state_component_equality"]
  \\ Q.ABBREV_TAC `ff = heap_map 0 (ha ++ DataElement ys l d::hb)`
  \\ `heap_length (ha ++ DataElement ys l d::hb) =
       heap_length (ha ++ ForwardPointer state.a a l::hb)` by all_tac
  THEN1
    (fs [heap_length_APPEND]
    \\ fs [heap_length_def,el_length_def])
  \\ drule heap_length_heap_split_same_lemma
  \\ disch_then (qspec_then `conf.gen_start` (assume_tac o GSYM))
  \\ `l + 1 <= state.n` by all_tac
  THEN1
    (fs [heap_length_def,FILTER_APPEND,isForwardPointer_def,SUM_APPEND,el_length_def]
    \\ cheat)                   (* easy *)
  \\ qpat_assum `_ <=> ok` (assume_tac o GSYM)
  \\ rpt strip_tac
  \\ TRY (fs [] \\ NO_TAC)
  THEN1
    (qpat_assum `_ = state.a` (assume_tac o GSYM)
    \\ simp [heap_length_APPEND]
    \\ simp [heap_length_def,el_length_def])
  THEN1
    (qpat_assum `_ = conf.gen_start + (conf.refs_start + state.n)` mp_tac
    \\ simp [FILTER_APPEND,heap_length_APPEND,isForwardPointer_def,heap_length_def,el_length_def,SUM_APPEND])
  THEN1
    (qpat_assum `heaps_similar _ _` mp_tac
    \\ once_rewrite_tac [GSYM APPEND_CONS_LEMMA]
    \\ strip_tac
    \\ drule heaps_similar_lemma
    \\ fs [])
  THEN1
    (simp []
    \\ drule heap_split_less_FST
    \\ disch_then (qspec_then `ForwardPointer state.a a l::hb` assume_tac)
    \\ simp []
    \\ qpat_assum `EVERY isDataElement (FST _)` assume_tac
    \\ drule heap_split_less_FST
    \\ disch_then (qspec_then `DataElement ys l d::hb` (assume_tac o GSYM))
    \\ simp [])
  THEN1
    fs [isDataElement_def]
  THEN1
    (once_rewrite_tac [GSYM APPEND_ASSOC]
    \\ drule heap_split_less_FST
    \\ disch_then (fn th =>
      qspec_then `[DataElement ys l d] ++ hb` assume_tac th
      \\ qspec_then `[ForwardPointer state.a a l] ++ hb` assume_tac th)
    \\ fs [])
  THEN1
    (simp [heap_map1_def]
    \\ simp [heap_map_APPEND]
    \\ `(λa'. (ff |+ (heap_length ha,state.a)) ' a') =
       ((heap_length ha =+ state.a) (\a. ff ' a))` by all_tac
    THEN1
      fs [FUN_EQ_THM,APPLY_UPDATE_THM,FAPPLY_FUPDATE_THM]
    \\ simp []
    \\ `~(state.a IN
          (heap_addresses conf.gen_start (state.h1 ++ state.h2)))` by all_tac
    THEN1
      (qpat_assum `_ = state.a` (mp_tac o GSYM)
      \\ simp [heap_length_APPEND]
      \\ DISCH_TAC
      \\ simp [GSYM heap_length_APPEND]
      \\ simp [NOT_IN_heap_addresses_general])
    \\ `~(state.a IN
          heap_addresses (state.a + state.n)
            (state.r4 ++ state.r3 ++ state.r2 ++ state.r1))` by all_tac
    THEN1
      (`state.a < state.a + state.n` by decide_tac
      \\ drule NOT_IN_heap_addresses_less
      \\ disch_then (qspec_then `state.r4 ++ state.r3 ++ state.r2 ++ state.r1` assume_tac)
      \\ simp [])
    \\ `heap_addresses conf.gen_start (state.h1 ++ state.h2 ++ [DataElement ys l d]) =
        (conf.gen_start + heap_length (state.h1 ++ state.h2)) INSERT
        (heap_addresses conf.gen_start (state.h1 ++ state.h2))` by all_tac
    THEN1
      (simp [heap_addresses_APPEND]
      \\ simp [heap_addresses_def]
      \\ simp [UNION_COMM]
      \\ simp [GSYM INSERT_SING_UNION])
    \\ simp []
    \\ drule BIJ_UPDATE
    \\ simp []
    \\ ntac 2 (disch_then drule)
    \\ simp []
    \\ qpat_assum `_ = state.a` (assume_tac o SIMP_RULE std_ss [heap_length_APPEND] o GSYM)
    \\ simp [heap_map1_def]
    \\ simp [INSERT_UNION_EQ,heap_length_APPEND])

  THEN1
    cheat

  \\ cheat)
    );

  (* Cases_on `x` *)
  (* \\ simp_tac (srw_ss()) [gc_move_def,ADDR_APPLY_def] *)
  (* \\ simp_tac std_ss [Once isSomeDataOrForward_def] *)
  (* \\ rpt strip_tac *)
  (* \\ full_simp_tac (srw_ss()) [isSomeForwardPointer_def] *)
  (*   THEN1 (full_simp_tac (srw_ss()) [ADDR_APPLY_def] *)
  (*         \\ imp_res_tac heap_lookup_FLOOKUP *)
  (*         \\ full_simp_tac std_ss [FLOOKUP_DEF,heap_map1_def]) *)
  (* \\ full_simp_tac (srw_ss()) [isSomeDataElement_def,LET_DEF] *)
  (* \\ imp_res_tac heap_lookup_SPLIT *)
  (* \\ full_simp_tac std_ss [] *)
  (* \\ full_simp_tac (srw_ss()) [gc_forward_ptr_thm] *)
  (* \\ `heap_map 0 (ha ++ [ForwardPointer a a' l] ++ hb) = *)
  (*     heap_map 0 (ha ++ DataElement ys l d::hb) |+ (heap_length ha,a)` by *)
  (*  (once_rewrite_tac [GSYM (EVAL ``[x] ++ xs``)] *)
  (*   \\ simp_tac std_ss [APPEND_NIL,APPEND_ASSOC] *)
  (*   \\ full_simp_tac std_ss [heap_map_APPEND] *)
  (*   \\ full_simp_tac (srw_ss()) [heap_length_def,el_length_def] *)
  (*   \\ full_simp_tac (srw_ss()) [heap_map_def,SUM_APPEND] *)
  (*   \\ full_simp_tac (srw_ss()) [GSYM fmap_EQ_THM,heap_map_APPEND] *)
  (*   \\ full_simp_tac (srw_ss()) [EXTENSION] \\ strip_tac THEN1 metis_tac [] *)
  (*   \\ full_simp_tac (srw_ss()) [FUNION_DEF,FAPPLY_FUPDATE_THM] \\ strip_tac *)
  (*   \\ Cases_on `x = SUM (MAP el_length ha)` \\ full_simp_tac std_ss [] *)
  (*   \\ full_simp_tac std_ss [GSYM heap_length_def] *)
  (*   \\ full_simp_tac std_ss [FDOM_heap_map]) *)
  (* \\ `~(heap_length ha IN FDOM (heap_map 0 (ha ++ DataElement ys l d::hb)))` *)
  (*      by full_simp_tac std_ss [NOT_IN_heap_map] *)
  (* \\ strip_tac THEN1 (full_simp_tac (srw_ss()) [heap_map1_def]) *)
  (* \\ strip_tac THEN1 (full_simp_tac (srw_ss()) []) *)
  (* \\ strip_tac THEN1 metis_tac [isSomeDataOrForward_lemma] *)
  (* \\ strip_tac THEN1 *)
  (*  (full_simp_tac (srw_ss()) [SUBMAP_DEF,FAPPLY_FUPDATE_THM] *)
  (*   \\ SRW_TAC [] [] \\ full_simp_tac std_ss []) *)
  (* \\ full_simp_tac std_ss [gc_inv_def,heap_map1_def] *)
  (* \\ Q.ABBREV_TAC `ff = heap_map 0 (ha ++ DataElement ys l d::hb)` *)
  (* \\ rpt (strip_tac THEN1 *)
  (*  (full_simp_tac (srw_ss()) [heap_length_def,FILTER_APPEND,FILTER_APPEND, *)
  (*     isForwardPointer_def,SUM_APPEND,el_length_def] \\ decide_tac)) *)
  (* \\ strip_tac THEN1 (metis_tac [heaps_similar_lemma]) *)
  (* \\ strip_tac *)
  (* THEN1 (full_simp_tac std_ss [EVERY_APPEND] \\ EVAL_TAC \\ full_simp_tac std_ss []) *)
  (* \\ full_simp_tac std_ss [APPEND_ASSOC,heap_addresses_SNOC] *)
  (* \\ full_simp_tac std_ss [FDOM_FUPDATE] *)
  (* \\ strip_tac THEN1 *)
  (*  (`(heap_addresses 0 (h1 ++ h2) UNION {heap_length (h1 ++ h2)}) = *)
  (*    (heap_length (h1 ++ h2) INSERT heap_addresses 0 (h1 ++ h2))` by all_tac *)
  (*   THEN1 (full_simp_tac (srw_ss()) [EXTENSION] \\ metis_tac []) *)
  (*   \\ `~(heap_length (h1 ++ h2) IN heap_addresses 0 (h1 ++ h2))` by *)
  (*         full_simp_tac std_ss [NOT_IN_heap_addresses] *)
  (*   \\ imp_res_tac BIJ_UPDATE *)
  (*   \\ `(\a'. (ff |+ (heap_length ha,heap_length (h1 ++ h2))) ' a') = *)
  (*       ((heap_length ha =+ heap_length (h1 ++ h2)) (\a. ff ' a))` by all_tac THEN1 *)
  (*    (full_simp_tac std_ss [FUN_EQ_THM,APPLY_UPDATE_THM,FAPPLY_FUPDATE_THM] *)
  (*     \\ SRW_TAC [] []) \\ full_simp_tac std_ss []) *)
  (* \\ ntac 3 strip_tac *)
  (* \\ Cases_on `i = heap_length ha` THEN1 *)
  (*  (`j = heap_length (h1 ++ h2)` by all_tac *)
  (*   THEN1 full_simp_tac std_ss [FLOOKUP_DEF,FAPPLY_FUPDATE_THM] *)
  (*   \\ full_simp_tac std_ss [] *)
  (*   \\ `heap_lookup (heap_length ha) heap0 = SOME (DataElement ys l d)` by *)
  (*    (imp_res_tac heap_similar_Data_IMP *)
  (*     \\ full_simp_tac std_ss [heap_lookup_PREFIX]) *)
  (*   \\ full_simp_tac (srw_ss()) [heap_lookup_PREFIX] *)
  (*   \\ `~(heap_length (h1 ++ h2) < heap_length h1)` by all_tac *)
  (*   THEN1 (full_simp_tac (srw_ss()) [heap_length_def,SUM_APPEND] \\ decide_tac) *)
  (*   \\ full_simp_tac std_ss []) *)
  (* \\ `FLOOKUP ff i = SOME j` by all_tac *)
  (* THEN1 full_simp_tac (srw_ss()) [FLOOKUP_DEF,FAPPLY_FUPDATE_THM] *)
  (* \\ qpat_assum `!i j:num. bbb` (mp_tac o Q.SPECL [`i`,`j`]) *)
  (* \\ full_simp_tac std_ss [] \\ strip_tac *)
  (* \\ full_simp_tac (srw_ss()) [] *)
  (* \\ imp_res_tac heap_lookup_EXTEND *)
  (* \\ full_simp_tac (srw_ss()) [] *)
  (* \\ SRW_TAC [] [] \\ full_simp_tac std_ss [] *)
  (* \\ res_tac \\ fs [] *)
  (* \\ match_mp_tac ADDR_MAP_EQ *)
  (* \\ full_simp_tac std_ss [FAPPLY_FUPDATE_THM] \\ metis_tac []); *)

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
  \\ `∀ptr u. MEM (Pointer ptr u) xs ==> isSomeDataOrForward (heap_lookup ptr state'.heap)` by all_tac
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

val APPEND_NIL_LEMMA = METIS_PROVE [APPEND_NIL] ``?xs1. xs = xs ++ xs1:'a list``

val gc_state_component_equality = fetch "-" "gc_state_component_equality";

val gc_move_ALT = store_thm("gc_move_ALT",
  ``gc_move conf state y =
     let (y', state') = gc_move conf (state with <| h2 := []; r4 := [] |>) y in
       (y', state' with <| h2 := state.h2 ++ state'.h2; r4 := state'.r4 ++ state.r4 |>)``,
  reverse (Cases_on `y`) \\ fs [gc_move_def]
  THEN1 fs [LET_THM,gc_state_component_equality]
  \\ IF_CASES_TAC
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

val gc_move_refs_thm = prove(
  ``!state.
      gc_inv conf state heap0 ==>
      ?state'.
        (gc_move_refs conf state = state') /\
        ((heap_map 0 state.heap) SUBMAP (heap_map 0 state'.heap)) /\
        gc_inv conf state' heap0``,
  cheat);

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
\\ Cases_on `state.h2`
THEN1 fs []
\\ `isDataElement h` by all_tac
THEN1
  (qpat_assum `gc_inv _ _ _` mp_tac
  \\ simp [gc_inv_def]
  \\ pairarg_tac
  \\ fs [])
\\ pop_assum mp_tac \\ once_rewrite_tac [isDataElement_def] \\ strip_tac
\\ `~(conf.limit <= heap_length state.h1)` by all_tac
THEN1
  (qpat_assum `gc_inv _ _ _` mp_tac
  \\ simp [gc_inv_def]
  \\ simp [heap_length_def,SUM_APPEND,el_length_def])
\\ `~(conf.limit < heap_length (state.h1 ++ h::t))` by all_tac
THEN1
  (qpat_assum `gc_inv _ _ _` mp_tac
  \\ simp [gc_inv_def]
  \\ fs [heap_length_def,SUM_APPEND,el_length_def])
\\ full_simp_tac std_ss [list_case_def]
\\ simp []
\\ pairarg_tac
\\ pop_assum mp_tac \\ simp [] \\ strip_tac
\\ qpat_assum `h = _` (fn th => fs [th] (* \\ assume_tac th *))
\\ imp_res_tac gc_move_list_consts
\\ fs []
\\ `∀ptr u. MEM (Pointer ptr u) ys ==>
     isSomeDataOrForward (heap_lookup ptr state.heap)` by all_tac
THEN1
  (rpt strip_tac
  \\ qpat_assum `gc_inv _ _ _ ==> _` kall_tac
  \\ fs [gc_inv_def]
  \\ `?y. FLOOKUP (heap_map 0 state.heap) y =
       SOME (conf.gen_start + heap_length state.h1)` by all_tac
  THEN1
    (fs [FLOOKUP_DEF,BIJ_DEF,SURJ_DEF,heap_map1_def]
    \\ qpat_assum `!xx.bbb` kall_tac
    \\ qpat_assum `!x.bbb` match_mp_tac
    \\ fs [heap_addresses_APPEND,heap_addresses_def])
  \\ res_tac
  \\ `~(is_final conf state (conf.gen_start + heap_length state.h1))` by all_tac
  THEN1
    (simp [is_final_def,heap_length_APPEND]
    \\ qpat_assum `_ = state.a` (assume_tac o GSYM)
    \\ `heap_length [] = 0` by fs [heap_length_def]
    \\ simp [heap_length_APPEND]
    \\ cheat)                   (* simple? *)
  \\ fs []
  \\ `heap_lookup (conf.gen_start + heap_length state.h1)
         (FST (heap_split conf.gen_start state.heap) ++ state.h1 ++
          DataElement ys l d::t ++ heap_expand state.n ++ state.r4 ++
          state.r1) = SOME (DataElement ys l d)` by all_tac
  THEN1
    cheat
  \\ `SOME (DataElement xs l' d') = SOME (DataElement ys l d)` by all_tac
  THEN1
    rfs []
  \\ rw []
  \\ fs [heap_ok_def]
  \\ match_mp_tac heap_similar_Data_IMP_DataOrForward
  \\ asm_exists_tac
  \\ fs []
  \\ first_x_assum match_mp_tac
  \\ imp_res_tac heap_lookup_MEM
  \\ asm_exists_tac \\ qexists_tac `u`
  \\ fs [])
\\ imp_res_tac gc_move_list_thm
\\ fs []
\\ rpt var_eq_tac
\\ imp_res_tac gc_move_list_APPEND_lemma
\\ last_x_assum mp_tac
\\ match_mp_tac IMP_IMP
\\ reverse strip_tac
THEN1
  (rpt strip_tac
  THEN1 imp_res_tac SUBMAP_TRANS
  \\ fs [])
\\ last_x_assum kall_tac
\\ fs [gc_inv_def]
\\ rpt strip_tac
THEN1
  (qpat_assum `_ = state'.a` (assume_tac o GSYM)
  \\ fs [heap_length_APPEND]
  \\ fs [heap_length_def,el_length_def])
THEN1
  (qpat_assum `_ = state'.r` (assume_tac o GSYM)
  \\ fs [heap_length_APPEND]
  \\ fs [heap_length_def,el_length_def])
THEN1
  fs [isDataElement_def]
THEN1
  rfs []
THEN1
  (fs [gen_inv_def]
  \\ rpt strip_tac
  \\ first_x_assum match_mp_tac
  \\ fs [])
THEN1
  (qpat_assum `BIJ _ _ _` mp_tac
  \\ simp []
  \\ once_rewrite_tac [GSYM APPEND_CONS_LEMMA]
  \\ simp [heap_addresses_APPEND,heap_length_def,el_length_def]
  \\ simp [heap_addresses_def])

\\ qpat_assum `!i j. _` (qspecl_then [`i`,`j`] mp_tac)
\\ fs []
\\ strip_tac
\\ fs []
\\ Cases_on `is_final conf state' j`
\\ fs [is_final_def]
THEN1
 simp [heap_length_APPEND]
 \\ cheat                       (* simple *)


\\ cheat);
(* \\ simp [] *)
(* \\ `state.h1 ++ [h] ++ t = state.h1 ++ h::t` by fs [] *)
(* \\ full_simp_tac std_ss [] *)
(* \\ IF_CASES_TAC \\ fs [] *)
(* THEN1 *)
(*   fs [gc_inv_def,heap_length_def,SUM_APPEND,el_length_def] *)
(* \\ `isDataElement h` by fs [gc_inv_def] *)
(* \\ Cases_on `h` \\ fs [isDataElement_def] *)
(* \\ pairarg_tac \\ fs [] *)
(* \\ drule gc_move_list_thm *)
(* \\ disch_then (qspec_then `l` mp_tac) \\ fs [] *)
(* \\ discharge_hyps *)
(* THEN1 cheat *)
(* \\ strip_tac *)
(* \\ rpt var_eq_tac *)
(* \\ last_assum mp_tac *)
(* \\ reverse discharge_hyps *)
(* THEN1 *)
(*   (strip_tac *)
(*   \\ metis_tac [SUBMAP_TRANS]) *)
(* \\ `state'.h2 ≠ [] ∧ (HD state'.h2 = DataElement l n b)` by all_tac *)
(* THEN1 *)
(*   (qpat_assum `gc_move_list conf state l = _` mp_tac *)
(*   \\ once_rewrite_tac [gc_move_list_ALT] *)
(*   \\ fs [LET_THM] *)
(*   \\ pairarg_tac \\ fs [] *)
(*   \\ rw [] \\ fs []) *)
(* \\ qpat_assum `gc_inv conf _ _ /\ _ /\ _ ==> _` kall_tac *)
(* \\ qpat_assum `gc_inv conf state heap0` kall_tac *)
(* \\ fs [gc_inv_def] *)
(* \\ Cases_on `state'.h2` \\ fs [] *)
(* \\ rpt strip_tac *)
(* THEN1 *)
(*   fs [heap_length_def,SUM_APPEND,SUM,el_length_def] *)
(* THEN1 *)
(*   fs [isDataElement_def] *)
(* THEN1 *)
(*   (qpat_assum `BIJ _ _ _` mp_tac *)
(*   \\ fs [heap_addresses_def,heap_addresses_APPEND,heap_length_def *)
(*         ,GSYM UNION_ASSOC,GSYM INSERT_SING_UNION,heap_length_APPEND,el_length_def]) *)
(* \\ drule gc_move_list_consts \\ strip_tac \\ fs [] *)
(* \\ qpat_assum `!i j:num. _` (qspecl_then [`i`,`j`] mp_tac) *)
(* \\ rw [] \\ fs [] *)
(* \\ Cases_on `is_final state j` *)
(* \\ fs [is_final_def] *)
(* THEN1 *)
(*   (imp_res_tac LESS_IMP_heap_lookup *)
(*   \\ full_simp_tac std_ss [GSYM APPEND_ASSOC] *)
(*   \\ fs [heap_length_APPEND] \\ fs [] *)
(*   \\ cheat) *)

(* THEN1                           (* HERE *) *)
(*   (strip_tac \\ fs [] *)
(*   \\ cheat) *)

(* \\ cheat); *)

  (* ``!h1 h2 a n heap c. *)
  (*     gc_inv (h1,h2,a,n,heap:('a,'b) heap_element list,c,limit) heap0 ==> *)
  (*     ?h13 a3 n3 heap3 c3. *)
  (*       (gc_move_loop (h1,h2,a,n,heap,c,limit) = (h13,a3,n3,heap3,c3)) /\ *)
  (*     ((heap_map 0 heap) SUBMAP (heap_map 0 heap3)) /\ *)
  (*     gc_inv (h13,[],a3,n3,heap3,c3,limit) heap0``, *)
  (* completeInduct_on `limit - heap_length h1` \\ rpt strip_tac *)
  (* \\ full_simp_tac std_ss [PULL_FORALL] \\ Cases_on `h2` *)
  (* \\ full_simp_tac std_ss [gc_move_loop_def,SUBMAP_REFL] *)
  (* \\ `isDataElement h` by full_simp_tac (srw_ss()) [gc_inv_def] *)
  (* \\ full_simp_tac std_ss [isDataElement_def] *)
  (* \\ `~(limit <= heap_length h1)` by all_tac THEN1 *)
  (*  (full_simp_tac (srw_ss()) [gc_inv_def,heap_length_def,SUM_APPEND] *)
  (*   \\ full_simp_tac std_ss [el_length_def] \\ decide_tac) *)
  (* \\ `~(limit < heap_length (h1 ++ DataElement ys l d::t))` by all_tac THEN1 *)
  (*  (full_simp_tac (srw_ss()) [gc_inv_def,heap_length_def,SUM_APPEND] *)
  (*   \\ full_simp_tac std_ss [el_length_def] \\ decide_tac) *)
  (* \\ full_simp_tac (srw_ss()) [] *)
  (* \\ `!ptr u. MEM (Pointer ptr u) (ys:'a heap_address list) ==> *)
  (*             isSomeDataOrForward (heap_lookup ptr heap)` by all_tac THEN1 *)
  (*  (rpt strip_tac \\ qpat_assum `!x1 x2 x3. bbb` (K all_tac) *)
  (*   \\ full_simp_tac std_ss [gc_inv_def] *)
  (*   \\ `?i. FLOOKUP (heap_map 0 heap) i = SOME (heap_length h1)` by all_tac THEN1 *)
  (*    (full_simp_tac std_ss [FLOOKUP_DEF,BIJ_DEF,SURJ_DEF,heap_map1_def] *)
  (*     \\ qpat_assum `!xx.bbb` (K all_tac) \\ qpat_assum `!xx.bbb` match_mp_tac *)
  (*     \\ full_simp_tac (srw_ss()) [heap_addresses_APPEND,heap_addresses_def]) *)
  (*   \\ res_tac \\ `~(heap_length h1 < heap_length h1)` by decide_tac *)
  (*   \\ imp_res_tac NOT_LESS_IMP_heap_lookup *)
  (*   \\ full_simp_tac (srw_ss()) [heap_lookup_def] *)
  (*   \\ full_simp_tac std_ss [heap_ok_def] *)
  (*   \\ imp_res_tac heap_lookup_MEM \\ res_tac *)
  (*   \\ imp_res_tac heap_similar_Data_IMP_DataOrForward) *)
  (* \\ mp_tac (Q.SPECL [`ys`,`DataElement ys l d::t`,`a`,`n`,`heap`,`c`] gc_move_list_thm) *)
  (* \\ match_mp_tac IMP_IMP \\ strip_tac THEN1 (fs [] \\ rw [] \\ res_tac) *)
  (* \\ full_simp_tac std_ss [] \\ strip_tac \\ full_simp_tac std_ss [LET_DEF] *)
  (* \\ imp_res_tac gc_move_list_APPEND_lemma *)
  (* \\ full_simp_tac (srw_ss()) [] \\ full_simp_tac std_ss [AND_IMP_INTRO] *)
  (* \\ qpat_assum `!limit h1 h2. bbb` (mp_tac o Q.SPECL [`limit`, *)
  (*      `h1 ++ [DataElement (ADDR_MAP (heap_map1 (heap3:('a,'b) heap_element list)) ys) l d]`,`t ++ xs1`, *)
  (*      `a3`,`n3`,`heap3`,`c3`]) \\ full_simp_tac std_ss [] *)
  (* \\ match_mp_tac IMP_IMP \\ reverse strip_tac *)
  (* THEN1 (rpt strip_tac \\ full_simp_tac std_ss [] \\ imp_res_tac SUBMAP_TRANS) *)
  (* \\ strip_tac THEN1 *)
  (*  (full_simp_tac (srw_ss()) [heap_length_def,el_length_def,SUM_APPEND] \\ decide_tac) *)
  (* \\ full_simp_tac std_ss [gc_inv_def,EVERY_DEF,EVERY_APPEND] *)
  (* \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND] *)
  (* \\ strip_tac *)
  (* THEN1 (full_simp_tac (srw_ss()) [heap_length_def,SUM_APPEND,el_length_def]) *)
  (* \\ strip_tac THEN1 (full_simp_tac (srw_ss()) [isDataElement_def]) *)
  (* \\ strip_tac THEN1 *)
  (*  (full_simp_tac std_ss [heap_addresses_APPEND,heap_addresses_def,el_length_def]) *)
  (* \\ rpt strip_tac *)
  (* \\ qpat_assum `!i j:num. bbb` (mp_tac o Q.SPECL [`i`,`j`]) *)
  (* \\ full_simp_tac std_ss [] \\ strip_tac \\ full_simp_tac (srw_ss()) [] *)
  (* \\ Cases_on `j < heap_length h1` THEN1 *)
  (*  (imp_res_tac LESS_IMP_heap_lookup \\ full_simp_tac (srw_ss()) [] *)
  (*   \\ full_simp_tac (srw_ss()) [heap_length_def,SUM_APPEND] *)
  (*   \\ rw [] \\ res_tac \\ `F` by decide_tac) *)
  (* \\ imp_res_tac NOT_LESS_IMP_heap_lookup \\ full_simp_tac std_ss [] *)
  (* \\ full_simp_tac std_ss [heap_lookup_def] *)
  (* \\ Cases_on `j <= heap_length h1` \\ full_simp_tac (srw_ss()) [] THEN1 *)
  (*  (full_simp_tac std_ss [heap_length_APPEND] \\ SRW_TAC [] [] *)
  (*   \\ full_simp_tac (srw_ss()) [heap_length_def,el_length_def] *)
  (*   \\ res_tac \\ `F` by decide_tac) *)
  (* \\ full_simp_tac std_ss [el_length_def] *)
  (* \\ `0 < l+1` by decide_tac \\ full_simp_tac std_ss [] *)
  (* \\ Cases_on `j < heap_length h1 + (l + 1)` \\ full_simp_tac (srw_ss()) [] *)
  (* \\ full_simp_tac std_ss [heap_length_APPEND] *)
  (* \\ full_simp_tac (srw_ss()) [heap_length_def,el_length_def]); *)

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

Induct
\\ once_rewrite_tac [gc_move_loop_def]
  \\ cheat);

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
    gc_inv conf (starting_state with <| heap := heap; n := conf.limit |>) heap``,
  fs [heap_ok_def,gc_inv_def,starting_state_def,LET_THM]
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

val gc_inv_imp_n = prove(
  ``gc_inv conf state heap ==>
    (state.n = conf.limit − state.a − state.r) /\
    (state.a + state.n + state.r = conf.limit)``,
  fs [gc_inv_def,LET_THM]
  \\ strip_tac
  \\ decide_tac);

val full_gc_thm = store_thm("full_gc_thm",
  ``roots_ok roots heap /\ heap_ok (heap : ('a,'b) heap_element list) conf.limit ==>
      ?state.
        (full_gc conf (roots : 'a heap_address list,heap) =
          (ADDR_MAP (heap_map1 state.heap) roots,state.h1,state.r1,state.a,state.r,T)) /\
        (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM (heap_map 0 state.heap)) /\
        gc_inv conf state heap /\
        (state.h2 = []) /\
        (state.r4 = []) /\
        (state.r3 = []) /\
        (state.r2 = [])``,
  rpt strip_tac
  \\ imp_res_tac gc_inv_init
  \\ fs [full_gc_def]
  \\ fs [LET_THM]
  \\ pairarg_tac \\ fs []
  \\ drule gc_move_list_thm
  \\ disch_then (qspec_then `roots` mp_tac)
  \\ discharge_hyps
  THEN1 (fs [roots_ok_def,isSomeDataOrForward_def] \\ metis_tac [])
  \\ strip_tac \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ mp_tac (Q.SPECL [`conf.limit`,`state`] gc_move_loop_thm)
  \\ fs []
  \\ strip_tac
  \\ qexists_tac `gc_move_loop conf state conf.limit`
  \\ fs []
  \\ rpt strip_tac
  THEN1
    (match_mp_tac ADDR_MAP_EQ
    \\ rpt strip_tac
    \\ fs [heap_map1_def,SUBMAP_DEF]
    \\ metis_tac [])
  \\ TRY (fs [heap_ok_def,gc_inv_def,LET_THM] \\ NO_TAC)
  \\ rpt strip_tac
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

val full_gc_LENGTH = store_thm("full_gc_LENGTH",
  ``roots_ok roots heap /\
    heap_ok (heap:('a,'b) heap_element list) conf.limit ==>
    ?roots2 h12 r12.
      (full_gc conf (roots:'a heap_address list,heap) =
        (roots2,h12,r12,heap_length h12,heap_length r12,T))``,
  rw []
  \\ imp_res_tac full_gc_thm
  \\ fs []
  \\ rpt strip_tac
  \\ fs [full_gc_def,gc_inv_def,LET_THM]);

val FILTER_isForward_heap_expand_lemma = prove(
  ``!n. FILTER isForwardPointer (heap_expand n) = []``,
  fs [FILTER,heap_expand_def,isForwardPointer_def]
  \\ Cases
  \\ fs [isForwardPointer_def]);

val MEM_heap_expand_FALSE = prove(
  ``!n. ~(MEM (DataElement xs l d) (heap_expand n))``,
  Cases \\ fs [MEM,heap_expand_def]);

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

val heap_lookup_IMP_heap_addresses2 = prove(
  ``!(xs:('a,'b) heap_element list) (ys:('a,'b) heap_element list) x j.
    (heap_lookup j ys = SOME x) ==>
    (heap_length xs + j) IN heap_addresses (heap_length xs) ys``,
  rpt strip_tac
  \\ imp_res_tac heap_lookup_IMP_heap_addresses_GEN
  \\ pop_assum (mp_tac o Q.SPEC `heap_length xs`) \\ strip_tac);

val full_gc_ok = store_thm("full_gc_ok",
  ``roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) conf.limit ==>
    ?roots2 state.
      let heap' = state.h1 ++ heap_expand state.n ++ state.r1 in
      (full_gc conf (roots:'a heap_address list,heap) =
        (roots2,state.h1,state.r1,state.a,state.r,T)) /\
      state.a + state.r <= conf.limit /\
      roots_ok roots2 heap' /\
      heap_ok heap' conf.limit``,

  rpt strip_tac
  \\ mp_tac full_gc_thm
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
    \\ `is_final state j` by all_tac
    THEN1
      (simp [is_final_def,LET_THM]
      \\ imp_res_tac heap_lookup_LESS
      \\ fs [])
    \\ fs []
    \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
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
    THEN1
      simp [heap_length_APPEND,heap_length_heap_expand]
    \\ `?i. (FLOOKUP (heap_map 0 state.heap) i = SOME (state.a + state.n + j))` by all_tac
    THEN1
      (imp_res_tac heap_lookup_IMP_heap_addresses_GEN
      \\ pop_assum (qspecl_then [`state.a + state.n`] mp_tac)
      \\ simp []
      \\ strip_tac
      \\ fs [BIJ_DEF,SURJ_DEF,heap_map1_def,FLOOKUP_DEF])
    \\ res_tac
    \\ `is_final state (state.a + state.n + j)` by all_tac
    THEN1 simp [is_final_def,LET_THM,heap_length_def]
    \\ fs []
    \\ imp_res_tac heap_lookup_AND_PREPEND_IMP
    \\ fs [] \\ rpt var_eq_tac \\ fs []
    \\ ntac 2 (pop_assum kall_tac)
    \\ drule MEM_ADDR_MAP \\ strip_tac \\ var_eq_tac
    \\ res_tac
    \\ rfs []
    \\ rpt var_eq_tac \\ fs []
    \\ fs [heap_map1_def,FLOOKUP_DEF]
    \\ qpat_assum `!i':num. _ ==> _` drule
    \\ strip_tac
    \\ res_tac
    \\ fs [isSomeDataElement_def]));

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

val full_gc_related = store_thm("full_gc_related",
  ``roots_ok roots heap /\ heap_ok (heap:('a,'b) heap_element list) conf.limit ==>
    ?state f.
      (full_gc conf (roots:'a heap_address list,heap) =
         (ADDR_MAP (FAPPLY f) roots,state.h1,state.r1,state.a,state.r,T)) /\
      (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM f) /\
      gc_related f heap (state.h1 ++ heap_expand state.n ++ state.r1)``,
  strip_tac
  \\ mp_tac full_gc_thm
  \\ fs []
  \\ rpt strip_tac \\ fs []
  \\ qexists_tac `state`
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
    \\ qpat_assum `state.n = _` (fn th => fs [th])
    \\ fs [isSomeDataElement_def])
  THEN1
    (`(FLOOKUP (heap_map 0 state.heap) i = SOME (heap_map1 state.heap i))` by fs [FLOOKUP_DEF]
    \\ res_tac \\ fs []
    \\ `is_final conf.limit state.h1 [] [] state.r1 (heap_map1 state.heap i)` by all_tac
    THEN1
      (simp [is_final_def,LET_THM]
      \\ fs [INJ_DEF,SURJ_DEF]
      \\ res_tac \\ fs [] \\ rpt var_eq_tac \\ fs []
      \\ drule IN_heap_addresses_LESS \\ strip_tac
      \\ decide_tac)
    \\ fs []
    \\ rpt var_eq_tac \\ fs []
    \\ imp_res_tac heap_lookup_LESS
    \\ rpt var_eq_tac \\ fs []
    \\ fs []
    \\ drule heap_lookup_EXTEND \\ disch_then (qspec_then `[]` assume_tac)
    \\ fs []
    \\ qpat_assum `state.n = _` (fn th => fs [th]))
  \\ `(FLOOKUP (heap_map 0 state.heap) i = SOME (heap_map1 state.heap i))` by all_tac
  THEN1
    fs [FLOOKUP_DEF]
  \\ res_tac \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ `is_final conf.limit state.h1 [] [] state.r1 (heap_map1 state.heap i)` by all_tac
  THEN1
    (simp [is_final_def,LET_THM]
    \\ fs [INJ_DEF,SURJ_DEF]
    \\ res_tac \\ fs [] \\ rpt var_eq_tac \\ fs []
    \\ drule IN_heap_addresses_LESS \\ strip_tac
    \\ decide_tac)
  \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ qpat_assum `!ptr d. _ ==> _ ` (qspecl_then [`ptr`, `u`] assume_tac)
  \\ fs []);

(* Lemmas about ok and a *)

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
    state.ok /\
    ((state.a = b + heap_length state.h2) ==> (state'.a = b + heap_length state'.h2)) /\
    ((state.r = c + heap_length state.r4) ==> (state'.r = c + heap_length state'.r4))``,
  Cases_on `x`
  \\ fs [gc_move_def]
  \\ Cases_on `heap_lookup n state.heap`
  \\ fs []
  \\ rpt strip_tac
  \\ fs [fetch "-" "gc_state_component_equality"]
  \\ Cases_on `x`
  \\ fs [fetch "-" "gc_state_component_equality",LET_THM]
  THEN1
    (pairarg_tac
    \\ Cases_on `conf.isRef (DataElement l n' b)` \\ fs []
    \\ TRY pairarg_tac
    \\ fs [fetch "-" "gc_state_component_equality"]
    \\ rpt var_eq_tac
    \\ imp_res_tac gc_forward_ptr_ok)
  THEN1
    metis_tac []
  THEN1
    (pairarg_tac
    \\ Cases_on `conf.isRef (DataElement l n' b')` \\ fs []
    \\ TRY pairarg_tac
    \\ fs [fetch "-" "gc_state_component_equality"]
    THEN1 metis_tac []
    \\ qpat_assum `_ = state'.h2` (mp_tac o GSYM)
    \\ strip_tac
    \\ fs [heap_length_APPEND,heap_length_def,el_length_def,SUM_APPEND])
  THEN1
    metis_tac []
  THEN1
    (Cases_on `conf.isRef (DataElement l n' b)` \\ fs []
    \\ TRY pairarg_tac \\ fs [fetch "-" "gc_state_component_equality"]
    THEN1
      (rpt var_eq_tac \\ fs []
      \\ qpat_assum `_ = state'.r4` (mp_tac o GSYM) \\ strip_tac
      \\ fs [heap_length_APPEND,heap_length_def,el_length_def,SUM_APPEND])
    \\ metis_tac []));

val gc_move_list_ok = store_thm("gc_move_list_ok",
  ``!xs xs' state state'.
      (gc_move_list conf state xs = (xs',state')) /\ state'.ok ==>
      state.ok /\
      ((state.a = b + heap_length state.h2) ==> (state'.a = b + heap_length state'.h2)) /\
      ((state.r = c + heap_length state.r4) ==> (state'.r = c + heap_length state'.r4))``,
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

(* Let's only prove the following once they are needed.

val th =
  fetch "-" "gc_move_loop_ind" |>
  Q.SPEC `(\(h1,h2,a,n,heap,c,limit).
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
  \\ qpat_assum `!xs.bbb` mp_tac
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV (srw_ss()) []))
  \\ asm_rewrite_tac [] \\ simp_tac std_ss [LET_DEF] \\ rpt strip_tac
  \\ res_tac \\ full_simp_tac std_ss [] \\ imp_res_tac gc_move_list_ok);

val th = MP th lemma |> SIMP_RULE std_ss []
         |> Q.SPECL [`h1`,`h2`,`a`,`n`,`heap`,`c`,`limit`,`h1'`,`a'`,`n'`,`heap'`]

val gc_move_loop_ok = save_thm("gc_move_loop_ok",th);

val gc_move_list_IMP_LENGTH = store_thm("gc_move_list_IMP_LENGTH",
  ``!xs xs' state state'.
      (gc_move_list conf state xs = (xs',state')) ==>
      (LENGTH xs = LENGTH xs')``,
  cheat);
  (* ``!l5 h a n heap c k xs ys a1 xs1 heap1 c1. *)
  (*     (gc_move_list (l5,h,a,n,heap,c,k) = *)
  (*       (xs,ys,a1,xs1,heap1,c1)) ==> (LENGTH xs = LENGTH l5)``, *)
  (* Induct \\ fs [gc_move_list_def,LET_THM] \\ rw [] *)
  (* \\ pairarg_tac \\ fs[] *)
  (* \\ pairarg_tac \\ fs[] \\ rw [] *)
  (* \\ res_tac \\ fs []); *)

val full_gc_IMP_LENGTH = store_thm("full_gc_IMP_LENGTH",
  ``(full_gc conf (xs,heap) = (roots2,h1,r1,a,r,T)) ==>
    (LENGTH roots2 = LENGTH xs)``,
  fs [full_gc_def,LET_THM]
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ imp_res_tac gc_move_list_IMP_LENGTH \\ fs []);

*)

val _ = export_theory();
