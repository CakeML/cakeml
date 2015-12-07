open preamble bvlSemTheory bvpSemTheory bvpPropsTheory copying_gcTheory
     int_bitwiseTheory wordSemTheory bvp_to_wordTheory set_sepTheory labSemTheory;

val _ = new_theory "bvp_to_wordProps";

(* -------------------------------------------------------------
    TODO:
     - put length into higher bits of block headers
       (make byte array length easy to retrieve)
     - consider putting information in the abstract pointers?
   ------------------------------------------------------------- *)

val _ = Datatype `
  tag = BlockTag num | RefTag | BytesTag num | NumTag bool`;

val BlockRep_def = Define `
  BlockRep tag xs = DataElement xs (LENGTH xs) (BlockTag tag,[])`;

val _ = type_abbrev("ml_el",
  ``:('a word_loc, tag # ('a word_loc list)) heap_element``);

val _ = type_abbrev("ml_heap",``:'a ml_el list``);

val words_of_bits_def = tDefine "words_of_bits" `
  (words_of_bits [] = []:'a word list) /\
  (words_of_bits xs =
     let n = dimindex (:'a) in
       n2w (num_of_bits (TAKE n xs)) :: words_of_bits (DROP n xs))`
  (WF_REL_TAC `measure LENGTH` \\ fs [LENGTH_DROP])

val bits_of_words_def = Define `
  (bits_of_words [] = []) /\
  (bits_of_words ((w:'a word)::ws) =
     GENLIST (\n. w ' n) (dimindex (:'a)) ++ bits_of_words ws)`

val word_of_bytes_def = Define `
  (word_of_bytes be a [] = 0w) /\
  (word_of_bytes be a (b::bs) =
     set_byte a b (word_of_bytes be (a+1w) bs) be)`

val words_of_bytes_def = tDefine "words_of_bytes" `
  (words_of_bytes be [] = ([]:'a word list)) /\
  (words_of_bytes be bytes =
     let xs = TAKE (MAX 1 (w2n (bytes_in_word:'a word))) bytes in
     let ys = DROP (MAX 1 (w2n (bytes_in_word:'a word))) bytes in
       word_of_bytes be 0w xs :: words_of_bytes be ys)`
 (WF_REL_TAC `measure (LENGTH o SND)` \\ fs [])

val Bytes_def = Define`
  ((Bytes is_bigendian (bs:word8 list)):'a ml_el) =
    let ws = words_of_bytes is_bigendian bs in
      DataElement [] (LENGTH ws) (BytesTag (LENGTH bs), MAP Word ws)`

val words_of_int_def = Define `
  words_of_int i =
    if 0 <= i then words_of_bits (bits_of_num (Num i)) else
      MAP (~) (words_of_bits (bits_of_num (Num (int_not i))))`

val Bignum_def = Define `
  Bignum i =
    DataElement [] (LENGTH ((words_of_int i):'a word list))
      (NumTag (i < 0), MAP Word ((words_of_int i):'a word list))`;

val Smallnum_def = Define `
  Smallnum i =
    if i < 0 then 0w - n2w (Num (4 * (0 - i))) else n2w (Num (4 * i))`;

val small_int_def = Define `
  small_int (:'a) i <=> w2i (((Smallnum i) >> 2):'a word) = i`;

val BlockNil_def = Define `
  BlockNil n = n2w n << 2 + 2w`;

val v_size_LEMMA = prove(
  ``!vs v. MEM v vs ==> v_size v <= v1_size vs``,
  Induct \\ full_simp_tac (srw_ss()) [v_size_def]
  \\ rpt strip_tac \\ res_tac \\ full_simp_tac std_ss [] \\ DECIDE_TAC);

(*
  code pointers (i.e. Locs) will end in ...0
  small numbers end in ...00
  NIL-like constructors end in ...10
*)

val v_inv_def = tDefine "v_inv" `
  (v_inv (Number i) (x,f,heap:'a ml_heap) <=>
     if small_int (:'a) i then (x = Data (Word (Smallnum i))) else
       ?ptr u. (x = Pointer ptr u) /\ (heap_lookup ptr heap = SOME (Bignum i))) /\
  (v_inv (CodePtr n) (x,f,heap) <=>
     (x = Data (Loc n 0))) /\
  (v_inv (RefPtr n) (x,f,heap) <=>
     ?u. (x = Pointer (f ' n) u) /\ n IN FDOM f) /\
  (v_inv (Block n vs) (x,f,heap) <=>
     if vs = [] then (x = Data (Word (BlockNil n))) else
       ?ptr u xs.
         EVERY2 (\v x. v_inv v (x,f,heap)) vs xs /\
         (x = Pointer ptr u) /\ (heap_lookup ptr heap = SOME (BlockRep n xs)))`
 (WF_REL_TAC `measure (v_size o FST)` \\ rpt strip_tac
  \\ imp_res_tac v_size_LEMMA \\ DECIDE_TAC);

val get_refs_def = tDefine "get_refs" `
  (get_refs (Number _) = []) /\
  (get_refs (CodePtr _) = []) /\
  (get_refs (RefPtr p) = [p]) /\
  (get_refs (Block tag vs) = FLAT (MAP get_refs vs))`
 (WF_REL_TAC `measure (v_size)` \\ rpt strip_tac \\ Induct_on `vs`
  \\ srw_tac [] [v_size_def] \\ res_tac \\ DECIDE_TAC);

val ref_edge_def = Define `
  ref_edge refs (x:num) (y:num) =
    case FLOOKUP refs x of
    | SOME (ValueArray ys) => MEM y (get_refs (Block ARB ys))
    | _ => F`

val reachable_refs_def = Define `
  reachable_refs roots refs t =
    ?x r. MEM x roots /\ MEM r (get_refs x) /\ RTC (ref_edge refs) r t`;

val RefBlock_def = Define `
  RefBlock xs = DataElement xs (LENGTH xs) (RefTag,[])`;

val bc_ref_inv_def = Define `
  bc_ref_inv n refs (f,heap,be) =
    case (FLOOKUP f n, FLOOKUP refs n) of
    | (SOME x, SOME (ValueArray ys)) =>
        (?zs. (heap_lookup x heap = SOME (RefBlock zs)) /\
              EVERY2 (\z y. v_inv y (z,f,heap)) zs ys)
    | (SOME x, SOME (ByteArray ws)) =>
        (heap_lookup x heap = SOME (Bytes be ws))
    | _ => F`;

val bc_stack_ref_inv_def = Define `
  bc_stack_ref_inv stack refs (roots, heap, be) =
    ?f. INJ (FAPPLY f) (FDOM f) { a | isSomeDataElement (heap_lookup a heap) } /\
        FDOM f SUBSET FDOM refs /\
        EVERY2 (\v x. v_inv v (x,f,heap)) stack roots /\
        !n. reachable_refs stack refs n ==> bc_ref_inv n refs (f,heap,be)`;

val unused_space_inv_def = Define `
  unused_space_inv ptr l heap <=>
    (l <> 0 ==> (heap_lookup ptr heap = SOME (Unused (l-1))))`;

val abs_ml_inv_def = Define `
  abs_ml_inv stack refs (roots,heap,be,a,sp) limit <=>
    roots_ok roots heap /\ heap_ok heap limit /\
    unused_space_inv a sp heap /\
    bc_stack_ref_inv stack refs (roots,heap,be)`;

(* --- *)

val MOD_EQ_0_0 = prove(
  ``∀n b. 0 < b ⇒ (n MOD b = 0) ⇒ n < b ⇒ (n = 0)``,
  rw[MOD_EQ_0_DIVISOR] >> Cases_on`d`>>fs[])

val EVERY2_IMP_EVERY2 = prove(
  ``!xs ys P1 P2.
      (!x y. MEM x xs /\ MEM y ys /\ P1 x y ==> P2 x y) ==>
      EVERY2 P1 xs ys ==> EVERY2 P2 xs ys``,
  Induct \\ Cases_on `ys` \\ full_simp_tac (srw_ss()) []
  \\ rpt strip_tac \\ metis_tac []);

val EVERY2_APPEND_IMP = prove(
  ``!xs1 xs2 ys.
      EVERY2 P (xs1 ++ xs2) ys ==>
      ?ys1 ys2. (ys = ys1 ++ ys2) /\ EVERY2 P xs1 ys1 /\ EVERY2 P xs2 ys2``,
  Induct \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `ys` \\ full_simp_tac (srw_ss()) [] \\ rpt strip_tac
  \\ res_tac \\ metis_tac [LIST_REL_def,APPEND]);

val MEM_EVERY2_IMP = prove(
  ``!l x zs P. MEM x l /\ EVERY2 P zs l ==> ?z. MEM z zs /\ P z x``,
  Induct \\ Cases_on `zs` \\ full_simp_tac (srw_ss()) [] \\ metis_tac []);

val EVERY2_LENGTH = LIST_REL_LENGTH
val EVERY2_IMP_LENGTH = EVERY2_LENGTH

val EVERY2_APPEND_CONS = prove(
  ``!xs y ys zs P. EVERY2 P (xs ++ y::ys) zs ==>
                   ?t1 t t2. (zs = t1 ++ t::t2) /\ (LENGTH t1 = LENGTH xs) /\
                             EVERY2 P xs t1 /\ P y t /\ EVERY2 P ys t2``,
  Induct \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `zs` \\ full_simp_tac (srw_ss()) []
  \\ rpt strip_tac
  \\ res_tac \\ full_simp_tac std_ss []
  \\ Q.LIST_EXISTS_TAC [`h::t1`,`t'`,`t2`]
  \\ full_simp_tac (srw_ss()) []);

val EVERY2_SWAP = prove(
  ``!xs ys. EVERY2 P xs ys ==> EVERY2 (\y x. P x y) ys xs``,
  Induct \\ Cases_on `ys` \\ full_simp_tac (srw_ss()) []);

val EVERY2_APPEND_IMP_APPEND = prove(
  ``!xs1 xs2 ys P.
      EVERY2 P (xs1 ++ xs2) ys ==>
      ?ys1 ys2. (ys = ys1 ++ ys2) /\ EVERY2 P xs1 ys1 /\ EVERY2 P xs2 ys2``,
  Induct \\ Cases_on `ys` \\ full_simp_tac (srw_ss()) [] \\ rpt strip_tac
  \\ res_tac \\ full_simp_tac std_ss []
  \\ Q.LIST_EXISTS_TAC [`h::ys1`,`ys2`]
  \\ full_simp_tac std_ss [APPEND,LIST_REL_def] \\ metis_tac[]);

val EVERY2_IMP_APPEND = rich_listTheory.EVERY2_APPEND_suff
val IMP_EVERY2_APPEND = EVERY2_IMP_APPEND

val EVERY2_EQ_EL = LIST_REL_EL_EQN

val EVERY2_IMP_EL = METIS_PROVE[EVERY2_EQ_EL]
  ``!xs ys P. EVERY2 P xs ys ==> !n. n < LENGTH ys ==> P (EL n xs) (EL n ys)``

val EVERY2_MAP_FST_SND = prove(
  ``!xs. EVERY2 P (MAP FST xs) (MAP SND xs) = EVERY (\(x,y). P x y) xs``,
  Induct \\ srw_tac [] [LIST_REL_def] \\ Cases_on `h` \\ srw_tac [] []);

val fapply_fupdate_update = store_thm("fapply_fupdate_update",
  ``$' (f |+ p) = (FST p =+ SND p) ($' f)``,
  Cases_on`p`>>
  simp[FUN_EQ_THM,FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM] >> rw[])

val heap_lookup_APPEND1 = prove(
  ``∀h1 z h2.
    heap_length h1 ≤ z ⇒
    (heap_lookup z (h1 ++ h2) = heap_lookup (z - heap_length h1) h2)``,
  Induct >>fs[heap_lookup_def,heap_length_def] >> rw[] >> simp[]
  >> fsrw_tac[ARITH_ss][] >> Cases_on`h`>>fs[el_length_def])

val heap_lookup_APPEND2 = prove(
  ``∀h1 z h2.
    z < heap_length h1 ⇒
    (heap_lookup z (h1 ++ h2) = heap_lookup z h1)``,
  Induct >> fs[heap_lookup_def,heap_length_def] >> rw[] >>
  simp[])

val heap_lookup_APPEND = store_thm("heap_lookup_APPEND",
  ``heap_lookup a (h1 ++ h2) =
    if a < heap_length h1 then
    heap_lookup a h1 else
    heap_lookup (a-heap_length h1) h2``,
  rw[heap_lookup_APPEND2] >>
  simp[heap_lookup_APPEND1])


(* Prove refinement is maintained past GC calls *)

val LENGTH_ADDR_MAP = prove(
  ``!xs f. LENGTH (ADDR_MAP f xs) = LENGTH xs``,
  Induct \\ TRY (Cases_on `h`) \\ srw_tac [] [ADDR_MAP_def]);

val MEM_IMP_v_size = prove(
  ``!l a. MEM a l ==> v_size a < 1 + v1_size l``,
  Induct \\ full_simp_tac std_ss [MEM,v_size_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [] \\ res_tac \\ DECIDE_TAC);

val EL_ADDR_MAP = prove(
  ``!xs n f.
      n < LENGTH xs ==> (EL n (ADDR_MAP f xs) = ADDR_APPLY f (EL n xs))``,
  Induct \\ full_simp_tac (srw_ss()) [] \\ Cases_on `n` \\ Cases_on `h`
  \\ full_simp_tac (srw_ss()) [ADDR_MAP_def,ADDR_APPLY_def]);

val _ = augment_srw_ss [rewrites [LIST_REL_def]];

val v_inv_related = prove(
  ``!w x f.
      gc_related g heap1 (heap2:'a ml_heap) /\
      (!ptr u. (x = Pointer ptr u) ==> ptr IN FDOM g) /\
      v_inv w (x,f,heap1) ==>
      v_inv w (ADDR_APPLY (FAPPLY g) x,g f_o_f f,heap2) /\
      EVERY (\n. f ' n IN FDOM g) (get_refs w)``,
  completeInduct_on `v_size w` \\ NTAC 5 strip_tac
  \\ full_simp_tac std_ss [PULL_FORALL] \\ Cases_on `w` THEN1
   (full_simp_tac std_ss [v_inv_def,get_refs_def,EVERY_DEF]
    \\ Cases_on `small_int (:'a) i`
    \\ full_simp_tac (srw_ss()) [ADDR_APPLY_def,Bignum_def]
    \\ full_simp_tac std_ss [gc_related_def] \\ res_tac
    \\ full_simp_tac std_ss [ADDR_MAP_def] \\ fs [])
  THEN1
   (full_simp_tac (srw_ss()) [v_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ Cases_on `l = []` \\ full_simp_tac std_ss []
    THEN1 (full_simp_tac (srw_ss()) [get_refs_def,ADDR_APPLY_def])
    \\ full_simp_tac (srw_ss()) [v_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ full_simp_tac std_ss [gc_related_def] \\ res_tac
    \\ full_simp_tac (srw_ss()) [] \\ NTAC 2 (POP_ASSUM MP_TAC)
    \\ full_simp_tac std_ss [LENGTH_ADDR_MAP] \\ strip_tac
    \\ reverse strip_tac THEN1
     (full_simp_tac std_ss [get_refs_def,EVERY_MEM,MEM_FLAT,PULL_EXISTS,MEM_MAP]
      \\ full_simp_tac std_ss [v_size_def] \\ rpt strip_tac
      \\ Q.MATCH_ASSUM_RENAME_TAC `MEM k (get_f a)`
      \\ imp_res_tac MEM_IMP_v_size
      \\ `v_size a < 1 + (n + v1_size l)` by DECIDE_TAC
      \\ `?l1 l2. l = l1 ++ a::l2` by metis_tac [MEM_SPLIT]
      \\ full_simp_tac std_ss [] \\ imp_res_tac EVERY2_SPLIT_ALT
      \\ full_simp_tac std_ss [MEM_APPEND,MEM]
      \\ res_tac \\ metis_tac [])
    \\ full_simp_tac std_ss [EVERY2_EVERY,LENGTH_ADDR_MAP,EVERY_MEM,FORALL_PROD]
    \\ qpat_assum `LENGTH l = LENGTH xs` ASSUME_TAC
    \\ full_simp_tac std_ss [MEM_ZIP,LENGTH_ADDR_MAP,PULL_EXISTS]
    \\ strip_tac \\ strip_tac
    \\ Q.MATCH_ASSUM_RENAME_TAC `t < LENGTH xs` \\ res_tac
    \\ `MEM (EL t l) l` by (full_simp_tac std_ss [MEM_EL] \\ metis_tac [])
    \\ `MEM (EL t xs) xs` by (full_simp_tac std_ss [MEM_EL] \\ metis_tac [])
    \\ `(!ptr u. (EL t xs = Pointer ptr u) ==> ptr IN FDOM g)` by metis_tac []
    \\ `v_size (EL t l)  < v_size (Block n l)` by ALL_TAC THEN1
     (full_simp_tac std_ss [v_size_def]
      \\ imp_res_tac MEM_IMP_v_size \\ DECIDE_TAC)
    \\ res_tac \\ full_simp_tac std_ss [EL_ADDR_MAP]
    \\ first_assum match_mp_tac \\ fs [])
  THEN1
    (full_simp_tac (srw_ss()) [v_inv_def,ADDR_APPLY_def,get_refs_def])
  THEN1
    (full_simp_tac (srw_ss()) [v_inv_def,ADDR_APPLY_def]
     \\ `n IN FDOM (g f_o_f f)` by ALL_TAC \\ asm_simp_tac std_ss []
     \\ full_simp_tac (srw_ss()) [f_o_f_DEF,get_refs_def]));

val EVERY2_ADDR_MAP = prove(
  ``!zs l. EVERY2 P (ADDR_MAP g zs) l <=>
           EVERY2 (\x y. P (ADDR_APPLY g x) y) zs l``,
  Induct \\ Cases_on `l`
  \\ full_simp_tac std_ss [LIST_REL_def,ADDR_MAP_def] \\ Cases
  \\ full_simp_tac std_ss [LIST_REL_def,ADDR_MAP_def,ADDR_APPLY_def]);

val bc_ref_inv_related = prove(
  ``gc_related g heap1 heap2 /\
    bc_ref_inv n refs (f,heap1,be) /\ (f ' n) IN FDOM g ==>
    bc_ref_inv n refs (g f_o_f f,heap2,be)``,
  full_simp_tac std_ss [bc_ref_inv_def] \\ strip_tac \\ full_simp_tac std_ss []
  \\ MP_TAC v_inv_related \\ asm_simp_tac std_ss []
  \\ full_simp_tac (srw_ss()) [f_o_f_DEF,gc_related_def,RefBlock_def] \\ res_tac
  \\ Cases_on `FLOOKUP f n` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `FLOOKUP refs n` \\ full_simp_tac (srw_ss()) []
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,f_o_f_DEF]
  \\ Cases_on `x'` \\ full_simp_tac (srw_ss()) []
  \\ TRY (fs[Bytes_def,LET_THM] >> res_tac >> simp[ADDR_MAP_def] >> NO_TAC)
  \\ res_tac \\ full_simp_tac (srw_ss()) [LENGTH_ADDR_MAP,EVERY2_ADDR_MAP]
  \\ rpt strip_tac \\ qpat_assum `EVERY2 qqq zs l` MP_TAC
  \\ match_mp_tac EVERY2_IMP_EVERY2 \\ simp_tac std_ss [] \\ rpt strip_tac
  \\ Cases_on `x'` \\ full_simp_tac (srw_ss()) [ADDR_APPLY_def]
  \\ res_tac \\ fs [ADDR_APPLY_def]);

val RTC_lemma = prove(
  ``!r n. RTC (ref_edge refs) r n ==>
          (!m. RTC (ref_edge refs) r m ==> bc_ref_inv m refs (f,heap,be)) /\
          gc_related g heap heap2 /\
          f ' r IN FDOM g ==> f ' n IN FDOM g``,
  ho_match_mp_tac RTC_INDUCT \\ full_simp_tac std_ss [] \\ rpt strip_tac
  \\ full_simp_tac std_ss []
  \\ qpat_assum `bb ==> bbb` match_mp_tac \\ full_simp_tac std_ss []
  \\ strip_tac THEN1
   (rpt strip_tac \\ qpat_assum `!x.bb` match_mp_tac \\ metis_tac [RTC_CASES1])
  \\ `RTC (ref_edge refs) r r' /\ RTC (ref_edge refs) r r` by metis_tac [RTC_CASES1]
  \\ res_tac \\ qpat_assum `!x.bb` (K ALL_TAC)
  \\ full_simp_tac std_ss [bc_ref_inv_def,RefBlock_def,RTC_REFL]
  \\ Cases_on `FLOOKUP f r` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `FLOOKUP f r'` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `FLOOKUP refs r` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `FLOOKUP refs r'` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `x''` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `x'''` \\ full_simp_tac (srw_ss()) []
  \\ imp_res_tac v_inv_related
  \\ full_simp_tac std_ss [ref_edge_def]
  \\ full_simp_tac std_ss [gc_related_def,INJ_DEF,GSPECIFICATION]
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF] \\ srw_tac [] []
  \\ Cases_on `refs ' r` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `refs ' r'` \\ full_simp_tac (srw_ss()) []
  \\ res_tac \\ full_simp_tac std_ss [get_refs_def] \\ srw_tac [] []
  \\ full_simp_tac std_ss [MEM_FLAT,MEM_MAP] \\ srw_tac [] []
  \\ full_simp_tac std_ss [ref_edge_def,EVERY_MEM]
  \\ full_simp_tac std_ss [PULL_FORALL,AND_IMP_INTRO]
  \\ res_tac \\ CCONTR_TAC \\ full_simp_tac std_ss []
  \\ srw_tac [] [] \\ POP_ASSUM MP_TAC \\ simp_tac std_ss []
  \\ imp_res_tac MEM_EVERY2_IMP \\ fs []
  \\ fs [] \\ metis_tac []);

val reachable_refs_lemma = prove(
  ``gc_related g heap heap2 /\
    EVERY2 (\v x. v_inv v (x,f,heap)) stack roots /\
    (!n. reachable_refs stack refs n ==> bc_ref_inv n refs (f,heap,be)) /\
    (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM g) ==>
    (!n. reachable_refs stack refs n ==> n IN FDOM f /\ (f ' n) IN FDOM g)``,
  NTAC 3 strip_tac \\ full_simp_tac std_ss [reachable_refs_def,PULL_EXISTS]
  \\ `?xs1 xs2. stack = xs1 ++ x::xs2` by metis_tac [MEM_SPLIT]
  \\ full_simp_tac std_ss [] \\ imp_res_tac EVERY2_SPLIT_ALT
  \\ full_simp_tac std_ss [MEM,MEM_APPEND]
  \\ `EVERY (\n. f ' n IN FDOM g) (get_refs x)` by metis_tac [v_inv_related]
  \\ full_simp_tac std_ss [EVERY_MEM] \\ res_tac \\ full_simp_tac std_ss []
  \\ `n IN FDOM f` by ALL_TAC THEN1 (CCONTR_TAC
    \\ full_simp_tac (srw_ss()) [bc_ref_inv_def,FLOOKUP_DEF])
  \\ full_simp_tac std_ss []
  \\ `bc_ref_inv r refs (f,heap,be)` by metis_tac [RTC_REFL]
  \\ `(!m. RTC (ref_edge refs) r m ==> bc_ref_inv m refs (f,heap,be))` by ALL_TAC
  THEN1 metis_tac [] \\ imp_res_tac RTC_lemma);

val bc_stack_ref_inv_related = prove(
  ``gc_related g heap1 heap2 /\
    bc_stack_ref_inv stack refs (roots,heap1,be) /\
    (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM g) ==>
    bc_stack_ref_inv stack refs (ADDR_MAP (FAPPLY g) roots,heap2,be)``,
  rpt strip_tac \\ full_simp_tac std_ss [bc_stack_ref_inv_def]
  \\ qexists_tac `g f_o_f f` \\ rpt strip_tac
  THEN1 (full_simp_tac (srw_ss()) [INJ_DEF,gc_related_def,f_o_f_DEF])
  THEN1 (full_simp_tac (srw_ss()) [f_o_f_DEF,SUBSET_DEF])
  THEN1
   (full_simp_tac std_ss [ONCE_REWRITE_RULE [CONJ_COMM] EVERY2_EVERY,
      LENGTH_ADDR_MAP,EVERY_MEM,MEM_ZIP,PULL_EXISTS] \\ rpt strip_tac \\ res_tac
    \\ full_simp_tac std_ss [MEM_ZIP,PULL_EXISTS]
    \\ `MEM (EL n roots) roots` by (full_simp_tac std_ss [MEM_EL] \\ metis_tac [])
    \\ `(!ptr u. (EL n roots = Pointer ptr u) ==> ptr IN FDOM g)` by metis_tac []
    \\ imp_res_tac v_inv_related \\ imp_res_tac EL_ADDR_MAP
    \\ full_simp_tac std_ss [])
  \\ match_mp_tac bc_ref_inv_related \\ full_simp_tac std_ss []
  \\ metis_tac [reachable_refs_lemma]);

val full_gc_thm = store_thm("full_gc_thm",
  ``abs_ml_inv stack refs (roots,heap,be,a,sp) limit ==>
    ?roots2 heap2 a2.
      (full_gc (roots,heap,limit) = (roots2,heap2,a2,T)) /\
      abs_ml_inv stack refs
        (roots2,heap2 ++ heap_expand (limit - a2),be,a2,limit - a2) limit /\
      (heap_length heap2 = a2)``,
  simp_tac std_ss [abs_ml_inv_def,GSYM CONJ_ASSOC]
  \\ rpt strip_tac \\ imp_res_tac full_gc_related
  \\ NTAC 3 (POP_ASSUM (K ALL_TAC))
  \\ `heap_length heap2 = a2` by ALL_TAC
  THEN1 (imp_res_tac full_gc_LENGTH \\ full_simp_tac std_ss [] \\ metis_tac [])
  \\ `unused_space_inv a2 (limit - a2) (heap2 ++ heap_expand (limit - a2))` by
   (full_simp_tac std_ss [unused_space_inv_def] \\ rpt strip_tac
    \\ full_simp_tac std_ss [heap_expand_def]
    \\ metis_tac [heap_lookup_PREFIX])
  \\ full_simp_tac std_ss [] \\ simp_tac std_ss [CONJ_ASSOC] \\ strip_tac THEN1
   (qpat_assum `full_gc (roots,heap,limit) = xxx` (ASSUME_TAC o GSYM)
    \\ imp_res_tac full_gc_ok \\ NTAC 3 (POP_ASSUM (K ALL_TAC))
    \\ full_simp_tac std_ss [] \\ metis_tac [])
  \\ match_mp_tac (GEN_ALL bc_stack_ref_inv_related) \\ full_simp_tac std_ss []
  \\ qexists_tac `heap` \\ full_simp_tac std_ss []
  \\ rw [] \\ fs [] \\ res_tac \\ fs []);

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
  Induct \\ full_simp_tac (srw_ss()) [heap_length_def,heap_store_def,LET_DEF]
  THEN1 DECIDE_TAC \\ rpt strip_tac
  \\ `el_length h <> 0` by (Cases_on `h` \\ full_simp_tac std_ss [el_length_def])
  \\ `~(el_length h + SUM (MAP el_length xs) < el_length h)` by DECIDE_TAC
  \\ full_simp_tac std_ss []);

val heap_store_rel_def = Define `
  heap_store_rel heap heap2 <=>
    (!ptr. isSomeDataElement (heap_lookup ptr heap) ==>
           (heap_lookup ptr heap2 = heap_lookup ptr heap))`;

val isSomeDataElement_heap_lookup_lemma1 = prove(
  ``isSomeDataElement (heap_lookup n (Unused k :: xs)) <=>
    k < n /\ isSomeDataElement (heap_lookup (n-(k+1)) xs)``,
  srw_tac [] [heap_lookup_def,isSomeDataElement_def,el_length_def,NOT_LESS]
  THEN1 (DISJ1_TAC \\ DECIDE_TAC)
  \\ `k < n` by DECIDE_TAC \\ full_simp_tac std_ss []);

val isSomeDataElement_heap_lookup_lemma2 = prove(
  ``isSomeDataElement (heap_lookup n (heap_expand k ++ xs)) <=>
    k <= n /\ isSomeDataElement (heap_lookup (n-k) xs)``,
  srw_tac [] [heap_expand_def,isSomeDataElement_heap_lookup_lemma1]
  \\ imp_res_tac (DECIDE ``sp <> 0 ==> (sp - 1 + 1 = sp:num)``)
  \\ full_simp_tac std_ss []
  \\ Cases_on `isSomeDataElement (heap_lookup (n - k) xs)`
  \\ full_simp_tac std_ss [] \\ DECIDE_TAC);

val isSomeDataElement_heap_lookup_lemma3 = prove(
  ``n <> 0 ==>
    (isSomeDataElement (heap_lookup n (x::xs)) <=>
     el_length x <= n /\ isSomeDataElement (heap_lookup (n - el_length x) xs))``,
  srw_tac [] [heap_expand_def,heap_lookup_def,isSomeDataElement_def]
  \\ Cases_on`n < el_length x` THEN srw_tac[][]
  THEN1 (DISJ1_TAC \\ DECIDE_TAC)
  \\ `el_length x <= n` by DECIDE_TAC \\ full_simp_tac std_ss []);

val IMP_heap_store_unused = prove(
  ``unused_space_inv a sp (heap:('a,'b) heap_element list) /\
    el_length x <= sp ==>
    ?heap2. (heap_store_unused a sp x heap = (heap2,T)) /\
            unused_space_inv a (sp - el_length x) heap2 /\
            (heap_lookup (a + sp - el_length x) heap2 = SOME x) /\
            ~isSomeDataElement (heap_lookup (a + sp - el_length x) heap) /\
            (heap_length heap2 = heap_length heap) /\
            (~isForwardPointer x ==>
             (FILTER isForwardPointer heap2 = FILTER isForwardPointer heap)) /\
            (!xs l d.
               MEM (DataElement xs l d) heap2 <=>
                 (x = DataElement xs l d) \/
                 MEM (DataElement xs l d) heap) /\
            (isDataElement x ==>
             ({a | isSomeDataElement (heap_lookup a heap2)} =
               a + sp - el_length x
                 INSERT {a | isSomeDataElement (heap_lookup a heap)})) /\
            heap_store_rel heap heap2``,
  rpt strip_tac \\ asm_simp_tac std_ss [heap_store_unused_def,heap_store_rel_def]
  \\ `sp <> 0` by (Cases_on `x` \\ full_simp_tac std_ss [el_length_def] \\ DECIDE_TAC)
  \\ full_simp_tac std_ss [unused_space_inv_def]
  \\ imp_res_tac heap_lookup_SPLIT \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [heap_store_lemma]
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [heap_length_def,SUM_APPEND,el_length_def]
    \\ full_simp_tac std_ss [GSYM heap_length_def,heap_length_heap_expand]
    \\ DECIDE_TAC)
  \\ strip_tac THEN1
   (rpt strip_tac \\ full_simp_tac std_ss
      [heap_expand_def,APPEND,GSYM APPEND_ASSOC,heap_lookup_PREFIX])
  \\ strip_tac THEN1
   (full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ full_simp_tac std_ss [APPEND_ASSOC]
    \\ `heap_length ha + sp - el_length x =
        heap_length (ha ++ heap_expand (sp - el_length x))` by
     (full_simp_tac std_ss [heap_length_APPEND,heap_length_heap_expand] \\ DECIDE_TAC)
    \\ full_simp_tac std_ss [heap_lookup_PREFIX])
  \\ strip_tac THEN1
   (`~(heap_length ha + sp - el_length x < heap_length ha)` by DECIDE_TAC
    \\ imp_res_tac NOT_LESS_IMP_heap_lookup
    \\ full_simp_tac std_ss []
    \\ `heap_length ha + sp - el_length x - heap_length ha =
        sp - el_length x` by DECIDE_TAC \\ full_simp_tac std_ss []
    \\ simp_tac std_ss [heap_lookup_def]
    \\ srw_tac [] [isSomeDataElement_def,el_length_def]
    \\ reverse (full_simp_tac std_ss []) THEN1 (`F` by DECIDE_TAC)
    \\ Cases_on `x` \\ full_simp_tac std_ss [el_length_def]
    \\ `F` by DECIDE_TAC)
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [heap_length_APPEND,heap_length_heap_expand,
      heap_length_def,el_length_def] \\ DECIDE_TAC)
  \\ strip_tac THEN1
   (full_simp_tac std_ss [rich_listTheory.FILTER_APPEND,FILTER,isForwardPointer_def,APPEND_NIL]
    \\ srw_tac [] [heap_expand_def,isForwardPointer_def])
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [MEM_APPEND,MEM,heap_expand_def]
    \\ Cases_on `sp <= el_length x` \\ full_simp_tac (srw_ss()) []
    \\ metis_tac [])
  \\ strip_tac THEN1
   (rpt strip_tac \\ full_simp_tac (srw_ss()) [EXTENSION]
    \\ strip_tac \\ Q.ABBREV_TAC `y = x'` \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `y = heap_length ha + sp - el_length x`
    \\ full_simp_tac std_ss [] THEN1
     (once_rewrite_tac [GSYM APPEND_ASSOC] \\ simp_tac std_ss [APPEND]
      \\ `(heap_length ha + sp - el_length x) =
          heap_length (ha ++ heap_expand (sp - el_length x))` by
       (full_simp_tac std_ss [heap_length_APPEND,heap_length_heap_expand]
        \\ DECIDE_TAC)
      \\ full_simp_tac std_ss [heap_lookup_PREFIX]
      \\ full_simp_tac (srw_ss()) [isDataElement_def,isSomeDataElement_def])
    \\ Cases_on `y < heap_length ha`
    THEN1 (full_simp_tac std_ss [LESS_IMP_heap_lookup,GSYM APPEND_ASSOC])
    \\ imp_res_tac NOT_LESS_IMP_heap_lookup
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ full_simp_tac std_ss [isSomeDataElement_heap_lookup_lemma1,
         isSomeDataElement_heap_lookup_lemma2]
    \\ `0 < el_length x` by
         (Cases_on `x` \\ full_simp_tac std_ss [el_length_def] \\ DECIDE_TAC)
    \\ reverse (Cases_on `sp <= el_length x + (y - heap_length ha)`)
    \\ full_simp_tac std_ss []
    THEN1 (CCONTR_TAC \\ full_simp_tac std_ss [] \\ DECIDE_TAC)
    \\ `0 < y - heap_length ha` by DECIDE_TAC
    \\ full_simp_tac std_ss []
    \\ `y - heap_length ha - (sp - el_length x) <> 0` by DECIDE_TAC
    \\ full_simp_tac std_ss [APPEND,isSomeDataElement_heap_lookup_lemma3]
    \\ reverse (Cases_on `el_length x <= y - heap_length ha - (sp - el_length x)`)
    \\ full_simp_tac std_ss []
    THEN1 (CCONTR_TAC \\ full_simp_tac std_ss [] \\ DECIDE_TAC)
    \\ `sp < 1 + (y - heap_length ha)` by DECIDE_TAC
    \\ full_simp_tac std_ss [SUB_SUB]
    \\ imp_res_tac (DECIDE ``sp <> 0 ==> (sp - 1 + 1 = sp:num)``)
    \\ full_simp_tac std_ss []
    \\ imp_res_tac (DECIDE  ``n <= sp ==> (y - m + n - sp - n = y - m - sp:num)``)
    \\ full_simp_tac std_ss [])
  \\ rpt strip_tac
  \\ full_simp_tac std_ss [isSomeDataElement_def]
  \\ Cases_on `ptr < heap_length ha`
  THEN1 (imp_res_tac LESS_IMP_heap_lookup \\ full_simp_tac std_ss [GSYM APPEND_ASSOC])
  \\ imp_res_tac NOT_LESS_IMP_heap_lookup \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ POP_ASSUM (K ALL_TAC) \\ qpat_assum `xxx = SOME yyy` MP_TAC
  \\ simp_tac std_ss [Once heap_lookup_def] \\ srw_tac [] []
  \\ `~(ptr - heap_length ha < heap_length (heap_expand (sp - el_length x) ++ [x]))` by
   (full_simp_tac (srw_ss()) [heap_length_APPEND,heap_length_heap_expand,
      el_length_def,heap_length_def] \\ DECIDE_TAC)
  \\ imp_res_tac NOT_LESS_IMP_heap_lookup \\ POP_ASSUM (K ALL_TAC)
  \\ POP_ASSUM (fn th => once_rewrite_tac [th])
  \\ `heap_length (heap_expand (sp - el_length x) ++ [x]) = sp` by
   (full_simp_tac (srw_ss()) [heap_length_APPEND,heap_length_heap_expand,
      el_length_def,heap_length_def] \\ DECIDE_TAC)
  \\ `el_length (Unused (sp - 1)) = sp` by
   (full_simp_tac (srw_ss()) [heap_length_APPEND,heap_length_heap_expand,
      el_length_def,heap_length_def] \\ DECIDE_TAC)
  \\ full_simp_tac std_ss []);

val heap_store_rel_lemma = prove(
  ``heap_store_rel h1 h2 /\ (heap_lookup n h1 = SOME (DataElement ys l d)) ==>
    (heap_lookup n h2 = SOME (DataElement ys l d))``,
  simp_tac std_ss [heap_store_rel_def,isSomeDataElement_def] \\ metis_tac []);

(* cons *)

val v_inv_SUBMAP = prove(
  ``!w x.
      f SUBMAP f1 /\ heap_store_rel heap heap1 /\
      v_inv w (x,f,heap) ==>
      v_inv w (x,f1,heap1) ``,
  completeInduct_on `v_size w` \\ NTAC 3 strip_tac
  \\ full_simp_tac std_ss [PULL_FORALL] \\ Cases_on `w` THEN1
   (full_simp_tac std_ss [v_inv_def,Bignum_def] \\ srw_tac [] []
    \\ imp_res_tac heap_store_rel_lemma \\ full_simp_tac std_ss [])
  THEN1 (full_simp_tac (srw_ss()) [v_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ Cases_on `l = []` \\ full_simp_tac std_ss []
    \\ full_simp_tac (srw_ss()) [v_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ rpt strip_tac
    \\ full_simp_tac std_ss [EVERY2_EVERY,LENGTH_ADDR_MAP,EVERY_MEM,FORALL_PROD]
    \\ qpat_assum `LENGTH l = LENGTH xs` ASSUME_TAC
    \\ full_simp_tac (srw_ss()) [MEM_ZIP,LENGTH_ADDR_MAP,PULL_EXISTS]
    \\ imp_res_tac heap_store_rel_lemma \\ full_simp_tac (srw_ss()) []
    \\ full_simp_tac (srw_ss()) [MEM_ZIP,LENGTH_ADDR_MAP,PULL_EXISTS]
    \\ rpt strip_tac
    \\ Q.MATCH_ASSUM_RENAME_TAC `t < LENGTH xs` \\ res_tac
    \\ `MEM (EL t l) l` by (full_simp_tac std_ss [MEM_EL] \\ metis_tac [])
    \\ `v_size (EL t l) < v_size (Block n l)` by ALL_TAC THEN1
     (full_simp_tac std_ss [v_size_def]
      \\ imp_res_tac MEM_IMP_v_size \\ DECIDE_TAC) \\ res_tac)
  THEN1 (full_simp_tac std_ss [v_inv_def] \\ metis_tac [])
  THEN1 (full_simp_tac (srw_ss()) [v_inv_def,SUBMAP_DEF] \\ rw []));

val cons_thm = store_thm("cons_thm",
  ``abs_ml_inv (xs ++ stack) refs (roots,heap,be,a,sp) limit /\
    LENGTH xs < sp /\ xs <> [] ==>
    ?rs roots2 heap2.
      (roots = rs ++ roots2) /\ (LENGTH rs = LENGTH xs) /\
      (heap_store_unused a sp (BlockRep tag rs) heap = (heap2,T)) /\
      abs_ml_inv ((Block tag xs)::stack) refs
                 (Pointer (a + sp - el_length (BlockRep tag rs)) u::roots2,heap2,be,a,
                  sp-el_length (BlockRep tag rs)) limit``,
  simp_tac std_ss [abs_ml_inv_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [bc_stack_ref_inv_def,LIST_REL_def]
  \\ imp_res_tac EVERY2_APPEND_IMP \\ full_simp_tac std_ss []
  \\ Q.LIST_EXISTS_TAC [`ys1`,`ys2`] \\ full_simp_tac std_ss []
  \\ imp_res_tac EVERY2_LENGTH \\ full_simp_tac std_ss []
  \\ qpat_assum `unused_space_inv a sp heap` (fn th =>
    MATCH_MP (IMP_heap_store_unused |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> GEN_ALL) th
    |> ASSUME_TAC)
  \\ POP_ASSUM (MP_TAC o Q.SPEC `(BlockRep tag ys1)`) \\ match_mp_tac IMP_IMP
  \\ strip_tac THEN1 (full_simp_tac std_ss [BlockRep_def,el_length_def] \\ DECIDE_TAC)
  \\ strip_tac \\ full_simp_tac std_ss []
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [roots_ok_def,MEM,BlockRep_def]
    \\ reverse (rpt strip_tac \\ res_tac) THEN1 metis_tac [heap_store_rel_def]
    \\ full_simp_tac (srw_ss()) [el_length_def,isSomeDataElement_def])
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [roots_ok_def,MEM,BlockRep_def,heap_ok_def,
      isForwardPointer_def] \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ rpt strip_tac \\ metis_tac [heap_store_rel_def])
  \\ strip_tac THEN1 (full_simp_tac std_ss [el_length_def,BlockRep_def])
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ strip_tac THEN1
   (match_mp_tac INJ_SUBSET
    \\ FIRST_ASSUM (match_exists_tac o concl)
    \\ full_simp_tac (srw_ss()) [isDataElement_def,BlockRep_def])
  \\ rpt strip_tac THEN1
   (full_simp_tac (srw_ss()) [v_inv_def]
    \\ full_simp_tac std_ss [BlockRep_def,el_length_def]
    \\ qexists_tac `ys1` \\ full_simp_tac std_ss []
    \\ full_simp_tac std_ss [EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS]
    \\ `f SUBMAP f` by full_simp_tac std_ss [SUBMAP_REFL]
    \\ rpt strip_tac \\ res_tac \\ imp_res_tac v_inv_SUBMAP)
  THEN1
   (full_simp_tac std_ss [EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS]
    \\ `f SUBMAP f` by full_simp_tac std_ss [SUBMAP_REFL]
    \\ rpt strip_tac \\ res_tac \\ imp_res_tac v_inv_SUBMAP)
  \\ `reachable_refs (xs++stack) refs n` by ALL_TAC THEN1
   (POP_ASSUM MP_TAC \\ simp_tac std_ss [reachable_refs_def]
    \\ rpt strip_tac \\ full_simp_tac std_ss [MEM] THEN1
     (NTAC 2 (POP_ASSUM MP_TAC) \\ full_simp_tac std_ss []
      \\ full_simp_tac std_ss [get_refs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]
      \\ full_simp_tac std_ss [MEM_APPEND] \\ metis_tac [])
    \\ full_simp_tac std_ss [MEM_APPEND] \\ metis_tac [])
  \\ res_tac \\ POP_ASSUM MP_TAC \\ simp_tac std_ss [bc_ref_inv_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [RefBlock_def]
  \\ Cases_on `FLOOKUP f n` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `FLOOKUP refs n` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `x'` \\ full_simp_tac (srw_ss()) []
  THEN1 (
    imp_res_tac heap_store_rel_lemma \\ full_simp_tac (srw_ss()) []
    \\ qpat_assum `EVERY2 PP zs l` MP_TAC
    \\ match_mp_tac EVERY2_IMP_EVERY2 \\ full_simp_tac (srw_ss()) []
    \\ rpt strip_tac \\ res_tac \\ imp_res_tac v_inv_SUBMAP
    \\ `f SUBMAP f` by full_simp_tac std_ss [SUBMAP_REFL] \\ res_tac)
  \\ fs[Bytes_def,LET_THM] >> imp_res_tac heap_store_rel_lemma)

val cons_thm_EMPTY = store_thm("cons_thm_EMPTY",
  ``abs_ml_inv stack refs (roots,heap:'a ml_heap,be,a,sp) limit /\
    tag < 2 ** 61 ==>
    abs_ml_inv ((Block tag [])::stack) refs
                (Data (Word (BlockNil tag))::roots,heap,be,a,sp) limit``,
  simp_tac std_ss [abs_ml_inv_def] \\ rpt strip_tac
  \\ full_simp_tac std_ss [bc_stack_ref_inv_def,LIST_REL_def]
  \\ full_simp_tac (srw_ss()) [roots_ok_def,MEM]
  THEN1 (rw [] \\ fs [] \\ res_tac \\ fs [])
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ full_simp_tac (srw_ss()) [v_inv_def]
  \\ rpt strip_tac \\ `reachable_refs stack refs n` by ALL_TAC \\ res_tac
  \\ full_simp_tac std_ss [reachable_refs_def]
  \\ Cases_on `x = Block tag []` \\ full_simp_tac std_ss []
  \\ full_simp_tac (srw_ss()) [get_refs_def] \\ metis_tac []);


(* update ref *)

val ref_edge_ValueArray = prove(
  ``ref_edge (refs |+ (ptr,ValueArray xs)) x y =
    if x = ptr then MEM y (get_refs (Block ARB xs)) else ref_edge refs x y``,
  simp_tac std_ss [FUN_EQ_THM,ref_edge_def] \\ rpt strip_tac
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
  \\ Cases_on `x = ptr` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `ptr IN FDOM refs` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `refs ' ptr` \\ full_simp_tac (srw_ss()) []);

val reachable_refs_UPDATE = prove(
  ``reachable_refs (xs ++ RefPtr ptr::stack) (refs |+ (ptr,ValueArray xs)) n ==>
    reachable_refs (xs ++ RefPtr ptr::stack) refs n``,
  full_simp_tac std_ss [reachable_refs_def] \\ rpt strip_tac
  \\ Cases_on `?m. MEM m (get_refs (Block ARB xs)) /\
        RTC (ref_edge refs) m n` THEN1
   (full_simp_tac std_ss [get_refs_def,MEM_FLAT,MEM_MAP]
    \\ srw_tac [] [] \\ metis_tac [])
  \\ full_simp_tac std_ss [METIS_PROVE [] ``~b \/ c <=> b ==> c``]
  \\ full_simp_tac std_ss [] \\ Q.LIST_EXISTS_TAC [`x`,`r`]
  \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [RTC_eq_NRC]
  \\ Q.ABBREV_TAC `k = n'` \\ POP_ASSUM (K ALL_TAC) \\ qexists_tac `k`
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Q.SPEC_TAC (`r`,`r`) \\ Induct_on `k`
  \\ full_simp_tac std_ss [NRC]
  \\ rpt strip_tac \\ full_simp_tac std_ss [] \\ res_tac
  \\ qexists_tac `z` \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [ref_edge_ValueArray]
  \\ reverse (Cases_on `r = ptr`)
  \\ full_simp_tac std_ss [] \\ res_tac);

val reachable_refs_UPDATE1 = prove(
  ``reachable_refs (xs ++ RefPtr ptr::stack) (refs |+ (ptr,ValueArray xs1)) n ==>
    (!v. MEM v xs1 ==> ~MEM v xs ==> ?xs2. (FLOOKUP refs ptr = SOME (ValueArray xs2)) /\ MEM v xs2) ==>
    reachable_refs (xs ++ RefPtr ptr::stack) refs n``,
  full_simp_tac std_ss [reachable_refs_def] \\ rpt strip_tac
  \\ pop_assum mp_tac \\ last_x_assum mp_tac \\ last_x_assum mp_tac
  \\ map_every qid_spec_tac[`stack`,`xs`,`x`]
  \\ pop_assum mp_tac
  \\ map_every qid_spec_tac[`n`,`r`] >>
  ho_match_mp_tac RTC_INDUCT >>
  conj_tac >- ( simp[] >> rw[] >> metis_tac[RTC_REFL] ) >>
  simp[ref_edge_ValueArray] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[get_refs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >- (
    gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    BasicProvers.VAR_EQ_TAC >>
    first_assum(qspecl_then[`a`,`xs1`]mp_tac) >>
    first_x_assum(qspecl_then[`a`,`xs`]mp_tac) >>
    simp[] >> strip_tac >>
    disch_then(qspec_then`[]`mp_tac) >> simp[] >>
    strip_tac >- (
      disch_then kall_tac >>
      disch_then(qspec_then`x'`mp_tac) >>
      simp[] >>
      Cases_on`MEM x' xs`>-metis_tac[]>>simp[]>>strip_tac>>
      qexists_tac`RefPtr ptr`>>simp[get_refs_def]>>
      simp[Once RTC_CASES1]>>simp[ref_edge_def,get_refs_def]>>
      simp[MEM_MAP,MEM_FLAT,PULL_EXISTS]>>metis_tac[]) >>
    BasicProvers.VAR_EQ_TAC >>
    metis_tac[]) >>
  strip_tac >>
  rpt gen_tac >> strip_tac >>
  match_mp_tac (METIS_PROVE[]``(P ==> (Q ==> R)) ==> (Q ==> P ==> R)``) >>
  strip_tac >>
  first_x_assum(qspecl_then[`RefPtr r'`,`xs`,`[RefPtr r']`]mp_tac) >>
  simp[get_refs_def] >>
  strip_tac >- metis_tac[] >- metis_tac[] >>
  BasicProvers.VAR_EQ_TAC >> fs[get_refs_def] >>
  rw[] >> metis_tac[RTC_CASES1]);

val isRefBlock_def = Define `
  isRefBlock x = ?p. x = RefBlock p`;

val RefBlock_inv_def = Define `
  RefBlock_inv heap heap2 <=>
    (!n x. (heap_lookup n heap = SOME x) /\ ~(isRefBlock x) ==>
           (heap_lookup n heap2 = SOME x)) /\
    (!n x. (heap_lookup n heap2 = SOME x) /\ ~(isRefBlock x) ==>
           (heap_lookup n heap = SOME x))`;

val heap_store_RefBlock_thm = prove(
  ``!ha. (LENGTH x = LENGTH y) ==>
         (heap_store (heap_length ha) [RefBlock x] (ha ++ RefBlock y::hb) =
           (ha ++ RefBlock x::hb,T))``,
  Induct \\ full_simp_tac (srw_ss()) [heap_store_def,heap_length_def]
  THEN1 full_simp_tac std_ss [RefBlock_def,el_length_def] \\ strip_tac
  \\ rpt strip_tac \\ full_simp_tac std_ss []
  \\ `~(el_length h + SUM (MAP el_length ha) < el_length h) /\ el_length h <> 0` by
       (Cases_on `h` \\ full_simp_tac std_ss [el_length_def] \\ DECIDE_TAC)
  \\ full_simp_tac std_ss [LET_DEF]);

val heap_lookup_RefBlock_lemma = prove(
  ``(heap_lookup n (ha ++ RefBlock y::hb) = SOME x) =
      if n < heap_length ha then
        (heap_lookup n ha = SOME x)
      else if n = heap_length ha then
        (x = RefBlock y)
      else if heap_length ha + (LENGTH y + 1) <= n then
        (heap_lookup (n - heap_length ha - (LENGTH y + 1)) hb = SOME x)
      else F``,
  Cases_on `n < heap_length ha` \\ full_simp_tac std_ss [LESS_IMP_heap_lookup]
  \\ full_simp_tac std_ss [NOT_LESS_IMP_heap_lookup]
  \\ full_simp_tac std_ss [heap_lookup_def]
  \\ Cases_on `n <= heap_length ha` \\ full_simp_tac std_ss []
  THEN1 (`heap_length ha = n` by DECIDE_TAC \\ full_simp_tac std_ss [] \\ metis_tac [])
  \\ `heap_length ha <> n` by DECIDE_TAC \\ full_simp_tac std_ss []
  \\ `0 < el_length (RefBlock y)` by full_simp_tac std_ss [el_length_def,RefBlock_def]
  \\ full_simp_tac std_ss [] \\ srw_tac [] []
  THEN1 DECIDE_TAC
  \\ full_simp_tac std_ss [el_length_def,RefBlock_def,NOT_LESS]
  \\ DISJ1_TAC \\ DECIDE_TAC);

val heap_store_RefBlock = prove(
  ``(LENGTH y = LENGTH h) /\
    (heap_lookup n heap = SOME (RefBlock y)) ==>
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
  rpt strip_tac \\ imp_res_tac heap_lookup_SPLIT
  \\ full_simp_tac std_ss [heap_store_RefBlock_thm]
  \\ strip_tac THEN1
   (full_simp_tac std_ss [RefBlock_inv_def]
    \\ full_simp_tac std_ss [heap_lookup_RefBlock_lemma]
    \\ full_simp_tac std_ss [isRefBlock_def] \\ metis_tac [])
  \\ strip_tac THEN1 (full_simp_tac std_ss [heap_lookup_PREFIX])
  \\ strip_tac THEN1 (full_simp_tac (srw_ss())
       [heap_length_APPEND,heap_length_def,RefBlock_def,el_length_def])
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [rich_listTheory.FILTER_APPEND,FILTER,isForwardPointer_def,RefBlock_def])
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [MEM,MEM_APPEND,RefBlock_def] \\ metis_tac [])
  \\ strip_tac THEN1
   (full_simp_tac std_ss [isSomeDataElement_def,heap_lookup_RefBlock_lemma]
    \\ full_simp_tac std_ss [RefBlock_def] \\ metis_tac [])
  \\ full_simp_tac std_ss [isSomeDataElement_def,heap_lookup_RefBlock_lemma]
  \\ metis_tac []);

val NOT_isRefBlock = prove(
  ``~(isRefBlock (Bignum x)) /\
    ~(isRefBlock (DataElement xs (LENGTH xs) (BlockTag n,[])))``,
  simp_tac (srw_ss()) [isRefBlock_def,RefBlock_def,Bignum_def]);

val v_inv_Ref = prove(
  ``RefBlock_inv heap heap2 ==>
    !x h f. (v_inv x (h,f,heap2) = v_inv x (h,f,heap))``,
  strip_tac \\ completeInduct_on `v_size x` \\ NTAC 3 strip_tac
  \\ full_simp_tac std_ss [PULL_FORALL] \\ Cases_on `x` THEN1
   (full_simp_tac std_ss [v_inv_def] \\ srw_tac [] []
    \\ rpt strip_tac \\ full_simp_tac std_ss []
    \\ full_simp_tac std_ss [RefBlock_inv_def]
    \\ metis_tac [NOT_isRefBlock])
  THEN1 (full_simp_tac (srw_ss()) [v_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ Cases_on `l = []` \\ full_simp_tac std_ss []
    \\ full_simp_tac (srw_ss()) [v_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ rpt strip_tac
    \\ full_simp_tac std_ss [EVERY2_EVERY,LENGTH_ADDR_MAP,EVERY_MEM,FORALL_PROD]
    \\ rpt strip_tac \\ EQ_TAC \\ rpt strip_tac
    THEN1
     (qpat_assum `LENGTH l = LENGTH xs` ASSUME_TAC
      \\ full_simp_tac (srw_ss()) [MEM_ZIP,LENGTH_ADDR_MAP,PULL_EXISTS]
      \\ `heap_lookup ptr heap =
           SOME (DataElement xs (LENGTH xs) (BlockTag n,[]))` by
              metis_tac [RefBlock_inv_def,NOT_isRefBlock]
      \\ full_simp_tac (srw_ss()) [MEM_ZIP]
      \\ rpt strip_tac
      \\ Q.MATCH_ASSUM_RENAME_TAC `t < LENGTH xs` \\ res_tac
      \\ `MEM (EL t l) l` by (full_simp_tac std_ss [MEM_EL] \\ metis_tac [])
      \\ `v_size (EL t l) < v_size (Block n l)` by ALL_TAC THEN1
       (full_simp_tac std_ss [v_size_def]
        \\ imp_res_tac MEM_IMP_v_size \\ DECIDE_TAC) \\ res_tac
      \\ full_simp_tac std_ss [])
    THEN1
     (qpat_assum `LENGTH l = LENGTH xs` ASSUME_TAC
      \\ full_simp_tac (srw_ss()) [MEM_ZIP,LENGTH_ADDR_MAP,PULL_EXISTS]
      \\ `heap_lookup ptr heap2 =
           SOME (DataElement xs (LENGTH xs) (BlockTag n,[]))` by
              metis_tac [RefBlock_inv_def,NOT_isRefBlock]
      \\ full_simp_tac (srw_ss()) [MEM_ZIP]
      \\ rpt strip_tac
      \\ Q.MATCH_ASSUM_RENAME_TAC `t < LENGTH xs` \\ res_tac
      \\ `MEM (EL t l) l` by (full_simp_tac std_ss [MEM_EL] \\ metis_tac [])
      \\ `v_size (EL t l) < v_size (Block n l)` by ALL_TAC THEN1
       (full_simp_tac std_ss [v_size_def]
        \\ imp_res_tac MEM_IMP_v_size \\ DECIDE_TAC) \\ res_tac
      \\ full_simp_tac std_ss []))
  THEN1 (full_simp_tac std_ss [v_inv_def])
  THEN1 (full_simp_tac (srw_ss()) [v_inv_def,SUBMAP_DEF]));

val update_ref_thm = store_thm("update_ref_thm",
  ``abs_ml_inv (xs ++ (RefPtr ptr)::stack) refs (roots,heap,be,a,sp) limit /\
    (FLOOKUP refs ptr = SOME (ValueArray xs1)) /\ (LENGTH xs = LENGTH xs1) ==>
    ?p rs roots2 heap2 u.
      (roots = rs ++ Pointer p u :: roots2) /\
      (heap_store p [RefBlock rs] heap = (heap2,T)) /\
      abs_ml_inv (xs ++ (RefPtr ptr)::stack) (refs |+ (ptr,ValueArray xs))
        (roots,heap2,be,a,sp) limit``,
  simp_tac std_ss [abs_ml_inv_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [bc_stack_ref_inv_def]
  \\ imp_res_tac EVERY2_APPEND_CONS
  \\ full_simp_tac std_ss [v_inv_def]
  \\ Q.LIST_EXISTS_TAC [`f ' ptr`,`t1`,`t2`]
  \\ full_simp_tac std_ss []
  \\ `reachable_refs (xs ++ RefPtr ptr::stack) refs ptr` by ALL_TAC THEN1
   (full_simp_tac std_ss [reachable_refs_def] \\ qexists_tac `RefPtr ptr`
    \\ full_simp_tac (srw_ss()) [get_refs_def])
  \\ res_tac \\ POP_ASSUM MP_TAC \\ simp_tac std_ss [Once bc_ref_inv_def]
  \\ Cases_on `FLOOKUP refs ptr` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `FLOOKUP f ptr` \\ full_simp_tac (srw_ss()) []
  \\ rpt strip_tac
  \\ imp_res_tac heap_store_RefBlock \\ POP_ASSUM (MP_TAC o Q.SPEC `t1`)
  \\ full_simp_tac std_ss []
  \\ imp_res_tac EVERY2_IMP_LENGTH
  \\ full_simp_tac std_ss []
  \\ strip_tac \\ full_simp_tac std_ss []
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF]
  \\ strip_tac THEN1
   (full_simp_tac std_ss [roots_ok_def] \\ fs [] \\ metis_tac [])
  \\ strip_tac THEN1
   (full_simp_tac std_ss [heap_ok_def] \\ rpt strip_tac \\ res_tac
    \\ full_simp_tac (srw_ss()) [RefBlock_def] \\ srw_tac [] []
    \\ Q.ABBREV_TAC `p1 = ptr'` \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `p1 = f ' ptr` \\ full_simp_tac std_ss []
    THEN1 (EVAL_TAC \\ simp_tac std_ss [])
    \\ full_simp_tac std_ss [roots_ok_def,MEM_APPEND]
    \\ fs [] \\ metis_tac [])
  \\ strip_tac THEN1
   (full_simp_tac std_ss [unused_space_inv_def] \\ rpt strip_tac
    \\ res_tac \\ Cases_on `a = f ' ptr` \\ full_simp_tac (srw_ss()) []
    THEN1 full_simp_tac (srw_ss()) [RefBlock_def]
    \\ full_simp_tac std_ss [RefBlock_inv_def]
    \\ res_tac \\ full_simp_tac (srw_ss()) [isRefBlock_def,RefBlock_def])
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss []
  \\ MP_TAC v_inv_Ref
  \\ full_simp_tac std_ss [] \\ rpt strip_tac
  THEN1 (full_simp_tac (srw_ss()) [SUBSET_DEF])
  \\ `reachable_refs (xs ++ RefPtr ptr::stack) refs n` by ALL_TAC
  THEN1 imp_res_tac reachable_refs_UPDATE
  \\ Cases_on `n = ptr` \\ full_simp_tac (srw_ss()) [bc_ref_inv_def] THEN1
   (srw_tac [] [] \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,RefBlock_def]
    \\ imp_res_tac EVERY2_SWAP \\ full_simp_tac std_ss []) \\ res_tac
  \\ Cases_on `FLOOKUP f n` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `FLOOKUP refs n` \\ full_simp_tac (srw_ss()) []
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,FAPPLY_FUPDATE_THM] \\ rw []
  \\ Cases_on `refs ' n` \\ full_simp_tac (srw_ss()) []
  \\ full_simp_tac (srw_ss()) [INJ_DEF] \\ metis_tac [])

val heap_deref_def = Define `
  (heap_deref a heap =
    case heap_lookup a heap of
    | SOME (DataElement xs l (RefTag,[])) => SOME xs
    | _ => NONE)`;

val update_ref_thm1 = store_thm("update_ref_thm1",
  ``abs_ml_inv (xs ++ RefPtr ptr::stack) refs (roots,heap,be,a,sp) limit /\
    (FLOOKUP refs ptr = SOME (ValueArray xs1)) /\ i < LENGTH xs1 /\ 0 < LENGTH xs
    ==>
    ?p rs roots2 vs1 heap2 u.
      (roots = rs ++ Pointer p u :: roots2) /\ (LENGTH rs = LENGTH xs) /\
      (heap_deref p heap = SOME vs1) /\
      (heap_store p [RefBlock (LUPDATE (HD rs) i vs1)] heap = (heap2,T)) /\
      abs_ml_inv (xs ++ (RefPtr ptr)::stack) (refs |+ (ptr,ValueArray (LUPDATE (HD xs) i xs1)))
        (roots,heap2,be,a,sp) limit``,
  simp_tac std_ss [abs_ml_inv_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [bc_stack_ref_inv_def]
  \\ imp_res_tac EVERY2_APPEND_CONS
  \\ full_simp_tac std_ss [v_inv_def]
  \\ Q.LIST_EXISTS_TAC [`f ' ptr`,`t1`,`t2`]
  \\ full_simp_tac std_ss []
  \\ `reachable_refs (xs ++ RefPtr ptr::stack) refs ptr` by ALL_TAC THEN1
   (full_simp_tac std_ss [reachable_refs_def] \\ qexists_tac `RefPtr ptr`
    \\ full_simp_tac (srw_ss()) [get_refs_def])
  \\ res_tac \\ POP_ASSUM MP_TAC \\ simp_tac std_ss [Once bc_ref_inv_def]
  \\ Cases_on `FLOOKUP refs ptr` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `FLOOKUP f ptr` \\ full_simp_tac (srw_ss()) []
  \\ rpt strip_tac
  \\ `heap_deref (f ' ptr) heap = SOME zs` by (
       fs[heap_deref_def,RefBlock_def,FLOOKUP_DEF] )
  \\ imp_res_tac heap_store_RefBlock
  \\ POP_ASSUM (MP_TAC o Q.SPEC `LUPDATE (HD t1) i zs`)
  \\ full_simp_tac std_ss [] \\ simp[LENGTH_LUPDATE]
  \\ strip_tac \\ full_simp_tac std_ss []
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF]
  \\ strip_tac THEN1
   (full_simp_tac std_ss [roots_ok_def] \\ fs [] \\ metis_tac [])
  \\ strip_tac THEN1
   (full_simp_tac std_ss [heap_ok_def] \\ rpt strip_tac \\ res_tac
    \\ full_simp_tac (srw_ss()) [RefBlock_def] \\ srw_tac [] []
    \\ Q.ABBREV_TAC `p1 = ptr'` \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `p1 = f ' ptr` \\ full_simp_tac std_ss []
    THEN1 (EVAL_TAC \\ simp_tac std_ss [])
    \\ full_simp_tac std_ss [roots_ok_def,MEM_APPEND,MEM]
    \\ Cases_on`t1`>>fs[]
    \\ imp_res_tac MEM_LUPDATE_E >> fs[]
    \\ rfs[heap_deref_def] >> metis_tac[heap_lookup_MEM])
  \\ strip_tac THEN1
   (full_simp_tac std_ss [unused_space_inv_def] \\ rpt strip_tac
    \\ res_tac \\ Cases_on `a = f ' ptr` \\ full_simp_tac (srw_ss()) []
    THEN1 full_simp_tac (srw_ss()) [RefBlock_def]
    \\ full_simp_tac std_ss [RefBlock_inv_def]
    \\ res_tac \\ full_simp_tac (srw_ss()) [isRefBlock_def,RefBlock_def])
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss []
  \\ MP_TAC v_inv_Ref
  \\ full_simp_tac std_ss [] \\ rpt strip_tac
  THEN1 (full_simp_tac (srw_ss()) [SUBSET_DEF])
  \\ Cases_on `n = ptr` THEN1 (
    full_simp_tac (srw_ss()) [bc_ref_inv_def]
    \\ srw_tac [] [] \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,RefBlock_def]
    \\ imp_res_tac EVERY2_SWAP \\ full_simp_tac std_ss []
    \\ match_mp_tac EVERY2_LUPDATE_same
    \\ Cases_on`t1`>>fs[])
  \\ `reachable_refs (xs ++ RefPtr ptr::stack) refs n` by ALL_TAC
  THEN1 (
    match_mp_tac (GEN_ALL (MP_CANON reachable_refs_UPDATE1)) >>
    qexists_tac`LUPDATE (HD xs) i xs1` >> rw[] >>
    Cases_on`xs`>>fs[]>>
    imp_res_tac MEM_LUPDATE_E >> fs[]>>
    simp[FLOOKUP_DEF] ) >>
  full_simp_tac (srw_ss()) [bc_ref_inv_def]
  \\ res_tac
  \\ Cases_on `FLOOKUP f n` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `FLOOKUP refs n` \\ full_simp_tac (srw_ss()) []
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,FAPPLY_FUPDATE_THM] \\ rw []
  \\ Cases_on `refs ' n` \\ full_simp_tac (srw_ss()) []
  \\ full_simp_tac (srw_ss()) [INJ_DEF] \\ metis_tac [])

(* new ref *)

val new_ref_thm = store_thm("new_ref_thm",
  ``abs_ml_inv (xs ++ stack) refs (roots,heap,be,a,sp) limit /\
    ~(ptr IN FDOM refs) /\ LENGTH xs + 1 <= sp ==>
    ?p rs roots2 heap2.
      (roots = rs ++ roots2) /\
      (heap_store_unused a sp (RefBlock rs) heap = (heap2,T)) /\
      abs_ml_inv (xs ++ (RefPtr ptr)::stack) (refs |+ (ptr,ValueArray xs))
                 (rs ++ Pointer (a+sp-(LENGTH xs + 1)) u::roots2,heap2,be,a,
                  sp - (LENGTH xs + 1)) limit``,
  simp_tac std_ss [abs_ml_inv_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [bc_stack_ref_inv_def]
  \\ imp_res_tac EVERY2_APPEND_IMP_APPEND
  \\ full_simp_tac (srw_ss()) []
  \\ Q.LIST_EXISTS_TAC [`ys1`,`ys2`] \\ full_simp_tac std_ss []
  \\ imp_res_tac EVERY2_IMP_LENGTH
  \\ `el_length (RefBlock ys1) <= sp` by ALL_TAC
  THEN1 (full_simp_tac std_ss [el_length_def,RefBlock_def])
  \\ qpat_assum `unused_space_inv a sp heap` (fn th =>
    MATCH_MP (IMP_heap_store_unused
    |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> GEN_ALL) th
    |> ASSUME_TAC)
  \\ POP_ASSUM (MP_TAC o Q.SPEC `RefBlock ys1`) \\ match_mp_tac IMP_IMP
  \\ strip_tac THEN1 full_simp_tac std_ss [RefBlock_def,el_length_def]
  \\ strip_tac \\ full_simp_tac std_ss []
  \\ `unused_space_inv a (sp - (LENGTH ys1 + 1)) heap2` by ALL_TAC
  THEN1 full_simp_tac std_ss [RefBlock_def,el_length_def]
  \\ full_simp_tac std_ss [] \\ strip_tac THEN1
   (full_simp_tac std_ss [roots_ok_def,MEM,heap_store_rel_def] \\ rpt strip_tac
    \\ full_simp_tac (srw_ss()) [RefBlock_def,el_length_def]
    \\ full_simp_tac (srw_ss()) [isSomeDataElement_def]
    \\ fs [] \\ metis_tac [])
  \\ strip_tac THEN1
   (full_simp_tac std_ss [heap_ok_def,RefBlock_def,isForwardPointer_def]
    \\ once_rewrite_tac [EQ_SYM_EQ] \\ rpt strip_tac THEN1
     (POP_ASSUM MP_TAC \\ full_simp_tac (srw_ss()) []
      \\ once_rewrite_tac [EQ_SYM_EQ] \\ rpt strip_tac
      \\ full_simp_tac (srw_ss()) [roots_ok_def,MEM]
      \\ metis_tac [heap_store_rel_def])
    \\ res_tac \\ full_simp_tac std_ss [heap_store_rel_def])
  \\ `~(ptr IN FDOM f)` by (full_simp_tac (srw_ss()) [SUBSET_DEF] \\ metis_tac [])
  \\ qexists_tac `f |+ (ptr,a+sp-(LENGTH ys1 + 1))`
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [FDOM_FUPDATE]
    \\ `(FAPPLY (f |+ (ptr,a + sp - (LENGTH ys1 + 1)))) =
          (ptr =+ (a+sp-(LENGTH ys1 + 1))) (FAPPLY f)` by
     (full_simp_tac std_ss [FUN_EQ_THM,FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM]
      \\ metis_tac []) \\ full_simp_tac std_ss []
    \\ match_mp_tac (METIS_PROVE [] ``!y. (x = y) /\ f y ==> f x``)
    \\ qexists_tac `(a + sp - (LENGTH ys1 + 1)) INSERT
         {a | isSomeDataElement (heap_lookup a heap)}`
    \\ strip_tac
    THEN1 (full_simp_tac (srw_ss()) [RefBlock_def,isDataElement_def,el_length_def])
    \\ match_mp_tac INJ_UPDATE \\ full_simp_tac std_ss []
    \\ full_simp_tac (srw_ss()) []
    \\ full_simp_tac std_ss [RefBlock_def,el_length_def])
  \\ strip_tac THEN1
     (full_simp_tac (srw_ss()) [SUBSET_DEF,FDOM_FUPDATE] \\ metis_tac [])
  \\ Q.ABBREV_TAC `f1 = f |+ (ptr,a + sp - (LENGTH ys1 + 1))`
  \\ `f SUBMAP f1` by ALL_TAC THEN1
   (Q.UNABBREV_TAC `f1` \\ full_simp_tac (srw_ss()) [SUBMAP_DEF,FAPPLY_FUPDATE_THM]
    \\ metis_tac [])
  \\ strip_tac THEN1
   (match_mp_tac EVERY2_IMP_APPEND
    \\ full_simp_tac std_ss [LIST_REL_def]
    \\ match_mp_tac (METIS_PROVE [] ``p2 /\ (p1 /\ p3) ==> p1 /\ p2 /\ p3``)
    \\ strip_tac THEN1 (UNABBREV_ALL_TAC \\ fs [v_inv_def])
    \\ full_simp_tac (srw_ss()) [v_inv_def,FAPPLY_FUPDATE_THM]
    \\ full_simp_tac std_ss [EVERY2_EQ_EL]
    \\ imp_res_tac EVERY2_IMP_LENGTH
    \\ metis_tac [v_inv_SUBMAP])
  \\ rpt strip_tac
  \\ Cases_on `n = ptr` THEN1
   (Q.UNABBREV_TAC `f1` \\ asm_simp_tac (srw_ss()) [bc_ref_inv_def,FDOM_FUPDATE,
      FAPPLY_FUPDATE_THM] \\ full_simp_tac std_ss [el_length_def,RefBlock_def]
    \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,EVERY2_EQ_EL]
    \\ rpt strip_tac
    \\ match_mp_tac v_inv_SUBMAP \\ full_simp_tac (srw_ss()) [])
  \\ `reachable_refs (xs ++ RefPtr ptr::stack) refs n` by ALL_TAC
  THEN1 imp_res_tac reachable_refs_UPDATE
  \\ qpat_assum `reachable_refs (xs ++ RefPtr ptr::stack)
        (refs |+ (ptr,x)) n` (K ALL_TAC)
  \\ `reachable_refs (xs ++ stack) refs n` by ALL_TAC THEN1
    (full_simp_tac std_ss [reachable_refs_def]
     \\ reverse (Cases_on `x = RefPtr ptr`)
     THEN1 (full_simp_tac std_ss [MEM,MEM_APPEND] \\ metis_tac [])
     \\ full_simp_tac std_ss [get_refs_def,MEM]
     \\ srw_tac [] []
     \\ imp_res_tac RTC_NRC
     \\ Cases_on `n'` \\ full_simp_tac std_ss [NRC]
     \\ full_simp_tac std_ss [ref_edge_def,FLOOKUP_DEF]
     \\ rev_full_simp_tac std_ss [])
  \\ res_tac \\ Q.UNABBREV_TAC `f1` \\ full_simp_tac std_ss [bc_ref_inv_def]
  \\ Cases_on `FLOOKUP f n` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `FLOOKUP refs n` \\ full_simp_tac (srw_ss()) []
  \\ full_simp_tac (srw_ss()) [FDOM_FUPDATE,FAPPLY_FUPDATE_THM,FLOOKUP_DEF]
  \\ reverse (Cases_on `x'`) \\ full_simp_tac (srw_ss()) []
  THEN1 (
    fs[Bytes_def,LET_THM] >>
    imp_res_tac heap_store_rel_lemma )
  \\ `isSomeDataElement (heap_lookup (f ' n) heap)` by
    (full_simp_tac std_ss [RefBlock_def] \\ EVAL_TAC
     \\ simp_tac (srw_ss()) [] \\ NO_TAC)
  \\ res_tac \\ full_simp_tac std_ss [] \\ simp_tac (srw_ss()) [RefBlock_def]
  \\ qpat_assum `n IN FDOM f` ASSUME_TAC
  \\ qpat_assum `n IN FDOM refs` ASSUME_TAC
  \\ qpat_assum `refs ' n = ValueArray l` ASSUME_TAC
  \\ full_simp_tac (srw_ss()) []
  \\ srw_tac [] [] \\ full_simp_tac std_ss [RefBlock_def]
  \\ imp_res_tac heap_store_rel_lemma
  \\ res_tac \\ full_simp_tac (srw_ss()) []
  \\ qpat_assum `EVERY2 PPP zs l` MP_TAC
  \\ match_mp_tac EVERY2_IMP_EVERY2
  \\ full_simp_tac std_ss [] \\ simp_tac (srw_ss()) []
  \\ rpt strip_tac
  \\ match_mp_tac v_inv_SUBMAP
  \\ full_simp_tac (srw_ss()) []);

(* deref *)

val heap_el_def = Define `
  (heap_el (Pointer a u) n heap =
    case heap_lookup a heap of
    | SOME (DataElement xs l d) =>
        if n < LENGTH xs then (EL n xs,T) else (ARB,F)
    | _ => (ARB,F)) /\
  (heap_el _ _ _ = (ARB,F))`;

val deref_thm = store_thm("deref_thm",
  ``abs_ml_inv (RefPtr ptr::stack) refs (roots,heap,be,a,sp) limit ==>
    ?r roots2.
      (roots = r::roots2) /\ ptr IN FDOM refs /\
      case refs ' ptr of
      | ByteArray _ => T
      | ValueArray ts =>
      !n. n < LENGTH ts ==>
          ?y. (heap_el r n heap = (y,T)) /\
                abs_ml_inv (EL n ts::RefPtr ptr::stack) refs
                  (y::roots,heap,be,a,sp) limit``,
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
  \\ rpt strip_tac \\ Cases_on `roots` \\ full_simp_tac (srw_ss()) [LIST_REL_def]
  \\ full_simp_tac std_ss [v_inv_def]
  \\ `reachable_refs (RefPtr ptr::stack) refs ptr` by ALL_TAC THEN1
   (full_simp_tac std_ss [reachable_refs_def,MEM] \\ qexists_tac `RefPtr ptr`
    \\ asm_simp_tac (srw_ss()) [get_refs_def])
  \\ res_tac \\ POP_ASSUM MP_TAC
  \\ simp_tac std_ss [Once bc_ref_inv_def]
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF]
  \\ Cases_on `ptr IN FDOM refs` \\ full_simp_tac (srw_ss()) []
  \\ reverse (Cases_on `refs ' ptr`) \\ full_simp_tac (srw_ss()) []
  \\ NTAC 3 strip_tac
  \\ imp_res_tac EVERY2_IMP_LENGTH
  \\ asm_simp_tac (srw_ss()) [heap_el_def,RefBlock_def]
  \\ srw_tac [] [] THEN1
   (full_simp_tac std_ss [roots_ok_def,heap_ok_def]
    \\ imp_res_tac heap_lookup_MEM
    \\ strip_tac \\ once_rewrite_tac [MEM] \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ rpt strip_tac \\ res_tac
    \\ full_simp_tac std_ss [RefBlock_def]
    \\ res_tac \\ full_simp_tac std_ss [MEM]
    \\ FIRST_X_ASSUM match_mp_tac
    \\ metis_tac [MEM_EL])
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ imp_res_tac EVERY2_IMP_EL
  \\ full_simp_tac std_ss []
  \\ rpt strip_tac
  \\ FIRST_X_ASSUM match_mp_tac
  \\ qpat_assum `reachable_refs (RefPtr ptr::stack) refs ptr` (K ALL_TAC)
  \\ full_simp_tac std_ss [reachable_refs_def]
  \\ reverse (Cases_on `x = EL n l`)
  THEN1 (full_simp_tac std_ss [MEM] \\ metis_tac [])
  \\ qexists_tac `RefPtr ptr` \\ simp_tac std_ss [MEM,get_refs_def]
  \\ once_rewrite_tac [RTC_CASES1] \\ DISJ2_TAC
  \\ qexists_tac `r` \\ full_simp_tac std_ss []
  \\ full_simp_tac (srw_ss()) [ref_edge_def,FLOOKUP_DEF,get_refs_def]
  \\ full_simp_tac (srw_ss()) [MEM_FLAT,MEM_MAP,PULL_EXISTS]
  \\ qexists_tac `(EL n l)` \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [MEM_EL] \\ metis_tac []);

(* el *)

val el_thm = store_thm("el_thm",
  ``abs_ml_inv (Block n xs::stack) refs (roots,heap,be,a,sp) limit /\ i < LENGTH xs ==>
    ?r roots2 y.
      (roots = r :: roots2) /\ (heap_el r i heap = (y,T)) /\
      abs_ml_inv (EL i xs::Block n xs::stack) refs (y::roots,heap,be,a,sp) limit``,
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
  \\ rpt strip_tac \\ Cases_on `roots` \\ full_simp_tac (srw_ss()) [LIST_REL_def]
  \\ full_simp_tac std_ss [v_inv_def]
  \\ `xs <> []` by (rpt strip_tac \\ full_simp_tac std_ss [GSYM LENGTH_NIL,LENGTH])
  \\ full_simp_tac std_ss []
  \\ asm_simp_tac (srw_ss()) [heap_el_def,BlockRep_def]
  \\ imp_res_tac EVERY2_LENGTH \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss []
  \\ strip_tac THEN1
   (full_simp_tac std_ss [roots_ok_def,heap_ok_def] \\ once_rewrite_tac [MEM]
    \\ rpt strip_tac \\ res_tac
    \\ imp_res_tac heap_lookup_MEM
    \\ full_simp_tac std_ss [BlockRep_def]
    \\ `MEM (Pointer ptr' u') xs'` by ALL_TAC \\ res_tac
    \\ full_simp_tac std_ss [MEM_EL] \\ metis_tac [])
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ strip_tac THEN1 (full_simp_tac std_ss [EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS])
  \\ rpt strip_tac
  \\ qpat_assum `!xx.bbb` match_mp_tac
  \\ full_simp_tac std_ss [reachable_refs_def]
  \\ reverse (Cases_on `x = EL i xs`)
  THEN1 (full_simp_tac std_ss [MEM] \\ metis_tac [])
  \\ Q.LIST_EXISTS_TAC [`Block n xs`,`r`]
  \\ asm_simp_tac std_ss [MEM]
  \\ full_simp_tac std_ss [get_refs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]
  \\ qexists_tac `EL i xs` \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [MEM_EL] \\ qexists_tac `i`
  \\ full_simp_tac std_ss []);

(* pop *)

val pop_thm = store_thm("pop_thm",
  ``abs_ml_inv (xs ++ stack) refs (rs ++ roots,heap,be,a,sp) limit /\
    (LENGTH xs = LENGTH rs) ==>
    abs_ml_inv (stack) refs (roots,heap,be,a,sp) limit``,
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ rpt strip_tac
  \\ full_simp_tac std_ss [roots_ok_def,MEM_APPEND]
  THEN1 (rw [] \\ res_tac \\ fs [])
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ imp_res_tac EVERY2_APPEND \\ full_simp_tac std_ss []
  \\ rpt strip_tac
  \\ full_simp_tac std_ss [reachable_refs_def,MEM_APPEND] \\ metis_tac []);

(* permute stack *)

val abs_ml_inv_stack_permute = store_thm("abs_ml_inv_stack_permute",
  ``!xs ys.
      abs_ml_inv (MAP FST xs ++ stack) refs (MAP SND xs ++ roots,heap,be,a,sp) limit /\
      set ys SUBSET set xs ==>
      abs_ml_inv (MAP FST ys ++ stack) refs (MAP SND ys ++ roots,heap,be,a,sp) limit``,
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ rpt strip_tac
  \\ full_simp_tac std_ss [roots_ok_def]
  THEN1 (full_simp_tac std_ss [MEM_APPEND,SUBSET_DEF,MEM_MAP] \\ metis_tac [])
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [EVERY2_APPEND,LENGTH_MAP]
  \\ full_simp_tac std_ss [EVERY2_MAP_FST_SND]
  \\ full_simp_tac std_ss [EVERY_MEM,SUBSET_DEF]
  \\ full_simp_tac std_ss [reachable_refs_def,MEM_APPEND,MEM_MAP]
  \\ metis_tac []);

(* duplicate *)

val duplicate_thm = store_thm("duplicate_thm",
  ``abs_ml_inv (xs ++ stack) refs (rs ++ roots,heap,be,a,sp) limit /\
    (LENGTH xs = LENGTH rs) ==>
    abs_ml_inv (xs ++ xs ++ stack) refs (rs ++ rs ++ roots,heap,be,a,sp) limit``,
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ rpt strip_tac
  \\ full_simp_tac std_ss [roots_ok_def] THEN1 metis_tac [MEM_APPEND]
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ imp_res_tac EVERY2_APPEND \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [APPEND_ASSOC]
  \\ full_simp_tac std_ss [reachable_refs_def,MEM_APPEND] \\ metis_tac []);

val duplicate1_thm = save_thm("duplicate1_thm",
  duplicate_thm |> Q.INST [`xs`|->`[x1]`,`rs`|->`[r1]`]
                |> SIMP_RULE std_ss [LENGTH,APPEND]);

(* move *)

val EVERY2_APPEND_IMP = prove(
  ``EVERY2 P (xs1 ++ xs2) (ys1 ++ ys2) ==>
    (LENGTH xs1 = LENGTH ys1) ==> EVERY2 P xs1 ys1 /\ EVERY2 P xs2 ys2``,
  rpt strip_tac \\ imp_res_tac EVERY2_LENGTH \\ imp_res_tac EVERY2_APPEND);

val move_thm = store_thm("move_thm",
  ``!xs1 rs1 xs2 rs2 xs3 rs3.
      abs_ml_inv (xs1 ++ xs2 ++ xs3 ++ stack) refs
                 (rs1 ++ rs2 ++ rs3 ++ roots,heap,be,a,sp) limit /\
      (LENGTH xs1 = LENGTH rs1) /\
      (LENGTH xs2 = LENGTH rs2) /\
      (LENGTH xs3 = LENGTH rs3) ==>
      abs_ml_inv (xs1 ++ xs3 ++ xs2 ++ stack) refs
                 (rs1 ++ rs3 ++ rs2 ++ roots,heap,be,a,sp) limit``,
  REPEAT GEN_TAC
  \\ full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ rpt strip_tac
  \\ full_simp_tac std_ss [roots_ok_def] THEN1 metis_tac [MEM_APPEND]
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ strip_tac THEN1
   (NTAC 5 (imp_res_tac EVERY2_APPEND_IMP \\ REPEAT (POP_ASSUM MP_TAC)
    \\ full_simp_tac std_ss [LENGTH_APPEND,AC ADD_COMM ADD_ASSOC]
    \\ rpt strip_tac)
    \\ NTAC 5 (match_mp_tac IMP_EVERY2_APPEND \\ full_simp_tac std_ss []))
  \\ full_simp_tac std_ss [reachable_refs_def,MEM_APPEND] \\ metis_tac []);

(* splits *)

val EVERY2_APPEND1 = prove(
  ``!xs1 xs2 ys.
      EVERY2 P (xs1 ++ xs2) ys ==>
      ?ys1 ys2. (ys = ys1 ++ ys2) /\
                (LENGTH xs1 = LENGTH ys1) /\ EVERY2 P xs2 ys2``,
  Induct THEN1
   (full_simp_tac (srw_ss()) [] \\ rpt strip_tac
    \\ qexists_tac `[]` \\ full_simp_tac (srw_ss()) [])
  \\ Cases_on `ys` \\ full_simp_tac (srw_ss()) [] \\ rpt strip_tac
  \\ res_tac \\ full_simp_tac std_ss []
  \\ Q.LIST_EXISTS_TAC [`h::ys1`,`ys2`] \\ full_simp_tac (srw_ss()) []);

val split1_thm = store_thm("split1_thm",
  ``abs_ml_inv (xs1 ++ stack) refs (roots,heap,be,a,sp) limit ==>
    ?rs1 roots1. (roots = rs1 ++ roots1) /\ (LENGTH rs1 = LENGTH xs1)``,
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,GSYM APPEND_ASSOC]
  \\ rpt strip_tac \\ NTAC 5 (imp_res_tac EVERY2_APPEND1) \\ metis_tac []);

val split2_thm = store_thm("split2_thm",
  ``abs_ml_inv (xs1 ++ xs2 ++ stack) refs (roots,heap,be,a,sp) limit ==>
    ?rs1 rs2 roots1. (roots = rs1 ++ rs2 ++ roots1) /\
      (LENGTH rs1 = LENGTH xs1) /\ (LENGTH rs2 = LENGTH xs2)``,
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,GSYM APPEND_ASSOC]
  \\ rpt strip_tac \\ NTAC 5 (imp_res_tac EVERY2_APPEND1) \\ metis_tac []);

val split3_thm = store_thm("split3_thm",
  ``abs_ml_inv (xs1 ++ xs2 ++ xs3 ++ stack) refs (roots,heap,be,a,sp) limit ==>
    ?rs1 rs2 rs3 roots1. (roots = rs1 ++ rs2 ++ rs3 ++ roots1) /\
      (LENGTH rs1 = LENGTH xs1) /\ (LENGTH rs2 = LENGTH xs2) /\
      (LENGTH rs3 = LENGTH xs3)``,
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,GSYM APPEND_ASSOC]
  \\ rpt strip_tac \\ NTAC 5 (imp_res_tac EVERY2_APPEND1) \\ metis_tac []);

val LESS_EQ_LENGTH = store_thm("LESS_EQ_LENGTH",
  ``!xs k. k <= LENGTH xs ==> ?ys1 ys2. (xs = ys1 ++ ys2) /\ (LENGTH ys1 = k)``,
  Induct \\ Cases_on `k` \\ full_simp_tac std_ss [LENGTH,ADD1,LENGTH_NIL,APPEND]
  \\ rpt strip_tac \\ res_tac \\ full_simp_tac std_ss []
  \\ qexists_tac `h::ys1` \\ full_simp_tac std_ss [LENGTH,APPEND]
  \\ srw_tac [] [ADD1]);

val LESS_LENGTH = store_thm("LESS_LENGTH",
  ``!xs k. k < LENGTH xs ==>
           ?ys1 y ys2. (xs = ys1 ++ y::ys2) /\ (LENGTH ys1 = k)``,
  Induct \\ Cases_on `k` \\ full_simp_tac std_ss [LENGTH,ADD1,LENGTH_NIL,APPEND]
  \\ rpt strip_tac \\ res_tac \\ full_simp_tac std_ss [CONS_11]
  \\ qexists_tac `h::ys1` \\ full_simp_tac std_ss [LENGTH,APPEND]
  \\ srw_tac [] [ADD1]);


(* -------------------------------------------------------
    representation in memory
   ------------------------------------------------------- *)

val all_ones_def = Define `
  all_ones m n = (m -- n) (~0w)`

val maxout_bits_def = Define `
  maxout_bits n rep_len k =
    if n < 2 ** rep_len then n2w n << k else all_ones (k + rep_len) k`

val has_header_def = Define `
  (has_header conf (SOME (DataElement xs l (BlockTag tag,_))) <=>
     LENGTH xs < 2 ** conf.len_bits - 1 ==> ~(tag < 2 ** conf.tag_bits - 1)) /\
  (has_header _ _ <=> F)`

val pointer_bits_def = Define ` (* pointers have tag and len bits *)
  pointer_bits conf abs_heap n =
    case heap_lookup n abs_heap of
    | SOME (DataElement xs l (BlockTag tag,[])) =>
        maxout_bits (LENGTH xs) conf.len_bits (conf.tag_bits + 2) ||
        maxout_bits tag conf.tag_bits 2 || 1w
    | _ => all_ones (conf.len_bits + conf.tag_bits + 1) 0`

val get_addr_def = Define ` (* each pointer points at the first payload value *)
  (get_addr conf n (Word w) =
     (n2w n << (2 + conf.pad_bits + conf.len_bits + conf.tag_bits) || w)) /\
  (get_addr conf n _ = 0w)`;

val word_addr_def = Define `
  (word_addr conf (Data w) = w) /\
  (word_addr conf (Pointer n w) = Word (get_addr conf n w))`

val one_list_def = Define `
  (one_list a [] = emp) /\
  (one_list a (x::xs) = one (a,x) * one_list (a + bytes_in_word) xs)`;

val one_list_exists_def = Define `
  one_list_exists a n =
    SEP_EXISTS xs. one_list a xs * cond (LENGTH xs = n)`;

val b2w_def = Define `(b2w T = 1w) /\ (b2w F = 0w)`;

val word_payload_def = Define `
  (word_payload ys l (BlockTag n) qs conf =
     if (n < 2 ** conf.tag_bits - 1 /\
         LENGTH ys - 1 < 2 ** conf.len_bits - 1)
     then (NONE, (* no header *)
           MAP (word_addr conf) ys,
           (qs = []) /\ (LENGTH ys - 1 = l))
     else (SOME (n2w n << 2), (* header: ...00 *)
           MAP (word_addr conf) ys,
           (qs = []) /\ (LENGTH ys = l))) /\
  (word_payload ys l (RefTag) qs conf =
     (SOME 1w, (* header: ...01 *)
      MAP (word_addr conf) ys,
      (qs = []) /\ (LENGTH ys = l) /\ l <> 0)) /\
  (word_payload ys l (NumTag b) qs conf =
     (SOME (b2w b << 2 || 2w), (* header: ...110 or ...010 *)
      qs, (ys = []) /\ (LENGTH qs = l) /\ l <> 0)) /\
  (word_payload ys l (BytesTag n) qs conf =
     (SOME (n2w n << 2 || 3w), (* header: ...11 *)
      qs, (ys = []) /\ (LENGTH qs = l) /\ l <> 0))`;

val decode_tag_bits_def = Define `
  decode_tag_bits conf w =
    let h = (w >>> (3 + conf.len_size)) in
      if h = 0b001w then RefTag else
      if h = 0b110w then NumTag T else
      if h = 0b010w then NumTag F else
      if (h && 3w) = 3w then BytesTag (w2n (h >>> 2)) else
        BlockTag (w2n (h >>> 2))`

(*
data pointers end in 01
forward pointers and headers end in 11
*)

val word_el_def = Define `
  (word_el a (Unused l) conf = one_list_exists a (l+1)) /\
  (word_el a (ForwardPointer n d l) conf =
     one_list_exists a 1 *
     if l = 0 then emp else
       one (a + bytes_in_word,Word (n2w n << 2 || 3w)) *
       one_list_exists (a + 2w * bytes_in_word) (l - 1)) /\
  (word_el a (DataElement ys l (tag,qs)) conf =
     case word_payload ys l tag qs conf of
     | (NONE,ts,c) => one_list a ts * cond c
     | (SOME h,ts,c) =>
         let w = (h << (2 + conf.len_size) || n2w (LENGTH ts) << 2 || 3w) in
           one (a,Word w) * one_list (a + bytes_in_word) ts *
           cond (c /\ LENGTH ts < 2 ** conf.len_size /\
                 decode_tag_bits conf w = tag))`;

val word_heap_def = Define `
  (word_heap a ([]:'a ml_heap) conf = emp) /\
  (word_heap a (x::xs) conf =
     word_el a x conf *
     word_heap (a + bytes_in_word * n2w (el_length x)) xs conf)`;

val _ = export_theory();
