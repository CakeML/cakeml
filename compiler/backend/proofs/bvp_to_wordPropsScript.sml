open preamble bvlSemTheory bvpSemTheory bvpPropsTheory copying_gcTheory
     int_bitwiseTheory wordSemTheory bvp_to_wordTheory set_sepTheory
     labSemTheory whileTheory helperLib alignmentTheory;

val _ = new_theory "bvp_to_wordProps";

val get_lowerbits_def = Define `
  (get_lowerbits conf (Word w) = ((((shift_length conf - 1) -- 0) w) || 1w)) /\
  (get_lowerbits conf _ = 1w)`;

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

val bytes_to_word_def = Define `
  (bytes_to_word 0 a bs w be = w) /\
  (bytes_to_word (SUC k) a [] w be = w) /\
  (bytes_to_word (SUC k) a (b::bs) w be =
     set_byte a b (bytes_to_word k (a+1w) bs w be) be)`

val write_bytes_def = Define `
  (write_bytes bs [] be = []) /\
  (write_bytes bs ((w:'a word)::ws) be =
     let k = dimindex (:'a) DIV 8 in
       bytes_to_word k 0w bs w be
          :: write_bytes (DROP k bs) ws be)`

val Bytes_def = Define`
  ((Bytes is_bigendian (bs:word8 list) (ws:'a word list)):'a ml_el) =
    let ws = write_bytes bs ws is_bigendian in
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
  small_int (:'a) i <=>
    -&(dimword (:'a) DIV 8) <= i /\ i < &(dimword (:'a) DIV 8)`

val BlockNil_def = Define `
  BlockNil n = n2w n << 4 + 2w`;

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
       F /\ (* TODO: remove this line, so that bignums are allowed *)
       ?ptr. (x = Pointer ptr (Word 0w)) /\
             (heap_lookup ptr heap = SOME (Bignum i))) /\
  (v_inv (CodePtr n) (x,f,heap) <=>
     (x = Data (Loc n 0))) /\
  (v_inv (RefPtr n) (x,f,heap) <=>
     (x = Pointer (f ' n) (Word 0w)) /\ n IN FDOM f) /\
  (v_inv (Block n vs) (x,f,heap) <=>
     if vs = []
     then (x = Data (Word (BlockNil n))) /\ n < dimword(:'a) DIV 16
     else
       ?ptr xs.
         EVERY2 (\v x. v_inv v (x,f,heap)) vs xs /\
         (x = Pointer ptr (Word (ptr_bits conf n (LENGTH xs)))) /\
         (heap_lookup ptr heap = SOME (BlockRep n xs)))`
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
  bc_ref_inv conf n refs (f,heap,be) =
    case (FLOOKUP f n, FLOOKUP refs n) of
    | (SOME x, SOME (ValueArray ys)) =>
        (?zs. (heap_lookup x heap = SOME (RefBlock zs)) /\
              EVERY2 (\z y. v_inv conf y (z,f,heap)) zs ys)
    | (SOME x, SOME (ByteArray bs)) =>
        ?ws. LENGTH bs + 8 < 2 ** (dimindex (:'a) - 3) /\
             LENGTH ws = LENGTH bs DIV (dimindex (:α) DIV 8) + 1 /\
             (heap_lookup x heap = SOME (Bytes be bs (ws:'a word list)))
    | _ => F`;

val bc_stack_ref_inv_def = Define `
  bc_stack_ref_inv conf stack refs (roots, heap, be) =
    ?f. INJ (FAPPLY f) (FDOM f) { a | isSomeDataElement (heap_lookup a heap) } /\
        FDOM f SUBSET FDOM refs /\
        EVERY2 (\v x. v_inv conf v (x,f,heap)) stack roots /\
        !n. reachable_refs stack refs n ==> bc_ref_inv conf n refs (f,heap,be)`;

val unused_space_inv_def = Define `
  unused_space_inv ptr l heap <=>
    (l <> 0 ==> (heap_lookup ptr heap = SOME (Unused (l-1))))`;

val abs_ml_inv_def = Define `
  abs_ml_inv conf stack refs (roots,heap,be,a,sp) limit <=>
    roots_ok roots heap /\ heap_ok heap limit /\
    unused_space_inv a sp heap /\
    bc_stack_ref_inv conf stack refs (roots,heap,be)`;

(* --- *)

val MOD_EQ_0_0 = store_thm("MOD_EQ_0_0",
  ``∀n b. 0 < b ⇒ (n MOD b = 0) ⇒ n < b ⇒ (n = 0)``,
  rw[MOD_EQ_0_DIVISOR] >> Cases_on`d`>>fs[])

val EVERY2_IMP_EVERY = store_thm("EVERY2_IMP_EVERY",
  ``!xs ys. EVERY2 P xs ys ==> EVERY (\(x,y). P y x) (ZIP(ys,xs))``,
  Induct \\ Cases_on `ys` \\ full_simp_tac(srw_ss())[]);

val EVERY2_IMP_EVERY2 = store_thm("EVERY2_IMP_EVERY2",
  ``!xs ys P1 P2.
      (!x y. MEM x xs /\ MEM y ys /\ P1 x y ==> P2 x y) ==>
      EVERY2 P1 xs ys ==> EVERY2 P2 xs ys``,
  Induct \\ Cases_on `ys` \\ full_simp_tac (srw_ss()) []
  \\ rpt strip_tac \\ metis_tac []);

val EVERY2_APPEND_IMP = store_thm("EVERY2_APPEND_IMP",
  ``!xs1 xs2 ys.
      EVERY2 P (xs1 ++ xs2) ys ==>
      ?ys1 ys2. (ys = ys1 ++ ys2) /\ EVERY2 P xs1 ys1 /\ EVERY2 P xs2 ys2``,
  Induct \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `ys` \\ full_simp_tac (srw_ss()) [] \\ rpt strip_tac
  \\ res_tac \\ metis_tac [LIST_REL_def,APPEND]);

val MEM_EVERY2_IMP = store_thm("MEM_EVERY2_IMP",
  ``!l x zs P. MEM x l /\ EVERY2 P zs l ==> ?z. MEM z zs /\ P z x``,
  Induct \\ Cases_on `zs` \\ full_simp_tac (srw_ss()) [] \\ metis_tac []);

val EVERY2_LENGTH = LIST_REL_LENGTH
val EVERY2_IMP_LENGTH = EVERY2_LENGTH

val EVERY2_APPEND_CONS = store_thm("EVERY2_APPEND_CONS",
  ``!xs y ys zs P. EVERY2 P (xs ++ y::ys) zs ==>
                   ?t1 t t2. (zs = t1 ++ t::t2) /\ (LENGTH t1 = LENGTH xs) /\
                             EVERY2 P xs t1 /\ P y t /\ EVERY2 P ys t2``,
  Induct \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `zs` \\ full_simp_tac (srw_ss()) []
  \\ rpt strip_tac
  \\ res_tac \\ full_simp_tac std_ss []
  \\ Q.LIST_EXISTS_TAC [`h::t1`,`t'`,`t2`]
  \\ full_simp_tac (srw_ss()) []);

val EVERY2_SWAP = store_thm("EVERY2_SWAP",
  ``!xs ys. EVERY2 P xs ys ==> EVERY2 (\y x. P x y) ys xs``,
  Induct \\ Cases_on `ys` \\ full_simp_tac (srw_ss()) []);

val EVERY2_APPEND_IMP_APPEND = store_thm("EVERY2_APPEND_IMP_APPEND",
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
      v_inv conf w (x,f,heap1) ==>
      v_inv conf w (ADDR_APPLY (FAPPLY g) x,g f_o_f f,heap2) /\
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
    bc_ref_inv conf n refs (f,heap1,be) /\ (f ' n) IN FDOM g ==>
    bc_ref_inv conf n refs (g f_o_f f,heap2,be)``,
  full_simp_tac std_ss [bc_ref_inv_def] \\ strip_tac \\ full_simp_tac std_ss []
  \\ MP_TAC v_inv_related \\ asm_simp_tac std_ss []
  \\ full_simp_tac (srw_ss()) [f_o_f_DEF,gc_related_def,RefBlock_def] \\ res_tac
  \\ Cases_on `FLOOKUP f n` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `FLOOKUP refs n` \\ full_simp_tac (srw_ss()) []
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,f_o_f_DEF]
  \\ Cases_on `x'` \\ full_simp_tac (srw_ss()) []
  \\ TRY (fs[Bytes_def,LET_THM] >> res_tac >> simp[ADDR_MAP_def]
          \\ rw [] \\ qexists_tac `ws` \\ fs [] >> NO_TAC)
  \\ res_tac \\ full_simp_tac (srw_ss()) [LENGTH_ADDR_MAP,EVERY2_ADDR_MAP]
  \\ rpt strip_tac \\ qpat_assum `EVERY2 qqq zs l` MP_TAC
  \\ match_mp_tac EVERY2_IMP_EVERY2 \\ simp_tac std_ss [] \\ rpt strip_tac
  \\ Cases_on `x'` \\ full_simp_tac (srw_ss()) [ADDR_APPLY_def]
  \\ res_tac \\ fs [ADDR_APPLY_def]);

val RTC_lemma = prove(
  ``!r n. RTC (ref_edge refs) r n ==>
          (!m. RTC (ref_edge refs) r m ==> bc_ref_inv conf m refs (f,heap,be)) /\
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
    EVERY2 (\v x. v_inv conf v (x,f,heap)) stack roots /\
    (!n. reachable_refs stack refs n ==> bc_ref_inv conf n refs (f,heap,be)) /\
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
  \\ `bc_ref_inv conf r refs (f,heap,be)` by metis_tac [RTC_REFL]
  \\ `(!m. RTC (ref_edge refs) r m ==>
           bc_ref_inv conf m refs (f,heap,be))` by ALL_TAC
  THEN1 metis_tac [] \\ imp_res_tac RTC_lemma);

val bc_stack_ref_inv_related = prove(
  ``gc_related g heap1 heap2 /\
    bc_stack_ref_inv conf stack refs (roots,heap1,be) /\
    (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM g) ==>
    bc_stack_ref_inv conf stack refs (ADDR_MAP (FAPPLY g) roots,heap2,be)``,
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
  ``abs_ml_inv conf stack refs (roots,heap,be,a,sp) limit ==>
    ?roots2 heap2 a2.
      (full_gc (roots,heap,limit) = (roots2,heap2,a2,T)) /\
      abs_ml_inv conf stack refs
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
      v_inv conf w (x,f,heap) ==>
      v_inv conf w (x,f1,heap1) ``,
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
  ``abs_ml_inv conf (xs ++ stack) refs (roots,heap,be,a,sp) limit /\
    LENGTH xs < sp /\ xs <> [] ==>
    ?rs roots2 heap2.
      (roots = rs ++ roots2) /\ (LENGTH rs = LENGTH xs) /\
      (heap_store_unused a sp (BlockRep tag rs) heap = (heap2,T)) /\
      abs_ml_inv conf
        ((Block tag xs)::stack) refs
        (Pointer (a + sp - el_length (BlockRep tag rs))
           (Word (ptr_bits conf tag (LENGTH xs)))::roots2,
         heap2,be,a,
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
  \\ fs[Bytes_def,LET_THM] >> imp_res_tac heap_store_rel_lemma
  \\ metis_tac [])

val cons_thm_EMPTY = store_thm("cons_thm_EMPTY",
  ``abs_ml_inv conf stack refs (roots,heap:'a ml_heap,be,a,sp) limit /\
    tag < dimword (:'a) DIV 16 ==>
    abs_ml_inv conf ((Block tag [])::stack) refs
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

val heap_store_RefBlock_thm = store_thm("heap_store_RefBlock_thm",
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
    !x h f. (v_inv conf x (h,f,heap2) = v_inv conf x (h,f,heap))``,
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
  ``abs_ml_inv conf (xs ++ (RefPtr ptr)::stack) refs (roots,heap,be,a,sp) limit /\
    (FLOOKUP refs ptr = SOME (ValueArray xs1)) /\ (LENGTH xs = LENGTH xs1) ==>
    ?p rs roots2 heap2 u.
      (roots = rs ++ Pointer p u :: roots2) /\
      (heap_store p [RefBlock rs] heap = (heap2,T)) /\
      abs_ml_inv conf (xs ++ (RefPtr ptr)::stack) (refs |+ (ptr,ValueArray xs))
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
  ``abs_ml_inv conf (xs ++ RefPtr ptr::stack) refs (roots,heap,be,a,sp) limit /\
    (FLOOKUP refs ptr = SOME (ValueArray xs1)) /\ i < LENGTH xs1 /\ 0 < LENGTH xs
    ==>
    ?p rs roots2 vs1 heap2 u.
      (roots = rs ++ Pointer p u :: roots2) /\ (LENGTH rs = LENGTH xs) /\
      (heap_deref p heap = SOME vs1) /\ LENGTH vs1 = LENGTH xs1 /\
      (heap_store p [RefBlock (LUPDATE (HD rs) i vs1)] heap = (heap2,T)) /\
      abs_ml_inv conf (xs ++ (RefPtr ptr)::stack) (refs |+ (ptr,ValueArray (LUPDATE (HD xs) i xs1)))
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
   (imp_res_tac EVERY2_LENGTH \\ fs [])
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

(* update byte ref *)

val LENGTH_write_bytes = store_thm("LENGTH_write_bytes[simp]",
  ``!ws bs be. LENGTH (write_bytes bs ws be) = LENGTH ws``,
  Induct \\ fs [write_bytes_def]);

val LIST_REL_IMP_LIST_REL = prove(
  ``!xs ys.
      (!x y. MEM x xs ==> P x y ==> Q x y) ==>
      LIST_REL P xs ys ==> LIST_REL Q xs ys``,
  Induct \\ fs [PULL_EXISTS]);

val v_size_LESS_EQ = prove(
  ``!l x. MEM x l ==> v_size x <= v1_size l``,
  Induct \\ fs [v_size_def] \\ rw [] \\ fs [] \\ res_tac \\ fs []);

val v_inv_IMP = prove(
  ``∀y x f ha.
      v_inv conf y (x,f,ha ++ [Bytes be xs ws] ++ hb) ⇒
      v_inv conf y (x,f,ha ++ [Bytes be ys ws] ++ hb)``,
  completeInduct_on `v_size y` \\ rw [] \\ fs [PULL_FORALL]
  \\ Cases_on `y` \\ fs [v_inv_def] \\ rw [] \\ fs []
  \\ qexists_tac `xs'` \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ conj_tac THEN1
   (qpat_assum `LIST_REL _ _ _` mp_tac
    \\ match_mp_tac LIST_REL_IMP_LIST_REL \\ fs []
    \\ rpt strip_tac \\ first_x_assum match_mp_tac \\ fs []
    \\ fs [v_size_def] \\ imp_res_tac v_size_LESS_EQ \\ fs [])
  \\ fs [Bytes_def,heap_lookup_APPEND,heap_lookup_def,BlockRep_def,
         heap_length_APPEND,heap_length_def,SUM_APPEND,el_length_def]
  \\ rw [] \\ fs []);

val update_byte_ref_thm = store_thm("update_byte_ref_thm",
  ``abs_ml_inv conf ((RefPtr ptr)::stack) refs (roots,heap,be,a,sp) limit /\
    (FLOOKUP refs ptr = SOME (ByteArray xs)) /\ (LENGTH xs = LENGTH ys) ==>
    ?roots2 h1 h2 ws.
      (roots = Pointer (heap_length h1) ((Word 0w):'a word_loc) :: roots2) /\
      heap = h1 ++ [Bytes be xs ws] ++ h2 /\
      LENGTH ws = LENGTH xs DIV (dimindex (:α) DIV 8) + 1 /\
      abs_ml_inv conf ((RefPtr ptr)::stack) (refs |+ (ptr,ByteArray ys))
        (roots,h1 ++ [Bytes be ys ws] ++ h2,be,a,sp) limit``,
  simp_tac std_ss [abs_ml_inv_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [bc_stack_ref_inv_def]
  \\ Cases_on `roots` \\ fs [v_inv_def] \\ rpt var_eq_tac \\ fs []
  \\ `reachable_refs (RefPtr ptr::stack) refs ptr` by
   (full_simp_tac std_ss [reachable_refs_def] \\ qexists_tac `RefPtr ptr`
    \\ full_simp_tac (srw_ss()) [get_refs_def] \\ NO_TAC)
  \\ res_tac \\ fs []
  \\ pop_assum mp_tac \\ simp_tac std_ss [Once bc_ref_inv_def]
  \\ fs [FLOOKUP_DEF] \\ rw []
  \\ drule heap_lookup_SPLIT \\ rw [] \\ fs []
  \\ qexists_tac `ha` \\ fs []
  \\ qexists_tac `ws` \\ fs [PULL_EXISTS]
  \\ qexists_tac `f` \\ fs []
  \\ `!a. isSomeDataElement (heap_lookup a (ha ++ [Bytes be ys ws] ++ hb)) =
          isSomeDataElement (heap_lookup a (ha ++ [Bytes be xs ws] ++ hb))` by
   (rw [] \\ fs [isSomeDataElement_def] \\ rw []
    \\ fs [heap_lookup_APPEND] \\ rw [] \\ rw [] \\ fs []
    \\ fs [heap_length_def,Bytes_def,el_length_def,heap_lookup_def])
  \\ `ptr INSERT FDOM refs = FDOM refs` by (fs [EXTENSION] \\ metis_tac [])
  \\ fs [] \\ rpt strip_tac
  THEN1 (fs [roots_ok_def] \\ rw [] \\ fs [] \\ metis_tac [])
  THEN1
   (fs [heap_ok_def]
    \\ fs [heap_length_def,Bytes_def,el_length_def,heap_lookup_def,
           FILTER_APPEND,FILTER,isForwardPointer_def]
    \\ rfs [] \\ fs [] \\ rpt strip_tac
    \\ first_x_assum match_mp_tac \\ metis_tac [])
  THEN1
   (fs [unused_space_inv_def,heap_lookup_APPEND,heap_length_def]
    \\ fs [heap_length_def,Bytes_def,el_length_def,heap_lookup_def,
           FILTER_APPEND,FILTER,isForwardPointer_def]
    \\ rfs [] \\ fs [] \\ rw [] \\ fs [])
  THEN1
   (qpat_assum `LIST_REL _ _ _` mp_tac
    \\ match_mp_tac LIST_REL_mono \\ fs []
    \\ metis_tac [v_inv_IMP])
  \\ `reachable_refs (RefPtr ptr::stack) refs n` by
   (pop_assum mp_tac
    \\ `ref_edge (refs |+ (ptr,ByteArray ys)) = ref_edge refs` by all_tac
    \\ simp [reachable_refs_def]
    \\ fs [ref_edge_def,FUN_EQ_THM,FLOOKUP_UPDATE]
    \\ rw [] \\ fs [FLOOKUP_DEF])
  \\ Cases_on `n = ptr` \\ fs [] THEN1
   (fs [] \\ rw [bc_ref_inv_def,FLOOKUP_DEF]
    \\ fs [heap_lookup_APPEND,heap_length_APPEND,Bytes_def,
           heap_length_def,el_length_def,heap_lookup_def]
    \\ asm_exists_tac \\ fs [])
  \\ first_x_assum drule
  \\ fs [bc_ref_inv_def]
  \\ strip_tac \\ CASE_TAC \\ fs []
  \\ fs [FLOOKUP_UPDATE] \\ rfs [] \\ fs []
  \\ CASE_TAC \\ fs [] \\ CASE_TAC \\ fs []
  THEN1
   (once_rewrite_tac [CONJ_COMM] \\ qexists_tac `zs` \\ fs []
    \\ conj_tac THEN1 (pop_assum mp_tac
      \\ match_mp_tac LIST_REL_mono \\ fs [] \\ metis_tac [v_inv_IMP])
    \\ fs [heap_lookup_def,heap_lookup_APPEND,Bytes_def,
           el_length_def,SUM_APPEND,RefBlock_def,heap_length_APPEND]
    \\ rw [] \\ fs [] \\ rfs [heap_length_def,el_length_def] \\ fs [NOT_LESS])
  \\ asm_exists_tac \\ fs []
  \\ Cases_on `x = heap_length ha`
  THEN1 (fs [INJ_DEF,FLOOKUP_DEF] \\ metis_tac [])
  \\ fs [heap_lookup_APPEND,Bytes_def,heap_length_def,el_length_def,SUM_APPEND]
  \\ rfs [] \\ rw [] \\ fs [] \\ rfs [heap_lookup_def])

(* new ref *)

val new_ref_thm = store_thm("new_ref_thm",
  ``abs_ml_inv conf (xs ++ stack) refs (roots,heap,be,a,sp) limit /\
    ~(ptr IN FDOM refs) /\ LENGTH xs + 1 <= sp ==>
    ?p rs roots2 heap2.
      (roots = rs ++ roots2) /\ LENGTH rs = LENGTH xs /\
      (heap_store_unused a sp (RefBlock rs) heap = (heap2,T)) /\
      abs_ml_inv conf (xs ++ (RefPtr ptr)::stack) (refs |+ (ptr,ValueArray xs))
                 (rs ++ Pointer (a+sp-(LENGTH xs + 1)) (Word 0w)::roots2,heap2,be,a,
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
  THEN1 (asm_exists_tac \\ fs []
         \\ imp_res_tac heap_store_rel_lemma \\ fs [Bytes_def])
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
  ``abs_ml_inv conf (RefPtr ptr::stack) refs (roots,heap,be,a,sp) limit ==>
    ?r roots2.
      (roots = r::roots2) /\ ptr IN FDOM refs /\
      case refs ' ptr of
      | ByteArray _ => T
      | ValueArray ts =>
      !n. n < LENGTH ts ==>
          ?y. (heap_el r n heap = (y,T)) /\
                abs_ml_inv conf (EL n ts::RefPtr ptr::stack) refs
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
  ``abs_ml_inv conf (Block n xs::stack) refs (roots,heap,be,a,sp) limit /\
    i < LENGTH xs ==>
    ?r roots2 y.
      (roots = r :: roots2) /\ (heap_el r i heap = (y,T)) /\
      abs_ml_inv conf (EL i xs::Block n xs::stack) refs
                      (y::roots,heap,be,a,sp) limit``,
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
    \\ `?u'. MEM (Pointer ptr' u') xs'` by ALL_TAC \\ res_tac
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
  ``abs_ml_inv conf (xs ++ stack) refs (rs ++ roots,heap,be,a,sp) limit /\
    (LENGTH xs = LENGTH rs) ==>
    abs_ml_inv conf (stack) refs (roots,heap,be,a,sp) limit``,
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ rpt strip_tac
  \\ full_simp_tac std_ss [roots_ok_def,MEM_APPEND]
  THEN1 (rw [] \\ res_tac \\ fs [])
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ imp_res_tac EVERY2_APPEND \\ full_simp_tac std_ss []
  \\ rpt strip_tac
  \\ full_simp_tac std_ss [reachable_refs_def,MEM_APPEND] \\ metis_tac []);

(* equality *)

val ref_eq_thm = store_thm("ref_eq_thm",
  ``abs_ml_inv conf (RefPtr p1::RefPtr p2::stack) refs
      (r1::r2::roots,heap,be,a,sp) limit ==>
    ((p1 = p2) <=> (r1 = r2)) /\
    ?p1 p2. r1 = Pointer p1 (Word 0w) /\ r2 = Pointer p2 (Word 0w)``,
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ rpt strip_tac
  \\ fs [v_inv_def,INJ_DEF] \\ res_tac \\ fs [] \\ fs []
  \\ eq_tac \\ rw [] \\ fs []);

val num_eq_thm = store_thm("num_eq_thm",
  ``abs_ml_inv conf (Number i1::Number i2::stack) refs
      (r1::r2::roots,heap,be,a,sp) limit ==>
    ((i1 = i2) <=> (r1 = r2)) /\
    r1 = Data (Word (Smallnum i1)) /\
    r2 = Data (Word (Smallnum i2))``,
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ rpt strip_tac
  \\ fs [v_inv_def,INJ_DEF] \\ fs [Smallnum_def]
  \\ Cases_on `i1` \\ Cases_on `i2`
  \\ fs [small_int_def,X_LT_DIV,X_LE_DIV] \\ fs [word_2comp_n2w]);

val Smallnum_i2w = store_thm("Smallnum_i2w",
  ``Smallnum i = i2w (4 * i)``,
  fs [Smallnum_def,integer_wordTheory.i2w_def]
  \\ Cases_on `i` \\ fs []
  \\ reverse IF_CASES_TAC \\ fs [WORD_EQ_NEG]
  THEN1 (`F` by intLib.COOPER_TAC)
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ intLib.COOPER_TAC);

val small_int_IMP_MIN_MAX = store_thm("small_int_IMP_MIN_MAX",
  ``good_dimindex (:'a) /\ small_int (:'a) i ==>
    INT_MIN (:'a) <= 4 * i ∧ 4 * i <= INT_MAX (:'a)``,
  fs [labPropsTheory.good_dimindex_def] \\ rw []
  \\ rfs [small_int_def,dimword_def,
       wordsTheory.INT_MIN_def,wordsTheory.INT_MAX_def]
  \\ intLib.COOPER_TAC);

val num_less_thm = store_thm("num_less_thm",
  ``good_dimindex (:'a) /\ small_int (:'a) i1 /\ small_int (:'a) i2 ==>
    ((i1 < i2) <=> (Smallnum i1 < Smallnum i2:'a word))``,
  fs [integer_wordTheory.WORD_LTi,Smallnum_i2w] \\ strip_tac
  \\ imp_res_tac small_int_IMP_MIN_MAX
  \\ fs [integer_wordTheory.w2i_i2w]
  \\ intLib.COOPER_TAC);

(* permute stack *)

val abs_ml_inv_stack_permute = store_thm("abs_ml_inv_stack_permute",
  ``!xs ys.
      abs_ml_inv conf (MAP FST xs ++ stack) refs (MAP SND xs ++ roots,heap,be,a,sp) limit /\
      set ys SUBSET set xs ==>
      abs_ml_inv conf (MAP FST ys ++ stack) refs (MAP SND ys ++ roots,heap,be,a,sp) limit``,
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
  ``abs_ml_inv conf (xs ++ stack) refs (rs ++ roots,heap,be,a,sp) limit /\
    (LENGTH xs = LENGTH rs) ==>
    abs_ml_inv conf (xs ++ xs ++ stack) refs (rs ++ rs ++ roots,heap,be,a,sp) limit``,
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
      abs_ml_inv conf (xs1 ++ xs2 ++ xs3 ++ stack) refs
                      (rs1 ++ rs2 ++ rs3 ++ roots,heap,be,a,sp) limit /\
      (LENGTH xs1 = LENGTH rs1) /\
      (LENGTH xs2 = LENGTH rs2) /\
      (LENGTH xs3 = LENGTH rs3) ==>
      abs_ml_inv conf (xs1 ++ xs3 ++ xs2 ++ stack) refs
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
  ``abs_ml_inv conf (xs1 ++ stack) refs (roots,heap,be,a,sp) limit ==>
    ?rs1 roots1. (roots = rs1 ++ roots1) /\ (LENGTH rs1 = LENGTH xs1)``,
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,GSYM APPEND_ASSOC]
  \\ rpt strip_tac \\ NTAC 5 (imp_res_tac EVERY2_APPEND1) \\ metis_tac []);

val split2_thm = store_thm("split2_thm",
  ``abs_ml_inv conf (xs1 ++ xs2 ++ stack) refs (roots,heap,be,a,sp) limit ==>
    ?rs1 rs2 roots1. (roots = rs1 ++ rs2 ++ roots1) /\
      (LENGTH rs1 = LENGTH xs1) /\ (LENGTH rs2 = LENGTH xs2)``,
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,GSYM APPEND_ASSOC]
  \\ rpt strip_tac \\ NTAC 5 (imp_res_tac EVERY2_APPEND1) \\ metis_tac []);

val split3_thm = store_thm("split3_thm",
  ``abs_ml_inv conf (xs1 ++ xs2 ++ xs3 ++ stack) refs (roots,heap,be,a,sp) limit ==>
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

val abs_ml_inv_Num = store_thm("abs_ml_inv_Num",
  ``abs_ml_inv conf stack refs (roots,heap,be,a,sp) limit /\ small_int (:α) i ==>
    abs_ml_inv conf (Number i::stack) refs
      (Data (Word ((Smallnum i):'a word))::roots,heap,be,a,sp) limit``,
  fs [abs_ml_inv_def,roots_ok_def,bc_stack_ref_inv_def,v_inv_def]
  \\ fs [reachable_refs_def]
  \\ rw [] \\ fs [] \\ res_tac \\ fs []
  \\ qexists_tac `f` \\ fs []
  \\ rw [] \\ fs [get_refs_def] \\ metis_tac []);

val heap_store_unused_IMP_length = store_thm("heap_store_unused_IMP_length",
  ``heap_store_unused a sp' x heap = (heap2,T) ==>
    heap_length heap2 = heap_length heap``,
  fs [heap_store_unused_def] \\ IF_CASES_TAC \\ fs []
  \\ imp_res_tac heap_lookup_SPLIT \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND,heap_store_lemma]
  \\ rw [] \\ fs [] \\ fs [heap_length_APPEND,el_length_def,heap_length_def]);


(* -------------------------------------------------------
    representation in memory
   ------------------------------------------------------- *)

val pointer_bits_def = Define ` (* pointers have tag and len bits *)
  pointer_bits conf abs_heap n =
    case heap_lookup n abs_heap of
    | SOME (DataElement xs l (BlockTag tag,[])) =>
        maxout_bits (LENGTH xs) conf.len_bits (conf.tag_bits + 2) ||
        maxout_bits tag conf.tag_bits 2 || 1w
    | _ => all_ones (conf.len_bits + conf.tag_bits + 1) 0`

val is_all_ones_def = Define `
  is_all_ones m n w = ((all_ones m n && w) = all_ones m n)`;

val decode_maxout_def = Define `
  decode_maxout l n w =
    if is_all_ones (n+l) n w then NONE else SOME (((n+l) -- n) w >> n)`

val decode_addr_def = Define `
  decode_addr conf w =
    (decode_maxout conf.len_bits (conf.tag_bits + 2) w,
     decode_maxout conf.tag_bits 2 w)`

val get_addr_def = Define `
  get_addr conf n w =
    ((n2w n << shift_length conf) || get_lowerbits conf w)`;

val word_addr_def = Define `
  (word_addr conf (Data (Loc l1 l2)) = Loc l1 l2) /\
  (word_addr conf (Data (Word v)) = Word (v && (~1w))) /\
  (word_addr conf (Pointer n w) = Word (get_addr conf n w))`

val b2w_def = Define `(b2w T = 1w) /\ (b2w F = 0w)`;

val make_byte_header_def = Define `
  make_byte_header conf len =
    (if dimindex (:'a) = 32
     then n2w (len + 4) << (dimindex (:α) - 2 - conf.len_size) || 15w
     else n2w (len + 8) << (dimindex (:α) - 3 - conf.len_size) || 15w):'a word`

val word_payload_def = Define `
  (word_payload ys l (BlockTag n) qs conf =
     (* header: ...00 *)
     (make_header conf (n2w n << 2) (LENGTH ys),
      MAP (word_addr conf) ys,
      (qs = []) /\ (LENGTH ys = l) /\
      encode_header conf (n * 4) (LENGTH ys) =
        SOME (make_header conf (n2w n << 2) (LENGTH ys):'a word))) /\
  (word_payload ys l (RefTag) qs conf =
     (* header: ...10 *)
     (make_header conf 2w (LENGTH ys),
      MAP (word_addr conf) ys,
      (qs = []) /\ (LENGTH ys = l))) /\
  (word_payload ys l (NumTag b) qs conf =
     (* header: ...101 or ...001 *)
     (make_header conf (b2w b << 2 || 1w) (LENGTH qs),
      qs, (ys = []) /\ (LENGTH qs = l))) /\
  (word_payload ys l (BytesTag n) qs conf =
     (* header: ...11 *)
     ((make_byte_header conf n):'a word,
      qs, (ys = []) /\ (LENGTH qs = l) /\
          n < 2 ** (conf.len_size + if dimindex (:'a) = 32 then 2 else 3)))`;

val word_payload_T_IMP = store_thm("word_payload_T_IMP",
  ``word_payload l5 n5 tag r conf = (h:'a word,ts,T) /\
    good_dimindex (:'a) /\ conf.len_size + 2 < dimindex (:'a) ==>
    n5 = LENGTH ts /\
    if word_bit 2 h then l5 = [] else ts = MAP (word_addr conf) l5``,
  Cases_on `tag`
  \\ full_simp_tac(srw_ss())[word_payload_def,make_header_def,
       make_byte_header_def,LET_THM]
  \\ rw [] \\ fs [] \\ fs [word_bit_def]
  \\ rfs [word_or_def,fcpTheory.FCP_BETA,word_lsl_def,wordsTheory.word_index]
  \\ fs [labPropsTheory.good_dimindex_def,fcpTheory.FCP_BETA,
         word_index] \\ rfs []);

val decode_length_def = Define `
  decode_length conf (w:'a word) = w >>> (dimindex (:'a) - conf.len_size)`;

val word_el_def = Define `
  (word_el a (Unused l) conf = word_list_exists (a:'a word) (l+1)) /\
  (word_el a (ForwardPointer n d l) conf =
     one (a,Word (n2w n << 2)) *
     word_list_exists (a + bytes_in_word) l) /\
  (word_el a (DataElement ys l (tag,qs)) conf =
     let (h,ts,c) = word_payload ys l tag qs conf in
       word_list a (Word h :: ts) *
       cond (LENGTH ts < 2 ** (dimindex (:'a) - 4) /\
             decode_length conf h = n2w (LENGTH ts) /\ c))`;

val word_heap_def = Define `
  (word_heap a ([]:'a ml_heap) conf = emp) /\
  (word_heap a (x::xs) conf =
     word_el a x conf *
     word_heap (a + bytes_in_word * n2w (el_length x)) xs conf)`;

val heap_in_memory_store_def = Define `
  heap_in_memory_store heap a sp c s m dm limit <=>
    heap_length heap <= dimword (:'a) DIV 2 ** shift_length c /\
    heap_length heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    shift (:'a) <= shift_length c /\ c.len_size <> 0 /\
    c.len_size + 6 < dimindex (:'a) /\
    shift_length c < dimindex (:'a) /\ Globals ∈ FDOM s /\
    ?curr other.
      byte_aligned curr /\ byte_aligned other /\
      (FLOOKUP s CurrHeap = SOME (Word (curr:'a word))) /\
      (FLOOKUP s OtherHeap = SOME (Word other)) /\
      (FLOOKUP s NextFree = SOME (Word (curr + bytes_in_word * n2w a))) /\
      (FLOOKUP s EndOfHeap = SOME (Word (curr + bytes_in_word * n2w (a + sp)))) /\
      (FLOOKUP s HeapLength = SOME (Word (bytes_in_word * n2w limit))) /\
      (word_heap curr heap c *
       word_heap other (heap_expand limit) c) (fun2set (m,dm))`

val word_ml_inv_def = Define `
  word_ml_inv (heap,be,a,sp) limit c refs stack <=>
    ?hs. abs_ml_inv c (MAP FST stack) refs (hs,heap,be,a,sp) limit /\
         EVERY2 (\v w. word_addr c v = w) hs (MAP SND stack)`

val IMP_THE_EQ = store_thm("IMP_THE_EQ",
  ``x = SOME w ==> THE x = w``,
  full_simp_tac(srw_ss())[]);

val memory_rel_def = Define `
  memory_rel c be refs space st (m:'a word -> 'a word_loc) dm vars <=>
    ∃heap limit a sp.
       heap_in_memory_store heap a sp c st m dm limit ∧
       word_ml_inv (heap,be,a,sp) limit c refs vars ∧
       limit * (dimindex (:α) DIV 8) + 1 < dimword (:α) ∧ space ≤ sp`

val EVERY2_MAP_MAP = store_thm("EVERY2_MAP_MAP",
  ``!xs. EVERY2 P (MAP f xs) (MAP g xs) = EVERY (\x. P (f x) (g x)) xs``,
  Induct \\ full_simp_tac(srw_ss())[]);

val MEM_FIRST_EL = store_thm("MEM_FIRST_EL",
  ``!xs x.
      MEM x xs <=>
      ?n. n < LENGTH xs /\ (EL n xs = x) /\
          !m. m < n ==> (EL m xs <> EL n xs)``,
  srw_tac[][] \\ eq_tac
  THEN1 (srw_tac[][] \\ qexists_tac `LEAST n. EL n xs = x /\ n < LENGTH xs`
    \\ mp_tac (Q.SPEC `\n. EL n xs = x /\ n < LENGTH xs` (GEN_ALL FULL_LEAST_INTRO))
    \\ full_simp_tac(srw_ss())[MEM_EL]
    \\ strip_tac \\ pop_assum (qspec_then `n` mp_tac)
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ imp_res_tac LESS_LEAST \\ full_simp_tac(srw_ss())[] \\ `F` by decide_tac)
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[MEM_EL]
  \\ qexists_tac `n` \\ full_simp_tac(srw_ss())[]);

val ALOOKUP_ZIP_EL = store_thm("ALOOKUP_ZIP_EL",
  ``!xs hs n.
      n < LENGTH xs /\ LENGTH hs = LENGTH xs /\
      (∀m. m < n ⇒ EL m xs ≠ EL n xs) ==>
      ALOOKUP (ZIP (xs,hs)) (EL n xs) = SOME (EL n hs)``,
  Induct \\ Cases_on `hs` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `n` \\ full_simp_tac(srw_ss())[]
  \\ rpt strip_tac \\ first_assum (qspec_then `0` assume_tac)
  \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ first_x_assum match_mp_tac
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ first_x_assum (qspec_then `SUC m` mp_tac) \\ full_simp_tac(srw_ss())[]);

val word_ml_inv_rearrange = store_thm("word_ml_inv_rearrange",
  ``(!x. MEM x ys ==> MEM x xs) ==>
    word_ml_inv (heap,be,a,sp) limit c refs xs ==>
    word_ml_inv (heap,be,a,sp) limit c refs ys``,
  full_simp_tac(srw_ss())[word_ml_inv_def] \\ srw_tac[][]
  \\ qexists_tac `MAP (\y. THE (ALOOKUP (ZIP(xs,hs)) y)) ys`
  \\ full_simp_tac(srw_ss())[EVERY2_MAP_MAP,EVERY_MEM]
  \\ reverse (srw_tac[][])
  THEN1
   (imp_res_tac EVERY2_IMP_EVERY
    \\ res_tac \\ full_simp_tac(srw_ss())[EVERY_MEM,FORALL_PROD]
    \\ first_x_assum match_mp_tac
    \\ imp_res_tac EVERY2_LENGTH
    \\ full_simp_tac(srw_ss())[MEM_ZIP] \\ full_simp_tac(srw_ss())[MEM_FIRST_EL]
    \\ srw_tac[][] \\ qexists_tac `n'` \\ full_simp_tac(srw_ss())[EL_MAP]
    \\ match_mp_tac IMP_THE_EQ
    \\ imp_res_tac ALOOKUP_ZIP_EL)
  \\ qpat_assum `abs_ml_inv c (MAP FST xs) refs (hs,heap,be,a,sp) limit` mp_tac
  \\ `MAP FST ys = MAP FST (MAP (\y. FST y, THE (ALOOKUP (ZIP (xs,hs)) y)) ys) /\
      MAP (λy. THE (ALOOKUP (ZIP (xs,hs)) y)) ys =
        MAP SND (MAP (\y. FST y, THE (ALOOKUP (ZIP (xs,hs)) y)) ys)` by
    (imp_res_tac EVERY2_LENGTH \\ full_simp_tac(srw_ss())[MAP_ZIP,MAP_MAP_o,o_DEF]
     \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[] \\ pop_assum (K all_tac) \\ pop_assum (K all_tac)
  \\ `MAP FST xs = MAP FST (ZIP (MAP FST xs, hs)) /\
      hs = MAP SND (ZIP (MAP FST xs, hs))` by
    (imp_res_tac EVERY2_LENGTH \\ full_simp_tac(srw_ss())[MAP_ZIP])
  \\ pop_assum (fn th => simp [Once th])
  \\ pop_assum (fn th => simp [Once th])
  \\ (abs_ml_inv_stack_permute |> Q.INST [`stack`|->`[]`,`roots`|->`[]`]
        |> SIMP_RULE std_ss [APPEND_NIL] |> SPEC_ALL
        |> ONCE_REWRITE_RULE [CONJ_COMM] |> REWRITE_RULE [GSYM AND_IMP_INTRO]
        |> match_mp_tac)
  \\ full_simp_tac(srw_ss())[SUBSET_DEF,FORALL_PROD]
  \\ imp_res_tac EVERY2_LENGTH
  \\ full_simp_tac(srw_ss())[MEM_ZIP,MEM_MAP,PULL_EXISTS,FORALL_PROD]
  \\ srw_tac[][] \\ res_tac
  \\ `MEM p_1 (MAP FST xs)` by (fs[MEM_MAP,EXISTS_PROD] \\ metis_tac [])
  \\ full_simp_tac(srw_ss())[MEM_FIRST_EL]
  \\ qexists_tac `n'` \\ rev_full_simp_tac(srw_ss())[EL_MAP]
  \\ match_mp_tac IMP_THE_EQ
  \\ qpat_assum `EL n' xs = (p_1,p_2')` (fn th => full_simp_tac(srw_ss())[GSYM th])
  \\ match_mp_tac ALOOKUP_ZIP_EL \\ full_simp_tac(srw_ss())[]);

val memory_rel_rearrange = store_thm("memory_rel_rearrange",
  ``(∀x. MEM x ys ⇒ MEM x xs) ⇒
    memory_rel c be refs sp st m dm xs ==>
    memory_rel c be refs sp st m dm ys``,
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ qpat_assum `word_ml_inv _ _ _ _ _` mp_tac
  \\ match_mp_tac word_ml_inv_rearrange \\ fs []);

val word_ml_inv_Unit = store_thm("word_ml_inv_Unit",
  ``word_ml_inv (heap,F,a,sp) limit c refs ws /\
    good_dimindex (:'a) ==>
    word_ml_inv (heap,F,a,sp) limit c refs
      ((Unit,Word (2w:'a word))::ws)``,
  fs [word_ml_inv_def,PULL_EXISTS] \\ rw []
  \\ qexists_tac `Data (Word 2w)`
  \\ qexists_tac `hs` \\ fs [word_addr_def]
  \\ fs [bvlSemTheory.Unit_def,EVAL ``tuple_tag``]
  \\ drule (GEN_ALL cons_thm_EMPTY)
  \\ disch_then (qspec_then `0` mp_tac)
  \\ fs [labPropsTheory.good_dimindex_def,dimword_def]
  \\ fs [BlockNil_def]);

val memory_rel_Unit = store_thm("memory_rel_Unit",
  ``memory_rel c F refs sp st m dm xs /\ good_dimindex (:'a) ==>
    memory_rel c F refs sp st m dm ((Unit,Word (2w:'a word))::xs)``,
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ match_mp_tac word_ml_inv_Unit \\ fs []);

val get_lowerbits_LSL_shift_length = store_thm("get_lowerbits_LSL_shift_length",
  ``get_lowerbits conf a >>> shift_length conf = 0w``,
  Cases_on `a`
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss]
       [word_index, get_lowerbits_def, shift_length_def])

val get_real_addr_def = Define `
  get_real_addr conf st (w:'a word) =
    let k = shift (:α) in
      case FLOOKUP st CurrHeap of
      | SOME (Word curr) =>
          SOME (curr + (w >>> (shift_length conf) << k))
      | _ => NONE`

val get_real_offset_def = Define `
  get_real_offset (w:'a word) =
    if dimindex (:'a) = 32
    then SOME (w + bytes_in_word) else SOME (w << 1 + bytes_in_word)`

val get_real_addr_get_addr = store_thm("get_real_addr_get_addr",
  ``heap_length heap <= dimword (:'a) DIV 2 ** shift_length c /\
    heap_lookup n heap = SOME anything /\
    FLOOKUP st CurrHeap = SOME (Word (curr:'a word)) /\
    good_dimindex (:'a) ==>
    get_real_addr c st (get_addr c n w) = SOME (curr + n2w n * bytes_in_word)``,
  fs [X_LE_DIV] \\ fs [get_addr_def,get_real_addr_def] \\ strip_tac
  \\ imp_res_tac copying_gcTheory.heap_lookup_LESS \\ fs []
  \\ `w2n ((n2w n):'a word) * 2 ** shift_length c < dimword (:'a)` by
   (`n < dimword (:'a)` by
     (Cases_on `2 ** (shift_length c)` \\ fs []
      \\ Cases_on `n'` \\ fs [MULT_CLAUSES])
    \\ match_mp_tac LESS_LESS_EQ_TRANS
    \\ once_rewrite_tac [CONJ_COMM]
    \\ asm_exists_tac \\ fs [])
  \\ drule lsl_lsr \\ fs [get_lowerbits_LSL_shift_length]
  \\ fs [] \\ rw []
  \\ fs [labPropsTheory.good_dimindex_def,dimword_def] \\ rw []
  \\ rfs [WORD_MUL_LSL,word_mul_n2w,shift_def,bytes_in_word_def])

val get_real_offset_thm = store_thm("get_real_offset_thm",
  ``good_dimindex (:'a) ==>
    get_real_offset (n2w (4 * index)) =
      SOME (bytes_in_word + n2w index * bytes_in_word:'a word)``,
  fs [labPropsTheory.good_dimindex_def,dimword_def] \\ rw []
  \\ fs [get_real_offset_def,bytes_in_word_def,word_mul_n2w,WORD_MUL_LSL]);

val word_heap_APPEND = store_thm("word_heap_APPEND",
  ``!xs ys a.
      word_heap a (xs ++ ys) conf =
      word_heap a xs conf *
      word_heap (a + bytes_in_word * n2w (heap_length xs)) ys conf``,
  Induct \\ full_simp_tac(srw_ss())[word_heap_def,heap_length_def,
              SEP_CLAUSES,STAR_ASSOC]
  \\ full_simp_tac(srw_ss())[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]);

val FORALL_WORD = store_thm("FORALL_WORD",
  ``(!v:'a word. P v) <=> !n. n < dimword (:'a) ==> P (n2w n)``,
  eq_tac \\ rw [] \\ Cases_on `v` \\ fs []);

val BlockNil_and_lemma = store_thm("BlockNil_and_lemma",
  ``good_dimindex (:'a) ==>
    (-2w && 16w * tag + 2w) = 16w * tag + 2w:'a word``,
  `!w:word64. (-2w && 16w * w + 2w) = 16w * w + 2w` by blastLib.BBLAST_TAC
  \\ `!w:word32. (-2w && 16w * w + 2w) = 16w * w + 2w` by blastLib.BBLAST_TAC
  \\ fs [GSYM word_mul_n2w,GSYM word_add_n2w]
  \\ rfs [dimword_def,FORALL_WORD]
  \\ Cases_on `tag` \\ fs [labPropsTheory.good_dimindex_def] \\ rw []
  \\ fs [word_mul_n2w,word_add_n2w,word_2comp_n2w,word_and_n2w]
  \\ rfs [dimword_def] \\ fs []);

val word_ml_inv_num_lemma = store_thm("word_ml_inv_num_lemma",
  ``good_dimindex (:'a) ==> (-2w && 4w * v) = 4w * v:'a word``,
  `!w:word64. (-2w && 4w * w) = 4w * w` by blastLib.BBLAST_TAC
  \\ `!w:word32. (-2w && 4w * w) = 4w * w` by blastLib.BBLAST_TAC
  \\ rfs [dimword_def,FORALL_WORD]
  \\ fs [labPropsTheory.good_dimindex_def] \\ rw []
  \\ Cases_on `v` \\ fs [word_mul_n2w,word_and_n2w,word_2comp_n2w]
  \\ rfs [dimword_def]);

val word_ml_inv_num = store_thm("word_ml_inv_num",
  ``word_ml_inv (heap,F,a,sp) limit c s.refs ws /\
    good_dimindex (:'a) /\
    small_enough_int (&n) ==>
    word_ml_inv (heap,F,a,sp) limit c s.refs
      ((Number (&n),Word (n2w (4 * n):'a word))::ws)``,
  fs [word_ml_inv_def,PULL_EXISTS] \\ rw []
  \\ qexists_tac `Data (Word (Smallnum (&n)))`
  \\ qexists_tac `hs` \\ fs [] \\ conj_tac
  THEN1
   (match_mp_tac abs_ml_inv_Num \\ fs []
    \\ fs [bviSemTheory.small_enough_int_def]
    \\ fs [small_int_def,Smallnum_def]
    \\ fs [labPropsTheory.good_dimindex_def,dimword_def] \\ rw [])
  \\ fs [word_addr_def,Smallnum_def,GSYM word_mul_n2w]
  \\ match_mp_tac word_ml_inv_num_lemma \\ fs []);

val word_ml_inv_zero = save_thm("word_ml_inv_zero",
  word_ml_inv_num |> Q.INST [`n`|->`0`] |> SIMP_RULE (srw_ss()) [])

val word_ml_inv_neg_num_lemma = store_thm("word_ml_inv_neg_num_lemma",
  ``good_dimindex (:'a) ==> (-2w && -4w * v) = -4w * v:'a word``,
  `!w:word64. (-2w && -4w * w) = -4w * w` by blastLib.BBLAST_TAC
  \\ `!w:word32. (-2w && -4w * w) = -4w * w` by blastLib.BBLAST_TAC
  \\ rfs [dimword_def,FORALL_WORD]
  \\ fs [labPropsTheory.good_dimindex_def] \\ rw []
  \\ Cases_on `v` \\ fs [word_mul_n2w,word_and_n2w,word_2comp_n2w]
  \\ rfs [dimword_def]);

val word_ml_inv_neg_num = store_thm("word_ml_inv_neg_num",
  ``word_ml_inv (heap,F,a,sp) limit c s.refs ws /\
    good_dimindex (:'a) /\
    small_enough_int (-&n) /\ n <> 0 ==>
    word_ml_inv (heap,F,a,sp) limit c s.refs
      ((Number (-&n),Word (-n2w (4 * n):'a word))::ws)``,
  fs [word_ml_inv_def,PULL_EXISTS] \\ rw []
  \\ qexists_tac `Data (Word (Smallnum (-&n)))`
  \\ qexists_tac `hs` \\ fs [] \\ conj_tac
  THEN1
   (match_mp_tac abs_ml_inv_Num \\ fs []
    \\ fs [bviSemTheory.small_enough_int_def]
    \\ fs [small_int_def,Smallnum_def]
    \\ fs [labPropsTheory.good_dimindex_def,dimword_def] \\ rw [])
  \\ fs [word_addr_def,Smallnum_def,GSYM word_mul_n2w]
  \\ match_mp_tac word_ml_inv_neg_num_lemma \\ fs []);

val word_list_APPEND = store_thm("word_list_APPEND",
  ``!xs ys a. word_list a (xs ++ ys) =
              word_list a xs * word_list (a + n2w (LENGTH xs) * bytes_in_word) ys``,
  Induct \\ full_simp_tac(srw_ss())[word_list_def,SEP_CLAUSES,STAR_ASSOC,ADD1,
                GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]);

val clean_tac = rpt var_eq_tac \\ rpt (qpat_assum `T` kall_tac)
fun rpt_drule th = drule (th |> GEN_ALL) \\ rpt (disch_then drule \\ fs [])

val memory_rel_El = store_thm("memory_rel_El",
  ``memory_rel c be refs sp st m dm
     ((Block tag vals,ptr)::(Number (&index),i)::vars) /\
    good_dimindex (:'a) /\
    index < LENGTH vals ==>
    ?ptr_w i_w x y:'a word.
      ptr = Word ptr_w /\ i = Word i_w /\
      get_real_addr c st ptr_w = SOME x /\
      get_real_offset i_w = SOME y /\
      (x + y) IN dm /\
      memory_rel c be refs sp st m dm
        ((EL index vals,m (x + y))::
         (Block tag vals,ptr)::(Number (&index),i)::vars)``,
  rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ fs [memory_rel_def,PULL_EXISTS] \\ rw []
  \\ asm_exists_tac \\ fs []
  \\ fs [word_ml_inv_def,PULL_EXISTS] \\ clean_tac
  \\ rpt_drule el_thm \\ strip_tac
  \\ asm_exists_tac \\ fs []
  \\ Cases_on `v` \\ fs [heap_el_def]
  \\ every_case_tac \\ fs [] \\ clean_tac
  \\ fs [GSYM CONJ_ASSOC,word_addr_def]
  \\ fs [heap_in_memory_store_def]
  \\ rpt_drule get_real_addr_get_addr \\ fs []
  \\ disch_then kall_tac
  \\ `word_addr c v' = Word (n2w (4 * index))` by
   (imp_res_tac heap_lookup_SPLIT
    \\ qpat_assum `abs_ml_inv _ _ _ _ _` kall_tac
    \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def,BlockRep_def]
    \\ clean_tac
    \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
    \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
    \\ `small_int (:α) (&index)` by
     (fs [small_int_def,intLib.COOPER_CONV ``-&n <= &k``]
      \\ fs [labPropsTheory.good_dimindex_def,dimword_def] \\ rw [] \\ rfs [])
    \\ fs [] \\ clean_tac \\ fs [word_addr_def]
    \\ fs [Smallnum_def,GSYM word_mul_n2w,word_ml_inv_num_lemma] \\ NO_TAC)
  \\ fs [] \\ fs [get_real_offset_thm]
  \\ drule LESS_LENGTH
  \\ strip_tac \\ fs [] \\ clean_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_LENGTH_APPEND]
  \\ imp_res_tac heap_lookup_SPLIT
  \\ qcase_tac `heap = ha ++ DataElement (ys1 ++ y::ys2) tt yy::hb`
  \\ PairCases_on `yy`
  \\ qpat_assum `abs_ml_inv _ _ _ _ _` kall_tac
  \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def,BlockRep_def]
  \\ clean_tac
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
  \\ fs [word_list_def,word_list_APPEND]
  \\ SEP_R_TAC \\ fs []);

val memory_rel_Deref = store_thm("memory_rel_Deref",
  ``memory_rel c be refs sp st m dm
     ((RefPtr nn,ptr)::(Number (&index),i)::vars) /\
    FLOOKUP refs nn = SOME (ValueArray vals) /\
    good_dimindex (:'a) /\
    index < LENGTH vals ==>
    ?ptr_w i_w x y:'a word.
      ptr = Word ptr_w /\ i = Word i_w /\
      get_real_addr c st ptr_w = SOME x /\
      get_real_offset i_w = SOME y /\
      (x + y) IN dm /\
      memory_rel c be refs sp st m dm
        ((EL index vals,m (x + y))::
         (RefPtr nn,ptr)::(Number (&index),i)::vars)``,
  rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ fs [memory_rel_def,PULL_EXISTS] \\ rw []
  \\ asm_exists_tac \\ fs []
  \\ fs [word_ml_inv_def,PULL_EXISTS] \\ clean_tac
  \\ rpt_drule deref_thm \\ fs [FLOOKUP_DEF]
  \\ disch_then drule \\ strip_tac
  \\ asm_exists_tac \\ fs []
  \\ Cases_on `v` \\ fs [heap_el_def]
  \\ every_case_tac \\ fs [] \\ clean_tac
  \\ fs [GSYM CONJ_ASSOC,word_addr_def]
  \\ fs [heap_in_memory_store_def]
  \\ rpt_drule get_real_addr_get_addr \\ fs []
  \\ disch_then kall_tac
  \\ `word_addr c v' = Word (n2w (4 * index))` by
   (qpat_assum `abs_ml_inv _ _ _ _ _` kall_tac
    \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def,BlockRep_def]
    \\ clean_tac
    \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
    \\ `reachable_refs (RefPtr nn::Number (&index)::MAP FST vars) refs nn` by
     (fs [reachable_refs_def] \\ qexists_tac `RefPtr nn` \\ fs []
      \\ fs [get_refs_def] \\ NO_TAC) \\ res_tac
    \\ pop_assum mp_tac
    \\ simp_tac std_ss [bc_ref_inv_def]
    \\ fs [FLOOKUP_DEF,RefBlock_def] \\ strip_tac \\ clean_tac
    \\ imp_res_tac heap_lookup_SPLIT
    \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
    \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
    \\ `small_int (:α) (&index)` by
     (fs [small_int_def,intLib.COOPER_CONV ``-&n <= &k``]
      \\ fs [labPropsTheory.good_dimindex_def,dimword_def]
      \\ rw [] \\ rfs [] \\ fs [] \\ NO_TAC)
    \\ fs [] \\ clean_tac \\ fs [word_addr_def]
    \\ fs [Smallnum_def,GSYM word_mul_n2w,word_ml_inv_num_lemma] \\ NO_TAC)
  \\ fs [] \\ fs [get_real_offset_thm]
  \\ drule LESS_LENGTH
  \\ strip_tac \\ fs [] \\ clean_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_LENGTH_APPEND]
  \\ imp_res_tac heap_lookup_SPLIT
  \\ PairCases_on `b` \\ fs []
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
  \\ Cases_on `b0` \\ fs [word_payload_def]
  \\ fs [word_list_def,word_list_APPEND,SEP_CLAUSES] \\ fs [SEP_F_def]
  \\ SEP_R_TAC \\ fs []);

val LENGTH_EQ_1 = store_thm("LENGTH_EQ_1",
  ``(LENGTH xs = 1 <=> ?a1. xs = [a1]) /\
    (1 = LENGTH xs <=> ?a1. xs = [a1])``,
  rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `xs` \\ fs [LENGTH_NIL]);

val LENGTH_EQ_2 = store_thm("LENGTH_EQ_2",
  ``(LENGTH xs = 2 <=> ?a1 a2. xs = [a1;a2]) /\
    (2 = LENGTH xs <=> ?a1 a2. xs = [a1;a2])``,
  rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `xs` \\ fs []
  \\ Cases_on `t` \\ fs [LENGTH_NIL]);

val LENGTH_EQ_3 = store_thm("LENGTH_EQ_3",
  ``(LENGTH xs = 3 <=> ?a1 a2 a3. xs = [a1;a2;a3]) /\
    (3 = LENGTH xs <=> ?a1 a2 a3. xs = [a1;a2;a3])``,
  rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `xs` \\ fs []
  \\ Cases_on `t` \\ fs [LENGTH_NIL]
  \\ Cases_on `t'` \\ fs [LENGTH_NIL]
  \\ Cases_on `t` \\ fs [LENGTH_NIL]);

val memory_rel_Update = store_thm("memory_rel_Update",
  ``memory_rel c be refs sp st m dm
     ((h,w)::(RefPtr nn,ptr)::(Number (&index),i)::vars) /\
    FLOOKUP refs nn = SOME (ValueArray vals) /\
    good_dimindex (:'a) /\
    index < LENGTH vals ==>
    ?ptr_w i_w x y:'a word.
      ptr = Word ptr_w /\ i = Word i_w /\
      get_real_addr c st ptr_w = SOME x /\
      get_real_offset i_w = SOME y /\
      (x + y) IN dm /\
      memory_rel c be (refs |+ (nn,ValueArray (LUPDATE h index vals))) sp st
        ((x + y =+ w) m) dm
        ((h,w)::(RefPtr nn,ptr)::(Number (&index),i)::vars)``,
  rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ fs [memory_rel_def,PULL_EXISTS] \\ rw []
  \\ fs [word_ml_inv_def,PULL_EXISTS] \\ clean_tac
  \\ rpt_drule (update_ref_thm1 |> Q.INST [`xs`|->`[xx]`]
                  |> SIMP_RULE (srw_ss()) [])
  \\ fs [LENGTH_EQ_1,PULL_EXISTS]
  \\ rpt strip_tac \\ fs [] \\ clean_tac
  \\ rewrite_tac [GSYM CONJ_ASSOC]
  \\ once_rewrite_tac [METIS_PROVE [] ``b1 /\ b2 /\ b3 <=> b2 /\ b1 /\ b3:bool``]
  \\ asm_exists_tac \\ fs [word_addr_def]
  \\ fs [heap_deref_def] \\ every_case_tac \\ fs [] \\ clean_tac
  \\ fs [heap_in_memory_store_def]
  \\ rpt_drule get_real_addr_get_addr \\ fs []
  \\ disch_then kall_tac
  \\ `word_addr c v'' = Word (n2w (4 * index)) /\ n = LENGTH l` by
   (qpat_assum `abs_ml_inv _ _ _ _ _` kall_tac
    \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def,BlockRep_def]
    \\ clean_tac
    \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
    \\ `reachable_refs (h::RefPtr nn::Number (&index)::MAP FST vars) refs nn` by
     (fs [reachable_refs_def] \\ qexists_tac `RefPtr nn` \\ fs []
      \\ fs [get_refs_def] \\ NO_TAC) \\ res_tac
    \\ pop_assum mp_tac
    \\ simp_tac std_ss [bc_ref_inv_def]
    \\ fs [FLOOKUP_DEF,RefBlock_def] \\ strip_tac \\ clean_tac
    \\ imp_res_tac heap_lookup_SPLIT
    \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
    \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
    \\ `small_int (:α) (&index)` by
     (fs [small_int_def,intLib.COOPER_CONV ``-&n <= &k``]
      \\ fs [labPropsTheory.good_dimindex_def,dimword_def]
      \\ rw [] \\ rfs [] \\ fs [] \\ NO_TAC)
    \\ fs [] \\ clean_tac \\ fs [word_addr_def]
    \\ fs [Smallnum_def,GSYM word_mul_n2w,word_ml_inv_num_lemma] \\ NO_TAC)
  \\ fs [] \\ fs [get_real_offset_thm]
  \\ fs [GSYM RefBlock_def]
  \\ imp_res_tac heap_lookup_SPLIT \\ fs [] \\ clean_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [heap_store_RefBlock_thm,LENGTH_LUPDATE] \\ clean_tac
  \\ fs [heap_length_APPEND]
  \\ fs [heap_length_def,el_length_def,RefBlock_def]
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR,SEP_CLAUSES]
  \\ fs [word_list_def,SEP_CLAUSES]
  \\ `index < LENGTH l` by fs []
  \\ drule LESS_LENGTH
  \\ strip_tac \\ fs [] \\ clean_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND,LUPDATE_LENGTH]
  \\ fs [word_list_def,word_list_APPEND,SEP_CLAUSES,heap_length_def]
  \\ fs [el_length_def,SUM_APPEND]
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ SEP_R_TAC \\ fs []
  \\ SEP_W_TAC \\ fs [AC STAR_ASSOC STAR_COMM]);

val make_cons_ptr_def = Define `
  make_cons_ptr conf nf tag len =
    Word (nf << (shift_length conf - shift (:'a)) || (1w:'a word)
            || get_lowerbits conf (Word (ptr_bits conf tag len)))`;

val make_ptr_def = Define `
  make_ptr conf nf tag len =
    Word (nf << (shift_length conf - shift (:'a)) || (1w:'a word))`;

val store_list_def = Define `
  (store_list a [] (m:'a word -> 'a word_loc) dm = SOME m) /\
  (store_list a (w::ws) m dm =
     if a IN dm then
       store_list (a + bytes_in_word) ws ((a =+ w) m) dm
     else NONE)`

val minus_lemma = prove(
  ``-1w * (bytes_in_word * w) = bytes_in_word * -w``,
  fs []);

val bytes_in_word_mul_eq_shift = store_thm("bytes_in_word_mul_eq_shift",
  ``good_dimindex (:'a) ==>
    (bytes_in_word * w = (w << shift (:'a)):'a word)``,
  fs [bytes_in_word_def,shift_def,WORD_MUL_LSL,word_mul_n2w]
  \\ fs [labPropsTheory.good_dimindex_def,dimword_def] \\ rw [] \\ rfs []);

val n2w_lsr_eq_0 = store_thm("n2w_lsr_eq_0",
  ``n DIV 2 ** k = 0 /\ n < dimword (:'a) ==> n2w n >>> k = 0w:'a word``,
  rw [] \\ simp_tac std_ss [GSYM w2n_11,w2n_lsr] \\ fs []);

val LESS_EXO_SUB = prove(
  ``n < 2 ** (k - m) ==> n < 2n ** k``,
  rw [] \\ match_mp_tac LESS_LESS_EQ_TRANS
  \\ asm_exists_tac \\ fs []);

val LESS_EXO_SUB_ALT = prove(
  ``m <= k ==> n < 2 ** (k - m) ==> n * 2 ** m < 2n ** k``,
  rw [] \\ match_mp_tac LESS_LESS_EQ_TRANS
  \\ qexists_tac `2 ** (k - m) * 2 ** m`
  \\ fs [GSYM EXP_ADD]);

val less_pow_dimindex_sub_imp = prove(
  ``n < 2 ** (dimindex (:'a) - k) ==> n < dimword (:'a)``,
  fs [dimword_def] \\ metis_tac [LESS_EXO_SUB]);

val encode_header_NEQ_0 = store_thm("encode_header_NEQ_0",
  ``encode_header c n k = SOME w ==> w <> 0w``,
  fs [encode_header_def] \\ rw []
  \\ fs [make_header_def,LET_DEF]
  \\ full_simp_tac (srw_ss()++wordsLib.WORD_BIT_EQ_ss) []
  \\ qexists_tac `0` \\ fs [] \\ EVAL_TAC);

val encode_header_IMP = prove(
  ``encode_header c tag len = SOME (hd:'a word) /\
    c.len_size + 6 < dimindex (:'a) /\ good_dimindex (:'a) ==>
    len < 2 ** (dimindex (:'a) - 4) /\
    decode_length c hd = n2w len``,
  fs [encode_header_def] \\ rw [make_header_def] \\ fs [decode_length_def]
  \\ `3w >>> (dimindex (:α) − c.len_size) = 0w:'a word` by
      (match_mp_tac n2w_lsr_eq_0
       \\ fs [labPropsTheory.good_dimindex_def,dimword_def]
       \\ fs [DIV_EQ_X]
       \\ match_mp_tac LESS_LESS_EQ_TRANS
       \\ qexists_tac `2 ** 2`
       \\ strip_tac \\ TRY (EVAL_TAC \\ NO_TAC)
       \\ simp_tac std_ss [EXP_BASE_LE_IFF] \\ fs [])
  \\ `n2w tag << 2 ⋙ (dimindex (:α) - c.len_size) = 0w:'a word` by
      (fs [WORD_MUL_LSL,word_mul_n2w]
       \\ match_mp_tac n2w_lsr_eq_0
       \\ rpt strip_tac \\ TRY (match_mp_tac LESS_DIV_EQ_ZERO)
       \\ `2 ** (dimindex (:α) − c.len_size) =
           2n ** 2 * 2 ** (dimindex (:α) − (c.len_size + 2))` by
              (full_simp_tac std_ss [GSYM EXP_ADD] \\ fs []) \\ fs []
       \\ `4 * tag = tag * 2 ** 2` by fs []
       \\ asm_rewrite_tac [dimword_def]
       \\ match_mp_tac (MP_CANON LESS_EXO_SUB_ALT)
       \\ full_simp_tac std_ss [SUB_PLUS |> ONCE_REWRITE_RULE [ADD_COMM]]
       \\ imp_res_tac LESS_EXO_SUB \\ fs [])
  \\ fs [] \\ match_mp_tac lsl_lsr
  \\ imp_res_tac less_pow_dimindex_sub_imp \\ fs []
  \\ `dimword (:'a) = 2 ** c.len_size * 2 ** (dimindex (:α) − c.len_size)`
        suffices_by fs []
  \\ fs [GSYM EXP_ADD,dimword_def]);

val word_list_exists_thm = store_thm("word_list_exists_thm",
  ``(word_list_exists a 0 = emp) /\
    (word_list_exists a (SUC n) =
     SEP_EXISTS w. one (a,w) * word_list_exists (a + bytes_in_word) n)``,
  full_simp_tac(srw_ss())[word_heap_def,word_list_exists_def,
          LENGTH_NIL,FUN_EQ_THM,ADD1,
          SEP_EXISTS_THM,cond_STAR,word_list_def,word_el_def,SEP_CLAUSES]
  \\ srw_tac[][] \\ eq_tac \\ srw_tac[][]
  THEN1
   (Cases_on `xs` \\ full_simp_tac(srw_ss())[ADD1]
    \\ full_simp_tac(srw_ss())[word_list_def]
    \\ qexists_tac `h` \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `t` \\ full_simp_tac(srw_ss())[SEP_CLAUSES])
  \\ qexists_tac `w::xs`
  \\ full_simp_tac(srw_ss())[word_list_def,ADD1,STAR_ASSOC,cond_STAR]);

val word_list_exists_ADD = store_thm("word_list_exists_ADD",
  ``!m n a.
      word_list_exists a (m + n) =
      word_list_exists a m *
      word_list_exists (a + bytes_in_word * n2w m) n``,
  Induct \\ full_simp_tac(srw_ss())[word_list_exists_thm,SEP_CLAUSES,ADD_CLAUSES]
  \\ full_simp_tac(srw_ss())[STAR_ASSOC,ADD1,
        GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]);

val store_list_thm = store_thm("store_list_thm",
  ``!xs a frame m dm.
      (word_list_exists a (LENGTH xs) * frame) (fun2set (m,dm)) ==>
      ?m1.
        store_list a xs m dm = SOME m1 /\
        (word_list a xs * frame) (fun2set (m1,dm))``,
  Induct \\ fs [store_list_def,word_list_exists_thm,word_list_def,SEP_CLAUSES]
  \\ fs [SEP_EXISTS_THM,PULL_EXISTS] \\ rpt strip_tac
  \\ SEP_R_TAC \\ fs [] \\ SEP_W_TAC
  \\ SEP_F_TAC \\ rw [] \\ fs [AC STAR_COMM STAR_ASSOC])

val EVERY2_f_EQ = prove(
  ``!rs ws f. EVERY2 (\v w. f v = w) rs ws <=> MAP f rs = ws``,
  Induct \\ fs [] \\ rw [] \\ eq_tac \\ rw [] \\ fs []);

val word_heap_heap_expand = store_thm("word_heap_heap_expand",
  ``word_heap a (heap_expand n) conf = word_list_exists a n``,
  Cases_on `n` \\ full_simp_tac(srw_ss())[heap_expand_def]
  \\ fs [word_heap_def,word_list_exists_def,LENGTH_NIL,FUN_EQ_THM,ADD1,
         SEP_EXISTS_THM,cond_STAR,word_list_def,word_el_def,SEP_CLAUSES])

val get_lowerbits_or_1 = prove(
  ``get_lowerbits c v = (get_lowerbits c v || 1w)``,
  Cases_on `v` \\ fs [get_lowerbits_def]);

val memory_rel_Cons = store_thm("memory_rel_Cons",
  ``memory_rel c be refs sp st m dm (ZIP (vals,ws) ++ vars) /\
    LENGTH vals = LENGTH (ws:'a word_loc list) /\ vals <> [] /\
    encode_header c (4 * tag) (LENGTH ws) = SOME hd /\
    LENGTH ws < sp /\ good_dimindex (:'a) ==>
    ?eoh (curr:'a word) m1.
      FLOOKUP st EndOfHeap = SOME (Word eoh) /\
      FLOOKUP st CurrHeap = SOME (Word curr) /\
      let w = eoh - bytes_in_word * n2w (LENGTH ws + 1) in
        store_list w (Word hd::ws) m dm = SOME m1 /\
        memory_rel c be refs (sp - (LENGTH ws + 1))
          (st |+ (EndOfHeap,Word w)) m1 dm
          ((Block tag vals,make_cons_ptr c (w - curr) tag (LENGTH ws))::vars)``,
  simp_tac std_ss [LET_THM]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ fs [memory_rel_def,PULL_EXISTS] \\ rw []
  \\ fs [word_ml_inv_def,PULL_EXISTS] \\ clean_tac
  \\ fs [MAP_ZIP]
  \\ drule (GEN_ALL cons_thm)
  \\ disch_then (qspecl_then [`tag`] strip_assume_tac)
  \\ rfs [] \\ fs [] \\ clean_tac
  \\ rewrite_tac [GSYM CONJ_ASSOC]
  \\ once_rewrite_tac [METIS_PROVE [] ``b1 /\ b2 /\ b3 <=> b2 /\ b1 /\ b3:bool``]
  \\ asm_exists_tac \\ fs [word_addr_def]
  \\ fs [heap_in_memory_store_def,FLOOKUP_UPDATE]
  \\ qpat_abbrev_tac `ll = el_length _`
  \\ `ll = LENGTH ws + 1` by (UNABBREV_ALL_TAC \\ EVAL_TAC \\ fs [] \\ NO_TAC)
  \\ UNABBREV_ALL_TAC \\ fs []
  \\ `n2w (a + sp' - (LENGTH ws + 1)) =
      n2w (a + sp') - n2w (LENGTH ws + 1):'a word`
          by fs [addressTheory.word_arith_lemma2]
  \\ fs [WORD_LEFT_ADD_DISTRIB,get_addr_def,make_cons_ptr_def,get_lowerbits_def]
  \\ fs [el_length_def,BlockRep_def]
  \\ imp_res_tac heap_store_unused_IMP_length \\ fs []
  \\ fs [copying_gcTheory.EVERY2_APPEND,minus_lemma]
  \\ fs [bytes_in_word_mul_eq_shift]
  \\ fs [GSYM bytes_in_word_mul_eq_shift]
  \\ `LENGTH ws + 1 <= sp'` by decide_tac
  \\ pop_assum mp_tac \\ simp_tac std_ss [LESS_EQ_EXISTS] \\ strip_tac
  \\ clean_tac \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [heap_store_unused_def,el_length_def]
  \\ every_case_tac \\ fs []
  \\ imp_res_tac heap_lookup_SPLIT \\ fs [] \\ clean_tac
  \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ fs [heap_store_lemma] \\ clean_tac \\ fs []
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def,
         SEP_CLAUSES,word_heap_heap_expand]
  \\ fs [word_list_exists_ADD |> Q.SPECL [`m`,`n+1`]]
  \\ `(make_header c (n2w tag << 2) (LENGTH ws)) = hd` by
       (fs [encode_header_def,make_header_def] \\ every_case_tac \\ fs []
        \\ fs [WORD_MUL_LSL,word_mul_n2w,EXP_ADD] \\ NO_TAC)
  \\ fs [] \\ drule encode_header_IMP \\ fs [] \\ strip_tac
  \\ simp [WORD_MUL_LSL,word_mul_n2w]
  \\ fs [SEP_CLAUSES,STAR_ASSOC]
  \\ `LENGTH ws + 1 = LENGTH (Word hd::ws)` by fs []
  \\ full_simp_tac std_ss []
  \\ assume_tac store_list_thm
  \\ SEP_F_TAC \\ strip_tac \\ fs []
  \\ fs [EVERY2_f_EQ] \\ clean_tac \\ fs []
  \\ fs [el_length_def,heap_length_APPEND,heap_length_heap_expand,
         GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [AC STAR_ASSOC STAR_COMM] \\ fs [STAR_ASSOC]
  \\ pop_assum mp_tac \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ fs [AC STAR_ASSOC STAR_COMM] \\ fs [STAR_ASSOC]
  \\ rpt strip_tac
  \\ simp [Once get_lowerbits_or_1]);

val memory_rel_Ref = store_thm("memory_rel_Ref",
  ``memory_rel c be refs sp st m dm (ZIP (vals,ws) ++ vars) /\
    LENGTH vals = LENGTH (ws:'a word_loc list) /\
    encode_header c 2 (LENGTH ws) = SOME hd /\ ~(new IN FDOM refs) /\
    LENGTH ws < sp /\ good_dimindex (:'a) ==>
    ?eoh (curr:'a word) m1.
      FLOOKUP st EndOfHeap = SOME (Word eoh) /\
      FLOOKUP st CurrHeap = SOME (Word curr) /\
      let w = eoh - bytes_in_word * n2w (LENGTH ws + 1) in
        store_list w (Word hd::ws) m dm = SOME m1 /\
        memory_rel c be (refs |+ (new,ValueArray vals)) (sp - (LENGTH ws + 1))
          (st |+ (EndOfHeap,Word w)) m1 dm
          ((RefPtr new,make_ptr c (w - curr) 0w (LENGTH ws))::vars)``,
  simp_tac std_ss [LET_THM]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ fs [memory_rel_def,PULL_EXISTS] \\ rw []
  \\ fs [word_ml_inv_def,PULL_EXISTS] \\ clean_tac
  \\ fs [MAP_ZIP]
  \\ drule (GEN_ALL new_ref_thm)
  \\ disch_then (qspecl_then [`new`] strip_assume_tac)
  \\ rfs [] \\ fs [] \\ clean_tac
  \\ rewrite_tac [GSYM CONJ_ASSOC]
  \\ once_rewrite_tac [METIS_PROVE [] ``b1 /\ b2 /\ b3 <=> b2 /\ b1 /\ b3:bool``]
  \\ drule pop_thm \\ fs []
  \\ strip_tac \\ asm_exists_tac \\ fs [word_addr_def]
  \\ fs [heap_in_memory_store_def,FLOOKUP_UPDATE]
  \\ imp_res_tac heap_store_unused_IMP_length \\ fs []
  \\ `LENGTH ws + 1 <= sp'` by decide_tac
  \\ pop_assum mp_tac \\ simp_tac std_ss [LESS_EQ_EXISTS]
  \\ strip_tac \\ clean_tac \\ fs []
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [copying_gcTheory.EVERY2_APPEND]
  \\ fs [WORD_LEFT_ADD_DISTRIB,get_addr_def,make_ptr_def,get_lowerbits_def]
  \\ fs [bytes_in_word_mul_eq_shift]
  \\ fs [GSYM bytes_in_word_mul_eq_shift,GSYM word_add_n2w]
  \\ fs [heap_store_unused_def,el_length_def]
  \\ every_case_tac \\ fs []
  \\ imp_res_tac heap_lookup_SPLIT \\ fs [] \\ clean_tac
  \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ fs [heap_store_lemma] \\ clean_tac \\ fs []
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def,
         SEP_CLAUSES,word_heap_heap_expand,RefBlock_def,el_length_def,
         heap_length_APPEND,heap_length_heap_expand]
  \\ fs [word_list_exists_ADD |> Q.SPECL [`m`,`n+1`]]
  \\ `make_header c 2w (LENGTH ws) = hd` by
       (fs [encode_header_def] \\ every_case_tac \\ fs []
        \\ fs [WORD_MUL_LSL,word_mul_n2w,EXP_ADD] \\ NO_TAC)
  \\ fs [] \\ drule encode_header_IMP \\ fs [] \\ strip_tac
  \\ fs [SEP_CLAUSES,STAR_ASSOC]
  \\ `LENGTH ws + 1 = LENGTH (Word hd::ws)` by fs []
  \\ full_simp_tac std_ss []
  \\ assume_tac store_list_thm
  \\ SEP_F_TAC \\ strip_tac \\ fs []
  \\ fs [EVERY2_f_EQ] \\ clean_tac \\ fs []
  \\ fs [el_length_def,heap_length_APPEND,heap_length_heap_expand,
         GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [AC STAR_ASSOC STAR_COMM] \\ fs [STAR_ASSOC]
  \\ pop_assum mp_tac \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [AC STAR_ASSOC STAR_COMM] \\ fs [STAR_ASSOC]);

val get_addr_0 = store_thm("get_addr_0",
  ``get_addr c n u ' 0``,
  Cases_on `u` \\ fs [get_addr_def,get_lowerbits_def,
     word_or_def,fcpTheory.FCP_BETA,word_index]);

val word_addr_eq_Loc = store_thm("word_addr_eq_Loc",
  ``word_addr c v = Loc l1 l2 <=> v = Data (Loc l1 l2)``,
  Cases_on `v` \\ fs [word_addr_def]
  \\ Cases_on `a` \\ fs [word_addr_def]);

val memory_rel_CodePtr = store_thm("memory_rel_CodePtr",
  ``memory_rel c be refs sp st m dm vars ==>
    memory_rel c be refs sp st m dm ((CodePtr lab,Loc lab 0)::vars)``,
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ fs [word_ml_inv_def,PULL_EXISTS,word_addr_eq_Loc]
  \\ once_rewrite_tac [CONJ_COMM] \\ asm_exists_tac \\ fs []
  \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def,
         roots_ok_def,reachable_refs_def]
  \\ rw [] \\ fs [] \\ res_tac \\ fs []
  \\ asm_exists_tac \\ fs [PULL_EXISTS] \\ rw [] \\ fs []
  \\ fs [get_refs_def] \\ res_tac);

val memory_rel_Block_IMP = store_thm("memory_rel_Block_IMP",
  ``memory_rel c be refs sp st m dm ((Block tag vals,v:'a word_loc)::vars) /\
    good_dimindex (:'a) ==>
    ?w. v = Word w /\
        if vals = [] then
          w = n2w tag * 16w + 2w /\ ~(w ' 0) /\ tag < dimword (:'a) DIV 16
        else
          ?a x.
            w ' 0 /\ ~(word_bit 3 x) /\
            get_real_addr c st w = SOME a /\ m a = Word x /\ a IN dm /\
            decode_length c x = n2w (LENGTH vals) /\
            LENGTH vals < 2 ** (dimindex (:'a) − 4) /\
            encode_header c (4 * tag) (LENGTH vals) = SOME x``,
  fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
      bc_stack_ref_inv_def,v_inv_def]
  \\ CASE_TAC \\ fs [] \\ rw []
  THEN1 (fs [word_addr_def,BlockNil_def,WORD_MUL_LSL,GSYM word_mul_n2w,
             GSYM word_add_n2w,BlockNil_and_lemma])
  THEN1
   (fs [word_add_n2w,word_mul_n2w,word_index,bitTheory.BIT_def,
        bitTheory.BITS_THM]
    \\ full_simp_tac std_ss [DECIDE ``16 * n + 2 = (8 * n + 1:num) * 2``,
          MATCH_MP MOD_EQ_0 (DECIDE ``0<2:num``)])
  \\ fs [word_addr_def,heap_in_memory_store_def]
  \\ rpt_drule get_real_addr_get_addr \\ disch_then kall_tac
  \\ imp_res_tac heap_lookup_SPLIT \\ clean_tac
  \\ fs [word_heap_APPEND,word_heap_def,BlockRep_def,word_el_def,
         word_payload_def,word_list_def]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ imp_res_tac EVERY2_LENGTH \\ SEP_R_TAC \\ fs [get_addr_0]
  \\ fs [make_header_def,word_bit_def,word_or_def,fcpTheory.FCP_BETA]
  \\ fs [labPropsTheory.good_dimindex_def]
  \\ fs [fcpTheory.FCP_BETA,word_lsl_def,word_index])

val memory_rel_tag_limit = store_thm("memory_rel_tag_limit",
  ``memory_rel c be refs sp st m dm ((Block tag l,w)::rest) ==>
    tag < dimword (:'a) DIV 16``,
  cheat);

val memory_rel_test_nil_eq = store_thm("memory_rel_test_nil_eq",
  ``memory_rel c be refs sp st m dm ((Block tag l,w:'a word_loc)::rest) /\
    n < dimword (:'a) DIV 16 ==>
    ?v. w = Word v /\ (v = n2w (16 * n + 2) <=> tag = n /\ l = [])``,
  cheat);

val memory_rel_test_none_eq = store_thm("memory_rel_test_none_eq",
  ``encode_header c (4 * n) len = NONE /\
    memory_rel c be refs sp st m dm ((Block tag l,w:'a word_loc)::rest) /\
    len <> 0 ==>
    ~(tag = n /\ LENGTH l = len)``,
  cheat);

val encode_header_EQ = store_thm("encode_header_EQ",
  ``encode_header c t1 l1 = SOME w1 /\
    encode_header c t2 l2 = SOME w2 ==>
    (w1 = w2 <=> t1 = t2 /\ l1 = l2)``,
  cheat);

val memory_rel_ValueArray_IMP = store_thm("memory_rel_ValueArray_IMP",
  ``memory_rel c be refs sp st m dm ((RefPtr p,v:'a word_loc)::vars) /\
    FLOOKUP refs p = SOME (ValueArray vals) /\ good_dimindex (:'a) ==>
    ?w a x.
      v = Word w /\ w ' 0 /\ word_bit 3 x /\
      get_real_addr c st w = SOME a /\ m a = Word x /\ a IN dm /\
      decode_length c x = n2w (LENGTH vals) /\
      LENGTH vals < 2 ** (dimindex (:'a) − 4)``,
  fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
      bc_stack_ref_inv_def,v_inv_def,word_addr_def] \\ rw [get_addr_0]
  \\ `bc_ref_inv c p refs (f,heap,be)` by
    (first_x_assum match_mp_tac \\ fs [reachable_refs_def]
     \\ qexists_tac `RefPtr p` \\ fs [get_refs_def])
  \\ pop_assum mp_tac \\ simp [bc_ref_inv_def]
  \\ fs [FLOOKUP_DEF] \\ rw []
  \\ fs [word_addr_def,heap_in_memory_store_def]
  \\ rpt_drule get_real_addr_get_addr \\ disch_then kall_tac
  \\ imp_res_tac heap_lookup_SPLIT \\ clean_tac
  \\ fs [word_heap_APPEND,word_heap_def,RefBlock_def,word_el_def,
         word_payload_def,word_list_def]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ imp_res_tac EVERY2_LENGTH \\ SEP_R_TAC \\ fs [get_addr_0]
  \\ fs [make_header_def,word_bit_def,word_or_def,fcpTheory.FCP_BETA]
  \\ fs [labPropsTheory.good_dimindex_def]
  \\ fs [fcpTheory.FCP_BETA,word_lsl_def,word_index])

val LESS_LENGTH_IMP = prove(
  ``!xs n. n < LENGTH xs ==> ?ys t ts. xs = ys ++ t::ts /\ LENGTH ys = n``,
  Induct \\ fs [] \\ Cases_on `n` \\ fs [LENGTH_NIL] \\ rw []
  \\ res_tac \\ clean_tac \\ qexists_tac `h::ys` \\ fs []);

val write_bytes_APPEND = store_thm("write_bytes_APPEND",
  ``!xs ys vals be.
      write_bytes vals (xs ++ (ys:'a word list)) be =
      write_bytes vals xs be ++
      write_bytes (DROP ((dimindex (:α) DIV 8) * LENGTH xs) vals) ys be``,
  Induct \\ fs [write_bytes_def,ADD1,RIGHT_ADD_DISTRIB,DROP_DROP_T]);

val LESS_4 = DECIDE ``i < 4 <=> (i = 0) \/ (i = 1) \/ (i = 2) \/ (i = 3n)``
val LESS_8 = DECIDE ``i < 8 <=> (i = 0) \/ (i = 1) \/ (i = 2) \/ (i = 3n) \/
                                (i = 4) \/ (i = 5) \/ (i = 6) \/ (i = 7)``

val expand_num =
  DECIDE ``4 = SUC 3 /\ 3 = SUC 2 /\ 2 = SUC 1 /\ 1 = SUC 0 /\
           5 = SUC 4 /\ 6 = SUC 5 /\ 7 = SUC 6 /\ 8 = SUC 7``

val get_byte_set_byte_alt = store_thm("get_byte_set_byte_alt",
  ``good_dimindex (:'a) /\ w <> v /\ byte_align w = byte_align v /\
    get_byte w s be = x ==>
    get_byte w (set_byte v b (s:'a word) be) be = x``,
  rw [] \\ rpt_drule labPropsTheory.get_byte_set_byte_diff \\ fs []);

val get_byte_bytes_to_word = store_thm("get_byte_bytes_to_word",
  ``∀zs (t:'a word).
      i < LENGTH zs /\ i < 2 ** k /\
      2 ** k = dimindex(:'a) DIV 8 /\ good_dimindex (:'a) ⇒
      get_byte (n2w i) (bytes_to_word (2 ** k) 0w zs t be) be = EL i zs``,
  rw [] \\ fs [] \\ Cases_on `dimindex (:α) = 32` \\ fs [] THEN1
   (fs [LESS_4] \\ fs []
    \\ Cases_on `zs` \\ fs []
    \\ TRY (Cases_on `t'`) \\ fs []
    \\ TRY (Cases_on `t''`) \\ fs []
    \\ TRY (Cases_on `t`) \\ fs []
    \\ TRY (Cases_on `t'`) \\ fs []
    \\ rewrite_tac [expand_num,bytes_to_word_def]
    \\ rpt (fs [labPropsTheory.get_byte_set_byte]
      \\ match_mp_tac get_byte_set_byte_alt
      \\ fs [dimword_def,alignmentTheory.byte_align_def,
             alignmentTheory.align_w2n]))
  \\ fs [] \\ Cases_on `dimindex (:α) = 64` \\ fs [] THEN1
   (fs [LESS_8] \\ fs []
    \\ Cases_on `zs` \\ fs []
    \\ TRY (Cases_on `t'`) \\ fs []
    \\ TRY (Cases_on `t''`) \\ fs []
    \\ TRY (Cases_on `t`) \\ fs []
    \\ TRY (Cases_on `t'`) \\ fs []
    \\ TRY (Cases_on `t`) \\ fs []
    \\ TRY (Cases_on `t'`) \\ fs []
    \\ TRY (Cases_on `t`) \\ fs []
    \\ TRY (Cases_on `t'`) \\ fs []
    \\ rewrite_tac [expand_num,bytes_to_word_def]
    \\ rpt (fs [labPropsTheory.get_byte_set_byte]
      \\ match_mp_tac get_byte_set_byte_alt
      \\ fs [dimword_def,alignmentTheory.byte_align_def,
             alignmentTheory.align_w2n]))
  \\ rfs [labPropsTheory.good_dimindex_def]);

val pow_eq_0 = store_thm("pow_eq_0",
  ``dimindex (:'a) <= k ==> (n2w (2 ** k) = 0w:'a word)``,
  fs [dimword_def] \\ fs [LESS_EQ_EXISTS]
  \\ rw [] \\ fs [EXP_ADD,MOD_EQ_0]);

val aligned_pow = store_thm("aligned_pow",
  ``aligned k (n2w (2 ** k))``,
  Cases_on `k < dimindex (:'a)`
  \\ fs [NOT_LESS,pow_eq_0,aligned_0]
  \\ `2 ** k < dimword (:'a)` by fs [dimword_def]
  \\ fs [aligned_def,align_w2n])

local
  val aligned_add_mult_lemma = prove(
    ``aligned k (w + n2w (2 ** k)) = aligned k w``,
    fs [aligned_add_sub,aligned_pow]) |> GEN_ALL
  val aligned_add_mult_any = prove(
    ``!n w. aligned k (w + n2w (n * 2 ** k)) = aligned k w``,
    Induct \\ fs [MULT_CLAUSES,GSYM word_add_n2w] \\ rw []
    \\ pop_assum (qspec_then `w + n2w (2 ** k)` mp_tac)
    \\ fs [aligned_add_mult_lemma]) |> GEN_ALL
in
  val aligned_add_pow = save_thm("aligned_add_pow[simp]",
    CONJ aligned_add_mult_lemma aligned_add_mult_any)
end

val MOD_MULT_MOD_LEMMA = prove(
  ``k MOD n = 0 /\ x MOD n = t /\ 0 < k /\ 0 < n /\ n <= k ==>
    x MOD k MOD n = t``,
  rw [] \\ drule DIVISION
  \\ disch_then (qspec_then `k` mp_tac) \\ strip_tac
  \\ qpat_assum `_ = _` (fn th => once_rewrite_tac [th])
  \\ fs [] \\ Cases_on `0 < k DIV n` \\ fs [MOD_MULT_MOD]
  \\ fs [DIV_EQ_X] \\ rfs [DIV_EQ_X]);

val w2n_add_byte_align_lemma = store_thm("w2n_add_byte_align_lemma",
  ``good_dimindex (:'a) ==>
    w2n (a' + byte_align (a:'a word)) MOD (dimindex (:'a) DIV 8) =
    w2n a' MOD (dimindex (:'a) DIV 8)``,
  Cases_on `a'` \\ Cases_on `a`
  \\ fs [byte_align_def,align_w2n]
  \\ fs [labPropsTheory.good_dimindex_def] \\ rw []
  \\ fs [word_add_n2w] \\ fs [dimword_def]
  \\ match_mp_tac MOD_MULT_MOD_LEMMA \\ fs []
  \\ once_rewrite_tac [MULT_COMM]
  \\ once_rewrite_tac [ADD_COMM]
  \\ fs [MOD_TIMES]);

val get_byte_byte_align = store_thm("get_byte_byte_align",
  ``good_dimindex (:'a) ==>
    get_byte (a' + byte_align a) w be = get_byte a' (w:'a word) be``,
  fs [wordSemTheory.get_byte_def] \\ rw [] \\ rpt AP_TERM_TAC
  \\ fs [wordSemTheory.byte_index_def,w2n_add_byte_align_lemma]);

val get_byte_eq = store_thm("get_byte_eq",
  ``good_dimindex (:'a) /\ a = byte_align a + a' ==>
    get_byte a w be = get_byte a' (w:'a word) be``,
  rw [] \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs [get_byte_byte_align]);

val TTT_def = Define `TTT x = T`

val memory_rel_ByteArray_IMP = store_thm("memory_rel_ByteArray_IMP",
  ``memory_rel c be refs sp st m dm ((RefPtr p,v:'a word_loc)::vars) /\
    FLOOKUP refs p = SOME (ByteArray vals) /\ good_dimindex (:'a) ==>
    ?w a x l.
      v = Word w /\ w ' 0 /\ word_bit 3 x /\
      get_real_addr c st w = SOME a /\ m a = Word x /\ a IN dm /\
      (!i. i < LENGTH vals ==>
           mem_load_byte_aux m dm be (a + bytes_in_word + n2w i) =
           SOME (EL i vals)) /\
      if dimindex (:'a) = 32 then
        LENGTH vals + 4 < 2 ** (dimindex (:'a) - 3) /\
        TTT (x >>> (dimindex (:'a) - c.len_size - 2) = n2w (LENGTH vals + 4))
      else
        LENGTH vals + 8 < 2 ** (dimindex (:'a) - 3) /\
        TTT (x >>> (dimindex (:'a) - c.len_size - 3) = n2w (LENGTH vals + 8))``,
  fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
      bc_stack_ref_inv_def,v_inv_def,word_addr_def] \\ rw [get_addr_0]
  \\ `bc_ref_inv c p refs (f,heap,be)` by
    (first_x_assum match_mp_tac \\ fs [reachable_refs_def]
     \\ qexists_tac `RefPtr p` \\ fs [get_refs_def])
  \\ pop_assum mp_tac \\ simp [bc_ref_inv_def]
  \\ fs [FLOOKUP_DEF] \\ rw []
  \\ fs [word_addr_def,heap_in_memory_store_def]
  \\ rpt_drule get_real_addr_get_addr \\ disch_then kall_tac
  \\ imp_res_tac heap_lookup_SPLIT \\ clean_tac
  \\ fs [word_heap_APPEND,word_heap_def,RefBlock_def,word_el_def,
         word_payload_def,word_list_def,Bytes_def]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ imp_res_tac EVERY2_LENGTH \\ SEP_R_TAC \\ fs [get_addr_0]
  \\ rpt strip_tac
  THEN1 (fs [make_byte_header_def,word_bit_def,word_or_def,fcpTheory.FCP_BETA]
    \\ fs [labPropsTheory.good_dimindex_def]
    \\ fs [fcpTheory.FCP_BETA,word_lsl_def,word_index])
  THEN1
   (fs [wordSemTheory.mem_load_byte_aux_def]
    \\ fs [alignmentTheory.byte_align_def,bytes_in_word_def]
    \\ qabbrev_tac `k = LOG2 (dimindex (:α) DIV 8)`
    \\ `dimindex (:α) DIV 8 = 2 ** k` by
         (rfs [labPropsTheory.good_dimindex_def,Abbr`k`] \\ NO_TAC) \\ fs []
    \\ `(align k (curr + n2w (2 ** k) +
                  n2w (heap_length ha) * n2w (2 ** k) + n2w i) =
         curr + n2w (2 ** k) + n2w (heap_length ha) * n2w (2 ** k) +
         n2w (i DIV 2 ** k * 2 ** k))` by
     (`0n < 2 ** k` by fs []
      \\ drule DIVISION
      \\ disch_then (qspec_then `i` strip_assume_tac)
      \\ qpat_assum `_ = _` (fn th => simp_tac std_ss [Once th]
            THEN assume_tac (GSYM th))
      \\ simp_tac std_ss [GSYM word_add_n2w,WORD_ADD_ASSOC]
      \\ match_mp_tac align_add_aligned
      \\ fs [aligned_add_pow,word_mul_n2w,byte_aligned_def]
      \\ `i MOD 2 ** k < dimword (:'a)` by all_tac \\ fs []
      \\ match_mp_tac LESS_LESS_EQ_TRANS \\ qexists_tac `2 ** k` \\ fs []
      \\ fs [dimword_def]
      \\ fs [labPropsTheory.good_dimindex_def] \\ rfs []
      \\ Cases_on `k` \\ fs []
      \\ Cases_on `n` \\ fs []
      \\ Cases_on `n'` \\ fs []
      \\ Cases_on `n` \\ fs []
      \\ fs [ADD1,EXP_ADD] \\ NO_TAC)
    \\ `!v. get_byte
             (curr + n2w i + n2w (2 ** k) +
              n2w (heap_length ha) * n2w (2 ** k)) v be =
            get_byte (n2w (i MOD 2 ** k)) v be` by
     (rw [] \\ match_mp_tac get_byte_eq
      \\ fs [byte_align_def]
      \\ `0n < 2 ** k` by fs []
      \\ drule DIVISION
      \\ disch_then (qspec_then `i` strip_assume_tac)
      \\ qpat_assum `_ = _` (fn th => simp_tac std_ss [Once th])
      \\ Cases_on `curr` \\ fs [word_add_n2w,word_mul_n2w] \\ NO_TAC)
    \\ fs []
    \\ `i DIV 2 ** k < LENGTH ws` by
        (fs [DIV_LT_X,RIGHT_ADD_DISTRIB]
         \\ `0n < 2 ** k` by fs []
         \\ rpt_drule DIVISION
         \\ disch_then (qspec_then `LENGTH vals` strip_assume_tac)
         \\ decide_tac)
    \\ `(curr + n2w (i DIV 2 ** k * 2 ** k) + n2w (2 ** k) +
          n2w (heap_length ha) * n2w (2 ** k) IN dm) /\
        m (curr + n2w (i DIV 2 ** k * 2 ** k) + n2w (2 ** k) +
          n2w (heap_length ha) * n2w (2 ** k)) =
        (EL (i DIV 2 ** k) (MAP Word (write_bytes vals ws be)))` by
     (`i DIV 2 ** k < LENGTH (MAP Word (write_bytes vals ws be))` by
                (fs [] \\ decide_tac)
      \\ drule LESS_LENGTH_IMP \\ strip_tac \\ clean_tac
      \\ fs [word_list_def,word_list_APPEND,bytes_in_word_def,word_mul_n2w]
      \\ SEP_R_TAC \\ fs []
      \\ pop_assum (fn th => rewrite_tac [GSYM th])
      \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ fs [EL_LENGTH_APPEND])
    \\ fs [EL_MAP,LENGTH_write_bytes]
    \\ drule LESS_LENGTH_IMP \\ strip_tac \\ clean_tac
    \\ fs [write_bytes_APPEND]
    \\ `i DIV 2 ** k = LENGTH (write_bytes vals ys' be)` by
          metis_tac [LENGTH_write_bytes]
    \\ full_simp_tac std_ss [EL_LENGTH_APPEND,NULL_DEF,write_bytes_def,LET_DEF]
    \\ fs [] \\ pop_assum (fn th => fs [GSYM th]) \\ fs []
    \\ `EL i vals =
        EL (i MOD 2 ** k) (DROP (i DIV 2 ** k * 2 ** k) vals)` by
     (`0n < 2 ** k` by fs []
      \\ rpt_drule DIVISION
      \\ disch_then (qspec_then `i` strip_assume_tac)
      \\ qpat_assum `_ = _` (fn th => simp [Once th] THEN assume_tac (GSYM th))
      \\ once_rewrite_tac [ADD_COMM]
      \\ match_mp_tac (GSYM EL_DROP) \\ decide_tac)
    \\ fs [] \\ match_mp_tac get_byte_bytes_to_word \\ fs []
    \\ `0n < 2 ** k` by fs []
    \\ rpt_drule DIVISION
    \\ disch_then (qspec_then `i` strip_assume_tac)
    \\ decide_tac)
  \\ qpat_assum `LENGTH vals < 2 ** (_ + _)` assume_tac
  \\ fs [labPropsTheory.good_dimindex_def,make_byte_header_def,
         LENGTH_write_bytes] \\ rfs []
  \\ fs [TTT_def] (*
  THEN1
   (`4 <= 30 - c.len_size` by decide_tac
    \\ `c.len_size <= 30` by decide_tac
    \\ pop_assum mp_tac
    \\ simp [LESS_EQ_EXISTS] \\ strip_tac \\ fs []
    \\ qcase_tac `4n <= k`
    \\ `15w >>> k = 0w`
    by (srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index]
        \\ Cases_on `i + k < 32`
        \\ simp [wordsTheory.word_index])
    \\ simp []
    \\ match_mp_tac lsl_lsr
    \\ simp [wordsTheory.dimword_def]
    \\ `c.len_size = 30 - k` by decide_tac \\ fs []
    \\ fs [EXP_SUB,X_LT_DIV,RIGHT_ADD_DISTRIB]
    \\ `29 = c.len_size + k - 1` by decide_tac
    \\ `2n ** 29 = 2 ** (c.len_size + k - 1)` by metis_tac []
    \\ full_simp_tac bool_ss [EVAL ``2n ** 29``])
  THEN1
   (`4 <= 61 - c.len_size` by decide_tac
    \\ `c.len_size <= 61` by decide_tac \\ pop_assum mp_tac
    \\ simp [LESS_EQ_EXISTS] \\ strip_tac \\ fs []
    \\ qcase_tac `4n <= k` \\ fs []) *))

val memory_rel_RefPtr_IMP_lemma = store_thm("memory_rel_RefPtr_IMP_lemma",
  ``memory_rel c be refs sp st m dm ((RefPtr p,v:'a word_loc)::vars) ==>
    ?res. FLOOKUP refs p = SOME res``,
  fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
      bc_stack_ref_inv_def,v_inv_def,word_addr_def] \\ rw []
  \\ `bc_ref_inv c p refs (f,heap,be)` by
    (first_x_assum match_mp_tac \\ fs [reachable_refs_def]
     \\ qexists_tac `RefPtr p` \\ fs [get_refs_def])
  \\ pop_assum mp_tac \\ simp [bc_ref_inv_def]
  \\ fs [FLOOKUP_DEF] \\ rw []);

val memory_rel_RefPtr_IMP = store_thm("memory_rel_RefPtr_IMP",
  ``memory_rel c be refs sp st m dm ((RefPtr p,v:'a word_loc)::vars) /\
    good_dimindex (:'a) ==>
    ?w a x.
      v = Word w /\ w ' 0 /\ word_bit 3 x /\
      get_real_addr c st w = SOME a /\ m a = Word x /\ a IN dm``,
  strip_tac \\ drule memory_rel_RefPtr_IMP_lemma \\ strip_tac
  \\ Cases_on `res` \\ fs []
  THEN1 (rpt_drule memory_rel_ValueArray_IMP \\ rw [] \\ fs [])
  THEN1 (rpt_drule memory_rel_ByteArray_IMP \\ rw [] \\ fs []));

val memory_rel_Number_IMP = store_thm("memory_rel_Number_IMP",
  ``good_dimindex (:'a) /\
    memory_rel c be refs sp st m dm ((Number i,v:'a word_loc)::vars) ==>
    v = Word (Smallnum i) /\ small_int (:'a) i``,
  fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
      bc_stack_ref_inv_def,v_inv_def] \\ rw []
  \\ fs [word_addr_def,Smallnum_def,integer_wordTheory.i2w_def]
  \\ Cases_on `i`
  \\ fs [GSYM word_mul_n2w,word_ml_inv_num_lemma,word_ml_inv_neg_num_lemma])

val IMP_memory_rel_Number = store_thm("IMP_memory_rel_Number",
  ``good_dimindex (:'a) /\ small_int (:'a) i /\
    memory_rel c be refs sp st m dm vars ==>
    memory_rel c be refs sp st m dm
     ((Number i,(Word (Smallnum i):'a word_loc))::vars)``,
  fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS] \\ rpt strip_tac
  \\ asm_exists_tac \\ fs []
  \\ rpt_drule abs_ml_inv_Num
  \\ strip_tac \\ asm_exists_tac \\ fs [word_addr_def]
  \\ fs [Smallnum_def] \\ Cases_on `i`
  \\ fs [GSYM word_mul_n2w,word_ml_inv_num_lemma,word_ml_inv_neg_num_lemma])

val IMP_memory_rel_Number_num3 = store_thm("IMP_memory_rel_Number_num3",
  ``good_dimindex (:'a) /\ n < 2 ** (dimindex (:'a) - 3) /\
    memory_rel c be refs sp st m dm vars ==>
    memory_rel c be refs sp st m dm
     ((Number (&n),Word ((n2w n << 2):'a word))::vars)``,
  strip_tac \\ mp_tac (IMP_memory_rel_Number |> Q.INST [`i`|->`&n`]) \\ fs []
  \\ fs [Smallnum_def,WORD_MUL_LSL,word_mul_n2w]
  \\ disch_then match_mp_tac
  \\ fs [small_int_def,dimword_def]
  \\ fs [labPropsTheory.good_dimindex_def] \\ rfs [])

val IMP_memory_rel_Number_num = store_thm("IMP_memory_rel_Number_num",
  ``good_dimindex (:'a) /\ n < 2 ** (dimindex (:'a) - 4) /\
    memory_rel c be refs sp st m dm vars ==>
    memory_rel c be refs sp st m dm
     ((Number (&n),Word ((n2w n << 2):'a word))::vars)``,
  strip_tac \\ mp_tac (IMP_memory_rel_Number |> Q.INST [`i`|->`&n`]) \\ fs []
  \\ fs [Smallnum_def,WORD_MUL_LSL,word_mul_n2w]
  \\ disch_then match_mp_tac
  \\ fs [small_int_def,dimword_def]
  \\ fs [labPropsTheory.good_dimindex_def] \\ rfs [])

val memory_rel_tail = store_thm("memory_rel_tail",
  ``memory_rel c be refs sp st m dm (v::vars) ==>
    memory_rel c be refs sp st m dm vars``,
  match_mp_tac memory_rel_rearrange \\ fs []);

val memory_rel_Number_EQ = store_thm("memory_rel_Number_EQ",
  ``memory_rel c be refs sp st m dm
      ((Number i1,w1)::(Number i2,w2)::vars) /\ good_dimindex (:'a) ==>
      ?v1 v2. w1 = Word v1 /\ w2 = Word (v2:'a word) /\ (v1 = v2 <=> i1 = i2)``,
  strip_tac
  \\ imp_res_tac memory_rel_Number_IMP
  \\ drule memory_rel_tail \\ strip_tac
  \\ imp_res_tac memory_rel_Number_IMP
  \\ fs [] \\ fs [memory_rel_def] \\ rw [] \\ fs [word_ml_inv_def] \\ clean_tac
  \\ drule num_eq_thm \\ rw []);

val memory_rel_Number_LESS = store_thm("memory_rel_Number_LESS",
  ``memory_rel c be refs sp st m dm
      ((Number i1,w1)::(Number i2,w2)::vars) /\ good_dimindex (:'a) ==>
      ?v1 v2. w1 = Word v1 /\ w2 = Word v2 /\ (v1 < (v2:'a word) <=> i1 < i2)``,
  strip_tac
  \\ imp_res_tac memory_rel_Number_IMP
  \\ drule memory_rel_tail \\ strip_tac
  \\ imp_res_tac memory_rel_Number_IMP
  \\ fs [] \\ fs [memory_rel_def] \\ rw [] \\ fs [num_less_thm]);

val memory_rel_Number_LESS_EQ = store_thm("memory_rel_Number_LESS_EQ",
  ``memory_rel c be refs sp st m dm
      ((Number i1,w1)::(Number i2,w2)::vars) /\ good_dimindex (:'a) ==>
      ?v1 v2. w1 = Word v1 /\ w2 = Word v2 /\ (v1 <= (v2:'a word) <=> i1 <= i2)``,
  rw [] \\ drule memory_rel_Number_LESS \\ fs [] \\ rw [] \\ fs []
  \\ drule memory_rel_Number_EQ \\ fs [] \\ rw [] \\ fs []
  \\ fs [WORD_LESS_OR_EQ,integerTheory.INT_LE_LT]);

val memory_rel_RefPtr_EQ_lemma = prove(
  ``n * 2 ** k < dimword (:'a) /\ m * 2 ** k < dimword (:'a) /\ 0 < k /\
    (n2w n << k || 1w) = (n2w m << k || 1w:'a word) ==> n = m``,
  `!n a b. 0n < n ==> (a * n = b * n) = (a = b)`
  by (Cases \\ simp [])
  \\ rw []
  \\ `(n2w n << k || 1w) = (n2w n << k + 1w)`
  by (match_mp_tac (GSYM wordsTheory.WORD_ADD_OR)
      \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index])
  \\ `(n2w m << k || 1w) = (n2w m << k + 1w)`
  by (match_mp_tac (GSYM wordsTheory.WORD_ADD_OR)
      \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index])
  \\ fs [addressTheory.word_LSL_n2w]
  \\ rfs []
  )

val memory_rel_RefPtr_EQ = store_thm("memory_rel_RefPtr_EQ",
  ``memory_rel c be refs sp st m dm
      ((RefPtr i1,w1)::(RefPtr i2,w2)::vars) /\ good_dimindex (:'a) ==>
      ?v1 v2. w1 = Word v1 /\ w2 = Word (v2:'a word) /\ (v1 = v2 <=> i1 = i2)``,
  fs [memory_rel_def] \\ rw [] \\ fs [word_ml_inv_def] \\ clean_tac
  \\ drule ref_eq_thm \\ rw [] \\ clean_tac
  \\ fs [word_addr_def,get_addr_def]
  \\ eq_tac \\ rw [] \\ fs [get_lowerbits_def]
  \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def]
  \\ `bc_ref_inv c i1 refs (f,heap,be) /\
      bc_ref_inv c i2 refs (f,heap,be)` by
   (rpt strip_tac \\ first_x_assum match_mp_tac
    \\ fs [reachable_refs_def]
    \\ metis_tac [get_refs_def,MEM,RTC_DEF])
  \\ fs [bc_ref_inv_def,FLOOKUP_DEF] \\ rfs [SUBSET_DEF]
  \\ NTAC 2 (pop_assum mp_tac) \\ fs []
  \\ rpt strip_tac
  \\ `?x1 x2. heap_lookup (f ' i1) heap = SOME x1 /\
              heap_lookup (f ' i2) heap = SOME x2` by
          (every_case_tac \\ fs [] \\ NO_TAC)
  \\ `f ' i1 < dimword (:'a) DIV 2 ** shift_length c /\
      f ' i2 < dimword (:'a) DIV 2 ** shift_length c` by
    (imp_res_tac heap_lookup_LESS \\ fs [heap_in_memory_store_def])
  \\ `0 < shift_length c` by fs [shift_length_def]
  \\ `f ' i1 * 2 ** shift_length c < dimword (:'a) /\
      f ' i2 * 2 ** shift_length c < dimword (:'a)` by
    (fs [X_LT_DIV,RIGHT_ADD_DISTRIB]
     \\ Cases_on `2 ** shift_length c` \\ fs []) \\ fs []
  \\ imp_res_tac memory_rel_RefPtr_EQ_lemma \\ rfs[]);

val memory_rel_Boolv_T = store_thm("memory_rel_Boolv_T",
  ``memory_rel c be refs sp st m dm vars /\ good_dimindex (:'a) ==>
    memory_rel c be refs sp st m dm ((Boolv T,Word (2w:'a word))::vars)``,
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ fs [word_ml_inv_def,PULL_EXISTS,EVAL ``Boolv F``,EVAL ``Boolv T``]
  \\ rpt_drule cons_thm_EMPTY \\ disch_then (qspec_then `0` assume_tac)
  \\ rfs [labPropsTheory.good_dimindex_def,dimword_def]
  \\ rfs [labPropsTheory.good_dimindex_def,dimword_def]
  \\ asm_exists_tac \\ fs [] \\ fs [word_addr_def,BlockNil_def]
  \\ EVAL_TAC \\ fs [labPropsTheory.good_dimindex_def,dimword_def]);

val memory_rel_Boolv_F = store_thm("memory_rel_Boolv_F",
  ``memory_rel c be refs sp st m dm vars /\ good_dimindex (:'a) ==>
    memory_rel c be refs sp st m dm ((Boolv F,Word (18w:'a word))::vars)``,
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ fs [word_ml_inv_def,PULL_EXISTS,EVAL ``Boolv F``,EVAL ``Boolv T``]
  \\ rpt_drule cons_thm_EMPTY \\ disch_then (qspec_then `1` assume_tac)
  \\ rfs [labPropsTheory.good_dimindex_def,dimword_def]
  \\ rfs [labPropsTheory.good_dimindex_def,dimword_def]
  \\ asm_exists_tac \\ fs [] \\ fs [word_addr_def,BlockNil_def]
  \\ EVAL_TAC \\ fs [labPropsTheory.good_dimindex_def,dimword_def]);

val Smallnum_bits = store_thm("Smallnum_bits",
  ``(1w && Smallnum i) = 0w /\ (2w && Smallnum i) = 0w``,
  Cases_on `i`
  \\ srw_tac [wordsLib.WORD_MUL_LSL_ss]
             [Smallnum_def, GSYM wordsTheory.word_mul_n2w]
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index])

val IsBlock_word_lemma = store_thm("IsBlock_word_lemma",
  ``good_dimindex (:'a) ==> (2w && 16w * n2w n' + 2w) <> 0w :'a word``,
  `!a : 'a word. (a << 4 + 2w) = (a << 4 || 2w)`
  by (strip_tac \\ match_mp_tac wordsTheory.WORD_ADD_OR
      \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index])
  \\ srw_tac [wordsLib.WORD_MUL_LSL_ss] [labPropsTheory.good_dimindex_def]
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index])

val word_ml_inv_SP_LIMIT = store_thm("word_ml_inv_SP_LIMIT",
  ``word_ml_inv (heap,be,a,sp) limit c refs stack ==> sp <= limit``,
  srw_tac[][] \\ Cases_on `sp = 0`
  \\ full_simp_tac(srw_ss())[word_ml_inv_def,abs_ml_inv_def,
        heap_ok_def,unused_space_inv_def]
  \\ imp_res_tac heap_lookup_SPLIT \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[heap_length_APPEND,
        heap_length_def,el_length_def] \\ decide_tac);

val word_or_eq_0 = prove(
  ``((w || v) = 0w) <=> (w = 0w) /\ (v = 0w)``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [] \\ metis_tac [])

val lt8 =
  DECIDE ``(n < 8n) = (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/
                       n = 4 \/ n = 5 \/ n = 6 \/ n = 7)``

val Smallnum_test = prove(
  ``((Smallnum i && -1w ≪ (dimindex (:'a) − 2)) = 0w:'a word) /\
    good_dimindex (:'a) /\ small_int (:'a) i ==>
    ~(i < 0) /\ i < 2 ** (dimindex (:'a) - 4)``,
  Tactical.REVERSE (Cases_on `i`)
  \\ srw_tac [wordsLib.WORD_MUL_LSL_ss]
      [Smallnum_def, small_int_def, labPropsTheory.good_dimindex_def,
       wordsTheory.dimword_def, GSYM wordsTheory.word_mul_n2w]
  >- (Cases_on `n <= 2n ** dimindex(:'a) DIV 8`
      \\ simp [wordsTheory.word_2comp_n2w, wordsTheory.dimword_def]
      \\ Cases_on `dimindex(:'a) = 32`
      \\ fs []
      >- (`3758096384 <= 4294967296 - n /\ 4294967296 - n < 4294967296`
          by decide_tac
          \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index]
          \\ qabbrev_tac `x = 4294967296 - n`
          \\ `BITS 31 29 x = 7`
          by (imp_res_tac
                (bitTheory.BITS_ZEROL |> Q.SPEC `31` |> numLib.REDUCE_RULE)
              \\ fs [bitTheory.BIT_COMP_THM3
                     |> Q.SPECL [`31`, `28`, `0`] |> numLib.REDUCE_RULE |> GSYM]
              \\ assume_tac
                   (bitTheory.BITSLT_THM2
                    |> Q.SPECL [`28`, `0`, `x`] |> numLib.REDUCE_RULE)
              \\ assume_tac
                   (bitTheory.BITSLT_THM
                    |> Q.SPECL [`31`, `29`, `x`] |> numLib.REDUCE_RULE)
              \\ fs [lt8]
             )
          \\ simp [bitTheory.BIT_OF_BITS_THM
                   |> Q.SPECL [`0`, `31`, `29`] |> numLib.REDUCE_RULE |> GSYM]
         )
      \\ Cases_on `dimindex(:'a) = 64`
      \\ fs []
      \\ `16140901064495857664 <= 18446744073709551616 - n /\
          18446744073709551616 - n < 18446744073709551616`
      by decide_tac
      \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index]
      \\ qabbrev_tac `x = 18446744073709551616 - n`
      \\ `BITS 63 61 x = 7`
      by (imp_res_tac
            (bitTheory.BITS_ZEROL |> Q.SPEC `63` |> numLib.REDUCE_RULE)
          \\ fs [bitTheory.BIT_COMP_THM3
                 |> Q.SPECL [`63`, `60`, `0`] |> numLib.REDUCE_RULE |> GSYM]
          \\ assume_tac
               (bitTheory.BITSLT_THM2
                |> Q.SPECL [`60`, `0`, `x`] |> numLib.REDUCE_RULE)
          \\ assume_tac
               (bitTheory.BITSLT_THM
                |> Q.SPECL [`63`, `60`, `x`] |> numLib.REDUCE_RULE)
          \\ fs [lt8]
         )
      \\ simp [bitTheory.BIT_OF_BITS_THM
               |> Q.SPECL [`0`, `63`, `61`] |> numLib.REDUCE_RULE |> GSYM]
     )
  \\ full_simp_tac (srw_ss()++wordsLib.WORD_BIT_EQ_ss) [wordsTheory.word_index]
  \\ rfs [bitTheory.BIT_def, bitTheory.NOT_BITS2]
  >- (imp_res_tac
        (bitTheory.BITS_ZEROL |> Q.SPEC `28` |> numLib.REDUCE_RULE |> GSYM)
      \\ pop_assum SUBST1_TAC
      \\ simp [bitTheory.BIT_COMP_THM3
               |> Q.SPECL [`28`, `27`, `0`] |> numLib.REDUCE_RULE |> GSYM,
               bitTheory.BITSLT_THM2 |> Q.SPEC `27` |> numLib.REDUCE_RULE])
  >- (imp_res_tac
        (bitTheory.BITS_ZEROL |> Q.SPEC `60` |> numLib.REDUCE_RULE |> GSYM)
      \\ pop_assum SUBST1_TAC
      \\ simp [bitTheory.BIT_COMP_THM3
               |> Q.SPECL [`60`, `59`, `0`] |> numLib.REDUCE_RULE |> GSYM,
               bitTheory.BITSLT_THM2 |> Q.SPEC `59` |> numLib.REDUCE_RULE])
  )

val memory_rel_Add = store_thm("memory_rel_Add",
  ``memory_rel c be refs sp st m dm
      ((Number i,Word wi)::(Number j,Word wj)::vars) /\
    good_dimindex (:'a) /\
    (((wi || wj) && (~0w << (dimindex (:'a)-2))) = 0w) ==>
    memory_rel c be refs sp st m dm
      ((Number (i + j),Word (wi + wj:'a word))::vars)``,
  rw [] \\ imp_res_tac memory_rel_Number_IMP \\ fs []
  \\ fs [WORD_LEFT_AND_OVER_OR]
  \\ drule memory_rel_tail \\ strip_tac
  \\ imp_res_tac memory_rel_Number_IMP \\ fs []
  \\ rpt var_eq_tac \\ fs [word_or_eq_0]
  \\ drule Smallnum_test \\ fs []
  \\ qpat_assum `_ = 0w` kall_tac
  \\ drule Smallnum_test \\ fs []
  \\ qpat_assum `_ = 0w` kall_tac
  \\ rpt strip_tac
  \\ `Smallnum i + Smallnum j = (Smallnum (i + j)):'a word` by
   (`~(i + j < 0)` by intLib.COOPER_TAC
    \\ fs [Smallnum_def] \\ fs [word_add_n2w]
    \\ AP_THM_TAC \\ AP_TERM_TAC \\ intLib.COOPER_TAC)
  \\ fs [] \\ match_mp_tac IMP_memory_rel_Number
  \\ imp_res_tac memory_rel_tail \\ fs []
  \\ fs [small_int_def]
  \\ fs [labPropsTheory.good_dimindex_def]
  \\ rfs [dimword_def]
  \\ intLib.COOPER_TAC);

val exists_num = prove(
  ``~(i < 0i) <=> ?n. i = &n``,
  Cases_on `i` \\ fs []);

val memory_rel_Sub = store_thm("memory_rel_Sub",
  ``memory_rel c be refs sp st m dm
       ((Number i,Word wi)::(Number j,Word wj)::vars) /\
    good_dimindex (:'a) /\
    (((wi || wj) && (~0w << (dimindex (:'a)-2))) = 0w) ==>
    memory_rel c be refs sp st m dm
       ((Number (i - j),Word (wi - wj:'a word))::vars)``,
  rw [] \\ imp_res_tac memory_rel_Number_IMP \\ fs []
  \\ fs [WORD_LEFT_AND_OVER_OR]
  \\ drule memory_rel_tail \\ strip_tac
  \\ imp_res_tac memory_rel_Number_IMP \\ fs []
  \\ rpt var_eq_tac \\ fs [word_or_eq_0]
  \\ drule Smallnum_test \\ fs []
  \\ qpat_assum `_ = 0w` kall_tac
  \\ drule Smallnum_test \\ fs []
  \\ qpat_assum `_ = 0w` kall_tac
  \\ rpt strip_tac
  \\ `Smallnum i - Smallnum j = (Smallnum (i - j)):'a word` by
   (`i − j < 0 <=> i < j` by intLib.COOPER_TAC \\ fs [Smallnum_def]
    \\ fs [exists_num] \\ rpt var_eq_tac \\ fs []
    \\ full_simp_tac std_ss [SIMP_CONV (srw_ss()) [] ``w - x:'a word`` |> GSYM,
         addressTheory.word_arith_lemma2]
    \\ IF_CASES_TAC \\ fs []
    \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
    \\ intLib.COOPER_TAC)
  \\ fs [] \\ match_mp_tac IMP_memory_rel_Number
  \\ imp_res_tac memory_rel_tail \\ fs []
  \\ fs [small_int_def]
  \\ fs [labPropsTheory.good_dimindex_def]
  \\ rfs [dimword_def]
  \\ intLib.COOPER_TAC);

val memory_rel_Number_IMP_Word = store_thm("memory_rel_Number_IMP_Word",
  ``memory_rel c be refs sp st m dm ((Number i,v)::vars) ==> ?w. v = Word w``,
  fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
      bc_stack_ref_inv_def,v_inv_def] \\ rw [] \\ fs [word_addr_def]);

val memory_rel_Number_IMP_Word_2 = store_thm("memory_rel_Number_IMP_Word_2",
  ``memory_rel c be refs sp st m dm ((Number i,v)::(Number j,w)::vars) ==>
    ?w1 w2. v = Word w1 /\ w = Word w2``,
  fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
      bc_stack_ref_inv_def,v_inv_def] \\ rw [] \\ fs [word_addr_def]);

val memory_rel_zero_space = store_thm("memory_rel_zero_space",
  ``memory_rel c be refs sp st m dm vars ==>
    memory_rel c be refs 0 st m dm vars``,
  fs [memory_rel_def,heap_in_memory_store_def]
  \\ rw [] \\ fs [] \\ rpt (asm_exists_tac \\ fs []) \\ metis_tac []);

val _ = export_theory();
