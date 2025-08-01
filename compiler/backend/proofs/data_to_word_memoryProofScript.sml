(*
  Part of the correctness proof for data_to_word
*)

open preamble dataSemTheory dataPropsTheory copying_gcTheory
     int_bitwiseTheory wordSemTheory data_to_wordTheory set_sepTheory
     labSemTheory whileTheory helperLib alignmentTheory multiwordTheory
     gc_sharedTheory gc_combinedTheory word_gcFunctionsTheory;
local open blastLib in end;

val shift_def = backend_commonTheory.word_shift_def;
val good_dimindex_def = miscTheory.good_dimindex_def;

val _ = new_theory "data_to_word_memoryProof";

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val drule = old_drule

(* TODO: move? *)
val clean_tac = rpt var_eq_tac \\ rpt (qpat_x_assum `T` kall_tac)
fun rpt_drule th = drule (th |> GEN_ALL) \\ rpt (disch_then drule \\ fs [])

val _ = augment_srw_ss[rewrites[LENGTH_REPLICATE]]

val _ = set_grammar_ancestry
  ["dataSem", "dataProps", "wordSem", "data_to_word",
   "gc_shared", "gc_combined", "word_gcFunctions"];
val _ = Parse.hide"el";
Overload good_dimindex[local] = ``misc$good_dimindex``

val LESS_4 = DECIDE ``i < 4 <=> (i = 0) \/ (i = 1) \/ (i = 2) \/ (i = 3n)``
val LESS_8 = DECIDE ``i < 8 <=> (i = 0) \/ (i = 1) \/ (i = 2) \/ (i = 3n) \/
                                (i = 4) \/ (i = 5) \/ (i = 6) \/ (i = 7)``

Theorem word_eq:
   !w v. w = v <=> !n. word_bit n w = word_bit n v
Proof
  fs [word_bit_thm,fcpTheory.CART_EQ]
  \\ rw [] \\ eq_tac \\ rw []
  \\ eq_tac \\ rw [] \\ res_tac \\ fs []
QED

Theorem ZIP_REPLICATE:
   !n. ZIP (REPLICATE n x, REPLICATE n y) = REPLICATE n (x,y)
Proof
  Induct \\ fs [REPLICATE]
QED

Theorem list_max_leq_suff:
   EVERY (\x. x <= b) ls ==> list_max ls <= b
Proof
  Induct_on`ls` \\ rw[list_max_def]
QED

Theorem list_max_mem:
   ls <> [] ==> MEM (list_max ls) ls
Proof
  Induct_on`ls` \\ rw[list_max_def]
  \\ Cases_on`ls` \\ fs[list_max_def]
QED

Theorem list_max_sum_bound:
   SUM ls <= list_max ls * LENGTH ls
Proof
  Induct_on`ls` \\ rw[list_max_def,ADD1,LEFT_ADD_DISTRIB]
  \\ match_mp_tac LESS_EQ_TRANS
  \\ asm_exists_tac \\ simp[]
QED

Theorem list_max_bounded_elements:
   !l1 l2. LIST_REL $<= l1 l2 ==> list_max l1 <= list_max l2
Proof
  Induct \\ rw[list_max_def] \\ res_tac \\ rw[list_max_def]
QED

Theorem list_max_map:
   ∀f l. (∀x y. x < y ==> f x < f y) ==> list_max (MAP f l) = if NULL l then 0 else f (list_max l)
Proof
  rpt strip_tac
  \\ Induct_on`l` \\ rw[list_max_def,NULL_EQ]
  \\ res_tac \\ fs[list_max_def] \\ rveq
  \\ fs[NOT_LESS]
  \\ Cases_on`l = []` \\ fs[list_max_def]
  \\ Cases_on`h < list_max l` \\ fs[]
  >- ( res_tac \\ fs[] )
  \\ `h = list_max l` by fs[]
  \\ fs[]
QED

Theorem w2i_i2w_IMP:
   (w2i ((i2w i):'a word)) = i ==> INT_MIN (:α) ≤ i ∧ i ≤ INT_MAX (:α)
Proof
  Cases_on `i`
  \\ fs [integer_wordTheory.i2w_def,integer_wordTheory.w2i_def] \\ rw []
  THEN1
   (fs [word_msb_def,word_index,bitTheory.BIT_def,bitTheory.BITS_THM]
    \\ `(n DIV 2 ** (dimindex (:α) − 1)) MOD 2 < 2` by fs []
    \\ Cases_on `(n DIV 2 ** (dimindex (:α) − 1)) MOD 2` \\ fs []
    \\ fs [DIV_MOD_MOD_DIV,GSYM EXP,ADD1]
    \\ assume_tac DIMINDEX_GT_0
    \\ `dimindex (:α) − 1 + 1 = dimindex (:α)` by decide_tac \\ fs []
    \\ rfs [dimword_def] \\ fs [DIV_EQ_X]
    \\ fs [wordsTheory.INT_MIN_def,integer_wordTheory.INT_MIN_def,
           wordsTheory.INT_MAX_def,integer_wordTheory.INT_MAX_def])
  \\ full_simp_tac std_ss [GSYM (``-(w:'a word)`` |> SIMP_CONV (srw_ss()) []),
        WORD_NEG_NEG,w2n_n2w] \\ fs [X_MOD_Y_EQ_X]
  \\ `dimindex (:α) − 1 < dimindex (:α)` by fs []
  \\ full_simp_tac std_ss [word_msb_def,word_2comp_n2w,word_index]
  \\ fs [bitTheory.BIT_def,bitTheory.BITS_THM]
  \\ fs [DIV_MOD_MOD_DIV,GSYM EXP,ADD1]
  \\ assume_tac DIMINDEX_GT_0
  \\ `dimindex (:α) − 1 + 1 = dimindex (:α)` by decide_tac \\ fs []
  \\ fs [dimword_def]
  \\ `(2 ** dimindex (:α) − n) < 2 ** dimindex (:α)` by decide_tac \\ fs []
  \\ fs [DIV_EQ_X] \\ fs [GSYM EXP,ADD1]
  \\ Cases_on `dimindex (:α)` \\ fs []
  \\ fs [wordsTheory.INT_MIN_def,integer_wordTheory.INT_MIN_def,
         wordsTheory.INT_MAX_def,integer_wordTheory.INT_MAX_def,EXP]
QED

Theorem word_i2w_sub:
   !a b. i2w a - i2w b = i2w (a - b)
Proof
  fs [integer_wordTheory.word_i2w_add,word_sub_def,integerTheory.int_sub,
      integer_wordTheory.MULT_MINUS_ONE]
QED

(* -- *)

Datatype:
  tag = BlockTag num | RefTag | BytesTag bool num | NumTag bool | Word64Tag
End

Definition BlockRep_def:
  BlockRep tag xs = DataElement xs (LENGTH xs) (BlockTag tag,[])
End

Type ml_el = ``:('a word_loc, tag # ('a word_loc list)) heap_element``
Type ml_heap = ``:'a ml_el list``

Definition Bytes_def:
  ((Bytes is_bigendian cmp_by_contents (bs:word8 list) (ws:'a word list)):'a ml_el) =
    let ws = write_bytes bs ws is_bigendian in
      DataElement [] (LENGTH ws) (BytesTag cmp_by_contents (LENGTH bs), MAP Word ws)
End

Definition Bignum_def:
  Bignum i =
    let (sign,payload:'a word list) = i2mw i in
      DataElement [] (LENGTH payload) (NumTag sign, MAP Word payload)
End

Definition BlockNil_def:
  BlockNil n = n2w n << 4 + 2w
End

Definition Word64Rep_def:
  Word64Rep (:'a) (w:word64) =
    if dimindex (:'a) < 64 then
      DataElement [] 2 (Word64Tag, [Word ((63 >< 32) w); Word ((31 >< 0) w)])
    else
      DataElement [] 1 (Word64Tag, [Word (((63 >< 0) w):'a word)])
End

Theorem Word64Rep_DataElement:
   ∀a w. ∃ws. (Word64Rep a w:'a ml_el) = DataElement [] (LENGTH ws) (Word64Tag,ws)
Proof
  Cases \\ rw[Word64Rep_def]
QED

Triviality v_size_LEMMA:
  !vs v. MEM v vs ==> v_size v <= v1_size vs
Proof
  Induct \\ full_simp_tac (srw_ss()) [v_size_def]
  \\ rpt strip_tac \\ res_tac \\ full_simp_tac std_ss [] \\ DECIDE_TAC
QED

(*
  code pointers (i.e. Locs) will end in ...0
  small numbers end in ...00
  NIL-like constructors end in ...10
*)

Definition v_inv_def[schematic]:
  (* v_inv v (x,f,tf,heap)
     v    : the dataSem value
     x    : the abstract gc value
     f    : reference values in dataLang to gc address (sort of like the content of the pointer)
     tf   : time-stamps in dataLang to gc addresses
     heap : is the gc abstract heap
   *)
  (v_inv (Number i) (x,f,tf,heap:'a ml_heap) <=>
     if small_int (:'a) i then (x = Data (Word (Smallnum i))) else
       ?ptr. (x = Pointer ptr (Word 0w)) /\
             (heap_lookup ptr heap = SOME (Bignum i))) /\
  (v_inv (Word64 w) (x,f,tf,heap) <=>
    ?ptr. (x = Pointer ptr (Word 0w)) /\
          (heap_lookup ptr heap = SOME (Word64Rep (:'a) w))) /\
  (v_inv (CodePtr n) (x,f,tf,heap) <=>
     (x = Data (Loc n 0))) /\
  (v_inv (RefPtr _ n) (x,f,tf,heap) <=>
     (x = Pointer (f ' n) (Word 0w)) /\ n IN FDOM f) /\
  (v_inv (Block ts n vs) (x,f,tf,heap) <=>
     if vs = []
     then (x = Data (Word (BlockNil n))) /\
          n < dimword(:'a) DIV 16 /\
          ts = 0
     else
       ?ptr xs.
         EVERY2 (\v x. v_inv v (x,f,tf,heap)) vs xs /\
         FLOOKUP tf ts = SOME ptr ∧
         (x = Pointer ptr (Word (ptr_bits conf n (LENGTH xs)))) /\
         (heap_lookup ptr heap = SOME (BlockRep n xs)))
Termination
  WF_REL_TAC `measure (v_size o FST)` \\ rpt strip_tac
  \\ imp_res_tac v_size_LEMMA \\ DECIDE_TAC
End

Definition get_refs_def:
  (get_refs (Number _) = []) /\
  (get_refs (Word64 _) = []) /\
  (get_refs (CodePtr _) = []) /\
  (get_refs (RefPtr _ p) = [p]) /\
  (get_refs (Block _ _ vs) = FLAT (MAP get_refs vs))
Termination
  WF_REL_TAC `measure (v_size)` \\ rpt strip_tac \\ Induct_on `vs`
  \\ srw_tac [] [v_size_def] \\ res_tac \\ DECIDE_TAC
End

Definition ref_edge_def:
  ref_edge refs (x:num) (y:num) =
    case lookup x refs of
    | SOME (ValueArray ys) => MEM y (get_refs (Block 0 ARB ys))
    | _ => F
End

Definition reachable_refs_def:
  reachable_refs roots refs t =
    ?x r. MEM x roots /\ MEM r (get_refs x) /\ RTC (ref_edge refs) r t
End

Definition RefBlock_def:
  RefBlock xs = DataElement xs (LENGTH xs) (RefTag,[])
End

Definition bc_ref_inv_def:
  bc_ref_inv conf n refs (f,tf,heap,be) =
    case (FLOOKUP f n, lookup n refs) of
    | (SOME x, SOME (ValueArray ys)) =>
        (?zs. (heap_lookup x heap = SOME (RefBlock zs)) /\
              EVERY2 (\z y. v_inv conf y (z,f,tf,heap)) zs ys)
    | (SOME x, SOME (ByteArray flag bs)) =>
        let ws = LENGTH bs DIV (dimindex (:α) DIV 8) + 1 in
          (heap_lookup x heap = SOME (Bytes be flag bs (REPLICATE ws (0w:'a word))))
    | _ => F
End

(* TODO: MOVE *)
Definition v_all_ts_def:
  v_all_ts (Block ts _ xs) = ts :: FLAT (MAP v_all_ts xs)
∧ v_all_ts _ = []
Termination
  WF_REL_TAC `measure (v_size)` \\ rpt strip_tac \\ Induct_on `xs`
  \\ srw_tac [] [v_size_def] \\ res_tac \\ DECIDE_TAC
End

(* TODO: MOVE *)
Definition all_ts_def:
  all_ts refs stack =
    let refs_v = {x | ∃n l. sptree$lookup n refs = SOME (ValueArray l) ∧ MEM x l}
    in {ts | ∃x. (x ∈ refs_v ∨ MEM x stack) ∧ MEM ts (v_all_ts x)}
End

Definition be_ok_def:
  be_ok b1 b2 ⇔ b1 = b2
End

(* THIS IS IMPORTANT *)
Definition bc_stack_ref_inv_def:
  bc_stack_ref_inv conf ts stack refs (roots, heap, be) =
    ?f tf.
      INJ (FAPPLY f) (FDOM f) { a | isSomeDataElement (heap_lookup a heap) } /\
      FDOM f SUBSET (domain refs) /\
      INJ (FAPPLY tf) (FDOM tf) { a | isSomeDataElement (heap_lookup a heap) } /\
      FDOM tf SUBSET (all_ts refs stack) /\
      FDOM tf SUBSET { n | n < ts } /\ be_ok conf.be be /\
      EVERY2 (\v x. v_inv conf v (x,f,tf,heap)) stack roots /\
      !n. reachable_refs stack refs n ==> bc_ref_inv conf n refs (f,tf,heap,be)
End

Definition data_up_to_def:
  data_up_to a heap =
    ?h1 h2. heap_split a heap = SOME (h1,h2) /\ EVERY isDataElement h1
End

Definition unused_space_inv_def:
  unused_space_inv ptr l heap <=>
    (l <> 0 ==> (heap_lookup ptr heap = SOME (Unused (l-1)))) /\
    ptr + l <= heap_length heap /\
    data_up_to ptr heap
End

Definition isRef_def:
  isRef (DataElement ys l (tag,qs)) = (tag = RefTag) /\
  isRef _ = F
End

Definition gen_start_ok_def:
  gen_start_ok heap refs_start gen_start =
    ?h1 h2.
      heap_split gen_start heap = SOME (h1,h2) /\
      !xs l d p e.
        MEM (DataElement xs l d) h1 /\ MEM (Pointer p e) xs ==>
        p < gen_start \/ refs_start <= p
End

Definition gen_state_ok_def:
  gen_state_ok a refs_start heap (GenState _ starts) <=>
    EVERY (\s. s <= a) starts /\
    EVERY (gen_start_ok heap refs_start) starts
End

Definition gc_kind_inv_def:
  gc_kind_inv c a sp sp1 (gens:gen_state) heap <=>
    case c.gc_kind of
    | None => (sp1 = 0n)
    | Simple => (sp1 = 0n)
    | Generational sizes =>
        gen_state_ok a (a + sp + sp1) heap gens /\
        ?h1 h2. (heap_split (a + sp + sp1) heap = SOME (h1,h2)) /\
                EVERY (\x. ~isRef x) h1 /\ EVERY isRef h2
End

Definition abs_ml_inv_def:
  abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts <=>
    roots_ok roots heap /\ heap_ok heap limit /\
    gc_kind_inv conf a sp sp1 gens heap /\
    unused_space_inv a (sp+sp1) heap /\
    bc_stack_ref_inv conf ts stack refs (roots,heap,be)
End

(* --- *)

(* TODO: move/reorganise various things in this file *)

Theorem word_list_limit:
   EVERY isWord ws ∧ ALL_DISTINCT ws ⇒
    LENGTH (ws:'a word_loc list) ≤ dimword(:'a)
Proof
  rw[]
  \\ `LENGTH ws = CARD (set ws)` by simp[ALL_DISTINCT_CARD_LIST_TO_SET]
  \\ pop_assum SUBST_ALL_TAC
  \\ CONV_TAC(RAND_CONV(REWR_CONV(GSYM CARD_COUNT)))
  \\ CCONTR_TAC
  \\ pop_assum (strip_assume_tac o REWRITE_RULE[NOT_LESS_EQUAL])
  \\ `FINITE (count (dimword (:'a)))` by simp[]
  \\ imp_res_tac PHP
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ simp[]
  \\ qexists_tac`w2n o theWord`
  \\ simp[INJ_DEF] \\ fs[EVERY_MEM,isWord_exists]
  \\ rw[] \\ res_tac \\ fs[theWord_def]
  \\ metis_tac[w2n_lt]
QED

Theorem MOD_EQ_0_0:
   ∀n b. 0 < b ⇒ (n MOD b = 0) ⇒ n < b ⇒ (n = 0)
Proof
  rw[MOD_EQ_0_DIVISOR] >> Cases_on`d`>>fs[]
QED

Theorem EVERY2_IMP_EVERY:
   !xs ys. EVERY2 P xs ys ==> EVERY (\(x,y). P y x) (ZIP(ys,xs))
Proof
  Induct \\ Cases_on `ys` \\ full_simp_tac(srw_ss())[]
QED

Theorem EVERY2_IMP_EVERY2:
   !xs ys P1 P2.
      (!x y. MEM x xs /\ MEM y ys /\ P1 x y ==> P2 x y) ==>
      EVERY2 P1 xs ys ==> EVERY2 P2 xs ys
Proof
  Induct \\ Cases_on `ys` \\ full_simp_tac (srw_ss()) []
  \\ rpt strip_tac \\ metis_tac []
QED

Theorem MEM_EVERY2_IMP:
   !l x zs P. MEM x l /\ EVERY2 P zs l ==> ?z. MEM z zs /\ P z x
Proof
  Induct \\ Cases_on `zs` \\ full_simp_tac (srw_ss()) [] \\ metis_tac []
QED

val EVERY2_LENGTH = LIST_REL_LENGTH
val EVERY2_IMP_LENGTH = EVERY2_LENGTH

Theorem EVERY2_APPEND_CONS:
   !xs y ys zs P. EVERY2 P (xs ++ y::ys) zs ==>
                   ?t1 t t2. (zs = t1 ++ t::t2) /\ (LENGTH t1 = LENGTH xs) /\
                             EVERY2 P xs t1 /\ P y t /\ EVERY2 P ys t2
Proof
  Induct \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `zs` \\ full_simp_tac (srw_ss()) []
  \\ rpt strip_tac
  \\ res_tac \\ full_simp_tac std_ss []
  \\ Q.LIST_EXISTS_TAC [`h::t1`,`t'`,`t2`]
  \\ full_simp_tac (srw_ss()) []
QED

Theorem EVERY2_SWAP:
   !xs ys. EVERY2 P xs ys ==> EVERY2 (\y x. P x y) ys xs
Proof
  Induct \\ Cases_on `ys` \\ full_simp_tac (srw_ss()) []
QED

Theorem EVERY2_APPEND_IMP_APPEND:
   !xs1 xs2 ys P.
      EVERY2 P (xs1 ++ xs2) ys ==>
      ?ys1 ys2. (ys = ys1 ++ ys2) /\ EVERY2 P xs1 ys1 /\ EVERY2 P xs2 ys2
Proof
  Induct \\ Cases_on `ys` \\ full_simp_tac (srw_ss()) [] \\ rpt strip_tac
  \\ res_tac \\ full_simp_tac std_ss []
  \\ Q.LIST_EXISTS_TAC [`h::ys1`,`ys2`]
  \\ full_simp_tac std_ss [APPEND,LIST_REL_def] \\ metis_tac[]
QED

val EVERY2_IMP_APPEND = rich_listTheory.EVERY2_APPEND_suff
val IMP_EVERY2_APPEND = EVERY2_IMP_APPEND

val EVERY2_EQ_EL = LIST_REL_EL_EQN

val EVERY2_IMP_EL = METIS_PROVE[EVERY2_EQ_EL]
  ``!xs ys P. EVERY2 P xs ys ==> !n. n < LENGTH ys ==> P (EL n xs) (EL n ys)``

Triviality EVERY2_MAP_FST_SND:
  !xs. EVERY2 P (MAP FST xs) (MAP SND xs) = EVERY (\(x,y). P x y) xs
Proof
  Induct \\ srw_tac [] [LIST_REL_def] \\ Cases_on `h` \\ srw_tac [] []
QED

Theorem fapply_fupdate_update:
   $' (f |+ p) = (FST p =+ SND p) ($' f)
Proof
  Cases_on`p`>>
  simp[FUN_EQ_THM,FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM] >> rw[]
QED

Triviality heap_lookup_APPEND1:
  ∀h1 z h2.
    heap_length h1 ≤ z ⇒
    (heap_lookup z (h1 ++ h2) = heap_lookup (z - heap_length h1) h2)
Proof
  Induct >>fs[heap_lookup_def,heap_length_def] >> rw[] >> simp[]
  >> fsrw_tac[ARITH_ss][] >> Cases_on`h`>>fs[el_length_def]
QED

Triviality heap_lookup_APPEND2:
  ∀h1 z h2.
    z < heap_length h1 ⇒
    (heap_lookup z (h1 ++ h2) = heap_lookup z h1)
Proof
  Induct >> fs[heap_lookup_def,heap_length_def] >> rw[] >>
  simp[]
QED

Theorem heap_lookup_APPEND:
   heap_lookup a (h1 ++ h2) =
    if a < heap_length h1 then
    heap_lookup a h1 else
    heap_lookup (a-heap_length h1) h2
Proof
  rw[heap_lookup_APPEND2] >>
  simp[heap_lookup_APPEND1]
QED

(* Prove refinement is maintained past GC calls *)

Triviality LENGTH_ADDR_MAP:
  !xs f. LENGTH (ADDR_MAP f xs) = LENGTH xs
Proof
  Induct \\ TRY (Cases_on `h`) \\ srw_tac [] [ADDR_MAP_def]
QED

Triviality MEM_IMP_v_size:
  !l a. MEM a l ==> v_size a < 1 + list_size v_size l
Proof
  rw []
  \\ imp_res_tac MEM_list_size
  \\ pop_assum $ qspec_then ‘v_size’ mp_tac \\ gvs []
QED

Triviality EL_ADDR_MAP:
  !xs n f.
      n < LENGTH xs ==> (EL n (ADDR_MAP f xs) = ADDR_APPLY f (EL n xs))
Proof
  Induct \\ full_simp_tac (srw_ss()) [] \\ Cases_on `n` \\ Cases_on `h`
  \\ full_simp_tac (srw_ss()) [ADDR_MAP_def,ADDR_APPLY_def]
QED

val _ = augment_srw_ss [rewrites [LIST_REL_def]];

Triviality v_inv_related:
  !w x f tf.
        gc_shared$gc_related g heap1 (heap2:'a ml_heap) /\
      (!ptr u. (x = Pointer ptr u) ==> ptr IN FDOM g) /\
      v_inv conf w (x,f,tf,heap1) ==>
      v_inv conf w (ADDR_APPLY (FAPPLY g) x,g f_o_f f,g f_o_f tf,heap2) /\
      EVERY (\n. f ' n IN FDOM g) (get_refs w)
Proof
  completeInduct_on `v_size w` \\ NTAC 6 strip_tac
  \\ fs[PULL_FORALL] \\ Cases_on `w` THEN1
   (fs[v_inv_def,get_refs_def,EVERY_DEF]
    \\ Cases_on `small_int (:'a) i` \\ fs [] THEN1
     (full_simp_tac (srw_ss()) [ADDR_APPLY_def,Bignum_def]
      \\ fs[gc_related_def] \\ res_tac
      \\ fs[ADDR_MAP_def] \\ fs [])
    \\ fs [gc_related_def,ADDR_APPLY_def,Bignum_def]
    \\ pairarg_tac \\ fs [] \\ res_tac \\ fs [ADDR_MAP_def])
  THEN1
   (fs[v_inv_def,get_refs_def,EVERY_DEF]
    \\ full_simp_tac (srw_ss()) [ADDR_APPLY_def]
    \\ fs[gc_related_def]
    \\ first_x_assum drule
    \\ qspecl_then[`:'a`,`c`]strip_assume_tac Word64Rep_DataElement
    \\ fs[ADDR_MAP_def])
  THEN1
   (full_simp_tac (srw_ss()) [v_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ Cases_on `l = []` \\ fs[]
    THEN1 (full_simp_tac (srw_ss()) [get_refs_def,ADDR_APPLY_def])
    \\ full_simp_tac (srw_ss()) [v_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ fs[gc_related_def] \\ res_tac
    \\ full_simp_tac (srw_ss()) [] \\ NTAC 2 (POP_ASSUM MP_TAC)
    \\ fs[LENGTH_ADDR_MAP] \\ strip_tac
    \\ reverse strip_tac THEN1
     (fs[get_refs_def,EVERY_MEM,MEM_FLAT,PULL_EXISTS,MEM_MAP]
      \\ gvs[v_size_def] \\ rpt strip_tac
      \\ Q.MATCH_ASSUM_RENAME_TAC `MEM k (get_f a)`
      \\ imp_res_tac MEM_IMP_v_size
      \\ last_x_assum $ qspec_then ‘a’ mp_tac \\ gvs []
      \\ `?l1 l2. l = l1 ++ a::l2` by metis_tac [MEM_SPLIT]
      \\ full_simp_tac std_ss [] \\ imp_res_tac LIST_REL_SPLIT1
      \\ fs[] \\ rw[] \\ fs[]
      \\ res_tac \\ metis_tac [])
    \\ fs[EVERY2_EVERY,LENGTH_ADDR_MAP,EVERY_MEM,FORALL_PROD]
    \\ qpat_x_assum `LENGTH l = LENGTH xs` ASSUME_TAC
    \\ fs[MEM_ZIP,LENGTH_ADDR_MAP,PULL_EXISTS]
    \\ reverse strip_tac
    THEN1 (fs [f_o_f_DEF,FLOOKUP_DEF])
    \\ strip_tac \\ strip_tac
    \\ Q.MATCH_ASSUM_RENAME_TAC `t < LENGTH xs` \\ res_tac
    \\ `MEM (EL t xs) xs` by (fs[MEM_EL] \\ metis_tac [])
    \\ `MEM (EL t l) l` by (fs[MEM_EL] \\ metis_tac [])
    \\ `(!ptr u. (EL t xs = Pointer ptr u) ==> ptr IN FDOM g)` by metis_tac []
    \\ last_x_assum $ qspec_then ‘EL t l’ mp_tac
    \\ imp_res_tac MEM_IMP_v_size \\ gvs []
    \\ res_tac \\ fs[EL_ADDR_MAP]
    \\ first_assum match_mp_tac \\ fs [])
  THEN1
    (full_simp_tac (srw_ss()) [v_inv_def,ADDR_APPLY_def,get_refs_def])
  THEN1
    (full_simp_tac (srw_ss()) [v_inv_def,ADDR_APPLY_def]
     \\ sg `n IN FDOM (g f_o_f f)` \\ asm_simp_tac std_ss []
     \\ full_simp_tac (srw_ss()) [f_o_f_DEF,get_refs_def])
QED

Triviality EVERY2_ADDR_MAP:
  !zs l. EVERY2 P (ADDR_MAP g zs) l <=>
           EVERY2 (\x y. P (ADDR_APPLY g x) y) zs l
Proof
  Induct \\ Cases_on `l`
  \\ full_simp_tac std_ss [LIST_REL_def,ADDR_MAP_def] \\ Cases
  \\ full_simp_tac std_ss [LIST_REL_def,ADDR_MAP_def,ADDR_APPLY_def]
QED

Triviality bc_ref_inv_related:
  gc_shared$gc_related g heap1 heap2 /\
    bc_ref_inv conf n refs (f,tf,heap1,be) /\ (f ' n) IN FDOM g ==>
    bc_ref_inv conf n refs (g f_o_f f,g f_o_f tf,heap2,be)
Proof
  full_simp_tac std_ss [bc_ref_inv_def] \\ strip_tac \\ full_simp_tac std_ss []
  \\ MP_TAC v_inv_related \\ asm_simp_tac std_ss []
  \\ full_simp_tac (srw_ss()) [f_o_f_DEF,gc_related_def,RefBlock_def] \\ res_tac
  \\ Cases_on `FLOOKUP f n` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `lookup n refs` \\ full_simp_tac (srw_ss()) []
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,f_o_f_DEF]
  \\ Cases_on `x'` \\ full_simp_tac (srw_ss()) []
  \\ TRY (fs[Bytes_def,LET_THM] >> res_tac >> simp[ADDR_MAP_def]
          \\ rw [] \\ qexists_tac `ws` \\ fs [] >> NO_TAC)
  \\ res_tac \\ full_simp_tac (srw_ss()) [LENGTH_ADDR_MAP,EVERY2_ADDR_MAP]
  \\ rpt strip_tac \\ qpat_x_assum `EVERY2 qqq zs l` MP_TAC
  \\ match_mp_tac EVERY2_IMP_EVERY2 \\ simp_tac std_ss [] \\ rpt strip_tac
  \\ Cases_on `x'` \\ full_simp_tac (srw_ss()) [ADDR_APPLY_def]
  \\ res_tac \\ fs [ADDR_APPLY_def]
QED

Triviality RTC_lemma:
  !r n. RTC (ref_edge refs) r n ==>
          (!m. RTC (ref_edge refs) r m ==> bc_ref_inv conf m refs (f,tf,heap,be)) /\
          gc_shared$gc_related g heap heap2 /\
          f ' r IN FDOM g ==> f ' n IN FDOM g
Proof
  ho_match_mp_tac RTC_INDUCT \\ full_simp_tac std_ss [] \\ rpt strip_tac
  \\ full_simp_tac std_ss []
  \\ qpat_x_assum `bb ==> bbb` match_mp_tac \\ full_simp_tac std_ss []
  \\ strip_tac THEN1
   (rpt strip_tac \\ qpat_x_assum `!x.bb` match_mp_tac \\ metis_tac [RTC_CASES1])
  \\ `RTC (ref_edge refs) r r' /\ RTC (ref_edge refs) r r` by metis_tac [RTC_CASES1]
  \\ res_tac \\ qpat_x_assum `!x.bb` (K ALL_TAC)
  \\ full_simp_tac std_ss [bc_ref_inv_def,RefBlock_def,RTC_REFL]
  \\ Cases_on `FLOOKUP f r` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `FLOOKUP f r'` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `lookup r refs` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `lookup r' refs` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `x''` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `x'''` \\ full_simp_tac (srw_ss()) []
  \\ imp_res_tac v_inv_related
  \\ full_simp_tac std_ss [ref_edge_def]
  \\ full_simp_tac std_ss [gc_related_def,INJ_DEF,GSPECIFICATION]
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF] \\ srw_tac [] []
  \\ res_tac \\ full_simp_tac std_ss [get_refs_def] \\ srw_tac [] []
  \\ full_simp_tac std_ss [MEM_FLAT,MEM_MAP] \\ srw_tac [] []
  \\ full_simp_tac std_ss [ref_edge_def,EVERY_MEM]
  \\ full_simp_tac std_ss [PULL_FORALL,AND_IMP_INTRO]
  \\ res_tac \\ CCONTR_TAC \\ full_simp_tac std_ss []
  \\ srw_tac [] [] \\ POP_ASSUM MP_TAC \\ simp_tac std_ss []
  \\ imp_res_tac MEM_EVERY2_IMP \\ fs []
  \\ fs [] \\ metis_tac []
QED

Triviality reachable_refs_lemma:
  gc_related g heap heap2 /\
    EVERY2 (\v x. v_inv conf v (x,f,tf,heap)) stack roots /\
    (!n. reachable_refs stack refs n ==> bc_ref_inv conf n refs (f,tf,heap,be)) /\
    (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM g) ==>
    (!n. reachable_refs stack refs n ==> n IN FDOM f /\ (f ' n) IN FDOM g)
Proof
  NTAC 3 strip_tac \\ full_simp_tac std_ss [reachable_refs_def,PULL_EXISTS]
  \\ `?xs1 xs2. stack = xs1 ++ x::xs2` by metis_tac [MEM_SPLIT]
  \\ full_simp_tac std_ss [] \\ imp_res_tac LIST_REL_SPLIT1
  \\ full_simp_tac std_ss [LIST_REL_CONS1] \\ rveq
  \\ full_simp_tac std_ss [MEM,MEM_APPEND,LIST_REL_CONS1]
  \\ `EVERY (\n. f ' n IN FDOM g) (get_refs x)` by metis_tac [v_inv_related]
  \\ full_simp_tac std_ss [EVERY_MEM] \\ res_tac \\ full_simp_tac std_ss []
  \\ `n IN FDOM f` by (CCONTR_TAC
    \\ full_simp_tac (srw_ss()) [bc_ref_inv_def,FLOOKUP_DEF])
  \\ full_simp_tac std_ss []
  \\ `bc_ref_inv conf r refs (f,tf,heap,be)` by metis_tac [RTC_REFL]
  \\ `(!m. RTC (ref_edge refs) r m ==>
           bc_ref_inv conf m refs (f,tf,heap,be))` by metis_tac [] \\ imp_res_tac RTC_lemma
QED

Triviality bc_stack_ref_inv_related:
  gc_related g heap1 heap2 /\
    bc_stack_ref_inv conf ts stack refs (roots,heap1,be) /\
    (!ptr u. MEM (Pointer ptr u) roots ==> ptr IN FDOM g) ==>
    bc_stack_ref_inv conf ts stack refs (ADDR_MAP (FAPPLY g) roots,heap2,be)
Proof
  rpt strip_tac \\ full_simp_tac std_ss [bc_stack_ref_inv_def]
  \\ qexists_tac `g f_o_f f`
  \\ qexists_tac `g f_o_f tf`
  \\ rpt strip_tac
  THEN1 (full_simp_tac (srw_ss()) [INJ_DEF,gc_related_def,f_o_f_DEF])
  THEN1 (full_simp_tac (srw_ss()) [f_o_f_DEF,SUBSET_DEF])
  THEN1 (full_simp_tac (srw_ss()) [INJ_DEF,gc_related_def,f_o_f_DEF])
  THEN1 (full_simp_tac (srw_ss()) [f_o_f_DEF,SUBSET_DEF])
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
  \\ metis_tac [reachable_refs_lemma]
QED

Theorem data_up_to_APPEND[simp]:
   data_up_to (heap_length xs) (xs ++ ys) <=> EVERY isDataElement xs
Proof
  fs [data_up_to_def,heap_split_APPEND_if,heap_split_0]
QED

Definition all_reachable_from_roots_def:
  all_reachable_from_roots roots heap <=>
    !p xs l d.
       heap_lookup p heap = SOME (DataElement xs l d) ==>
       p IN reachable_addresses roots heap
End

val IN_reachable_addresses =
  ``x ∈ reachable_addresses roots heap``
  |> SIMP_CONV std_ss [Once IN_DEF,reachable_addresses_def]

Theorem reachable_addresses_related:
  k ∈ reachable_addresses roots heap /\ gc_related f heap heap2 /\
  reachable_addresses roots heap SUBSET FDOM f ==>
  f ' k ∈ reachable_addresses (ADDR_MAP ($' f) roots) heap2
Proof
  fs [IN_reachable_addresses,PULL_EXISTS]
  \\ Cases_on `gc_related f heap heap2` \\ fs [] \\ rw []
  \\ qexists_tac `t`
  \\ qexists_tac `f ' x`
  \\ strip_tac
  THEN1 (fs [MEM_SPLIT,ADDR_MAP_APPEND,ADDR_MAP_def] \\ metis_tac [])
  \\ `x IN FDOM f` by
   (fs [SUBSET_DEF] \\ pop_assum match_mp_tac
    \\ fs [IN_reachable_addresses] \\ asm_exists_tac \\ fs [])
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ qid_spec_tac `k`
  \\ qid_spec_tac `x`
  \\ ho_match_mp_tac RTC_INDUCT
  \\ fs [] \\ rw []
  \\ once_rewrite_tac [RTC_CASES1] \\ disj2_tac
  \\ fs [gc_related_def]
  \\ fs [gc_edge_def,PULL_EXISTS]
  \\ first_x_assum drule \\ fs []
  \\ rw [] \\ res_tac \\ fs []
  \\ once_rewrite_tac [CONJ_COMM]
  \\ asm_exists_tac \\ fs []
  \\ fs [MEM_SPLIT,ADDR_MAP_APPEND,ADDR_MAP_def] \\ metis_tac []
QED

Theorem IMP_all_reachable_from_roots:
  FDOM f = reachable_addresses roots heap /\
  FRANGE f = { a | isSomeDataElement (heap_lookup a heap2) } /\
  gc_related f heap heap2 ==>
  all_reachable_from_roots (ADDR_MAP ($' f) roots) heap2
Proof
  fs [all_reachable_from_roots_def,EXTENSION] \\ rw []
  \\ `p IN FRANGE f` by fs [isSomeDataElement_def]
  \\ pop_assum mp_tac
  \\ simp_tac std_ss [IN_FRANGE]
  \\ strip_tac \\ rveq
  \\ match_mp_tac reachable_addresses_related
  \\ res_tac \\ fs [] \\ fs [SUBSET_DEF]
QED

Theorem heap_lookup_expand_eq_SOME:
  heap_lookup a (heap ++ heap_expand n) = SOME (DataElement ys l d) <=>
  heap_lookup a heap = SOME (DataElement ys l d)
Proof
  fs [heap_lookup_APPEND]
  \\ Cases_on `heap_lookup a heap` \\ fs [] \\ rw []
  \\ imp_res_tac gc_sharedTheory.heap_lookup_LESS \\ fs []
  \\ rw [heap_lookup_def,heap_expand_def]
QED

Theorem isSomeDataElement_heap_lookup:
  isSomeDataElement (heap_lookup a (heap ++ heap_expand n)) =
  isSomeDataElement (heap_lookup a heap)
Proof
  fs [isSomeDataElement_def,heap_lookup_expand_eq_SOME]
QED

Theorem gc_related_APPEND_heap_expand:
  gc_related f heap (heap2 ++ heap_expand n) = gc_related f heap heap2
Proof
  fs [gc_related_def,isSomeDataElement_heap_lookup,heap_lookup_expand_eq_SOME]
QED

Theorem full_gc_thm:
   abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
   conf.gc_kind = Simple ==>
    ?roots2 heap2 a2.
      (full_gc (roots,heap,limit) = (roots2,heap2,a2,T)) /\
       abs_ml_inv conf stack refs
        (roots2,heap2 ++ heap_expand (limit - a2),be,
         a2,limit - a2,0,gens) limit ts /\
      (heap_length heap2 = a2) /\
      (heap_length (heap_filter (reachable_addresses roots heap) heap) =
       heap_length heap2) /\
      all_reachable_from_roots roots2 (heap2 ++ heap_expand (limit - a2)) /\
      EVERY isDataElement heap2
Proof
  simp_tac std_ss [abs_ml_inv_def,GSYM CONJ_ASSOC]
  \\ rpt strip_tac \\ drule full_gc_related
  \\ asm_simp_tac std_ss [] \\ strip_tac
  \\ qpat_x_assum `heap_length heap2 = _` (assume_tac o GSYM)
  \\ `heap_length heap2 = a2` by (imp_res_tac full_gc_LENGTH \\ full_simp_tac std_ss [] \\ metis_tac [])
  \\ `unused_space_inv a2 (limit - a2) (heap2 ++ heap_expand (limit - a2))` by
   (full_simp_tac std_ss [unused_space_inv_def] \\ rpt strip_tac
    \\ full_simp_tac std_ss [heap_expand_def]
    \\ imp_res_tac full_gc_IMP_isDataElement
    \\ rveq \\ fs [heap_lookup_APPEND,heap_lookup_def,heap_length_APPEND]
    \\ rw [heap_length_def,el_length_def])
  \\ full_simp_tac std_ss [] \\ simp_tac std_ss [CONJ_ASSOC]
  \\ reverse conj_tac THEN1
    (drule (GEN_ALL IMP_all_reachable_from_roots)
     \\ disch_then match_mp_tac \\ fs [gc_related_APPEND_heap_expand]
     \\ fs [isSomeDataElement_heap_lookup])
  \\ reverse conj_tac THEN1 metis_tac []
  \\ reverse conj_tac THEN1
   (match_mp_tac (GEN_ALL bc_stack_ref_inv_related) \\ full_simp_tac std_ss []
    \\ qexists_tac `heap` \\ full_simp_tac std_ss []
    \\ rw [] \\ fs [] \\ res_tac \\ fs []
    \\ fs [reachable_addresses_def,IN_DEF]
    \\ asm_exists_tac \\ fs [])
  \\ conj_tac THEN1
   (qpat_x_assum `full_gc (roots,heap,limit) = xxx` (ASSUME_TAC o GSYM)
    \\ imp_res_tac full_gc_ok \\ NTAC 3 (POP_ASSUM (K ALL_TAC))
    \\ full_simp_tac std_ss [] \\ metis_tac [])
  \\ fs [gc_kind_inv_def] \\ CASE_TAC \\ fs []
QED

Definition make_gc_conf_def:
  make_gc_conf limit =
    <| limit := limit; isRef := \x. FST x = RefTag |>
        : (tag # 'a) gen_gc$gen_gc_conf
End

Triviality gc_move_data_refs_split:
  (gen_gc$gc_move cc s x = (x1,s1)) /\ (!t r. (cc.isRef (t,r) <=> t = RefTag))
   /\ EVERY isDataElement s.h2 /\(EVERY (λx. ¬isRef x)) s.h2 /\ EVERY isRef s.r4 ==>
   EVERY isDataElement s1.h2 /\
   (EVERY (λx. ¬isRef x)) s1.h2 /\ EVERY isRef s1.r4
Proof
  Cases_on `x` >> fs[gen_gcTheory.gc_move_def]
  >> rpt strip_tac >> rveq >> fs[]
  >> every_case_tac >> rveq >> fs[]
  >> TRY pairarg_tac >> fs[]
  >> qpat_x_assum `_ = s1` (assume_tac o GSYM) >> fs[isDataElement_def]
  >> Cases_on `b` >> fs[isRef_def] >> metis_tac[]
QED

Triviality gc_move_list_data_refs_split:
  !x x1 s s1.
  (gen_gc$gc_move_list cc s x = (x1,s1)) /\ (!t r. (cc.isRef (t,r) <=> t = RefTag))
   /\ EVERY isDataElement s.h2 /\(EVERY (λx. ¬isRef x)) s.h2 /\ EVERY isRef s.r4 ==>
   EVERY isDataElement s1.h2 /\(EVERY (λx. ¬isRef x)) s1.h2 /\ EVERY isRef s1.r4
Proof
  Induct >> fs[gen_gcTheory.gc_move_list_def]
  >> rpt strip_tac >> rpt(pairarg_tac >> fs[])
  >> drule gc_move_data_refs_split >> metis_tac[]
QED

Triviality gc_move_refs_data_refs_split:
  !cc s s1.
  (gen_gc$gc_move_refs cc s = s1) /\ (!t r. (cc.isRef (t,r) <=> t = RefTag))
   /\ EVERY isDataElement (s.h1++s.h2) /\ (EVERY (λx. ¬isRef x)) (s.h1++s.h2) /\
   EVERY isRef (s.r1 ++ s.r2 ++ s.r3 ++ s.r4) ==>
   EVERY isDataElement (s1.h1++s1.h2) /\
   (EVERY (λx. ¬isRef x)) (s1.h1++s1.h2) /\
   EVERY isRef (s1.r1 ++ s1.r2 ++ s1.r3 ++ s1.r4)
Proof
  recInduct (fetch "gen_gc" "gc_move_refs_ind")
  >> rpt strip_tac
  >> qpat_x_assum `gc_move_refs _ _ = _` mp_tac
  >> simp[Once gen_gcTheory.gc_move_refs_def]
  >> strip_tac >> every_case_tac
  >> TRY pairarg_tac >> fs[]
  >> qpat_x_assum `_ = s1` (assume_tac o GSYM) >> fs[]
  >> drule gen_gcTheory.gc_move_list_IMP >> strip_tac >> fs[]
  >> drule gc_move_list_data_refs_split >> fs[] >> strip_tac
  >> first_x_assum drule >> fs[]
  >> Cases_on `b` >> fs[isRef_def]
QED

Triviality gc_move_data_data_refs_split:
  !cc s s1.
  (gen_gc$gc_move_data cc s = s1) /\ (!t r. (cc.isRef (t,r) <=> t = RefTag))
   /\ (EVERY (λx. ¬isRef x)) (s.h1++s.h2) /\
   EVERY isDataElement (s.h1++s.h2) /\
   EVERY isRef (s.r1 ++ s.r2 ++ s.r3 ++ s.r4) ==>
   EVERY isDataElement (s1.h1++s1.h2) /\
   (EVERY (λx. ¬isRef x)) (s1.h1++s1.h2) /\
   EVERY isRef (s1.r1 ++ s1.r2 ++ s1.r3 ++ s1.r4)
Proof
  recInduct (fetch "gen_gc" "gc_move_data_ind")
  >> rpt strip_tac >> qpat_x_assum `gc_move_data _ _ = _` mp_tac
  >> simp[Once gen_gcTheory.gc_move_data_def]
  >> every_case_tac >> fs[] >> rpt strip_tac >> rveq >> fs[]
  >> pairarg_tac >> fs[]
  >> drule gen_gcTheory.gc_move_list_IMP >> strip_tac >> fs[]
  >> drule gc_move_list_data_refs_split >> fs[] >> strip_tac
  >> first_x_assum drule >> fs[]
  >> Cases_on `b` >> fs[isRef_def]
  >> Cases_on `state''.h2` >> fs[] >> rfs[isDataElement_def]
QED

Triviality gc_move_loop_data_refs_split:
  !clock cc s s1.
  (gen_gc$gc_move_loop cc s clock = s1) /\
  (!t r. (cc.isRef (t,r) <=> t = RefTag)) /\
  EVERY isDataElement (s.h1++s.h2) /\
  (EVERY (λx. ¬isRef x)) (s.h1++s.h2) /\
  EVERY isRef (s.r1 ++ s.r2 ++ s.r3 ++ s.r4) ==>
  EVERY isDataElement (s1.h1++s1.h2) /\
  (EVERY (λx. ¬isRef x)) (s1.h1++s1.h2) /\
  EVERY isRef (s1.r1 ++ s1.r2 ++ s1.r3 ++ s1.r4)
Proof
  Induct >> rpt strip_tac >> qpat_x_assum `gc_move_loop _ _ _ = _` mp_tac
  >> PURE_ONCE_REWRITE_TAC [gen_gcTheory.gc_move_loop_def]
  >> every_case_tac >> fs[]
  >> rpt strip_tac >> TRY(rveq >> fs[] >> NO_TAC)
  >> TRY(rename1 `s.r4 = h1::t1`)
  >> `gc_move_refs cc (s with <|r4 := []; r2 := h1::t1|>) =
      gc_move_refs cc (s with <|r4 := []; r2 := h1::t1|>)` by fs[]
  >> `gc_move_data cc s =
      gc_move_data cc s` by fs[]
  >> drule gc_move_refs_data_refs_split >> drule gc_move_data_data_refs_split
  >> fs[] >> rpt strip_tac
  >> qpat_x_assum `_ = s1` (assume_tac o GSYM) >> fs[]
  >> rpt strip_tac >> fs[]
QED

Triviality gen_gc_data_refs_split:
  !cc roots heap.
  (gen_gc cc (roots,heap) = (roots1,s)) /\
  (!t r. (cc.isRef (t,r) <=> t = RefTag)) ==>
  (EVERY (λx. ¬isRef x)) (s.h1 ++ s.h2) /\
  EVERY isDataElement (s.h1 ++ s.h2) /\
  EVERY isRef (s.r1 ++ s.r2 ++ s.r3 ++ s.r4)
Proof
  rpt strip_tac >> fs[gen_gcTheory.gen_gc_def]
  >> rpt (pairarg_tac >> fs[])
  >> drule gc_move_list_data_refs_split >> fs[empty_state_def]
  >> strip_tac
  >> drule gen_gcTheory.gc_move_list_IMP
  >> fs[] >> disch_then (assume_tac o GSYM) >> fs[]
  >> drule gc_move_loop_data_refs_split
  >> fs []
QED

Theorem heap_expand_not_isRef:
  EVERY (λx. ¬isRef x) (heap_expand n)
Proof
  Induct_on `n` >> fs[isRef_def,heap_expand_def]
QED

Definition reset_gens_def:
  reset_gens conf a =
    case conf.gc_kind of
    | Generational sizes => GenState 0 (MAP (K a) sizes)
    | _ => GenState 0 []
End

Theorem gen_state_ok_reset:
   heap_ok (h ++ heap_expand n ++ r) l ==>
    gen_state_ok (heap_length h) (n + heap_length h)
      (h ++ heap_expand n ++ r) (reset_gens conf (heap_length h))
Proof
  strip_tac
  \\ fs [reset_gens_def] \\ TOP_CASE_TAC \\ fs [gen_state_ok_def,reset_gens_def]
  \\ fs [EVERY_MAP] \\ disj2_tac
  \\ fs [gen_start_ok_def]
  \\ rewrite_tac [GSYM APPEND_ASSOC]
  \\ once_rewrite_tac [heap_split_APPEND_if]
  \\ fs [heap_split_0]
  \\ fs [heap_ok_def]
  \\ rw [] \\ res_tac
  \\ rpt (qpat_x_assum `!x._` kall_tac)
  \\ fs [isSomeDataElement_def]
  \\ rfs [heap_lookup_APPEND,heap_length_APPEND,heap_length_heap_expand]
  \\ every_case_tac
  \\ imp_res_tac heap_lookup_MEM
  \\ pop_assum mp_tac \\ fs [heap_expand_def]
QED

Theorem gen_gc_thm:
   abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts ==>
    ?roots2 state2.
      (gen_gc (make_gc_conf limit) (roots,heap) = (roots2,state2)) /\
      abs_ml_inv conf stack refs
        (roots2,state2.h1 ++ heap_expand state2.n ++ state2.r1,be,
         state2.a,state2.n,0,reset_gens conf state2.a) limit ts /\ state2.ok /\
      (heap_length (state2.h1 ⧺ state2.r1) =
       heap_length (heap_filter (reachable_addresses roots heap) heap)) /\
      EVERY isDataElement state2.h1 /\
      EVERY isDataElement state2.r1 /\
      all_reachable_from_roots roots2
        (state2.h1 ++ heap_expand state2.n ++ state2.r1)
Proof
  simp_tac std_ss [abs_ml_inv_def,GSYM CONJ_ASSOC,make_gc_conf_def]
  \\ rpt strip_tac \\ qmatch_goalsub_abbrev_tac `gen_gc cc`
  \\ `heap_ok heap cc.limit` by fs [Abbr `cc`]
  \\ drule gen_gcTheory.gen_gc_related
  \\ disch_then drule \\ strip_tac \\ fs []
  \\ drule gen_gcTheory.gen_gc_ok
  \\ disch_then drule \\ strip_tac \\ fs [] \\ rveq \\ fs []
  \\ `cc.limit = limit` by fs [Abbr`cc`] \\ fs []
  \\ reverse (rpt conj_tac)
  THEN1 (match_mp_tac IMP_all_reachable_from_roots \\ fs [])
  THEN1
   (match_mp_tac (GEN_ALL bc_stack_ref_inv_related) \\ full_simp_tac std_ss []
    \\ qexists_tac `heap` \\ full_simp_tac std_ss []
    \\ rw [] \\ fs [] \\ res_tac \\ fs []
    \\ fs [reachable_addresses_def,IN_DEF] \\ asm_exists_tac \\ fs [])
  THEN1
   (fs [unused_space_inv_def] \\ fs [heap_expand_def]
    \\ rewrite_tac [APPEND,GSYM APPEND_ASSOC]
    \\ fs [heap_lookup_APPEND] \\ fs [heap_lookup_def]
    \\ drule(GEN_ALL gen_gc_data_refs_split) \\ fs[]
    \\ fs[] \\ impl_tac THEN1 (unabbrev_all_tac >> fs[]) \\ fs[]
    \\ fs [heap_length_APPEND] \\ rw [heap_length_def,el_length_def])
  THEN1
   (fs [gc_kind_inv_def] \\ CASE_TAC \\ fs []
    \\ drule(GEN_ALL gen_gc_data_refs_split) \\ fs[]
    \\ fs[] \\ impl_tac THEN1 (unabbrev_all_tac >> fs[]) \\ fs[]
    \\ strip_tac \\ conj_tac
    THEN1 (once_rewrite_tac [ADD_COMM]
           \\ match_mp_tac (GEN_ALL gen_state_ok_reset)
           \\ asm_exists_tac \\ fs [])
    \\ `state'.n + heap_length state'.h1 =
        heap_length(state'.h1 ++ heap_expand state'.n)`
          by fs[heap_length_APPEND,heap_length_heap_expand]
    \\ once_rewrite_tac [ADD_COMM]
    \\ pop_assum (fn thm => PURE_ONCE_REWRITE_TAC [thm])
    \\ PURE_ONCE_REWRITE_TAC [gen_gc_partialTheory.heap_split_length]
    \\ fs[heap_expand_not_isRef])
QED

Definition has_gen_def:
  has_gen (GenState _ xs) <=> xs <> []
End

Theorem heap_split_heap_split:
   !heap n1 n2 h1 h2 h3 h4.
      heap_split n2 heap = SOME (h3,h4) /\
      heap_split n1 heap = SOME (h1,h2) /\ n1 <= n2 ==>
      ?m.
        h2 = m ++ h4 /\ h3 = h1 ++ m /\ heap = h1 ++ m ++ h4 /\
        heap_split (n2 - heap_length h1) h2 = SOME (m,h4)
Proof
  Induct \\ fs [heap_split_def]
  \\ rpt gen_tac
  \\ Cases_on `n2 = 0` \\ fs []
  THEN1 (strip_tac \\ rveq \\ fs [] \\ rveq \\ fs [heap_split_0])
  \\ Cases_on `n2 < el_length h` \\ fs []
  \\ Cases_on `heap_split (n2 − el_length h) heap` \\ fs []
  \\ Cases_on `x` \\ fs []
  \\ Cases_on `n1 = 0` \\ fs []
  THEN1
   (strip_tac \\ rveq \\ fs []
    \\ fs [heap_split_def]
    \\ first_x_assum drule
    \\ disch_then drule \\ fs [])
  \\ TOP_CASE_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ res_tac \\ rfs [] \\ fs [heap_length_def]
QED

Theorem heap_split_LESS_EQ:
   !heap n x. heap_split n heap = SOME x ==> n <= heap_length heap
Proof
  Induct \\ fs [heap_split_def] \\ rw []
  \\ every_case_tac \\ fs [] \\ rveq
  \\ res_tac \\ fs [heap_length_def]
QED

val isRef_heap_expand = prove(
  ``!x. EVERY (λx. ¬isRef x) (heap_expand x)``,
  Cases \\ EVAL_TAC \\ fs [] \\ EVAL_TAC);

Theorem gen_gc_partial_thm:
   abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
   has_gen gens /\ conf.gc_kind = Generational xs ==>
    ?roots2 state2.
      partial_gc
        (make_partial_conf (make_gc_conf limit) gens (a + (sp + sp1)))
        (roots,heap) = (roots2,state2) /\
      abs_ml_inv conf stack refs
        (roots2,state2.old ++ state2.h1 ++ heap_expand state2.n ++ state2.r1,be,
         state2.a,state2.n,0,reset_gens conf state2.a) limit ts /\ state2.ok
Proof
  simp_tac std_ss [abs_ml_inv_def,GSYM CONJ_ASSOC,make_gc_conf_def]
  \\ rpt strip_tac \\ qmatch_goalsub_abbrev_tac `partial_gc cc`
  \\ `heap_ok heap cc.limit` by
        (fs [Abbr `cc`] \\ Cases_on `gens` \\ fs [make_partial_conf_def])
  \\ drule (GEN_ALL gen_gc_partialTheory.partial_gc_related
            |> SIMP_RULE std_ss [Once CONJ_COMM, GSYM CONJ_ASSOC])
  \\ `heap_gen_ok heap cc` by
   (fs [gen_gc_partialTheory.heap_gen_ok_def]
    \\ Cases_on `gens` \\ unabbrev_all_tac \\ fs [make_partial_conf_def]
    \\ fs [gc_kind_inv_def,gen_state_ok_def,has_gen_def]
    \\ Cases_on `l` \\ fs []
    \\ fs [gen_start_ok_def]
    \\ fs [heap_segment_def]
    \\ drule heap_split_LESS_EQ \\ strip_tac
    \\ `limit = heap_length heap` by fs [heap_ok_def]
    \\ drule (GEN_ALL heap_split_heap_split)
    \\ qpat_x_assum `heap_split h heap = _` assume_tac
    \\ disch_then drule \\ fs [] \\ strip_tac \\ fs [] \\ rveq
    \\ rpt strip_tac
    \\ fs [unused_space_inv_def]
    THEN1
     (fs [data_up_to_def]
      \\ qpat_x_assum `heap_split a _ = _` assume_tac
      \\ drule heap_split_heap_split
      \\ qpat_x_assum `heap_split h _ = _` assume_tac
      \\ disch_then drule \\ fs []
      \\ strip_tac \\ fs [])
    THEN1
     (fs [EVERY_MEM] \\ rw [] \\ res_tac
      \\ Cases_on `e` \\ fs [isRef_def,isDataElement_def])
    THEN1
     (first_x_assum match_mp_tac
      \\ asm_exists_tac \\ fs []
      \\ asm_exists_tac \\ fs [])
    \\ Cases_on `d` \\ fs [] \\ rveq
    \\ fs [EVERY_MEM] \\ res_tac \\ fs [isRef_def] \\ NO_TAC)
  \\ fs []
  \\ disch_then drule \\ strip_tac \\ fs []
  \\ `cc.limit = limit` by
       (unabbrev_all_tac \\ EVAL_TAC \\ Cases_on `gens` \\ EVAL_TAC \\ NO_TAC)
  \\ fs []
  \\ `state'.a = heap_length (state'.old ++ state'.h1)` by
   (drule gen_gc_partialTheory.partial_gc_IMP \\ fs []
    \\ fs [heap_length_APPEND] \\ NO_TAC)
  \\ fs []
  \\ reverse (rpt conj_tac) THEN1
   (match_mp_tac (GEN_ALL bc_stack_ref_inv_related) \\ full_simp_tac std_ss []
    \\ qexists_tac `heap` \\ full_simp_tac std_ss []
    \\ rw [] \\ fs [] \\ res_tac \\ fs [])
  THEN1
   (qpat_abbrev_tac `hh = state'.old ++ state'.h1`
    \\ fs [unused_space_inv_def] \\ fs [heap_expand_def]
    \\ rewrite_tac [APPEND,GSYM APPEND_ASSOC]
    \\ fs [heap_lookup_APPEND] \\ fs [heap_lookup_def]
    \\ unabbrev_all_tac \\ fs []
    \\ conj_tac
    THEN1 (fs [heap_length_APPEND] \\ rw [heap_length_def,el_length_def])
    \\ drule gen_gc_partialTheory.partial_gc_IMP \\ fs []
    \\ strip_tac
    \\ Cases_on `gens`
    \\ fs [make_partial_conf_def]
    \\ fs [gen_gc_partialTheory.heap_gen_ok_def]
    \\ fs [heap_segment_def])
  THEN1
    (fs [gc_kind_inv_def] \\ conj_tac THEN1
     (fs [reset_gens_def,gen_state_ok_def,EVERY_MAP]
      \\ qabbrev_tac `hh = state'.old ++ state'.h1`
      \\ fs [gen_start_ok_def]
      \\ simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ simp_tac std_ss [Once heap_split_APPEND_if]
      \\ fs [heap_split_0] \\ disj2_tac
      \\ rpt strip_tac \\ fs [heap_ok_def]
      \\ res_tac
      \\ rpt (qpat_x_assum `!x._` kall_tac)
      \\ CCONTR_TAC \\ fs [NOT_LESS,isSomeDataElement_def]
      \\ qpat_x_assum `heap_lookup _ _ = _` mp_tac
      \\ fs [heap_lookup_APPEND,heap_length_APPEND,heap_length_heap_expand]
      \\ fs [heap_expand_def,heap_lookup_def])
    \\ rename1 `s1.ok`
    \\ qabbrev_tac `hh = (s1.old ++ s1.h1 ++ heap_expand s1.n)`
    \\ `s1.n + heap_length (s1.old ++ s1.h1) = heap_length hh` by
      (unabbrev_all_tac \\ fs [heap_length_APPEND,heap_length_heap_expand])
    \\ fs [] \\ fs [heap_split_APPEND_if,heap_split_0]
    \\ unabbrev_all_tac \\ fs []
    \\ drule gen_gc_partialTheory.partial_gc_IMP \\ fs []
    \\ strip_tac
    \\ Cases_on `gens`
    \\ fs [make_partial_conf_def]
    \\ fs [gen_gc_partialTheory.heap_gen_ok_def]
    \\ fs [heap_segment_def]
    \\ every_case_tac \\ fs []
    \\ rveq \\ fs [heap_length_APPEND] \\ rfs []
    \\ qpat_x_assum `heap_split (a + (sp + sp1)) heap = _` assume_tac
    \\ drule heap_split_heap_split
    \\ pop_assum kall_tac
    \\ disch_then drule \\ fs []
    \\ strip_tac \\ rveq \\ fs [isRef_heap_expand]
    \\ rpt strip_tac THEN1
     (fs [EVERY_MEM] \\ CCONTR_TAC \\ fs []
      \\ Cases_on `x` \\ fs [isRef_def]
      \\ Cases_on `b` \\ fs [isRef_def] \\ rveq
      \\ res_tac \\ fs [] \\ res_tac \\ fs [])
    \\ fs [EVERY_MEM] \\ CCONTR_TAC \\ fs []
    \\ qpat_x_assum `MEM e _` (assume_tac o REWRITE_RULE [MEM_SPLIT])
    \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ fs[LIST_REL_SPLIT2]
    \\ rveq \\ fs[]
    \\ `isRef x` by metis_tac []
    \\ Cases_on `x` \\ fs [isRef_def]
    \\ Cases_on `b` \\ fs [isRef_def]
    \\ Cases_on `e` \\ rveq
    \\ fs [gen_gc_partialTheory.similar_data_def,isRef_def]
    \\ rveq \\ fs[isRef_def])
  \\ fs [roots_ok_def]
  \\ rpt strip_tac
  \\ imp_res_tac MEM_ADDR_MAP
  \\ rveq \\ fs []
  \\ res_tac
  \\ qmatch_goalsub_abbrev_tac `heap_lookup _ heap2`
  \\ fs [gc_related_def,isSomeDataElement_def]
  \\ res_tac \\ fs []
QED

Definition data_pointers_def:
  (data_pointers [] = []) /\
  (data_pointers ((DataElement x y z) :: rest) =
     0 :: MAP (\n. n + el_length (DataElement x y z)) (data_pointers rest)) /\
  (data_pointers (x :: rest) =
     MAP (\n. n + el_length x) (data_pointers rest))
End

Definition lookup_len_def:
  lookup_len heap p =
    case heap_lookup p heap of NONE => 0 | SOME x => el_length x
End

Definition data_length_def:
  data_length heap =
    SUM (MAP (lookup_len heap) (data_pointers heap))
End

Theorem data_pointers_heap_expand:
  data_pointers (heap ++ heap_expand n) = data_pointers heap
Proof
  Induct_on `heap` \\ fs [data_pointers_def]
  \\ rw [heap_expand_def,data_pointers_def]
  \\ Cases_on `h`
  \\ rw [heap_expand_def,data_pointers_def]
  \\ fs [MAP_MAP_o,o_DEF,lookup_len_def,heap_lookup_def,el_length_def]
  \\ fs [heap_expand_def,data_pointers_def]
QED

Theorem data_length_APPEND_heap_expand:
  data_length (heap ++ heap_expand n) = data_length heap
Proof
  fs [data_length_def,data_pointers_heap_expand]
  \\ Induct_on `heap` \\ fs [data_length_def,data_pointers_def]
  \\ rw [heap_expand_def,data_pointers_def]
  \\ Cases_on `h` \\ fs [data_pointers_def,el_length_def]
  \\ fs [MAP_MAP_o,o_DEF,lookup_len_def,heap_lookup_def,el_length_def]
  \\ qmatch_goalsub_abbrev_tac `SUM (MAP f1 _) = SUM (MAP f2 _)`
  \\ qmatch_asmsub_abbrev_tac `SUM (MAP g1 _) = SUM (MAP g2 _)`
  \\ qsuff_tac `f1 = g1 /\ f2 = g2` \\ fs []
  \\ unabbrev_all_tac
  \\ fs [FUN_EQ_THM,lookup_len_def,heap_expand_def]
QED

Theorem data_length_heap_length:
  EVERY isDataElement heap ==>
  data_length heap = heap_length heap
Proof
  Induct_on `heap` \\ fs [data_length_def,data_pointers_def]
  \\ Cases \\ fs [data_length_def,data_pointers_def,isDataElement_def,el_length_def]
  \\ fs [lookup_len_def,heap_lookup_def,el_length_def,heap_length_def]
  \\ rw [] \\ fs [] \\ fs [MAP_MAP_o]
  \\ fs [lookup_len_def,o_DEF,heap_lookup_def,el_length_def]
  \\ last_x_assum (fn th => simp [GSYM th])
  \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ fs [FUN_EQ_THM] \\ fs [lookup_len_def]
QED

Theorem data_length_CONS:
  !x xs. data_length (x::xs) = data_length [x] + data_length xs
Proof
  Cases \\ fs [data_length_def,data_pointers_def,el_length_def]
  \\ fs [lookup_len_def,heap_lookup_def] \\ fs [MAP_MAP_o,o_DEF]
  \\ fs [lookup_len_def,heap_lookup_def,el_length_def]
  \\ rw [] \\ AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ fs [FUN_EQ_THM] \\ fs [lookup_len_def]
QED

Theorem data_length_APPEND:
  !xs ys. data_length (xs ++ ys) = data_length xs + data_length ys
Proof
  Induct
  THEN1 fs [data_length_def,data_pointers_def]
  \\ simp [] \\ once_rewrite_tac [data_length_CONS] \\ fs []
QED

Theorem data_length_heap_expand:
  data_length (heap_expand n) = 0
Proof
  rw [heap_expand_def] \\ EVAL_TAC
QED

Theorem gc_combined_thm:
   abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
   (do_partial ==> has_gen gens) ==>
    ?roots2 heap2 gens2 n2 a2.
      (gc_combined (make_gc_conf limit) conf.gc_kind
            (roots,heap,gens,a+sp+sp1,do_partial) =
         (roots2,heap2,a2,n2,gens2,T)) /\
      abs_ml_inv conf stack refs (roots2,heap2,be,a2,n2,0,gens2) limit ts /\
      (conf.gc_kind <> None /\ (conf.gc_kind <> Simple ==> ~do_partial) ==>
       all_reachable_from_roots roots2 heap2 /\
       heap_length heap2 = data_length heap2 + n2)
Proof
  Cases_on `conf.gc_kind` \\ fs [gc_combined_def]
  THEN1
   (fs [make_gc_conf_def] \\ fs [abs_ml_inv_def]
    \\ fs [unused_space_inv_def,gc_kind_inv_def]
    \\ fs [data_up_to_def,heap_split_0])
  THEN1
   (pairarg_tac \\ fs [] \\ strip_tac
    \\ drule (GEN_ALL full_gc_thm) \\ fs [make_gc_conf_def]
    \\ strip_tac \\ rveq \\ fs []
    \\ fs [heap_length_APPEND,heap_length_heap_expand,
           data_length_APPEND_heap_expand,data_length_heap_length])
  \\ IF_CASES_TAC THEN1
   (pairarg_tac \\ fs [] \\ strip_tac \\ rveq
    \\ drule (GEN_ALL gen_gc_partial_thm) \\ fs [reset_gens_def])
  \\ fs [] \\ pairarg_tac \\ fs [] \\ strip_tac
  \\ drule (GEN_ALL gen_gc_thm) \\ fs [reset_gens_def]
  \\ strip_tac
  \\ fs [data_length_APPEND,data_length_heap_length]
  \\ rewrite_tac [heap_length_APPEND,heap_length_heap_expand,
       data_length_heap_expand]
  \\ simp_tac std_ss [AC ADD_COMM ADD_ASSOC]
QED

(* Write to unused heap space is fine, e.g. cons *)

Definition heap_store_def:
  (heap_store a y [] = ([],F)) /\
  (heap_store a y (x::xs) =
    if a = 0 then (y ++ xs, el_length x = heap_length y) else
    if a < el_length x then (x::xs,F) else
      let (xs,c) = heap_store (a - el_length x) y xs in
        (x::xs,c))
End

Definition isUnused_def:
  isUnused x = ?k. x = Unused k
End

Definition isSomeUnused_def:
  isSomeUnused x = ?k. x = SOME (Unused k)
End

Definition heap_store_unused_def:
  heap_store_unused a sp x xs =
    if (heap_lookup a xs = SOME (Unused (sp-1))) /\ el_length x <= sp then
      heap_store a (heap_expand (sp - el_length x) ++ [x]) xs
    else (xs,F)
End

Definition heap_store_unused_alt_def:
  heap_store_unused_alt a sp x xs =
    if (heap_lookup a xs = SOME (Unused (sp-1))) /\ el_length x <= sp then
      heap_store a ([x] ++ heap_expand (sp - el_length x)) xs
    else (xs,F)
End

Theorem heap_store_lemma:
   !xs y x ys.
      heap_store (heap_length xs) y (xs ++ x::ys) =
      (xs ++ y ++ ys, heap_length y = el_length x)
Proof
  Induct \\ full_simp_tac (srw_ss()) [heap_length_def,heap_store_def,LET_DEF]
  THEN1 DECIDE_TAC \\ rpt strip_tac
  \\ `el_length h <> 0` by (Cases_on `h` \\ full_simp_tac std_ss [el_length_def])
  \\ `~(el_length h + SUM (MAP el_length xs) < el_length h)` by DECIDE_TAC
  \\ full_simp_tac std_ss []
QED

Definition heap_store_rel_def:
  heap_store_rel heap heap2 <=>
    (!ptr. isSomeDataElement (heap_lookup ptr heap) ==>
           (heap_lookup ptr heap2 = heap_lookup ptr heap))
End

Triviality isSomeDataElement_heap_lookup_lemma1:
  isSomeDataElement (heap_lookup n (Unused k :: xs)) <=>
    k < n /\ isSomeDataElement (heap_lookup (n-(k+1)) xs)
Proof
  srw_tac [] [heap_lookup_def,isSomeDataElement_def,el_length_def,NOT_LESS]
  THEN1 (DISJ1_TAC \\ DECIDE_TAC)
  \\ `k < n` by DECIDE_TAC \\ full_simp_tac std_ss []
QED

Triviality isSomeDataElement_heap_lookup_lemma2:
  isSomeDataElement (heap_lookup n (heap_expand k ++ xs)) <=>
    k <= n /\ isSomeDataElement (heap_lookup (n-k) xs)
Proof
  srw_tac [] [heap_expand_def,isSomeDataElement_heap_lookup_lemma1]
  \\ imp_res_tac (DECIDE ``sp <> 0 ==> (sp - 1 + 1 = sp:num)``)
  \\ full_simp_tac std_ss []
  \\ Cases_on `isSomeDataElement (heap_lookup (n - k) xs)`
  \\ full_simp_tac std_ss [] \\ DECIDE_TAC
QED

Triviality isSomeDataElement_heap_lookup_lemma3:
  n <> 0 ==>
    (isSomeDataElement (heap_lookup n (x::xs)) <=>
     el_length x <= n /\ isSomeDataElement (heap_lookup (n - el_length x) xs))
Proof
  srw_tac [] [heap_expand_def,heap_lookup_def,isSomeDataElement_def]
  \\ Cases_on`n < el_length x` THEN srw_tac[][]
  THEN1 (DISJ1_TAC \\ DECIDE_TAC)
  \\ `el_length x <= n` by DECIDE_TAC \\ full_simp_tac std_ss []
QED

Theorem IMP_heap_store_unused[local]:
  unused_space_inv a sp (heap:('a,'b) heap_element list) /\
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
            heap_store_rel heap heap2
Proof
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
   (fs [heap_length_APPEND,el_length_def,heap_length_heap_expand])
  \\ strip_tac THEN1
   (full_simp_tac std_ss [GSYM APPEND_ASSOC,data_up_to_APPEND])
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
    \\ reverse (full_simp_tac std_ss [])
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
  \\ POP_ASSUM (K ALL_TAC) \\ qpat_x_assum `xxx = SOME yyy` MP_TAC
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
  \\ full_simp_tac std_ss [] \\ fs[]
QED

Triviality IMP_heap_store_unused_alt:
  unused_space_inv a sp (heap:('a,'b) heap_element list) /\
    el_length x <= sp ==>
    ?heap2. (heap_store_unused_alt a sp x heap = (heap2,T)) /\
            (isDataElement x ==>
               unused_space_inv (a + el_length x) (sp - el_length x) heap2) /\
            (heap_lookup a heap2 = SOME x) /\
            ~isSomeDataElement (heap_lookup a heap) /\
            (heap_length heap2 = heap_length heap) /\
            (~isForwardPointer x ==>
             (FILTER isForwardPointer heap2 = FILTER isForwardPointer heap)) /\
            (!xs l d.
               MEM (DataElement xs l d) heap2 <=>
                 (x = DataElement xs l d) \/
                 MEM (DataElement xs l d) heap) /\
            (isDataElement x ==>
             ({a | isSomeDataElement (heap_lookup a heap2)} =
               a INSERT {a | isSomeDataElement (heap_lookup a heap)})) /\
            heap_store_rel heap heap2
Proof
  rpt strip_tac \\ asm_simp_tac std_ss [heap_store_unused_alt_def,heap_store_rel_def]
  \\ `sp <> 0` by (Cases_on `x` \\ full_simp_tac std_ss [el_length_def] \\ DECIDE_TAC)
  \\ full_simp_tac std_ss [unused_space_inv_def]
  \\ imp_res_tac heap_lookup_SPLIT \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [heap_store_lemma]
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [heap_length_def,SUM_APPEND,el_length_def]
    \\ full_simp_tac std_ss [GSYM heap_length_def,heap_length_heap_expand]
    \\ DECIDE_TAC)
  \\ strip_tac THEN1
   (rpt strip_tac
    \\ full_simp_tac std_ss [APPEND_ASSOC,heap_expand_def]
    \\ `ha ++ [x] ++ [Unused (sp − el_length x − 1)] ++ hb =
        ha ++ [x] ++ Unused (sp − el_length x − 1)::hb` by
          fs [APPEND] \\ pop_assum (fn th => fs [th])
    \\ `el_length x + heap_length ha = heap_length (ha ++ [x])` by
          (fs [heap_length_def,SUM_APPEND] \\ NO_TAC)
    \\ pop_assum (fn th => fs [th]) \\ fs [heap_lookup_PREFIX]
    \\ qabbrev_tac `hh = ha ++ [x]`
    \\ full_simp_tac std_ss [data_up_to_APPEND,GSYM APPEND_ASSOC]
    \\ unabbrev_all_tac \\ fs []
    \\ fs [heap_length_APPEND,el_length_def,heap_length_heap_expand]
    \\ fs [heap_length_def,el_length_def] \\ rw [el_length_def])
  \\ strip_tac THEN1
   (full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ full_simp_tac std_ss [APPEND_ASSOC]
    \\ `heap_length ha + sp - el_length x =
        heap_length (ha ++ heap_expand (sp - el_length x))` by
     (full_simp_tac std_ss [heap_length_APPEND,heap_length_heap_expand] \\ DECIDE_TAC)
    \\ full_simp_tac std_ss [heap_lookup_PREFIX])
  \\ strip_tac THEN1 (fs [isSomeDataElement_def])
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
    \\ Cases_on `y = heap_length ha`
    \\ full_simp_tac std_ss [] THEN1
     (full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND,heap_lookup_PREFIX]
      \\ full_simp_tac (srw_ss()) [isDataElement_def,isSomeDataElement_def])
    \\ Cases_on `y < heap_length ha`
    THEN1 (full_simp_tac std_ss [LESS_IMP_heap_lookup,GSYM APPEND_ASSOC])
    \\ imp_res_tac NOT_LESS_IMP_heap_lookup
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ full_simp_tac std_ss [isSomeDataElement_heap_lookup_lemma1,
         isSomeDataElement_heap_lookup_lemma2]
    \\ `0 < el_length x` by
         (Cases_on `x` \\ full_simp_tac std_ss [el_length_def] \\ DECIDE_TAC)
    \\ fs [heap_lookup_def,APPEND,heap_expand_def]
    \\ IF_CASES_TAC \\ fs []
    THEN1 fs [isSomeDataElement_def]
    \\ Cases_on `sp = el_length x` \\ fs []
    \\ fs [heap_lookup_def,el_length_def]
    \\ rw [] \\ fs [isSomeDataElement_def])
  \\ rpt strip_tac
  \\ full_simp_tac std_ss [isSomeDataElement_def]
  \\ Cases_on `ptr < heap_length ha`
  THEN1 (imp_res_tac LESS_IMP_heap_lookup \\ full_simp_tac std_ss [GSYM APPEND_ASSOC])
  \\ `0 < el_length x` by (Cases_on `x` \\ EVAL_TAC \\ fs [])
  \\ imp_res_tac NOT_LESS_IMP_heap_lookup \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ POP_ASSUM (K ALL_TAC) \\ qpat_x_assum `xxx = SOME yyy` MP_TAC
  \\ simp_tac std_ss [Once heap_lookup_def] \\ srw_tac [] []
  \\ fs [el_length_def]
  \\ fs [heap_expand_def] \\ rw []
  \\ fs [heap_lookup_def] \\ rw []
  \\ fs [el_length_def]
  \\ imp_res_tac LESS_EQUAL_ANTISYM \\ fs []
  \\ rveq \\ fs []
  \\ rfs [GSYM SUB_PLUS]
QED

Triviality heap_store_rel_lemma:
  heap_store_rel h1 h2 /\ (heap_lookup n h1 = SOME (DataElement ys l d)) ==>
    (heap_lookup n h2 = SOME (DataElement ys l d))
Proof
  simp_tac std_ss [heap_store_rel_def,isSomeDataElement_def] \\ metis_tac []
QED

(* cons *)

Triviality v_inv_SUBMAP:
  !w x.
      f SUBMAP f1 /\ tf SUBMAP tf1 /\
      heap_store_rel heap heap1 /\
      v_inv conf w (x,f,tf,heap) ==>
      v_inv conf w (x,f1,tf1,heap1)
Proof
  completeInduct_on `v_size w` \\ NTAC 3 strip_tac
  \\ full_simp_tac std_ss [PULL_FORALL] \\ Cases_on `w` THEN1
   (full_simp_tac std_ss [v_inv_def,Bignum_def] \\ srw_tac [] []
    \\ imp_res_tac heap_store_rel_lemma \\ fs [])
  THEN1 (
    rw[] \\ fs[v_inv_def]
    \\ qspecl_then[`:'a`,`c`]strip_assume_tac Word64Rep_DataElement
    \\ fs[]
    \\ imp_res_tac heap_store_rel_lemma )
  THEN1 (full_simp_tac (srw_ss()) [v_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ Cases_on `l = []` \\ full_simp_tac std_ss []
    \\ full_simp_tac (srw_ss()) [v_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ rpt strip_tac
    \\ full_simp_tac std_ss [EVERY2_EVERY,LENGTH_ADDR_MAP,EVERY_MEM,FORALL_PROD]
    \\ qpat_x_assum `LENGTH l = LENGTH xs` ASSUME_TAC
    \\ full_simp_tac (srw_ss()) [MEM_ZIP,LENGTH_ADDR_MAP,PULL_EXISTS]
    \\ imp_res_tac heap_store_rel_lemma \\ full_simp_tac (srw_ss()) []
    \\ full_simp_tac (srw_ss()) [MEM_ZIP,LENGTH_ADDR_MAP,PULL_EXISTS]
    \\ reverse (rpt strip_tac)
    THEN1 (drule_then (drule_then (fn t => fs [t])) FLOOKUP_SUBMAP)
    \\ Q.MATCH_ASSUM_RENAME_TAC `t < LENGTH xs` \\ res_tac
    \\ `MEM (EL t l) l` by (full_simp_tac std_ss [MEM_EL] \\ metis_tac [])
    \\ last_x_assum irule
    \\ imp_res_tac MEM_IMP_v_size
    \\ gvs [])
  THEN1 (full_simp_tac std_ss [v_inv_def] \\ metis_tac [])
  THEN1 (full_simp_tac (srw_ss()) [v_inv_def,SUBMAP_DEF] \\ rw [])
QED

Theorem heap_store_rel_v_inv:
  !w x.
      heap_store_rel heap heap1 /\
      v_inv conf w (x,f,tf,heap) ==>
      v_inv conf w (x,f,tf,heap1)
Proof
  rw [] \\ ho_match_mp_tac v_inv_SUBMAP \\ rw []
QED

val heap_store_unused_alt_thm = prove(
  ``!a n heap h1 h2 heap2 x.
      heap_split (a + n) heap = SOME (h1,h2) /\
      heap_store_unused_alt a n x heap = (heap2,T) /\
      unused_space_inv (a + el_length x) (n − el_length x) heap2 ==>
      ?h0. h1 = h0 ++ [Unused (n-1)] /\
           heap = h1 ++ h2 /\ heap_length h0 = a /\
           heap2 = h0 ++ [x] ++ heap_expand (n − el_length x) ++ h2``,
  fs [heap_store_unused_alt_def] \\ rw []
  \\ fs [unused_space_inv_def]
  \\ imp_res_tac gc_sharedTheory.heap_split_heap_length
  \\ fs [] \\ rveq \\ fs []
  \\ fs [heap_lookup_APPEND]
  \\ `0 < n` by (Cases_on `x` \\ fs [el_length_def])
  \\ fs [] \\ drule heap_lookup_SPLIT
  \\ strip_tac \\ rveq \\ fs []
  \\ `hb = []` by
   (fs [heap_length_APPEND]
    \\ fs [heap_length_def,el_length_def]
    \\ Cases_on `hb` \\ fs [])
  \\ rveq \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [heap_store_lemma]);

Theorem heap_store_unused_alt_heap_lookup:
   !heap heap2 a k x n.
      heap_store_unused_alt a k x heap = (heap2,T) /\ n < a ==>
      heap_lookup n heap = heap_lookup n heap2
Proof
  Induct THEN1 fs [heap_lookup_def,heap_store_unused_alt_def]
  \\ simp [heap_store_unused_alt_def]
  \\ rpt strip_tac \\ every_case_tac \\ fs []
  \\ ntac 4 (pop_assum mp_tac)
  \\ once_rewrite_tac [heap_store_def]
  \\ IF_CASES_TAC \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ rveq
  \\ once_rewrite_tac [heap_lookup_def] \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ rpt strip_tac
  \\ first_x_assum match_mp_tac
  \\ fs [heap_store_unused_alt_def]
  \\ qexists_tac `(a − el_length h)` \\ fs [] \\ metis_tac []
QED

val heap_split_heap_store = prove(
  ``!heap e h1 h2 a y heap2.
      heap_split e heap = SOME (h1,h2) /\
      heap_store a y heap = (heap2,T) /\ e <= a ==>
      ?h3. heap_split e heap2 = SOME (h1,h3)``,
  Induct \\ fs [heap_split_def,heap_store_def]
  \\ rpt gen_tac
  \\ IF_CASES_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ TOP_CASE_TAC \\ fs []
  \\ strip_tac \\ rveq
  \\ Cases_on `a=0` \\ fs []
  \\ Cases_on `a < el_length h` \\ fs []
  \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
  \\ res_tac \\ rfs []
  \\ fs [heap_split_def]);

val heap_store_unused_alt_gen_state_ok = prove(
  ``heap_store_unused_alt a k x heap = (heap2,T) /\
    gen_state_ok a (a + k) heap gens ==>
    gen_state_ok (a + el_length x) (a + k) heap2 gens``,
  Cases_on `gens` \\ fs [gen_state_ok_def]
  \\ fs [EVERY_MEM] \\ rw [] \\ res_tac \\ fs []
  \\ fs [gen_start_ok_def]
  \\ rw [] \\ CCONTR_TAC \\ fs []
  \\ fs [GSYM NOT_LESS] \\ fs [NOT_LESS]
  \\ fs [heap_store_unused_alt_def]
  \\ every_case_tac \\ fs []
  \\ fs [GSYM IMP_DISJ_THM]
  \\ imp_res_tac heap_split_heap_store \\ fs []
  \\ rveq \\ fs [] \\ res_tac \\ fs []);

Theorem isDataElement_lemmas[simp]:
   isDataElement (DataElement x1 x2 x3) /\
    isDataElement (BlockRep tag ys1) /\
    isDataElement (Word64Rep (:'a) w) /\
    isDataElement (RefBlock ws) /\
    isDataElement (Bytes y1 y2 y3 y4) /\
    isDataElement (Bignum i)
Proof
  rw [BlockRep_def,isDataElement_def,Bignum_def,i2mw_def,
    Word64Rep_def,RefBlock_def,Bytes_def]
QED

(* --- Allocating multiple cons-elements in one go --- *)

Definition list_to_BlockReps_def:
  list_to_BlockReps conf t a []     = ARB /\
  list_to_BlockReps conf t a (h::l) =
    case l of
      [] => [BlockRep cons_tag [h;t]]
    | _ =>
        BlockRep cons_tag
          [h; Pointer (a + 3) (Word (ptr_bits conf cons_tag 2))] ::
            list_to_BlockReps conf t (a + 3) l
End

Theorem list_to_BlockReps_heap_length:
   !xs len.
     xs <> []
     ==>
     heap_length (list_to_BlockReps conf x len xs) =
      3 * LENGTH xs
Proof
  Induct \\ fs []
  \\ rw [list_to_BlockReps_def, el_length_def, BlockRep_def]
  \\ Cases_on `xs` \\ fs [heap_length_def, el_length_def]
QED

Theorem heap_lookup_heap_length:
   heap_lookup (heap_length h1) (h1 ++ h2) = heap_lookup 0 h2
Proof
  rw [heap_length_def, heap_lookup_def, heap_lookup_APPEND]
QED

Theorem list_to_BlockReps_heap_lookup_0:
   xs <> []
   ==>
   isSomeDataElement (heap_lookup 0 (list_to_BlockReps conf x len xs))
Proof
  Cases_on `xs` \\ rw [list_to_BlockReps_def, BlockRep_def, isSomeDataElement_def]
  \\ CASE_TAC \\ fs [heap_lookup_def]
QED

Theorem list_to_BlockReps_isDataElement:
   !xs x len.
     xs <> []
     ==>
     EVERY isDataElement (list_to_BlockReps conf x len xs)
Proof
  Induct \\ rw [list_to_BlockReps_def] \\ CASE_TAC \\ fs []
QED

Triviality list_to_BlockReps_data_up_to_lem:
  xs <> [] /\
   h1 = list_to_BlockReps conf x len xs ==>
   data_up_to (heap_length h1) (h1 ++ h2)
Proof
  rw [data_up_to_def, list_to_BlockReps_isDataElement]
QED

Theorem list_to_BlockReps_data_up_to =
  list_to_BlockReps_data_up_to_lem
  |> Q.INST [`h1`|->`list_to_BlockReps conf x len xs`]
  |> SIMP_RULE std_ss []

Theorem list_to_BlockReps_ForwardPointer:
   xs <> [] ==> FILTER isForwardPointer (list_to_BlockReps conf x len xs) = []
Proof
  rw [FILTER_EQ_NIL, EVERY_MEM] \\ CCONTR_TAC \\ fs []
  \\ imp_res_tac (list_to_BlockReps_isDataElement
                 |> SIMP_RULE (srw_ss()) [EVERY_MEM])
  \\ Cases_on `x'` \\ fs [isForwardPointer_def, isDataElement_def]
QED

Theorem list_to_BlockReps_Ref:
   !xs len x conf.
     xs <> [] ==> EVERY (\v. ~isRef v) (list_to_BlockReps conf x len xs)
Proof
  Induct \\ rw [list_to_BlockReps_def, BlockRep_def]
  \\ TRY CASE_TAC \\ fs [isRef_def]
QED

Theorem list_to_BlockReps_NULL:
   xs <> [] ==> list_to_BlockReps conf x len xs <> []
Proof
  Cases_on `xs` \\ fs [list_to_BlockReps_def] \\ CASE_TAC \\ fs []
QED

fun unlength_tac thms =
  fs ([heap_length_def, el_length_def, SUM_APPEND] @ thms)
  \\ fs [GSYM heap_length_def]

Theorem list_to_BlockReps_MEM:
   MEM v (list_to_BlockReps conf x len (h::t)) ==>
     MEM v (list_to_BlockReps conf x (len + 3) t) \/
     v = BlockRep cons_tag
           [h; Pointer (len + 3) (Word (ptr_bits conf cons_tag 2))] \/
     v = BlockRep cons_tag [h; x]
Proof
  rw [list_to_BlockReps_def, BlockRep_def] \\ fs []
  \\ Cases_on `t` \\ fs [list_to_BlockReps_def]
QED

Triviality list_to_BlockReps_Pointer_lem:
  !xs len ys l d ptr u.
     let allocd = list_to_BlockReps conf x len xs in
       xs <> [] /\
       MEM (DataElement ys l d) allocd /\
       MEM (Pointer ptr u) ys ==>
         Pointer ptr u = x \/
         MEM (Pointer ptr u) xs \/
         (ptr < len + heap_length allocd /\
          ptr > len /\
          isSomeDataElement
            (heap_lookup (ptr - len) allocd))
Proof
  fs [LET_THM]
  \\ Induct \\ rw []
  \\ imp_res_tac list_to_BlockReps_MEM
  \\ Cases_on `xs`
  >-
   (fs [list_to_BlockReps_def, BlockRep_def, heap_length_def, el_length_def]
    \\ fs [heap_lookup_def, el_length_def]
    \\ rw [] \\ fs [isSomeDataElement_def])
  \\ fs []
  \\ TRY
   (first_x_assum drule
    \\ disch_then drule)
  \\ fs [list_to_BlockReps_def, BlockRep_def, heap_length_def, el_length_def]
  \\ CASE_TAC \\ fs [el_length_def, heap_lookup_def]
  \\ rw [isSomeDataElement_def]
  \\ fs [list_to_BlockReps_def, BlockRep_def]
  \\ CASE_TAC \\ fs [el_length_def, isSomeDataElement_def, heap_lookup_def]
QED

Theorem list_to_BlockReps_Pointer =
  list_to_BlockReps_Pointer_lem
  |> SIMP_RULE (srw_ss()) [LET_THM]

Theorem list_to_v_get_refs:
   !xs t r ts.
     MEM r (get_refs (list_to_v ts t xs)) ==>

       ?x. (MEM x xs \/ x = t) /\ MEM r (get_refs x)
Proof
  Induct \\ rw [dataSemTheory.list_to_v_def]
  \\ fs [get_refs_def] \\ metis_tac []
QED

Theorem v_inv_lemma:
  !v x f tf hs ha hb sp.
   0 < heap_length hs /\
   heap_length hs <= sp /\
   v_inv conf v (x,f,tf,ha++heap_expand sp++hb) ==>
   v_inv conf v (x,f,tf,ha++hs++heap_expand (sp - heap_length hs)++hb)
Proof
  recInduct (theorem"v_inv_ind") \\ rw [v_inv_def]
  \\ unlength_tac [heap_lookup_APPEND, heap_length_APPEND, heap_expand_def]
  \\ fs [case_eq_thms]
  \\ namedCases_on `sp` ["", "sp'"] \\ fs []
  \\ fs [heap_lookup_def, Bignum_def, Word64Rep_def, BlockRep_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ unlength_tac [ADD1]
  \\ IF_CASES_TAC \\ fs []
  \\ TRY (qexists_tac `xs`)
  \\ fs [LIST_REL_EL_EQN] \\ rw []
  \\ TRY
   (rename1 `EL m vs`
    \\ first_x_assum (qspecl_then [`EL m vs`,`EL m xs`,`xs`] mp_tac)
    \\ simp [EL_MEM]
    \\ rpt (disch_then drule \\ fs []))
  \\ unlength_tac []
  \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC) \\ fs []
  \\ imp_res_tac heap_lookup_SPLIT
  \\ gvs[]
  \\ unlength_tac [heap_lookup_APPEND, heap_length_APPEND, heap_lookup_def]
QED

Theorem v_inv_LIST_REL:
   !l1 l2.
     0 < heap_length hs /\
     heap_length hs <= sp /\
     LIST_REL (\z y. v_inv conf y
       (z, f, tf, ha ++ heap_expand sp ++ hb)) l1 l2
     ==>
     LIST_REL (\z y. v_inv conf y
       (z, f, tf, ha ++ hs ++ heap_expand (sp - heap_length hs) ++ hb)) l1 l2
Proof
  rw [LIST_REL_EL_EQN]
  \\ metis_tac [v_inv_lemma]
QED

Definition bind_each_def:
  bind_each tf ts (k:num) i 0 = tf /\
  bind_each tf ts (k:num) i (SUC n) = bind_each tf (ts+1n) (k+i) i n |+ (ts,k)
End

Theorem bind_each_MONO:
  ∀n t1 t2 tf k i. t1 < t2 ∧ (∀t. t ∈ FDOM tf ⇒ t < t1)
   ⇒ t1 ∉ FDOM (bind_each tf t2 k i n)
Proof
 Induct
 \\ rw [bind_each_def]
 \\ CCONTR_TAC \\ fs []
 \\ first_x_assum drule
 \\ rw []
QED

Theorem bind_each_SUBMAP:
  ∀n tf ts k i.
   (∀t.t ∈ FDOM tf ⇒ t < ts) ⇒ tf ⊑ bind_each tf ts k i n
Proof
  Induct \\ rw [bind_each_def]
  \\ ho_match_mp_tac SUBMAP_TRANS
  \\ qexists_tac `bind_each tf (ts + 1) (k + i) i n`
  \\ conj_tac
  >- (first_x_assum ho_match_mp_tac \\ rw []
     \\ first_x_assum drule \\ rw [])
  \\ rw []
  \\ disj1_tac
  \\ last_x_assum (K ALL_TAC)
  \\ ho_match_mp_tac bind_each_MONO
  \\ rw []
QED

Theorem v_inv_list_to_v_lem:
  !rs xs t rt ha hb sp ts.
    let hm = list_to_BlockReps conf rt (heap_length ha) rs in
      rs <> [] /\
      v_inv conf t (rt, f, tf, ha ++ heap_expand sp ++ hb) /\
      LIST_REL (\v x. v_inv conf v (x, f, tf, ha ++ heap_expand sp ++ hb)) xs rs /\
      heap_length hm <= sp /\ (∀t. t ∈ FDOM tf ⇒ t < ts)
      ==>
      v_inv conf (list_to_v ts t xs)
        (Pointer (heap_length ha) (Word (ptr_bits conf cons_tag 2)),
         f, bind_each tf ts (heap_length ha) 3 (LENGTH xs),
         ha ++ hm ++ heap_expand (sp - heap_length hm) ++ hb)
Proof
  gen_tac \\ completeInduct_on `LENGTH rs` \\ rw []
  \\ `ts ∉ FDOM tf`
     by (CCONTR_TAC \\ fs []
        \\ first_x_assum drule \\ rw [])
  \\ Cases_on `rs = []` \\ fs []
  \\ Cases_on `?r. rs = [r]` \\ fs [] \\ rveq
  >-
   (fs [list_to_v_def, list_to_BlockReps_def, v_inv_def]
    \\ unlength_tac [BlockRep_def, heap_length_APPEND, heap_lookup_APPEND,
                     heap_lookup_def, dataSemTheory.list_to_v_def]
    \\ rewrite_tac [EVAL ``bind_each tf ts n 3 1``,FLOOKUP_UPDATE]
    \\ qmatch_goalsub_abbrev_tac `ha ++ hs ++ _`
    \\ `3 = heap_length hs` by unlength_tac [Abbr`hs`]
    \\ pop_assum (fn th => fs [th])
    \\ conj_tac
    \\ match_mp_tac v_inv_lemma
    \\ unlength_tac [heap_expand_def, Abbr`hs`]
    \\ qmatch_goalsub_abbrev_tac `v_inv conf tv _`
    \\ qpat_x_assum `v_inv conf tv _` (mp_then Any ho_match_mp_tac (GEN_ALL v_inv_SUBMAP))
    \\ rw [heap_store_rel_def])
  \\ Cases_on `rs` \\ fs []
  \\ rw [list_to_BlockReps_def] \\ CASE_TAC \\ fs [] \\ rveq
  \\ rename1 `v::w::vs`
  \\ rename1 `list_to_BlockReps _ _ _ (r::rr::rs)`
  \\ first_x_assum (qspec_then `LENGTH (rr::rs)` mp_tac) \\ simp []
  \\ disch_then (qspec_then `rr::rs` mp_tac) \\ fs [] \\ strip_tac
  \\ once_rewrite_tac [dataSemTheory.list_to_v_def]
  \\ first_x_assum (qspecl_then [`w::vs`,`t`,`rt`] mp_tac)
  \\ qmatch_goalsub_abbrev_tac `ha++el::_++_`
  \\ disch_then (qspec_then `ha++[el]` mp_tac) \\ fs []
  \\ disch_then (qspecl_then [`hb`,`sp-3`,`ts+1`] mp_tac) \\ fs []
  \\ impl_tac
  >-
   (`sp - 3 = sp - heap_length [el]` by unlength_tac [Abbr`el`, BlockRep_def]
    \\ pop_assum (fn th => fs [th])
    \\ qunabbrev_tac `el`
    \\ conj_tac
    >-
     (match_mp_tac v_inv_lemma
      \\ unlength_tac [heap_expand_def, BlockRep_def, list_to_BlockReps_def])
    \\ reverse conj_tac
    >-
     (fs [list_to_BlockReps_def, BlockRep_def]
      \\ CASE_TAC \\ unlength_tac []
      \\ rw [] \\ first_x_assum drule \\ rw [])
    \\ reverse conj_tac
    >-
     (unlength_tac [BlockRep_def]
      \\ qmatch_goalsub_abbrev_tac `ha ++ [el] ++ _`
      \\ `sp - 3 = sp - heap_length [el]` by
        unlength_tac [Abbr`el`]
      \\ pop_assum (fn th => fs [th])
      \\ ho_match_mp_tac EVERY2_SWAP
      \\ match_mp_tac v_inv_LIST_REL
      \\ unlength_tac [heap_expand_def, BlockRep_def, Abbr`el`,
                       list_to_BlockReps_def]
      \\ Cases_on `sp` \\ fs []
      \\ imp_res_tac EVERY2_SWAP \\ fs [])
    \\ match_mp_tac v_inv_lemma
    \\ unlength_tac [heap_expand_def, BlockRep_def, list_to_BlockReps_def]
    \\ rfs [])
  \\ strip_tac
  \\ simp [v_inv_def, PULL_EXISTS]
  \\ qexists_tac `r`
  \\ qexists_tac `Pointer (heap_length ha + 3) (Word (ptr_bits conf cons_tag 2))`
  \\ conj_tac
  >-
   (match_mp_tac v_inv_lemma
    \\ unlength_tac [Abbr`el`, BlockRep_def, list_to_BlockReps_def]
    \\ qmatch_goalsub_abbrev_tac `v_inv conf tv _`
    \\ qpat_x_assum `v_inv conf tv _` (mp_then Any ho_match_mp_tac (GEN_ALL v_inv_SUBMAP))
    \\ rw [heap_store_rel_def,bind_each_SUBMAP])
  \\ conj_tac
  >-
   (once_rewrite_tac [CONS_APPEND] \\ fs []
    \\ `heap_length ha + 3 = heap_length (ha ++ [el])` by
      unlength_tac [heap_length_APPEND, Abbr`el`, BlockRep_def]
    \\ fs []
    \\ `heap_length [el] = 3` by unlength_tac [Abbr`el`]
    \\ fs [heap_length_APPEND, heap_length_def]
    \\ qmatch_goalsub_abbrev_tac `v_inv _ tv (x,f,_,heap)`
    \\ qmatch_asmsub_abbrev_tac `v_inv _ _ (x,f,tf',heap)`
    \\ qpat_x_assum `v_inv _ tv _` (mp_then Any mp_tac (GEN_ALL v_inv_SUBMAP))
    \\ disch_then (qspecl_then [`tf' |+ (ts,SUM (MAP el_length ha))`,`heap`,`f`] mp_tac)
    \\ rw [Abbr `tf'`, heap_store_rel_def,bind_each_MONO]
    \\ qpat_x_assum `v_inv conf tv _` (mp_then Any ho_match_mp_tac (GEN_ALL v_inv_SUBMAP))
    \\ rw [heap_store_rel_def,bind_each_def])
  \\ conj_tac
  >- (rw[bind_each_def,FLOOKUP_UPDATE])
  \\ unlength_tac [heap_lookup_APPEND, heap_length_APPEND, heap_expand_def,
                   Abbr`el`, BlockRep_def, heap_lookup_def]
QED

Theorem v_inv_list_to_v =
  SIMP_RULE (srw_ss()) [LET_THM] v_inv_list_to_v_lem

(* A timestamp that is not in the  *)

Theorem all_ts_cons:
  ∀refs stack ts tag xs.
    all_ts refs (Block ts tag xs::stack) = ts INSERT all_ts refs (xs++stack)
Proof
  rw [all_ts_def, FUN_EQ_THM]
  \\ EQ_TAC
  >- (rw [] \\ fs [v_all_ts_def,MEM_FLAT,MEM_MAP]
      \\ metis_tac [v_all_ts_def])
  >- (rw [] \\ fs [v_all_ts_def,MEM_FLAT,MEM_MAP]
     >- (Q.EXISTS_TAC `Block ts tag xs`
        \\ fs [v_all_ts_def,MEM_FLAT,MEM_MAP])
     >- metis_tac [v_all_ts_def]
     >- (Q.EXISTS_TAC `Block ts tag xs`
        \\ fs [v_all_ts_def,MEM_FLAT,MEM_MAP]
        \\ metis_tac [])
     >- metis_tac [v_all_ts_def])
QED

Theorem all_ts_cons_no_block:
  ∀refs stack v.
    (∀ ts tag xs. v ≠ Block ts tag xs) ⇒ all_ts refs  (v::stack) = all_ts refs stack
Proof
  rw [all_ts_def, FUN_EQ_THM]
  \\ EQ_TAC \\ Cases_on `v`
  \\ rw [] \\ fs [v_all_ts_def,MEM_FLAT,MEM_MAP]
  \\ metis_tac [v_all_ts_def]
QED

(* NOT USED *)
Theorem all_ts_in_no_block:
     ∀refs stack v t.
       (∀ts tag xs. v ≠ Block ts tag xs) ∧
       t ∈ all_ts refs (v::stack)
       ⇒ t ∈ all_ts refs stack
Proof
  rw []
  \\ drule all_ts_cons_no_block
  \\ rw [] \\ fs []
QED

Theorem all_ts_append:
  ∀refs x y. all_ts refs (x ++ y) = all_ts refs x ∪ all_ts refs y
Proof
  rw [all_ts_def, FUN_EQ_THM]
  \\ EQ_TAC
  \\ rw [] \\ fs [v_all_ts_def,MEM_FLAT,MEM_MAP]
  \\ metis_tac [v_all_ts_def]
QED

Theorem all_ts_head:
  ∀refs x xs. all_ts refs (x::xs) = all_ts refs [x] ∪ all_ts refs xs
Proof
  rw [GSYM all_ts_append]
QED

Definition v_all_vs_def:
  v_all_vs (Block ts tag l :: xs) = Block ts tag l :: v_all_vs l ++ v_all_vs xs
∧ v_all_vs (x::xs)                = x :: v_all_vs xs
∧ v_all_vs [] = []
End

Definition all_vs_def:
  all_vs refs stack = { v | ∃(n:num) l. lookup n refs = SOME (ValueArray l) ∧ MEM v (v_all_vs l)} ∪
                      { v | MEM v (v_all_vs stack)}
End

Theorem v_all_vs_MEM:
  ∀l ts tag xs. MEM (Block ts tag xs) (v_all_vs l)
    ⇒ ∃x y. v_all_vs l =  x ++ Block ts tag xs :: v_all_vs xs ++ y
Proof
  ho_match_mp_tac (theorem "v_all_vs_ind")
  \\ rw [v_all_vs_def]
  >- (map_every qexists_tac [`[]`,`v_all_vs l'`] \\ rw [])
  >- (first_x_assum drule \\ rw []
     \\ map_every qexists_tac [`Block ts tag l::x`,`y ++ v_all_vs l'`]
     \\ rw [])
  >- (first_x_assum drule \\ rw []
     \\ map_every qexists_tac [`Block ts tag l::v_all_vs l ++ x`,`y`]
     \\ rw [])
  \\ first_x_assum  drule \\ rw [] \\ rw []
  \\ qmatch_goalsub_abbrev_tac `z::(_ ++ _)`
  \\ map_every qexists_tac [`z::x`,`y`] \\ EVAL_TAC
QED

Theorem v_in_all_vs:
  ∀x y stack refs.
    x ∈ all_vs refs stack ∧ MEM y (v_all_vs [x])
    ⇒ y ∈ all_vs refs stack
Proof
  rw [all_vs_def]
  >- (disj1_tac
     \\ cases_on `x` \\ fs [v_all_vs_def]
     \\ map_every qexists_tac [`n`,`l`]
     \\ rw []
     \\ drule_then ASSUME_TAC v_all_vs_MEM
     \\ fs [])
  >- (disj2_tac
     \\ cases_on `x` \\ fs [v_all_vs_def]
     \\ drule_then ASSUME_TAC v_all_vs_MEM
     \\ fs [])
QED

Theorem v_all_vs_MEM2:
  ∀l ts tag xs. MEM (Block ts tag xs) (v_all_vs l)
    ⇒ ∃x. MEM x l ∧ MEM (Block ts tag xs) (v_all_vs [x])
Proof
  Induct \\ rw [v_all_vs_def]
  \\ Cases_on `h` \\ fs [v_all_vs_def]
  >- metis_tac []
  >- metis_tac []
  >- (qexists_tac `Block n0 n l'` \\ rw [v_all_vs_def])
  >- (qexists_tac `Block n0 n l'` \\ rw [v_all_vs_def])
  >- (first_x_assum drule \\ rw [] \\ metis_tac [])
  \\ metis_tac []
QED

Theorem v_all_vs_ts:
  ∀x ts tag xs. MEM (Block ts tag xs) (v_all_vs [x]) ⇒ MEM ts (v_all_ts x)
Proof
  ho_match_mp_tac (theorem "v_all_ts_ind")
  \\ rw [v_all_vs_def,v_all_ts_def]
  \\ disj2_tac \\ drule_then ASSUME_TAC v_all_vs_MEM2
  \\ fs [] \\ first_x_assum (drule_then ASSUME_TAC)
  \\ first_x_assum (drule_then ASSUME_TAC)
  \\ rw [MEM_FLAT,MEM_MAP] \\ metis_tac []
QED

Theorem MEM_v_all_vs:
  ∀l v. MEM v l ⇒ MEM v (v_all_vs l)
Proof
  ho_match_mp_tac (theorem "v_all_vs_ind")
  \\ rw [v_all_vs_def]
  \\ metis_tac []
QED

Theorem MEM_stack_all_vs:
  ∀v stack refs. MEM v stack ⇒ v ∈ all_vs refs stack
Proof
  rw [all_vs_def,MEM_v_all_vs]
QED

Theorem v_all_vs_ts_MEM:
  ∀x y ts. MEM ts (v_all_ts x) ∧ MEM x (v_all_vs [y]) ⇒ MEM ts (v_all_ts y)
Proof
  ho_match_mp_tac (theorem "v_all_ts_ind")
  \\ rw [v_all_vs_def,v_all_ts_def]
  >- (ho_match_mp_tac v_all_vs_ts \\ metis_tac [])
  >- (fs [MEM_FLAT,MEM_MAP]
     \\ first_x_assum drule \\ rveq
     \\ disch_then drule
     \\ disch_then ho_match_mp_tac
     \\ drule_then ASSUME_TAC v_all_vs_MEM \\ fs []
     \\ metis_tac [MEM_v_all_vs])
QED

Theorem v_all_vs_trans:
  ∀x y z. MEM y (v_all_vs x) ∧ MEM z (v_all_vs [y]) ⇒ MEM z (v_all_vs x)
Proof
  rw [] \\ Cases_on `y` \\ fs [v_all_vs_def] \\ rveq \\ fs [v_all_vs_def]
  \\ drule_then ASSUME_TAC v_all_vs_MEM \\ fs []
QED

Theorem MEM_in_all_ts:
  ∀x ts stack refs.
    x ∈ all_vs refs stack ∧ MEM ts (v_all_ts x)
    ⇒ ts ∈ all_ts refs stack
Proof
  Cases \\  rw [all_vs_def,all_ts_def,v_all_ts_def]
  >- (drule_then ASSUME_TAC v_all_vs_MEM2 \\ fs []
     \\ drule_then ASSUME_TAC v_all_vs_ts \\ fs []
     \\ metis_tac [FRANGE_FLOOKUP])
  >- (fs [MEM_FLAT,MEM_MAP] \\ rveq
     \\ `MEM a (v_all_vs l')`
        by (drule_then ASSUME_TAC v_all_vs_MEM \\ fs [MEM_v_all_vs])
     \\ drule_then ASSUME_TAC v_all_vs_MEM2 \\ fs []
     \\ drule_then ASSUME_TAC v_all_vs_ts \\ fs []
     \\ `MEM a (v_all_vs [Block n0 n l])` by rw [v_all_vs_def,MEM_v_all_vs]
     \\ `MEM a (v_all_vs [x])`            by metis_tac [v_all_vs_trans]
     \\ `MEM ts (v_all_ts x)`             by metis_tac [v_all_vs_ts_MEM]
     \\ qexists_tac `x` \\ rw [] \\ disj1_tac
     \\ asm_exists_tac \\ rw [])
  >- (drule_then ASSUME_TAC v_all_vs_MEM2 \\ fs []
     \\ drule_then ASSUME_TAC v_all_vs_ts
     \\ metis_tac [])
  >- (fs [MEM_FLAT,MEM_MAP] \\ rveq
     \\ drule_then ASSUME_TAC v_all_vs_MEM2 \\ fs []
     \\ `MEM a (v_all_vs [Block n0 n l])` by rw [v_all_vs_def,MEM_v_all_vs]
     \\ `MEM a (v_all_vs [x])`            by metis_tac [v_all_vs_trans]
     \\ `MEM ts (v_all_ts x)`             by metis_tac [v_all_vs_ts_MEM]
     \\ metis_tac [])
QED

Theorem MEM_in_all_vs:
  ∀x y refs stack. x ∈ all_vs refs stack ∧ MEM y (v_all_vs [x]) ⇒ y ∈ all_vs refs stack
Proof
  rw [all_vs_def]
  \\ metis_tac [v_all_vs_trans]
QED

(* NOT USED *)
Theorem v_all_vs_ts_list:
  ∀x y ts. MEM x (v_all_vs y) ∧ MEM ts (v_all_ts x) ⇒ MEM ts (FLAT (MAP v_all_ts y))
Proof
  ho_match_mp_tac (theorem "v_all_ts_ind")
  \\ rw [v_all_vs_def,v_all_ts_def]
  >- (fs [MEM_FLAT,MEM_MAP]
     \\ drule_then ASSUME_TAC v_all_vs_MEM2 \\ fs []
     \\ drule_then ASSUME_TAC v_all_vs_ts \\ fs []
     \\ metis_tac [])
  >- (fs [MEM_FLAT,MEM_MAP]
     \\ drule_then ASSUME_TAC v_all_vs_MEM2 \\ fs [] \\ rveq
     \\ drule_then ASSUME_TAC v_all_vs_ts \\ fs []
     \\ first_x_assum drule \\ rveq \\ rw []
     \\ qpat_assum `MEM a _` (mp_then Any ASSUME_TAC MEM_v_all_vs)
     \\ first_x_assum drule \\ rveq \\ rw []
     \\ first_x_assum drule \\ rveq \\ rw []
     \\ `MEM ts' (v_all_ts (Block ts v0 xs))`
        by (rw [v_all_ts_def] \\ disj2_tac
           \\ fs [MEM_MAP,MEM_FLAT] \\ metis_tac [])
     \\ drule_then ASSUME_TAC v_all_vs_ts_MEM \\ fs []
     \\ metis_tac [])
QED

(* NOT USED *)
Theorem all_ts_alt:
  all_ts refs stack = { ts | ∃x. x ∈ all_vs refs stack ∧ MEM ts (v_all_ts x)}
Proof
  rw [FUN_EQ_THM]
  \\ EQ_TAC
  \\ rw []
  >- (fs [all_ts_def,all_vs_def] \\ metis_tac [FRANGE_FLOOKUP,MEM_v_all_vs])
  >- (drule MEM_in_all_ts \\ disch_then drule \\ fs [IN_DEF])
QED

Theorem v_inv_tf_update_thm:
  ∀v y f tf heap ts' a conf.
    v_inv conf v (y,f,tf,heap) ∧ ts' ∉ FDOM tf ⇒
    v_inv conf v (y,f, tf |+ (ts', a),heap)
Proof
  recInduct (fetch "-" "v_inv_ind") \\ fs [v_inv_def] \\ rw [] \\ rw []
  \\ fs [FLOOKUP_UPDATE]
  \\ CASE_TAC THEN1 fs [FLOOKUP_DEF]
  \\ qexists_tac `xs` \\ fs []
  \\ qpat_x_assum `LIST_REL _ _ _` mp_tac
  \\ match_mp_tac EVERY2_IMP_EVERY2
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem v_inv_tf_update:
  ∀y f tf heap heap1 a stack conf ts ts' tag xs refs.
     (Block ts tag xs) ∈ (all_vs refs stack) ∧
     ts' ∉ all_ts refs stack ∧
     v_inv conf (Block ts tag xs) (y,f,tf,heap)
     ⇒ v_inv conf ((Block ts tag xs)) (y,f, tf |+ (ts', a),heap)
Proof
  `∀x y f tf heap heap1 a stack conf ts ts' tag xs refs.
     x = Block ts tag xs ∧ (Block ts tag xs) ∈ (all_vs refs stack) ∧
      ts' ∉ all_ts refs stack ∧
      v_inv conf (Block ts tag xs) (y,f,tf,heap)
      ⇒ v_inv conf ((Block ts tag xs)) (y,f, tf |+ (ts', a),heap)`
  suffices_by metis_tac []
  \\ let val ind = theorem "v_inv_ind" |> Q.SPEC `λv (x,f,tf,heap). P v x f tf heap`
                                       |> SIMP_RULE std_ss []
                                       |> Q.GEN `P`
     in ho_match_mp_tac ind end
  \\ rw [v_inv_def,BlockRep_def]
  \\ every_case_tac \\ rfs []
  \\ `ts ∈ all_ts refs stack`
     by (ho_match_mp_tac MEM_in_all_ts
        \\ qexists_tac `Block ts n vs` \\ fs [v_all_ts_def])
  \\ conj_tac
  >- (qpat_x_assum `LIST_REL _ _ _` mp_tac
     \\ ONCE_REWRITE_TAC [LIST_REL_MEM]
     \\ ho_match_mp_tac  LIST_REL_mono
     \\ rw [] \\ fs []
     \\ Cases_on `x` \\ fs [v_inv_def,BlockRep_def]
     \\ first_x_assum drule
     \\ disch_then drule
     \\ rw [] \\ fs []
     \\ `MEM (Block n0 n' l) (v_all_vs [Block ts n vs])` by rw [v_all_vs_def,MEM_v_all_vs]
     \\ `Block n0 n' l ∈ all_vs refs stack` by metis_tac [MEM_in_all_vs]
     \\ first_x_assum drule \\ rw []
     \\ first_x_assum drule \\ rw []
     \\ first_x_assum drule \\ rw [])
  >- (fs [FLOOKUP_UPDATE]
     \\ every_case_tac
     \\ rveq \\ fs [])
QED

Theorem v_inv_tf_restrict:
  ∀v y f tf heap conf P.
     v_inv conf v (y,f,tf,heap) ∧ (∀x. MEM x (v_all_ts v) ⇒ x ∈ P)
     ⇒ v_inv conf v (y,f, DRESTRICT tf P,heap)
Proof
  let val ind = theorem "v_inv_ind" |> Q.SPEC `λv (x,f,tf,heap). P v x f tf heap`
                                    |> SIMP_RULE std_ss []
                                    |> Q.GEN `P`
  in ho_match_mp_tac ind end
  \\ rw [v_inv_def]
  \\ every_case_tac \\ fs []
  \\ qexists_tac `xs` \\ rw []
  >- (qpat_x_assum `LIST_REL _ _ _` mp_tac
     \\ ONCE_REWRITE_TAC [LIST_REL_MEM]
     \\ ho_match_mp_tac  LIST_REL_mono
     \\ rw [] \\ fs []
     \\ first_x_assum (drule_then (drule_then drule))
     \\ disch_then ho_match_mp_tac \\ rw []
     \\ first_x_assum ho_match_mp_tac \\ rw [v_all_ts_def]
     \\ Cases_on `x' = ts` \\ rw []
     \\ drule_then ASSUME_TAC MEM_v_all_vs
     \\ metis_tac [v_all_vs_ts_list])
  >- (fs [v_all_ts_def]
     \\ first_x_assum (qspec_then `ts` ASSUME_TAC)
     \\ fs []
     \\ fs [FLOOKUP_DRESTRICT])
QED

Theorem cons_thm_alt:
   abs_ml_inv conf (xs ++ stack) refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
    LENGTH xs < sp /\ xs <> [] ==>
    ?rs roots2 heap2.
      (roots = rs ++ roots2) /\ (LENGTH rs = LENGTH xs) /\
      (heap_store_unused_alt a (sp+sp1) (BlockRep tag rs) heap = (heap2,T)) /\
      abs_ml_inv conf
        ((Block ts tag xs)::stack) refs
        (Pointer a (Word (ptr_bits conf tag (LENGTH xs)))::roots2,
         heap2,be,a+el_length (BlockRep tag rs),
         sp-el_length (BlockRep tag rs),sp1,gens) limit (ts + 1)
Proof
  simp_tac std_ss [abs_ml_inv_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [bc_stack_ref_inv_def,LIST_REL_def]
  \\ `~(ts IN FDOM tf)` by
     (qpat_x_assum `FDOM tf ⊆ _` mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ rw [SUBSET_DEF] \\ CCONTR_TAC \\ fs [] \\ res_tac \\ fs [])
  \\ imp_res_tac LIST_REL_SPLIT1 \\ full_simp_tac std_ss []
  \\ Q.LIST_EXISTS_TAC [`ys1`,`ys2`] \\ full_simp_tac std_ss []
  \\ imp_res_tac EVERY2_LENGTH \\ full_simp_tac std_ss []
  \\ qpat_x_assum `unused_space_inv a (sp+sp1) heap` (fn th =>
    MATCH_MP (IMP_heap_store_unused_alt |> REWRITE_RULE [GSYM AND_IMP_INTRO]
      |> GEN_ALL) th
    |> ASSUME_TAC)
  \\ POP_ASSUM (qspec_then `(BlockRep tag ys1)` mp_tac) \\ match_mp_tac IMP_IMP
  \\ full_simp_tac std_ss [isDataElement_lemmas]
  \\ strip_tac THEN1 (fs [BlockRep_def,el_length_def] \\ DECIDE_TAC)
  \\ strip_tac \\ full_simp_tac std_ss []
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [roots_ok_def,MEM,BlockRep_def]
    \\ reverse (rpt strip_tac \\ res_tac) THEN1 metis_tac [heap_store_rel_def]
    \\ full_simp_tac (srw_ss()) [el_length_def,isSomeDataElement_def])
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [roots_ok_def,MEM,BlockRep_def,heap_ok_def,
      isForwardPointer_def] \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ rpt strip_tac \\ metis_tac [heap_store_rel_def])
  \\ strip_tac THEN1
   (fs [gc_kind_inv_def] \\ Cases_on `conf.gc_kind` \\ fs []
    \\ drule (GEN_ALL heap_store_unused_alt_gen_state_ok)
    \\ disch_then drule
    \\ drule (GEN_ALL heap_store_unused_alt_thm)
    \\ disch_then drule \\ fs []
    \\ fs [EVAL ``el_length (BlockRep tag ys)``]
    \\ strip_tac \\ fs [] \\ rveq \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ once_rewrite_tac [heap_split_APPEND_if] \\ fs []
    \\ fs [heap_split_def]
    \\ fs [EVAL ``el_length (BlockRep tag ys)``]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ once_rewrite_tac [heap_split_APPEND_if]
    \\ fs [heap_length_heap_expand] \\ rw []
    \\ `heap_split 0 h2 = SOME ([],h2)` by (Cases_on `h2` \\ fs [heap_split_def])
    \\ fs [heap_split_def]
    \\ EVAL_TAC \\ rw [] \\ EVAL_TAC)
  \\ strip_tac THEN1 (full_simp_tac std_ss [el_length_def,BlockRep_def] \\ fs [])
  \\ qexists_tac `f`
  \\ qexists_tac `tf |+ (ts, a)`
  \\ full_simp_tac std_ss []
  \\ strip_tac THEN1
   (match_mp_tac INJ_SUBSET
    \\ FIRST_ASSUM (match_exists_tac o concl)
    \\ full_simp_tac (srw_ss()) [isDataElement_def,BlockRep_def]
    \\ fs [SUBSET_DEF])
  \\ rpt strip_tac
  THEN1
   (qpat_x_assum `INJ ($' tf) (FDOM tf) _` mp_tac
    \\ rewrite_tac [INJ_DEF]
    \\ simp_tac (srw_ss()) [FAPPLY_FUPDATE_THM]
    \\ metis_tac [])
  THEN1 (rw [FDOM_FUPDATE,SUBSET_INSERT_RIGHT,all_ts_cons])
  THEN1 (fs [] \\ fs [SUBSET_DEF] \\ rw [] \\ res_tac \\ fs [])
  THEN1
   (full_simp_tac (srw_ss()) [v_inv_def]
    \\ full_simp_tac std_ss [BlockRep_def,el_length_def]
    \\ qexists_tac `ys1` \\ full_simp_tac std_ss []
    \\ full_simp_tac std_ss [EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS,FLOOKUP_UPDATE]
    \\ rpt strip_tac
    \\ match_mp_tac v_inv_tf_update_thm \\ asm_rewrite_tac []
    \\ match_mp_tac (GEN_ALL v_inv_SUBMAP)
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ qexists_tac `tf`
    \\ qexists_tac `f`
    \\ rewrite_tac [SUBMAP_REFL]
    \\ first_x_assum match_mp_tac
    \\ asm_rewrite_tac [])
  THEN1
   (full_simp_tac std_ss [EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS]
    \\ `f SUBMAP f` by full_simp_tac std_ss [SUBMAP_REFL]
    \\ rpt strip_tac \\ res_tac
    \\ `MEM (EL n stack) (xs ++ stack)` by (rw [EL_MEM])
    \\ match_mp_tac v_inv_tf_update_thm \\ asm_rewrite_tac []
    \\ match_mp_tac (GEN_ALL v_inv_SUBMAP)
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ fs [])
  \\ `reachable_refs (xs++stack) refs n` by
   (POP_ASSUM MP_TAC \\ simp_tac std_ss [reachable_refs_def]
    \\ rpt strip_tac \\ full_simp_tac std_ss [MEM] THEN1
     (NTAC 2 (POP_ASSUM MP_TAC) \\ full_simp_tac std_ss []
      \\ full_simp_tac std_ss [get_refs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]
      \\ full_simp_tac std_ss [MEM_APPEND] \\ metis_tac [])
    \\ full_simp_tac std_ss [MEM_APPEND] \\ metis_tac [])
  \\ res_tac \\ POP_ASSUM MP_TAC \\ simp_tac std_ss [bc_ref_inv_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [RefBlock_def]
  \\ Cases_on `FLOOKUP f n` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `lookup n refs` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `x'` \\ full_simp_tac (srw_ss()) []
  THEN1 (
    imp_res_tac heap_store_rel_lemma \\ full_simp_tac (srw_ss()) []
    \\ qpat_x_assum `EVERY2 PP zs l` MP_TAC
    \\ match_mp_tac EVERY2_IMP_EVERY2 \\ full_simp_tac (srw_ss()) []
    \\ rpt strip_tac \\ res_tac
    \\ match_mp_tac v_inv_tf_update_thm \\ asm_rewrite_tac []
    \\ match_mp_tac (GEN_ALL v_inv_SUBMAP)
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ fs [])
  \\ fs[Bytes_def,LET_THM] >> imp_res_tac heap_store_rel_lemma
  \\ metis_tac []
QED

Theorem cons_thm_EMPTY:
   abs_ml_inv conf stack refs (roots,heap:'a ml_heap,be,a,sp,sp1,gens) limit ts /\
    tag < dimword (:'a) DIV 16 ==>
    abs_ml_inv conf ((Block 0 tag [])::stack) refs
      (Data (Word (BlockNil tag))::roots,heap,be,a,sp,sp1,gens) limit ts
Proof
  simp_tac std_ss [abs_ml_inv_def] \\ rpt strip_tac
  \\ full_simp_tac std_ss [bc_stack_ref_inv_def,LIST_REL_def]
  \\ full_simp_tac (srw_ss()) [roots_ok_def,MEM]
  THEN1 (rw [] \\ fs [] \\ res_tac \\ fs [])
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ qexists_tac `tf` \\ full_simp_tac std_ss []
  \\ fs [all_ts_cons,SUBSET_INSERT_RIGHT]
  \\ full_simp_tac (srw_ss()) [v_inv_def]
  \\ rpt strip_tac \\ sg `reachable_refs stack refs n` \\ res_tac
  \\ full_simp_tac std_ss [reachable_refs_def]
  \\ Cases_on `x = Block 0 tag []` \\ full_simp_tac std_ss []
  \\ full_simp_tac (srw_ss()) [get_refs_def] \\ metis_tac []
QED

(* word64 *)

Theorem word64_alt_thm:
   abs_ml_inv conf (ws ++ stack) refs (rs ++ roots,heap,be,a,sp,sp1,gens) limit ts ∧
   LENGTH ws = LENGTH rs ∧
   (Word64Rep (:'a) w64 :'a ml_el) = DataElement [] len (Word64Tag,xs) ∧
   LENGTH xs < sp
   ⇒
   ∃heap2.
     heap_store_unused_alt a (sp + sp1) (Word64Rep (:'a) w64) heap = (heap2,T) ∧
     abs_ml_inv conf (Word64 w64::stack) refs
       (Pointer a (Word 0w)::roots,heap2,
        be,a + len + 1,sp - len - 1,sp1,gens) limit ts
Proof
  rw[abs_ml_inv_def]
  \\ qpat_abbrev_tac`wr = DataElement _ _ _`
  \\ `el_length wr = len + 1`
  by ( fs[Abbr`wr`,Word64Rep_def] \\ rw[] \\ fs[el_length_def])
  \\ `LENGTH xs = len`
  by (
    fs[Word64Rep_def,Abbr`wr`,el_length_def]
    \\ every_case_tac \\ fs[]
    \\ clean_tac \\ fs[] )
  \\ qunabbrev_tac`wr`
  \\ clean_tac
  \\ rpt_drule IMP_heap_store_unused_alt
  \\ disch_then(qspec_then`Word64Rep(:'a)w64`mp_tac)
  \\ impl_tac >- fs[] \\ strip_tac \\ rfs[]
  \\ conj_tac
  >- (
    fs[roots_ok_def,heap_store_rel_def]
    \\ rw[] \\ rfs[]
    >- (simp[Word64Rep_def] \\ rw[isSomeDataElement_def])
    \\ res_tac \\ res_tac \\ fs[] )
  \\ conj_tac
  >- (
    fs[heap_ok_def] \\ rfs[]
    \\ conj_tac
    >- (
      first_x_assum match_mp_tac
      \\ simp[Word64Rep_def] \\ rw[isForwardPointer_def] )
    \\ rw[]
    >- (
      fs[Word64Rep_def]
      \\ every_case_tac \\ rfs[]
      \\ clean_tac \\ fs[] )
    \\ metis_tac[heap_store_rel_lemma,isSomeDataElement_def] )
  \\ rfs[]
  \\ fs[bc_stack_ref_inv_def]
  \\ conj_tac THEN1
   (fs [gc_kind_inv_def] \\ Cases_on `conf.gc_kind` \\ fs []
    \\ drule (GEN_ALL heap_store_unused_alt_gen_state_ok)
    \\ disch_then drule
    \\ drule (GEN_ALL heap_store_unused_alt_thm)
    \\ disch_then drule \\ fs []
    \\ fs [el_length_def]
    \\ strip_tac \\ fs [] \\ rveq \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ once_rewrite_tac [heap_split_APPEND_if] \\ fs []
    \\ fs [heap_split_def]
    \\ fs [el_length_def]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ once_rewrite_tac [heap_split_APPEND_if]
    \\ fs [heap_length_heap_expand] \\ rw []
    \\ `heap_split 0 h2 = SOME ([],h2)` by (Cases_on `h2` \\ fs [heap_split_def])
    \\ fs [heap_split_def]
    \\ EVAL_TAC \\ rw [] \\ EVAL_TAC)
  \\ qexists_tac`f` \\ fs[]
  \\ qexists_tac `DRESTRICT tf (all_ts refs stack)` \\ fs []
  \\ fs[isDataElement_def]
  \\ conj_tac
  >- fs[INJ_DEF]
  \\ conj_tac
  >- fs[INJ_DEF,DRESTRICT_DEF]
  \\ conj_tac
  >- (fs [all_ts_cons_no_block,DRESTRICT_DEF])
  \\ conj_tac
  >- (fs [all_ts_cons_no_block,DRESTRICT_DEF,SUBSET_DEF,IN_INTER])
  \\ conj_tac
  >- (
    simp[v_inv_def]
    \\ match_mp_tac EVERY2_MEM_MONO
    \\ imp_res_tac LIST_REL_APPEND_IMP
    \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
    \\ simp[FORALL_PROD] \\ rw[]
    \\ ho_match_mp_tac v_inv_tf_restrict
    \\ conj_tac
    >- (match_mp_tac v_inv_SUBMAP \\ simp[])
    >- (rw [] \\ ho_match_mp_tac MEM_in_all_ts
       \\ qexists_tac `p_1` \\ rw []
       \\ ho_match_mp_tac MEM_stack_all_vs
       \\ drule MEM_ZIP2 \\ rw []
       \\ rw [EL_MEM]))
  \\ fs[reachable_refs_def,PULL_EXISTS]
  \\ rw[]
  >- fs[get_refs_def]
  \\ fs[bc_ref_inv_def]
  \\ fsrw_tac[boolSimps.DNF_ss][]
  \\ first_x_assum rpt_drule
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[] \\ rw[]
  \\ fs[RefBlock_def,Bytes_def]
  \\ imp_res_tac heap_store_rel_lemma
  \\ fs[]
  \\ TRY (qexists_tac`ws'` \\ simp[])
  \\ match_mp_tac EVERY2_MEM_MONO
  \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
  \\ simp[FORALL_PROD] \\ rw[]
  \\ ho_match_mp_tac v_inv_tf_restrict
  \\ conj_tac
  >- (match_mp_tac v_inv_SUBMAP \\ simp[])
  >- (rw [] \\ ho_match_mp_tac MEM_in_all_ts
       \\ qexists_tac `p_2` \\ rw []
       \\ rw [all_vs_def] \\ disj1_tac
       \\ map_every qexists_tac [`n`,`l`] \\ rw []
       \\ ho_match_mp_tac MEM_v_all_vs
       \\ drule MEM_ZIP2 \\ rw []
       \\ rw [EL_MEM])
QED

(* bignum *)

Theorem bignum_alt_thm:
   abs_ml_inv conf (ws ++ stack) refs (rs ++ roots,heap,be,a,sp,sp1,gens) limit ts ∧
   LENGTH ws = LENGTH rs ∧ ¬small_int (:α) i ∧
   (Bignum i :α ml_el) = DataElement [] len (tag,xs) ∧
   LENGTH xs < sp ⇒
   ∃heap2.
   heap_store_unused_alt a (sp+sp1) (Bignum i) heap = (heap2,T) ∧
   abs_ml_inv conf (Number i::stack) refs
     (Pointer a (Word (0w:α word))::roots,heap2,be,a+len+1,sp-len-1,sp1,gens) limit ts
Proof
  rw[abs_ml_inv_def]
  \\ qmatch_assum_abbrev_tac`br = DataElement _ _ _`
  \\ `el_length br = len + 1` by
   (fs[Bignum_def,Abbr`br`] \\ pairarg_tac \\ rw[] \\ fs[el_length_def])
  \\ `LENGTH xs = len` by
   (fs[Bignum_def,Abbr`br`,el_length_def]
    \\ pairarg_tac \\ fs[]
    \\ clean_tac \\ fs[])
  \\ var_eq_tac
  \\ `el_length br ≤ sp + sp1` by simp[]
  \\ Q.ISPEC_THEN`br`rpt_drule (Q.GEN`x`(IMP_heap_store_unused_alt))
  \\ disch_then strip_assume_tac
  \\ rfs[]
  \\ conj_tac
  >- (
    fs[roots_ok_def,heap_store_rel_def]
    \\ rw[] \\ rfs[]
    >- (rw[isSomeDataElement_def])
    \\ res_tac \\ res_tac \\ fs[] )
  \\ conj_tac
  >- (
    fs[heap_ok_def] \\ rfs[]
    \\ conj_tac
    >- (
      first_x_assum match_mp_tac
      \\ rw[isForwardPointer_def] )
    \\ rw[]
    >- (
      every_case_tac \\ rfs[]
      \\ clean_tac \\ fs[] )
    \\ metis_tac[heap_store_rel_lemma,isSomeDataElement_def] )
  \\ rfs[]
  \\ fs[bc_stack_ref_inv_def]
  \\ conj_tac THEN1
   (`tag <> RefTag` by
     (CCONTR_TAC \\ qpat_x_assum `Abbrev _` mp_tac
      \\ fs [Bignum_def,markerTheory.Abbrev_def]
      \\ pairarg_tac \\ fs [] \\ NO_TAC)
    \\ fs [gc_kind_inv_def] \\ Cases_on `conf.gc_kind` \\ fs []
    \\ drule (GEN_ALL heap_store_unused_alt_gen_state_ok)
    \\ disch_then drule
    \\ drule (GEN_ALL heap_store_unused_alt_thm)
    \\ disch_then drule \\ fs []
    \\ fs [el_length_def]
    \\ strip_tac \\ fs [] \\ rveq \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ once_rewrite_tac [heap_split_APPEND_if] \\ fs []
    \\ fs [heap_split_def]
    \\ fs [el_length_def]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ once_rewrite_tac [heap_split_APPEND_if]
    \\ fs [heap_length_heap_expand] \\ rw []
    \\ `heap_split 0 h2 = SOME ([],h2)` by (Cases_on `h2` \\ fs [heap_split_def])
    \\ fs [heap_split_def]
    \\ EVAL_TAC \\ rw [] \\ EVAL_TAC \\ fs [])
  \\ qexists_tac`f` \\ fs[]
  \\ qexists_tac `DRESTRICT tf (all_ts refs stack)` \\ fs []
  \\ fs[isDataElement_def]
  \\ conj_tac
  >- fs[INJ_DEF]
  \\ conj_tac
  >- fs[INJ_DEF,DRESTRICT_DEF]
  \\ conj_tac
  >- (fs [all_ts_cons_no_block,DRESTRICT_DEF])
  \\ conj_tac
  >- (fs [all_ts_cons_no_block,DRESTRICT_DEF,SUBSET_DEF,IN_INTER])
  \\ conj_tac
  >- (
    simp[v_inv_def]
    \\ match_mp_tac EVERY2_MEM_MONO
    \\ imp_res_tac LIST_REL_APPEND_IMP
    \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
    \\ simp[FORALL_PROD] \\ rw[]
    \\ ho_match_mp_tac v_inv_tf_restrict
    \\ conj_tac
    >- (match_mp_tac v_inv_SUBMAP \\ simp[])
    >- (rw [] \\ ho_match_mp_tac MEM_in_all_ts
       \\ qexists_tac `p_1` \\ rw []
       \\ ho_match_mp_tac MEM_stack_all_vs
       \\ drule MEM_ZIP2 \\ rw []
       \\ rw [EL_MEM]))
  \\ fs[reachable_refs_def,PULL_EXISTS]
  \\ rw[]
  >- fs[get_refs_def]
  \\ fs[bc_ref_inv_def]
  \\ fsrw_tac[boolSimps.DNF_ss][]
  \\ first_x_assum rpt_drule
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[] \\ rw[]
  \\ fs[RefBlock_def,Bytes_def]
  \\ imp_res_tac heap_store_rel_lemma
  \\ fs[]
  \\ TRY (qexists_tac`ws'` \\ simp[])
  \\ match_mp_tac EVERY2_MEM_MONO
  \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
  \\ simp[FORALL_PROD] \\ rw[]
  \\ ho_match_mp_tac v_inv_tf_restrict
  \\ conj_tac
  >- (match_mp_tac v_inv_SUBMAP \\ simp[])
  >- (rw [] \\ ho_match_mp_tac MEM_in_all_ts
       \\ qexists_tac `p_2` \\ rw []
       \\ rw [all_vs_def] \\ disj1_tac
       \\ map_every qexists_tac [`n`,`l`] \\ rw []
       \\ ho_match_mp_tac MEM_v_all_vs
       \\ drule MEM_ZIP2 \\ rw []
       \\ rw [EL_MEM])
QED

(* update ref *)

Triviality ref_edge_ValueArray:
  ref_edge (insert ptr (ValueArray xs) refs) x y =
    if x = ptr then MEM y (get_refs (Block 0 ARB xs)) else ref_edge refs x y
Proof
  simp_tac std_ss [FUN_EQ_THM,ref_edge_def] \\ rpt strip_tac
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
  \\ Cases_on `x = ptr` \\ full_simp_tac (srw_ss()) []
  \\ rw [lookup_insert]
QED

Triviality reachable_refs_UPDATE:
  reachable_refs (xs ++ RefPtr b ptr::stack) (insert ptr (ValueArray xs) refs) n ==>
    reachable_refs (xs ++ RefPtr b ptr::stack) refs n
Proof
  full_simp_tac std_ss [reachable_refs_def] \\ rpt strip_tac
  \\ Cases_on `?m. MEM m (get_refs (Block 0 ARB xs)) /\
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
  \\ full_simp_tac std_ss [] \\ res_tac
QED

Triviality reachable_refs_UPDATE1:
  reachable_refs (xs ++ RefPtr b ptr::stack) (insert ptr (ValueArray xs1) refs) n ==>
    (!v. MEM v xs1 ==> ~MEM v xs ==> ?xs2. (lookup ptr refs = SOME (ValueArray xs2)) /\ MEM v xs2) ==>
    reachable_refs (xs ++ RefPtr b ptr::stack) refs n
Proof
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
      qexists_tac`RefPtr b ptr`>>simp[get_refs_def]>>
      simp[Once RTC_CASES1]>>simp[ref_edge_def,get_refs_def]>>
      simp[MEM_MAP,MEM_FLAT,PULL_EXISTS]>>metis_tac[]) >>
    BasicProvers.VAR_EQ_TAC >>
    metis_tac[]) >>
  strip_tac >>
  rpt gen_tac >> strip_tac >>
  match_mp_tac (METIS_PROVE[]``(P ==> (Q ==> R)) ==> (Q ==> P ==> R)``) >>
  strip_tac >>
  first_x_assum(qspecl_then[`RefPtr b r'`,`xs`,`[RefPtr b r']`]mp_tac) >>
  simp[get_refs_def] >>
  strip_tac >- metis_tac[] >- metis_tac[] >>
  BasicProvers.VAR_EQ_TAC >> fs[get_refs_def] >>
  rw[] >> metis_tac[RTC_CASES1]
QED

Definition isRefBlock_def:
  isRefBlock x = ?p. x = RefBlock p
End

Definition RefBlock_inv_def:
  RefBlock_inv heap heap2 <=>
    (!n x. (heap_lookup n heap = SOME x) /\ ~(isRefBlock x) ==>
           (heap_lookup n heap2 = SOME x)) /\
    (!n x. (heap_lookup n heap2 = SOME x) /\ ~(isRefBlock x) ==>
           (heap_lookup n heap = SOME x))
End

Theorem heap_store_RefBlock_thm:
   !ha. (LENGTH x = LENGTH y) ==>
         (heap_store (heap_length ha) [RefBlock x] (ha ++ RefBlock y::hb) =
           (ha ++ RefBlock x::hb,T))
Proof
  Induct \\ full_simp_tac (srw_ss()) [heap_store_def,heap_length_def]
  THEN1 full_simp_tac std_ss [RefBlock_def,el_length_def] \\ strip_tac
  \\ rpt strip_tac \\ full_simp_tac std_ss []
  \\ `~(el_length h + SUM (MAP el_length ha) < el_length h) /\ el_length h <> 0` by
       (Cases_on `h` \\ full_simp_tac std_ss [el_length_def] \\ DECIDE_TAC)
  \\ full_simp_tac std_ss [LET_DEF]
QED

Triviality heap_lookup_RefBlock_lemma:
  (heap_lookup n (ha ++ RefBlock y::hb) = SOME x) =
      if n < heap_length ha then
        (heap_lookup n ha = SOME x)
      else if n = heap_length ha then
        (x = RefBlock y)
      else if heap_length ha + (LENGTH y + 1) <= n then
        (heap_lookup (n - heap_length ha - (LENGTH y + 1)) hb = SOME x)
      else F
Proof
  Cases_on `n < heap_length ha` \\ full_simp_tac std_ss [LESS_IMP_heap_lookup]
  \\ full_simp_tac std_ss [NOT_LESS_IMP_heap_lookup]
  \\ full_simp_tac std_ss [heap_lookup_def]
  \\ Cases_on `n <= heap_length ha` \\ full_simp_tac std_ss []
  THEN1 (`heap_length ha = n` by DECIDE_TAC \\ full_simp_tac std_ss [] \\ metis_tac [])
  \\ `heap_length ha <> n` by DECIDE_TAC \\ full_simp_tac std_ss []
  \\ `0 < el_length (RefBlock y)`
       by (full_simp_tac std_ss [el_length_def,RefBlock_def] >> decide_tac)
  \\ full_simp_tac std_ss [] \\ srw_tac [] []
  \\ full_simp_tac std_ss [el_length_def,RefBlock_def,NOT_LESS]
  \\ DISJ1_TAC \\ DECIDE_TAC
QED

Triviality heap_store_RefBlock:
  (LENGTH y = LENGTH h) /\
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
                  (heap_lookup m heap2 = SOME x)
Proof
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
  \\ metis_tac []
QED

Triviality NOT_isRefBlock:
  ~(isRefBlock (Bignum x)) /\
    ~(isRefBlock (Word64Rep a w)) /\
    ~(isRefBlock (DataElement xs (LENGTH xs) (BlockTag n,[])))
Proof
  simp_tac (srw_ss()) [isRefBlock_def,RefBlock_def,Bignum_def]
  \\ Cases_on`a` \\ rw[]
  \\ TRY pairarg_tac \\ fs[]
  \\ EVAL_TAC \\ rw[]
QED

Triviality v_inv_Ref:
  RefBlock_inv heap heap2 ==>
    !x h f tf. (v_inv conf x (h,f,tf,heap2) = v_inv conf x (h,f,tf,heap))
Proof
  strip_tac \\ completeInduct_on `v_size x` \\ NTAC 3 strip_tac
  \\ full_simp_tac std_ss [PULL_FORALL] \\ Cases_on `x` THEN1
   (full_simp_tac std_ss [v_inv_def] \\ srw_tac [] []
    \\ rpt strip_tac \\ full_simp_tac std_ss []
    \\ full_simp_tac std_ss [RefBlock_inv_def]
    \\ metis_tac [NOT_isRefBlock])
  THEN1 (
    fs[v_inv_def,RefBlock_inv_def]
    \\ metis_tac[NOT_isRefBlock] )
  THEN1 (full_simp_tac (srw_ss()) [v_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ Cases_on `l = []` \\ full_simp_tac std_ss []
    \\ full_simp_tac (srw_ss()) [v_inv_def,ADDR_APPLY_def,BlockRep_def]
    \\ rpt strip_tac
    \\ full_simp_tac std_ss [EVERY2_EVERY,LENGTH_ADDR_MAP,EVERY_MEM,FORALL_PROD]
    \\ rpt strip_tac \\ EQ_TAC \\ rpt strip_tac
    THEN1
     (qpat_x_assum `LENGTH l = LENGTH xs` ASSUME_TAC
      \\ full_simp_tac (srw_ss()) [MEM_ZIP,LENGTH_ADDR_MAP,PULL_EXISTS]
      \\ `heap_lookup ptr heap =
           SOME (DataElement xs (LENGTH xs) (BlockTag n,[]))` by
              metis_tac [RefBlock_inv_def,NOT_isRefBlock]
      \\ full_simp_tac (srw_ss()) [MEM_ZIP]
      \\ rpt strip_tac
      \\ Q.MATCH_ASSUM_RENAME_TAC `t < LENGTH xs` \\ res_tac
      \\ `MEM (EL t l) l` by (full_simp_tac std_ss [MEM_EL] \\ metis_tac [])
      \\ imp_res_tac MEM_IMP_v_size
      \\ last_x_assum $ qspec_then ‘EL t l’ mp_tac \\ gvs []
      \\ metis_tac [])
    THEN1
     (qpat_x_assum `LENGTH l = LENGTH xs` ASSUME_TAC
      \\ full_simp_tac (srw_ss()) [MEM_ZIP,LENGTH_ADDR_MAP,PULL_EXISTS]
      \\ `heap_lookup ptr heap2 =
           SOME (DataElement xs (LENGTH xs) (BlockTag n,[]))` by
              metis_tac [RefBlock_inv_def,NOT_isRefBlock]
      \\ full_simp_tac (srw_ss()) [MEM_ZIP]
      \\ rpt strip_tac
      \\ Q.MATCH_ASSUM_RENAME_TAC `t < LENGTH xs` \\ res_tac
      \\ `MEM (EL t l) l` by (full_simp_tac std_ss [MEM_EL] \\ metis_tac [])
      \\ `MEM (EL t l) l` by (full_simp_tac std_ss [MEM_EL] \\ metis_tac [])
      \\ imp_res_tac MEM_IMP_v_size
      \\ last_x_assum $ qspec_then ‘EL t l’ mp_tac \\ gvs []
      \\ metis_tac []))
  THEN1 (full_simp_tac std_ss [v_inv_def])
  THEN1 (full_simp_tac (srw_ss()) [v_inv_def,SUBMAP_DEF])
QED

val heap_lookup_heap_split = prove(
  ``!heap a b h1 h2 x.
      heap_split a heap = SOME (h1,h2) /\
      heap_lookup b heap = SOME x ==>
      if b < a then MEM x h1 else MEM x h2``,
  rpt strip_tac
  \\ drule heap_lookup_SPLIT \\ fs [] \\ strip_tac
  \\ rveq \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ full_simp_tac std_ss [heap_split_APPEND_if]
  \\ IF_CASES_TAC \\ fs [GSYM NOT_LESS]
  \\ every_case_tac \\ fs [] \\ rveq \\ fs []
  \\ fs [NOT_LESS]
  \\ CCONTR_TAC \\ fs []
  \\ fs [heap_split_def]
  \\ Cases_on `a = heap_length ha` \\ fs []
  \\ rveq \\ fs [] \\ rfs []
  \\ every_case_tac \\ fs [] \\ rveq \\ fs []);

Theorem heap_store_heap_lookup:
   !heap heap2 a x n.
      heap_store a x heap = (heap2,T) /\ n < a ==>
      heap_lookup n heap = heap_lookup n heap2
Proof
  Induct THEN1 fs [heap_lookup_def,heap_store_def]
  \\ simp [heap_store_def]
  \\ rpt strip_tac \\ every_case_tac \\ fs []
  \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
  \\ once_rewrite_tac [heap_lookup_def] \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ rpt strip_tac
  \\ first_x_assum match_mp_tac
  \\ asm_exists_tac \\ fs []
QED

val update_ref_gen_state_ok = prove(
  ``heap_store b [RefBlock t1] heap = (heap2,T) /\ a <= b /\
    gen_state_ok a (a + (sp + sp1)) heap gens ==>
    gen_state_ok a (a + (sp + sp1)) heap2 gens``,
  Cases_on `gens` \\ fs [gen_state_ok_def]
  \\ fs [EVERY_MEM] \\ rpt strip_tac \\ fs [] \\ res_tac
  \\ fs [gen_start_ok_def] \\ rpt strip_tac
  \\ drule (GEN_ALL heap_split_heap_store)
  \\ disch_then drule \\ fs [] \\ strip_tac
  \\ fs [] \\ rpt strip_tac \\ res_tac \\ fs []) |> GEN_ALL;

val data_up_to_alt = prove(
  ``(data_up_to n [] <=> (n = 0)) /\
    (data_up_to n (x::xs) <=>
       if n = 0 then T else
       if n < el_length x \/ ~isDataElement x then F else
         data_up_to (n - el_length x) xs)``,
  fs [data_up_to_def,heap_split_def]
  \\ IF_CASES_TAC \\ fs []
  \\ rpt (CASE_TAC \\ fs [])
  \\ rw [] \\ eq_tac \\ rw []);

Theorem data_up_to_heap_store:
   !heap a b heap2 y.
      data_up_to a heap /\ heap_store b [y] heap = (heap2,T) /\
      isDataElement y ==> data_up_to a heap2
Proof
  Induct \\ fs [heap_store_def]
  \\ rpt gen_tac \\ fs [data_up_to_alt]
  \\ Cases_on `a = 0` \\ fs []
  THEN1 (fs [data_up_to_def])
  \\ Cases_on `b = 0` \\ fs []
  THEN1
   (fs [el_length_def] \\ strip_tac \\ rveq \\ fs []
    \\ fs [data_up_to_alt,heap_length_def])
  \\ IF_CASES_TAC \\ fs [] \\ pairarg_tac \\ fs []
  \\ strip_tac \\ rveq \\ fs []
  \\ fs [data_up_to_alt,heap_length_def]
  \\ first_x_assum match_mp_tac \\ fs []
  \\ asm_exists_tac \\ fs []
QED

Theorem update_ref_thm:
   abs_ml_inv conf (xs ++ (RefPtr b ptr)::stack) refs
    (roots,heap,be,a,sp,sp1,gens) limit ts /\
    (lookup ptr refs = SOME (ValueArray xs1)) /\ (LENGTH xs = LENGTH xs1) ==>
    ?p rs roots2 heap2 u.
      (roots = rs ++ Pointer p u :: roots2) /\
      (heap_store p [RefBlock rs] heap = (heap2,T)) /\
      abs_ml_inv conf (xs ++ (RefPtr b ptr)::stack) (insert ptr (ValueArray xs) refs)
        (roots,heap2,be,a,sp,sp1,gens) limit ts
Proof
  simp_tac std_ss [abs_ml_inv_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [bc_stack_ref_inv_def]
  \\ imp_res_tac EVERY2_APPEND_CONS
  \\ full_simp_tac std_ss [v_inv_def]
  \\ Q.LIST_EXISTS_TAC [`f ' ptr`,`t1`,`t2`]
  \\ full_simp_tac std_ss []
  \\ `reachable_refs (xs ++ RefPtr b ptr::stack) refs ptr` by
   (full_simp_tac std_ss [reachable_refs_def] \\ qexists_tac `RefPtr b ptr`
    \\ full_simp_tac (srw_ss()) [get_refs_def])
  \\ res_tac \\ POP_ASSUM MP_TAC \\ simp_tac std_ss [Once bc_ref_inv_def]
  \\ Cases_on `lookup ptr refs` \\ full_simp_tac (srw_ss()) []
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
   (fs [gc_kind_inv_def] \\ every_case_tac \\ fs[]
    \\ conj_tac THEN1
     (match_mp_tac update_ref_gen_state_ok
      \\ asm_exists_tac \\ fs []
      \\ rpt_drule heap_lookup_heap_split
      \\ IF_CASES_TAC \\ fs [] \\ strip_tac
      \\ fs [EVERY_MEM] \\ res_tac
      \\ fs [EVAL ``isRef (RefBlock zs)``])
    \\ drule heap_split_heap_length \\ strip_tac
    \\ qpat_x_assum `_ ++ _ = _` (assume_tac o GSYM)
    \\ fs[] \\ fs[heap_lookup_APPEND] \\ every_case_tac \\ fs[] \\ rfs[]
    \\ qpat_x_assum `heap_lookup _ _ = SOME (RefBlock zs)` assume_tac
    \\ drule heap_lookup_SPLIT \\ strip_tac \\ fs[] \\ rveq \\ fs[]
    THEN1 fs[RefBlock_def,isRef_def]
    \\ qpat_x_assum `heap_store _ _ _ = _` mp_tac
    \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,heap_store_lemma]
    \\ disch_then (assume_tac o GSYM) \\ fs[]
    \\ `f ' ptr = heap_length(h1 ++ ha)` by fs[heap_length_APPEND]
    \\ fs[heap_store_lemma]
    \\ qpat_x_assum `heap_length h1 = _` (assume_tac o GSYM) \\ fs[]
    \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,gen_gc_partialTheory.heap_split_length]
    \\ fs[isRef_def,RefBlock_def])
  \\ strip_tac THEN1
   (full_simp_tac std_ss [unused_space_inv_def] \\ rpt strip_tac
    \\ res_tac \\ Cases_on `a = f ' ptr` \\ full_simp_tac (srw_ss()) []
    THEN1 full_simp_tac (srw_ss()) [RefBlock_def]
    \\ full_simp_tac std_ss [RefBlock_inv_def]
    \\ res_tac \\ full_simp_tac (srw_ss()) [isRefBlock_def,RefBlock_def]
    \\ imp_res_tac data_up_to_heap_store \\ fs [])
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ qexists_tac `DRESTRICT tf (all_ts (insert ptr (ValueArray xs) refs) (xs ++ RefPtr b ptr::stack))`
  \\ full_simp_tac std_ss []
  \\ MP_TAC v_inv_Ref
  \\ full_simp_tac std_ss [] \\ rpt strip_tac
  THEN1 (fs [SUBSET_DEF])
  THEN1 (fs [INJ_DEF,DRESTRICT_DEF])
  THEN1 (fs [SUBSET_DEF,DRESTRICT_DEF])
  THEN1 (fs [SUBSET_DEF,DRESTRICT_DEF,SUBSET_DEF,IN_INTER])
  >- (match_mp_tac EVERY2_MEM_MONO
     \\ imp_res_tac LIST_REL_APPEND_IMP
     \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
     \\ simp[FORALL_PROD] \\ rw[]
     \\ ho_match_mp_tac v_inv_tf_restrict
     \\ rw []
     \\ ho_match_mp_tac MEM_in_all_ts
     \\ qexists_tac `p_1` \\ rw []
     \\ ho_match_mp_tac MEM_stack_all_vs
     \\ qmatch_asmsub_abbrev_tac `MEM (_,_) (ZIP (l,_))`
     \\ drule MEM_ZIP2 \\ rw []
     \\ rw [EL_MEM])
  \\ `reachable_refs (xs ++ RefPtr b ptr::stack) refs n` by imp_res_tac reachable_refs_UPDATE
  \\ Cases_on `n = ptr` \\ full_simp_tac (srw_ss()) [bc_ref_inv_def] THEN1
   (srw_tac [] [] \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,RefBlock_def]
    \\ imp_res_tac EVERY2_SWAP \\ full_simp_tac std_ss []
    \\ match_mp_tac EVERY2_MEM_MONO
    \\ imp_res_tac LIST_REL_APPEND_IMP
    \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
    \\ simp[FORALL_PROD] \\ rw[]
    \\ ho_match_mp_tac v_inv_tf_restrict
    \\ rw []
    \\ ho_match_mp_tac MEM_in_all_ts
    \\ qexists_tac `p_2` \\ rw []
    \\ ho_match_mp_tac MEM_stack_all_vs
    \\ qmatch_asmsub_abbrev_tac `MEM (_,_) (ZIP (l,_))`
    \\ drule MEM_ZIP2 \\ rw []
    \\ rw [EL_MEM]) \\ res_tac
  \\ Cases_on `FLOOKUP f n` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `lookup n refs` \\ full_simp_tac (srw_ss()) []
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,FAPPLY_FUPDATE_THM,lookup_insert] \\ rw []
  \\ Cases_on `x'''` \\ full_simp_tac (srw_ss()) []
  >- (qexists_tac `zs'` \\ conj_tac
     >- (first_x_assum ho_match_mp_tac \\ rw [] \\ CCONTR_TAC \\ metis_tac [INJ_DEF])
     >- (match_mp_tac EVERY2_MEM_MONO
        \\ imp_res_tac LIST_REL_APPEND_IMP
        \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
        \\ simp[FORALL_PROD] \\ rw[]
        \\ ho_match_mp_tac v_inv_tf_restrict
        \\ rw []
        \\ ho_match_mp_tac MEM_in_all_ts
        \\ qexists_tac `p_2` \\ rw []
        \\ rw [all_vs_def] \\ disj1_tac
        \\ map_every qexists_tac [`n`,`l`]
        \\ rw [lookup_insert]
        \\ ho_match_mp_tac MEM_v_all_vs
        \\ drule MEM_ZIP2 \\ rw []
        \\ rw [EL_MEM]))
  \\ (full_simp_tac (srw_ss()) [INJ_DEF] \\ metis_tac [])
QED

Definition heap_deref_def:
  (heap_deref a heap =
    case heap_lookup a heap of
    | SOME (DataElement xs l (RefTag,[])) => SOME xs
    | _ => NONE)
End

Theorem update_ref_thm1:
   abs_ml_inv conf (xs ++ RefPtr b ptr::stack) refs
    (roots,heap,be,a,sp,sp1,gens) limit ts /\
    (lookup ptr refs = SOME (ValueArray xs1)) /\ i < LENGTH xs1 /\ 0 < LENGTH xs
    ==>
    ?p rs roots2 vs1 heap2 u.
      (roots = rs ++ Pointer p u :: roots2) /\ (LENGTH rs = LENGTH xs) /\
      (heap_deref p heap = SOME vs1) /\ LENGTH vs1 = LENGTH xs1 /\
      (heap_store p [RefBlock (LUPDATE (HD rs) i vs1)] heap = (heap2,T)) /\
      abs_ml_inv conf (xs ++ (RefPtr b ptr)::stack)
        (insert ptr (ValueArray (LUPDATE (HD xs) i xs1)) refs)
        (roots,heap2,be,a,sp,sp1,gens) limit ts
Proof
  simp_tac std_ss [abs_ml_inv_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [bc_stack_ref_inv_def]
  \\ imp_res_tac EVERY2_APPEND_CONS
  \\ full_simp_tac std_ss [v_inv_def]
  \\ Q.LIST_EXISTS_TAC [`f ' ptr`,`t1`,`t2`]
  \\ full_simp_tac std_ss []
  \\ `reachable_refs (xs ++ RefPtr b ptr::stack) refs ptr` by
   (full_simp_tac std_ss [reachable_refs_def] \\ qexists_tac `RefPtr b ptr`
    \\ full_simp_tac (srw_ss()) [get_refs_def])
  \\ res_tac \\ POP_ASSUM MP_TAC \\ simp_tac std_ss [Once bc_ref_inv_def]
  \\ Cases_on `lookup ptr refs` \\ full_simp_tac (srw_ss()) []
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
   (fs [gc_kind_inv_def] \\ every_case_tac \\ fs[]
    \\ conj_tac THEN1
     (match_mp_tac update_ref_gen_state_ok
      \\ asm_exists_tac \\ fs []
      \\ rpt_drule heap_lookup_heap_split
      \\ IF_CASES_TAC \\ fs [] \\ strip_tac
      \\ fs [EVERY_MEM] \\ res_tac
      \\ fs [EVAL ``isRef (RefBlock zs)``])
    \\ drule heap_split_heap_length \\ strip_tac \\ qpat_x_assum `_ ++ _ = _` (assume_tac o GSYM)
    \\ fs[] \\ fs[heap_lookup_APPEND] \\ every_case_tac \\ fs[] \\ rfs[]
    \\ qpat_x_assum `heap_lookup _ _ = SOME (RefBlock zs)` assume_tac
    \\ drule heap_lookup_SPLIT \\ strip_tac \\ fs[] \\ rveq \\ fs[]
    THEN1 fs[RefBlock_def,isRef_def]
    \\ qpat_x_assum `heap_store _ _ _ = _` mp_tac
    \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,heap_store_lemma] \\ disch_then (assume_tac o GSYM)
    \\ fs[]
    \\ `f ' ptr = heap_length(h1 ++ ha)` by fs[heap_length_APPEND]
    \\ fs[heap_store_lemma]
    \\ qpat_x_assum `heap_length h1 = _` (assume_tac o GSYM)
    \\ fs[]
    \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,gen_gc_partialTheory.heap_split_length]
    \\ fs[isRef_def,RefBlock_def])
  \\ strip_tac THEN1
   (full_simp_tac std_ss [unused_space_inv_def] \\ rpt strip_tac
    \\ res_tac \\ Cases_on `a = f ' ptr` \\ full_simp_tac (srw_ss()) []
    THEN1 full_simp_tac (srw_ss()) [RefBlock_def]
    \\ full_simp_tac std_ss [RefBlock_inv_def]
    \\ res_tac \\ full_simp_tac (srw_ss()) [isRefBlock_def,RefBlock_def]
    \\ imp_res_tac data_up_to_heap_store \\ fs [])
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ qexists_tac `DRESTRICT tf (all_ts (insert ptr (ValueArray (LUPDATE (HD xs) i xs1)) refs) (xs ++ RefPtr b ptr::stack))`
  \\ full_simp_tac std_ss []
  \\ MP_TAC v_inv_Ref
  \\ full_simp_tac std_ss [] \\ rpt strip_tac
  THEN1 (fs [SUBSET_DEF])
  THEN1 (fs [INJ_DEF,DRESTRICT_DEF])
  THEN1 (fs [SUBSET_DEF,DRESTRICT_DEF])
  THEN1 (fs [SUBSET_DEF,DRESTRICT_DEF,SUBSET_DEF,IN_INTER])
  >- (match_mp_tac EVERY2_MEM_MONO
     \\ imp_res_tac LIST_REL_APPEND_IMP
     \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
     \\ simp[FORALL_PROD] \\ rw[]
     \\ ho_match_mp_tac v_inv_tf_restrict
     \\ rw []
     \\ ho_match_mp_tac MEM_in_all_ts
     \\ qexists_tac `p_1` \\ rw []
     \\ ho_match_mp_tac MEM_stack_all_vs
     \\ qmatch_asmsub_abbrev_tac `MEM (_,_) (ZIP (l,_))`
     \\ drule MEM_ZIP2 \\ rw []
     \\ rw [EL_MEM])
  \\ Cases_on `n = ptr` THEN1 (
    full_simp_tac (srw_ss()) [bc_ref_inv_def]
    \\ srw_tac [] [] \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,RefBlock_def]
    \\ qpat_x_assum `LIST_REL _ zs xs1` (mp_then (Pos (el 2)) mp_tac EVERY2_LUPDATE_same)
    \\ disch_then (qspecl_then [`HD t1`,`HD xs`,`i`] mp_tac)
    \\ impl_tac
    >- (Cases_on`t1`>>fs[])
    >- (rw [] \\ match_mp_tac EVERY2_MEM_MONO
       \\ imp_res_tac LIST_REL_APPEND_IMP
       \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
       \\ simp[FORALL_PROD] \\ rw[]
       \\ ho_match_mp_tac v_inv_tf_restrict
       \\ rw []
       \\ ho_match_mp_tac MEM_in_all_ts
       \\ qexists_tac `p_2` \\ rw []
       \\ rw [all_vs_def] \\ disj1_tac
       \\ map_every qexists_tac [`n`,`LUPDATE (HD xs) i xs1`]
       \\ rw [FLOOKUP_UPDATE,FLOOKUP_DEF]
       \\ ho_match_mp_tac MEM_v_all_vs
       \\ drule MEM_ZIP2 \\ rw []
       \\ rw [EL_MEM]))
  \\ `reachable_refs (xs ++ RefPtr b ptr::stack) refs n` by (
    match_mp_tac (GEN_ALL (MP_CANON reachable_refs_UPDATE1)) >>
    qexists_tac`LUPDATE (HD xs) i xs1` >> rw[] >>
    Cases_on`xs`>>fs[]>>
    imp_res_tac MEM_LUPDATE_E >> fs[]>>
    simp[FLOOKUP_DEF] ) >>
  full_simp_tac (srw_ss()) [bc_ref_inv_def]
  \\ res_tac
  \\ Cases_on `FLOOKUP f n` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `lookup n refs` \\ full_simp_tac (srw_ss()) []
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,FAPPLY_FUPDATE_THM] \\ rw [lookup_insert]
  \\ Cases_on `x'''` \\ full_simp_tac (srw_ss()) []
  >- (qexists_tac `zs'` \\ conj_tac
     >- (first_x_assum ho_match_mp_tac \\ rw [] \\ CCONTR_TAC \\ metis_tac [INJ_DEF])
     >- (match_mp_tac EVERY2_MEM_MONO
        \\ imp_res_tac LIST_REL_APPEND_IMP
        \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
        \\ simp[FORALL_PROD] \\ rw[]
        \\ ho_match_mp_tac v_inv_tf_restrict
        \\ rw []
        \\ ho_match_mp_tac MEM_in_all_ts
        \\ qexists_tac `p_2` \\ rw []
        \\ rw [all_vs_def] \\ disj1_tac
        \\ map_every qexists_tac [`n`,`l`]
        \\ rw [lookup_insert]
        \\ ho_match_mp_tac MEM_v_all_vs
        \\ drule MEM_ZIP2 \\ rw []
        \\ rw [EL_MEM]))
  \\ full_simp_tac (srw_ss()) [INJ_DEF] \\ metis_tac []
QED

(* update byte ref *)

Theorem LENGTH_write_bytes[simp]:
   !ws bs be. LENGTH (write_bytes bs ws be) = LENGTH ws
Proof
  Induct \\ fs [write_bytes_def]
QED

Triviality LIST_REL_IMP_LIST_REL:
  !xs ys.
      (!x y. MEM x xs ==> P x y ==> Q x y) ==>
      LIST_REL P xs ys ==> LIST_REL Q xs ys
Proof
  Induct \\ fs [PULL_EXISTS]
QED

Triviality v_size_LESS_EQ:
  !l x. MEM x l ==> v_size x <= list_size v_size l
Proof
  rw [] \\ imp_res_tac MEM_list_size
  \\ pop_assum $ qspec_then ‘v_size’ mp_tac \\ gvs []
QED

Triviality v_inv_IMP:
  ∀y x f tf ha.
      v_inv conf y (x,f,tf,ha ++ [Bytes be fl xs ws] ++ hb) ⇒
      v_inv conf y (x,f,tf,ha ++ [Bytes be fl ys ws] ++ hb)
Proof
  completeInduct_on `v_size y` \\ rw [] \\ fs [PULL_FORALL]
  \\ Cases_on `y` \\ fs [v_inv_def] \\ rw [] \\ fs []
  THEN1
   (fs[heap_lookup_APPEND,heap_length_APPEND,Bytes_def,heap_length_def,el_length_def]
    \\ rw[] \\ fs[] \\ fs[heap_lookup_def,Bignum_def,i2mw_def])
  >- (
    fs[heap_lookup_APPEND,heap_length_APPEND,Bytes_def,heap_length_def,el_length_def]
    \\ rw[] \\ fs[]
    \\ fs[heap_lookup_def]
    \\ fs[Word64Rep_def]
    \\ IF_CASES_TAC \\ fs[] )
  \\ qexists_tac `xs'` \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ conj_tac THEN1
   (qpat_x_assum `LIST_REL _ _ _` mp_tac
    \\ match_mp_tac LIST_REL_IMP_LIST_REL \\ fs []
    \\ rpt strip_tac \\ first_x_assum match_mp_tac \\ fs []
    \\ fs [v_size_def] \\ imp_res_tac v_size_LESS_EQ \\ fs [])
  \\ fs [Bytes_def,heap_lookup_APPEND,heap_lookup_def,BlockRep_def,
         heap_length_APPEND,heap_length_def,SUM_APPEND,el_length_def]
  \\ rw [] \\ fs []
QED

val gen_state_ok_update_byte = prove(
  ``gen_state_ok a k (ha ++ [Bytes be fl xs ws] ++ hb) gens ==>
    gen_state_ok a k (ha ++ [Bytes be fl ys ws] ++ hb) gens``,
  Cases_on `gens` \\ fs [gen_state_ok_def,EVERY_MEM] \\ rw []
  \\ res_tac \\ fs [gen_start_ok_def]
  \\ rpt (qpat_x_assum `!e. _ ==> _` kall_tac)
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
  \\ full_simp_tac std_ss [heap_split_APPEND_if]
  \\ IF_CASES_TAC \\ fs []
  THEN1 (every_case_tac \\ fs [] \\ rpt strip_tac \\ res_tac \\ fs [])
  \\ fs [LENGTH_write_bytes,EVAL ``heap_length [Bytes be fl ys ws]``]
  \\ IF_CASES_TAC \\ fs []
  \\ fs[Bytes_def,heap_split_def,el_length_def]
  \\ TRY IF_CASES_TAC \\ fs [] \\ rveq
  \\ rpt strip_tac \\ res_tac \\ fs []
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs [] \\ rveq
  \\ rpt strip_tac
  \\ rveq \\ fs []
  \\ metis_tac [MEM_APPEND]);

Theorem heap_length_Bytes =
  EVAL``heap_length [Bytes be fl bs ws]``
  |> SIMP_RULE std_ss [LENGTH_write_bytes]

val unused_space_inv_byte_update = prove(
  ``unused_space_inv a (sp + sp1)
        (ha ++ [Bytes be fl xs (REPLICATE ws 0w)] ++ hb) ==>
    unused_space_inv a (sp + sp1)
        (ha ++ [Bytes be fl ys (REPLICATE ws 0w)] ++ hb)``,
  fs [unused_space_inv_def] \\ rw [] \\ fs []
  \\ fs [heap_lookup_APPEND,heap_length_APPEND,heap_length_Bytes]
  THEN1 (every_case_tac \\ fs [heap_lookup_def,Bytes_def])
  THEN1 (every_case_tac \\ fs [heap_lookup_def,Bytes_def])
  \\ pop_assum mp_tac \\ rpt (pop_assum kall_tac)
  \\ qspec_tac (`a`,`a`) \\ Induct_on `ha`
  \\ fs [data_up_to_alt,el_length_def,Bytes_def]
  \\ rpt gen_tac \\ Cases_on `a = 0` \\ fs []);

Theorem update_byte_ref_thm:
   abs_ml_inv conf ((RefPtr b ptr)::stack) refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
    (lookup ptr refs = SOME (ByteArray fl xs)) /\ (LENGTH xs = LENGTH ys) ==>
    ?roots2 h1 h2 ws.
      (roots = Pointer (heap_length h1) ((Word 0w):'a word_loc) :: roots2) /\
      heap = h1 ++ [Bytes be fl xs ws] ++ h2 /\
      LENGTH ws = LENGTH xs DIV (dimindex (:α) DIV 8) + 1 /\
      abs_ml_inv conf ((RefPtr b ptr)::stack) (insert ptr (ByteArray fl ys) refs)
        (roots,h1 ++ [Bytes be fl ys ws] ++ h2,be,a,sp,sp1,gens) limit ts
Proof
  simp_tac std_ss [abs_ml_inv_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [bc_stack_ref_inv_def]
  \\ Cases_on `roots` \\ fs [v_inv_def] \\ rpt var_eq_tac \\ fs []
  \\ `reachable_refs (RefPtr b ptr::stack) refs ptr` by
   (full_simp_tac std_ss [reachable_refs_def] \\ qexists_tac `RefPtr b ptr`
    \\ full_simp_tac (srw_ss()) [get_refs_def] \\ NO_TAC)
  \\ res_tac \\ fs []
  \\ pop_assum mp_tac \\ simp_tac std_ss [Once bc_ref_inv_def]
  \\ fs [FLOOKUP_DEF] \\ rw []
  \\ drule heap_lookup_SPLIT \\ rw [] \\ fs []
  \\ qpat_abbrev_tac `ws = LENGTH _ DIV _ + 1`
  \\ qexists_tac `ha` \\ fs []
  \\ qexists_tac `REPLICATE ws 0w` \\ fs [PULL_EXISTS]
  \\ qexists_tac `f` \\ fs []
  \\ qexists_tac `DRESTRICT tf (all_ts (insert ptr (ByteArray fl ys) refs) (RefPtr b ptr::stack))`
  \\ `!a. isSomeDataElement (heap_lookup a (ha ++ [Bytes be fl ys (REPLICATE ws 0w)] ++ hb)) =
          isSomeDataElement (heap_lookup a (ha ++ [Bytes be fl xs (REPLICATE ws 0w)] ++ hb))` by
   (rw [] \\ fs [isSomeDataElement_def] \\ rw []
    \\ fs [heap_lookup_APPEND] \\ rw [] \\ rw [] \\ fs []
    \\ fs [heap_length_def,Bytes_def,el_length_def,heap_lookup_def])
  \\ `ptr INSERT (domain refs) = domain refs`
     by (fs [EXTENSION,SUBSET_DEF] \\ metis_tac [])
  \\ fs [] \\ rpt strip_tac
  THEN1 (fs [roots_ok_def] \\ rw [] \\ fs [] \\ metis_tac [])
  THEN1
   (fs [heap_ok_def]
    \\ fs [heap_length_def,Bytes_def,el_length_def,heap_lookup_def,
           FILTER_APPEND,FILTER,isForwardPointer_def]
    \\ rfs [] \\ fs [] \\ rpt strip_tac
    \\ first_x_assum match_mp_tac \\ metis_tac [])
  THEN1
   (fs [gc_kind_inv_def] \\ every_case_tac \\ fs[]
    \\ conj_tac THEN1 (imp_res_tac gen_state_ok_update_byte \\ fs [])
    \\ fs[Once heap_split_APPEND_if]
    \\ fs[heap_length_APPEND,heap_length_def,Bytes_def,el_length_def]
    \\ IF_CASES_TAC \\ fs[] \\ TOP_CASE_TAC \\ fs[]
    \\ every_case_tac \\ fs[]
    >- (fs[Once heap_split_APPEND_if]
        \\ fs[heap_length_APPEND,heap_length_def,Bytes_def,el_length_def]
        \\ pop_assum mp_tac \\ IF_CASES_TAC \\ fs[] \\ TOP_CASE_TAC \\ fs[] \\ TOP_CASE_TAC
        \\ fs[] \\ fs[heap_split_def,el_length_def]
        \\ Cases_on `a + (sp + sp1) ≤ SUM (MAP el_length ha)`
        \\ fs[el_length_def])
    >- (rveq \\ fs[]
        \\ pop_assum mp_tac
        \\ fs[Once heap_split_APPEND_if]
        \\ IF_CASES_TAC \\ fs[] \\ TOP_CASE_TAC \\ fs[] \\ TOP_CASE_TAC \\ fs[]
        \\ disch_then (assume_tac o GSYM)
        >- (qpat_x_assum `_ = r` (assume_tac o GSYM) \\ fs[isRef_def])
        \\ fs[] \\ rveq \\ fs[] \\ every_case_tac \\ fs[]
        \\ rveq \\ fs[] \\ fs[heap_split_def] \\ rfs[]
        \\ every_case_tac \\ fs[]
        \\ qpat_x_assum `_ = r` (assume_tac o GSYM) \\ fs[isRef_def]
        \\ qpat_x_assum `_ = r'` (assume_tac o GSYM) \\ fs[isRef_def]
        \\ qpat_x_assum `_ = q'` (assume_tac o GSYM) \\ fs[isRef_def]
        \\ rveq \\ fs[isRef_def])
    >- (rveq \\ fs[isRef_def]))
  THEN1 (imp_res_tac unused_space_inv_byte_update \\ fs [])
  THEN1 (fs [INJ_DEF,DRESTRICT_DEF])
  THEN1 (fs [SUBSET_DEF,DRESTRICT_DEF])
  THEN1 (fs [SUBSET_DEF,DRESTRICT_DEF,SUBSET_DEF,IN_INTER])
  THEN1
   (match_mp_tac EVERY2_MEM_MONO
    \\ imp_res_tac LIST_REL_APPEND_IMP
    \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
    \\ simp[FORALL_PROD] \\ rw[]
    \\ ho_match_mp_tac v_inv_tf_restrict
    \\ conj_tac
    >- metis_tac [v_inv_IMP]
    \\ rw []
    \\ ho_match_mp_tac MEM_in_all_ts
    \\ qexists_tac `p_1` \\ rw []
    \\ rw [all_vs_def] \\ disj2_tac
    \\ ho_match_mp_tac MEM_v_all_vs
    \\ drule MEM_ZIP2 \\ rw []
    \\ rw [EL_MEM])
  \\ `reachable_refs (RefPtr b ptr::stack) refs n` by
   (pop_assum mp_tac
    \\ sg `ref_edge (insert ptr (ByteArray fl ys) refs) = ref_edge refs`
    \\ simp [reachable_refs_def]
    \\ fs [ref_edge_def,FUN_EQ_THM,lookup_insert]
    \\ rw [] \\ fs [lookup_def])
  \\ Cases_on `n = ptr` \\ fs [] THEN1
   (fs [] \\ rw [bc_ref_inv_def,FLOOKUP_DEF]
    \\ fs [heap_lookup_APPEND,heap_length_APPEND,Bytes_def,
           heap_length_def,el_length_def,heap_lookup_def]
    \\ metis_tac[])
  \\ first_x_assum drule
  \\ fs [bc_ref_inv_def]
  \\ strip_tac \\ CASE_TAC \\ fs []
  \\ fs [FLOOKUP_UPDATE,lookup_insert] \\ rfs [] \\ fs []
  \\ CASE_TAC \\ fs [] \\ CASE_TAC \\ fs []
  THEN1
   (once_rewrite_tac [CONJ_COMM] \\ qexists_tac `zs` \\ fs []
    \\ conj_tac
    THEN1 (match_mp_tac EVERY2_MEM_MONO
    \\ imp_res_tac LIST_REL_APPEND_IMP
    \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
    \\ simp[FORALL_PROD] \\ rw[]
    \\ ho_match_mp_tac v_inv_tf_restrict
    \\ conj_tac
    >- metis_tac [v_inv_IMP]
    \\ rw []
    \\ ho_match_mp_tac MEM_in_all_ts
    \\ qexists_tac `p_2` \\ rw []
    \\ rw [all_vs_def] \\ disj1_tac
    \\ map_every qexists_tac [`n`,`l`]
    \\ rw [lookup_insert]
    \\ ho_match_mp_tac MEM_v_all_vs
    \\ drule MEM_ZIP2 \\ rw []
    \\ rw [EL_MEM])
    \\ fs [heap_lookup_def,heap_lookup_APPEND,Bytes_def,
           el_length_def,SUM_APPEND,RefBlock_def,heap_length_APPEND]
    \\ rw [] \\ fs [] \\ rfs [heap_length_def,el_length_def] \\ fs [NOT_LESS])
  \\ Cases_on `x = heap_length ha`
  THEN1 (fs [INJ_DEF,FLOOKUP_DEF] \\ metis_tac [])
  \\ fs [heap_lookup_APPEND,Bytes_def,heap_length_def,el_length_def,SUM_APPEND]
  \\ rfs [] \\ rw [] \\ fs [] \\ rfs [heap_lookup_def]
  \\ metis_tac[]
QED

val heap_store_unused_thm = prove(
  ``!a n heap h1 h2 heap2 x.
      heap_split (a + n) heap = SOME (h1,h2) /\
      heap_store_unused a n x heap = (heap2,T) /\
      unused_space_inv a (n − el_length x) heap2 ==>
      ?h0. h1 = h0 ++ [Unused (n-1)] /\
           heap = h1 ++ h2 /\ heap_length h0 = a /\
           heap2 = h0 ++ heap_expand (n − el_length x) ++ [x] ++ h2``,
  fs [heap_store_unused_def] \\ rw []
  \\ fs [unused_space_inv_def]
  \\ imp_res_tac gc_sharedTheory.heap_split_heap_length
  \\ fs [] \\ rveq \\ fs []
  \\ fs [heap_lookup_APPEND]
  \\ `0 < n` by (Cases_on `x` \\ fs [el_length_def])
  \\ fs [] \\ drule heap_lookup_SPLIT
  \\ strip_tac \\ rveq \\ fs []
  \\ `hb = []` by
   (fs [heap_length_APPEND]
    \\ fs [heap_length_def,el_length_def]
    \\ Cases_on `hb` \\ fs [])
  \\ rveq \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [heap_store_lemma]);

Theorem heap_store_unused_heap_lookup:
   !heap heap2 a k x n.
      heap_store_unused a k x heap = (heap2,T) /\ n < a ==>
      heap_lookup n heap = heap_lookup n heap2
Proof
  Induct THEN1 fs [heap_lookup_def,heap_store_unused_def]
  \\ simp [heap_store_unused_def]
  \\ rpt strip_tac \\ every_case_tac \\ fs []
  \\ ntac 4 (pop_assum mp_tac)
  \\ once_rewrite_tac [heap_store_def]
  \\ IF_CASES_TAC \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ rveq
  \\ once_rewrite_tac [heap_lookup_def] \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ rpt strip_tac
  \\ first_x_assum match_mp_tac
  \\ fs [heap_store_unused_def]
  \\ qexists_tac `(a − el_length h)` \\ fs [] \\ metis_tac []
QED

val heap_store_unused_gen_state_ok = prove(
  ``heap_store_unused a k x heap = (heap2,T) /\
    gen_state_ok a (a + k) heap gens ==>
    gen_state_ok a (a + k - el_length x) heap2 gens``,
  Cases_on `gens` \\ fs [gen_state_ok_def]
  \\ fs [EVERY_MEM] \\ rw [] \\ res_tac \\ fs []
  \\ fs [gen_start_ok_def]
  \\ rw [] \\ CCONTR_TAC \\ fs []
  \\ fs [GSYM NOT_LESS] \\ fs [NOT_LESS]
  \\ fs [heap_store_unused_def]
  \\ every_case_tac \\ fs []
  \\ fs [GSYM IMP_DISJ_THM]
  \\ imp_res_tac heap_split_heap_store \\ fs []
  \\ rveq \\ fs [] \\ res_tac \\ fs []);

(* new ref *)

Theorem new_ref_thm:
   abs_ml_inv conf (xs ++ stack) refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
    ~(ptr IN (domain refs)) /\ LENGTH xs + 1 <= sp ==>
    ?p rs roots2 heap2.
      (roots = rs ++ roots2) /\ LENGTH rs = LENGTH xs /\
      (heap_store_unused a (sp+sp1) (RefBlock rs) heap = (heap2,T)) /\
      abs_ml_inv conf (xs ++ (RefPtr T ptr)::stack) (insert ptr (ValueArray xs) refs)
                 (rs ++ Pointer (a+sp+sp1-(LENGTH xs + 1)) (Word 0w)::roots2,heap2,be,a,
                  sp - (LENGTH xs + 1),sp1,gens) limit ts
Proof
  simp_tac std_ss [abs_ml_inv_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [bc_stack_ref_inv_def]
  \\ imp_res_tac EVERY2_APPEND_IMP_APPEND
  \\ full_simp_tac (srw_ss()) []
  \\ Q.LIST_EXISTS_TAC [`ys1`,`ys2`] \\ full_simp_tac std_ss []
  \\ imp_res_tac EVERY2_IMP_LENGTH
  \\ `el_length (RefBlock ys1) <= sp + sp1` by (full_simp_tac std_ss [el_length_def,RefBlock_def] \\ fs [])
  \\ qpat_x_assum `unused_space_inv a (sp+sp1) heap` (fn th =>
    MATCH_MP (IMP_heap_store_unused
    |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> GEN_ALL) th
    |> ASSUME_TAC)
  \\ POP_ASSUM (MP_TAC o Q.SPEC `RefBlock ys1`) \\ match_mp_tac IMP_IMP
  \\ strip_tac THEN1 full_simp_tac std_ss [RefBlock_def,el_length_def]
  \\ strip_tac \\ full_simp_tac std_ss []
  \\ `unused_space_inv a (sp + sp1 - (LENGTH ys1 + 1)) heap2` by fs [RefBlock_def,el_length_def]
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
  \\ conj_tac THEN1
   (fs [gc_kind_inv_def] \\ Cases_on `conf.gc_kind` \\ fs []
    \\ conj_tac THEN1
     (drule heap_store_unused_gen_state_ok
      \\ fs [EVAL ``el_length (RefBlock ys1)``])
    \\ drule (GEN_ALL heap_store_unused_thm)
    \\ disch_then drule \\ fs []
    \\ strip_tac \\ fs [] \\ rveq \\ fs []
    \\ fs [EVAL ``el_length (RefBlock ys1)``]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ once_rewrite_tac [heap_split_APPEND_if] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ once_rewrite_tac [heap_split_APPEND_if]
    \\ fs [heap_length_heap_expand]
    \\ fs [heap_split_def]
    \\ EVAL_TAC \\ rw [] \\ EVAL_TAC)
  \\ `~(ptr IN FDOM f)` by (full_simp_tac (srw_ss()) [SUBSET_DEF] \\ metis_tac [])
  \\ conj_tac THEN1 fs []
  \\ qexists_tac `f |+ (ptr,a+sp+sp1-(LENGTH ys1 + 1))`
  \\ qexists_tac `DRESTRICT tf (all_ts (insert ptr (ValueArray xs) refs) (xs ++ RefPtr T ptr::stack))`
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [FDOM_FUPDATE]
    \\ `(FAPPLY (f |+ (ptr,a + sp + sp1 - (LENGTH ys1 + 1)))) =
          (ptr =+ (a+sp+sp1-(LENGTH ys1 + 1))) (FAPPLY f)` by
     (full_simp_tac std_ss [FUN_EQ_THM,FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM]
      \\ metis_tac []) \\ full_simp_tac std_ss []
    \\ match_mp_tac (METIS_PROVE [] ``!y. (x = y) /\ f y ==> f x``)
    \\ qexists_tac `(a + sp + sp1 - (LENGTH ys1 + 1)) INSERT
         {a | isSomeDataElement (heap_lookup a heap)}`
    \\ strip_tac
    THEN1 (fs [RefBlock_def,isDataElement_def,el_length_def])
    \\ match_mp_tac INJ_UPDATE \\ full_simp_tac std_ss []
    \\ full_simp_tac (srw_ss()) []
    \\ full_simp_tac std_ss [RefBlock_def,el_length_def] \\ fs [])
  \\ strip_tac THEN1
     (full_simp_tac (srw_ss()) [SUBSET_DEF,FDOM_FUPDATE] \\ metis_tac [])
  \\ strip_tac
  THEN1 (fs [INJ_DEF,DRESTRICT_DEF,heap_store_rel_def])
  \\ strip_tac
  THEN1 (fs [DRESTRICT_DEF,SUBSET_DEF])
  \\ strip_tac
  THEN1 (fs [DRESTRICT_DEF,SUBSET_DEF,IN_INTER])
  \\ Q.ABBREV_TAC `f1 = f |+ (ptr,a + sp + sp1 - (LENGTH ys1 + 1))`
  \\ `f SUBMAP f1` by
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
    \\ conj_tac
    >- (rw []
       \\ ho_match_mp_tac v_inv_tf_restrict
       \\ rw []
       >- (ho_match_mp_tac v_inv_SUBMAP \\ rw [])
       \\ ho_match_mp_tac MEM_in_all_ts
       \\ qexists_tac `EL n xs` \\ rw []
       \\ rw [all_vs_def] \\ disj2_tac
       \\ ho_match_mp_tac MEM_v_all_vs
       \\ rw [MEM_APPEND,EL_MEM])
   >- (rw []
       \\ ho_match_mp_tac v_inv_tf_restrict
       \\ rw []
       >- (ho_match_mp_tac v_inv_SUBMAP \\ rw [])
       \\ ho_match_mp_tac MEM_in_all_ts
       \\ qexists_tac `EL n stack` \\ rw []
       \\ rw [all_vs_def] \\ disj2_tac
       \\ ho_match_mp_tac MEM_v_all_vs
       \\ rw [MEM_APPEND,EL_MEM]))
  \\ rpt strip_tac
  \\ Cases_on `n = ptr` THEN1
   (Q.UNABBREV_TAC `f1` \\ asm_simp_tac (srw_ss()) [bc_ref_inv_def,FDOM_FUPDATE,
      FAPPLY_FUPDATE_THM] \\ fs [el_length_def,RefBlock_def]
    \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,EVERY2_EQ_EL]
    \\ rpt strip_tac
    \\ ho_match_mp_tac v_inv_tf_restrict
    \\ conj_tac
    >- (match_mp_tac v_inv_SUBMAP \\ full_simp_tac (srw_ss()) [])
    \\ rw []
    \\ ho_match_mp_tac MEM_in_all_ts
    \\ qexists_tac `EL n' xs` \\ rw []
    \\ rw [all_vs_def] \\ disj2_tac
    \\ ho_match_mp_tac MEM_v_all_vs
    \\ rw [MEM_APPEND,EL_MEM])
  \\ `reachable_refs (xs ++ RefPtr T ptr::stack) refs n` by imp_res_tac reachable_refs_UPDATE
  \\ qpat_x_assum `reachable_refs (xs ++ RefPtr T ptr::stack)
        (insert ptr x refs) n` (K ALL_TAC)
  \\ `reachable_refs (xs ++ stack) refs n` by
    (full_simp_tac std_ss [reachable_refs_def]
     \\ reverse (Cases_on `x = RefPtr T ptr`)
     THEN1 (full_simp_tac std_ss [MEM,MEM_APPEND] \\ metis_tac [])
     \\ full_simp_tac std_ss [get_refs_def,MEM]
     \\ srw_tac [] []
     \\ imp_res_tac RTC_NRC
     \\ Cases_on `n'` \\ full_simp_tac std_ss [NRC]
     \\ full_simp_tac std_ss [ref_edge_def,lookup_def]
     \\ every_case_tac \\ rev_full_simp_tac std_ss [GSYM lookup_NONE_domain])
  \\ res_tac \\ Q.UNABBREV_TAC `f1` \\ full_simp_tac std_ss [bc_ref_inv_def]
  \\ Cases_on `FLOOKUP f n` \\ full_simp_tac (srw_ss()) []
  \\ Cases_on `lookup n refs` \\ full_simp_tac (srw_ss()) []
  \\ full_simp_tac (srw_ss()) [FDOM_FUPDATE,FAPPLY_FUPDATE_THM,FLOOKUP_DEF,lookup_insert]
  \\ reverse (Cases_on `x'`) \\ full_simp_tac (srw_ss()) []
  THEN1 (imp_res_tac heap_store_rel_lemma \\ fs [Bytes_def] \\ metis_tac[])
  \\ `isSomeDataElement (heap_lookup (f ' n) heap)` by
    (full_simp_tac std_ss [RefBlock_def] \\ EVAL_TAC
     \\ simp_tac (srw_ss()) [] \\ NO_TAC)
  \\ res_tac \\ full_simp_tac std_ss [] \\ simp_tac (srw_ss()) [RefBlock_def]
  \\ qpat_x_assum `n IN FDOM f` ASSUME_TAC
  \\ `n IN (domain refs)` by fs [domain_lookup]
  \\ qpat_x_assum `lookup n refs  = SOME (ValueArray l)` ASSUME_TAC
  \\ full_simp_tac (srw_ss()) []
  \\ srw_tac [] [] \\ full_simp_tac std_ss [RefBlock_def]
  \\ imp_res_tac heap_store_rel_lemma
  \\ res_tac \\ full_simp_tac (srw_ss()) []
  \\ qpat_x_assum `EVERY2 PPP zs l` MP_TAC
  \\ match_mp_tac EVERY2_IMP_EVERY2
  \\ full_simp_tac std_ss [] \\ simp_tac (srw_ss()) []
  \\ rpt strip_tac
  \\ ho_match_mp_tac v_inv_tf_restrict
  \\ conj_tac
  >- (match_mp_tac v_inv_SUBMAP
     \\ full_simp_tac (srw_ss()) [])
  \\ rw []
  \\ ho_match_mp_tac MEM_in_all_ts
  \\ qexists_tac `y` \\ rw []
  \\ rw [all_vs_def] \\ disj1_tac
  \\ map_every qexists_tac [`n`,`l`]
  \\ fs [lookup_insert]
  \\ ho_match_mp_tac MEM_v_all_vs
  \\ rw []
QED

(* deref *)

Definition heap_el_def:
  (heap_el (Pointer a u) n heap =
    case heap_lookup a heap of
    | SOME (DataElement xs l d) =>
        if n < LENGTH xs then (EL n xs,T) else (ARB,F)
    | _ => (ARB,F)) /\
  (heap_el _ _ _ = (ARB,F))
End

Theorem deref_thm:
   abs_ml_inv conf (RefPtr b ptr::stack) refs (roots,heap,be,a,sp,sp1,gens) limit ts ==>
    ?r roots2.
      (roots = r::roots2) /\ ptr IN (domain refs) /\
      case THE (lookup ptr refs) of
      | ByteArray _ _ => T
      | ValueArray vs =>
      !n. n < LENGTH vs ==>
          ?y. (heap_el r n heap = (y,T)) /\
                abs_ml_inv conf (EL n vs::RefPtr b ptr::stack) refs
                  (y::roots,heap,be,a,sp,sp1,gens) limit ts
Proof
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
  \\ rpt strip_tac \\ Cases_on `roots` \\ full_simp_tac (srw_ss()) [LIST_REL_def]
  \\ full_simp_tac std_ss [v_inv_def]
  \\ `reachable_refs (RefPtr b ptr::stack) refs ptr` by
   (full_simp_tac std_ss [reachable_refs_def,MEM] \\ qexists_tac `RefPtr b ptr`
    \\ asm_simp_tac (srw_ss()) [get_refs_def])
  \\ res_tac \\ POP_ASSUM MP_TAC
  \\ simp_tac std_ss [Once bc_ref_inv_def]
  \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF]
  \\ `ptr IN (domain refs)` by fs [SUBSET_DEF]
  \\ full_simp_tac (srw_ss()) [domain_lookup]
  \\ reverse (Cases_on `v`) \\ full_simp_tac (srw_ss()) []
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
  \\ qexists_tac `tf` \\ full_simp_tac std_ss []
  \\ conj_tac
  >- (`all_ts refs (RefPtr b ptr::stack) = all_ts refs (EL n l::RefPtr b ptr::stack)`
      suffices_by metis_tac []
      \\ rw [FUN_EQ_THM,all_ts_def]
      \\ EQ_TAC
      >- metis_tac []
      \\ rw []
      >- metis_tac []
      >- (qexists_tac `EL n l` \\ rw [] \\ disj1_tac
         \\ metis_tac [EL_MEM,FRANGE_FLOOKUP,FLOOKUP_DEF])
      \\  metis_tac [])
  \\ imp_res_tac EVERY2_IMP_EL
  \\ full_simp_tac std_ss []
  \\ rpt strip_tac
  \\ FIRST_X_ASSUM match_mp_tac
  \\ qpat_x_assum `reachable_refs (RefPtr b ptr::stack) refs ptr` (K ALL_TAC)
  \\ full_simp_tac std_ss [reachable_refs_def]
  \\ reverse (Cases_on `x = EL n l`)
  THEN1 (full_simp_tac std_ss [MEM] \\ metis_tac [])
  \\ qexists_tac `RefPtr b ptr` \\ simp_tac std_ss [MEM,get_refs_def]
  \\ once_rewrite_tac [RTC_CASES1] \\ DISJ2_TAC
  \\ qexists_tac `r` \\ full_simp_tac std_ss []
  \\ full_simp_tac (srw_ss()) [ref_edge_def,FLOOKUP_DEF,get_refs_def]
  \\ full_simp_tac (srw_ss()) [MEM_FLAT,MEM_MAP,PULL_EXISTS]
  \\ qexists_tac `(EL n l)` \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [MEM_EL] \\ metis_tac []
QED

(* el *)

Theorem el_thm:
   abs_ml_inv conf (Block t0 n xs::stack) refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
    i < LENGTH xs ==>
    ?r roots2 y.
      (roots = r :: roots2) /\ (heap_el r i heap = (y,T)) /\
      abs_ml_inv conf (EL i xs::Block t0 n xs::stack) refs
                      (y::roots,heap,be,a,sp,sp1,gens) limit ts
Proof
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
    \\ sg `?u'. MEM (Pointer ptr' u') xs'` \\ res_tac
    \\ full_simp_tac std_ss [MEM_EL] \\ metis_tac [])
  \\ qexists_tac `f`  \\ full_simp_tac std_ss []
  \\ qexists_tac `tf` \\ full_simp_tac std_ss []
  \\ conj_tac
  THEN1 (
    `∀x y. FDOM tf ⊆ y ∧ x = y ⇒ FDOM tf ⊆ x` by metis_tac []
    \\ qpat_x_assum `FDOM tf ⊆ _` kall_tac
    \\ pop_assum drule
    \\ disch_then ho_match_mp_tac
    \\ rw [FUN_EQ_THM,all_ts_def]
    \\ EQ_TAC
    >- (rw []
       >- metis_tac []
       >- (qexists_tac `Block t0 n xs` \\ rw [v_all_ts_def]
          \\ disj2_tac \\ rw [ETA_THM]
          \\ ho_match_mp_tac v_all_vs_ts_list
          \\ qexists_tac `EL i xs` \\ rw []
          \\ ho_match_mp_tac MEM_v_all_vs
          \\ rw [EL_MEM])
       \\ metis_tac [])
    \\ metis_tac [])
  \\ strip_tac THEN1 (full_simp_tac std_ss [EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS])
  \\ rpt strip_tac
  \\ qpat_x_assum `!xx.bbb` match_mp_tac
  \\ full_simp_tac std_ss [reachable_refs_def]
  \\ reverse (Cases_on `x = EL i xs`)
  THEN1 (full_simp_tac std_ss [MEM] \\ metis_tac [])
  \\ Q.LIST_EXISTS_TAC [`Block t0 n xs`,`r`]
  \\ asm_simp_tac std_ss [MEM]
  \\ full_simp_tac std_ss [get_refs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]
  \\ qexists_tac `EL i xs` \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [MEM_EL] \\ qexists_tac `i`
  \\ full_simp_tac std_ss []
QED

(* new byte array *)

Theorem new_byte_alt_thm:
    abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
    Abbrev (ws = LENGTH bs DIV (dimindex (:α) DIV 8) + 1) /\
    ~(ptr IN (domain refs)) /\ ws + 1 <= sp ==>
    ?heap2.
      (heap_store_unused_alt a (sp+sp1)
        (Bytes be fl bs (REPLICATE ws (0w:'a word))) heap = (heap2,T)) /\
      abs_ml_inv conf ((RefPtr b ptr)::stack) (insert ptr (ByteArray fl bs) refs)
                 (Pointer a (Word 0w)::roots,heap2,be,a + ws + 1,
                  sp - (ws + 1),sp1,gens) limit ts
Proof
  simp_tac std_ss [abs_ml_inv_def]
  \\ rpt strip_tac \\ full_simp_tac std_ss [bc_stack_ref_inv_def]
  \\ imp_res_tac EVERY2_APPEND_IMP_APPEND
  \\ full_simp_tac (srw_ss()) []
  \\ `el_length (Bytes be fl bs (REPLICATE ws 0w)) <= sp + sp1` by (fs [el_length_def,Bytes_def])
  \\ qpat_x_assum `unused_space_inv a (sp+sp1) heap` (fn th =>
    MATCH_MP (IMP_heap_store_unused_alt
    |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> GEN_ALL) th
    |> ASSUME_TAC)
  \\ pop_assum drule \\ strip_tac \\ fs []
  \\ full_simp_tac std_ss [] \\ strip_tac
  THEN1
   (fs [roots_ok_def] \\ fs [MEM,heap_store_rel_def,Bytes_def]
    \\ full_simp_tac (srw_ss()) [Bytes_def,el_length_def]
    \\ full_simp_tac (srw_ss()) [isSomeDataElement_def]
    \\ fs [] \\ metis_tac [])
  \\ strip_tac THEN1
   (fs [heap_ok_def,Bytes_def,isForwardPointer_def] \\ rveq \\ rw []
    \\ res_tac \\ full_simp_tac std_ss [heap_store_rel_def]
    \\ POP_ASSUM MP_TAC \\ full_simp_tac (srw_ss()) [])
  \\ conj_tac THEN1
   (fs [gc_kind_inv_def] \\ Cases_on `conf.gc_kind` \\ fs []
    \\ drule (GEN_ALL heap_store_unused_alt_gen_state_ok)
    \\ disch_then drule
    \\ drule (GEN_ALL heap_store_unused_alt_thm)
    \\ disch_then drule \\ fs []
    \\ fs [EVAL ``el_length (Bytes be fl bs (REPLICATE ws 0w))``,
           LENGTH_write_bytes]
    \\ strip_tac \\ fs [] \\ rveq \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ once_rewrite_tac [heap_split_APPEND_if] \\ fs []
    \\ fs [heap_split_def]
    \\ fs [EVAL ``el_length (Bytes be fl bs (REPLICATE ws 0w))``,
           LENGTH_write_bytes]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ once_rewrite_tac [heap_split_APPEND_if]
    \\ fs [heap_length_heap_expand]
    \\ `heap_split 0 h2 = SOME ([],h2)` by (Cases_on `h2` \\ fs [heap_split_def])
    \\ fs [heap_split_def]
    \\ EVAL_TAC \\ rw [] \\ EVAL_TAC)
  \\ `unused_space_inv (a + ws + 1) (sp + sp1 - (ws + 1)) heap2` by fs [Bytes_def,el_length_def] \\ fs []
  \\ `~(ptr IN FDOM f)` by (full_simp_tac (srw_ss()) [SUBSET_DEF] \\ metis_tac [])
  \\ qexists_tac `f |+ (ptr,a)`
  \\ qexists_tac `tf`
  \\ strip_tac THEN1
   (full_simp_tac (srw_ss()) [FDOM_FUPDATE]
    \\ `(FAPPLY (f |+ (ptr,a))) =
          (ptr =+ a) (FAPPLY f)` by
     (full_simp_tac std_ss [FUN_EQ_THM,FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM]
      \\ metis_tac []) \\ full_simp_tac std_ss []
    \\ match_mp_tac (METIS_PROVE [] ``!y. (x = y) /\ f y ==> f x``)
    \\ qexists_tac `a INSERT
         {a | isSomeDataElement (heap_lookup a heap)}`
    \\ strip_tac
    THEN1 (fs [Bytes_def,LET_DEF,isDataElement_def,el_length_def])
    \\ match_mp_tac INJ_UPDATE \\ full_simp_tac std_ss []
    \\ full_simp_tac (srw_ss()) []
    \\ full_simp_tac std_ss [Bytes_def,LET_DEF,el_length_def]
    \\ fs [isDataElement_def])
  \\ strip_tac THEN1
     (full_simp_tac (srw_ss()) [SUBSET_DEF,FDOM_FUPDATE] \\ metis_tac [])
  \\ strip_tac THEN1 fs [INJ_DEF]
  \\ strip_tac THEN1
      (`∀x y. FDOM tf ⊆ y ∧ x = y ⇒ FDOM tf ⊆ x` by metis_tac []
      \\ qpat_x_assum `FDOM tf ⊆ _` kall_tac
      \\ pop_assum drule
      \\ disch_then ho_match_mp_tac
      \\ fs [all_ts_cons_no_block]
      \\ rw [FUN_EQ_THM,all_ts_def]
      \\ EQ_TAC
      >- (rw [] \\ fs [lookup_insert] \\ every_case_tac \\ fs []
         \\ metis_tac [])
      \\ rw []
      >- (`ptr ≠ n` by (CCONTR_TAC \\ fs[GSYM lookup_NONE_domain])
         \\ metis_tac [lookup_insert])
      \\ metis_tac [])
  \\ strip_tac THEN1 asm_rewrite_tac []
  \\ Q.ABBREV_TAC `f1 = f |+ (ptr,a)`
  \\ `f SUBMAP f1` by
   (Q.UNABBREV_TAC `f1` \\ full_simp_tac (srw_ss()) [SUBMAP_DEF,FAPPLY_FUPDATE_THM]
    \\ metis_tac [])
  \\ `tf SUBMAP tf` by rw []
  \\ strip_tac THEN1
   (full_simp_tac std_ss [LIST_REL_def]
    \\ strip_tac THEN1 (UNABBREV_ALL_TAC \\ fs [v_inv_def])
    \\ full_simp_tac std_ss [EVERY2_EQ_EL]
    \\ imp_res_tac EVERY2_IMP_LENGTH
    \\ metis_tac [v_inv_SUBMAP])
  \\ rpt strip_tac
  \\ Cases_on `n = ptr` THEN1
   (Q.UNABBREV_TAC `f1` \\ asm_simp_tac (srw_ss()) [bc_ref_inv_def,FDOM_FUPDATE,
      FAPPLY_FUPDATE_THM] \\ full_simp_tac std_ss [el_length_def,Bytes_def,LET_DEF]
    \\ full_simp_tac (srw_ss()) [FLOOKUP_DEF,EVERY2_EQ_EL]
    \\ rpt strip_tac \\ qexists_tac `REPLICATE ws 0w` \\ fs [])
  \\ `reachable_refs stack refs n` by
   (fs [reachable_refs_def]
    \\ `ref_edge (insert ptr (ByteArray fl bs) refs) = ref_edge refs` by
     (fs [ref_edge_def,FUN_EQ_THM,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,lookup_insert]
      \\ rw [] \\ rfs [GSYM lookup_NONE_domain])
    \\ rpt (asm_exists_tac \\ fs [])
    \\ fs [] \\ rveq \\ fs [get_refs_def] \\ rveq \\ fs []
    \\ qpat_assum `RTC _ _ _` mp_tac
    \\ once_rewrite_tac [RTC_CASES1] \\ fs [ref_edge_def]
    \\ fs [GSYM lookup_NONE_domain] \\ NO_TAC)
  \\ first_x_assum drule
  \\ simp [bc_ref_inv_def,FLOOKUP_DEF,Abbr`f1`,FAPPLY_FUPDATE_THM,lookup_insert]
  \\ strip_tac
  \\ `n ∈ (domain refs)`
     by (pop_assum mp_tac \\ every_case_tac \\ rveq \\ fs [domain_lookup])
  \\ pop_assum (fn thm => pop_assum mp_tac \\ assume_tac thm)
  \\ TOP_CASE_TAC \\ fs [] \\ rveq \\ fs []
  \\ TOP_CASE_TAC \\ fs [] \\ rveq \\ fs []
  \\ TOP_CASE_TAC \\ fs [] \\ rveq \\ fs []
  \\ fs [Bytes_def,isDataElement_def,LET_THM,heap_store_rel_def,
         isSomeDataElement_def,PULL_EXISTS,RefBlock_def,lookup_NONE_domain] \\ rw []
  \\ res_tac
  \\ qpat_x_assum `EVERY2 PPP zs l` MP_TAC
  \\ fs [heap_store_rel_def,isSomeDataElement_def,PULL_EXISTS]
  \\ match_mp_tac EVERY2_IMP_EVERY2
  \\ full_simp_tac std_ss [] \\ simp_tac (srw_ss()) []
  \\ rpt strip_tac
  \\ match_mp_tac v_inv_SUBMAP \\ fs []
  \\ fs [heap_store_rel_def,isSomeDataElement_def,PULL_EXISTS]
QED

(* pop *)

Theorem pop_thm:
   abs_ml_inv conf (xs ++ stack) refs (rs ++ roots,heap,be,a,sp,sp1,gens) limit ts /\
    (LENGTH xs = LENGTH rs) ==>
    abs_ml_inv conf (stack) refs (roots,heap,be,a,sp,sp1,gens) limit ts
Proof
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ rpt strip_tac
  \\ full_simp_tac std_ss [roots_ok_def,MEM_APPEND]
  THEN1 (rw [] \\ res_tac \\ fs [])
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ qexists_tac `DRESTRICT tf (all_ts refs stack)` \\ full_simp_tac std_ss []
  \\ conj_tac
  >- fs [INJ_DEF,DRESTRICT_DEF]
  \\ conj_tac
  >- fs [SUBSET_DEF,DRESTRICT_DEF]
  \\ conj_tac
  >- fs [SUBSET_DEF,DRESTRICT_DEF,IN_INTER]
  \\ conj_tac
  >- (match_mp_tac EVERY2_MEM_MONO
     \\ imp_res_tac LIST_REL_APPEND_IMP
     \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
     \\ simp[FORALL_PROD] \\ rw[]
     \\ ho_match_mp_tac v_inv_tf_restrict
     \\ rw []
     \\ ho_match_mp_tac MEM_in_all_ts
     \\ qexists_tac `p_1` \\ rw []
     \\ ho_match_mp_tac MEM_stack_all_vs
     \\ drule MEM_ZIP2 \\ rw []
     \\ rw [EL_MEM])
  \\ fs[reachable_refs_def,PULL_EXISTS]
  \\ rw[]
  \\ fs[bc_ref_inv_def]
  \\ fsrw_tac[boolSimps.DNF_ss][]
  \\ first_x_assum rpt_drule
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[] \\ rw[]
  \\ fs[RefBlock_def,Bytes_def]
  \\ match_mp_tac EVERY2_MEM_MONO
  \\ imp_res_tac LIST_REL_APPEND_IMP
  \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
  \\ simp[FORALL_PROD] \\ rw[]
  \\ ho_match_mp_tac v_inv_tf_restrict
  \\ rw []
  \\ ho_match_mp_tac MEM_in_all_ts
  \\ qexists_tac `p_2` \\ rw []
  \\ rw [all_vs_def] \\ disj1_tac
  \\ map_every qexists_tac [`n`,`l`] \\ rw []
  \\ ho_match_mp_tac MEM_v_all_vs
  \\ drule MEM_ZIP2 \\ rw []
  \\ rw [EL_MEM]
QED

(* equality *)

Theorem ref_eq_thm:
   abs_ml_inv conf (RefPtr T p1::RefPtr T p2::stack) refs
      (r1::r2::roots,heap,be,a,sp,sp1,gens) limit ts ==>
    ((p1 = p2) <=> (r1 = r2)) /\
    ?p1 p2. r1 = Pointer p1 (Word 0w) /\ r2 = Pointer p2 (Word 0w)
Proof
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ rpt strip_tac
  \\ fs [v_inv_def,INJ_DEF] \\ res_tac \\ fs [] \\ fs []
  \\ eq_tac \\ rw [] \\ fs []
QED

Theorem num_eq_thm:
    abs_ml_inv conf (Number i1::Number i2::stack) refs
      (r1::r2::roots,heap,be,a,sp,sp1,gens) limit ts /\
    small_int (:'a) i1 /\
    small_int (:'a) i2 ==>
    ((i1 = i2) <=> (r1 = r2)) /\
    r1 = Data (Word (Smallnum i1:'a word)) /\
    r2 = Data (Word (Smallnum i2))
Proof
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ rpt strip_tac
  \\ fs [v_inv_def,INJ_DEF] \\ fs [Smallnum_def]
  \\ Cases_on `i1` \\ Cases_on `i2`
  \\ fs [small_int_def,X_LT_DIV,X_LE_DIV] \\ fs [word_2comp_n2w]
QED

Theorem Smallnum_i2w:
   Smallnum i = i2w (4 * i)
Proof
  fs [Smallnum_def,integer_wordTheory.i2w_def]
  \\ Cases_on `i` \\ fs []
  \\ reverse IF_CASES_TAC \\ fs [WORD_EQ_NEG]
  THEN1 (`F` by intLib.COOPER_TAC)
  \\ AP_THM_TAC \\ AP_TERM_TAC \\ intLib.COOPER_TAC
QED

Theorem small_int_IMP_MIN_MAX:
   good_dimindex (:'a) /\ small_int (:'a) i ==>
    INT_MIN (:'a) <= 4 * i ∧ 4 * i <= INT_MAX (:'a)
Proof
  fs [good_dimindex_def] \\ rw []
  \\ rfs [small_int_def,dimword_def,
       wordsTheory.INT_MIN_def,wordsTheory.INT_MAX_def]
  \\ intLib.COOPER_TAC
QED

Theorem num_less_thm:
   good_dimindex (:'a) /\ small_int (:'a) i1 /\ small_int (:'a) i2 ==>
    ((i1 < i2) <=> (Smallnum i1 < Smallnum i2:'a word))
Proof
  fs [integer_wordTheory.WORD_LTi,Smallnum_i2w] \\ strip_tac
  \\ imp_res_tac small_int_IMP_MIN_MAX
  \\ fs [integer_wordTheory.w2i_i2w]
  \\ intLib.COOPER_TAC
QED

(* permute stack *)

Theorem all_ts_permute:
  ∀(refs : v ref num_map) stack stack'. PERM stack stack' ⇒ all_ts refs stack = all_ts refs stack'
Proof
  strip_tac
  \\ ho_match_mp_tac PERM_IND
  \\ rw []
  \\ ONCE_REWRITE_TAC [all_ts_head] \\ rw []
  \\ qmatch_goalsub_abbrev_tac `all_ts refs x' ∪ _ = all_ts refs y' ∪ _`
  \\ ONCE_REWRITE_TAC [all_ts_head] \\ rw [UNION_ASSOC]
  \\ ONCE_REWRITE_TAC [UNION_COMM] \\ AP_TERM_TAC
  \\ rw [Once UNION_COMM]
QED

Theorem reachable_refs_stack_subset:
  ∀x y refs n. reachable_refs y refs n ∧ set y ⊆ set x ⇒ reachable_refs x refs n
Proof
  rw [reachable_refs_def]
  \\ qexists_tac `x'`
  \\ qexists_tac `r`
  \\ rw []
  \\ fs [SUBSET_DEF,LIST_TO_SET_DEF,MEM]
QED

Theorem abs_ml_inv_stack_permute:
  !xs ys.
      abs_ml_inv conf (MAP FST xs ++ stack) refs
        (MAP SND xs ++ roots,heap,be,a,sp,sp1,gens) limit ts /\
      set ys SUBSET set xs ==>
      abs_ml_inv conf (MAP FST ys ++ stack) refs
        (MAP SND ys ++ roots,heap,be,a,sp,sp1,gens) limit ts
Proof
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ rpt strip_tac
  \\ full_simp_tac std_ss [roots_ok_def]
  THEN1 (full_simp_tac std_ss [MEM_APPEND,SUBSET_DEF,MEM_MAP] \\ metis_tac [])
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ qexists_tac `DRESTRICT tf (all_ts refs (MAP FST ys ++ stack))` \\ full_simp_tac std_ss []
  \\ conj_tac
  >- fs[INJ_DEF,DRESTRICT_DEF]
  \\ conj_tac
  >- fs[SUBSET_DEF,DRESTRICT_DEF]
  \\ conj_tac
  >- fs[SUBSET_DEF,DRESTRICT_DEF,IN_INTER]
  \\ conj_tac
  >- (full_simp_tac std_ss [LIST_REL_APPEND_EQ,LENGTH_MAP]
     \\ conj_tac
     >- (full_simp_tac std_ss [EVERY2_MAP_FST_SND]
        \\ full_simp_tac std_ss [EVERY_MEM,SUBSET_DEF]
        \\ rw [] \\ pairarg_tac \\ rw []
        \\ ho_match_mp_tac v_inv_tf_restrict
        \\ rw []
        >- (pop_assum (fn t => first_assum (fn t' => mp_then Any ASSUME_TAC t' t))
           \\ pop_assum (fn t => first_assum (fn t' => mp_then Any ASSUME_TAC t' t))
           \\ fs [])
        >- (rw [all_ts_def] \\ qexists_tac `v`
           \\ rw [] \\ disj2_tac \\ disj1_tac
           \\ drule mem_exists_set
           \\ rw [MEM,MEM_MAP]
           \\ metis_tac []))
     >- (match_mp_tac EVERY2_MEM_MONO
        \\ imp_res_tac LIST_REL_APPEND_IMP
        \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
        \\ simp[FORALL_PROD] \\ rw[]
        \\ ho_match_mp_tac v_inv_tf_restrict
        \\ rw [] \\ ho_match_mp_tac MEM_in_all_ts
        \\ qexists_tac `p_1` \\ rw []
        \\ ho_match_mp_tac MEM_stack_all_vs
        \\ drule MEM_ZIP2 \\ rw []
        \\ rw [EL_MEM]))
  \\ rw []
  \\ drule_then (qspec_then `MAP FST xs ++ stack` mp_tac) reachable_refs_stack_subset
  \\ impl_tac
  >- (fs [SUBSET_DEF,LIST_TO_SET_DEF,MEM_MAP] \\ metis_tac [])
  (* TODO: lookup for flip combinator *)
  \\ disch_then (fn t1 => first_x_assum (fn t2 => mp_then Any mp_tac t2 t1))
  \\ fs[bc_ref_inv_def]
  \\ Cases_on `FLOOKUP f n` \\ fs []
  \\ Cases_on `lookup n refs` \\ fs []
  \\ Cases_on `x'` \\ rw []
  \\ qexists_tac `zs` \\ rw []
  \\ match_mp_tac EVERY2_MEM_MONO
  \\ imp_res_tac LIST_REL_APPEND_IMP
  \\ first_assum(part_match_exists_tac(last o strip_conj) o concl)
  \\ simp[FORALL_PROD] \\ rw[]
  \\ ho_match_mp_tac v_inv_tf_restrict
  \\ rw [] \\ ho_match_mp_tac MEM_in_all_ts
  \\ qexists_tac `p_2` \\ rw []
  \\ rw [all_vs_def] \\ disj1_tac
  \\ map_every qexists_tac [`n`,`l`] \\ rw []
  \\ ho_match_mp_tac MEM_v_all_vs
  \\ drule MEM_ZIP2 \\ rw []
  \\ rw [EL_MEM]
QED

(* duplicate *)

Theorem duplicate_thm:
   abs_ml_inv conf (xs ++ stack) refs (rs ++ roots,heap,be,a,sp,sp1,gens) limit ts /\
   (LENGTH xs = LENGTH rs) ==>
   abs_ml_inv conf (xs ++ xs ++ stack) refs (rs ++ rs ++ roots,heap,be,a,sp,sp1,gens) limit ts
Proof
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ rpt strip_tac
  \\ full_simp_tac std_ss [roots_ok_def] THEN1 metis_tac [MEM_APPEND]
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ qexists_tac `tf` \\ full_simp_tac std_ss []
  \\ conj_tac >- fs [all_ts_def]
  \\ imp_res_tac LIST_REL_APPEND_EQ \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [APPEND_ASSOC]
  \\ full_simp_tac std_ss [reachable_refs_def,MEM_APPEND] \\ metis_tac []
QED

Theorem duplicate1_thm =
  duplicate_thm |> Q.INST [`xs`|->`[x1]`,`rs`|->`[r1]`]
                |> SIMP_RULE std_ss [LENGTH,APPEND]

(* move *)

Theorem move_thm:
   !xs1 rs1 xs2 rs2 xs3 rs3.
      abs_ml_inv conf (xs1 ++ xs2 ++ xs3 ++ stack) refs
                      (rs1 ++ rs2 ++ rs3 ++ roots,heap,be,a,sp,sp1,gens) limit ts /\
      (LENGTH xs1 = LENGTH rs1) /\
      (LENGTH xs2 = LENGTH rs2) /\
      (LENGTH xs3 = LENGTH rs3) ==>
      abs_ml_inv conf (xs1 ++ xs3 ++ xs2 ++ stack) refs
                      (rs1 ++ rs3 ++ rs2 ++ roots,heap,be,a,sp,sp1,gens) limit ts
Proof
  REPEAT GEN_TAC
  \\ full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def] \\ rpt strip_tac
  \\ full_simp_tac std_ss [roots_ok_def] THEN1 metis_tac [MEM_APPEND]
  \\ qexists_tac `f` \\ full_simp_tac std_ss []
  \\ qexists_tac `tf` \\ full_simp_tac std_ss []
  \\ conj_tac >- (fs [all_ts_def,SUBSET_DEF] \\ metis_tac [])
  \\ strip_tac THEN1 fs[LIST_REL_APPEND_EQ]
  \\ full_simp_tac std_ss [reachable_refs_def,MEM_APPEND] \\ metis_tac []
QED

(* splits *)

Theorem split1_thm:
   abs_ml_inv conf (xs1 ++ stack) refs (roots,heap,be,a,sp,sp1,gens) limit ts ==>
    ?rs1 roots1. (roots = rs1 ++ roots1) /\ (LENGTH rs1 = LENGTH xs1)
Proof
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,GSYM APPEND_ASSOC]
  \\ rpt strip_tac \\ NTAC 5 (imp_res_tac LIST_REL_SPLIT1 \\ imp_res_tac LIST_REL_LENGTH) \\ metis_tac []
QED

Theorem split2_thm:
   abs_ml_inv conf (xs1 ++ xs2 ++ stack) refs (roots,heap,be,a,sp,sp1,gens) limit ts ==>
    ?rs1 rs2 roots1. (roots = rs1 ++ rs2 ++ roots1) /\
      (LENGTH rs1 = LENGTH xs1) /\ (LENGTH rs2 = LENGTH xs2)
Proof
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,GSYM APPEND_ASSOC]
  \\ rpt strip_tac \\ NTAC 5 (imp_res_tac LIST_REL_SPLIT1 \\ imp_res_tac LIST_REL_LENGTH) \\ metis_tac []
QED

Theorem split3_thm:
   abs_ml_inv conf (xs1 ++ xs2 ++ xs3 ++ stack) refs (roots,heap,be,a,sp,sp1,gens) limit ts ==>
    ?rs1 rs2 rs3 roots1. (roots = rs1 ++ rs2 ++ rs3 ++ roots1) /\
      (LENGTH rs1 = LENGTH xs1) /\ (LENGTH rs2 = LENGTH xs2) /\
      (LENGTH rs3 = LENGTH xs3)
Proof
  full_simp_tac std_ss [abs_ml_inv_def,bc_stack_ref_inv_def,GSYM APPEND_ASSOC]
  \\ rpt strip_tac \\ NTAC 5 (imp_res_tac LIST_REL_SPLIT1 \\ imp_res_tac LIST_REL_LENGTH) \\ metis_tac []
QED

Theorem abs_ml_inv_Num:
   abs_ml_inv conf stack refs (roots,heap,be,a,sp,sp1,gens) limit ts /\ small_int (:α) i ==>
    abs_ml_inv conf (Number i::stack) refs
      (Data (Word ((Smallnum i):'a word))::roots,heap,be,a,sp,sp1,gens) limit ts
Proof
  fs [abs_ml_inv_def,roots_ok_def,bc_stack_ref_inv_def,v_inv_def]
  \\ fs [reachable_refs_def]
  \\ rw [] \\ fs [] \\ res_tac \\ fs []
  \\ qexists_tac `f` \\ fs []
  \\ qexists_tac `tf` \\ fs []
  \\ conj_tac >- (fs [all_ts_def,SUBSET_DEF] \\ metis_tac [])
  \\ rw [] \\ fs [get_refs_def] \\ metis_tac []
QED

Theorem heap_store_unused_IMP_length:
  heap_store_unused a sp' x heap = (heap2,T) ==>
    heap_length heap2 = heap_length heap
Proof
  fs [heap_store_unused_def] \\ IF_CASES_TAC \\ fs []
  \\ imp_res_tac heap_lookup_SPLIT \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND,heap_store_lemma]
  \\ rw [] \\ fs [] \\ fs [heap_length_APPEND,el_length_def,heap_length_def]
QED

Theorem heap_store_unused_alt_IMP_length:
   heap_store_unused_alt a sp' x heap = (heap2,T) ==>
    heap_length heap2 = heap_length heap
Proof
  fs [heap_store_unused_alt_def] \\ IF_CASES_TAC \\ fs []
  \\ imp_res_tac heap_lookup_SPLIT \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND,heap_store_lemma]
  \\ rw [] \\ fs [] \\ fs [heap_length_APPEND,el_length_def,heap_length_def]
QED


(* -------------------------------------------------------
    representation in memory
   ------------------------------------------------------- *)

Definition pointer_bits_def:
  (* pointers have tag and len bits *)
  pointer_bits conf abs_heap n =
    case heap_lookup n abs_heap of
    | SOME (DataElement xs l (BlockTag tag,[])) =>
        maxout_bits (LENGTH xs) conf.len_bits (conf.tag_bits + 2) ||
        maxout_bits tag conf.tag_bits 2 || 1w
    | _ => all_ones (conf.len_bits + conf.tag_bits + 1) 0
End

Definition is_all_ones_def:
  is_all_ones m n w = ((all_ones m n && w) = all_ones m n)
End

Definition decode_maxout_def:
  decode_maxout l n w =
    if is_all_ones (n+l) n w then NONE else SOME (((n+l) -- n) w >> n)
End

Definition decode_addr_def:
  decode_addr conf w =
    (decode_maxout conf.len_bits (conf.tag_bits + 2) w,
     decode_maxout conf.tag_bits 2 w)
End

Definition get_addr_def:
  get_addr conf n w =
    ((n2w n << shift_length conf) || get_lowerbits conf w)
End

Definition word_addr_def:
  (word_addr conf (Data (Loc l1 l2)) = Loc l1 0) /\
  (word_addr conf (Data (Word v)) = Word (v && (~1w))) /\
  (word_addr conf (Pointer n w) = Word (get_addr conf n w))
End

Theorem b2w_def:
  (multiword$b2w T = 1w) ∧ (multiword$b2w F = 0w)
Proof
  EVAL_TAC
QED

Definition word_payload_def:
  (word_payload ys l (BlockTag n) qs conf =
     (* header: ...00[11] here i in ...i[11] must be 0 for the GC *)
     (make_header conf (n2w n << 2) (LENGTH ys),
      MAP (word_addr conf) ys,
      (qs = []) /\ (LENGTH ys = l) /\
      encode_header conf (n * 4) (LENGTH ys) =
        SOME (make_header conf (n2w n << 2) (LENGTH ys):'a word))) /\
  (word_payload ys l (RefTag) qs conf =
     (* header: ...010[11] here i in ...i[11] must be 0 for the GC *)
     (make_header conf 2w (LENGTH ys),
      MAP (word_addr conf) ys,
      (qs = []) /\ (LENGTH ys = l))) /\
  (word_payload ys l Word64Tag qs conf =
     (* header: ...011[11] here i in ...i[11] must be 1 for the GC *)
     (make_header conf 3w l,
      qs, (ys = []) /\ (LENGTH qs = l) /\
          IS_SOME ((encode_header conf 3 l):'a word option))) /\
  (word_payload ys l (NumTag b) qs conf =
     (* header: ...111[11] or ...011[11]
            here i in ...i[11] must be 1 for GC *)
     (make_header conf (b2w b << 2 || 3w:'a word) (LENGTH qs),
      qs, (ys = []) /\ (LENGTH qs = l) /\
          IS_SOME ((encode_header conf (w2n (b2w b << 2 || 3w:'a word))
                      (LENGTH qs)):'a word option))) /\
  (word_payload ys l (BytesTag fl n) qs conf =
     (* header: ...101[11] or ...001[11] (compare-by-contents)
            here i in ...i[11] must be 1 for the GC *)
     ((make_byte_header conf fl n):'a word,
      qs, (ys = []) /\ (LENGTH qs = l) /\
          let k = if dimindex(:'a) = 32 then 2 else 3 in
          n + 2 ** k < 2 ** (conf.len_size + k)))
End

Theorem word_payload_T_IMP:
   word_payload l5 n5 tag r conf = (h:'a word,ts,T) /\
    good_dimindex (:'a) /\ conf.len_size + 2 < dimindex (:'a) ==>
    n5 = LENGTH ts /\
    if word_bit 2 h then l5 = [] else ts = MAP (word_addr conf) l5
Proof
  Cases_on `tag`
  \\ full_simp_tac(srw_ss())[word_payload_def,make_header_def,
       make_byte_header_def,LET_THM]
  \\ rw [] \\ fs [] \\ fs [word_bit_def]
  \\ rfs [word_or_def,fcpTheory.FCP_BETA,word_lsl_def,wordsTheory.word_index]
  \\ fs [good_dimindex_def,fcpTheory.FCP_BETA,
         word_index] \\ rfs []
QED

Definition word_el_def:
  (word_el a (Unused l) conf = word_list_exists (a:'a word) (l+1)) /\
  (word_el a (ForwardPointer n d l) conf =
     one (a,Word (n2w n << 2)) *
     word_list_exists (a + bytes_in_word) l) /\
  (word_el a (DataElement ys l (tag,qs)) conf =
     let (h,ts,c) = word_payload ys l tag qs conf in
       word_list a (Word h :: ts) *
       cond (LENGTH ts < 2 ** (dimindex (:'a) - 4) /\
             decode_length conf h = n2w (LENGTH ts) /\ c))
End

Definition word_heap_def:
  (word_heap a ([]:'a ml_heap) conf = emp) /\
  (word_heap a (x::xs) conf =
     word_el a x conf *
     word_heap (a + bytes_in_word * n2w (el_length x)) xs conf)
End

Definition gen_starts_in_store_def:
  gen_starts_in_store c (GenState _ gen_starts) (SOME (Word w)) =
    (!gen_sizes.
       c.gc_kind = Generational gen_sizes ==>
       LENGTH gen_starts = LENGTH gen_sizes /\
       !x xs. gen_starts = x::xs ==>
              w = (bytes_in_word * n2w x)) /\
  gen_starts_in_store c _ _ = F
End

Theorem gen_starts_in_store_IMP:
   gen_starts_in_store c gens x ==> ?w. x = SOME (Word w)
Proof
  Cases_on `x` \\ Cases_on `gens` \\ fs [gen_starts_in_store_def]
  \\ Cases_on `x'` \\ fs [gen_starts_in_store_def]
QED

Definition glob_real_inv_def:
  glob_real_inv c (curr:'a word) globals globreal ⇔
    ∃w. globals = SOME (Word w) ∧
        globreal = SOME (Word (curr + (w >>> (shift_length c) << shift (:α))))
End

Definition heap_in_memory_store_def:
  heap_in_memory_store heap a sp sp1 gens c s m dm limit <=>
    heap_length heap <= dimword (:'a) DIV 2 ** shift_length c /\
    (* +3 is breathing room for lists: *)
    (heap_length heap + 3) * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    shift (:'a) <= shift_length c /\ c.len_size <> 0 /\
    c.len_size + 7 (* 5 tag bits + 2-3 bits for byte arrays *) < dimindex (:'a) /\
    shift_length c < dimindex (:'a) /\ Globals ∈ FDOM s /\
    ?curr other.
      byte_aligned curr /\ byte_aligned other /\
      (FLOOKUP s CurrHeap = SOME (Word (curr:'a word))) /\
      (FLOOKUP s OtherHeap = SOME (Word other)) /\
      (FLOOKUP s NextFree = SOME (Word (curr + bytes_in_word * n2w a))) /\
      (FLOOKUP s TriggerGC = SOME (Word (curr + bytes_in_word * n2w (a+sp)))) /\
      (FLOOKUP s EndOfHeap = SOME (Word (curr + bytes_in_word * n2w (a+sp+sp1)))) /\
      (FLOOKUP s HeapLength = SOME (Word (bytes_in_word * n2w limit))) /\
      glob_real_inv c curr (FLOOKUP s Globals) (FLOOKUP s GlobReal) /\
      gen_starts_in_store c gens (FLOOKUP s GenStart) /\
      (word_heap curr heap c *
       word_heap other (heap_expand limit) c) (fun2set (m,dm))
End

Definition word_ml_inv_def:
  word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs stack <=>
    ?hs. abs_ml_inv c (MAP FST stack) refs (hs,heap,be,a,sp,sp1,gens) limit ts /\
         EVERY2 (\v w. word_addr c v = w) hs (MAP SND stack)
End

Theorem IMP_THE_EQ:
   x = SOME w ==> THE x = w
Proof
  full_simp_tac(srw_ss())[]
QED

Definition memory_rel_def:
  memory_rel c be ts refs space st (m:'a word -> 'a word_loc) dm vars <=>
    ∃heap limit a sp sp1 gens.
       heap_in_memory_store heap a sp sp1 gens c st m dm limit ∧
       word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs vars ∧
       (limit+3) * (dimindex (:α) DIV 8) + 1 < dimword (:α) ∧ space ≤ sp
End

Theorem EVERY2_MAP_MAP:
   !xs. EVERY2 P (MAP f xs) (MAP g xs) = EVERY (\x. P (f x) (g x)) xs
Proof
  Induct \\ full_simp_tac(srw_ss())[]
QED

Theorem MEM_FIRST_EL:
   !xs x.
      MEM x xs <=>
      ?n. n < LENGTH xs /\ (EL n xs = x) /\
          !m. m < n ==> (EL m xs <> EL n xs)
Proof
  srw_tac[][] \\ eq_tac
  THEN1 (srw_tac[][] \\ qexists_tac `LEAST n. EL n xs = x /\ n < LENGTH xs`
    \\ mp_tac (Q.SPEC `\n. EL n xs = x /\ n < LENGTH xs` (GEN_ALL FULL_LEAST_INTRO))
    \\ full_simp_tac(srw_ss())[MEM_EL]
    \\ strip_tac \\ pop_assum (qspec_then `n` mp_tac)
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ imp_res_tac LESS_LEAST \\ full_simp_tac(srw_ss())[] \\ `F` by decide_tac)
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[MEM_EL]
  \\ qexists_tac `n` \\ full_simp_tac(srw_ss())[]
QED

Theorem ALOOKUP_ZIP_EL:
   !xs hs n.
      n < LENGTH xs /\ LENGTH hs = LENGTH xs /\
      (∀m. m < n ⇒ EL m xs ≠ EL n xs) ==>
      ALOOKUP (ZIP (xs,hs)) (EL n xs) = SOME (EL n hs)
Proof
  Induct \\ Cases_on `hs` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `n` \\ full_simp_tac(srw_ss())[]
  \\ rpt strip_tac \\ first_assum (qspec_then `0` assume_tac)
  \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ first_x_assum match_mp_tac
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ first_x_assum (qspec_then `SUC m` mp_tac) \\ full_simp_tac(srw_ss())[]
QED

Theorem word_ml_inv_rearrange:
   (!x. MEM x ys ==> MEM x xs) ==>
   word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs xs ==>
   word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs ys
Proof
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
  \\ qpat_x_assum `abs_ml_inv c (MAP FST xs) refs (hs,heap,be,a,sp,sp1,gens) limit ts` mp_tac
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
  \\ qpat_x_assum `EL n' xs = (p_1,p_2')` (fn th => full_simp_tac(srw_ss())[GSYM th])
  \\ match_mp_tac ALOOKUP_ZIP_EL \\ full_simp_tac(srw_ss())[]
QED

Theorem memory_rel_rearrange:
   (∀x. MEM x ys ⇒ MEM x xs) ⇒
   memory_rel c be ts refs sp st m dm xs ==>
   memory_rel c be ts refs sp st m dm ys
Proof
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ qpat_x_assum `word_ml_inv _ _ _ _ _ _` mp_tac
  \\ match_mp_tac word_ml_inv_rearrange \\ fs []
QED

Theorem memory_rel_tl:
   memory_rel c be ts refs sp st m dm (x::xs) ==>
   memory_rel c be ts refs sp st m dm xs
Proof
  match_mp_tac memory_rel_rearrange \\ fs []
QED

Theorem word_ml_inv_Unit:
   word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs ws /\
    good_dimindex (:'a) ==>
    word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs
      ((Unit,Word (2w:'a word))::ws)
Proof
  fs [word_ml_inv_def,PULL_EXISTS] \\ rw []
  \\ qexists_tac `Data (Word 2w)`
  \\ qexists_tac `hs` \\ fs [word_addr_def]
  \\ fs [dataSemTheory.Unit_def,EVAL ``tuple_tag``]
  \\ drule (GEN_ALL cons_thm_EMPTY)
  \\ disch_then (qspec_then `0` mp_tac)
  \\ fs [good_dimindex_def,dimword_def]
  \\ fs [BlockNil_def]
QED

Theorem memory_rel_Unit:
   memory_rel c be ts refs sp st m dm xs /\ good_dimindex (:'a) ==>
   memory_rel c be ts refs sp st m dm ((Unit,Word (2w:'a word))::xs)
Proof
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ match_mp_tac word_ml_inv_Unit \\ fs []
QED

Theorem get_lowerbits_LSL_shift_length:
   get_lowerbits conf a >>> shift_length conf = 0w
Proof
  Cases_on `a`
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss]
       [word_index, get_lowerbits_def, small_shift_length_def, shift_length_def]
QED

Definition get_real_addr_def:
  get_real_addr conf st (w:'a word) =
    let k = shift (:α) in
      case FLOOKUP st CurrHeap of
      | SOME (Word curr) =>
          if k = shift_length conf ∧ conf.len_bits = 0 ∧ conf.tag_bits = 0
          then SOME (curr + w - 1w)
          else
            if k <= conf.pad_bits + 1
            then SOME (curr + (w >>> (shift_length conf - k)))
            else SOME (curr + (w >>> (shift_length conf) << k))
      | _ => NONE
End

Definition get_real_offset_def:
  get_real_offset (w:'a word) =
    if dimindex (:'a) = 32
    then SOME (w + bytes_in_word) else SOME (w << 1 + bytes_in_word)
End

Definition get_real_simple_addr_def:
  get_real_simple_addr conf st (w:'a word) =
    case FLOOKUP st CurrHeap of
    | SOME (Word curr) => SOME (curr + w ⋙ shift_length conf ≪ shift (:α))
    | _ => NONE
End

Triviality or_1:
  ∀w. (0 -- 0) w ‖ 1w = 1w :'a word
Proof
  fs [fcpTheory.CART_EQ,word_or_def,fcpTheory.FCP_BETA,word_lsl_def,
      word_0,word_bits_def]
  \\ once_rewrite_tac [wordsTheory.word_index_n2w] \\ fs []
  \\ rw [] \\ eq_tac \\ rw []
QED

Theorem get_real_addr_get_addr:
   heap_length heap <= dimword (:'a) DIV 2 ** shift_length c /\
    heap_lookup n heap = SOME anything /\
    FLOOKUP st CurrHeap = SOME (Word (curr:'a word)) /\
    good_dimindex (:'a) ==>
    get_real_simple_addr c st (get_addr c n w) = SOME (curr + n2w n * bytes_in_word) ∧
    get_real_addr c st (get_addr c n w) = SOME (curr + n2w n * bytes_in_word)
Proof
  fs [X_LE_DIV] \\ fs [get_addr_def,get_real_addr_def,get_real_simple_addr_def]
  \\ strip_tac
  \\ imp_res_tac heap_lookup_LESS \\ fs []
  \\ `w2n ((n2w n):'a word) * 2 ** shift_length c < dimword (:'a)` by
   (`n < dimword (:'a)` by
     (Cases_on `2 ** (shift_length c)` \\ fs []
      \\ Cases_on `n'` \\ fs [MULT_CLAUSES])
    \\ match_mp_tac LESS_LESS_EQ_TRANS
    \\ once_rewrite_tac [CONJ_COMM]
    \\ asm_exists_tac \\ fs [])
  \\ conj_asm1_tac THEN1
   (drule lsl_lsr \\ fs [get_lowerbits_LSL_shift_length]
    \\ fs [] \\ rw []
    \\ fs [good_dimindex_def,dimword_def] \\ rw []
    \\ rfs [WORD_MUL_LSL,word_mul_n2w,shift_def,bytes_in_word_def])
  \\ IF_CASES_TAC
  THEN1
   (Cases_on ‘w’
    \\ fs [get_lowerbits_def,small_shift_length_def,or_1]
    \\ ‘0w = n2w n ≪ shift_length c && 1w’ by
     (fs [fcpTheory.CART_EQ,word_and_def,fcpTheory.FCP_BETA,word_lsl_def,word_0]
      \\ rewrite_tac [word_1comp_def]
      \\ once_rewrite_tac [wordsTheory.word_index_n2w] \\ fs []
      \\ gvs [good_dimindex_def,shift_def])
    \\ drule (GSYM WORD_ADD_OR)
    \\ pop_assum kall_tac
    \\ fs []
    \\ gvs [WORD_MUL_LSL,bytes_in_word_def,word_mul_n2w,good_dimindex_def,
            dimword_def,shift_def]
    \\ qpat_x_assum ‘_ = shift_length _’ (assume_tac o GSYM)
    \\ fs [])
  \\ pop_assum kall_tac
  \\ reverse IF_CASES_TAC THEN1 fs []
  \\ fs []
  \\ `get_lowerbits c w ⋙ (shift_length c − shift (:α)) = 0w` by
    (Cases_on `w` \\ srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss]
       [word_index, get_lowerbits_def, shift_length_def, small_shift_length_def]
     \\ NO_TAC) \\ fs []
  \\ rewrite_tac [GSYM w2n_11,w2n_lsr]
  \\ fs [WORD_MUL_LSL,word_mul_n2w,bytes_in_word_def]
  \\ `(n * 2 ** shift_length c) < dimword (:α)` by
   (match_mp_tac LESS_LESS_EQ_TRANS
    \\ once_rewrite_tac [CONJ_COMM] \\ asm_exists_tac \\ fs [] \\ NO_TAC)
  \\ `(n * (dimindex (:α) DIV 8)) < dimword (:α)` by
   (match_mp_tac LESS_EQ_LESS_TRANS
    \\ qexists_tac `n * 2 ** shift_length c` \\ fs []
    \\ disj2_tac \\ fs [DIV_LE_X]
    \\ rfs [shift_def,good_dimindex_def,shift_length_def,EXP_ADD]
    \\ Cases_on `c.pad_bits` \\ fs [EXP,LEFT_ADD_DISTRIB]
    \\ fs [GSYM EXP_ADD]
    \\ Cases_on `2 ** (n' + (c.len_bits + c.tag_bits))` \\ fs [] \\ NO_TAC)
  \\ fs []
  \\ `shift_length c = shift (:'a) + (shift_length c - shift (:'a))` by
    (fs [shift_def,good_dimindex_def,shift_length_def] \\ NO_TAC)
  \\ pop_assum (fn th => simp_tac std_ss [Once th])
  \\ simp_tac std_ss [EXP_ADD,MULT_ASSOC,MULT_DIV]
  \\ fs [shift_def,good_dimindex_def]
QED

Theorem get_real_offset_thm:
   good_dimindex (:'a) ==>
    get_real_offset (n2w (4 * index)) =
      SOME (bytes_in_word + n2w index * bytes_in_word:'a word)
Proof
  fs [good_dimindex_def,dimword_def] \\ rw []
  \\ fs [get_real_offset_def,bytes_in_word_def,word_mul_n2w,WORD_MUL_LSL]
QED

Theorem word_heap_APPEND:
   !xs ys a.
      word_heap a (xs ++ ys) conf =
      word_heap a xs conf *
      word_heap (a + bytes_in_word * n2w (heap_length xs)) ys conf
Proof
  Induct \\ full_simp_tac(srw_ss())[word_heap_def,heap_length_def,
              SEP_CLAUSES,STAR_ASSOC]
  \\ full_simp_tac(srw_ss())[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
QED

Theorem FORALL_WORD:
   (!v:'a word. P v) <=> !n. n < dimword (:'a) ==> P (n2w n)
Proof
  eq_tac \\ rw [] \\ Cases_on `v` \\ fs []
QED

Theorem BlockNil_and_lemma:
   good_dimindex (:'a) ==>
    (-2w && 16w * tag + 2w) = 16w * tag + 2w:'a word
Proof
  `!w:word64. (-2w && 16w * w + 2w) = 16w * w + 2w` by blastLib.BBLAST_TAC
  \\ `!w:word32. (-2w && 16w * w + 2w) = 16w * w + 2w` by blastLib.BBLAST_TAC
  \\ fs [GSYM word_mul_n2w,GSYM word_add_n2w]
  \\ rfs [dimword_def,FORALL_WORD]
  \\ Cases_on `tag` \\ fs [good_dimindex_def] \\ rw []
  \\ fs [word_mul_n2w,word_add_n2w,word_2comp_n2w,word_and_n2w]
  \\ rfs [dimword_def] \\ fs []
QED

Theorem word_ml_inv_num_lemma:
   good_dimindex (:'a) ==> (-2w && 4w * v) = 4w * v:'a word
Proof
  `!w:word64. (-2w && 4w * w) = 4w * w` by blastLib.BBLAST_TAC
  \\ `!w:word32. (-2w && 4w * w) = 4w * w` by blastLib.BBLAST_TAC
  \\ rfs [dimword_def,FORALL_WORD]
  \\ fs [good_dimindex_def] \\ rw []
  \\ Cases_on `v` \\ fs [word_mul_n2w,word_and_n2w,word_2comp_n2w]
  \\ rfs [dimword_def]
QED

Theorem word_ml_inv_num:
   word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c s.refs ws /\
    good_dimindex (:'a) /\
    small_enough_int (&n) ==>
    word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c s.refs
      ((Number (&n),Word (n2w (4 * n):'a word))::ws)
Proof
  fs [word_ml_inv_def,PULL_EXISTS] \\ rw []
  \\ qexists_tac `Data (Word (Smallnum (&n)))`
  \\ qexists_tac `hs` \\ fs [] \\ conj_tac
  THEN1
   (match_mp_tac abs_ml_inv_Num \\ fs []
    \\ fs [backend_commonTheory.small_enough_int_def]
    \\ fs [small_int_def,Smallnum_def]
    \\ fs [good_dimindex_def,dimword_def] \\ rw [])
  \\ fs [word_addr_def,Smallnum_def,GSYM word_mul_n2w]
  \\ match_mp_tac word_ml_inv_num_lemma \\ fs []
QED

Theorem word_ml_inv_zero =
  word_ml_inv_num |> Q.INST [`n`|->`0`] |> SIMP_RULE (srw_ss()) []

Theorem word_ml_inv_neg_num_lemma:
   good_dimindex (:'a) ==> (-2w && -4w * v) = -4w * v:'a word
Proof
  `!w:word64. (-2w && -4w * w) = -4w * w` by blastLib.BBLAST_TAC
  \\ `!w:word32. (-2w && -4w * w) = -4w * w` by blastLib.BBLAST_TAC
  \\ rfs [dimword_def,FORALL_WORD]
  \\ fs [good_dimindex_def] \\ rw []
  \\ Cases_on `v` \\ fs [word_mul_n2w,word_and_n2w,word_2comp_n2w]
  \\ rfs [dimword_def]
QED

Theorem word_ml_inv_neg_num:
   word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c s.refs ws /\
    good_dimindex (:'a) /\
    small_enough_int (-&n) /\ n <> 0 ==>
    word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c s.refs
      ((Number (-&n),Word (-n2w (4 * n):'a word))::ws)
Proof
  fs [word_ml_inv_def,PULL_EXISTS] \\ rw []
  \\ qexists_tac `Data (Word (Smallnum (-&n)))`
  \\ qexists_tac `hs` \\ fs [] \\ conj_tac
  THEN1
   (match_mp_tac abs_ml_inv_Num \\ fs []
    \\ fs [backend_commonTheory.small_enough_int_def]
    \\ fs [small_int_def,Smallnum_def]
    \\ fs [good_dimindex_def,dimword_def] \\ rw [])
  \\ fs [word_addr_def,Smallnum_def,GSYM word_mul_n2w]
  \\ match_mp_tac word_ml_inv_neg_num_lemma \\ fs []
QED

Theorem word_list_APPEND:
   !xs ys a. word_list a (xs ++ ys) =
              word_list a xs * word_list (a + n2w (LENGTH xs) * bytes_in_word) ys
Proof
  Induct \\ full_simp_tac(srw_ss())[word_list_def,SEP_CLAUSES,STAR_ASSOC,ADD1,
                GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
QED

Theorem all_ts_head_eq:
  ∀v refs stack ts.
   v  ∈ all_vs refs stack
   ⇒ all_ts refs stack = all_ts refs (v::stack)
Proof
  rw [FUN_EQ_THM]
  \\ EQ_TAC
  >- (rw [all_ts_def,all_vs_def] \\ metis_tac [])
  \\ fs [all_ts_def,all_vs_def] \\ rw []
  >- metis_tac []
  >- (Cases_on `v` \\ fs [v_all_ts_def]
     >- (rw [] \\ drule_then assume_tac v_all_vs_MEM2 \\ rw []
        \\ qexists_tac `x` \\ rw []
        >- metis_tac []
        \\ ho_match_mp_tac v_all_vs_ts_MEM
        \\ qexists_tac `Block n0 n' l'`
        \\ rw [v_all_ts_def])
     \\ drule_then assume_tac v_all_vs_MEM2 \\ rw []
     \\ qexists_tac `x'` \\ rw [v_all_ts_def]
     >- metis_tac []
     \\ rw [] \\ ho_match_mp_tac v_all_vs_ts_MEM
     \\ qexists_tac `Block n0 n' l'` \\ rw [v_all_ts_def])
  >- metis_tac []
  >- metis_tac []
  >- (Cases_on `v` \\ fs [v_all_ts_def]
     >- (rw []
        \\ drule_then assume_tac v_all_vs_MEM2
        \\ rw []
        \\ qexists_tac `x` \\ rw []
        \\ ho_match_mp_tac v_all_vs_ts
        \\ metis_tac [])
    \\ drule_then assume_tac v_all_vs_MEM2 \\ rw []
    \\ qexists_tac `x'`\\ rw [v_all_ts_def]
    \\ ho_match_mp_tac v_all_vs_ts_MEM
    \\ qexists_tac `Block n0 n l`
    \\ rw [v_all_ts_def])
  >- metis_tac []
QED

Theorem memory_rel_El':
   memory_rel c be ts refs sp st m dm
     ((Block ts' tag vals,ptr)::vars) /\
    good_dimindex (:'a) /\
    index < LENGTH vals ==>
    ?ptr_w i_w x:'a word.
      ptr = Word ptr_w /\
      get_real_addr c st ptr_w = SOME x /\
      (x + bytes_in_word + bytes_in_word * n2w index) IN dm /\
      memory_rel c be ts refs sp st m dm
        ((EL index vals,m (x + bytes_in_word + bytes_in_word * n2w index))::
         (Block ts' tag vals,ptr)::vars)
Proof
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
  \\ drule LESS_LENGTH
  \\ strip_tac \\ fs [] \\ clean_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_LENGTH_APPEND]
  \\ imp_res_tac heap_lookup_SPLIT
  \\ rename1 `heap = ha ++ DataElement (ys1 ++ y::ys2) tt yy::hb`
  \\ PairCases_on `yy`
  \\ qpat_x_assum `abs_ml_inv _ _ _ _ _ _` kall_tac
  \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def,BlockRep_def]
  \\ clean_tac
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
  \\ fs [word_list_def,word_list_APPEND]
  \\ SEP_R_TAC \\ fs []
QED

Theorem memory_rel_El:
   memory_rel c be ts refs sp st m dm
     ((Block ts' tag vals,ptr)::(Number (&index),i)::vars) /\
    good_dimindex (:'a) /\
    index < LENGTH vals ==>
    ?ptr_w i_w x y:'a word.
      ptr = Word ptr_w /\ i = Word i_w /\
      get_real_addr c st ptr_w = SOME x /\
      get_real_offset i_w = SOME y /\
      (x + y) IN dm /\
      memory_rel c be ts refs sp st m dm
        ((EL index vals,m (x + y))::
         (Block ts' tag vals,ptr)::(Number (&index),i)::vars)
Proof
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
    \\ qpat_x_assum `abs_ml_inv _ _ _ _ _ _` kall_tac
    \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def,BlockRep_def]
    \\ clean_tac
    \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
    \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
    \\ `small_int (:α) (&index)` by
     (fs [small_int_def,intLib.COOPER_CONV ``-&n <= &k:int``]
      \\ fs [good_dimindex_def,dimword_def] \\ rw [] \\ rfs []
      \\ fs [] \\ clean_tac \\ fs [word_addr_def])
    \\ fs[word_addr_def]
    \\ fs [Smallnum_def,GSYM word_mul_n2w,word_ml_inv_num_lemma])
  \\ fs [] \\ fs [get_real_offset_thm]
  \\ drule LESS_LENGTH
  \\ strip_tac \\ fs [] \\ clean_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_LENGTH_APPEND]
  \\ imp_res_tac heap_lookup_SPLIT
  \\ rename1 `heap = ha ++ DataElement (ys1 ++ y::ys2) tt yy::hb`
  \\ PairCases_on `yy`
  \\ qpat_x_assum `abs_ml_inv _ _ _ _ _ _` kall_tac
  \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def,BlockRep_def]
  \\ clean_tac
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
  \\ fs [word_list_def,word_list_APPEND]
  \\ SEP_R_TAC \\ fs []
QED

Theorem memory_rel_swap:
   memory_rel c be ts refs sp st m dm (x::y::z) ==>
   memory_rel c be ts refs sp st m dm (y::x::z)
Proof
  match_mp_tac memory_rel_rearrange \\ rw[] \\ rw[]
QED

Theorem memory_rel_Deref':
   memory_rel c be ts refs sp st m dm ((RefPtr bl nn,ptr)::vars) /\
    lookup nn refs = SOME (ValueArray vals) /\
    good_dimindex (:'a) /\
    index < LENGTH vals ==>
    ?ptr_w x:'a word.
      ptr = Word ptr_w /\
      get_real_addr c st ptr_w = SOME x /\
      (x + bytes_in_word + bytes_in_word * n2w index) IN dm /\
      memory_rel c be ts refs sp st m dm
        ((EL index vals,m (x + bytes_in_word + bytes_in_word * n2w index))::
         (RefPtr bl nn,ptr)::vars)
Proof
  rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ fs [memory_rel_def,PULL_EXISTS] \\ rw []
  \\ asm_exists_tac \\ fs []
  \\ fs [word_ml_inv_def,PULL_EXISTS] \\ clean_tac
  \\ rpt_drule deref_thm \\ fs [domain_lookup]
  \\ disch_then drule \\ strip_tac
  \\ asm_exists_tac \\ fs []
  \\ Cases_on `v` \\ fs [heap_el_def]
  \\ every_case_tac \\ fs [] \\ clean_tac
  \\ fs [GSYM CONJ_ASSOC,word_addr_def]
  \\ fs [heap_in_memory_store_def]
  \\ rpt_drule get_real_addr_get_addr \\ fs []
  \\ disch_then kall_tac
  \\ drule LESS_LENGTH
  \\ strip_tac \\ fs [] \\ clean_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_LENGTH_APPEND]
  \\ imp_res_tac heap_lookup_SPLIT
  \\ PairCases_on `b` \\ fs []
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
  \\ Cases_on `b0` \\ fs [word_payload_def]
  \\ fs [word_list_def,word_list_APPEND,SEP_CLAUSES] \\ fs [SEP_F_def]
  \\ SEP_R_TAC \\ fs []
QED

Theorem memory_rel_Deref:
   memory_rel c be ts refs sp st m dm
     ((RefPtr bl nn,ptr)::(Number (&index),i)::vars) /\
    lookup nn refs = SOME (ValueArray vals) /\
    good_dimindex (:'a) /\
    index < LENGTH vals ==>
    ?ptr_w i_w x y:'a word.
      ptr = Word ptr_w /\ i = Word i_w /\
      get_real_addr c st ptr_w = SOME x /\
      get_real_offset i_w = SOME y /\
      (x + y) IN dm /\
      memory_rel c be ts refs sp st m dm
        ((EL index vals,m (x + y))::
         (RefPtr bl nn,ptr)::(Number (&index),i)::vars)
Proof
  rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ fs [memory_rel_def,PULL_EXISTS] \\ rw []
  \\ asm_exists_tac \\ fs []
  \\ fs [word_ml_inv_def,PULL_EXISTS] \\ clean_tac
  \\ rpt_drule deref_thm \\ fs [domain_lookup]
  \\ disch_then drule \\ strip_tac
  \\ asm_exists_tac \\ fs []
  \\ Cases_on `v` \\ fs [heap_el_def]
  \\ every_case_tac \\ fs [] \\ clean_tac
  \\ fs [GSYM CONJ_ASSOC,word_addr_def]
  \\ fs [heap_in_memory_store_def]
  \\ rpt_drule get_real_addr_get_addr \\ fs []
  \\ disch_then kall_tac
  \\ `word_addr c v' = Word (n2w (4 * index))` by
   (qpat_x_assum `abs_ml_inv _ _ _ _ _ _` kall_tac
    \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def,BlockRep_def]
    \\ clean_tac
    \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
    \\ `reachable_refs (RefPtr bl nn::Number (&index)::MAP FST vars) refs nn` by
     (fs [reachable_refs_def] \\ qexists_tac `RefPtr bl nn` \\ fs []
      \\ fs [get_refs_def] \\ NO_TAC) \\ res_tac
    \\ pop_assum mp_tac
    \\ simp_tac std_ss [bc_ref_inv_def]
    \\ fs [FLOOKUP_DEF,RefBlock_def] \\ strip_tac \\ clean_tac
    \\ imp_res_tac heap_lookup_SPLIT
    \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
    \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
    \\ `small_int (:α) (&index)` by
     (fs [small_int_def,intLib.COOPER_CONV ``-&n <= &k:int``]
      \\ fs [good_dimindex_def,dimword_def]
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
  \\ SEP_R_TAC \\ fs []
QED

Theorem LENGTH_EQ_1:
   (LENGTH xs = 1 <=> ?a1. xs = [a1]) /\
    (1 = LENGTH xs <=> ?a1. xs = [a1])
Proof
  rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `xs` \\ fs [LENGTH_NIL]
QED

Theorem LENGTH_EQ_2:
   (LENGTH xs = 2 <=> ?a1 a2. xs = [a1;a2]) /\
    (2 = LENGTH xs <=> ?a1 a2. xs = [a1;a2])
Proof
  rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `xs` \\ fs []
  \\ Cases_on `t` \\ fs [LENGTH_NIL]
QED

Theorem LENGTH_EQ_3:
   (LENGTH xs = 3 <=> ?a1 a2 a3. xs = [a1;a2;a3]) /\
    (3 = LENGTH xs <=> ?a1 a2 a3. xs = [a1;a2;a3])
Proof
  rw [] \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `xs` \\ fs []
  \\ Cases_on `t` \\ fs [LENGTH_NIL]
  \\ Cases_on `t'` \\ fs [LENGTH_NIL]
  \\ Cases_on `t` \\ fs [LENGTH_NIL]
QED

Theorem heap_split_SOME_APPEND:
   !xs ys a h1 h2.
      heap_split a (xs ++ ys) = SOME (h1,h2) <=>
      if a < heap_length xs then
        ?ha hb. heap_split a xs = SOME (ha,hb) /\
                h1 = ha /\ h2 = hb ++ ys
      else
        ?ha hb. heap_split (a - heap_length xs) ys = SOME (ha,hb) /\
                h1 = xs ++ ha /\ h2 = hb
Proof
  fs [heap_split_APPEND_if] \\ rw []
  \\ every_case_tac \\ fs []
  \\ eq_tac \\ rw []
QED

val gc_kind_update_Ref = prove(
  ``gc_kind_inv c a sp sp1 gens
        (ha ++ DataElement (ys1 ++ y::ys2) l (RefTag,[])::hb) ==>
    gc_kind_inv c a sp sp1 gens
        (ha ++ DataElement (ys1 ++ z::ys2) l (RefTag,[])::hb)``,
  fs [gc_kind_inv_def] \\ every_case_tac \\ fs []
  \\ ntac 2 strip_tac THEN1
   (Cases_on `gens` \\ fs [gen_state_ok_def,EVERY_MEM]
    \\ rw [] \\ res_tac \\ fs [gen_start_ok_def]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ fs [heap_split_APPEND_if]
    \\ IF_CASES_TAC \\ fs []
    THEN1
     (TOP_CASE_TAC \\ fs [] \\ TOP_CASE_TAC \\ fs [] \\ rveq
      \\ rpt strip_tac \\ res_tac  \\ fs [])
    \\ fs [heap_split_def,el_length_def]
    \\ IF_CASES_TAC \\ fs []
    \\ every_case_tac \\ fs [] \\ rveq
    \\ fs [MEM_APPEND,METIS_PROVE [] ``(!x. p x \/ q x ==> d x) <=>
                                       (!x. p x ==> d x) /\
                                       (!x. q x ==> d x)``]
    \\ fs [isRef_def])
  \\ fs [heap_split_SOME_APPEND]
  \\ CASE_TAC \\ rw [] \\ fs [isRef_def]
  \\ fs [heap_split_def,el_length_def] \\ rfs []
  \\ rpt (CASE_TAC \\ fs [])
  \\ rveq \\ fs [isRef_def]);

Theorem v_all_vs_append:
  ∀x y. v_all_vs (x ++ y) = v_all_vs x ++ v_all_vs y
Proof
  ho_match_mp_tac (theorem "v_all_vs_ind")
  \\ rw [v_all_vs_def]
QED

Theorem memory_rel_Update':
   memory_rel c be ts refs sp st m dm
     ((h,w)::(RefPtr bl nn,ptr)::vars) /\
    lookup nn refs = SOME (ValueArray vals) /\
    good_dimindex (:'a) /\
    index < LENGTH vals ==>
    ?ptr_w x:'a word.
      ptr = Word ptr_w /\
      data_to_word_memoryProof$get_real_addr c st ptr_w = SOME x /\
      (x + bytes_in_word + bytes_in_word * n2w index) IN dm /\
      memory_rel c be ts (insert nn (ValueArray (LUPDATE h index vals)) refs) sp st
        ((x + bytes_in_word + bytes_in_word * n2w index =+ w) m) dm
        ((h,w)::(RefPtr bl nn,ptr)::vars)
Proof
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
  \\ `n = LENGTH l` by
   (qpat_x_assum `abs_ml_inv _ _ _ _ _ _` kall_tac
    \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def,BlockRep_def]
    \\ clean_tac
    \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
    \\ `reachable_refs (h::RefPtr bl nn::Number (&index)::MAP FST vars) refs nn` by
     (fs [reachable_refs_def] \\ qexists_tac `RefPtr bl nn` \\ fs []
      \\ fs [get_refs_def] \\ NO_TAC) \\ res_tac
    \\ pop_assum mp_tac
    \\ simp_tac std_ss [bc_ref_inv_def]
    \\ fs [FLOOKUP_DEF,RefBlock_def] \\ strip_tac \\ clean_tac
    \\ imp_res_tac heap_lookup_SPLIT
    \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
    \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR])
  \\ fs [] \\ fs [get_real_offset_thm]
  \\ fs [GSYM RefBlock_def]
  \\ imp_res_tac heap_lookup_SPLIT \\ fs [] \\ clean_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [heap_store_RefBlock_thm,LENGTH_LUPDATE] \\ clean_tac
  \\ fs [PULL_EXISTS]
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
  \\ SEP_W_TAC \\ fs [AC STAR_ASSOC STAR_COMM]
QED

Theorem memory_rel_Update:
   memory_rel c be ts refs sp st m dm
     ((h,w)::(RefPtr bl nn,ptr)::(Number (&index),i)::vars) /\
    lookup nn refs = SOME (ValueArray vals) /\
    good_dimindex (:'a) /\
    index < LENGTH vals ==>
    ?ptr_w i_w x y:'a word.
      ptr = Word ptr_w /\ i = Word i_w /\
      get_real_addr c st ptr_w = SOME x /\
      get_real_offset i_w = SOME y /\
      (x + y) IN dm /\
      memory_rel c be ts (insert nn (ValueArray (LUPDATE h index vals)) refs) sp st
        ((x + y =+ w) m) dm
        ((h,w)::(RefPtr bl nn,ptr)::(Number (&index),i)::vars)
Proof
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
   (qpat_x_assum `abs_ml_inv _ _ _ _ _ _` kall_tac
    \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def,BlockRep_def]
    \\ clean_tac
    \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
    \\ `reachable_refs (h::RefPtr bl nn::Number (&index)::MAP FST vars) refs nn` by
     (fs [reachable_refs_def] \\ qexists_tac `RefPtr bl nn` \\ fs []
      \\ fs [get_refs_def] \\ NO_TAC) \\ res_tac
    \\ pop_assum mp_tac
    \\ simp_tac std_ss [bc_ref_inv_def]
    \\ fs [FLOOKUP_DEF,RefBlock_def] \\ strip_tac \\ clean_tac
    \\ imp_res_tac heap_lookup_SPLIT
    \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
    \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
    \\ `small_int (:α) (&index)` by
     (fs [small_int_def,intLib.COOPER_CONV ``-&n <= &k:int``]
      \\ fs [good_dimindex_def,dimword_def]
      \\ rw [] \\ rfs [] \\ fs [] \\ NO_TAC)
    \\ fs [] \\ clean_tac \\ fs [word_addr_def]
    \\ fs [Smallnum_def,GSYM word_mul_n2w,word_ml_inv_num_lemma] \\ NO_TAC)
  \\ fs [] \\ fs [get_real_offset_thm]
  \\ fs [GSYM RefBlock_def]
  \\ imp_res_tac heap_lookup_SPLIT \\ fs [] \\ clean_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [heap_store_RefBlock_thm,LENGTH_LUPDATE] \\ clean_tac
  \\ fs [PULL_EXISTS]
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
  \\ SEP_W_TAC \\ fs [AC STAR_ASSOC STAR_COMM]
QED

Definition store_list_def:
  (store_list a [] (m:'a word -> 'a word_loc) dm = SOME m) /\
  (store_list a (w::ws) m dm =
     if a IN dm then
       store_list (a + bytes_in_word) ws ((a =+ w) m) dm
     else NONE)
End

Theorem store_list_append:
  ∀xs ys a dm m m1.
    store_list a (xs ++ ys) m dm = SOME m1 ⇔
    ∃m0. store_list a xs m dm = SOME m0 ∧
         store_list (a + bytes_in_word * n2w (LENGTH xs)) ys m0 dm = SOME m1
Proof
  Induct \\ fs [store_list_def]
  \\ fs [ADD1,word_add_n2w,bytes_in_word_def,word_mul_n2w,RIGHT_ADD_DISTRIB]
  \\ fs [GSYM word_add_n2w,AC CONJ_COMM CONJ_ASSOC,PULL_EXISTS]
QED

Triviality minus_lemma:
  -1w * (bytes_in_word * w) = bytes_in_word * -w
Proof
  fs []
QED

Theorem n2w_lsr_eq_0:
   n DIV 2 ** k = 0 /\ n < dimword (:'a) ==> n2w n >>> k = 0w:'a word
Proof
  rw [] \\ simp_tac std_ss [GSYM w2n_11,w2n_lsr] \\ fs []
QED

Triviality LESS_EXO_SUB:
  n < 2 ** (k - m) ==> n < 2n ** k
Proof
  rw [] \\ match_mp_tac LESS_LESS_EQ_TRANS
  \\ asm_exists_tac \\ fs []
QED

Triviality LESS_EXO_SUB_ALT:
  m <= k ==> n < 2 ** (k - m) ==> n * 2 ** m < 2n ** k
Proof
  rw [] \\ match_mp_tac LESS_LESS_EQ_TRANS
  \\ qexists_tac `2 ** (k - m) * 2 ** m`
  \\ fs [GSYM EXP_ADD]
QED

Triviality less_pow_dimindex_sub_imp:
  n < 2 ** (dimindex (:'a) - k) ==> n < dimword (:'a)
Proof
  fs [dimword_def] \\ metis_tac [LESS_EXO_SUB]
QED

Theorem encode_header_NEQ_0:
   encode_header c n k = SOME w ==> w <> 0w
Proof
  fs [encode_header_def] \\ rw []
  \\ fs [make_header_def,LET_DEF]
  \\ full_simp_tac (srw_ss()++wordsLib.WORD_BIT_EQ_ss) []
  \\ qexists_tac `0` \\ fs [] \\ EVAL_TAC
QED

Triviality encode_header_IMP:
  encode_header c tag len = SOME (hd:'a word) /\
    c.len_size + 5 < dimindex (:'a) /\ good_dimindex (:'a) ==>
    len < 2 ** (dimindex (:'a) - 4) /\
    decode_length c hd = n2w len
Proof
  fs [encode_header_def] \\ rw [make_header_def] \\ fs [decode_length_def]
  \\ `3w >>> (dimindex (:α) − c.len_size) = 0w:'a word` by
      (match_mp_tac n2w_lsr_eq_0
       \\ fs [good_dimindex_def,dimword_def]
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
  \\ fs [GSYM EXP_ADD,dimword_def]
QED

Theorem word_list_exists_thm:
   (word_list_exists a 0 = emp) /\
    (word_list_exists a (SUC n) =
     SEP_EXISTS w. one (a,w) * word_list_exists (a + bytes_in_word) n)
Proof
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
  \\ full_simp_tac(srw_ss())[word_list_def,ADD1,STAR_ASSOC,cond_STAR]
QED

Theorem word_list_exists_ADD:
   !m n a.
      word_list_exists a (m + n) =
      word_list_exists a m *
      word_list_exists (a + bytes_in_word * n2w m) n
Proof
  Induct \\ full_simp_tac(srw_ss())[word_list_exists_thm,SEP_CLAUSES,ADD_CLAUSES]
  \\ full_simp_tac(srw_ss())[STAR_ASSOC,ADD1,
        GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
QED

Theorem store_list_thm:
   !xs a frame m dm.
      (word_list_exists a (LENGTH xs) * frame) (fun2set (m,dm)) ==>
      ?m1.
        store_list a xs m dm = SOME m1 /\
        (word_list a xs * frame) (fun2set (m1,dm))
Proof
  Induct \\ fs [store_list_def,word_list_exists_thm,word_list_def,SEP_CLAUSES]
  \\ fs [SEP_EXISTS_THM,PULL_EXISTS] \\ rpt strip_tac
  \\ SEP_R_TAC \\ fs [] \\ SEP_W_TAC
  \\ SEP_F_TAC \\ rw [] \\ fs [AC STAR_COMM STAR_ASSOC]
QED

Theorem store_list_domain:
   ∀a xs m dm m1.
   store_list a xs m dm = SOME m1 ==>
   ∀n. n < LENGTH xs ==> a + n2w n * bytes_in_word ∈ dm
Proof
  Induct_on`xs`
  \\ rw[store_list_def] \\ res_tac
  \\ Cases_on`n` \\ fs[ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
QED

Theorem store_list_append_imp:
   ∀w1 a m dm m' w2.
   store_list a (w1 ++ w2) m dm = SOME m' ⇒
   ∃m''. store_list a w1 m dm = SOME m'' ∧
         store_list (a + n2w (LENGTH w1) * bytes_in_word) w2 m'' dm = SOME m'
Proof
  Induct \\ rw[store_list_def]
  \\ first_x_assum drule \\ rw[] \\ rw[]
  \\ rw[ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
QED

Theorem store_list_update_m_outside:
   ∀ws a m dm m'.
   store_list a ws m dm = SOME m' ∧
   (∀i. i < LENGTH ws ⇒ a + n2w i * bytes_in_word ≠ a')
   ⇒
   store_list a ws ((a' =+ v) m) dm = SOME ((a' =+ v) m')
Proof
  Induct \\ rw[store_list_def]
  \\ first_x_assum drule
  \\ impl_tac
  >- (
    qx_gen_tac`i` \\ first_x_assum(qspec_then`SUC i`mp_tac)
    \\ simp[ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB] )
  \\ disch_then((SUBST1_TAC o SYM))
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ match_mp_tac UPDATE_COMMUTES
  \\ first_x_assum(qspec_then`0`mp_tac)
  \\ simp[]
QED

Theorem word_payload_IMP:
   word_payload addrs ll tags tt1 conf = (h,ts,T) ==> LENGTH ts = ll
Proof
  Cases_on `tags` \\ full_simp_tac(srw_ss())[word_payload_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED

Theorem word_el_IMP_word_list_exists:
   !temp p curr.
      (p * word_el curr temp conf) s ==>
      (p * word_list_exists curr (el_length temp)) s
Proof
  Cases \\ fs[word_el_def,el_length_def,GSYM ADD1,word_list_exists_thm]
  THEN1 (full_simp_tac(srw_ss())[SEP_CLAUSES,SEP_EXISTS_THM] \\ metis_tac [])
  \\ Cases_on `b`
  \\ fs[word_el_def,el_length_def,GSYM ADD1,word_list_exists_thm,LET_THM]
  \\ srw_tac[][] \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR] \\ srw_tac[][]
  \\ fs[word_list_def,SEP_CLAUSES,SEP_EXISTS_THM,word_list_exists_def]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ imp_res_tac word_payload_IMP \\ asm_exists_tac \\ fs [] \\ metis_tac []
QED

Theorem word_heap_IMP_word_list_exists:
   !temp p curr.
      (p * word_heap curr temp conf) s ==>
      (p * word_list_exists curr (heap_length temp)) s
Proof
  Induct \\ full_simp_tac(srw_ss())[heap_length_def,
              word_heap_def,word_list_exists_thm]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_el_def,word_list_exists_ADD]
  \\ full_simp_tac(srw_ss())[STAR_ASSOC] \\ res_tac
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [STAR_COMM] \\ full_simp_tac(srw_ss())[STAR_ASSOC]
  \\ metis_tac [word_el_IMP_word_list_exists]
QED

Triviality EVERY2_f_EQ:
  !rs ws f. EVERY2 (\v w. f v = w) rs ws <=> MAP f rs = ws
Proof
  Induct \\ fs [] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
QED

Theorem word_heap_heap_expand:
   word_heap a (heap_expand n) conf = word_list_exists a n
Proof
  Cases_on `n` \\ full_simp_tac(srw_ss())[heap_expand_def]
  \\ fs [word_heap_def,word_list_exists_def,LENGTH_NIL,FUN_EQ_THM,ADD1,
         SEP_EXISTS_THM,cond_STAR,word_list_def,word_el_def,SEP_CLAUSES]
QED

Triviality get_lowerbits_or_1:
  get_lowerbits c v = (get_lowerbits c v || 1w)
Proof
  Cases_on `v` \\ fs [get_lowerbits_def]
QED

Theorem memory_rel_Word64_alt:
   memory_rel c be ts refs sp st m dm (vs ++ vars) ∧ good_dimindex (:'a) ∧
   (Word64Rep (:'a) w64 : 'a ml_el) = DataElement [] (LENGTH ws) (Word64Tag,ws) ∧
   LENGTH ws < sp ∧
   encode_header c 3 (LENGTH ws) = SOME hd
   ⇒
   ∃ne curr m1.
     FLOOKUP st NextFree = SOME (Word ne) ∧
     FLOOKUP st CurrHeap = SOME (Word curr) ∧
     store_list ne (Word hd::ws) m dm = SOME m1 ∧
     memory_rel c be ts refs (sp - (LENGTH ws + 1))
        (st |+ (NextFree,Word (ne + bytes_in_word * n2w (LENGTH ws + 1)))) m1  dm
        ((Word64 w64, make_ptr c (ne - curr) (0w:'a word) (LENGTH ws))::vars)
Proof
  rw[memory_rel_def,word_ml_inv_def,PULL_EXISTS]
  \\ imp_res_tac EVERY2_SWAP
  \\ imp_res_tac EVERY2_APPEND_IMP_APPEND
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs[] \\ clean_tac
  \\ drule (GEN_ALL word64_alt_thm) \\ fs[]
  \\ disch_then drule \\ impl_tac >- fs[] \\ strip_tac
  \\ first_assum(part_match_exists_tac
       (find_term (same_const``abs_ml_inv`` o #1 o strip_comb)) o concl)
  \\ simp[]
  \\ fs[heap_in_memory_store_def,FLOOKUP_UPDATE]
  \\ imp_res_tac heap_store_unused_alt_IMP_length \\ fs[]
  \\ fs[heap_store_unused_alt_def]
  \\ rfs[el_length_def]
  \\ every_case_tac \\ fs[]
  \\ imp_res_tac heap_lookup_SPLIT
  \\ clean_tac
  \\ qpat_x_assum`_ (fun2set _)`mp_tac
  \\ ONCE_REWRITE_TAC[STAR_COMM]
  \\ ONCE_REWRITE_TAC[CONS_APPEND]
  \\ simp[word_heap_APPEND]
  \\ qmatch_goalsub_rename_tac`[Unused (ex + sp1 - 1)]`
  \\ qpat_abbrev_tac`hex = [Unused _]`
  \\ `hex = heap_expand (ex + sp1)` by (simp[Abbr`hex`,heap_expand_def] \\ NO_TAC)
  \\ qunabbrev_tac`hex`
  \\ simp[word_heap_heap_expand,heap_length_heap_expand]
  \\ qpat_abbrev_tac`len = LENGTH ws + 1`
  \\ simp[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,minus_lemma]
  \\ REWRITE_TAC[GSYM WORD_LEFT_ADD_DISTRIB,GSYM WORD_ADD_ASSOC]
  \\ REWRITE_TAC[WORD_ADD_ASSOC,word_add_n2w]
  \\ `len ≤ ex` by simp[Abbr`len`]
  \\ `ex + sp1 = len + (ex + sp1 - len)` by simp[]
  \\ pop_assum SUBST1_TAC
  \\ REWRITE_TAC[word_list_exists_ADD]
  \\ qmatch_goalsub_abbrev_tac`word_list_exists x len`
  \\ qpat_abbrev_tac `ll = word_list_exists x _`
  \\ fs [AC STAR_COMM STAR_ASSOC]
  \\ qunabbrev_tac `ll`
  \\ strip_tac
  \\ `len = LENGTH (Word hd::ws)` by simp[Abbr`len`]
  \\ qunabbrev_tac `len` \\ pop_assum SUBST_ALL_TAC
  \\ drule store_list_thm \\ strip_tac
  \\ asm_exists_tac \\ fs[]
  \\ fs[heap_store_lemma]
  \\ clean_tac
  \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ qunabbrev_tac `x` \\ fs []
  \\ conj_tac
  >- (pop_assum mp_tac
     \\ simp[word_heap_APPEND,heap_length_APPEND,
             heap_length_heap_expand,word_heap_heap_expand]
     \\ simp[AC STAR_ASSOC STAR_COMM]
     \\ simp[word_list_def,word_heap_def,SEP_CLAUSES]
     \\ simp[word_el_def,word_payload_def]
     \\ imp_res_tac encode_header_IMP
     \\ fs[encode_header_def,SEP_CLAUSES]
     \\ simp[word_list_def]
     \\ simp[Q.SPEC`[_]`heap_length_def,el_length_def,ADD1]
     \\ simp[AC STAR_ASSOC STAR_COMM,ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  \\ simp[word_addr_def,make_ptr_def,get_addr_def,
           get_lowerbits_def,bytes_in_word_mul_eq_shift]
  \\ imp_res_tac EVERY2_SWAP \\ fs[]
QED

Theorem memory_rel_WordOp64_alt =
  memory_rel_Word64_alt |> Q.GEN`vs` |> Q.SPEC`[w1;w2]`
  |> CONV_RULE(LAND_CONV(SIMP_CONV(srw_ss())[]))

Triviality IMP_memory_rel_bignum_alt:
  memory_rel c be ts refs sp st m dm (vs ++ vars) ∧
   good_dimindex (:α) ∧ ¬small_int (:α) i ∧
   (Bignum i :α ml_el) = DataElement [] (LENGTH ws) (NumTag sign,MAP Word ws) ∧
   LENGTH ws < sp ∧
   encode_header c (w2n ((b2w sign <<2 || 3w):α word)) (LENGTH ws) =
     SOME (hd:α word) ⇒
   ∃next curr m1.
     FLOOKUP st NextFree = SOME (Word next) ∧
     FLOOKUP st CurrHeap = SOME (Word curr) ∧
     (store_list next (MAP Word (hd::ws)) m dm = SOME m1 ∧
      memory_rel c be ts refs (sp - (LENGTH ws + 1))
        (st |+ (NextFree,Word (next + bytes_in_word * n2w (LENGTH ws + 1))))
        m1 dm ((Number i,make_ptr c (next - curr) (0w:α word) (LENGTH ws))::vars))
Proof
  rw[memory_rel_def,word_ml_inv_def,PULL_EXISTS]
  \\ imp_res_tac EVERY2_SWAP
  \\ imp_res_tac EVERY2_APPEND_IMP_APPEND
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs[] \\ clean_tac
  \\ drule (GEN_ALL bignum_alt_thm) \\ fs[]
  \\ disch_then drule
  \\ disch_then drule \\ impl_tac >- fs[] \\ strip_tac
  \\ first_assum(part_match_exists_tac
        (find_term (same_const``abs_ml_inv`` o #1 o strip_comb)) o concl)
  \\ simp[]
  \\ fs[heap_in_memory_store_def,FLOOKUP_UPDATE]
  \\ imp_res_tac heap_store_unused_alt_IMP_length \\ fs[]
  \\ fs[heap_store_unused_alt_def]
  \\ rfs[el_length_def]
  \\ every_case_tac \\ fs[]
  \\ imp_res_tac heap_lookup_SPLIT
  \\ clean_tac
  \\ qpat_x_assum`_ (fun2set _)`mp_tac
  \\ ONCE_REWRITE_TAC[STAR_COMM]
  \\ ONCE_REWRITE_TAC[CONS_APPEND]
  \\ simp[word_heap_APPEND]
  \\ qmatch_goalsub_rename_tac`[Unused (ex + sp1 - 1)]`
  \\ qpat_abbrev_tac`hex = [Unused _]`
  \\ `hex = heap_expand (ex + sp1)` by (simp[Abbr`hex`,heap_expand_def] \\ fs [])
  \\ qunabbrev_tac`hex`
  \\ simp[word_heap_heap_expand,heap_length_heap_expand]
  \\ qpat_abbrev_tac`len = LENGTH ws + 1`
  \\ simp[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,minus_lemma]
  \\ REWRITE_TAC[GSYM WORD_LEFT_ADD_DISTRIB,GSYM WORD_ADD_ASSOC]
  \\ REWRITE_TAC[WORD_ADD_ASSOC,word_add_n2w]
  \\ `len ≤ ex` by simp[Abbr`len`]
  \\ `ex + sp1 = len + (ex + sp1 - len)` by simp[]
  \\ pop_assum SUBST1_TAC
  \\ REWRITE_TAC[word_list_exists_ADD]
  \\ qmatch_goalsub_abbrev_tac`word_list_exists x len`
  \\ simp[GSYM STAR_ASSOC]
  \\ simp [AC STAR_COMM STAR_ASSOC]
  \\ once_rewrite_tac [STAR_COMM]
  \\ rewrite_tac [GSYM STAR_ASSOC]
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`Word hd::_`
  \\ `len = LENGTH (Word hd::MAP Word ws)` by simp[Abbr`len`]
  \\ qunabbrev_tac `len` \\ pop_assum SUBST_ALL_TAC
  \\ drule store_list_thm \\ strip_tac
  \\ asm_exists_tac \\ fs[]
  \\ fs[heap_store_lemma]
  \\ clean_tac
  \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ conj_tac
  >- (pop_assum mp_tac
     \\ simp[word_heap_APPEND,heap_length_APPEND,
             heap_length_heap_expand,word_heap_heap_expand]
     \\ simp[AC STAR_ASSOC STAR_COMM]
     \\ simp[word_list_def,word_heap_def,SEP_CLAUSES]
     \\ simp[word_el_def,word_payload_def]
     \\ imp_res_tac encode_header_IMP
     \\ fs[encode_header_def,SEP_CLAUSES]
     \\ simp[word_list_def]
     \\ simp[Q.SPEC`[_]`heap_length_def,el_length_def,ADD1]
     \\ unabbrev_all_tac
     \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
     \\ simp[AC STAR_ASSOC STAR_COMM])
  \\ simp[word_addr_def,make_ptr_def,get_addr_def,
          get_lowerbits_def,bytes_in_word_mul_eq_shift]
  \\ imp_res_tac EVERY2_SWAP \\ fs[]
QED

Theorem IMP_memory_rel_bignum_alt =
  IMP_memory_rel_bignum_alt |> Q.INST [`vs`|->`[]`] |> SIMP_RULE std_ss [APPEND]

Theorem memory_rel_Cons1:
   memory_rel c be ts refs sp st m dm (ZIP (vals,ws) ++ vars) /\
    LENGTH vals = LENGTH (ws:'a word_loc list) /\ vals <> [] /\
    encode_header c (4 * tag) (LENGTH ws) = SOME hd /\
    LENGTH ws < sp /\ good_dimindex (:'a) ==>
    ?free (curr:'a word) m1.
      FLOOKUP st NextFree = SOME (Word free) /\
      FLOOKUP st CurrHeap = SOME (Word curr) /\
      let w = free + bytes_in_word * n2w (LENGTH ws + 1) in
        store_list free (Word hd::ws) m dm = SOME m1 /\
        memory_rel c be (ts+1) refs (sp - (LENGTH ws + 1))
          (st |+ (NextFree,Word w)) m1 dm
          ((Block ts tag vals,make_cons_ptr c (free - curr) tag (LENGTH ws))::vars)
Proof
  simp_tac std_ss [LET_THM]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ fs [memory_rel_def,PULL_EXISTS] \\ rw []
  \\ fs [word_ml_inv_def,PULL_EXISTS] \\ clean_tac
  \\ fs [MAP_ZIP]
  \\ drule (GEN_ALL cons_thm_alt)
  \\ disch_then (qspecl_then [`tag`] strip_assume_tac)
  \\ rfs [] \\ fs [] \\ clean_tac
  \\ rewrite_tac [GSYM CONJ_ASSOC]
  \\ once_rewrite_tac [METIS_PROVE [] ``b1 /\ b2 /\ b3 <=> b2 /\ b1 /\ b3:bool``]
  \\ fs []
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
  \\ fs [LIST_REL_APPEND_EQ,minus_lemma]
  \\ fs [bytes_in_word_mul_eq_shift]
  \\ fs [GSYM bytes_in_word_mul_eq_shift]
  \\ `LENGTH ws + 1 <= sp' + sp1` by decide_tac
  \\ pop_assum mp_tac \\ simp_tac std_ss [Once LESS_EQ_EXISTS] \\ strip_tac
  \\ clean_tac \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [heap_store_unused_alt_def,el_length_def]
  \\ every_case_tac \\ fs []
  \\ imp_res_tac heap_lookup_SPLIT \\ fs [] \\ clean_tac
  \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ fs [heap_store_lemma] \\ clean_tac \\ fs []
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def,
         SEP_CLAUSES,word_heap_heap_expand]
  \\ fs [word_list_exists_ADD |> Q.SPECL [`m+1`,`n`]
         |> ONCE_REWRITE_RULE [ADD_COMM]]
  \\ `(make_header c (n2w tag << 2) (LENGTH ws)) = hd` by
       (fs [encode_header_def,make_header_def] \\ every_case_tac \\ fs []
        \\ fs [WORD_MUL_LSL,word_mul_n2w,EXP_ADD] \\ NO_TAC)
  \\ fs [] \\ drule encode_header_IMP \\ fs [] \\ strip_tac
  \\ simp [WORD_MUL_LSL,word_mul_n2w]
  \\ fs [SEP_CLAUSES,STAR_ASSOC]
  \\ `LENGTH ws + 1 = LENGTH (Word hd::ws)` by fs []
  \\ full_simp_tac std_ss []
  \\ qpat_x_assum `_ (fun2set (m,dm))` mp_tac
  \\ qpat_abbrev_tac `ll = word_list_exists _ (LENGTH _)`
  \\ simp_tac std_ss [AC STAR_COMM STAR_ASSOC]
  \\ qunabbrev_tac `ll` \\ strip_tac
  \\ drule store_list_thm
  \\ strip_tac \\ fs []
  \\ fs [EVERY2_f_EQ] \\ clean_tac \\ fs []
  \\ fs [el_length_def,heap_length_APPEND,heap_length_heap_expand,
         GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,ADD1]
  \\ fs [AC STAR_ASSOC STAR_COMM] \\ fs [STAR_ASSOC]
  \\ pop_assum mp_tac \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ fs [AC STAR_ASSOC STAR_COMM] \\ fs [STAR_ASSOC]
  \\ rpt strip_tac
  \\ simp [Once get_lowerbits_or_1]
  \\ fs [heap_length_def,el_length_def]
  \\ pop_assum mp_tac \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ fs [AC STAR_ASSOC STAR_COMM] \\ fs [STAR_ASSOC]
  \\ fs [el_length_def,heap_length_APPEND,heap_length_heap_expand,
         GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,ADD1]
  \\ fs [AC STAR_ASSOC STAR_COMM] \\ fs [STAR_ASSOC]
QED

Theorem memory_rel_Cons_empty:
   memory_rel c be ts refs sp st m (dm:'a word set) vars /\
    tag < dimword (:α) DIV 16 /\ good_dimindex (:'a) ==>
    memory_rel c be ts refs sp st m dm
      ((Block 0 tag [],Word (BlockNil tag))::vars)
Proof
  fs [memory_rel_def] \\ rw []
  \\ asm_exists_tac \\ fs []
  \\ fs [word_ml_inv_def]
  \\ rpt_drule cons_thm_EMPTY
  \\ disch_then strip_assume_tac
  \\ asm_exists_tac \\ fs []
  \\ fs [word_addr_def,BlockNil_def,WORD_MUL_LSL,word_mul_n2w]
  \\ fs [GSYM word_mul_n2w]
  \\ match_mp_tac BlockNil_and_lemma \\ fs []
QED

Theorem memory_rel_Ref:
   memory_rel c be ts refs sp st m dm (ZIP (vals,ws) ++ vars) /\
    LENGTH vals = LENGTH (ws:'a word_loc list) /\
    encode_header c 2 (LENGTH ws) = SOME hd /\ ~(new IN (domain refs)) /\
    LENGTH ws < sp /\ good_dimindex (:'a) ==>
    ?eoh (curr:'a word) trig m1.
      FLOOKUP st EndOfHeap = SOME (Word eoh) /\
      FLOOKUP st TriggerGC = SOME (Word trig) /\
      FLOOKUP st CurrHeap = SOME (Word curr) /\
      let w = eoh - bytes_in_word * n2w (LENGTH ws + 1) in
      let w1 = trig - bytes_in_word * n2w (LENGTH ws + 1) in
        store_list w (Word hd::ws) m dm = SOME m1 /\
        memory_rel c be ts (insert new (ValueArray vals) refs) (sp - (LENGTH ws + 1))
          (st |+ (EndOfHeap,Word w) |+ (TriggerGC,Word w1)) m1 dm
          ((RefPtr T new,make_ptr c (w - curr) 0w (LENGTH ws))::vars)
Proof
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
  \\ `LENGTH ws + 1 <= sp' + sp1` by decide_tac
  \\ pop_assum mp_tac \\ simp_tac std_ss [LESS_EQ_EXISTS]
  \\ strip_tac \\ clean_tac \\ fs []
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [LIST_REL_APPEND_EQ]
  \\ fs [WORD_LEFT_ADD_DISTRIB,get_addr_def,make_ptr_def,get_lowerbits_def]
  \\ fs [bytes_in_word_mul_eq_shift]
  \\ fs [GSYM bytes_in_word_mul_eq_shift,GSYM word_add_n2w]
  \\ fs [heap_store_unused_def,el_length_def]
  \\ fs [GSYM word_add_n2w,wordsTheory.n2w_sub,WORD_LEFT_ADD_DISTRIB]
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
  \\ fs [AC STAR_ASSOC STAR_COMM] \\ fs [STAR_ASSOC]
QED

Theorem memory_rel_write:
   memory_rel c be ts refs sp st m dm vars ==>
    ?(free:'a word).
      FLOOKUP st NextFree = SOME (Word free) /\
      !n.
        n < sp ==>
        let a = free + bytes_in_word * n2w n in
          a IN dm /\ memory_rel c be ts refs sp st ((a =+ w) m) dm vars
Proof
  fs [LET_THM,memory_rel_def,heap_in_memory_store_def]
  \\ strip_tac \\ fs [word_ml_inv_def,abs_ml_inv_def]
  \\ fs [unused_space_inv_def]
  \\ ntac 2 strip_tac \\ fs []
  \\ drule heap_lookup_SPLIT
  \\ strip_tac \\ fs [] \\ rveq
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_list_exists_def]
  \\ fs [SEP_CLAUSES,SEP_EXISTS_THM]
  \\ reverse (Cases_on `LENGTH xs = sp' + sp1`)
  THEN1 (fs [SEP_CLAUSES] \\ fs [SEP_F_def])
  \\ fs [SEP_CLAUSES] \\ fs [SEP_F_def] \\ rveq
  \\ `n < LENGTH xs` by decide_tac
  \\ drule LESS_LENGTH
  \\ strip_tac \\ rveq \\ fs [word_list_def,word_list_APPEND]
  \\ conj_tac THEN1 (fs [] \\ SEP_R_TAC \\ fs [])
  \\ qexists_tac `ha ++ [Unused (LENGTH ys1 + SUC (LENGTH ys2) − 1)] ++ hb`
  \\ qexists_tac `limit`
  \\ qexists_tac `heap_length ha`
  \\ qexists_tac `sp'`
  \\ qexists_tac `sp1`
  \\ qexists_tac `gens`
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_list_exists_def,
         SEP_CLAUSES,SEP_EXISTS_THM,PULL_EXISTS]
  \\ qexists_tac `ys1 ++ w::ys2` \\ fs [SEP_CLAUSES]
  \\ qexists_tac `hs` \\ fs []
  \\ fs [word_list_def,word_list_APPEND]
  \\ SEP_WRITE_TAC
QED

Theorem word_list_AND_word_list_exists_IMP:
   !ws aa frame n.
      (word_list aa ws * SEP_T) (fun2set (m,dm)) /\
      (word_list_exists aa n * frame) (fun2set (m,dm)) /\
      LENGTH ws <= n ==>
      (word_list aa ws *
       word_list_exists (aa + bytes_in_word * n2w (LENGTH ws)) (n - LENGTH ws) *
       frame) (fun2set (m,dm))
Proof
  Induct \\ fs [word_list_def,SEP_CLAUSES] \\ rw []
  \\ Cases_on `n` \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ qsuff_tac
  `(word_list (aa + bytes_in_word) ws *
     word_list_exists ((aa + bytes_in_word) + bytes_in_word * n2w (LENGTH ws))
   (n' − LENGTH ws) * (one (aa,h) * frame)) (fun2set (m,dm))`
  THEN1 fs [AC STAR_ASSOC STAR_COMM]
  \\ first_x_assum match_mp_tac
  \\ conj_tac THEN1
   (ntac 2 (pop_assum kall_tac)
    \\ pop_assum mp_tac
    \\ fs [AC STAR_ASSOC STAR_COMM] \\ fs [STAR_ASSOC]
    \\ qspec_tac (`fun2set (m,dm)`,`x`)
    \\ fs [GSYM SEP_IMP_def]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ match_mp_tac SEP_IMP_STAR
    \\ fs [SEP_IMP_REFL] \\ fs [SEP_IMP_def,SEP_T_def])
  \\ `m = (aa =+ h) m` by
         (fs [FUN_EQ_THM,APPLY_UPDATE_THM] \\ rw [] \\ SEP_R_TAC \\ NO_TAC)
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs [GSYM ADD1,word_list_exists_thm,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ SEP_WRITE_TAC
QED

Theorem memory_rel_Cons_alt:
   memory_rel c be ts refs sp st m dm (ZIP (vals,ws) ++ vars) /\
    LENGTH vals = LENGTH (ws:'a word_loc list) /\ vals <> [] /\
    encode_header c (4 * tag) (LENGTH ws) = SOME hd /\
    LENGTH ws < sp /\ good_dimindex (:'a) ==>
    ?free (curr:'a word) m1.
      FLOOKUP st NextFree = SOME (Word free) /\
      FLOOKUP st CurrHeap = SOME (Word curr) /\
      ((word_list free (Word hd::ws) * SEP_T) (fun2set(m,dm)) ==>
       memory_rel c be (ts+1) refs (sp - (LENGTH ws + 1))
         (st |+ (NextFree,Word (free + bytes_in_word * n2w (LENGTH ws + 1)))) m dm
         ((Block ts tag vals,make_cons_ptr c (free - curr) tag (LENGTH ws))::vars))
Proof
  simp_tac std_ss [LET_THM]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ fs [memory_rel_def,PULL_EXISTS] \\ rw []
  \\ fs [word_ml_inv_def,PULL_EXISTS] \\ clean_tac
  \\ fs [MAP_ZIP]
  \\ drule (GEN_ALL cons_thm_alt)
  \\ disch_then (qspecl_then [`tag`] strip_assume_tac)
  \\ rfs [] \\ fs [] \\ clean_tac
  \\ `?free curr. FLOOKUP st NextFree = SOME (Word free) ∧
                  FLOOKUP st CurrHeap = SOME (Word curr)` by
       (fs [heap_in_memory_store_def] \\ NO_TAC) \\ fs []
  \\ strip_tac
  \\ rewrite_tac [GSYM CONJ_ASSOC]
  \\ once_rewrite_tac [METIS_PROVE [] ``b2 /\ b1 /\ b3 <=> b1 /\ b2 /\ b3:bool``]
  \\ fs []
  \\ asm_exists_tac \\ fs [word_addr_def]
  \\ fs [heap_in_memory_store_def,FLOOKUP_UPDATE]
  \\ qpat_abbrev_tac `ll = el_length _`
  \\ `ll = LENGTH ws + 1` by (UNABBREV_ALL_TAC \\ EVAL_TAC \\ fs [] \\ NO_TAC)
  \\ UNABBREV_ALL_TAC \\ fs []
  \\ qpat_abbrev_tac `ll = el_length _`
  \\ `ll = LENGTH ws + 1` by (UNABBREV_ALL_TAC \\ EVAL_TAC \\ fs [] \\ NO_TAC)
  \\ UNABBREV_ALL_TAC \\ fs []
  \\ fs [WORD_LEFT_ADD_DISTRIB,get_addr_def,make_cons_ptr_def,get_lowerbits_def]
  \\ fs [el_length_def,BlockRep_def]
  \\ imp_res_tac heap_store_unused_alt_IMP_length \\ fs []
  \\ fs [LIST_REL_APPEND_EQ,minus_lemma]
  \\ fs [bytes_in_word_mul_eq_shift]
  \\ fs [GSYM bytes_in_word_mul_eq_shift]
  \\ conj_tac THEN1 (fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  \\ fs [heap_store_unused_alt_def,el_length_def]
  \\ every_case_tac \\ fs []
  \\ imp_res_tac heap_lookup_SPLIT \\ fs [] \\ clean_tac
  \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ fs [heap_store_lemma] \\ clean_tac \\ fs []
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def,
         SEP_CLAUSES,word_heap_heap_expand]
  \\ simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ fs [word_list_exists_ADD |> Q.SPECL [`m`,`n+1`]]
  \\ `(make_header c (n2w tag << 2) (LENGTH ws)) = hd` by
       (fs [encode_header_def,make_header_def] \\ every_case_tac \\ fs []
        \\ fs [WORD_MUL_LSL,word_mul_n2w,EXP_ADD] \\ NO_TAC)
  \\ fs [] \\ drule encode_header_IMP \\ fs [] \\ strip_tac
  \\ simp [WORD_MUL_LSL,word_mul_n2w]
  \\ qabbrev_tac `aa = (curr + bytes_in_word * n2w (heap_length ha))`
  \\ fs [el_length_def] \\ fs [word_list_exists_ADD]
  \\ fs [AC STAR_COMM STAR_ASSOC]
  \\ drule (GEN_ALL word_list_AND_word_list_exists_IMP
       |> SIMP_RULE std_ss [Once STAR_COMM])
  \\ disch_then drule \\ fs []
  \\ unabbrev_all_tac
  \\ fs [heap_length_APPEND,el_length_def]
  \\ fs [heap_length_def,el_length_def]
  \\ fs [GSYM heap_length_def,ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [heap_length_heap_expand]
  \\ fs [EVERY2_f_EQ] \\ rveq \\ fs []
  \\ fs [AC STAR_ASSOC STAR_COMM] \\ fs [STAR_ASSOC]
  \\ fs [wordsTheory.n2w_sub,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ `(sp' + sp1 − (LENGTH rs + 1)) = (sp' − (LENGTH rs + 1)) + sp1` by fs []
  \\ asm_rewrite_tac [word_list_exists_ADD]
  \\ simp_tac std_ss [AC STAR_ASSOC STAR_COMM]
  \\ pop_assum kall_tac
  \\ fs [wordsTheory.n2w_sub,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ simp_tac std_ss [AC STAR_ASSOC STAR_COMM]
QED

Theorem memory_rel_REPLICATE:
   memory_rel c be ts refs sp st m dm ((v,w)::vars) ==>
    memory_rel c be ts refs sp st m dm (REPLICATE n (v,w) ++ vars)
Proof
  match_mp_tac memory_rel_rearrange \\ fs [] \\ rw [] \\ fs []
  \\ Induct_on `n` \\ fs [REPLICATE] \\ rw [] \\ fs []
QED

Theorem memory_rel_RefArray =
  memory_rel_Ref
  |> Q.INST [`vals`|->`REPLICATE n v`,`ws`|->`REPLICATE n w`]
  |> SIMP_RULE std_ss [ZIP_REPLICATE,LENGTH_REPLICATE]
  |> REWRITE_RULE [GSYM AND_IMP_INTRO]
  |> (fn th => MATCH_MP th (UNDISCH memory_rel_REPLICATE))
  |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]

Definition word_of_byte_def:
  word_of_byte (w:'a word) =
    let w = (w << 8 || w) in
    let w = (w << 16 || w) in
      if dimindex (:'a) = 32 then w else w << 32 || w
End

Theorem ADD_DIV_EQ =
  LIST_CONJ
  [GSYM ADD_DIV_ADD_DIV,
   ONCE_REWRITE_RULE [ADD_COMM] (GSYM ADD_DIV_ADD_DIV)]

Triviality set_byte_word_of_byte:
  good_dimindex (:'a) ==>
    set_byte a w (word_of_byte ((w2w w):'a word)) be = word_of_byte (w2w w)
Proof
  fs [set_byte_def,good_dimindex_def] \\ rw [] \\ fs []
  \\ fs [word_of_byte_def]
  \\ `?k. byte_index a be = 8 * k /\ k < (dimindex (:'a) DIV 8)` by
        (fs [byte_index_def] \\ rw [])
  \\ rfs [DECIDE ``n < 4 <=> n = 0 \/ n = 1 \/ n = 2 \/ n = 3n``,
          DECIDE ``n < 8 <=> n = 0 \/ n = 1 \/ n = 2 \/ n = 3n \/
                              n = 4 \/ n = 5 \/ n = 6 \/ n = 7n``]
  \\ rveq \\ fs []
  \\ fs [fcpTheory.CART_EQ,word_or_def,word_lsl_def,fcpTheory.FCP_BETA,
        word_slice_alt_def,w2w] \\ rw [] \\ EQ_TAC \\ rw [] \\ fs []
QED

Theorem w2w_word_of_byte_w2w:
   good_dimindex(:'a) ==>
   w2w (word_of_byte (w2w w:'a word)):word8 = w
Proof
  rw[word_of_byte_def,good_dimindex_def]
  \\ srw_tac[wordsLib.WORD_BIT_EQ_ss][]
QED

Triviality write_bytes_REPLICATE:
  !n m.
      good_dimindex (:'a) ==>
      write_bytes (REPLICATE m w) (REPLICATE n (word_of_byte (w2w w))) be =
      REPLICATE n (word_of_byte ((w2w w):'a word))
Proof
  Induct \\ fs [write_bytes_def,REPLICATE,DROP_REPLICATE] \\ rw []
  \\ qspec_tac (`m`,`m`)
  \\ qspec_tac (`0w:'a word`,`a`)
  \\ qspec_tac (`dimindex (:α) DIV 8`,`n`)
  \\ Induct
  \\ simp [Once bytes_to_word_def,REPLICATE] \\ Cases_on `m`
  \\ fs [REPLICATE,set_byte_word_of_byte]
QED

Theorem IMP_EXP_LESS:
   m <= l ==> 2n ** m <= 2 ** l
Proof
  simp [Once LESS_EQ_EXISTS] \\ rw []
QED

Triviality shift_shift_lemma:
  l = k + shift (:'a) /\ t < k /\ n DIV i < 2 ** t /\ l = dimindex (:'a) /\
    i = 2 ** shift (:'a) /\ n < dimword (:'a) ==>
    n2w n << (k - t) >>> (l - t) = (n2w (n DIV i)):'a word
Proof
  rw [] \\ `k + shift (:α) − t = (k - t) + shift (:'a)` by decide_tac
  \\ pop_assum (fn th => rewrite_tac [th,GSYM LSR_ADD])
  \\ qsuff_tac `w2n ((n2w n):'a word) * 2 ** (k - t) < dimword (:'a)`
  THEN1
   (strip_tac \\ drule lsl_lsr \\ simp_tac std_ss [] \\ rw []
    \\ rewrite_tac [GSYM w2n_11,w2n_lsr] \\ fs []
    \\ `(n DIV 2 ** shift (:α)) < dimword (:α)` by
     (match_mp_tac LESS_LESS_EQ_TRANS
      \\ asm_exists_tac \\ fs [] \\ rewrite_tac [dimword_def]
      \\ match_mp_tac IMP_EXP_LESS \\ decide_tac)
    \\ fs [])
  \\ fs [DIV_LT_X]
  \\ `t <= k` by decide_tac
  \\ fs [LESS_EQ_EXISTS] \\ rw []
  \\ fs [dimword_def,EXP_ADD]
  \\ simp_tac bool_ss [Once MULT_COMM]
  \\ rewrite_tac [LT_MULT_LCANCEL,GSYM MULT_ASSOC] \\ fs []
QED

Theorem write_bytes_APPEND:
   !xs ys vals be.
      write_bytes vals (xs ++ (ys:'a word list)) be =
      write_bytes vals xs be ++
      write_bytes (DROP ((dimindex (:α) DIV 8) * LENGTH xs) vals) ys be
Proof
  Induct \\ fs [write_bytes_def,ADD1,RIGHT_ADD_DISTRIB,DROP_DROP_T]
QED

Theorem set_byte_sort:
   !n1 n2.
      set_byte (n2w n1) b1 (set_byte (n2w n2:'a word) b2 w be) be =
      if n1 = n2 then set_byte (n2w n1) b1 w be else
      if n1 < dimindex(:α) DIV 8 /\ n2 < dimindex(:α) DIV 8 /\
         good_dimindex(:α) /\ n2 <> n1
      then
        set_byte (n2w n2) b2 (set_byte (n2w n1) b1 w be) be
      else
        set_byte (n2w n1) b1 (set_byte (n2w n2) b2 w be) be
Proof
  rw [] THEN1
   (fs [set_byte_def]
    \\ full_simp_tac (std_ss++wordsLib.WORD_BIT_EQ_ss) [word_slice_alt_def]
    \\ rw [] \\ eq_tac \\ rw []
    \\ TRY (`F` by decide_tac)
    \\ metis_tac [])
  \\ fs [set_byte_def]
  \\ full_simp_tac (std_ss++wordsLib.WORD_BIT_EQ_ss) [word_slice_alt_def]
  \\ rw [] \\ eq_tac \\ rw []
  \\ TRY (metis_tac [])
  \\ fs [byte_index_def]
  \\ fs[good_dimindex_def] \\ rfs[dimword_def]
  \\ Cases_on `be` \\ fs []
  \\ fs [LESS_4,LESS_8] \\ rfs []
QED

val (set_byte_sort_dec,set_byte_sort_asc) = let
  fun cross [] ys = []
    | cross (x::xs) ys = map (fn y => (x,y)) ys :: cross xs ys
  val xs = [0,1,2,3,4,5,6,7]
  val ys = cross xs xs |> Lib.flatten
  fun f (x,y) =
    SPECL [numSyntax.term_of_int x,numSyntax.term_of_int y] set_byte_sort
    |> SIMP_RULE (srw_ss()) [good_dimindex_def]
  val ts1 = filter (fn (x,y) => x < y) ys
  val ts2 = filter (fn (x,y) => y < x) ys
  in (LIST_CONJ (map f ts1), LIST_CONJ (map f ts2)) end

Theorem set_byte_eq_ARB:
   good_dimindex (:α) ==>
    !x h h'.
      (set_byte 0w x h be = set_byte 0w x (h':'a word) be <=>
       set_byte 0w ARB h be = set_byte 0w ARB h' be) /\
      (set_byte 1w x h be = set_byte 1w x (h':'a word) be <=>
       set_byte 1w ARB h be = set_byte 1w ARB h' be) /\
      (set_byte 2w x h be = set_byte 2w x (h':'a word) be <=>
       set_byte 2w ARB h be = set_byte 2w ARB h' be) /\
      (set_byte 3w x h be = set_byte 3w x (h':'a word) be <=>
       set_byte 3w ARB h be = set_byte 3w ARB h' be) /\
      (set_byte 4w x h be = set_byte 4w x (h':'a word) be <=>
       set_byte 4w ARB h be = set_byte 4w ARB h' be) /\
      (set_byte 5w x h be = set_byte 5w x (h':'a word) be <=>
       set_byte 5w ARB h be = set_byte 5w ARB h' be) /\
      (set_byte 6w x h be = set_byte 6w x (h':'a word) be <=>
       set_byte 6w ARB h be = set_byte 6w ARB h' be) /\
      (set_byte 7w x h be = set_byte 7w x (h':'a word) be <=>
       set_byte 7w ARB h be = set_byte 7w ARB h' be)
Proof
  rw [good_dimindex_def]
  \\ Cases_on `be` \\ fs [set_byte_def,LET_THM,byte_index_def,dimword_def]
  \\ full_simp_tac (std_ss++wordsLib.WORD_BIT_EQ_ss)
        [word_slice_alt_def,set_byte_def,LET_THM,dimword_def]
QED

Theorem bytes_to_word_eq_lemma:
   good_dimindex (:α) /\ LENGTH bs' = LENGTH bs /\
    bytes_to_word (dimindex (:α) DIV 8) 0w bs (h:'a word) be =
    bytes_to_word (dimindex (:α) DIV 8) 0w bs h' be ==>
    bytes_to_word (dimindex (:α) DIV 8) 0w bs' h be =
    bytes_to_word (dimindex (:α) DIV 8) 0w bs' h' be
Proof
  fs[good_dimindex_def] \\ rfs[dimword_def]
  \\ rw [] \\ rfs [] \\ pop_assum mp_tac
  \\ `good_dimindex (:α)` by fs[good_dimindex_def]
  \\ Cases_on `bs` \\ Cases_on `bs'`
  \\ once_rewrite_tac [bytes_to_word_def] \\ fs []
  \\ assume_tac (UNDISCH set_byte_eq_ARB)
  \\ pop_assum (fn th => once_rewrite_tac [th]) \\ fs []
  \\ rpt (rename1 `LENGTH t1 = LENGTH t2`
    \\ Cases_on `t1` \\ Cases_on `t2`
    \\ once_rewrite_tac [bytes_to_word_def] \\ fs []
    \\ NTAC 30 (fs [Once set_byte_sort_dec])
    \\ assume_tac (UNDISCH set_byte_eq_ARB)
    \\ pop_assum (fn th => once_rewrite_tac [th]))
QED

Theorem write_bytes_inj_lemma:
   good_dimindex(:α) ⇒
   ∀w1 w2 bs bs'.
   write_bytes bs w1 be = write_bytes bs (w2:'a word list) be ∧
   LENGTH w1 = LENGTH w2 ∧
   LENGTH bs' = LENGTH bs (*∧
   LENGTH bs ≤ LENGTH (w1:α word list) * (dimindex (:α) DIV 8) *)
   (* ∧ LENGTH (w1:α word list) ≤ LENGTH bs DIV (dimindex(:α) DIV 8) +1 *)
   ⇒
   write_bytes bs' w1 be = write_bytes bs' w2 be
Proof
  strip_tac \\ Induct >- rw[] \\ rw[Once write_bytes_def]
  \\ Cases_on`w2` \\ fs[write_bytes_def] \\ rw[]
  >- (match_mp_tac bytes_to_word_eq_lemma \\ fs [])
  \\ first_x_assum match_mp_tac
  \\ rw[] \\ asm_exists_tac \\ simp[]
QED

(* slow *)
Theorem set_byte_all_64:
   dimindex(:'a) = 64 ⇒
   set_byte (0w:'a word) b1
     (set_byte 1w b2
       (set_byte 2w b3
         (set_byte 3w b4
           (set_byte 4w b5
             (set_byte 5w b6
               (set_byte 6w b7
                 (set_byte 7w b8 x be) be) be) be) be) be) be) be
   =
   set_byte 0w b1
     (set_byte 1w b2
       (set_byte 2w b3
         (set_byte 3w b4
           (set_byte 4w b5
             (set_byte 5w b6
               (set_byte 6w b7
                 (set_byte 7w b8 y be) be) be) be) be) be) be) be
Proof
  Cases_on`be`
  \\ rw[set_byte_def,byte_index_def,dimword_def,word_slice_alt_def]
  \\ srw_tac[wordsLib.WORD_BIT_EQ_ss][]
QED

Theorem set_byte_all_32:
   dimindex(:'a) = 32 ⇒
   set_byte (0w:'a word) b1
     (set_byte 1w b2
       (set_byte 2w b3
                 (set_byte 3w b8 x be) be) be) be
   =
   set_byte 0w b1
     (set_byte 1w b2
       (set_byte 2w b3
                 (set_byte 3w b8 y be) be) be) be
Proof
  Cases_on`be`
  \\ rw[set_byte_def,byte_index_def,dimword_def,word_slice_alt_def]
  \\ srw_tac[wordsLib.WORD_BIT_EQ_ss][]
QED

(* slow *)
Theorem word_of_byte_set_byte_64:
   dimindex(:'a) = 64 ⇒
   word_of_byte (w2w w) =
   set_byte 0w w
     (set_byte 1w w
       (set_byte 2w w
         (set_byte 3w w
           (set_byte 4w w
             (set_byte 5w w
               (set_byte 6w w
                 (set_byte 7w w (x:'a word) be) be) be) be) be) be) be) be
Proof
  rw[word_of_byte_def,set_byte_def,byte_index_def,dimword_def,word_slice_alt_def]
  \\ srw_tac[wordsLib.WORD_BIT_EQ_ss][]
QED

Theorem word_of_byte_set_byte_32:
   dimindex(:'a) = 32 ⇒
   word_of_byte (w2w w) =
   set_byte 0w w
     (set_byte 1w w
       (set_byte 2w w
                 (set_byte 3w w (x:'a word) be) be) be) be
Proof
  rw[word_of_byte_def,set_byte_def,byte_index_def,dimword_def,word_slice_alt_def]
  \\ srw_tac[wordsLib.WORD_BIT_EQ_ss][]
QED

Theorem write_bytes_change_extra:
   ∀ws bs be ws'.
     good_dimindex(:'a) ∧
     LENGTH ws = LENGTH ws' ∧
     LENGTH ws < byte_len (:'a) (LENGTH bs)
     ⇒
     write_bytes bs (ws:'a word list) be = write_bytes bs ws' be
Proof
  Induct \\ rw[write_bytes_def,LENGTH_NIL_SYM]
  \\ Cases_on`ws'` \\ fs[write_bytes_def]
  \\ reverse conj_tac
  >- (
    first_x_assum match_mp_tac
    \\ fs[byte_len_def,good_dimindex_def]
    \\ rfs [ADD_DIV_EQ,X_LT_DIV] )
  \\ fs[good_dimindex_def,byte_len_def]
  \\ Cases_on`bs` \\ rfs[ADD1]
  \\ qmatch_goalsub_rename_tac`_::bs`
  \\ Cases_on`bs` \\ rfs[ADD1]
  \\ qmatch_goalsub_rename_tac`_::_::bs`
  \\ Cases_on`bs` \\ rfs[ADD1]
  \\ qmatch_goalsub_rename_tac`_::_::_::bs`
  \\ Cases_on`bs` \\ rfs[ADD1]
  \\ qmatch_goalsub_rename_tac`_::_::_::_::bs`
  \\ Cases_on`bs` \\ rfs[ADD1]
  \\ TRY (
    qmatch_goalsub_rename_tac`_::_::_::_::_::bs`
    \\ Cases_on`bs` \\ rfs[ADD1] )
  \\ TRY (
    qmatch_goalsub_rename_tac`_::_::_::_::_::_::bs`
    \\ Cases_on`bs` \\ rfs[ADD1] )
  \\ TRY (
    qmatch_goalsub_rename_tac`_::_::_::_::_::_::_::bs`
    \\ Cases_on`bs` \\ rfs[ADD1] )
  \\ TRY (
    qmatch_goalsub_rename_tac`_::_::_::_::_::_::_::_::bs`
    \\ Cases_on`bs` \\ rfs[ADD1] )
  \\ rpt (once_rewrite_tac [bytes_to_word_def] \\ fs [set_byte_all_64,set_byte_all_32])
QED

Definition last_bytes_def:
  last_bytes k b a w be =
    if k = 0n then w else
      set_byte a b (last_bytes (k-1) b (a+1w) w be) be
End

Theorem last_bytes_simp = Q.prove(
  `(last_bytes 0 b a w be = w) ∧
   (last_bytes (SUC n) b a w be = set_byte a b (last_bytes n b (a + 1w) w be) be)`,
  rw[Once last_bytes_def] \\ rw[Once last_bytes_def])
  |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ |> CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV

Theorem last_bytes_bytes_to_word_REPLICATE:
   !n1 n k a (w:'a word).
   n <= k /\ b1 = b2 /\ n1 = n ==>
   bytes_to_word k a (REPLICATE n b2) w be =
   last_bytes n1 b1 a w be
Proof
  simp []
  \\ Induct \\ rw[Once bytes_to_word_def,REPLICATE]
  >- ( rw[Once last_bytes_def] )
  \\ rw[Once last_bytes_def,SimpRHS]
QED

Theorem decode_length_make_byte_header:
   good_dimindex(:α) ∧ c.len_size + 7 < dimindex(:α) ∧
   len + (2 ** shift(:α)) < 2 ** (c.len_size + shift(:α)) ⇒
   len ≤ w2n ((decode_length c (make_byte_header c fl len)):α word) *
       (dimindex(:α) DIV 8) /\
  w2n ((decode_length c (make_byte_header c fl len)):α word) ≤
       len DIV (dimindex(:α) DIV 8) + 1
Proof
  simp[decode_length_def,make_byte_header_def,good_dimindex_def]
  \\ strip_tac \\ simp[]
  \\ qpat_abbrev_tac`z = COND _ _ _ >>> _`
  \\ `z = 0w`
  by (
    fs[Abbr`z`]
    \\ fsrw_tac[wordsLib.WORD_BIT_EQ_ss][word_index]
    \\ rpt strip_tac
    \\ spose_not_then strip_assume_tac
    \\ rfs[word_index] )
  \\ unabbrev_all_tac \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`_ << s1`
  \\ qmatch_goalsub_abbrev_tac`_ >>> s2`
  \\ `s2 = s1 + shift(:α)`
  by ( simp[Abbr`s1`,Abbr`s2`,shift_def] )
  \\ fs [DIV_LT_X,ADD_DIV_EQ]
  \\ unabbrev_all_tac
  \\ qpat_abbrev_tac `pat = _ << _ >>> _`
  \\ qabbrev_tac `k = (if dimindex (:'a) = 32 then 4 else 8:num)`
  \\ `(k + len) DIV k < 2 ** c.len_size` by
    (`0 < k` by fs [Abbr `k`] \\ fs [DIV_LT_X]
     \\ rfs [shift_def,EXP_ADD] \\ rfs [] \\ fs [])
  \\ `k + len < dimword (:'a)` by
   (`0 < k` by fs [Abbr `k`] \\ fs [DIV_LT_X]
    \\ match_mp_tac LESS_LESS_EQ_TRANS \\ asm_exists_tac \\ fs []
    \\ `k = 2 ** (if dimindex (:'a) = 32 then 2 else 3)` by fs [Abbr`k`]
    \\ pop_assum (fn th => once_rewrite_tac [th])
    \\ rewrite_tac [GSYM EXP_ADD,dimword_def]
    \\ rewrite_tac [dimword_def,EXP_BASE_LE_IFF] \\ fs [])
  \\ `(len + k) DIV k < dimword (:'a)` by
   (fs [] \\ match_mp_tac LESS_LESS_EQ_TRANS \\ asm_exists_tac \\ fs []
    \\ rewrite_tac [dimword_def,EXP_BASE_LE_IFF] \\ fs [])
  \\ `pat = n2w ((len + k) DIV k)` by
   (rfs [] \\ fs []
    \\ qunabbrev_tac `pat`
    \\ match_mp_tac shift_shift_lemma \\ fs [shift_def]
    \\ fs [dimword_def,DIV_LT_X] \\ rfs [])
  \\ `0 < k` by fs [Abbr `k`]
  \\ drule arithmeticTheory.ADD_DIV_ADD_DIV
  \\ disch_then (qspec_then `1` assume_tac) \\ fs [] \\ rfs []
  \\ drule DIVISION
  \\ disch_then (qspec_then `len` strip_assume_tac)
  \\ qpat_x_assum `_ = _` (fn th => simp [th])
QED

Theorem memory_rel_RefByte_content:
   memory_rel c be ts refs sp st m dm vars ∧
   new ∉ (domain refs) ∧ byte_len (:'a) n < sp ∧
   byte_len (:'a) n < 2 ** (dimindex (:α) − 4) /\
   byte_len (:'a) n < 2 ** c.len_size /\ n = LENGTH bytes ∧
   good_dimindex (:α) ⇒
   ∃free curr m1.
     FLOOKUP st NextFree = SOME (Word free) ∧
     FLOOKUP st CurrHeap = SOME (Word curr) ∧
     (let w' = bytes_in_word * (n2w (byte_len (:'a) n + 1)):'a word in
      let ws = REPLICATE (byte_len (:'a) n) 0w in
      let ws = write_bytes bytes ws be in
        store_list free (Word (make_byte_header c fl n)::MAP Word ws) m dm = SOME m1 ∧
        memory_rel c be ts (insert new (ByteArray fl bytes) refs)
          (sp − (byte_len (:'a) n + 1)) (st |+ (NextFree,Word (free + w'))) m1 dm
          ((RefPtr T new,make_ptr c (free − curr) (0w:'a word) (byte_len (:'a) n))::vars))
Proof
  simp_tac std_ss [LET_THM]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ fs [memory_rel_def,PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac`Word _ :: ws`
  \\ rw []
  \\ qabbrev_tac ‘n = LENGTH bytes’
  \\ fs [word_ml_inv_def,PULL_EXISTS] \\ clean_tac
  \\ drule (GEN_ALL (new_byte_alt_thm |> Q.INST [‘b’|->‘T’]))
  \\ disch_then (qspecl_then [`(byte_len (:'a) n)`,
        `new`,`fl`,`bytes`] mp_tac)
  \\ fs [LENGTH_REPLICATE]
  \\ impl_tac THEN1
    (gvs [byte_len_def,good_dimindex_def] \\ gvs [markerTheory.Abbrev_def,dimword_def])
  \\ rfs [] \\ fs [] \\ clean_tac \\ strip_tac
  \\ rewrite_tac [GSYM CONJ_ASSOC]
  \\ once_rewrite_tac [METIS_PROVE [] ``b1 /\ b2 /\ b3 <=> b2 /\ b1 /\ b3:bool``]
  \\ asm_exists_tac \\ fs []
  \\ fs [heap_in_memory_store_def,FLOOKUP_UPDATE]
  \\ imp_res_tac heap_store_unused_alt_IMP_length \\ fs []
  \\ `byte_len (:'a) n <= sp' + sp1` by decide_tac
  \\ pop_assum mp_tac \\ simp_tac std_ss [LESS_EQ_EXISTS]
  \\ strip_tac \\ clean_tac \\ fs []
  \\ Cases_on `p` \\ fs [ADD1]
  \\ fs [bytes_in_word_mul_eq_shift]
  \\ fs [GSYM word_add_n2w,word_addr_def,
         WORD_LEFT_ADD_DISTRIB,get_addr_def,make_ptr_def,get_lowerbits_def]
  \\ fs [bytes_in_word_mul_eq_shift]
  \\ fs [heap_store_unused_alt_def,el_length_def,Bytes_def,LENGTH_REPLICATE]
  \\ qpat_x_assum`_ = (_,T)`mp_tac
  \\ rw[] \\ fs []
  \\ imp_res_tac heap_lookup_SPLIT \\ fs [] \\ clean_tac
  \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ fs [heap_store_lemma] \\ clean_tac \\ fs []
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def,
         SEP_CLAUSES,word_heap_heap_expand,RefBlock_def,el_length_def,
         heap_length_APPEND,heap_length_heap_expand,LENGTH_REPLICATE]
  \\ fs [word_list_exists_ADD |> Q.SPECL [`n+1`,`n'`]
           |> SIMP_RULE std_ss [Once ADD_COMM]]
  \\ fs [GSYM bytes_in_word_mul_eq_shift,write_bytes_REPLICATE]
  \\ qpat_abbrev_tac `ws2 = Word (make_byte_header c fl n)::_`
  \\ rveq \\ fs []
  \\ simp_tac (std_ss++helperLib.sep_cond_ss) [cond_STAR,GSYM CONJ_ASSOC]
  \\ fs [GSYM PULL_EXISTS] \\ fs [CONJ_ASSOC]
  \\ reverse conj_tac THEN1
   (`(byte_len (:α) n + 1) = LENGTH ws2` by
      (unabbrev_all_tac \\ fs [LENGTH_REPLICATE] \\ NO_TAC) \\ fs []
    \\ qpat_x_assum `_ (fun2set (m,dm))` mp_tac
    \\ qpat_abbrev_tac `ll = word_list_exists _ (LENGTH ws2)`
    \\ fs [AC STAR_COMM STAR_ASSOC]
    \\ qunabbrev_tac `ll` \\ strip_tac
    \\ drule store_list_thm
    \\ strip_tac \\ fs []
    \\ fs [heap_length_def,el_length_def]
    \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ fs [AC STAR_ASSOC STAR_COMM] \\ fs [STAR_ASSOC])
  \\ `0 < c.len_size` by fs [] \\ fs [GSYM shift_def]
  \\ fs [GSYM DIV_LT_X,EXP_ADD]
  \\ fs [good_dimindex_def,shift_def,byte_len_def,
         make_byte_header_def,decode_length_def] \\ rfs []
  \\ fs [DECIDE ``m + n < k <=> m < k - n:num``]
  \\ qpat_abbrev_tac `www = (COND _ _ _) >>> _`
  \\ `www = 0w` by
    (unabbrev_all_tac
     \\ IF_CASES_TAC
     \\ match_mp_tac n2w_lsr_eq_0
     \\ fs [dimword_def]
     \\ match_mp_tac LESS_DIV_EQ_ZERO \\ fs []
     \\ fs [LESS_EQ]
     \\ match_mp_tac LESS_EQ_TRANS
     \\ qexists_tac `2n ** 5`
     \\ (conj_tac THEN1 fs [])
     \\ match_mp_tac IMP_EXP_LESS \\ fs [] \\ NO_TAC) \\ fs []
  \\ qunabbrev_tac ‘ws’
  \\ fs [DIV_LT_X,ADD_DIV_EQ]
  \\ match_mp_tac shift_shift_lemma \\ fs [shift_def] \\ fs [dimword_def,DIV_LT_X]
QED

Theorem memory_rel_RefByte_alt:
  memory_rel c be ts refs sp st m dm vars ∧
   new ∉ (domain refs) ∧ byte_len (:'a) n < sp ∧
   byte_len (:'a) n < 2 ** (dimindex (:α) − 4) /\
   byte_len (:'a) n < 2 ** c.len_size /\
   good_dimindex (:α) ⇒
   ∃free curr m1.
     FLOOKUP st NextFree = SOME (Word free) ∧
     FLOOKUP st CurrHeap = SOME (Word curr) ∧
     (let w' = bytes_in_word * (n2w (byte_len (:'a) n + 1)):'a word in
      let ws = REPLICATE (byte_len (:'a) n) (Word (word_of_byte (w2w w))) in
      let nb = (n MOD (dimindex(:'a) DIV 8)) in
      let ws = LUPDATE (Word (last_bytes nb w 0w 0w be)) (byte_len (:'a) n - 1) ws in
        store_list free (Word (make_byte_header c fl n)::ws) m dm = SOME m1 ∧
        memory_rel c be ts (insert new (ByteArray fl (REPLICATE n w)) refs)
          (sp − (byte_len (:'a) n + 1)) (st |+ (NextFree,Word (free + w'))) m1 dm
          ((RefPtr T new,make_ptr c (free − curr) 0w (byte_len (:'a) n))::vars))
Proof
  simp_tac std_ss [LET_THM]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ fs [memory_rel_def,PULL_EXISTS]
  \\ qmatch_goalsub_abbrev_tac`Word _ :: ws`
  \\ rw []
  \\ fs [word_ml_inv_def,PULL_EXISTS] \\ clean_tac
  \\ drule (GEN_ALL (new_byte_alt_thm |> Q.INST [‘b’|->‘T’]))
  \\ disch_then (qspecl_then [`(byte_len (:'a) n)`,
        `new`,`fl`,`REPLICATE n w`] mp_tac)
  \\ fs [LENGTH_REPLICATE]
  \\ impl_tac THEN1
    (fs [byte_len_def,good_dimindex_def] \\ fs [markerTheory.Abbrev_def])
  \\ rfs [] \\ fs [] \\ clean_tac \\ strip_tac
  \\ rewrite_tac [GSYM CONJ_ASSOC]
  \\ once_rewrite_tac [METIS_PROVE [] ``b1 /\ b2 /\ b3 <=> b2 /\ b1 /\ b3:bool``]
  \\ asm_exists_tac \\ fs []
  \\ fs [heap_in_memory_store_def,FLOOKUP_UPDATE]
  \\ imp_res_tac heap_store_unused_alt_IMP_length \\ fs []
  \\ `byte_len (:'a) n <= sp' + sp1` by decide_tac
  \\ pop_assum mp_tac \\ simp_tac std_ss [LESS_EQ_EXISTS]
  \\ strip_tac \\ clean_tac \\ fs []
  \\ Cases_on `p` \\ fs [ADD1]
  \\ fs [bytes_in_word_mul_eq_shift]
  \\ fs [GSYM word_add_n2w,word_addr_def,
         WORD_LEFT_ADD_DISTRIB,get_addr_def,make_ptr_def,get_lowerbits_def]
  \\ fs [bytes_in_word_mul_eq_shift]
  \\ fs [heap_store_unused_alt_def,el_length_def,Bytes_def,LENGTH_REPLICATE]
  \\ qpat_x_assum`_ = (_,T)`mp_tac
  \\ rw[] \\ fs []
  \\ imp_res_tac heap_lookup_SPLIT \\ fs [] \\ clean_tac
  \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ fs [heap_store_lemma] \\ clean_tac \\ fs []
  \\ fs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def,
         SEP_CLAUSES,word_heap_heap_expand,RefBlock_def,el_length_def,
         heap_length_APPEND,heap_length_heap_expand,LENGTH_REPLICATE]
  \\ fs [word_list_exists_ADD |> Q.SPECL [`n+1`,`n'`]
           |> SIMP_RULE std_ss [Once ADD_COMM]]
  \\ fs [GSYM bytes_in_word_mul_eq_shift,write_bytes_REPLICATE]
  \\ qpat_abbrev_tac `ws2 = Word (make_byte_header c fl n)::_`
  \\ qpat_abbrev_tac `ws1 = Word (make_byte_header c fl n)::_`
  \\ `ws1 = ws2` by (
    unabbrev_all_tac \\ fs [map_replicate] \\
    Cases_on`byte_len (:'a) n` \\ fs[]
    >- ( fs[byte_len_def,REPLICATE,LUPDATE_def,write_bytes_def] )
    \\ rename1`REPLICATE l 0w`
    \\ rewrite_tac[GSYM REPLICATE]
    \\ rewrite_tac[REPLICATE_SNOC,SNOC_APPEND]
    \\ simp[LUPDATE_APPEND2,LUPDATE_def,write_bytes_APPEND]
    \\ simp[APPEND_EQ_APPEND] \\ disj1_tac \\ qexists_tac`[]` \\ simp[]
    \\ conj_tac
    >- (
      once_rewrite_tac[GSYM map_replicate]
      \\ AP_TERM_TAC
      \\ drule(GSYM write_bytes_REPLICATE)
      \\ disch_then(qspecl_then[`l`,`n`]SUBST_ALL_TAC)
      \\ match_mp_tac write_bytes_change_extra
      \\ simp[] )
    \\ simp[write_bytes_def]
    \\ simp[DROP_REPLICATE]
    \\ match_mp_tac (GEN_ALL last_bytes_bytes_to_word_REPLICATE)
    \\ simp[LESS_OR_EQ]
    \\ fs[good_dimindex_def,byte_len_def]
    \\ rfs [ADD1] \\ rveq
    \\ `0 < 4:num` by fs [] \\ drule DIVISION
    \\ disch_then (qspec_then `n` strip_assume_tac)
    \\ `0 < 8:num` by fs [] \\ drule DIVISION
    \\ disch_then (qspec_then `n` strip_assume_tac)
    \\ decide_tac)
  \\ rveq \\ fs []
  \\ simp_tac (std_ss++helperLib.sep_cond_ss) [cond_STAR,GSYM CONJ_ASSOC]
  \\ fs [GSYM PULL_EXISTS] \\ fs [CONJ_ASSOC]
  \\ conj_tac THEN1
   (`0 < c.len_size` by fs [] \\ fs [GSYM shift_def]
    \\ fs [GSYM DIV_LT_X,EXP_ADD]
    \\ fs [good_dimindex_def,shift_def,byte_len_def,
           make_byte_header_def,decode_length_def] \\ rfs []
    \\ fs [DECIDE ``m + n < k <=> m < k - n:num``]
    \\ qpat_abbrev_tac `www = (COND _ _ _) >>> _`
    \\ `www = 0w` by
     (unabbrev_all_tac
      \\ IF_CASES_TAC
      \\ match_mp_tac n2w_lsr_eq_0
      \\ fs [dimword_def]
      \\ match_mp_tac LESS_DIV_EQ_ZERO \\ fs []
      \\ fs [LESS_EQ]
      \\ match_mp_tac LESS_EQ_TRANS
      \\ qexists_tac `2n ** 5`
      \\ (conj_tac THEN1 fs [])
      \\ match_mp_tac IMP_EXP_LESS \\ fs [] \\ NO_TAC) \\ fs []
    \\ fs [DIV_LT_X,ADD_DIV_EQ]
    \\ match_mp_tac shift_shift_lemma \\ fs [shift_def]
    \\ fs [dimword_def,DIV_LT_X])
  \\ `(byte_len (:α) n + 1) = LENGTH ws1` by
       (unabbrev_all_tac \\ fs [LENGTH_REPLICATE] \\ NO_TAC) \\ fs []
  \\ qpat_x_assum `_ (fun2set (m,dm))` mp_tac
  \\ qpat_abbrev_tac `ll = word_list_exists _ (LENGTH ws1)`
  \\ fs [AC STAR_COMM STAR_ASSOC]
  \\ qunabbrev_tac `ll` \\ strip_tac
  \\ drule store_list_thm
  \\ strip_tac \\ fs []
  \\ fs [heap_length_def,el_length_def]
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [AC STAR_ASSOC STAR_COMM] \\ fs [STAR_ASSOC]
QED

(*
        memory_rel_def
word_ml_inv_def
abs_ml_inv_def
bc_stack_ref_inv_def
bc_ref_inv_def
Bytes_def
write_bytes_def


          heap_in_memory_store_def
  word_heap_def
  word_el_def
  word_el_def
   word_payload_def
*)

Theorem memory_rel_tail:
   memory_rel c be ts refs sp st m dm (v::vars) ==>
    memory_rel c be ts refs sp st m dm vars
Proof
  match_mp_tac memory_rel_rearrange \\ fs []
QED

Theorem memory_rel_drop:
   memory_rel c be ts refs sp st m dm (vs ++ vars) ==>
    memory_rel c be ts refs sp st m dm vars
Proof
  match_mp_tac memory_rel_rearrange \\ fs []
QED

Theorem memory_rel_IMP_word_list_exists:
   memory_rel c be ts refs sp st m dm vars /\ n <= sp /\
    FLOOKUP st NextFree = SOME (Word f) ==>
    (word_list_exists f n * SEP_T) (fun2set (m,dm))
Proof
  fs [memory_rel_def,heap_in_memory_store_def] \\ rw [] \\ fs []
  \\ fs [word_ml_inv_def,abs_ml_inv_def,unused_space_inv_def]
  \\ Cases_on `n = 0`
  THEN1 (fs [word_list_exists_thm,SEP_CLAUSES] \\ fs [SEP_T_def])
  \\ fs [] \\ imp_res_tac heap_lookup_SPLIT
  \\ rveq \\ fs [word_heap_APPEND,word_heap_def,word_el_def]
  \\ `n <= sp'` by decide_tac
  \\ pop_assum mp_tac
  \\ simp [LESS_EQ_EXISTS] \\ strip_tac \\ rveq
  \\ fs [word_list_exists_ADD]
  \\ qpat_abbrev_tac `aa = word_list_exists
       (curr + bytes_in_word * n2w (heap_length ha)) n`
  \\ fs [AC STAR_ASSOC STAR_COMM]
  \\ once_rewrite_tac [STAR_COMM]
  \\ qpat_assum `_ (fun2set _)` mp_tac
  \\ qspec_tac (`fun2set (m,dm)`,`x`)
  \\ fs [GSYM SEP_IMP_def]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ match_mp_tac SEP_IMP_STAR
  \\ fs [SEP_IMP_REFL]
  \\ fs [SEP_IMP_def,SEP_T_def]
QED

Theorem get_addr_0:
   get_addr c n u ' 0
Proof
  Cases_on `u` \\ fs [get_addr_def,get_lowerbits_def,
     word_or_def,fcpTheory.FCP_BETA,word_index]
QED

Theorem word_addr_eq_Loc:
  word_addr c v = Loc l1 l2 <=> l2 = 0 ∧ ∃l2. v = Data (Loc l1 l2)
Proof
  Cases_on `v` \\ fs [word_addr_def]
  \\ Cases_on `a` \\ fs [word_addr_def]
  \\ eq_tac \\ rw []
QED

Theorem memory_rel_CodePtr:
   memory_rel c be ts refs sp st m dm vars ==>
    memory_rel c be ts refs sp st m dm ((CodePtr lab,Loc lab 0)::vars)
Proof
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ fs [word_ml_inv_def,PULL_EXISTS,word_addr_eq_Loc]
  \\ once_rewrite_tac [CONJ_COMM] \\ asm_exists_tac \\ fs []
  \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def,
         roots_ok_def,reachable_refs_def]
  \\ rw [] \\ fs [] \\ res_tac \\ fs [PULL_EXISTS]
  \\ qexists_tac `f` \\ qexists_tac `tf`
  \\ fs [PULL_EXISTS] \\ rw [] \\ fs []
  \\ fs [get_refs_def] \\ res_tac
  \\ fs [all_ts_cons_no_block]
QED

Theorem memory_rel_Block_IMP:
   memory_rel c be ts refs sp st m dm ((Block ts' tag vals,v:'a word_loc)::vars) /\
    good_dimindex (:'a) ==>
    ?w. v = Word w /\
        (* ASK: If the Block has no vals then it's timestamp is 0 *)
        if vals = [] then
          w = n2w tag * 16w + 2w /\ ~(w ' 0) /\
          tag < dimword (:'a) DIV 16 /\ ts' = 0
        else
          ?a x.
            w ' 0 /\ ~(word_bit 3 x) /\ ~(word_bit 2 x) /\
            get_real_addr c st w = SOME a /\ m a = Word x /\ a IN dm /\
            decode_length c x = n2w (LENGTH vals) /\
            LENGTH vals < 2 ** (dimindex (:'a) − 4) /\
            encode_header c (4 * tag) (LENGTH vals) = SOME x /\
            ts' < ts
Proof
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
  \\ fs [good_dimindex_def]
  \\ fs [fcpTheory.FCP_BETA,word_lsl_def,word_index]
  \\ fs [FLOOKUP_DEF,SUBSET_DEF] \\ res_tac
QED

Theorem IMP_memory_rel_Number:
   good_dimindex (:'a) /\ small_int (:'a) i /\
    memory_rel c be ts refs sp st m dm vars ==>
    memory_rel c be ts refs sp st m dm
     ((Number i,(Word (Smallnum i):'a word_loc))::vars)
Proof
  fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS] \\ rpt strip_tac
  \\ asm_exists_tac \\ fs []
  \\ rpt_drule abs_ml_inv_Num
  \\ strip_tac \\ asm_exists_tac \\ fs [word_addr_def]
  \\ fs [Smallnum_def] \\ Cases_on `i`
  \\ fs [GSYM word_mul_n2w,word_ml_inv_num_lemma,word_ml_inv_neg_num_lemma]
QED

Theorem memory_rel_El_any:
   memory_rel c be ts refs sp st m dm ((Block ts' tag vals,ptr:'a word_loc)::vars) /\
    good_dimindex (:'a) /\
    index < LENGTH vals ==>
    ?ptr_w x y:'a word.
      ptr = Word ptr_w /\
      get_real_addr c st ptr_w = SOME x /\
      (x + bytes_in_word + bytes_in_word * n2w index) IN dm /\
      memory_rel c be ts refs sp st m dm
        ((EL index vals,m (x + bytes_in_word + bytes_in_word * n2w index))::
         (Block ts' tag vals,ptr)::vars)
Proof
  rw [] \\ rpt_drule memory_rel_Block_IMP \\ rw [] \\ fs []
  \\ Cases_on `vals = []` \\ fs []
  \\ `memory_rel c be ts refs sp st m dm
           ((Block ts' tag vals,Word w)::(Number (&index),
              Word (Smallnum (&index)))::vars)` by
   (match_mp_tac memory_rel_swap
    \\ match_mp_tac IMP_memory_rel_Number \\ fs []
    \\ fs [small_int_def,dimword_def,good_dimindex_def] \\ rfs [])
  \\ rpt_drule memory_rel_El \\ fs [] \\ strip_tac \\ fs []
  \\ fs [get_real_offset_def, good_dimindex_def] \\ rfs [Smallnum_def]
  \\ rveq \\ fs [bytes_in_word_def] \\ rfs [word_mul_n2w,WORD_MUL_LSL]
  \\ pop_assum mp_tac
  \\ match_mp_tac memory_rel_rearrange
  \\ fs [] \\ rw [] \\ fs []
QED

Definition copy_list_def:
  copy_list c' st k (a,x,b:'a word,m:'a word -> 'a word_loc,dm) =
    let c = (b IN dm) in
    let m = (b =+ x) m in
    let b = b + bytes_in_word in
      if k = 0n then (if c then SOME (b,m) else NONE) else
        case a of Loc _ _ => NONE | Word a =>
        case get_real_addr c' st a of NONE => NONE | SOME a =>
          let c = (c /\ a + 2w * bytes_in_word IN dm /\ a + bytes_in_word IN dm) in
          let x = m (a + bytes_in_word) in
          let a = m (a + 2w * bytes_in_word) in
            if c then copy_list c' st (k-1) (a,x,b,m,dm) else NONE
End

Theorem copy_list_thm = Q.prove(`
  !v k vs b m vars a x frame.
      memory_rel c be ts refs sp st m dm ((v,a:'a word_loc)::vars) /\
      v_to_list v = SOME vs /\
      (word_list_exists (b + bytes_in_word * n2w k) (SUC (LENGTH vs)) * frame)
         (fun2set (m,dm)) /\
      good_dimindex (:α) /\
      FLOOKUP st NextFree = SOME (Word b) /\
      k + LENGTH vs < sp ==>
      ?w xs m1.
        copy_list c st (LENGTH vs) (a,x,b + bytes_in_word * n2w k,m,dm) =
           SOME (b + bytes_in_word * n2w (k + LENGTH vs + 1),m1) /\
        LENGTH vs = LENGTH xs /\
        memory_rel c be ts refs sp st m1 dm (ZIP (vs,xs) ++ vars) /\
        (word_list (b + bytes_in_word * n2w k) (x::xs) * frame) (fun2set (m1,dm))`,
  Induct_on `vs`
  THEN1
   (rewrite_tac [LENGTH,word_list_exists_thm]
    \\ fs [] \\ rw [] \\ once_rewrite_tac [copy_list_def] \\ fs []
    \\ imp_res_tac memory_rel_tail
    \\ rpt_drule memory_rel_write \\ fs []
    \\ disch_then drule \\ strip_tac \\ fs []
    \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ fs [word_list_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SEP_W_TAC)
  \\ rewrite_tac [word_list_exists_thm]
  \\ rpt strip_tac
  \\ fs [SEP_CLAUSES,SEP_EXISTS_THM]
  \\ Cases_on `v` \\ fs [v_to_list_def]
  \\ Cases_on `l` \\ fs [v_to_list_def]
  \\ Cases_on `t` \\ fs [v_to_list_def]
  \\ Cases_on `t'` \\ fs [v_to_list_def]
  \\ FULL_CASE_TAC \\ fs [] \\ rveq
  \\ once_rewrite_tac [copy_list_def] \\ fs []
  \\ rpt_drule memory_rel_Block_IMP
  \\ strip_tac \\ fs []
  \\ qabbrev_tac `m0 = (b + bytes_in_word * n2w k =+ x) m`
  \\ rpt_drule memory_rel_write \\ fs []
  \\ `k < sp` by decide_tac
  \\ disch_then drule
  \\ disch_then (qspec_then `x` mp_tac) \\ strip_tac \\ rfs []
  \\ `small_int (:α) 0` by
       (EVAL_TAC \\ fs [good_dimindex_def,dimword_def])
  \\ rpt_drule (IMP_memory_rel_Number |> REWRITE_RULE [CONJ_ASSOC]
       |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ `small_int (:α) 1` by
       (EVAL_TAC \\ fs [good_dimindex_def,dimword_def])
  \\ strip_tac
  \\ rpt_drule (IMP_memory_rel_Number |> REWRITE_RULE [CONJ_ASSOC]
       |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ pop_assum kall_tac \\ strip_tac \\ rveq
  \\ rename1 `v_to_list h2 = SOME vs`
  \\ rename1 `get_real_addr c st w7 = SOME a7`
  \\ `memory_rel c be ts refs sp st m0 dm
         ((Block n0 cons_tag [h; h2],Word w7)::
              (Number 1,Word (Smallnum 1))::(Number 0,Word (Smallnum 0))::
              vars)` by (pop_assum mp_tac
        \\ match_mp_tac memory_rel_rearrange \\ fs [] \\ rw [] \\ fs [])
  \\ rpt_drule memory_rel_El \\ strip_tac
  \\ `y = 2w * bytes_in_word` by
    (fs [good_dimindex_def]
     \\ rfs [get_real_offset_def,good_dimindex_def,
         Smallnum_def,bytes_in_word_def,WORD_MUL_LSL] \\ NO_TAC) \\ rveq \\ fs []
  \\ `memory_rel c be ts refs sp st m0 dm
         ((Block n0 cons_tag [h; h2],Word w7)::
          (Number 0,Word (Smallnum 0))::
              (h2,m0 (a7 + 2w * bytes_in_word))::vars)` by (pop_assum mp_tac
        \\ match_mp_tac memory_rel_rearrange \\ fs [] \\ rw [] \\ fs [])
  \\ rpt_drule memory_rel_El \\ strip_tac
  \\ `y = bytes_in_word` by
    (fs [good_dimindex_def]
     \\ rfs [get_real_offset_def,good_dimindex_def,
          Smallnum_def,bytes_in_word_def,WORD_MUL_LSL] \\ NO_TAC) \\ rveq \\ fs []
  \\ qabbrev_tac `w2 = m0 (a7 + 2w * bytes_in_word)`
  \\ qabbrev_tac `w1 = m0 (a7 + bytes_in_word)`
  \\ `memory_rel c be ts refs sp st m0 dm
         ((h2,w2)::(h,w1)::vars)` by (first_assum
             (fn th => mp_tac th \\ match_mp_tac memory_rel_rearrange)
                 \\ fs [] \\ rw [] \\ fs [])
  \\ first_x_assum drule \\ fs []
  \\ disch_then (qspecl_then [`k+1`,`w1`,
        `one (b + bytes_in_word * n2w k,x) * frame`] mp_tac)
  \\ impl_tac THEN1
   (fs [AC STAR_ASSOC STAR_COMM,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ unabbrev_all_tac \\ SEP_W_TAC
    \\ fs [AC STAR_ASSOC STAR_COMM]) \\ strip_tac
  \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ qexists_tac `w1 :: xs` \\ fs []
  \\ fs [word_list_def,AC STAR_ASSOC STAR_COMM]
  \\ first_assum
       (fn th => mp_tac th \\ match_mp_tac memory_rel_rearrange)
  \\ fs [] \\ rw [] \\ fs [])
  |> Q.SPECL [`v`,`0`]
  |> SIMP_RULE (srw_ss()) [WORD_MULT_CLAUSES] |> Q.GEN `v`;

Theorem memory_rel_FromList:
   v_to_list v = SOME vs /\ vs <> [] /\
    memory_rel c be ts refs sp st m dm ((v,a:'a word_loc)::vars) /\
    encode_header c (4 * tag) (LENGTH vs) = SOME hd ∧ LENGTH vs < sp ∧
    good_dimindex (:α) ==>
    ?free curr m1 f1 xs.
      FLOOKUP st NextFree = SOME (Word free) ∧
      FLOOKUP st CurrHeap = SOME (Word curr) ∧
      copy_list c st (LENGTH vs) (a,Word hd,free,m,dm) = SOME (f1,m1) /\
      memory_rel c be (ts+1) refs (sp − (LENGTH vs + 1)) (st |+ (NextFree,Word f1)) m1 dm
        ((Block ts tag vs,
          make_cons_ptr c (free − curr) tag (LENGTH vs))::vars)
Proof
  strip_tac
  \\ `?f. FLOOKUP st NextFree = SOME (Word f)` by
       fs [memory_rel_def,heap_in_memory_store_def]
  \\ rpt_drule copy_list_thm
  \\ `SUC (LENGTH vs) <= sp` by decide_tac
  \\ rpt_drule memory_rel_IMP_word_list_exists
  \\ strip_tac \\ disch_then drule
  \\ disch_then (qspecl_then [`Word hd`] strip_assume_tac) \\ fs []
  \\ rpt_drule memory_rel_Cons_alt
  \\ strip_tac \\ fs []
QED

Triviality make_header_tag_mask:
  k < 2 ** (dimindex (:α) − (c.len_size + 2)) ==>
    (tag_mask c && make_header c ((n2w k):'a word) n) = n2w (4 * k)
Proof
  srw_tac [wordsLib.WORD_MUL_LSL_ss, boolSimps.LET_ss]
       [tag_mask_def, make_header_def, GSYM wordsTheory.word_mul_n2w]
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index]
  \\ Cases_on `2 <= i`
  \\ simp []
  \\ Cases_on `dimindex (:'a) <= i + c.len_size`
  \\ simp []
  \\ `?p. dimindex(:'a) = i + (p + 1)`
  by metis_tac [arithmeticTheory.LESS_ADD_1]
  \\ fs []
  \\ `?q. c.len_size = p + 1 + q`
  by metis_tac [arithmeticTheory.LESS_EQUAL_ADD]
  \\ fs []
  \\ `i - (q + 2) <= i - 2` by decide_tac
  \\ metis_tac [bitTheory.NOT_BIT_GT_TWOEXP, bitTheory.TWOEXP_MONO2,
                arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Triviality make_header_and_2:
  (2w && make_header c w n) = 2w
Proof
  fs [make_header_def]
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [word_index]
  \\ Cases_on `i=1` \\ fs []
QED

Theorem encode_header_tag_mask:
   encode_header c (4 * tag) n = SOME (w:'a word) /\ good_dimindex (:'a) ==>
    tag < dimword (:α) DIV 16 /\
    (w && (tag_mask c || 2w)) = n2w (16 * tag + 2)
Proof
  strip_tac \\ fs [encode_header_def,WORD_LEFT_AND_OVER_OR]
  \\ rw [make_header_and_2]
  \\ drule (GEN_ALL make_header_tag_mask)
  \\ fs [] \\ rw [GSYM word_add_n2w]
  \\ match_mp_tac (GSYM WORD_ADD_OR)
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [word_index]
  \\ fs [bitTheory.BIT_DIV2 |> Q.SPEC `0` |> SIMP_RULE std_ss [ADD1]
           |> GSYM,bitTheory.BIT0_ODD]
  \\ rewrite_tac [DECIDE ``16 * n = (8 * n) * 2n``,
        MATCH_MP MULT_DIV (DECIDE ``0<2n``),ODD_MULT] \\ fs []
QED

Theorem memory_rel_tag_limit:
   memory_rel c be ts refs sp st m dm ((Block ts' tag l,(w:'a word_loc))::rest) /\
    good_dimindex (:'a) ==>
    tag < dimword (:'a) DIV 16
Proof
  strip_tac \\ drule memory_rel_Block_IMP \\ fs [] \\ rw []
  \\ every_case_tac \\ fs []
  \\ imp_res_tac encode_header_tag_mask \\ fs []
QED

Triviality LESS_DIV_16_IMP:
  n < k DIV 16 ==> 16 * n + 2 < k:num
Proof
  fs [X_LT_DIV]
QED

Triviality MULT_BIT0:
  BIT 0 (m * n) <=> BIT 0 m /\ BIT 0 n
Proof
  fs [bitTheory.BIT0_ODD,ODD_MULT]
QED

Theorem memory_rel_test_nil_eq:
   memory_rel c be ts refs sp st m dm ((Block ts' tag l,w:'a word_loc)::rest) /\
    n < dimword (:'a) DIV 16 /\ good_dimindex (:'a) ==>
    ?v. w = Word v /\ (v = n2w (16 * n + 2) <=> tag = n /\ l = [])
Proof
  strip_tac \\ drule memory_rel_Block_IMP \\ fs [] \\ rw []
  \\ reverse every_case_tac \\ fs []
  THEN1 (CCONTR_TAC \\ rw [] \\ fs [word_index,bitTheory.ADD_BIT0,MULT_BIT0])
  \\ fs [word_mul_n2w,word_add_n2w]
  \\ imp_res_tac LESS_DIV_16_IMP \\ fs []
QED

Theorem memory_rel_test_none_eq:
   encode_header c (4 * n) len = (NONE:'a word option) /\
    memory_rel c be ts refs sp st m dm ((Block ts' tag l,w:'a word_loc)::rest) /\
    len <> 0 /\ good_dimindex (:'a) ==>
    ~(tag = n /\ LENGTH l = len)
Proof
  strip_tac \\ drule memory_rel_Block_IMP \\ fs [] \\ rw []
  \\ CCONTR_TAC \\ fs [] \\ rw [] \\ rfs [LENGTH_NIL,PULL_EXISTS]
QED

Triviality not_bit_lt_2exp:
  !p x n. n < 2 ** (p + 1) ==> ~BIT (p + (x + 1)) n
Proof
  metis_tac [DECIDE ``p + 1 <= p + (x + 1n)``, bitTheory.TWOEXP_MONO2,
     arithmeticTheory.LESS_LESS_EQ_TRANS, bitTheory.NOT_BIT_GT_TWOEXP]
QED

val not_bit_lt_2 = not_bit_lt_2exp |> Q.SPEC `0` |> SIMP_RULE (srw_ss()) []

Theorem encode_header_EQ:
   encode_header c t1 l1 = SOME (w1:'a word) /\
    encode_header c t2 l2 = SOME (w2:'a word) /\
    c.len_size + 2 < dimindex (:'a) ==>
    (w1 = w2 <=> t1 = t2 /\ l1 = l2)
Proof
  fs [encode_header_def] \\ rw [] \\ fs [make_header_def,LET_THM]
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index]
  \\ Tactical.REVERSE EQ_TAC >- rw []
  \\ `4 <= dimindex(:'a)`
  by (CCONTR_TAC
      \\ `(dimindex(:'a) = 2) \/ (dimindex(:'a) = 3)` by decide_tac
      \\ fs [wordsTheory.dimword_def])
  \\ `?p. dimindex(:'a) = c.len_size + 2 + (p + 1n)`
  by metis_tac [arithmeticTheory.LESS_ADD_1]
  \\ pop_assum SUBST_ALL_TAC
  \\ fs []
  \\ rw []
  >- (
    fs [GSYM ADD1]
    \\ `t1 = BITS p 0 t1 /\ t2 = BITS p 0 t2`
    by metis_tac [bitTheory.BITS_ZEROL]
    \\ NTAC 2 (pop_assum SUBST1_TAC)
    \\ rw [GSYM bitTheory.BIT_BITS_THM]
    \\ `x + 2 < p + (c.len_size + 3)` by decide_tac
    \\ res_tac
    \\ fs []
    \\ rfs []
  )
  \\ Cases_on `p = 0`
  \\ fs []
  >- (
    Cases_on `c.len_size - 1 = 0`
    \\ full_simp_tac bool_ss [] >- fs []
    \\ `c.len_size - 1 = SUC (c.len_size - 2)` by decide_tac
    \\ fs []
    \\ `l1 = BITS (c.len_size - 2) 0 l1 /\ l2 = BITS (c.len_size - 2) 0 l2`
    by metis_tac [bitTheory.BITS_ZEROL]
    \\ NTAC 2 (pop_assum SUBST1_TAC)
    \\ rw [GSYM bitTheory.BIT_BITS_THM]
    \\ `x + 3 < c.len_size + 3` by decide_tac
    \\ res_tac
    \\ fs []
    \\ rfs [not_bit_lt_2]
  )
  \\ Cases_on `c.len_size = 0`
  \\ fs []
  \\ `c.len_size = SUC (c.len_size - 1)` by decide_tac
  \\ fs []
  \\ `l1 = BITS (c.len_size - 1) 0 l1 /\ l2 = BITS (c.len_size - 1) 0 l2`
  by metis_tac [bitTheory.BITS_ZEROL]
  \\ NTAC 2 (pop_assum SUBST1_TAC)
  \\ rw [GSYM bitTheory.BIT_BITS_THM]
  \\ `x + (p + 3) < p + (c.len_size + 3)` by decide_tac
  \\ res_tac
  \\ fs []
  \\ rfs [not_bit_lt_2exp]
QED

Theorem memory_rel_ValueArray_IMP:
   memory_rel c be ts refs sp st m dm ((RefPtr bl p,v:'a word_loc)::vars) /\
    lookup p refs = SOME (ValueArray vals) /\ good_dimindex (:'a) ==>
    ?w a x.
      v = Word w /\ w ' 0 /\ word_bit 3 x /\ ~word_bit 2 x /\ ~word_bit 4 x /\
      get_real_simple_addr c st w = SOME a /\
      get_real_addr c st w = SOME a /\
      m a = Word x /\ a IN dm /\
      decode_length c x = n2w (LENGTH vals) /\
      LENGTH vals < 2 ** (dimindex (:'a) − 4)
Proof
  fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
      bc_stack_ref_inv_def,v_inv_def,word_addr_def] \\ rw [get_addr_0]
  \\ `bc_ref_inv c p refs (f,tf,heap,be)` by
    (first_x_assum match_mp_tac \\ fs [reachable_refs_def]
     \\ qexists_tac `RefPtr bl p` \\ fs [get_refs_def])
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
  \\ fs [good_dimindex_def]
  \\ fs [fcpTheory.FCP_BETA,word_lsl_def,word_index]
QED

val expand_num =
  DECIDE ``4 = SUC 3 /\ 3 = SUC 2 /\ 2 = SUC 1 /\ 1 = SUC 0 /\
           5 = SUC 4 /\ 6 = SUC 5 /\ 7 = SUC 6 /\ 8 = SUC 7``

Theorem get_byte_set_byte_alt:
   good_dimindex (:'a) /\ w <> v /\ byte_align w = byte_align v /\
    get_byte w s be = x ==>
    get_byte w (set_byte v b (s:'a word) be) be = x
Proof
  rw [] \\ rpt_drule miscTheory.get_byte_set_byte_diff \\ fs []
QED

Theorem get_byte_bytes_to_word:
   ∀zs (t:'a word).
      i < LENGTH zs /\ i < 2 ** k /\
      2 ** k = dimindex(:'a) DIV 8 /\ good_dimindex (:'a) ⇒
      get_byte (n2w i) (bytes_to_word (2 ** k) 0w zs t be) be = EL i zs
Proof
  rw [] \\ fs [] \\ Cases_on `dimindex (:α) = 32` \\ fs [] THEN1
   (fs [LESS_4] \\ fs []
    \\ Cases_on `zs` \\ fs []
    \\ TRY (Cases_on `t'`) \\ fs []
    \\ TRY (Cases_on `t''`) \\ fs []
    \\ TRY (Cases_on `t`) \\ fs []
    \\ TRY (Cases_on `t'`) \\ fs []
    \\ ntac 10 (once_rewrite_tac [expand_num,bytes_to_word_def]
                \\ rpt (fs [miscTheory.good_dimindex_get_byte_set_byte]
                        \\ match_mp_tac get_byte_set_byte_alt
                        \\ fs [dimword_def,alignmentTheory.byte_align_def,
                               alignmentTheory.align_w2n])))
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
    \\ ntac 10 (once_rewrite_tac [expand_num,bytes_to_word_def]
                \\ rpt (fs [miscTheory.good_dimindex_get_byte_set_byte]
                        \\ match_mp_tac get_byte_set_byte_alt
                        \\ fs [dimword_def,alignmentTheory.byte_align_def,
                               alignmentTheory.align_w2n])))
  \\ rfs [good_dimindex_def]
QED

Triviality MOD_MULT_MOD_LEMMA:
  k MOD n = 0 /\ x MOD n = t /\ 0 < k /\ 0 < n /\ n <= k ==>
    x MOD k MOD n = t
Proof
  rw [] \\ drule DIVISION
  \\ disch_then (qspec_then `k` mp_tac) \\ strip_tac
  \\ qpat_x_assum `_ = _` (fn th => once_rewrite_tac [th])
  \\ fs [] \\ Cases_on `0 < k DIV n` \\ fs [MOD_MULT_MOD]
  \\ fs [DIV_EQ_X] \\ rfs [DIV_EQ_X]
QED

Theorem w2n_add_byte_align_lemma:
   good_dimindex (:'a) ==>
    w2n (a' + byte_align (a:'a word)) MOD (dimindex (:'a) DIV 8) =
    w2n a' MOD (dimindex (:'a) DIV 8)
Proof
  Cases_on `a'` \\ Cases_on `a`
  \\ fs [byte_align_def,align_w2n]
  \\ fs [good_dimindex_def] \\ rw []
  \\ fs [word_add_n2w] \\ fs [dimword_def]
  \\ match_mp_tac MOD_MULT_MOD_LEMMA \\ fs []
  \\ once_rewrite_tac [MULT_COMM]
  \\ once_rewrite_tac [ADD_COMM]
  \\ fs [MOD_TIMES]
QED

Theorem get_byte_byte_align:
   good_dimindex (:'a) ==>
    get_byte (a' + byte_align a) w be = get_byte a' (w:'a word) be
Proof
  fs [get_byte_def] \\ rw [] \\ rpt AP_TERM_TAC
  \\ fs [byte_index_def,w2n_add_byte_align_lemma]
QED

Theorem get_byte_eq:
   good_dimindex (:'a) /\ a = byte_align a + a' ==>
    get_byte a w be = get_byte a' (w:'a word) be
Proof
  rw [] \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs [get_byte_byte_align]
QED

Theorem write_bytes_same:
   ∀ws b1 b2.
   (∀n. n < LENGTH (ws:α word list) * (dimindex(:α) DIV 8) ⇒ n < LENGTH b1 ∧ n < LENGTH b2 ∧ EL n b1 = EL n b2)
   ⇒ write_bytes b1 ws be = write_bytes b2 ws be
Proof
   Induct \\ rw[write_bytes_def]
   >- (
     match_mp_tac bytes_to_word_same
     \\ gen_tac \\ strip_tac
     \\ first_x_assum match_mp_tac
     \\ simp[ADD1] )
  \\ first_x_assum match_mp_tac
  \\ gen_tac \\ strip_tac
  \\ fs[MULT]
  \\ qpat_abbrev_tac`bw= _ DIV _`
  \\ first_x_assum(qspec_then`n+bw`mp_tac)
  \\ simp[EL_DROP]
QED

Theorem set_byte_bytes_to_word:
   i < LENGTH ls ∧ i < 2 ** k ∧ 2 ** k = dimindex (:α) DIV 8 ∧
   good_dimindex(:α) ⇒
   set_byte (n2w i) b (bytes_to_word (2 ** k) 0w ls t be) be =
   bytes_to_word (2 ** k) (0w:'a word) (LUPDATE b i ls) t be
Proof
  rw[] \\ fs[] \\ fs[good_dimindex_def] \\ fs[]
  \\ fs[LESS_4,LESS_8] \\ fs[]
  \\ Cases_on`ls` \\ fs[]
  \\ TRY (Cases_on`t'`) \\ fs[]
  \\ TRY (Cases_on`t''`) \\ fs[]
  \\ TRY (Cases_on`t'`) \\ fs[]
  \\ TRY (Cases_on`t''`) \\ fs[]
  \\ TRY (Cases_on`t'`) \\ fs[]
  \\ TRY (Cases_on`t''`) \\ fs[]
  \\ TRY (Cases_on`t'`) \\ fs[]
  \\ rewrite_tac[expand_num,bytes_to_word_eq,LUPDATE_def] \\ fs [ADD1]
  \\ rpt (fs [Once set_byte_sort,good_dimindex_def]
          \\ AP_THM_TAC \\ AP_TERM_TAC)
QED

Theorem heap_in_memory_store_UpdateByte:
   heap_in_memory_store heap a sp sp1 gens c s m dm limit ∧
   heap = ha ++ [Bytes be fl bs ws] ++ hb ∧ i < LENGTH bs ∧
   ad = curr + bytes_in_word + n2w i + (bytes_in_word:'a word) * n2w (heap_length ha) ∧
   FLOOKUP s CurrHeap = SOME (Word curr) ∧
   m (byte_align ad) = Word w ∧ good_dimindex(:'a)
   ⇒
   heap_in_memory_store (ha ++ [Bytes be fl (LUPDATE b i bs) ws] ++ hb)
   a sp sp1 gens c s
   ((byte_align ad =+ Word (set_byte ad b w be)) m) dm limit
Proof
  rw[heap_in_memory_store_def]
  \\ fs[heap_length_Bytes,heap_length_APPEND]
  \\ clean_tac
  \\ fs[byte_aligned_def,byte_align_def]
  \\ qmatch_goalsub_abbrev_tac`align p _`
  \\ qpat_abbrev_tac`ad = _ + bytes_in_word * _`
  \\ qspec_then`dimindex(:α)DIV 8`mp_tac DIVISION
  \\ impl_tac >- fs[good_dimindex_def]
  \\ disch_then(qspec_then`i`strip_assume_tac)
  \\ qmatch_assum_abbrev_tac`i = j * bw + r`
  \\ `ad = curr + bytes_in_word * (n2w (heap_length ha + j + 1)) + n2w r`
  by (
    simp[Abbr`ad`,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ simp[GSYM word_mul_n2w,Abbr`bw`,bytes_in_word_def])
  \\ qunabbrev_tac`ad`
  \\ pop_assum SUBST_ALL_TAC
  \\ qmatch_goalsub_abbrev_tac`ad + n2w r`
  \\ `aligned p ad`
  by (
    qunabbrev_tac`ad`
    \\ `∃n. (bytes_in_word:'a word) = n2w (2 ** p)`
    by (
      simp[bytes_in_word_def,Abbr`p`,dimword_def]
      \\ fs[good_dimindex_def,Abbr`bw`] )
    \\ pop_assum SUBST_ALL_TAC
    \\ REWRITE_TAC[word_mul_n2w]
    \\ metis_tac[aligned_add_pow,MULT_COMM] )
  \\ `w2n (n2w r) < 2 ** p`
  by (
    simp[Abbr`p`]
    \\ `bw = 2 ** LOG2 bw`
    by ( fs[Abbr`bw`,good_dimindex_def] )
    \\ simp[] )
  \\ drule align_add_aligned
  \\ disch_then drule
  \\ disch_then SUBST_ALL_TAC
  \\ qpat_x_assum`i = _`(assume_tac o SYM)
  \\ fs[word_heap_APPEND]
  \\ fs[word_heap_def,Bytes_def,word_el_def,word_payload_def,SEP_CLAUSES]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ qhdtm_assum`decode_length`(mp_tac o Q.AP_TERM`w2n`)
  \\ qspec_then`LENGTH bs`mp_tac (Q.GEN`len`decode_length_make_byte_header)
  \\ impl_tac >- ( fs[shift_def] )
  \\ rpt strip_tac
  \\ pop_assum SUBST_ALL_TAC
  \\ qmatch_assum_abbrev_tac`lws ≤ _ + 1n`
  \\ `lws = LENGTH ws`
  by (
    simp[Abbr`lws`]
    \\ fs[good_dimindex_def,dimword_def]
    \\ fs[] )
  \\ qunabbrev_tac`lws` \\ fs[]
  \\ `∃b1 b b2. bs = b1 ++ b::b2 ∧ i = LENGTH b1 (* ∧ bw ≤ LENGTH bs - bw * (LENGTH b1 DIV bw)*)`
  by (
    qexists_tac`TAKE i bs`
    \\ qispl_then[`i`,`bs`]mp_tac TAKE_DROP
    \\ disch_then(CONV_TAC o STRIP_QUANT_CONV o LAND_CONV o LAND_CONV o REWR_CONV o SYM)
    \\ simp[]
    \\ Cases_on`DROP i bs` >- ( fs[DROP_NIL] )
    \\ simp[] \\ rfs[])
  \\ pop_assum SUBST_ALL_TAC
  \\ pop_assum SUBST_ALL_TAC
  \\ REWRITE_TAC[LUPDATE_LENGTH]
  \\ qmatch_goalsub_abbrev_tac`LENGTH bs`
  \\ qmatch_goalsub_abbrev_tac`write_bytes bs'`
  \\ `∃w1 w2. ws = w1 ++ w2 ∧ LENGTH w1 = j`
  by (
    qispl_then[`j`,`ws`](SUBST1_TAC o SYM)TAKE_DROP
    \\ qexists_tac`TAKE j ws` \\ simp[]
    \\ dep_rewrite.DEP_REWRITE_TAC[LENGTH_TAKE]
    \\ simp[Abbr`j`,DIV_LE_X]
    \\ fs[Abbr`bs`,Abbr`bw`] )
  \\ qunabbrev_tac`j`
  \\ clean_tac
  \\ simp[write_bytes_APPEND]
  \\ ONCE_REWRITE_TAC[CONS_APPEND]
  \\ REWRITE_TAC[APPEND_ASSOC]
  \\ ONCE_REWRITE_TAC[word_list_APPEND]
  \\ fs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ qpat_x_assum`_ (fun2set _)`mp_tac
  \\ qmatch_goalsub_abbrev_tac`ha ++ [bytes]`
  \\ `bytes = Bytes be fl bs ((w1 ++ w2))`
  by ( simp[Bytes_def,Abbr`bytes`] )
  \\ qunabbrev_tac`bytes` \\ pop_assum SUBST_ALL_TAC
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`ha ++ [bytes]`
  \\ `bytes = Bytes be fl bs' ((w1 ++ w2))`
  by (
    simp[Bytes_def,Abbr`bytes`]
    \\ simp[Abbr`bs'`,Abbr`bs`]
    \\ simp[write_bytes_APPEND] )
  \\ qunabbrev_tac`bytes` \\ pop_assum SUBST_ALL_TAC
  \\ pop_assum mp_tac
  \\ qmatch_abbrev_tac`_ ⇒ G`
  \\ simp[write_bytes_APPEND]
  \\ ONCE_REWRITE_TAC[CONS_APPEND]
  \\ REWRITE_TAC[APPEND_ASSOC]
  \\ ONCE_REWRITE_TAC[word_list_APPEND]
  \\ fs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,Abbr`G`]
  \\ `write_bytes bs' w1 be = write_bytes bs w1 be`
  by (
    match_mp_tac write_bytes_same
    \\ simp[]
    \\ simp[Abbr`bs'`,Abbr`bs`,EL_APPEND1] )
  \\ fs[]
  \\ `∃wx wr. w2 = [wx] ++ wr`
  by (
    Cases_on`w2`\\fs[]
    \\ fs[Abbr`bs`,DIV_LE_X,Abbr`bw`])
  \\ clean_tac
  \\ REWRITE_TAC[write_bytes_APPEND]
  \\ simp[write_bytes_def]
  \\ qpat_abbrev_tac`bt = DROP _ (DROP _ bs)`
  \\ qpat_abbrev_tac`bt' = DROP _ (DROP _ bs')`
  \\ `bt' = bt`
  by (
    simp[Abbr`bt'`,Abbr`bt`]
    \\ simp[Abbr`bs`,Abbr`bs'`]
    \\ asm_simp_tac(std_ss++ARITH_ss)
         [DROP_APPEND,LENGTH_APPEND,LENGTH,DROP_def,LENGTH_DROP])
  \\ qunabbrev_tac`bt'` \\ pop_assum SUBST_ALL_TAC
  \\ qpat_abbrev_tac`bh = Word (make_byte_header _ _ _)::_`
  \\ simp[word_list_def]
  \\ strip_tac
  \\ SEP_W_TAC
  \\ rfs[heap_length_APPEND,heap_length_Bytes]
  \\ qmatch_goalsub_abbrev_tac`Word sb`
  \\ qmatch_asmsub_abbrev_tac`Word sb'`
  \\ ntac 3 (pop_assum mp_tac)
  \\ qmatch_asmsub_abbrev_tac`Word sb0`
  \\ ntac 3 strip_tac
  \\ `m ad = Word sb0` by SEP_R_TAC
  \\ rfs[Abbr`sb0`]
  \\ clean_tac
  \\ `sb' = sb`
  by (
    simp[Abbr`sb'`,Abbr`sb`]
    \\ qpat_x_assum`LENGTH w1 = _`(assume_tac o SYM) \\ fs[]
    \\ `DROP (bw * LENGTH w1) bs' = DROP (bw * LENGTH w1) b1 ++ [b] ++ b2`
    by (
      qpat_x_assum`_ = LENGTH b1`(assume_tac o SYM)
      \\ asm_simp_tac(std_ss++ARITH_ss)[Abbr`bs'`,DROP_APPEND,LENGTH_APPEND,LENGTH,DROP_def,APPEND_11]
      \\ qmatch_abbrev_tac`DROP n b2 = b2`
      \\ `n = 0` by ( simp[Abbr`n`] )
      \\ simp[] )
    \\ pop_assum SUBST_ALL_TAC
    \\ `DROP (bw * LENGTH w1) bs = DROP (bw * LENGTH w1) b1 ++ [b'] ++ b2`
    by (
      qpat_x_assum`_ = LENGTH b1`(assume_tac o SYM)
      \\ asm_simp_tac(std_ss++ARITH_ss)[Abbr`bs`,DROP_APPEND,LENGTH_APPEND,LENGTH,DROP_def,APPEND_11]
      \\ qmatch_abbrev_tac`DROP n b2 = b2`
      \\ `n = 0` by ( simp[Abbr`n`] )
      \\ simp[] )
    \\ pop_assum SUBST_ALL_TAC
    \\ qmatch_abbrev_tac`set_byte (ad + n2w r) b w be = _`
    \\ `set_byte (ad + n2w r) b w be = set_byte (n2w r) b w be`
    by (
      match_mp_tac set_byte_change_a
      \\ `ad = byte_align ad`
      by ( metis_tac[byte_aligned_def,aligned_def,byte_align_def] )
      \\ ONCE_REWRITE_TAC[WORD_ADD_COMM]
      \\ pop_assum SUBST1_TAC
      \\ match_mp_tac w2n_add_byte_align_lemma
      \\ simp[] )
    \\ pop_assum SUBST_ALL_TAC
    \\ qunabbrev_tac`w`
    \\ `∃k. bw = 2 ** k`
    by (
      fs[Abbr`bw`]
      \\ fs[good_dimindex_def]
      \\ TRY(qexists_tac`2` \\ simp[] \\ NO_TAC)
      \\ TRY(qexists_tac`3` \\ simp[] \\ NO_TAC) )
    \\ first_assum SUBST1_TAC
    \\ dep_rewrite.DEP_REWRITE_TAC[set_byte_bytes_to_word]
    \\ pop_assum(SUBST_ALL_TAC o SYM)
    \\ conj_tac >- ( simp[] )
    \\ `r = LENGTH (DROP (bw * LENGTH w1) b1)`
    by ( simp[] )
    \\ pop_assum SUBST1_TAC
    \\ simp[lupdate_append2] )
  \\ fsrw_tac[star_ss][]
QED

Definition hide_memory_rel_def:
  hide_memory_rel = memory_rel
End

Definition hide_heap_in_memory_store_def:
  hide_heap_in_memory_store = heap_in_memory_store
End

Theorem memory_rel_ByteArray_IMP:
   memory_rel c be ts refs sp st m dm ((RefPtr bl p,v:'a word_loc)::vars) /\
   lookup p refs = SOME (ByteArray fl vals) /\ good_dimindex (:'a) ==>
   ?w a x l.
     v = Word w /\ w ' 0 /\
     make_byte_header c fl (LENGTH vals) = x /\
     ~(word_bit 3 x) /\ (word_bit 4 x ⇔ ¬fl) /\ word_bit 2 x /\
     get_real_simple_addr c st w = SOME a /\
     get_real_addr c st w = SOME a /\
     m a = Word x /\ a IN dm /\
     (!i. i < LENGTH vals ==>
          mem_load_byte_aux m dm be (a + bytes_in_word + n2w i) =
          SOME (EL i vals)) /\
     (∀i w. i < LENGTH vals ⇒
       let addr = a + bytes_in_word + n2w i in
       memory_rel c be ts (insert p (ByteArray fl (LUPDATE w i vals)) refs) sp st
         ((byte_align addr =+
           Word (set_byte addr w (theWord (m (byte_align addr))) be)) m) dm
           ((RefPtr bl p,v)::vars)) ∧
     if dimindex (:'a) = 32 then
       LENGTH vals + 4 < 2 ** (dimindex (:'a) - 3) /\
       (x >>> (dimindex (:'a) - c.len_size - 2) = n2w (LENGTH vals + 4))
     else
       LENGTH vals + 8 < 2 ** (dimindex (:'a) - 3) /\
       (x >>> (dimindex (:'a) - c.len_size - 3) = n2w (LENGTH vals + 8))
Proof
  CONV_TAC(RAND_CONV(REWRITE_CONV[GSYM hide_memory_rel_def]))
  \\ qpat_abbrev_tac`P = $= (make_byte_header _ _ _)`
  \\ fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS,
         bc_stack_ref_inv_def,v_inv_def,word_addr_def]
  \\ rpt strip_tac
  \\ drule (GEN_ALL update_byte_ref_thm)
  \\ strip_tac
  \\ qhdtm_x_assum`abs_ml_inv`mp_tac \\ rfs[]
  \\ simp[abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def,word_addr_def]
  \\ rw [get_addr_0]
  \\ `bc_ref_inv c p refs (f,tf,heap,be)` by
    (first_x_assum match_mp_tac \\ fs [reachable_refs_def]
     \\ qexists_tac `RefPtr bl p` \\ fs [get_refs_def])
  \\ pop_assum mp_tac \\ simp [bc_ref_inv_def]
  \\ fs [FLOOKUP_DEF] \\ rw []
  \\ drule (GEN_ALL heap_in_memory_store_UpdateByte)
  \\ ONCE_REWRITE_TAC[GSYM hide_heap_in_memory_store_def]
  \\ strip_tac
  \\ fs [word_addr_def,heap_in_memory_store_def]
  \\ rpt_drule get_real_addr_get_addr \\ disch_then kall_tac
  \\ imp_res_tac heap_lookup_SPLIT \\ clean_tac
  \\ fs [word_heap_APPEND,word_heap_def,RefBlock_def,word_el_def,
         word_payload_def,word_list_def,Bytes_def]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ imp_res_tac EVERY2_LENGTH \\ SEP_R_TAC \\ fs [get_addr_0]
  \\ simp[Abbr`P`]
  \\ conj_asm1_tac
  THEN1 (fs [make_byte_header_def,word_bit_def,word_or_def,fcpTheory.FCP_BETA]
    \\ fs [good_dimindex_def]
    \\ IF_CASES_TAC
    \\ fs [fcpTheory.FCP_BETA,word_lsl_def,word_index])
  \\ conj_asm1_tac
  THEN1 (fs [make_byte_header_def,word_bit_def,word_or_def,fcpTheory.FCP_BETA]
    \\ fs [good_dimindex_def]
    \\ IF_CASES_TAC
    \\ fs [fcpTheory.FCP_BETA,word_lsl_def,word_index])
  \\ conj_tac
  THEN1 (fs [make_byte_header_def,word_bit_def,word_or_def,fcpTheory.FCP_BETA]
    \\ fs [good_dimindex_def]
    \\ IF_CASES_TAC
    \\ fs [fcpTheory.FCP_BETA,word_lsl_def,word_index])
  \\ conj_asm1_tac
  THEN1
   (rpt strip_tac
    \\ first_x_assum(qspec_then`ARB`kall_tac)
    \\ first_x_assum(qspec_then`ARB`kall_tac)
    \\ fs [wordSemTheory.mem_load_byte_aux_def]
    \\ fs [alignmentTheory.byte_align_def,bytes_in_word_def]
    \\ qabbrev_tac `k = LOG2 (dimindex (:α) DIV 8)`
    \\ qabbrev_tac `ws = LENGTH vals DIV 2 ** k + 1`
    \\ `dimindex (:α) DIV 8 = 2 ** k` by
         (rfs [good_dimindex_def,Abbr`k`] \\ NO_TAC) \\ fs []
    \\ `(align k (curr + n2w (2 ** k) +
                  n2w (heap_length ha) * n2w (2 ** k) + n2w i) =
         curr + n2w (2 ** k) + n2w (heap_length ha) * n2w (2 ** k) +
         n2w (i DIV 2 ** k * 2 ** k))` by
     (`0n < 2 ** k` by fs []
      \\ drule DIVISION
      \\ disch_then (qspec_then `i` strip_assume_tac)
      \\ qpat_x_assum `_ = _` (fn th => simp_tac std_ss [Once th]
            THEN assume_tac (GSYM th))
      \\ simp_tac std_ss [GSYM word_add_n2w,WORD_ADD_ASSOC]
      \\ match_mp_tac align_add_aligned
      \\ fs [aligned_add_pow,word_mul_n2w,byte_aligned_def]
      \\ sg `i MOD 2 ** k < dimword (:'a)` \\ fs []
      \\ match_mp_tac LESS_LESS_EQ_TRANS \\ qexists_tac `2 ** k` \\ fs []
      \\ fs [dimword_def]
      \\ fs [good_dimindex_def] \\ rfs []
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
      \\ qpat_x_assum `_ = _` (fn th => simp_tac std_ss [Once th])
      \\ Cases_on `curr` \\ fs [word_add_n2w,word_mul_n2w] \\ NO_TAC)
    \\ fs []
    \\ `i DIV 2 ** k < ws` by
        (fs [DIV_LT_X,RIGHT_ADD_DISTRIB]
         \\ fs [Abbr`ws`]
         \\ `0n < 2 ** k` by fs []
         \\ rpt_drule DIVISION
         \\ disch_then (qspec_then `LENGTH vals` strip_assume_tac)
         \\ decide_tac)
    \\ `(curr + n2w (i DIV 2 ** k * 2 ** k) + n2w (2 ** k) +
          n2w (heap_length ha) * n2w (2 ** k) IN dm) /\
        m (curr + n2w (i DIV 2 ** k * 2 ** k) + n2w (2 ** k) +
          n2w (heap_length ha) * n2w (2 ** k)) =
        (EL (i DIV 2 ** k) (MAP Word (write_bytes vals (REPLICATE ws 0w) be)))` by
     (`i DIV 2 ** k < LENGTH (MAP Word (write_bytes vals (REPLICATE ws 0w) be))` by
                (fs [] \\ decide_tac)
      \\ drule LESS_LENGTH \\ strip_tac \\ clean_tac
      \\ fs [word_list_def,word_list_APPEND,bytes_in_word_def,word_mul_n2w]
      \\ SEP_R_TAC \\ fs []
      \\ pop_assum (fn th => rewrite_tac [GSYM th])
      \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ fs [EL_LENGTH_APPEND])
    \\ fs [EL_MAP,LENGTH_write_bytes]
    \\ `i DIV 2 ** k < LENGTH (REPLICATE ws 0w)` by simp[]
    \\ drule LESS_LENGTH \\ strip_tac \\ clean_tac
    \\ rename [‘REPLICATE ws 0w = ys ++ t::ts’]
    \\ fs [write_bytes_APPEND]
    \\ `i DIV 2 ** k = LENGTH (write_bytes vals ys be)` by
          metis_tac [LENGTH_write_bytes]
    \\ asm_simp_tac std_ss [write_bytes_def,LET_DEF,GSYM APPEND_ASSOC,APPEND]
    \\ asm_simp_tac std_ss [EL_LENGTH_APPEND,NULL_DEF,HD]
    \\ fs [] \\ pop_assum (fn th => fs [GSYM th]) \\ fs []
    \\ `EL i vals =
        EL (i MOD 2 ** k) (DROP (i DIV 2 ** k * 2 ** k) vals)` by
     (`0n < 2 ** k` by fs []
      \\ rpt_drule DIVISION
      \\ disch_then (qspec_then `i` strip_assume_tac)
      \\ qpat_x_assum `_ = _` (fn th => simp [Once th] THEN assume_tac (GSYM th))
      \\ once_rewrite_tac [ADD_COMM]
      \\ match_mp_tac (GSYM EL_DROP) \\ decide_tac)
    \\ fs [] \\ match_mp_tac get_byte_bytes_to_word \\ fs []
    \\ `0n < 2 ** k` by fs []
    \\ rpt_drule DIVISION
    \\ disch_then (qspec_then `i` strip_assume_tac)
    \\ decide_tac)
  \\ conj_tac
  >- (
    rpt strip_tac
    \\ first_x_assum(qspec_then`i`mp_tac)
    \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`byte_align ad`
    \\ rw[hide_memory_rel_def]
    \\ rw[memory_rel_def]
    \\ fs[wordSemTheory.mem_load_byte_aux_def]
    \\ Cases_on`m (byte_align ad)` \\ fs[]
    \\ qmatch_asmsub_abbrev_tac`ha ++ bytes ::hb`
    \\ qabbrev_tac `ws = LENGTH vals DIV (dimindex (:α) DIV 8) + 1`
    \\ `bytes = Bytes be fl vals (REPLICATE ws 0w)` by simp[Abbr`bytes`,Bytes_def]
    \\ qunabbrev_tac`bytes` \\ fs[]
    \\ simp[theWord_def]
    \\ rfs[]
    \\ first_x_assum(qspecl_then[`i`,`ha`]mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["i'","ha'"])))
    \\ simp[]
    \\ pop_assum (assume_tac o SYM)
    \\ simp[]
    \\ pop_assum (assume_tac o SYM)
    \\ disch_then(qspec_then`REPLICATE ws 0w`mp_tac) \\ simp[]
    \\ disch_then(qspec_then`vals`mp_tac) \\ simp[]
    \\ disch_then(qspec_then`be`mp_tac) \\ simp[]
    \\ disch_then(qspec_then`w`mp_tac)
    \\ simp[hide_heap_in_memory_store_def]
    \\ strip_tac
    \\ asm_exists_tac
    \\ simp[]
    \\ simp[word_ml_inv_def]
    \\ first_x_assum(qspec_then`LUPDATE w i vals`mp_tac)
    \\ simp[]
    \\ strip_tac
    \\ simp[PULL_EXISTS]
    \\ first_assum(part_match_exists_tac (last o strip_conj) o concl)
    \\ simp[]
    \\ `h1 = ha`
    by (
      fs[APPEND_EQ_APPEND]
      \\ fs[heap_length_APPEND]
      \\ fs[heap_length_def,el_length_def]
      \\ clean_tac \\ fs[]
      \\ fs[APPEND_EQ_SING]
      \\ clean_tac \\ fs[]
      \\ fs[el_length_def]
      \\ fs[integerTheory.EQ_ADDL,el_length_def,Bytes_def])
    \\ fs[] \\ clean_tac
    \\ `write_bytes vals (REPLICATE (LENGTH ws') 0w) be = write_bytes vals ws' be`
    by (
      Q.ISPEC_THEN`Word`match_mp_tac INJ_MAP_EQ
      \\ simp[INJ_DEF] )
    \\ fs[]
    \\ drule (UNDISCH write_bytes_inj_lemma)
    \\ disch_then(qspec_then`LUPDATE w i vals`mp_tac)
    \\ simp[] \\ strip_tac \\ fs[]
    \\ asm_exists_tac
    \\ simp[word_addr_def])
  \\ qpat_x_assum `LENGTH vals + _ < 2 ** (_ + _)` assume_tac
  \\ `LENGTH vals + 2**(if dimindex (:α) = 32 then 2 else 3) < dimword (:'a)` by
   (match_mp_tac LESS_LESS_EQ_TRANS \\ asm_exists_tac \\ fs []
    \\ rewrite_tac [dimword_def,EXP_BASE_LE_IFF] \\ simp [])
  \\ fs [good_dimindex_def,make_byte_header_def,
         LENGTH_write_bytes] \\ rfs []
  THEN1 (
    `4 <= 30 - c.len_size` by decide_tac
    \\ `c.len_size <= 30` by decide_tac
    \\ pop_assum mp_tac
    \\ simp [LESS_EQ_EXISTS] \\ strip_tac \\ fs []
    \\ rename1 `4n <= k`
    \\ qmatch_goalsub_abbrev_tac`_ || www >>> k`
    \\ `www >>> k = 0w`
    by (srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index,Abbr`www`]
        \\ Cases_on `i + k < 32`
        \\ simp [wordsTheory.word_index] \\ NO_TAC)
    \\ simp []
    \\ conj_tac
    >- (
      `c.len_size + 2 ≤ 29` by decide_tac
      \\ drule bitTheory.TWOEXP_MONO2
      \\ CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[])))
      \\ decide_tac)
    \\ match_mp_tac lsl_lsr
    \\ simp [wordsTheory.dimword_def]
    \\ `c.len_size = 30 - k` by decide_tac \\ fs []
    \\ fs [EXP_SUB,X_LT_DIV,RIGHT_ADD_DISTRIB]
    \\ qmatch_assum_abbrev_tac`(x:num) + y ≤ z`
    \\ qmatch_abbrev_tac`x + y' < z`
    \\ `y' < y` by simp[Abbr`y`,Abbr`y'`]
    \\ decide_tac)
  THEN1 (
    `5 <= 61 - c.len_size` by decide_tac
    \\ `c.len_size <= 61` by decide_tac \\ pop_assum mp_tac
    \\ simp [LESS_EQ_EXISTS] \\ strip_tac \\ fs []
    \\ rename1 `5n <= k` \\ fs []
    \\ qmatch_goalsub_abbrev_tac`_ || www >>> k`
    \\ `www >>> k = 0w`
    by (
      rw[Abbr`www`]
      \\ match_mp_tac n2w_lsr_eq_0
      \\ simp[dimword_def]
      \\ match_mp_tac LESS_DIV_EQ_ZERO
      \\ `32 ≤ 2n ** k` suffices_by simp[]
      \\ `32n = 2 ** 5` by simp[]
      \\ pop_assum SUBST1_TAC
      \\ match_mp_tac bitTheory.TWOEXP_MONO2
      \\ simp[] )
    \\ simp[] \\ rfs [dimword_def]
    \\ conj_tac
    >- (
      `c.len_size + 3 ≤ 61` by decide_tac
      \\ drule bitTheory.TWOEXP_MONO2
      \\ CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[])))
      \\ decide_tac)
    \\ match_mp_tac lsl_lsr
    \\ simp[dimword_def]
    \\ `c.len_size = 61 - k` by decide_tac \\ fs []
    \\ fs [EXP_SUB,X_LT_DIV,RIGHT_ADD_DISTRIB]
    \\ qmatch_assum_abbrev_tac`(x:num) + y ≤ z`
    \\ qmatch_abbrev_tac`x + y' < z`
    \\ `y' < y` by simp[Abbr`y`,Abbr`y'`]
    \\ decide_tac)
QED

Theorem memory_rel_RefPtr_IMP_lemma:
   memory_rel c be ts refs sp st m dm ((RefPtr bl p,v:'a word_loc)::vars) ==>
    ?res. lookup p refs = SOME res
Proof
  fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
      bc_stack_ref_inv_def,v_inv_def,word_addr_def] \\ rw []
  \\ `bc_ref_inv c p refs (f,tf,heap,be)` by
    (first_x_assum match_mp_tac \\ fs [reachable_refs_def]
     \\ qexists_tac `RefPtr bl p` \\ fs [get_refs_def])
  \\ fs [SUBSET_DEF,domain_lookup]
QED

Theorem memory_rel_RefPtr_IMP':
  memory_rel c be ts refs sp st m dm ((RefPtr bl p,v)::vars) ∧
  good_dimindex (:α) ⇒
  ∃w a x.
    v = Word w ∧ w ' 0 ∧ (word_bit 4 x ⇒ word_bit 2 x) ∧
    (word_bit 3 x ⇔ ¬word_bit 2 x) ∧
    data_to_word_memoryProof$get_real_addr c st w = SOME a ∧
    get_real_simple_addr c st w = SOME a ∧
    m a = Word (x:'a word) ∧ a ∈ dm
Proof
  strip_tac \\ drule memory_rel_RefPtr_IMP_lemma \\ strip_tac
  \\ Cases_on `res` \\ fs []
  THEN1 (rpt_drule memory_rel_ValueArray_IMP \\ rw [] \\ fs [])
  THEN1 (rpt_drule memory_rel_ByteArray_IMP \\ rw [] \\ fs [])
QED

Theorem memory_rel_RefPtr_IMP:
   memory_rel c be ts refs sp st m dm ((RefPtr bl p,v:'a word_loc)::vars) /\
    good_dimindex (:'a) ==>
    ?w a x.
      v = Word w /\ w ' 0 /\ (word_bit 4 x ==> word_bit 2 x) /\
      (word_bit 3 x <=> ~word_bit 2 x) /\
      get_real_addr c st w = SOME a /\ m a = Word x /\ a IN dm
Proof
  rw [] \\ drule_all memory_rel_RefPtr_IMP' \\ rw [] \\ fs []
QED

Theorem Smallnum_bits:
   (1w && Smallnum i) = 0w /\ (2w && Smallnum i) = 0w
Proof
  Cases_on `i`
  \\ srw_tac [wordsLib.WORD_MUL_LSL_ss]
             [Smallnum_def, GSYM wordsTheory.word_mul_n2w]
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index]
QED

Theorem memory_rel_any_Number_IMP:
   good_dimindex (:'a) /\
    memory_rel c be ts refs sp st m dm ((Number i,v:'a word_loc)::vars) ==>
    ?w. v = Word w /\ (w ' 0 <=> ~small_int (:'a) i)
Proof
  fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
      bc_stack_ref_inv_def,v_inv_def] \\ rw []
  \\ fs [word_addr_def,get_addr_0]
  \\ fs [fcpTheory.FCP_BETA,word_and_def,word_index]
  \\ rewrite_tac [WORD_NEG,WORD_ADD_BIT0,word_index,word_1comp_def]
  \\ simp_tac std_ss [fcpTheory.FCP_BETA,DIMINDEX_GT_0,word_1comp_def]
  \\ EVAL_TAC
QED

Theorem memory_rel_Number_IMP:
   good_dimindex (:'a) /\ small_int (:'a) i /\
    memory_rel c be ts refs sp st m dm ((Number i,v:'a word_loc)::vars) ==>
    v = Word (Smallnum i)
Proof
  fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
      bc_stack_ref_inv_def,v_inv_def] \\ rw []
  \\ fs [word_addr_def,Smallnum_def,integer_wordTheory.i2w_def]
  \\ Cases_on `i`
  \\ fs [GSYM word_mul_n2w,word_ml_inv_num_lemma,word_ml_inv_neg_num_lemma]
QED

Theorem memory_rel_Number_bignum_IMP_ALT:
   memory_rel c be ts refs sp st m dm ((Number i,v)::vars) /\
    ~small_int (:'a) i /\ good_dimindex (:'a) ==>
    ?ff w x a y.
      v = Word w /\ (w && 1w) <> (0w:'a word) /\
      get_real_addr c st w = SOME a /\
      a IN dm /\ m a = Word x /\ ((x && 8w) <> 0w) /\
      word_bit 2 x /\ word_bit 3 x /\
      (word_bit 4 x <=> i < 0) /\
      (word_list (a + bytes_in_word)
        (MAP Word (n2mw (Num (ABS i)))) * ff) (fun2set (m,dm)) /\
      a + bytes_in_word IN dm /\
      m (a + bytes_in_word) = Word (n2w (Num (ABS i))) /\
      ((x && 16w) = 0w <=> 0 <= i) /\
      LENGTH (n2mw (Num (ABS i)):'a word list) < 2 ** (dimindex (:α) − 4) /\
      LENGTH (n2mw (Num (ABS i)):'a word list) < dimword (:'a) /\
      decode_length c x = n2w
        (LENGTH (n2mw (Num (ABS i)):'a word list))
Proof
  fs[memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
     bc_stack_ref_inv_def,v_inv_def] \\ rw[] \\ fs[word_addr_def]
  \\ fs[heap_in_memory_store_def]
  \\ imp_res_tac get_real_addr_get_addr \\ fs []
  \\ fs [GSYM PULL_EXISTS]
  \\ conj_tac THEN1
   (fs [get_addr_def,make_ptr_def,get_lowerbits_def]
    \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index])
  \\ imp_res_tac heap_lookup_SPLIT \\ rveq
  \\ fs[word_heap_APPEND,word_heap_def,word_el_def,UNCURRY,word_list_def,
        Bignum_def,multiwordTheory.i2mw_def]
  \\ `?ns. n2mw (Num (ABS i)) = (n2w (Num (ABS i))) :: ns` by
   (once_rewrite_tac [multiwordTheory.n2mw_def]
    \\ rw [n2w_mod]
    \\ fs [small_int_def]
    \\ fs [good_dimindex_def,dimword_def] \\ rfs []
    \\ fs [good_dimindex_def,dimword_def] \\ rfs []
    \\ intLib.COOPER_TAC)
  \\ fs [word_payload_def,make_header_def]
  \\ qmatch_asmsub_abbrev_tac `word_heap A hb`
  \\ qmatch_asmsub_abbrev_tac `one
           (curr + bytes_in_word * n2w (heap_length ha),B)`
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR,w2n_n2w]
  \\ fs [PULL_EXISTS]
  \\ qexists_tac `word_heap curr ha c *
        one (curr + bytes_in_word * n2w (heap_length ha),B) *
        word_heap A hb c * word_heap other (heap_expand limit) c`
  \\ fs [AC STAR_ASSOC STAR_COMM]
  \\ fs [word_payload_def,make_header_def,word_list_def]
  \\ SEP_R_TAC \\ simp[]
  \\ unabbrev_all_tac \\ fs []
  \\ `SUC (LENGTH ns) < dimword (:α)` by
    (fs [good_dimindex_def,dimword_def]
     \\ rfs [] \\ fs [] \\ NO_TAC)
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index]
  \\ fs [GSYM integerTheory.INT_NOT_LT]
  \\ Cases_on `i < 0i` \\ fs [] \\ EVAL_TAC
QED

Theorem memory_rel_Number_bignum_header:
   memory_rel c be ts refs sp st m dm ((Number i,v:'a word_loc)::vars) /\
    ~small_int (:'a) i /\ good_dimindex (:'a) ==>
    ?ff w x a y.
      v = Word w /\ get_real_addr c st w = SOME a /\
      IS_SOME ((encode_header c (w2n ((b2w (i < 0) ≪ 2 || 3w):'a word))
          (LENGTH (n2mw (Num (ABS i)):'a word list))):'a word option) /\
      m a = Word (make_header c (b2w (i < 0) ≪ 2 || 3w)
              (LENGTH (n2mw (Num (ABS i)):'a word list)))
Proof
  fs[memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
     bc_stack_ref_inv_def,v_inv_def] \\ rw[] \\ fs[word_addr_def]
  \\ fs[heap_in_memory_store_def]
  \\ imp_res_tac get_real_addr_get_addr \\ fs []
  \\ fs [GSYM PULL_EXISTS]
  \\ imp_res_tac heap_lookup_SPLIT \\ rveq
  \\ fs[word_heap_APPEND,word_heap_def,word_el_def,UNCURRY,word_list_def,
        Bignum_def,multiwordTheory.i2mw_def]
  \\ fs [word_payload_def,make_header_def]
  \\ SEP_R_TAC \\ fs []
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
QED

Theorem memory_rel_bignum_cmp:
   memory_rel c be ts refs sp st m dm
        ((Number i1,v1)::(Number i2,v2:'a word_loc)::vars) /\
    good_dimindex (:'a) /\ ~small_int (:'a) i1 /\ ~small_int (:'a) i2 ==>
    ?w1 w2 a1 a2 x1 x2.
       v1 = Word w1 /\ v2 = Word w2 /\
       get_real_addr c st w1 = SOME a1 /\
       get_real_addr c st w2 = SOME a2 /\
       m a1 = Word x1 /\
       m a2 = Word x2 /\
       (x1 <> x2 ==>
        (decode_length c (x1) = decode_length c (x2)) ==>
        ((16w && x1) = 0w) <> ((16w && x2) = 0w))
Proof
  fs [``~word_bit 4 w`` |> SIMP_CONV (srw_ss()) [word_bit_test] |> GSYM]
  \\ strip_tac
  \\ rpt_drule memory_rel_Number_bignum_header
  \\ rpt_drule memory_rel_Number_bignum_IMP_ALT
  \\ imp_res_tac memory_rel_tail
  \\ rpt_drule memory_rel_Number_bignum_header
  \\ rpt_drule memory_rel_Number_bignum_IMP_ALT
  \\ rw [] \\ fs []
  \\ fs [``~word_bit 4 w`` |> SIMP_CONV (srw_ss()) [word_bit_test] |> GSYM]
  \\ rfs [] \\ rveq \\ fs [] \\ rw [] \\ CCONTR_TAC \\ fs []
QED

Theorem memory_rel_Number_bignum_IMP:
   memory_rel c be ts refs sp st m dm ((Number i,v)::vars) /\
    ~small_int (:'a) i /\ good_dimindex (:'a) ==>
    ?w x a y.
      v = Word w /\ (w && 1w) <> (0w:'a word) /\
      get_real_addr c st w = SOME a /\
      a IN dm /\ m a = Word x /\ ((x && 8w) <> 0w) /\
      a + bytes_in_word IN dm /\
      m (a + bytes_in_word) = Word (n2w (Num (ABS i))) /\
      ((x && 16w) = 0w <=> 0 <= i)
Proof
  metis_tac [memory_rel_Number_bignum_IMP_ALT]
QED

Theorem memory_rel_Word64_IMP:
   memory_rel c be ts refs sp st m dm ((Word64 w64,v:'a word_loc)::vars) /\
   good_dimindex (:'a) ==>
   ?ptr x w.
     v = Word (get_addr c ptr (Word 0w)) ∧
     get_real_addr c st (get_addr c ptr (Word 0w)) = SOME x ∧
     x ∈ dm ∧ m x = Word w ∧ word_bit 3 w ∧ ¬word_bit 4 w ∧ word_bit 2 w ∧
     (x + bytes_in_word) ∈ dm ∧
     if dimindex (:'a) < 64 then
       (m (x + bytes_in_word) = Word ((63 >< 32) w64) ∧
        (x + (bytes_in_word << 1)) ∈ dm ∧ m (x + (bytes_in_word << 1)) = Word ((31 >< 0) w64) /\
       decode_length c w = 2w /\
       w = make_header c 3w 2)
     else
       (m (x + bytes_in_word) = Word ((63 >< 0) w64)) /\
       decode_length c w = 1w /\
       w = make_header c 3w 1
Proof
  fs[memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
     bc_stack_ref_inv_def,v_inv_def] \\ rw[]
  \\ fs[word_addr_def]
  \\ qexists_tac`ptr` \\ simp[]
  \\ fs[heap_in_memory_store_def]
  \\ imp_res_tac get_real_addr_get_addr
  \\ simp[]
  \\ imp_res_tac heap_lookup_SPLIT
  \\ qspecl_then[`:'a`,`w64`]strip_assume_tac Word64Rep_DataElement
  \\ fs[Word64Rep_def]
  \\ fs[word_heap_APPEND,word_heap_def,word_el_def,UNCURRY,word_list_def]
  \\ SEP_R_TAC \\ simp[]
  \\ ONCE_REWRITE_TAC[CONJ_ASSOC]
  \\ ONCE_REWRITE_TAC[CONJ_ASSOC]
  \\ conj_tac
  >- (
    simp[word_payload_def]
    \\ simp[word_bit_test]
    \\ simp [make_header_def]
    \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [word_index])
  \\ IF_CASES_TAC \\ fs[] \\ rveq
  \\ fs[word_payload_def,word_list_def,LSL_ONE]
  \\ SEP_R_TAC \\ fs[]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
QED

Theorem IMP_memory_rel_Number_num3:
   good_dimindex (:'a) /\ n < 2 ** (dimindex (:'a) - 3) /\
    memory_rel c be ts refs sp st m dm vars ==>
    memory_rel c be ts refs sp st m dm
     ((Number (&n),Word ((n2w n << 2):'a word))::vars)
Proof
  strip_tac \\ mp_tac (IMP_memory_rel_Number |> Q.INST [`i`|->`&n`]) \\ fs []
  \\ fs [Smallnum_def,WORD_MUL_LSL,word_mul_n2w]
  \\ disch_then match_mp_tac
  \\ fs [small_int_def,dimword_def]
  \\ fs [good_dimindex_def] \\ rfs []
QED

Theorem IMP_memory_rel_Number_num:
   good_dimindex (:'a) /\ n < 2 ** (dimindex (:'a) - 4) /\
    memory_rel c be ts refs sp st m dm vars ==>
    memory_rel c be ts refs sp st m dm
     ((Number (&n),Word ((n2w n << 2):'a word))::vars)
Proof
  strip_tac \\ mp_tac (IMP_memory_rel_Number |> Q.INST [`i`|->`&n`]) \\ fs []
  \\ fs [Smallnum_def,WORD_MUL_LSL,word_mul_n2w]
  \\ disch_then match_mp_tac
  \\ fs [small_int_def,dimword_def]
  \\ fs [good_dimindex_def] \\ rfs []
QED

Theorem memory_rel_Number_EQ:
   memory_rel c be ts refs sp st m dm
      ((Number i1,w1)::(Number i2,w2)::vars) /\
    (small_int (:'a) i1 \/ small_int (:'a) i2) /\
    good_dimindex (:'a) ==>
      ?v1 v2. w1 = Word v1 /\ w2 = Word (v2:'a word) /\ (v1 = v2 <=> i1 = i2)
Proof
  Cases_on `small_int (:'a) i1` \\ Cases_on `small_int (:'a) i2` \\ fs []
  THEN1
   (strip_tac
    \\ imp_res_tac memory_rel_Number_IMP
    \\ drule memory_rel_tail \\ strip_tac
    \\ imp_res_tac memory_rel_Number_IMP
    \\ fs [] \\ rpt (qpat_x_assum `!x. _` kall_tac)
    \\ fs [memory_rel_def] \\ rw [] \\ fs [word_ml_inv_def] \\ clean_tac
    \\ drule num_eq_thm \\ rw [])
  \\ strip_tac
  \\ imp_res_tac memory_rel_tl
  \\ imp_res_tac memory_rel_any_Number_IMP
  \\ fs [] \\ rw [] \\ fs [] \\ clean_tac \\ rfs []
  \\ Cases_on `w = w'` \\ fs []
  \\ CCONTR_TAC \\ fs []
QED

Theorem memory_rel_Number_LESS:
   memory_rel c be ts refs sp st m dm
      ((Number i1,w1)::(Number i2,w2)::vars) /\
    small_int (:'a) i1 /\
    small_int (:'a) i2 /\
    good_dimindex (:'a) ==>
      ?v1 v2. w1 = Word v1 /\ w2 = Word v2 /\ (v1 < (v2:'a word) <=> i1 < i2)
Proof
  strip_tac
  \\ imp_res_tac memory_rel_Number_IMP
  \\ drule memory_rel_tail \\ strip_tac
  \\ imp_res_tac memory_rel_Number_IMP
  \\ fs [] \\ fs [memory_rel_def] \\ rw [] \\ fs [num_less_thm]
QED

Theorem memory_rel_Number_LESS_EQ:
   memory_rel c be ts refs sp st m dm
      ((Number i1,w1)::(Number i2,w2)::vars) /\
    small_int (:'a) i1 /\
    small_int (:'a) i2 /\
    good_dimindex (:'a) ==>
      ?v1 v2. w1 = Word v1 /\ w2 = Word v2 /\ (v1 <= (v2:'a word) <=> i1 <= i2)
Proof
  rw [] \\ drule memory_rel_Number_LESS \\ fs [] \\ rw [] \\ fs []
  \\ drule memory_rel_Number_EQ \\ fs [] \\ rw [] \\ fs []
  \\ fs [WORD_LESS_OR_EQ,integerTheory.INT_LE_LT]
QED

Theorem memory_rel_Number_word_msb:
   memory_rel c be ts refs sp st m dm ((Number i1,Word (w:'a word))::vars) /\
    good_dimindex(:'a) /\ small_int (:'a) i1 ==>
    (word_msb w <=> i1 < 0)
Proof
  rw []
  \\ `small_int (:'a) 0` by (EVAL_TAC \\ fs [good_dimindex_def,dimword_def])
  \\ rpt_drule (IMP_memory_rel_Number
       |> REWRITE_RULE [CONJ_ASSOC] |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ fs [EVAL ``Smallnum 0``] \\ strip_tac
  \\ rpt_drule memory_rel_Number_LESS_EQ
  \\ Cases_on `i1` \\ fs [GSYM WORD_NOT_LESS,word_msb_neg]
QED

Triviality memory_rel_RefPtr_EQ_lemma:
  n * 2 ** k < dimword (:'a) /\ m * 2 ** k < dimword (:'a) /\ 0 < k /\
    (n2w n << k || 1w) = (n2w m << k || 1w:'a word) ==> n = m
Proof
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
QED

Theorem memory_rel_RefPtr_EQ:
   memory_rel c be ts refs sp st m dm
      ((RefPtr T i1,w1)::(RefPtr T i2,w2)::vars) /\ good_dimindex (:'a) ==>
      ?v1 v2. w1 = Word v1 /\ w2 = Word (v2:'a word) /\ (v1 = v2 <=> i1 = i2)
Proof
  fs [memory_rel_def] \\ rw [] \\ fs [word_ml_inv_def] \\ clean_tac
  \\ drule ref_eq_thm \\ rw [] \\ clean_tac
  \\ fs [word_addr_def,get_addr_def]
  \\ eq_tac \\ rw [] \\ fs [get_lowerbits_def]
  \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def]
  \\ `bc_ref_inv c i1 refs (f,tf,heap,be) /\
      bc_ref_inv c i2 refs (f,tf,heap,be)` by
   (rpt strip_tac \\ first_x_assum match_mp_tac
    \\ fs [reachable_refs_def]
    \\ metis_tac [get_refs_def,MEM,RTC_CASES1])
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
  \\ imp_res_tac memory_rel_RefPtr_EQ_lemma \\ rfs[]
QED

Theorem memory_rel_RefPtr_EQ_IMP:
  memory_rel c be ts refs sp st m (dm:'a word set)
    ((RefPtr b1 i1, Word w1)::(RefPtr b2 i1, Word w2)::vars) ∧ good_dimindex (:α) ∧
  lookup i1 refs = SOME (ByteArray ys_fl ys) ⇒
  w1 = w2
Proof
  strip_tac
  \\ gvs [memory_rel_def,word_ml_inv_def,abs_ml_inv_def,bc_stack_ref_inv_def]
  \\ gvs [v_inv_def]
QED

Theorem memory_rel_Boolv_T:
   memory_rel c be ts refs sp st m dm vars ∧ good_dimindex (:'a)
   ⇒ memory_rel c be ts refs sp st m dm ((Boolv T,Word (18w:'a word))::vars)
Proof
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ fs [word_ml_inv_def,PULL_EXISTS,EVAL ``Boolv F``,EVAL ``Boolv T``]
  \\ rpt_drule cons_thm_EMPTY \\ disch_then (qspecl_then [`1`] assume_tac)
  \\ rfs [good_dimindex_def,dimword_def]
  \\ rfs [good_dimindex_def,dimword_def]
  \\ asm_exists_tac \\ fs [] \\ fs [word_addr_def,BlockNil_def]
  \\ EVAL_TAC \\ fs [good_dimindex_def,dimword_def]
QED

Theorem memory_rel_Boolv_F:
   memory_rel c be ts refs sp st m dm vars ∧ good_dimindex (:'a)
   ⇒ memory_rel c be ts refs sp st m dm ((Boolv F,Word (2w:'a word))::vars)
Proof
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ fs [word_ml_inv_def,PULL_EXISTS,EVAL ``Boolv F``,EVAL ``Boolv T``]
  \\ rpt_drule cons_thm_EMPTY \\ disch_then (qspecl_then [`0`] assume_tac)
  \\ rfs [good_dimindex_def,dimword_def]
  \\ rfs [good_dimindex_def,dimword_def]
  \\ asm_exists_tac \\ fs [] \\ fs [word_addr_def,BlockNil_def]
  \\ EVAL_TAC \\ fs [good_dimindex_def,dimword_def]
QED

Theorem word_ml_inv_SP_LIMIT:
   word_ml_inv (heap,be,a,sp,sp1,gens) limit ts c refs stack ==> sp <= limit
Proof
  srw_tac[][] \\ Cases_on `sp = 0`
  \\ full_simp_tac(srw_ss())[word_ml_inv_def,abs_ml_inv_def,
        heap_ok_def,unused_space_inv_def]
  \\ imp_res_tac heap_lookup_SPLIT \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[heap_length_APPEND,
        heap_length_def,el_length_def] \\ decide_tac
QED

val lt8 =
  DECIDE ``(n < 8n) = (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/
                       n = 4 \/ n = 5 \/ n = 6 \/ n = 7)``

Triviality Smallnum_test:
  ((Smallnum i && -1w ≪ (dimindex (:'a) − 2)) = 0w:'a word) /\
    good_dimindex (:'a) /\ small_int (:'a) i ==>
    ~(i < 0) /\ i < 2 ** (dimindex (:'a) - 4)
Proof
  Tactical.REVERSE (Cases_on `i`)
  \\ srw_tac [wordsLib.WORD_MUL_LSL_ss]
      [Smallnum_def, small_int_def, good_dimindex_def,
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
QED

val small_int_w2i_i2w = prove(
  ``small_int (:α) i /\ good_dimindex (:'a) ==>
    w2i ((i2w (4 * i)):'a word) = 4 * i``,
  strip_tac \\ match_mp_tac integer_wordTheory.w2i_i2w
  \\ fs [small_int_def,dimword_def,good_dimindex_def,
         INT_MIN_def,INT_MAX_def] \\ rfs [] \\ fs []
  \\ intLib.COOPER_TAC);

Theorem memory_rel_Add:
   memory_rel c be ts refs sp st m dm
      ((Number i,Word wi)::(Number j,Word wj)::vars) /\
    ~word_bit 0 wi /\ ~word_bit 0 wj /\
    good_dimindex (:'a) /\ (w2i (wi + wj) = w2i wi + w2i wj) ==>
    memory_rel c be ts refs sp st m dm
      ((Number (i + j),Word (wi + wj:'a word))::vars)
Proof
  strip_tac
  \\ rpt_drule memory_rel_any_Number_IMP \\ fs [word_bit_def] \\ strip_tac
  \\ drule memory_rel_tail \\ strip_tac
  \\ rpt_drule memory_rel_any_Number_IMP \\ fs [word_bit_def] \\ strip_tac
  \\ imp_res_tac memory_rel_Number_IMP \\ fs [] \\ rveq
  \\ fs [Smallnum_i2w,integer_wordTheory.word_i2w_add]
  \\ fs [GSYM integerTheory.INT_LDISTRIB,GSYM Smallnum_i2w]
  \\ match_mp_tac IMP_memory_rel_Number
  \\ drule memory_rel_tail \\ strip_tac \\ fs []
  \\ fs [Smallnum_i2w,integerTheory.INT_LDISTRIB]
  \\ qpat_x_assum `good_dimindex (:α)` assume_tac
  \\ fs [small_int_w2i_i2w]
  \\ imp_res_tac w2i_i2w_IMP
  \\ fs [small_int_def,dimword_def,good_dimindex_def,
         INT_MIN_def,INT_MAX_def] \\ rfs []
  \\ intLib.COOPER_TAC
QED

Theorem memory_rel_Sub:
   memory_rel c be ts refs sp st m dm
      ((Number i,Word wi)::(Number j,Word wj)::vars) /\
    ~word_bit 0 wi /\ ~word_bit 0 wj /\
    good_dimindex (:'a) /\ (w2i (wi - wj) = w2i wi - w2i wj) ==>
    memory_rel c be ts refs sp st m dm
      ((Number (i - j),Word (wi - wj:'a word))::vars)
Proof
  strip_tac
  \\ rpt_drule memory_rel_any_Number_IMP \\ fs [word_bit_def] \\ strip_tac
  \\ drule memory_rel_tail \\ strip_tac
  \\ rpt_drule memory_rel_any_Number_IMP \\ fs [word_bit_def] \\ strip_tac
  \\ imp_res_tac memory_rel_Number_IMP \\ fs [] \\ rveq
  \\ fs [Smallnum_i2w,word_i2w_sub |> SIMP_RULE (srw_ss())[]]
  \\ fs [GSYM integerTheory.INT_SUB_LDISTRIB,GSYM Smallnum_i2w]
  \\ match_mp_tac IMP_memory_rel_Number
  \\ drule memory_rel_tail \\ strip_tac \\ fs []
  \\ fs [Smallnum_i2w,integerTheory.INT_SUB_LDISTRIB]
  \\ qpat_x_assum `good_dimindex (:α)` assume_tac
  \\ fs [small_int_w2i_i2w]
  \\ imp_res_tac w2i_i2w_IMP
  \\ fs [small_int_def,dimword_def,good_dimindex_def,
         INT_MIN_def,INT_MAX_def] \\ rfs []
  \\ intLib.COOPER_TAC
QED

Triviality exists_num:
  ~(i < 0i) <=> ?n. i = &n
Proof
  Cases_on `i` \\ fs []
QED

Theorem small_int_w2n[simp]:
   good_dimindex (:'a) ==> small_int (:'a) (& (w2n (w:word8)))
Proof
  rw [good_dimindex_def,small_int_def] \\ fs [dimword_def]
  \\ assume_tac (w2n_lt |> INST_TYPE [``:'a``|->``:8``])
  \\ fs [dimword_def] \\ pop_assum (assume_tac o SPEC_ALL) \\ fs []
QED

Theorem memory_rel_And:
   memory_rel c be ts refs sp st m dm
      ((Number (&(w2n (i:word8))),Word wi)::(Number (&(w2n j)),Word wj)::vars) /\
    good_dimindex (:'a) ==>
    memory_rel c be ts refs sp st m dm
      ((Number (&w2n(i && j)),Word (wi && wj:'a word))::vars)
Proof
  rw [] \\ imp_res_tac memory_rel_Number_IMP \\ fs []
  \\ rfs [small_int_w2n]
  \\ fs [WORD_LEFT_AND_OVER_OR]
  \\ drule memory_rel_tail \\ strip_tac
  \\ imp_res_tac memory_rel_Number_IMP \\ fs []
  \\ rpt var_eq_tac \\ fs [word_or_eq_0]
  \\ `(Smallnum (&w2n i) && Smallnum (&w2n j)) = (Smallnum (&(w2n (i && j)))):'a word` by
   (fs [Smallnum_def]
    \\ fs[GSYM word_mul_n2w]
    \\ `4w = n2w (2 ** 2)` by simp[]
    \\ pop_assum SUBST_ALL_TAC
    \\ simp[GSYM WORD_MUL_LSL]
    \\ fs[GSYM w2w_def]
    \\ fs[GSYM WORD_w2w_OVER_BITWISE])
  \\ fs [] \\ match_mp_tac IMP_memory_rel_Number
  \\ imp_res_tac memory_rel_tail \\ fs []
  \\ fs [small_int_def]
  \\ fs[dimword_def]
  \\ Q.ISPEC_THEN`i && j`strip_assume_tac w2n_lt
  \\ fs[good_dimindex_def]
QED

Theorem memory_rel_Or:
   memory_rel c be ts refs sp st m dm
      ((Number (&(w2n (i:word8))),Word wi)::(Number (&(w2n j)),Word wj)::vars) /\
    good_dimindex (:'a) ==>
    memory_rel c be ts refs sp st m dm
      ((Number (&w2n(i || j)),Word (wi || wj:'a word))::vars)
Proof
  rw [] \\ imp_res_tac memory_rel_Number_IMP \\ fs []
  \\ fs [WORD_LEFT_AND_OVER_OR]
  \\ drule memory_rel_tail \\ strip_tac
  \\ imp_res_tac memory_rel_Number_IMP \\ fs []
  \\ rpt var_eq_tac \\ fs [word_or_eq_0]
  \\ `(Smallnum (&w2n i) || Smallnum (&w2n j)) = (Smallnum (&(w2n (i || j)))):'a word` by
   (fs [Smallnum_def]
    \\ fs[GSYM word_mul_n2w]
    \\ `4w = n2w (2 ** 2)` by simp[]
    \\ pop_assum SUBST_ALL_TAC
    \\ simp[GSYM WORD_MUL_LSL]
    \\ fs[GSYM w2w_def]
    \\ fs[GSYM WORD_w2w_OVER_BITWISE])
  \\ fs [] \\ match_mp_tac IMP_memory_rel_Number
  \\ imp_res_tac memory_rel_tail \\ fs []
  \\ fs [small_int_def]
  \\ fs[dimword_def]
  \\ Q.ISPEC_THEN`i || j`strip_assume_tac w2n_lt
  \\ fs[good_dimindex_def]
QED

Theorem memory_rel_Xor:
   memory_rel c be ts refs sp st m dm
      ((Number (&(w2n (i:word8))),Word wi)::(Number (&(w2n j)),Word wj)::vars) /\
    good_dimindex (:'a) ==>
    memory_rel c be ts refs sp st m dm
      ((Number (&w2n(word_xor i j)),Word (word_xor wi wj:'a word))::vars)
Proof
  rw [] \\ imp_res_tac memory_rel_Number_IMP \\ fs []
  \\ fs [WORD_LEFT_AND_OVER_OR]
  \\ drule memory_rel_tail \\ strip_tac
  \\ imp_res_tac memory_rel_Number_IMP \\ fs []
  \\ rpt var_eq_tac \\ fs [word_or_eq_0]
  \\ `(Smallnum (&w2n i) ⊕ Smallnum (&w2n j)) = (Smallnum (&(w2n (i ⊕ j)))):'a word` by
   (fs [Smallnum_def]
    \\ fs[GSYM word_mul_n2w]
    \\ `4w = n2w (2 ** 2)` by simp[]
    \\ pop_assum SUBST_ALL_TAC
    \\ simp[GSYM WORD_MUL_LSL]
    \\ fs[GSYM w2w_def]
    \\ fs[GSYM WORD_w2w_OVER_BITWISE])
  \\ fs [] \\ match_mp_tac IMP_memory_rel_Number
  \\ imp_res_tac memory_rel_tail \\ fs []
  \\ fs [small_int_def]
  \\ fs[dimword_def]
  \\ Q.ISPEC_THEN`i ⊕ j`strip_assume_tac w2n_lt
  \\ fs[good_dimindex_def]
QED

Theorem memory_rel_Number_IMP_Word:
   memory_rel c be ts refs sp st m dm ((Number i,v)::vars) ==> ?w. v = Word w
Proof
  fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
      bc_stack_ref_inv_def,v_inv_def] \\ rw [] \\ fs [word_addr_def]
QED

Theorem memory_rel_Number_IMP_Word_2:
   memory_rel c be ts refs sp st m dm ((Number i,v)::(Number j,w)::vars) ==>
    ?w1 w2. v = Word w1 /\ w = Word w2
Proof
  fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
      bc_stack_ref_inv_def,v_inv_def] \\ rw [] \\ fs [word_addr_def]
QED

Theorem memory_rel_zero_space:
   memory_rel c be ts refs sp st m dm vars ==>
    memory_rel c be ts refs 0 st m dm vars
Proof
  fs [memory_rel_def,heap_in_memory_store_def]
  \\ rw [] \\ fs [] \\ rpt (asm_exists_tac \\ fs []) \\ metis_tac []
QED

Theorem memory_rel_less_space:
   memory_rel c be ts refs sp st m dm vars ∧ sp' ≤ sp ⇒
   memory_rel c be ts refs sp' st m dm vars
Proof
  rw[memory_rel_def] \\ asm_exists_tac \\ simp[]
QED

Theorem all_ones_bit:
  i < dimindex (:'a) ==>
  ((all_ones e b :'a word) ' i <=> b <= i /\ i < e)
Proof
  strip_tac
  \\ imp_res_tac wordsTheory.word_0
  \\ asm_simp_tac std_ss [all_ones_def]
  \\ IF_CASES_TAC THEN1 fs []
  \\ asm_simp_tac std_ss [word_slice_def,fcpTheory.FCP_BETA,word_1comp_def]
  \\ fs []
QED

Theorem maxout_bits_bit:
  (maxout_bits n l b:'a word) ' i /\ i < dimindex (:'a) ==>
  b <= i /\ i < b + l
Proof
  rw [maxout_bits_def,word_lsl_def]
  \\ fs [fcpTheory.FCP_BETA,n2w_def,all_ones_bit]
  \\ fs [LESS_EQ_EXISTS] \\ rveq \\ fs []
  \\ CCONTR_TAC \\ fs [NOT_LESS]
  \\ `n < 2 ** l` by fs []
  \\ qsuff_tac `n < 2 ** p`
  THEN1 (strip_tac \\ drule bitTheory.NOT_BIT_GT_TWOEXP \\ simp [])
  \\ match_mp_tac LESS_LESS_EQ_TRANS \\ asm_exists_tac \\ simp []
QED

Theorem maxout_bits_IMP:
   i < dimindex (:'a) /\ (maxout_bits tag k n:'a word) ' i ==> i < n + k
Proof
  rw [] \\ imp_res_tac maxout_bits_bit \\ fs []
QED

Theorem make_cons_ptr_thm:
   make_cons_ptr conf (f:'a word) tag len =
     Word ((f << (shift_length conf − shift (:'a)) || 1w ||
            ptr_bits conf tag len))
Proof
  fs [make_cons_ptr_def]
  \\ sg `get_lowerbits conf (Word (ptr_bits conf tag len)) =
      (ptr_bits conf tag len || 1w)` \\ fs []
  \\ fs [get_lowerbits_def]
  \\ fs [fcpTheory.CART_EQ,fcpTheory.FCP_BETA,word_bits_def,word_or_def]
  \\ rw [] \\ fs [] \\ eq_tac \\ fs [] \\ rw [] \\ fs []
  \\ disj1_tac \\ rfs [ptr_bits_def,word_or_def,fcpTheory.FCP_BETA]
  \\ imp_res_tac maxout_bits_IMP \\ fs [small_shift_length_def]
QED

val Num_ABS_lemmas = prove(
  ``Num (ABS (& n)) = n /\ Num (ABS (- & n)) = n``,
  intLib.COOPER_TAC);

Definition word_cmp_res_def:
  word_cmp_res i (j:int) =
    if i = j then 1w else if i < j then 0w else 2w
End

Definition word_cmp_loop_def:
  word_cmp_loop (l:'a word) (a1:'a word) a2 dm (m:'a word -> 'a word_loc) =
    if l = 0w then SOME 1w else
      if a1 IN dm /\ a2 IN dm then
        case (m a1, m a2) of
        | (Word w1,Word w2) =>
            if w1 = w2 then
              word_cmp_loop (l-1w) (a1 - bytes_in_word)
                (a2 - bytes_in_word) dm m
            else if w1 <+ w2 then SOME 0w else SOME (2w:'a word)
        | _ => NONE
      else NONE
End

val word_cmp_loop_ind =  theorem"word_cmp_loop_ind";

val word_cmp_loop_thm = prove(
  ``!xs1 (xs2:'a word list) f1 f2 (a1:'a word) a2.
      LENGTH xs1 = LENGTH xs2 /\ LENGTH xs1 < dimword (:'a) /\
      (word_list (a1 + bytes_in_word) (MAP Word xs1) * f1) (fun2set (m,dm)) /\
      (word_list (a2 + bytes_in_word) (MAP Word xs2) * f2) (fun2set (m,dm)) ==>
      word_cmp_loop (n2w (LENGTH xs1))
        (a1 + bytes_in_word * n2w (LENGTH xs1))
        (a2 + bytes_in_word * n2w (LENGTH xs1)) dm m =
        SOME (case mw_cmp xs1 xs2 of
              | NONE => 1w
              | SOME T => 0w
              | SOME F => 2w)``,
  ho_match_mp_tac mw_cmp_ind \\ rw []
  \\ `xs1 = [] ∨ ∃y1 ys1. xs1 = SNOC y1 ys1` by metis_tac [SNOC_CASES]
  \\ `xs2 = [] ∨ ∃y2 ys2. xs2 = SNOC y2 ys2` by metis_tac [SNOC_CASES]
  \\ simp [Once mw_cmp_def] \\ fs []
  \\ once_rewrite_tac [word_cmp_loop_def]
  \\ full_simp_tac std_ss [GSYM SNOC_APPEND,FRONT_SNOC] \\ fs []
  \\ fs [ADD1] \\ rfs []
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [SNOC_APPEND,word_list_APPEND,word_list_def,SEP_CLAUSES]
  \\ SEP_R_TAC \\ rfs [] \\ SEP_R_TAC \\ fs []
  \\ IF_CASES_TAC \\ fs [] \\ rw []
  \\ first_x_assum match_mp_tac
  \\ metis_tac [STAR_ASSOC]);

Theorem memory_rel_Number_cmp:
   memory_rel c be ts refs sp st m dm ((Number i1,v1)::(Number i2,v2)::vars) /\
   good_dimindex (:'a) ==>
   ?w1 w2.
     v1 = Word w1 /\ v2 = Word (w2:'a word) /\
     if ~word_bit 0 w1 /\ ~word_bit 0 w2 then
       (i1 < i2 <=> w1 < w2) /\ (i1 = i2 <=> w1 = w2)
     else if ~word_bit 0 w1 /\ word_bit 0 w2 then
       i1 <> i2 /\
       ?a x2. get_real_addr c st w2 = SOME a /\
              m a = Word x2 /\ a IN dm /\
              word_cmp_res i1 i2 = if (x2 && 16w) = 0w then 0w else 2w:'a word
     else if word_bit 0 w1 /\ word_bit 0 w2 then
       ?a1 x1 a2 x2.
         get_real_addr c st w1 = SOME a1 /\ m a1 = Word x1 /\ a1 IN dm /\
         get_real_addr c st w2 = SOME a2 /\ m a2 = Word x2 /\ a2 IN dm /\
         if x1 = x2 then
           let (a1,a2) = if (x1 && 16w) = 0w then (a1,a2) else (a2,a1) in
             word_cmp_loop (decode_length c x1)
               (a1 + bytes_in_word * (decode_length c x1))
               (a2 + bytes_in_word * (decode_length c x2))
                 dm m = SOME (word_cmp_res i1 i2)
         else
           word_cmp_res i1 i2 =
           (if (x1 && 16w) = 0w (* 0 <= i1 *) then
              if (x2 && 16w) = 0w (* 0 <= i2 *) then
                if decode_length c x1 <+ decode_length c x2 then 0w else 2w:'a word
              else
                2w
            else
              if (x2 && 16w) = 0w (* 0 <= i2 *) then
                0w
              else
                if decode_length c x1 <+ decode_length c x2 then 2w else 0w)
     else T
Proof
  strip_tac
  \\ drule memory_rel_Number_IMP_Word_2 \\ strip_tac \\ rveq
  \\ qexists_tac `w1` \\ qexists_tac `w2` \\ rewrite_tac []
  \\ IF_CASES_TAC THEN1
   (`small_int (:α) i1 /\ small_int (:α) i2` by
      (drule (memory_rel_any_Number_IMP |> ONCE_REWRITE_RULE [CONJ_COMM])
       \\ fs [word_bit_def]
       \\ imp_res_tac memory_rel_tail
       \\ drule (memory_rel_any_Number_IMP |> ONCE_REWRITE_RULE [CONJ_COMM])
       \\ fs [word_bit_def] \\ NO_TAC)
    \\ rpt_drule memory_rel_Number_EQ \\ fs []
    \\ rpt_drule memory_rel_Number_LESS \\ fs [])
  \\ IF_CASES_TAC THEN1
   (fs [] \\ clean_tac
    \\ `small_int (:'a) i1 /\ ~small_int (:'a) i2` by
      (drule (memory_rel_any_Number_IMP |> ONCE_REWRITE_RULE [CONJ_COMM])
       \\ fs [word_bit_def]
       \\ imp_res_tac memory_rel_tail
       \\ drule (memory_rel_any_Number_IMP |> ONCE_REWRITE_RULE [CONJ_COMM])
       \\ fs [word_bit_def] \\ NO_TAC)
    \\ conj_tac THEN1 (CCONTR_TAC \\ fs [])
    \\ imp_res_tac memory_rel_tail
    \\ drule memory_rel_Number_bignum_IMP_ALT \\ fs []
    \\ strip_tac \\ fs []
    \\ fs [small_int_def,word_cmp_res_def] \\ rw []
    \\ rfs [good_dimindex_def,dimword_def]
    \\ intLib.COOPER_TAC)
  \\ reverse (IF_CASES_TAC) THEN1 fs []
  \\ fs [] \\ clean_tac
  \\ `~small_int (:'a) i1 /\ ~small_int (:'a) i2` by
    (drule (memory_rel_any_Number_IMP |> ONCE_REWRITE_RULE [CONJ_COMM])
     \\ fs [word_bit_def]
     \\ imp_res_tac memory_rel_tail
     \\ drule (memory_rel_any_Number_IMP |> ONCE_REWRITE_RULE [CONJ_COMM])
     \\ fs [word_bit_def] \\ NO_TAC)
  \\ drule memory_rel_bignum_cmp \\ fs [] \\ strip_tac
  \\ drule memory_rel_Number_bignum_IMP_ALT \\ fs [] \\ strip_tac \\ fs []
  \\ imp_res_tac memory_rel_tail
  \\ drule memory_rel_Number_bignum_IMP_ALT \\ fs [] \\ strip_tac \\ fs []
  \\ IF_CASES_TAC THEN1
   (fs [] \\ rfs []
    \\ rpt_drule word_cmp_loop_thm \\ fs []
    \\ disch_then drule
    \\ disch_then drule
    \\ fs [mw_cmp_thm,mw2n_n2mw]
    \\ qpat_assum `LENGTH _ = _` (assume_tac o GSYM)
    \\ rpt_drule word_cmp_loop_thm \\ fs []
    \\ fs [mw_cmp_thm,mw2n_n2mw] \\ rpt strip_tac
    \\ IF_CASES_TAC \\ fs []
    \\ fs [word_cmp_res_def]
    \\ Cases_on `i1` \\ Cases_on `i2` \\ fs [Num_ABS_lemmas] \\ rw [])
  \\ fs [WORD_LO]
  \\ rveq \\ rfs [] \\ fs []
  \\ Cases_on `i1` \\ Cases_on `i2` \\ fs []
  \\ fs [word_cmp_res_def]
  \\ fs [EVAL ``n2mw 0``,Num_ABS_lemmas]
  \\ Cases_on `n = n'` \\ fs []
  \\ Cases_on `n <= n'` \\ Cases_on `n' <= n`
  \\ imp_res_tac LENGTH_n2mw_LESS_LENGTH_n2mw \\ fs []
  \\ full_simp_tac (std_ss++ARITH_ss) [GSYM LENGTH_NIL]
QED

Theorem word_cmp_loop_refl = Q.prove(
  `∀l a b dm m x. a = b ∧ word_cmp_loop l a a dm m = SOME x ⇒ x = 1w`,
  recInduct word_cmp_loop_ind
  \\ rpt strip_tac \\ rveq
  \\ pop_assum mp_tac
  \\ once_rewrite_tac[word_cmp_loop_def]
  \\ IF_CASES_TAC \\ simp_tac(srw_ss())[]
  \\ every_case_tac \\ strip_tac
  \\ first_x_assum(match_mp_tac o MP_CANON)
  \\ simp[])
  |> SIMP_RULE(srw_ss())[]

val good_dimindex_def = good_dimindex_def;

Definition v_same_type_def:
  (v_same_type (Number _) (Number _) = T) ∧
  (v_same_type (Word64 _) (Word64 _) = T) ∧
  (v_same_type (Block _ t1 l1) (Block _ t2 l2) = (t1 = t2 ∧ LENGTH l1 = LENGTH l2 ⇒ LIST_REL v_same_type l1 l2)) ∧
  (v_same_type (CodePtr _) (CodePtr _) = T) ∧
  (v_same_type (RefPtr _ _) (RefPtr _ _) = T) ∧
  (v_same_type _ _ = F)
Termination
  wf_rel_tac`measure (v_size o FST)`
 \\ Induct_on`l1` \\ ntac 2 (rw[v_size_def])
 \\ Cases_on`l2` \\ fs[] \\ rw[]
 \\ res_tac \\ fs[] \\ rfs[]
 \\ first_x_assum(qspecl_then[`0`,`t1`]mp_tac) \\ rw[]
End
val _ = export_rewrites["v_same_type_def"];

val v_ind =
  TypeBase.induction_of``:v``
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE(srw_ss())[]
  |> UNDISCH_ALL |> CONJUNCT1
  |> DISCH_ALL

Theorem memory_rel_Block_MEM:
   memory_rel c be ts refs sp st m dm ((Block ts' n ls,(v:'a word_loc))::vars) ∧
   i < LENGTH ls ∧
   good_dimindex (:'a)
   ⇒
   ∃w a y.
   get_real_offset (Smallnum (&i)) = SOME y ∧
   v = Word w ∧ get_real_addr c st w = SOME a ∧ (a + y) IN dm /\
   memory_rel c be ts refs sp st m dm ((EL i ls,m (a + y))::(Block ts' n ls,v)::vars)
Proof
  rw[]
  \\ rpt_drule memory_rel_Block_IMP
  \\ rw[]
  \\ Cases_on`ls=[]`\\fs[]
  \\ `small_int (:'a) (& i)`
    by ( rfs[good_dimindex_def] \\ rfs[small_int_def,dimword_def] )
  \\ rpt_drule IMP_memory_rel_Number
  \\ strip_tac
  \\ drule memory_rel_swap
  \\ strip_tac
  \\ rpt_drule memory_rel_El \\ rw[]
  \\ asm_exists_tac \\ rw[]
  \\ pop_assum mp_tac
  \\ match_mp_tac memory_rel_rearrange
  \\ rw[] \\ rw[]
QED

Theorem Smallnum_0:
   ¬(Smallnum i:'a word) ' 0
Proof
  `0 < dimindex(:'a)` by simp[]
  \\ strip_tac
  \\ imp_res_tac word_bit_thm
  \\ fs[word_bit_test,Smallnum_bits]
QED

Theorem Smallnum_1:
   good_dimindex(:'a) ==> ¬(Smallnum i:'a word) ' 1
Proof
  strip_tac
  \\ `1 < dimindex(:'a)` by fs[good_dimindex_def]
  \\ strip_tac
  \\ imp_res_tac word_bit_thm
  \\ fs[word_bit_test,Smallnum_bits]
QED

Theorem memory_rel_pointer_eq_size:
   ∀v1 v2 w.
   good_dimindex (:'a) ∧
   memory_rel c be ts refs sp st m dm ((v1,(w:'a word_loc))::(v2,w)::vars) ==>
     vb_size v1 = vb_size v2
Proof
  ho_match_mp_tac v_ind \\ rw[] \\ Cases_on`v2` \\ fs[vb_size_def]
  \\ qhdtm_x_assum`memory_rel`mp_tac
  \\ qid_spec_tac`n` \\ qid_spec_tac`n0` \\ qid_spec_tac`n'`
  THEN_LT USE_SG_THEN (fn th => metis_tac[memory_rel_swap,th]) 1 3
  THEN_LT USE_SG_THEN (fn th => metis_tac[memory_rel_swap,th]) 2 3
  THEN_LT USE_SG_THEN (fn th => metis_tac[memory_rel_swap,th]) 6 4
  THEN_LT USE_SG_THEN (fn th => metis_tac[memory_rel_swap,th]) 6 4
  \\ rw[]
  >- (
    Cases_on`small_int (:'a) i`
    >- (
      rpt_drule memory_rel_Number_IMP
      \\ rpt_drule memory_rel_tail \\ strip_tac
      \\ rpt_drule memory_rel_Block_IMP \\ strip_tac
      \\ strip_tac \\ rveq \\ fs[] \\ rveq
      \\ fs[Smallnum_0]
      \\ `Smallnum i ' 1`
      by (
        `1 < dimindex (:'a)` by fs[good_dimindex_def]
        \\ simp[Once WORD_ADD_BIT]
        \\ simp[word_index,word_mul_n2w]
        \\ `¬BIT 1 (n * 2 ** 4)`
        by ( match_mp_tac bitTheory.BIT_SHIFT_THM3 \\ simp[] )
        \\ fs[]
        \\ simp[word_bits_n2w,word_index]
        \\ match_mp_tac bitTheory.BIT_OF_BITS_THM2
        \\ simp[] )
      \\ rfs[Smallnum_1] )
    \\ rpt_drule memory_rel_Number_bignum_IMP
    \\ rpt_drule memory_rel_tail \\ strip_tac
    \\ rpt_drule memory_rel_Block_IMP \\ strip_tac
    \\ strip_tac \\ rveq \\ fs[] \\ rveq \\ fs[]
    \\ qmatch_assum_rename_tac`(1w && w1) <> 0w`
    \\ `word_bit 0 w1` by simp[word_bit_test]
    \\ pop_assum mp_tac \\ rw[word_bit_thm] \\ fs[]
    \\ rfs[word_bit_test] )
  >- (
    rpt_drule memory_rel_Word64_IMP
    \\ rpt_drule memory_rel_tail \\ strip_tac
    \\ rpt_drule memory_rel_Block_IMP \\ strip_tac
    \\ strip_tac
    \\ rveq \\ fs[] \\ rveq \\ fs[] \\ rveq \\ fs[]
    \\ fs[get_addr_0] )
  >- (
    rpt_drule memory_rel_Block_IMP \\ strip_tac
    \\ imp_res_tac memory_rel_tail
    \\ rpt_drule memory_rel_Block_IMP \\ strip_tac
    \\ clean_tac
    \\ qmatch_asmsub_rename_tac`Word w`
    \\ reverse(Cases_on`w ' 0` \\ fs[])
    >- (
      fs[word_mul_n2w]
      \\ fs[X_LT_DIV] \\ rfs[] \\ fs[])
    \\ fs[] \\ rveq \\ fs[] \\ rveq \\ fs[]
    \\ imp_res_tac encode_header_tag_mask \\ fs[]
    \\ fs[encode_header_def]
    \\ fs[X_LT_DIV,LEFT_ADD_DISTRIB] \\ rfs[] \\ rveq
    \\ `LENGTH l < dimword(:'a) ∧ LENGTH l' < dimword(:'a)`
    by (
      metis_tac[dimword_def,bitTheory.EXP_SUB_LESS_EQ,LESS_LESS_EQ_TRANS] )
    \\ fs[]
    \\ AP_TERM_TAC
    \\ simp[LIST_EQ_REWRITE,EL_MAP]
    \\ fs[] \\ qx_gen_tac`i` \\ strip_tac
    \\ clean_tac
    \\ qhdtm_x_assum`memory_rel`kall_tac
    \\ rpt_drule memory_rel_Block_MEM \\ rw[]
    \\ qmatch_assum_abbrev_tac`memory_rel _ _ _ _ _ _ _ _ (e1::b1::b2::vars)`
    \\ `memory_rel c be ts refs sp st m dm (b2::e1::vars)`
    by (
      qhdtm_x_assum`memory_rel`mp_tac
      \\ match_mp_tac memory_rel_rearrange
      \\ rw[] \\ rw[] )
    \\ unabbrev_all_tac
    \\ `i < LENGTH l'` by simp[]
    \\ rpt_drule memory_rel_Block_MEM \\ strip_tac
    \\ rpt_drule memory_rel_swap \\ strip_tac
    \\ rpt_drule memory_rel_tail \\ strip_tac
    \\ fs[EVERY_MEM,MEM_EL,PULL_EXISTS,LIST_REL_EL_EQN]
    \\ first_x_assum(match_mp_tac o MP_CANON) \\ simp[]
    \\ rpt_drule memory_rel_swap \\ strip_tac
    \\ asm_exists_tac \\ rw[] )
  >- (
    fs[memory_rel_def,word_ml_inv_def,abs_ml_inv_def,bc_stack_ref_inv_def]
    \\ fs[v_inv_def] \\ rveq
    \\ fs[word_addr_def]
    \\ every_case_tac \\ fs[] \\ rveq \\ fs[word_addr_def])
  >- (
    rpt_drule memory_rel_RefPtr_IMP
    \\ rpt_drule memory_rel_tail \\ strip_tac
    \\ rpt_drule memory_rel_Block_IMP \\ strip_tac
    \\ strip_tac
    \\ fs[] \\ rveq \\ fs[] \\ rfs [] )
QED

val do_eq_list_F_IMP_MEM = prove(
  ``!l l'.
      do_eq_list refs l l' = Eq_val F /\ LENGTH l' = LENGTH l ==>
      ?i. i < LENGTH l /\ do_eq refs (EL i l) (EL i l') = Eq_val F``,
  Induct \\ Cases_on `l'` \\ fs [] \\ rpt strip_tac
  \\ every_case_tac \\ fs [] \\ res_tac
  THEN1 (qexists_tac `SUC i` \\ fs [])
  \\ qexists_tac `0` \\ fs []);

val memory_rel_rotate3 = prove(
  ``memory_rel c be ts refs sp st m dm (x1::x2::x3::vars) ==>
    memory_rel c be ts refs sp st m dm (x3::x1::x2::vars)``,
  match_mp_tac memory_rel_rearrange
  \\ fs [] \\ rw [] \\ fs []);

Theorem memory_rel_pointer_eq = Q.prove(`
  ∀v1 v2 w b.
   good_dimindex (:'a) ∧
   do_eq refs v1 v2 = Eq_val b /\
   memory_rel c be ts refs sp st m dm ((v1,(w:'a word_loc))::(v2,w)::vars) ==> b`,
  ho_match_mp_tac v_ind \\ rw[] \\ Cases_on`v2` \\ fs[] \\ rveq
  \\ TRY (
    gvs [CaseEq"bool"]
    \\ rpt_drule memory_rel_RefPtr_EQ \\ strip_tac \\ fs []
    \\ every_case_tac \\ fs[] \\ rfs[] \\ NO_TAC)
  >- (
    rpt_drule memory_rel_Number_cmp \\ rw[]
    \\ fs[WORD_LESS_REFL]
    \\ pop_assum mp_tac \\ rw[]
    \\ fs[] \\ rveq \\ fs[] \\ rveq \\ fs[]
    \\ drule word_cmp_loop_refl
    \\ simp[word_cmp_res_def] \\ rw[]
    \\ fs[good_dimindex_def,dimword_def])
  >- (
    rpt_drule memory_rel_Word64_IMP
    \\ rpt_drule memory_rel_tail \\ rw[]
    \\ rpt_drule memory_rel_Word64_IMP \\ rw[]
    \\ fs[] \\ rveq \\ fs[] \\ rveq \\ fs[]
    \\ pop_assum mp_tac \\ rw[] \\ fs[]
    \\ rfs[good_dimindex_def]
    \\ fs[fcpTheory.CART_EQ,word_extract_def,word_bits_def,fcpTheory.FCP_BETA]
    \\ rfs[] \\ rw[] \\
    TRY (
      rpt(first_x_assum(qspec_then`i`mp_tac))
      \\ simp[fcpTheory.FCP_BETA,w2w] \\ NO_TAC)
    \\ Cases_on`i < 32` \\ fs[]
    >- (
      rpt(first_x_assum(qspec_then`i`mp_tac))
      \\ simp[fcpTheory.FCP_BETA,w2w] \\ NO_TAC)
    \\ pop_assum mp_tac \\ rw[NOT_LESS,LESS_EQ_EXISTS]
    \\ rpt(first_x_assum(qspec_then`p`mp_tac))
    \\ simp[fcpTheory.FCP_BETA,w2w])
  >- (
    Cases_on `b` \\ fs []
    \\ Cases_on `isClos n l` \\ fs []
    THEN1 (every_case_tac \\ fs [])
    \\ Cases_on `isClos n' l'` \\ fs []
    \\ `n = n' ∧ LENGTH l' = LENGTH l` by
     (rpt_drule memory_rel_Block_IMP \\ strip_tac
      \\ imp_res_tac memory_rel_swap
      \\ rpt_drule memory_rel_Block_IMP \\ strip_tac
      \\ clean_tac
      \\ Cases_on `l = []` \\ Cases_on `l' = []` \\ fs []
      THEN1
       (fs [good_dimindex_def] \\ rfs [dimword_def,word_add_n2w,word_mul_n2w]
        \\ sg `(16 * n') < dimword (:'a) /\ (16 * n) < dimword (:'a)`
        \\ fs [dimword_def,word_add_n2w,word_mul_n2w])
      THEN1 (rveq \\ fs [])
      \\ ntac 3 (fs [] \\ rveq)
      \\ `c.len_size + 2 < dimindex (:α)` by
            fs [memory_rel_def,heap_in_memory_store_def]
      \\ drule (GEN_ALL encode_header_EQ)
      \\ qpat_x_assum `encode_header c (4 * n) (LENGTH l) = SOME x` assume_tac
      \\ disch_then drule \\ fs [])
    \\ fs [] \\ rveq
    \\ rpt_drule do_eq_list_F_IMP_MEM
    \\ CCONTR_TAC \\ fs []
    \\ imp_res_tac EVERY_EL
    \\ qpat_x_assum `EVERY _ _` kall_tac
    \\ pop_assum mp_tac
    \\ fs [] \\ asm_exists_tac \\ fs []
    \\ rpt_drule memory_rel_Block_IMP \\ strip_tac
    \\ imp_res_tac memory_rel_swap
    \\ rpt_drule memory_rel_Block_IMP \\ strip_tac
    \\ clean_tac
    \\ Cases_on `l = []` \\ fs []
    \\ Cases_on `l' = []` \\ fs []
    \\ rpt_drule memory_rel_Block_MEM
    \\ disch_then (qspec_then `i` mp_tac)
    \\ fs [] \\ strip_tac
    \\ drule memory_rel_rotate3
    \\ strip_tac
    \\ rpt_drule memory_rel_Block_MEM
    \\ strip_tac \\ qexists_tac `m (a + y)`
    \\ pop_assum mp_tac
    \\ match_mp_tac memory_rel_rearrange
    \\ fs [] \\ rw [] \\ fs []))
  |> REWRITE_RULE [CONJ_ASSOC] |> ONCE_REWRITE_RULE [CONJ_COMM];

Theorem v1_size_map:
   ∀ls. v1_size ls = SUM (MAP v_size ls) + LENGTH ls
Proof
  Induct \\ rw[v_size_def]
QED

Definition v_depth_def:
  (v_depth (Block _ _ ls) = (if NULL ls then 0 else 1) + list_max (MAP v_depth ls)) ∧
  (v_depth _ = 0n)
Termination
  WF_REL_TAC`measure v_size` \\
 ntac 2 gen_tac \\ Induct \\ rw[v_size_def] \\ rw[]
 \\ res_tac \\ rw[]
End
val _ = export_rewrites["v_depth_def"];

val v_depth_ind = theorem"v_depth_ind";

Theorem v_inv_Block_tag_limit:
   v_inv c (Block ts n l) (v,f,tf,(heap:'a ml_heap)) ∧
   heap_in_memory_store heap a sp sp1 gens c s m (dm:'a word set) limit
  ⇒ n < dimword(:'a) DIV 16
Proof
  rw[v_inv_def] \\ fs[BlockRep_def]
  \\ fs[heap_in_memory_store_def]
  \\ imp_res_tac heap_lookup_SPLIT
  \\ fs[word_heap_APPEND,word_heap_def,word_el_def,word_payload_def]
  \\ fs[encode_header_def,X_LT_DIV]
  \\ fsrw_tac[sep_cond_ss][cond_STAR]
  \\ fs[LEFT_ADD_DISTRIB]
QED

Definition elements_list_def:
  (elements_list [] = T) ∧
  (elements_list [v] = T) ∧
  (elements_list (v::w::vs) =
   ∃ts t ls. w = Block ts t ls ∧ MEM v ls ∧ elements_list (w::vs))
End
val _ = export_rewrites["elements_list_def"];

val elements_list_ind = theorem"elements_list_ind";

Theorem elements_list_size_mono = Q.prove(
  `∀ls x xs y. ls = x::xs ==> elements_list (x::xs) ==> MEM y xs ==> vb_size x < vb_size y`,
  ho_match_mp_tac elements_list_ind
  \\ rw[] \\ fs[vb_size_def]
  \\ imp_res_tac SUM_MAP_MEM_bound
  \\ first_x_assum(qspec_then`vb_size`mp_tac)
  \\ srw_tac[ETA_ss][] \\ fs[] \\ res_tac
  \\ fsrw_tac[ETA_ss][] \\ decide_tac)
  |> SIMP_RULE std_ss []

Theorem memory_rel_depth_limit:
   ∀v w vars.
    memory_rel c b ts refs sp st m dm ((v,(w:'a word_loc))::vars) ∧
    elements_list (v::(MAP FST vars)) ∧ good_dimindex(:'a)
    ⇒
    ∃ls.
       memory_rel c b ts refs sp st m dm (ls ++ (v,w)::vars) ∧
       v_depth v = LENGTH ls ∧
       elements_list (MAP FST ls ++ (v::(MAP FST vars)))
Proof
  ho_match_mp_tac v_ind
  \\ rw[v_depth_def,LENGTH_NIL_SYM,NULL_EQ,list_max_def]
  \\ fsrw_tac[ETA_ss][]
  \\ `MEM (list_max (MAP v_depth l)) (MAP v_depth l)`
    by ( match_mp_tac list_max_mem \\ rw[] )
  \\ fs[MEM_MAP,EVERY_MEM]
  \\ qmatch_assum_rename_tac`MEM e l`
  \\ first_x_assum(qspec_then`e`mp_tac) \\ simp[]
  \\ pop_assum(strip_assume_tac o REWRITE_RULE[MEM_EL]) \\ rveq
  \\ rpt_drule memory_rel_Block_MEM \\ rw[]
  \\ first_x_assum drule
  \\ impl_tac >- ( simp[MEM_EL] \\ metis_tac[] )
  \\ rw[] \\ rw[]
  \\ qmatch_asmsub_rename_tac`MAP FST ls ++ EL i l::_`
  \\ qmatch_asmsub_abbrev_tac`(EL i l,wi)`
  \\ qexists_tac`ls ++ [(EL i l,wi)]`
  \\ simp[]
  \\ metis_tac[CONS_APPEND,APPEND_ASSOC]
QED

Theorem memory_rel_elements_list_distinct:
   ∀vs vars.
     memory_rel c be ts refs sp st m (dm:'a word set) vars ∧
     elements_list vs ∧ vs = MAP FST vars ∧
     good_dimindex (:'a)
     ⇒
     ALL_DISTINCT (MAP SND vars)
Proof
  ho_match_mp_tac elements_list_ind
  \\ rw[] \\ rw[]
  \\ Cases_on`vars` \\ fs[]
  \\ qmatch_assum_rename_tac`_ :: _ = MAP FST l1` \\ rveq
  \\ Cases_on`l1` \\ fs[] \\ rveq
  \\ qmatch_assum_rename_tac`Block _ _ _ = FST p`
  \\ Cases_on`p` \\ fs[]
  \\ qmatch_assum_rename_tac`MEM (FST p) ls`
  \\ Cases_on`p` \\ fs[] \\ rveq
  \\ qmatch_asmsub_rename_tac`(Block ts2 t ls,wb)`
  \\ qmatch_asmsub_rename_tac`Block _ t ls :: MAP FST l1`
  \\ first_x_assum(qspec_then`(Block ts2 t ls,wb)::l1`mp_tac)
  \\ simp[]
  \\ rpt_drule memory_rel_tail \\ simp[]
  \\ strip_tac \\ strip_tac
  \\ qmatch_asmsub_rename_tac`(v,w)::(Block _ _ _,_)::_`
  \\ Cases_on`w = wb` \\ fs[]
  >- (
    rpt_drule memory_rel_pointer_eq_size
    \\ simp[vb_size_def]
    \\ imp_res_tac SUM_MAP_MEM_bound
    \\ first_x_assum(qspec_then`vb_size`mp_tac)
    \\ srw_tac[ETA_ss][]
    \\ strip_tac \\ fs[] )
  \\ simp[MEM_MAP,FORALL_PROD]
  \\ rpt strip_tac
  \\ rename1`MEM (v',w) l1`
  \\ `memory_rel c be ts refs sp st m dm ((v,w)::(v',w)::l1)`
  by (
    last_x_assum mp_tac
    \\ match_mp_tac memory_rel_rearrange
    \\ rw[] \\ rw[] )
  \\ rpt_drule memory_rel_pointer_eq_size
  \\ imp_res_tac elements_list_size_mono
  \\ first_x_assum(qspec_then`v'`mp_tac)
  \\ simp[MEM_MAP,EXISTS_PROD]
  \\ impl_tac >- metis_tac[]
  \\ simp[vb_size_def]
  \\ srw_tac[ETA_ss][]
  \\ imp_res_tac SUM_MAP_MEM_bound
  \\ first_x_assum(qspec_then`vb_size`mp_tac)
  \\ simp[]
QED

Theorem memory_rel_elements_list_words:
   ∀vs vars.
   memory_rel c be ts refs sp st m (dm:'a word set) vars ∧
   elements_list vs ∧ vs = MAP FST vars ∧
   good_dimindex(:'a)
   ⇒ vars ≠ [] ==> EVERY isWord (TL (MAP SND vars))
Proof
  ho_match_mp_tac elements_list_ind
  \\ rw[] \\ rw[] \\ Cases_on`vars` \\ fs[]
  \\ qmatch_assum_rename_tac`_ :: _ = MAP FST l1` \\ rveq
  \\ Cases_on`l1` \\ fs[] \\ rveq
  \\ qmatch_assum_rename_tac`Block _ _ _ = FST p`
  \\ Cases_on`p` \\ fs[]
  \\ qmatch_assum_rename_tac`MEM (FST p) ls`
  \\ Cases_on`p` \\ fs[] \\ rveq
  \\ rpt_drule memory_rel_tail \\ strip_tac
  \\ rpt_drule memory_rel_Block_IMP \\ strip_tac
  \\ rw[isWord_def]
  \\ first_x_assum drule \\ simp[]
QED

Theorem memory_rel_depth_size_limit:
   ∀v w vars.
   memory_rel c be ts refs sp st m dm ((v,w:'a word_loc)::vars) ∧
   good_dimindex (:'a)
   ⇒
   vb_size v ≤ dimword(:'a) ** (v_depth v + 1)
Proof
  ho_match_mp_tac v_ind \\ rw[vb_size_def,EXP,NULL_EQ,list_max_def]
  \\ TRY ( fs[dimword_def] \\ NO_TAC )
  >- (
    rpt_drule memory_rel_Block_IMP
    \\ rw[X_LT_DIV] )
  \\ fsrw_tac[ETA_ss][EXP_ADD]
  \\ rpt_drule memory_rel_Block_IMP \\ strip_tac
  \\ `LENGTH l < dimword(:'a) DIV 16` by (
    fs[dimword_def] \\
    qspecl_then[`dimindex(:'a)`,`4`,`2`]mp_tac EXP_SUB
    \\ impl_tac >- fs[good_dimindex_def]
    \\ strip_tac \\ fs[X_LT_DIV] )
  \\ `SUM (MAP vb_size l) <= list_max (MAP vb_size l) * LENGTH l`
    by metis_tac[list_max_sum_bound,LENGTH_MAP]
  \\ `n < dimword(:'a) DIV 16`
  by (
    fs[memory_rel_def,word_ml_inv_def,bc_stack_ref_inv_def,abs_ml_inv_def]
    \\ imp_res_tac v_inv_Block_tag_limit \\ fs[X_LT_DIV] )
  \\ `n + LENGTH l + 1 < dimword(:'a) DIV 8` by ( fs[X_LT_DIV] )
  \\ match_mp_tac LESS_EQ_TRANS
  \\ qexists_tac`SUM (MAP vb_size l) + dimword(:'a) DIV 8`
  \\ conj_tac >- simp[]
  \\ qabbrev_tac`f = λx.  dimword(:'a) * dimword(:'a) ** x`
  \\ `list_max (MAP vb_size l) <= list_max (MAP (f o v_depth) l)`
  by (
    match_mp_tac list_max_bounded_elements
    \\ fs[LIST_REL_EL_EQN,EVERY_MEM,MEM_EL,EL_MAP,Abbr`f`,PULL_EXISTS]
    \\ rw[] \\ first_x_assum (match_mp_tac o MP_CANON) \\ rw[]
    \\ rpt_drule memory_rel_Block_MEM \\ rw[]
    \\ metis_tac[CONS_APPEND] )
  \\ Q.ISPECL_THEN[`f`,`MAP v_depth l`]mp_tac list_max_map
  \\ simp[NULL_EQ,Abbr`f`]
  \\ rewrite_tac[TWO,EXP,ONE]
  \\ rewrite_tac[GSYM ONE,MULT_RIGHT_1]
  \\ rewrite_tac[GSYM MULT_ASSOC]
  \\ disch_then(CHANGED_TAC o SUBST_ALL_TAC o SYM)
  \\ fs[MAP_MAP_o]
  \\ qmatch_goalsub_abbrev_tac`MAP (f o v_depth)`
  \\ qmatch_goalsub_abbrev_tac`(z:num) + dw DIV 8 <= _`
  \\ qmatch_assum_abbrev_tac`z <= ll * sz`
  \\ qmatch_assum_abbrev_tac`sz <= dz`
  \\ fs[X_LT_DIV]
  \\ fs[LEFT_ADD_DISTRIB]
  \\ match_mp_tac LESS_EQ_TRANS
  \\ qexists_tac`dw DIV 8 + ll * sz` \\ simp[]
  \\ match_mp_tac LESS_EQ_TRANS
  \\ qexists_tac`(ll + dw DIV 8) * sz`
  \\ simp[LEFT_ADD_DISTRIB]
  \\ conj_tac
  >- (
    Cases_on`sz` \\ fs[Abbr`z`,SUM_eq_0]
    \\ Cases_on`l` \\ fs[]
    \\ fsrw_tac[DNF_ss][]
    \\ Cases_on`h` \\ fs[vb_size_def] )
  \\ CONV_TAC(LAND_CONV(LAND_CONV(REWR_CONV MULT_COMM)))
  \\ simp[GSYM LEFT_ADD_DISTRIB]
  \\ CONV_TAC(LAND_CONV(REWR_CONV MULT_COMM))
  \\ match_mp_tac LESS_MONO_MULT2 \\ simp[]
  \\ match_mp_tac LESS_EQ_TRANS
  \\ qexists_tac`dw DIV 16 + dw DIV 8`
  \\ fs[X_LE_DIV]
  \\ fs[Abbr`dw`,dimword_def,good_dimindex_def]
QED

Theorem memory_rel_limit:
   ∀v w.
   memory_rel c be ts refs sp st m dm ((v,w:'a word_loc)::vars) ∧
   good_dimindex (:'a)
   ==>
   vb_size v * dimword (:'a) < MustTerminate_limit (:'a) - dimword (:'a)
Proof
  rw[]
  \\ rpt_drule memory_rel_depth_size_limit \\ rw[]
  \\ `memory_rel c be ts refs sp st m dm [(v,w)]`
  by (
    qhdtm_x_assum`memory_rel`mp_tac
    \\ match_mp_tac memory_rel_rearrange
    \\ rw[] )
  \\ rpt_drule memory_rel_depth_limit
  \\ simp[] \\ strip_tac
  \\ rpt_drule memory_rel_elements_list_distinct \\ strip_tac
  \\ rpt_drule memory_rel_elements_list_words \\ strip_tac
  \\ rpt_drule word_list_limit
  \\ qmatch_goalsub_abbrev_tac`TL ll`
  \\ `∃h t. ll = h::t`
  by ( Cases_on`ll` \\ fs[markerTheory.Abbrev_def] )
  \\ qunabbrev_tac`ll` \\ fs[]
  \\ pop_assum(mp_tac o Q.AP_TERM`LENGTH`)
  \\ fs[ADD1] \\ rw[] \\ fs[]
  \\ fs[EXP_ADD]
  \\ simp[MustTerminate_limit_def]
  \\ match_mp_tac LESS_EQ_LESS_TRANS
  \\ qexists_tac`dimword(:'a) * (dimword (:'a) * dimword(:'a) ** LENGTH t)`
  \\ conj_tac
  >- ( match_mp_tac LESS_MONO_MULT2 \\ simp[] )
  \\ match_mp_tac LESS_EQ_LESS_TRANS
  \\ qexists_tac`dimword(:'a) * (dimword (:'a) * dimword(:'a) ** dimword(:'a))`
  \\ conj_tac
  >- ( match_mp_tac LESS_MONO_MULT2 \\ simp[] )
  \\ match_mp_tac LESS_EQ_LESS_TRANS
  \\ qexists_tac`dimword(:'a) ** dimword(:'a) ** dimword(:'a)`
  \\ reverse conj_tac
  >- ( assume_tac ZERO_LT_dimword \\ simp[MustTerminate_limit_def] )
  \\ rewrite_tac[GSYM EXP]
  \\ match_mp_tac EXP_BASE_LEQ_MONO_IMP
  \\ simp[]
  \\ match_mp_tac LESS_EQ_TRANS
  \\ qexists_tac`dimword (:'a) * dimword (:'a)`
  \\ simp[]
  \\ fs[good_dimindex_def,dimword_def]
QED

Theorem memory_rel_ptr_eq:
   memory_rel c be ts refs sp st m dm ((v1,x1)::(v2,x1:'a word_loc)::vars) /\
   do_eq refs v1 v2 = Eq_val b /\
   good_dimindex (:'a) ==> b
Proof
  rw [] \\ CCONTR_TAC \\ fs [] \\ rveq
  \\ imp_res_tac memory_rel_pointer_eq
QED

val memory_rel_Block_Block_small_eq = prove(
  ``memory_rel c be ts refs sp st m dm
      ((Block ts1 t1 v1,Word (w1:'a word))::(Block ts2 t2 v2,Word w2)::vars) /\
    good_dimindex (:'a) /\ w1 <> w2 /\ ¬word_bit 0 w1 ==>
    LENGTH v1 <> LENGTH v2 \/ t1 <> t2``,
  rw [] \\ drule memory_rel_Block_IMP \\ fs []
  \\ fs [word_bit] \\ strip_tac \\ rveq
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ CCONTR_TAC \\ fs [LENGTH_NIL] \\ rveq
  \\ imp_res_tac memory_rel_tail
  \\ drule memory_rel_Block_IMP \\ fs []);

Theorem memory_rel_simple_eq:
   memory_rel c be ts refs sp st m dm ((v1,x1)::(v2,x2)::vars) /\
   do_eq refs v1 v2 = Eq_val b /\
   good_dimindex (:'a) ==>
   ?w1 w2:'a word.
     x1 = Word w1 /\ x2 = Word w2 /\
     (~word_bit 0 w1 \/ ~word_bit 0 w2 ==>
     (w1 = w2) = b)
Proof
  Cases_on `v1` \\ Cases_on `v2` \\ fs [do_eq_def] \\ rpt strip_tac
  \\ TRY (
    gvs [CaseEq"bool"]
    \\ drule memory_rel_RefPtr_EQ \\ fs [] \\ rw []
    \\ imp_res_tac memory_rel_RefPtr_IMP
    \\ imp_res_tac memory_rel_tl
    \\ imp_res_tac memory_rel_RefPtr_IMP
    \\ fs[word_bit_def] \\ NO_TAC)
  THEN1
   (rpt_drule memory_rel_Number_cmp \\ strip_tac \\ fs []
    \\ reverse (Cases_on `word_bit 0 w1`) \\ fs []
    \\ reverse (Cases_on `word_bit 0 w2`) \\ fs []
    THEN1 (CCONTR_TAC \\ fs [])
    \\ rpt_drule memory_rel_swap \\ strip_tac \\ fs []
    \\ rpt_drule memory_rel_Number_cmp \\ strip_tac \\ fs []
    \\ CCONTR_TAC \\ fs [])
  THEN1
   (drule memory_rel_Word64_IMP \\ fs []
    \\ imp_res_tac memory_rel_tail
    \\ drule memory_rel_Word64_IMP \\ fs []
    \\ pop_assum kall_tac
    \\ rpt strip_tac \\ fs [get_addr_0,GSYM word_bit])
  \\ Cases_on `isClos n l` \\ fs [] THEN1
   (every_case_tac \\ fs []
    \\ drule memory_rel_Block_IMP \\ fs []
    \\ imp_res_tac memory_rel_tail
    \\ drule memory_rel_Block_IMP \\ fs []
    \\ rw [] \\ fs [] \\ fs [word_bit,isClos_def] \\ rfs [])
  \\ Cases_on `isClos n' l'` \\ fs []
  \\ `?w1. x1 = Word w1` by
       (drule memory_rel_Block_IMP \\ fs [] \\ strip_tac \\ fs [])
  \\ `?w2. x2 = Word w2` by
       (imp_res_tac memory_rel_tail
        \\ drule memory_rel_Block_IMP \\ fs [] \\ strip_tac \\ fs [])
  \\ rveq \\ fs []
  \\ Cases_on `w1 = w2` \\ rveq
  THEN1 (fs [] \\ drule memory_rel_ptr_eq \\ fs [do_eq_def])
  \\ drule memory_rel_Block_Block_small_eq \\ fs []
  \\ Cases_on `word_bit 0 w1` \\ fs [] \\ strip_tac \\ fs []
  \\ imp_res_tac memory_rel_swap
  \\ drule memory_rel_Block_Block_small_eq \\ fs []
  \\ strip_tac \\ fs []
QED

Definition word_header_def:
  word_header c st a dm m =
    case get_real_addr c st a of
    | NONE => NONE
    | SOME a1 =>
        if ~(a1 IN dm) then NONE else
          case m a1 of Word x1 => SOME (a1,x1) | _ => NONE
End

Definition fix_clock_def:
  fix_clock ck l NONE = NONE /\
  fix_clock ck (l:num) (SOME (y,l1:num,ck1:num)) =
  let new_ck = if ck < ck1 then ck else ck1;
      new_l = if l < l1 then l else l1
  in SOME(y,new_l,new_ck)
End

val fix_clock_IMP = prove(
  ``!ck l x. fix_clock ck l x = SOME (w,l1,ck1) ==> ck1 <= ck /\ l1 <= l``,
  ho_match_mp_tac (theorem "fix_clock_ind") \\ fs [fix_clock_def] \\ rw []);

Definition word_is_clos_def:
  word_is_clos c h <=>
    (h && (tag_mask c || 2w)) = n2w (16 * closure_tag + 2) \/
    (h && (tag_mask c || 2w)) = n2w (16 * partial_app_tag + 2)
End

(* l  corresponds to the functional big-step semantics clock.
      Used to show that equality comparisons respect the
      MustTerminate limit.
   ck is an upper bound on the number of stack frames
      allocated by an equality comparison.
  *)
Definition word_eq_def:
  (word_eq c st dm m l ck w1 (w2:'a word) =
     if w1 = w2 then SOME (1w:'a word,l,ck) else
     if ~(word_bit 0 w1 /\ word_bit 0 w2) then SOME (0w,l,ck) else
       case (word_header c st w1 dm m, word_header c st w2 dm m) of
       | (SOME (a1,h1), SOME (a2,h2)) =>
           if (h1 && 0b1100w) = 0w (* is Block *) then
             if word_is_clos c h1 (* isClos *) then SOME (1w,l,ck) else
             if ~(h1 = h2) then SOME (0w,l,ck) else
             if l = 0(* \/ ck = 0 *)then NONE else
               word_eq_list c st dm m (l-1) ck (decode_length c h1)
                 (a1+bytes_in_word) (a2+bytes_in_word) else
           if ~(h1 = h2) then SOME (0w,l,ck) else
           if ~(word_bit 2 h1) (* is array *) then SOME (0w,l,ck) else
           if ~(word_bit 3 h1) /\ word_bit 4 h1 (* is cmp-by-pointer byte array *) then
             SOME (0w,l,ck)
           else
             (* must be a bignum or word64 or cmp-by-contents byte array *)
            (if l <= w2n (decode_length c h1)
             then NONE else
             case word_cmp_loop (decode_length c h1)
               (a1 + bytes_in_word * (decode_length c h1))
               (a2 + bytes_in_word * (decode_length c h1)) dm m of
             | NONE => NONE
             | SOME res => SOME (res,l - 1 - w2n (decode_length c h1),ck))
       | _ => NONE) /\
  (word_eq_list c st dm m l ck w a1 a2 =
     if w = 0w:'a word then SOME (1w,l,ck) else
     if ~(a1 IN dm) \/ ~(a2 IN dm) \/ (l = 0) \/ (ck=0) then NONE else
       case (m a1,m a2) of
       | (Word w1, Word w2) =>
        (case fix_clock (ck-1) (l-1) (word_eq c st dm m (l-1) (ck-1) w1 w2) of
         | NONE => NONE
         | SOME (x,l,ck') => if x <> 1w then SOME (x,l,ck) else
                            if l = 0 then NONE else
                              word_eq_list c st dm m (l-1) ck (w-1w)
                                (a1 + bytes_in_word) (a2 + bytes_in_word))
       | _ => NONE)
Termination
  WF_REL_TAC `measure(\x. case x of
                          | INL (c,st,dm,m,l1,ck1,w1,w2) => l1
                          | INR (c,st,dm,m,l1,ck1,w,a1,a2) => l1)` >>
  rw[] >> imp_res_tac fix_clock_IMP >> rw[]
End

val word_eq_ind = theorem "word_eq_ind";

Theorem word_eq_LESS_EQ:
  (!c st dm m l ck w1 (w2:'a word) x0 l1 ck1.
       word_eq c st dm m l ck w1 w2 = SOME (x0,l1,ck1) ==> l1 <= l /\ ck1 <= ck) /\
    (!c st dm m l ck w a1 (a2:'a word) x0 l1 ck1.
       word_eq_list c st dm m l ck w a1 a2 = SOME (x0,l1,ck1) ==> l1 <= l /\ ck1 <= ck)
Proof
  ho_match_mp_tac word_eq_ind
  \\ rw [] \\ pop_assum mp_tac
  \\ once_rewrite_tac [word_eq_def]
  \\ every_case_tac \\ fs []
  \\ rpt strip_tac \\ res_tac \\ fs []
  \\ rw [] \\ fs []
  \\ imp_res_tac fix_clock_IMP \\ fs []
  \\ `l ≠ 0` by(CCONTR_TAC >> fs[NOT_LESS_EQUAL])
  \\ res_tac
  \\ fs[]
QED

val fix_clock_word_eq = prove(
  ``fix_clock ck l (word_eq c st dm m l ck w1 w2) = word_eq c st dm m l ck w1 w2``,
  Cases_on `word_eq c st dm m l ck w1 w2` \\ fs [fix_clock_def]
  \\ PairCases_on `x` \\ fs [] \\ fs [fix_clock_def] \\ rw []
  \\ imp_res_tac word_eq_LESS_EQ \\ fs []);

Theorem word_eq_def[compute,allow_rebind] =
  word_eq_def |> REWRITE_RULE [fix_clock_word_eq]

Theorem word_eq_ind[allow_rebind] =
  word_eq_ind |> REWRITE_RULE [fix_clock_word_eq]

Theorem bit_pattern_1100[simp]:
   good_dimindex (:'a) ==>
    ((0b1100w && x1) = 0w <=> ~word_bit 2 x1 /\ ~word_bit 3 (x1:'a word))
Proof
  fs [fcpTheory.CART_EQ,word_and_def,word_index,fcpTheory.FCP_BETA,
      GSYM word_bit,good_dimindex_def] \\ fs [] \\ rw [] \\ eq_tac \\ rw []
  \\ metis_tac [DECIDE ``2 < 32n /\ 2 < 64n /\ 3 < 32n /\ 3 < 64n``]
QED

Theorem word_eq_add_clock:
  (!c st dm m l ck (a1:'a word) a2 res l' ck1 n.
  word_eq c st dm m l ck a1 a2 = SOME (res,l',ck1) ==>
  (word_eq c st dm m l (ck + n) a1 a2 = SOME (res,l',ck1 + n))) /\
  (!c st dm m l ck w (a1:'a word) a2 res l' ck1 n.
  word_eq_list c st dm m l ck w a1 a2 = SOME (res,l',ck1) ==>
  word_eq_list c st dm m l (ck + n) w a1 a2 = SOME (res,l',ck1 + n))
Proof
  ho_match_mp_tac word_eq_ind >> rpt strip_tac >>
  pop_assum mp_tac >>
  simp[Once word_eq_def] >> strip_tac >>
  let val tac = fn thm => rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq) >> assume_tac thm
  in
    PRED_ASSUM is_forall
     (fn thm =>
       (PRED_ASSUM is_forall tac >> assume_tac thm) ORELSE tac thm
     )
  end >>
  simp[Once word_eq_def] >>
  rfs[]
QED

Theorem word_eq_max_clock:
  (!c st dm m l ck (a1:'a word) a2 res l' ck1 n.
  word_eq c st dm m l ck a1 a2 = SOME (res,l',ck1) ==>
  (word_eq c st dm m l (MAX ck n) a1 a2 = SOME (res,l',ck1 + (n - ck)))) /\
  (!c st dm m l ck w (a1:'a word) a2 res l' ck1 n.
  word_eq_list c st dm m l ck w a1 a2 = SOME (res,l',ck1) ==>
  word_eq_list c st dm m l (MAX ck n) w a1 a2 = SOME (res,l',ck1 + (n - ck)))
Proof
  rw[MAX_DEF]
  >- (drule_then (qspec_then `n - ck` assume_tac) (CONJUNCT1 word_eq_add_clock) >>
      rfs[])
  >- (drule_then (qspec_then `n - ck` assume_tac) (CONJUNCT2 word_eq_add_clock) >>
      rfs[])
QED

Theorem word_eq_min_max_clock:
  (!x y. word_eq c st dm m l (MIN a b) a1 a2 = SOME (res,l',ck1) ==>
  ?ck1'. word_eq c st dm m l (MIN (MAX a x) (MAX b y)) a1 a2 = SOME (res,l',ck1')) /\
  (!x y. word_eq_list c st dm m l (MIN a b) w a1 a2 = SOME (res,l',ck1) ==>
  ?ck1'.  word_eq_list c st dm m l (MIN (MAX a x) (MAX b y)) w a1 a2 = SOME (res,l',ck1'))
Proof
  rw[MIN_DEF,MAX_DEF] >>
  fs[NOT_LESS] >>
  imp_res_tac LESS_ADD >>
  imp_res_tac LESS_EQ_ADD_EXISTS >>
  rveq >> fs[] >>
  MAP_FIRST dxrule (CONJUNCTS word_eq_add_clock) >>
  metis_tac[ADD_COMM,ADD_ASSOC]
QED

val memory_rel_isClos = prove(
  ``memory_rel c be ts refs sp st m dm ((Block ts1 t1 v1,Word (w1:'a word))::vars) /\
    word_bit 0 w1 /\
    get_real_addr c st w1 = SOME a' /\ m a' = Word x' /\ good_dimindex (:'a) ==>
    (isClos t1 v1 <=> word_is_clos c x')``,
  rw [] \\ drule memory_rel_Block_IMP \\ fs [word_bit] \\ rw []
  \\ fs [word_is_clos_def]
  \\ drule encode_header_tag_mask \\ fs [] \\ strip_tac
  \\ fs [isClos_def]
  \\ `4 <= dimindex (:'a)` by fs [good_dimindex_def]
  \\ fs [EXP_SUB,X_LT_DIV,LEFT_ADD_DISTRIB]
  \\ `(16 * t1 + 2) < dimword (:α)` by
        (fs [good_dimindex_def,dimword_def] \\ rfs []) \\ fs []
  \\ fs [good_dimindex_def,dimword_def,
         backend_commonTheory.partial_app_tag_def,
         backend_commonTheory.closure_tag_def]);

Definition eq_assum_def:
  (eq_assum a m dm [] = T) /\
  (eq_assum a m dm (v::vs) <=>
     a IN dm /\ eq_assum (a + bytes_in_word) m dm vs)
End

Definition eq_explode_def:
  (eq_explode a m dm [] = []) /\
  (eq_explode a m dm (v::vs) = (v,m a) :: eq_explode (a + bytes_in_word) m dm vs)
End

val eq_explode_APPEND = prove(
  ``!xs ys a.
      eq_explode a m dm (xs ++ ys) =
      eq_explode a m dm xs ++
      eq_explode (a + n2w (LENGTH xs) * bytes_in_word) m dm ys``,
  Induct \\ fs [eq_explode_def,ADD1,bytes_in_word_def,word_mul_n2w]
  \\ fs [RIGHT_ADD_DISTRIB] \\ fs [GSYM word_add_n2w]);

val eq_assum_APPEND = prove(
  ``!xs ys a.
      eq_assum a m dm (xs ++ ys) <=>
      eq_assum a m dm xs /\
      eq_assum (a + n2w (LENGTH xs) * bytes_in_word) m dm ys``,
  Induct \\ fs [eq_assum_def,ADD1,bytes_in_word_def,word_mul_n2w]
  \\ fs [RIGHT_ADD_DISTRIB] \\ fs [GSYM word_add_n2w]
  \\ rw [] \\ eq_tac \\ rw []);

val memory_rel_Block_explode_lemma = prove(
  ``!n.
      memory_rel c be ts refs sp st m dm ((Block ts1 t1 v1,Word w1)::vars) /\
      word_bit 0 w1 /\ get_real_addr c st w1 = SOME a /\ good_dimindex (:α) ==>
      memory_rel c be ts refs sp st m dm
        (eq_explode (a + bytes_in_word) m dm (TAKE n v1) ++
         (Block ts1 t1 v1,Word (w1:'a word))::vars) /\
      eq_assum (a + bytes_in_word) m dm (TAKE n v1)``,
  Induct THEN1
   (fs [TAKE_def,eq_explode_def,eq_assum_def] \\ rw []
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [] \\ rw [] \\ fs [] \\ NO_TAC)
  \\ reverse (Cases_on `n < LENGTH v1`)
  THEN1 (fs [TAKE_LENGTH_TOO_LONG])
  \\ drule (GSYM SNOC_EL_TAKE)
  \\ fs [SNOC_APPEND] \\ ntac 2 strip_tac
  \\ fs [eq_explode_APPEND,eq_explode_def,eq_assum_APPEND,eq_assum_def]
  \\ `memory_rel c be ts refs sp st m dm
        ((Block ts1 t1 v1,Word w1)::
         (eq_explode (a + bytes_in_word) m dm (TAKE n v1) ++ vars))` by
   (qpat_x_assum `memory_rel c be ts refs sp st m dm _` kall_tac
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [] \\ rw [] \\ fs [] \\ NO_TAC)
  \\ rpt_drule memory_rel_Block_MEM \\ fs []
  \\ fs [get_real_offset_def,Smallnum_def]
  \\ fs [good_dimindex_def,WORD_MUL_LSL,word_mul_n2w,Smallnum_def]
  \\ fs[bytes_in_word_def,word_mul_n2w]
  \\ strip_tac
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ fs [] \\ rw [] \\ fs []);

Theorem memory_rel_Block_explode:
   memory_rel c be ts refs sp st m dm ((Block ts1 t1 v1,Word w1)::vars) /\
    word_bit 0 w1 /\ get_real_addr c st w1 = SOME a /\ good_dimindex (:α) ==>
    memory_rel c be ts refs sp st m dm
      (eq_explode (a + bytes_in_word:'a word) m dm v1 ++ vars) /\
    eq_assum (a + bytes_in_word) m dm v1
Proof
  strip_tac
  \\ rpt_drule (memory_rel_Block_explode_lemma |> Q.SPEC `LENGTH (v1:v list)`)
  \\ strip_tac
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ fs [] \\ rw [] \\ fs []
QED

Theorem memory_rel_Loc:
   memory_rel c be ts refs sp st m dm ((v1,Loc n k)::vars) ==> v1 = CodePtr n
Proof
  fs [memory_rel_def,word_ml_inv_def,PULL_EXISTS,abs_ml_inv_def,
      bc_stack_ref_inv_def] \\ rw []
  \\ Cases_on `v1` \\ fs [v_inv_def,word_addr_def]
  \\ every_case_tac \\ fs [] \\ rveq \\ fs [word_addr_def]
QED

Theorem memory_rel_ByteArray_words_IMP:
   memory_rel c be ts refs sp st m dm ((RefPtr bl p,Word (w:'a word))::vars) ∧
   lookup p refs = SOME (ByteArray fl vals) ∧
   good_dimindex(:'a) ∧
   get_real_addr c st w = SOME a ⇒
   ∃x frame.
     m a = Word x ∧
     (word_list(a + bytes_in_word)
        (MAP Word (write_bytes vals (REPLICATE (w2n (decode_length c x)) 0w) be))
      * frame) (fun2set (m,dm)) ∧
   w2n (decode_length c x) < dimword(:'a) ∧
   w2n (decode_length c x) = LENGTH vals DIV (dimindex(:'a) DIV 8) + 1
Proof
  rw[memory_rel_def,word_ml_inv_def,abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def]
  \\ fs[word_addr_def] \\ rw[]
  \\ first_x_assum(qspec_then`p`mp_tac)
  \\ impl_tac >-  (
    simp[reachable_refs_def]
    \\ qexists_tac`RefPtr bl p` \\ simp[get_refs_def] )
  \\ rw[bc_ref_inv_def]
  \\ Cases_on`FLOOKUP f p` \\ fs[FLOOKUP_DEF]
  \\ fs[heap_in_memory_store_def]
  \\ imp_res_tac get_real_addr_get_addr \\ fs[]
  \\ pop_assum kall_tac
  \\ imp_res_tac heap_lookup_SPLIT
  \\ fs[word_heap_APPEND,word_heap_def]
  \\ fsrw_tac[star_ss][word_el_def,Bytes_def,LET_THM,word_payload_def]
  \\ fs[word_list_def]
  \\ SEP_R_TAC \\ simp[]
  \\ fsrw_tac[sep_cond_ss][cond_STAR]
  \\ simp [GSYM PULL_EXISTS]
  \\ `LENGTH vals DIV (dimindex (:α) DIV 8) + 1 < dimword (:α)`
       by (fs[dimword_def,good_dimindex_def] \\ fs[])
  \\ simp[]
  \\ goal_assum assume_tac
  \\ SEP_F_TAC \\ fs []
QED

Theorem poly_inj_lemma:
   (a:num) < b ∧ a' < b ∧ a + b * c = a' + b * c' ⇒ a = a' ∧ c = c'
Proof
  strip_tac
  \\ qspec_then`b`mp_tac DIVISION \\ simp[]
  \\ disch_then(qspec_then`a + b * c`mp_tac)
  \\ simp[ADD_DIV_RWT,LESS_DIV_EQ_ZERO]
  \\ once_rewrite_tac[MULT_COMM] \\ simp[MULT_DIV]
  \\ strip_tac \\ fs[]
QED

Theorem mw2n_inj:
   ∀x y. LENGTH x = LENGTH y ⇒ (mw2n (x:'a word list) = mw2n y ⇔ x = y)
Proof
  Induct \\ simp[mw2n_def,LENGTH_NIL,LENGTH_NIL_SYM]
  \\ gen_tac \\ Cases \\ simp[mw2n_def]
  \\ rw[EQ_IMP_THM]
  \\ res_tac \\ fs[]
  \\ imp_res_tac poly_inj_lemma
  \\ fs[w2n_lt]
QED

Theorem write_bytes_inj:
   good_dimindex(:'a) ==>
   ∀ws bs1 bs2.
     LENGTH bs1 = LENGTH bs2 ∧
     LENGTH bs1 ≤ LENGTH ws * (dimindex(:'a) DIV 8) ∧
     LENGTH ws ≤ LENGTH bs1 DIV (dimindex(:'a) DIV 8) + 1 ⇒
     (write_bytes bs1 (ws:'a word list) be = write_bytes bs2 ws be ⇔ bs1 = bs2)
Proof
  strip_tac \\ Induct
  \\ simp[write_bytes_def,LENGTH_NIL,LENGTH_NIL_SYM]
  \\ rw[] \\ rw[EQ_IMP_THM] \\ fs[MULT_CLAUSES]
  \\ qmatch_asmsub_abbrev_tac`bytes_to_word bw 0w bs1 _ _`
  \\ `0 < bw` by fs[Abbr`bw`,X_LT_DIV,good_dimindex_def]
  \\ fs[ADD1]
  \\ first_x_assum(qspecl_then[`DROP bw bs1`,`DROP bw bs2`]mp_tac)
  \\ impl_tac
  >- (
    rfs[] \\
    Cases_on`LENGTH ws = 0` \\ fs[] \\
    qspecl_then[`LENGTH bs2`,`bw`,`1`]mp_tac(Q.GENL[`m`,`n`,`q`]DIV_SUB) \\
    impl_tac >- (
      fs[X_LE_DIV]
      \\ Cases_on`LENGTH ws` \\ fs[MULT_CLAUSES] )
    \\ simp[] )
  \\ simp[] \\ strip_tac \\ fs[]
  \\ `TAKE bw bs1 = TAKE bw bs2` suffices_by metis_tac[TAKE_DROP]
  \\ map_every (fn i =>
       qpat_assum`bytes_to_word _ _ _ _ _ = _`(strip_assume_tac o
         Q.AP_TERM`get_byte (n2w ^(numSyntax.term_of_int i))`))
      (List.tabulate(8,I ))
  \\ qspec_then`2`mp_tac(Q.GENL[`k`,`i`]get_byte_bytes_to_word)
  \\ qspec_then`3`mp_tac(Q.GENL[`k`,`i`]get_byte_bytes_to_word)
  \\ simp[Abbr`bw`]
  \\ ntac 2 strip_tac
  \\ qhdtm_x_assum`good_dimindex`mp_tac
  \\ first_assum(qspec_then`bs1`mp_tac o CONV_RULE SWAP_FORALL_CONV)
  \\ first_x_assum(qspec_then`bs2`mp_tac o CONV_RULE SWAP_FORALL_CONV)
  \\ first_assum(qspec_then`bs1`mp_tac o CONV_RULE SWAP_FORALL_CONV)
  \\ first_x_assum(qspec_then`bs2`mp_tac o CONV_RULE SWAP_FORALL_CONV)
  \\ ntac 4 (disch_then(qspec_then`h`strip_assume_tac o CONV_RULE SWAP_FORALL_CONV))
  \\ rw[good_dimindex_def]
  \\ Cases_on`bs1` \\ Cases_on`bs2` \\ fs[]
  \\ first_x_assum(fn th => qspec_then`0`mp_tac th \\ assume_tac th)
  \\ last_x_assum(fn th => qspec_then`0`mp_tac th \\ assume_tac th)
  \\ simp_tac(srw_ss())[]
  \\ ntac 2 strip_tac \\ (conj_tac >- metis_tac[])
  \\ qmatch_goalsub_rename_tac`TAKE _ bs1 = TAKE _ bs2`
  \\ Cases_on`bs1` \\ Cases_on`bs2` \\ fs[]
  \\ first_x_assum(fn th => qspec_then`1`mp_tac th \\ assume_tac th)
  \\ last_x_assum(fn th => qspec_then`1`mp_tac th \\ assume_tac th)
  \\ simp_tac(srw_ss()++ARITH_ss)[ADD1]
  \\ ntac 2 strip_tac \\ (conj_tac >- metis_tac[])
  \\ qmatch_goalsub_rename_tac`TAKE _ bs1 = TAKE _ bs2`
  \\ Cases_on`bs1` \\ Cases_on`bs2` \\ fs[]
  \\ first_x_assum(fn th => qspec_then`2`mp_tac th \\ assume_tac th)
  \\ last_x_assum(fn th => qspec_then`2`mp_tac th \\ assume_tac th)
  \\ simp_tac(srw_ss()++ARITH_ss)[ADD1]
  \\ ntac 2 strip_tac \\ (conj_tac >- metis_tac[])
  \\ qmatch_goalsub_rename_tac`TAKE _ bs1 = TAKE _ bs2`
  \\ Cases_on`bs1` \\ Cases_on`bs2` \\ fs[]
  \\ first_x_assum(fn th => qspec_then`3`mp_tac th \\ assume_tac th)
  \\ last_x_assum(fn th => qspec_then`3`mp_tac th \\ assume_tac th)
  \\ simp_tac(srw_ss()++ARITH_ss)[ADD1]
  \\ ntac 2 strip_tac \\ (TRY conj_tac >- metis_tac[])
  \\ qmatch_goalsub_rename_tac`TAKE _ bs1 = TAKE _ bs2`
  \\ Cases_on`bs1` \\ Cases_on`bs2` \\ fs[]
  \\ first_x_assum(fn th => qspec_then`4`mp_tac th \\ assume_tac th)
  \\ last_x_assum(fn th => qspec_then`4`mp_tac th \\ assume_tac th)
  \\ simp_tac(srw_ss()++ARITH_ss)[ADD1]
  \\ ntac 2 strip_tac \\ (conj_tac >- metis_tac[])
  \\ qmatch_goalsub_rename_tac`TAKE _ bs1 = TAKE _ bs2`
  \\ Cases_on`bs1` \\ Cases_on`bs2` \\ fs[]
  \\ first_x_assum(fn th => qspec_then`5`mp_tac th \\ assume_tac th)
  \\ last_x_assum(fn th => qspec_then`5`mp_tac th \\ assume_tac th)
  \\ simp_tac(srw_ss()++ARITH_ss)[ADD1]
  \\ ntac 2 strip_tac \\ (conj_tac >- metis_tac[])
  \\ qmatch_goalsub_rename_tac`TAKE _ bs1 = TAKE _ bs2`
  \\ Cases_on`bs1` \\ Cases_on`bs2` \\ fs[]
  \\ first_x_assum(fn th => qspec_then`6`mp_tac th \\ assume_tac th)
  \\ last_x_assum(fn th => qspec_then`6`mp_tac th \\ assume_tac th)
  \\ simp_tac(srw_ss()++ARITH_ss)[ADD1]
  \\ ntac 2 strip_tac \\ (conj_tac >- metis_tac[])
  \\ qmatch_goalsub_rename_tac`TAKE _ bs1 = TAKE _ bs2`
  \\ Cases_on`bs1` \\ Cases_on`bs2` \\ fs[]
  \\ first_x_assum(fn th => qspec_then`7`mp_tac th \\ assume_tac th)
  \\ last_x_assum(fn th => qspec_then`7`mp_tac th \\ assume_tac th)
  \\ simp_tac(srw_ss()++ARITH_ss)[ADD1]
  \\ metis_tac[]
QED

Triviality MIN_ADD:
  MIN a b + c = MIN (a + c) (b + c)
Proof
  rw[MIN_DEF]
QED

Triviality MIN_SUB:
  MIN a b - c = MIN (a - c) (b - c)
Proof
  rw[MIN_DEF]
QED

Triviality MAX_ADD:
  MAX a b + c = MAX (a + c) (b + c)
Proof
  rw[MAX_DEF]
QED

Triviality MAX_SUB:
  MAX a b - c = MAX (a - c) (b - c)
Proof
  rw[MAX_DEF]
QED

Theorem word_eq_thm0:
  (!refs v1 v2 l ck b w1 w2.
       memory_rel c be ts refs sp st m dm
          ((v1,Word w1)::(v2,Word w2:'a word_loc)::vars) /\
       do_eq refs v1 v2 = Eq_val b /\
       ck = MIN (vs_depth v1) (vs_depth v2) /\
       vb_size v1 * dimword (:'a) < l /\
       good_dimindex (:'a) ==>
       ?res l1 ck1. word_eq c st dm m l ck w1 w2 = SOME (res,l1,ck1) /\
                (b <=> (res = 1w)) /\
                l <= l1 + vb_size v1 * dimword (:'a)) /\
    (!refs v1 v2 l ck b w1 w2 t1 t2.
       memory_rel c be ts refs sp st m dm
          (eq_explode w1 m dm v1 ++ eq_explode w2 m dm v2 ++ vars) /\
       LENGTH v2 = LENGTH v1 /\ LENGTH v1 < dimword (:'a) /\
       eq_assum w1 m dm v1 /\ eq_assum w2 m dm v2 /\
       do_eq_list refs v1 v2 = Eq_val b /\
       ck = MIN (vs_depth_list v1) (vs_depth_list v2) /\
       (LENGTH v1 + SUM (MAP vb_size v1)) * dimword (:'a) < l /\
       good_dimindex (:'a) ==>
       ?res l1 ck1. word_eq_list c st dm m l ck (n2w (LENGTH v1)) w1 w2 = SOME (res,l1,ck1) /\
                (b <=> (res = 1w)) /\
                l <= l1 + (LENGTH v1 + SUM (MAP vb_size v1)) * dimword (:'a))
Proof
  ho_match_mp_tac do_eq_ind \\ rpt conj_tac
  \\ once_rewrite_tac [do_eq_def] \\ simp []
  THEN1 (* do_eq Numbers *)
   (rw [] \\ fs [vb_size_def,vs_depth_def]
    \\ once_rewrite_tac [word_eq_def]
    \\ IF_CASES_TAC
    THEN1 (rveq
           \\ drule memory_rel_pointer_eq
           \\ fs [do_eq_def])
    \\ drule memory_rel_Number_cmp \\ fs []
    \\ reverse (Cases_on `word_bit 0 w1`) THEN1 (fs [] \\ rw []) \\ fs []
    \\ reverse (Cases_on `word_bit 0 w2`)
    THEN1
     (fs [] \\ drule memory_rel_swap \\ strip_tac
      \\ drule memory_rel_Number_cmp \\ fs [])
    \\ fs [] \\ strip_tac
    \\ fs [word_header_def]
    \\ `~(small_int (:'a) n1)` by
     (imp_res_tac memory_rel_any_Number_IMP
      \\ strip_tac \\ fs [] \\ rveq \\ fs [word_bit])
    \\ drule memory_rel_Number_bignum_IMP_ALT \\ fs []
    \\ Cases_on `word_bit 2 x1` \\ fs []
    \\ Cases_on `word_bit 3 x1` \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq
    THEN1
     (disch_then kall_tac
      \\ qpat_x_assum `word_cmp_res n1 n2 = _` mp_tac
      \\ fs [word_cmp_res_def]
      \\ Cases_on `n1 = n2` \\ fs []
      \\ fs [good_dimindex_def] \\ rw [] \\ fs [dimword_def])
    \\ strip_tac \\ fs []
    \\ Cases_on `0 ≤ n1` \\ fs [] THEN1
     (fs [word_cmp_res_def] \\ rw []
      \\ fs [good_dimindex_def] \\ rw [dimword_def]
     )
    \\ drule memory_rel_swap \\ strip_tac
    \\ drule memory_rel_Number_cmp \\ fs []
    \\ rw [] \\ fs [word_cmp_res_def] \\ rw []
    \\ fs [good_dimindex_def] \\ rw [dimword_def])
  THEN1 (* do_eq Word64 *)
   (rw [] \\ fs [vb_size_def,vs_depth_def]
    \\ once_rewrite_tac [word_eq_def]
    \\ IF_CASES_TAC
    THEN1 (rveq
           \\ drule memory_rel_pointer_eq
           \\ fs [do_eq_def])
    \\ drule memory_rel_Word64_IMP \\ fs []
    \\ imp_res_tac memory_rel_tail
    \\ drule memory_rel_Word64_IMP \\ fs []
    \\ pop_assum kall_tac
    \\ rpt strip_tac \\ fs [get_addr_0,GSYM word_bit]
    \\ fs [word_header_def]
    \\ reverse (Cases_on `dimindex (:α) < 64`) \\ fs []
    \\ fs [good_dimindex_def] \\ rfs []
    \\ once_rewrite_tac [word_cmp_loop_def]
    \\ once_rewrite_tac [word_cmp_loop_def]
    \\ once_rewrite_tac [word_cmp_loop_def]
    \\ fs [] THEN1
     (rw [] \\ fs [] \\ fs [dimword_def]
      \\ ntac 2 (pop_assum mp_tac)
      \\ srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [])
    \\ fs [dimword_def]
    \\ fs [WORD_MUL_LSL] THEN1
     (rw [] \\ fs [] \\ fs [dimword_def]
      \\ ntac 4 (pop_assum mp_tac)
      \\ srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] []))
  THEN1 (* do_eq RefPtr bl *)
   (rpt strip_tac
    \\ gvs [CaseEq"bool"] \\ drule memory_rel_RefPtr_EQ \\ fs []
    \\ strip_tac
    \\ once_rewrite_tac [word_eq_def]
    \\ IF_CASES_TAC \\ fs []
    >- gvs[AllCaseEqs()]
    \\ drule memory_rel_RefPtr_IMP \\ fs []
    \\ drule memory_rel_tail \\ strip_tac
    \\ drule memory_rel_RefPtr_IMP \\ fs []
    \\ rpt strip_tac \\ fs [word_bit,word_header_def]
    \\ IF_CASES_TAC \\ fs []
    >- (
      gvs[AllCaseEqs()]
      \\ drule (GEN_ALL memory_rel_ByteArray_IMP)
      \\ qhdtm_x_assum`memory_rel`kall_tac
      \\ drule (GEN_ALL memory_rel_ByteArray_IMP)
      \\ simp[] \\ strip_tac \\ fs[]
      \\ simp[] \\ strip_tac \\ fs[]
      \\ clean_tac \\ strip_tac \\  fs[])
    \\ IF_CASES_TAC \\ fs [] \\ fs []
    >- (
      gvs[AllCaseEqs()]
      \\ drule (GEN_ALL memory_rel_ByteArray_IMP)
      \\ qhdtm_x_assum`memory_rel`kall_tac
      \\ drule (GEN_ALL memory_rel_ByteArray_IMP)
      \\ simp[] \\ strip_tac \\ fs[]
      \\ simp[] \\ strip_tac \\ fs[]
      \\ clean_tac \\ strip_tac \\  fs[] )
    \\ IF_CASES_TAC \\ fs [] \\ fs []
    >- (
      every_case_tac \\  fs[]
      \\ drule (GEN_ALL memory_rel_ByteArray_IMP)
      \\ qhdtm_x_assum`memory_rel`kall_tac
      \\ drule (GEN_ALL memory_rel_ByteArray_IMP)
      \\ simp[] \\ strip_tac \\ fs[]
      \\ simp[] \\ strip_tac \\ fs[]
      \\ clean_tac \\ strip_tac \\  fs[] )
    \\ clean_tac \\ fs[]
    \\ fs[vb_size_def,vs_depth_def]
    \\ imp_res_tac memory_rel_RefPtr_IMP_lemma \\ fs[]
    \\ `∃bs1 bs2.
          lookup n1 refs = SOME (ByteArray T bs1) ∧
          lookup n2 refs = SOME (ByteArray T bs2)`
    by (
      every_case_tac \\ fs[]
      \\ drule (GEN_ALL memory_rel_ValueArray_IMP) \\ fs[]
      \\ drule (GEN_ALL memory_rel_ByteArray_IMP) \\ fs[]
      \\ qhdtm_x_assum`memory_rel`kall_tac
      \\ drule (GEN_ALL memory_rel_ValueArray_IMP) \\ fs[]
      \\ drule (GEN_ALL memory_rel_ByteArray_IMP) \\ fs[]
      \\ strip_tac \\ fs[])
    \\ fs[] \\ clean_tac \\ fs[] \\ clean_tac
    \\ rpt_drule memory_rel_ByteArray_words_IMP
    \\ qhdtm_x_assum`memory_rel`kall_tac
    \\ rpt_drule memory_rel_ByteArray_words_IMP
    \\ ntac 2 strip_tac
    \\ qmatch_asmsub_abbrev_tac`MAP Word xs2`
    \\ qpat_x_assum`_ (fun2set _)`mp_tac
    \\ qmatch_asmsub_abbrev_tac`MAP Word xs1`
    \\ strip_tac
    \\ `LENGTH xs1 = LENGTH xs2` by ( unabbrev_all_tac \\ simp[] )
    \\ `LENGTH xs1 < dimword(:'a)` by fs[Abbr`xs1`,Abbr`xs2`]
    \\ drule word_cmp_loop_thm \\ simp[]
    \\ disch_then drule
    \\ disch_then drule
    \\ simp[Abbr`xs2`]
    \\ qpat_x_assum `w2n (decode_length c x) = _` (assume_tac o GSYM) \\ fs []
    \\ qpat_x_assum `w2n (decode_length c x) = _` (assume_tac o GSYM) \\ fs []
    \\ disch_then kall_tac
    \\ simp[Abbr`xs1`]
    \\ simp[mw_cmp_thm,mw2n_inj]
    \\ Cases_on`w2n (decode_length c x) = 0`
    >- ( fs[LENGTH_NIL] )
    \\ `LENGTH bs1 = LENGTH bs2`
    by (
      imp_res_tac memory_rel_tail
      \\ imp_res_tac memory_rel_ByteArray_IMP
      \\ fs[] \\ clean_tac \\ fs[]
      \\ clean_tac \\ fs[]
      \\ clean_tac \\ fs[]
      \\ fs[good_dimindex_def] \\ rfs[dimword_def] \\ rfs[] \\ fs[] )
    \\ drule write_bytes_inj
    \\ disch_then drule
    \\ qpat_abbrev_tac `ws = REPLICATE _ 0w`
    \\ disch_then (qspec_then `ws` mp_tac)
    \\ impl_tac THEN1
     (fs [Abbr `ws`] \\ rfs []
      \\ fs[good_dimindex_def,dimword_def] \\ rfs []
      \\ qpat_x_assum `_ = w2n _` (assume_tac o GSYM) \\ fs []
      \\ fs [LEFT_ADD_DISTRIB]
      THEN1
       (`0 < 4n` by fs [] \\ drule DIVISION
        \\ disch_then (fn th => simp [Once th])
        \\ match_mp_tac (DECIDE ``n < m ==> n <= m:num``)
        \\ match_mp_tac MOD_LESS \\ fs [])
      THEN1
       (`0 < 8n` by fs [] \\ drule DIVISION
        \\ disch_then (fn th => simp [Once th])
        \\ match_mp_tac (DECIDE ``n < m ==> n <= m:num``)
        \\ match_mp_tac MOD_LESS \\ fs []))
    \\ fs [] \\ rw[] \\ rw[]
    \\ fs[good_dimindex_def,dimword_def])
  THEN1 (* do_eq Blocks *)
   (rpt gen_tac \\ strip_tac \\ rpt gen_tac
    \\ IF_CASES_TAC THEN1
     (reverse IF_CASES_TAC THEN1 fs []
      \\ pop_assum mp_tac \\ pop_assum kall_tac
      \\ strip_tac \\ fs []
      \\ once_rewrite_tac [word_eq_def]
      \\ IF_CASES_TAC \\ fs []
      \\ `v1 <> [] /\ v2 <> []` by fs [isClos_def]
      \\ strip_tac
      \\ drule memory_rel_Block_IMP \\ fs [word_bit]
      \\ imp_res_tac memory_rel_tail
      \\ drule memory_rel_Block_IMP \\ fs [word_bit]
      \\ rpt strip_tac \\ fs [word_header_def]
      \\ qpat_x_assum `memory_rel c be ts refs sp st m dm _` kall_tac
      \\ rpt_drule memory_rel_isClos \\ fs [])
    \\ fs [] \\ strip_tac
    \\ once_rewrite_tac [word_eq_def]
    \\ IF_CASES_TAC \\ fs []
    THEN1 (drule memory_rel_ptr_eq \\ fs [])
    \\ IF_CASES_TAC THEN1
     (reverse (Cases_on `word_bit 0 w1`) \\ fs []
      \\ drule memory_rel_Block_Block_small_eq \\ fs []
      \\ strip_tac \\ fs []
      \\ imp_res_tac memory_rel_swap
      \\ drule memory_rel_Block_Block_small_eq \\ fs []
      \\ CCONTR_TAC \\ fs [] \\ fs [])
    \\ fs []
    \\ drule memory_rel_Block_IMP \\ fs [word_bit]
    \\ imp_res_tac memory_rel_tail
    \\ drule memory_rel_Block_IMP \\ fs [word_bit]
    \\ pop_assum kall_tac
    \\ rpt strip_tac
    \\ fs [word_header_def]
    \\ drule memory_rel_isClos \\ fs [] \\ strip_tac
    \\ IF_CASES_TAC
    THEN1 (fs [] \\ every_case_tac \\ fs [])
    \\ fs [] \\ rveq
    \\ qpat_x_assum `_ = Eq_val b` mp_tac
    \\ reverse IF_CASES_TAC THEN1
     (`c.len_size + 2 < dimindex (:α)` by
             fs [memory_rel_def,heap_in_memory_store_def]
      \\ imp_res_tac encode_header_EQ \\ rveq  \\ fs [])
    \\ fs [] \\ rveq \\ strip_tac \\ fs []
    \\ rpt_drule memory_rel_Block_explode
    \\ strip_tac
    \\ rename [‘(eq_explode _ m dm v1 ++ (Block v_v t1 v2,Word w2)::vars)’]
    \\ `memory_rel c be ts refs sp st m dm
         ((Block v_v t1 v2,Word w2)::(eq_explode (a' + bytes_in_word) m dm v1 ++
          vars))` by
     (first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
      \\ fs [] \\ rw [] \\ fs [] \\ NO_TAC)
    \\ rpt_drule memory_rel_Block_explode
    \\ strip_tac
    \\ `memory_rel c be ts refs sp st m dm
         (eq_explode (a' + bytes_in_word) m dm v1 ++
          eq_explode (a + bytes_in_word) m dm v2 ++ vars)` by
     (first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
      \\ fs [] \\ rw [] \\ fs [] \\ NO_TAC)
    \\ first_x_assum drule \\ fs []
    \\ disch_then (qspec_then `l-1` mp_tac)
    \\ impl_tac THEN1
     (fs [LEFT_ADD_DISTRIB,vb_size_def,vs_depth_def]
      \\ qpat_x_assum `_ < l` mp_tac
      \\ CONV_TAC (DEPTH_CONV ETA_CONV)
      \\ Cases_on `l` \\ fs []
      \\ `0 < dimword (:'a)` by fs []
      \\ fs [encode_header_def]
      \\ fs [good_dimindex_def,dimword_def] \\ rfs [])
    \\ strip_tac \\ fs []
    \\ rw[vs_depth_def]
    \\ fs [LEFT_ADD_DISTRIB,vb_size_def,vs_depth_def]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ fs [good_dimindex_def,dimword_def] \\ rfs []
   )
  THEN1 (* do_eq_list nil case *)
   (once_rewrite_tac [word_eq_def] \\ fs [])
  (* do_eq_list cons case *)
  \\ rpt gen_tac \\ strip_tac \\ rpt gen_tac
  \\ fs [eq_assum_def,eq_explode_def]
  \\ strip_tac
  \\ once_rewrite_tac [word_eq_def]
  \\ fs [ADD1,word_add_n2w]
  \\ Cases_on `do_eq refs v1 v2` \\ fs []
  \\ `?c1. m w1 = Word c1` by
   (Cases_on `m w1` \\ fs [] \\ imp_res_tac memory_rel_Loc
    \\ rveq \\ fs [do_eq_def])
  \\ `?c2. m w2 = Word c2` by
   (`memory_rel c be ts refs sp st m dm [(v2,m w2)]` by
     (first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
      \\ fs [] \\ rw [] \\ fs [] \\ NO_TAC)
    \\ Cases_on `m w2` \\ fs [] \\ imp_res_tac memory_rel_Loc
    \\ rveq \\ Cases_on `v1` \\ fs [do_eq_def])
  \\ `memory_rel c be ts refs sp st m dm ((v1,Word c1)::(v2,Word c2)::vars)` by
   (first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [] \\ rw [] \\ fs [] \\ NO_TAC)
  \\ first_x_assum drule
  \\ disch_then (qspec_then `l-1` mp_tac)
  \\ impl_tac THEN1 fs [LEFT_ADD_DISTRIB]
  \\ strip_tac \\ fs []
  \\ simp[vs_depth_def]
  \\ simp[MIN_SUB,MAX_SUB]
  \\ drule_then (qspecl_then [`vs_depth_list v1' - 1`,`vs_depth_list v2' - 1`] strip_assume_tac)
                (CONJUNCT1 word_eq_min_max_clock)
  \\ fs[]
  \\ IF_CASES_TAC \\ fs []
  THEN1 (fs [LEFT_ADD_DISTRIB])
  \\ fs [GSYM word_add_n2w]
  \\ qpat_x_assum `memory_rel c be ts refs sp st m dm _` kall_tac
  \\ `memory_rel c be ts refs sp st m dm
                (eq_explode (w1 + bytes_in_word) m dm v1' ++
                 eq_explode (w2 + bytes_in_word) m dm v2' ++ vars)` by
       (first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
        \\ fs [] \\ rw [] \\ fs [] \\ NO_TAC)
  \\ first_x_assum drule \\ fs []
  \\ disch_then (qspec_then `l1-1` mp_tac)
  \\ impl_tac THEN1 fs [LEFT_ADD_DISTRIB]
  \\ strip_tac
  \\ drule_then(qspecl_then [`vs_depth v1 + 1`,`vs_depth v2 + 1`] strip_assume_tac)
               (CONJUNCT2 word_eq_min_max_clock)
  \\ PURE_ONCE_REWRITE_TAC[MAX_COMM]
  \\ fs[ETA_THM]
  \\ fs[LEFT_ADD_DISTRIB]
QED

Theorem word_eq_thm:
   memory_rel c be ts refs sp st m dm
      ((v1,Word w1)::(v2,Word w2:'a word_loc)::vars) /\
    do_eq refs v1 v2 = Eq_val b /\ good_dimindex (:'a) ==>
    ?res l1 ck1.
       word_eq c st dm m (MustTerminate_limit (:'a) - 1)
         (MIN (vs_depth v1) (vs_depth v2)) w1 w2 = SOME (res,l1,ck1) /\
       (b <=> (res = 1w))
Proof
  rw [] \\ imp_res_tac memory_rel_limit
  \\ drule (word_eq_thm0 |> CONJUNCT1)
  \\ fs []
  \\ `dimword(:'a) * vb_size v1 < MustTerminate_limit (:α) − 1`
           by (fs [good_dimindex_def,dimword_def] \\ rfs [])
  \\ rw [] \\ fs []
  \\ res_tac
  \\ goal_assum drule \\ fs[]
QED

Definition word_mem_eq_def:
  (word_mem_eq a [] dm m <=> SOME T) /\
  (word_mem_eq a (x::xs) dm m <=>
     if ~(a IN dm) then NONE else
     if ~isWord (m a) then NONE else
     if m a <> Word x then SOME F else
       word_mem_eq (a + bytes_in_word) xs dm m)
End

val word_mem_eq_thm = prove(
  ``!xs ys a ff.
     (word_list a (MAP Word xs) * ff) (fun2set (m,dm)) /\
     LENGTH xs = LENGTH ys ==>
     word_mem_eq a ys dm m = SOME (xs = ys)``,
  Induct \\ Cases_on `ys` \\ fs [word_mem_eq_def]
  \\ fs [word_list_def] \\ rpt strip_tac
  \\ SEP_R_TAC \\ fs [isWord_def]
  \\ IF_CASES_TAC \\ fs [] \\ rveq
  \\ first_x_assum match_mp_tac
  \\ qexists_tac `one (a,Word h) * ff`
  \\ fs [AC STAR_COMM STAR_ASSOC]);

Definition bignum_words_def:
  bignum_words c i =
    let (sign,payload) = i2mw i in
      case encode_header c (if sign then 7 else 3) (LENGTH payload) of
      | NONE => NONE
      | SOME h => SOME (h :: payload)
End

Theorem memory_rel_Number_const_test:
   memory_rel c be ts refs sp st m dm ((Number i,Word (w:'a word))::vars) /\
    good_dimindex (:'a) ==>
    if small_int (:'a) j then
      (Smallnum j = w <=> i = j)
    else
      case bignum_words c j of
      | NONE => i <> j
      | SOME words =>
        if ~(word_bit 0 w) then i <> j else
          ?a. get_real_addr c st w = SOME a /\
              word_mem_eq a words dm m = SOME (i = j)
Proof
  strip_tac
  \\ rpt_drule (memory_rel_any_Number_IMP |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ fs [word_bit] \\ strip_tac
  \\ IF_CASES_TAC THEN1
   (rpt_drule (IMP_memory_rel_Number
          |> REWRITE_RULE [CONJ_ASSOC] |> ONCE_REWRITE_RULE [CONJ_COMM])
    \\ strip_tac
    \\ rpt_drule memory_rel_Number_EQ \\ fs []
    \\ Cases_on `i = j` \\ fs [])
  \\ Cases_on `small_int (:α) i` \\ fs []
  THEN1 (every_case_tac \\ fs [] \\ CCONTR_TAC \\ fs [])
  \\ fs [bignum_words_def,i2mw_def]
  \\ rpt_drule memory_rel_Number_bignum_header
  \\ strip_tac \\ fs []
  \\ `(w2n (b2w (i < 0) ≪ 2 || 3w:'a word)) = if i < 0 then 7 else 3` by
   (Cases_on `i < 0i` \\ fs [] \\ EVAL_TAC
    \\ fs [good_dimindex_def,dimword_def] \\ NO_TAC)
  \\ fs []
  \\ qmatch_goalsub_abbrev_tac`encode_header c sj lj`
  \\ Cases_on `encode_header c sj lj` \\ fs []
  THEN1 (CCONTR_TAC \\ fs [])
  \\ pop_assum mp_tac
  \\ qmatch_asmsub_abbrev_tac `encode_header c si li`
  \\ Cases_on `encode_header c si li` \\ fs []
  \\ `m a = Word x'` by (fs [encode_header_def] \\ rw [])
  \\ qpat_x_assum `m a = Word (make_header _ _ _)` kall_tac
  \\ rw []
  \\ fs [word_mem_eq_def]
  \\ rpt_drule memory_rel_Number_bignum_IMP_ALT
  \\ strip_tac \\ fs [isWord_def]
  \\ IF_CASES_TAC
  THEN1 (fs [] \\ CCONTR_TAC \\ fs [] \\ unabbrev_all_tac \\ fs [])
  \\ unabbrev_all_tac
  \\ drule (encode_header_EQ |> GEN_ALL)
  \\ qpat_x_assum `encode_header c _ _ = _` kall_tac
  \\ disch_then drule
  \\ impl_tac THEN1 fs [memory_rel_def,heap_in_memory_store_def]
  \\ fs [] \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ strip_tac
  \\ `j < 0 <=> i < 0i` by
        (Cases_on `j < 0` \\ Cases_on `i < 0` \\ fs [] \\ NO_TAC)
  \\ rpt_drule word_mem_eq_thm
  \\ fs [n2mw_11] \\ strip_tac
  \\ Cases_on `i` \\ Cases_on `j` \\ fs []
  \\ pop_assum mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ intLib.COOPER_TAC
QED

Theorem memory_rel_Word64_const_test:
  memory_rel c be ts refs sp st m dm ((Word64 i,v)::vars) /\
  good_dimindex (:'a) ==>
    ∃(w:'a word) a words h.
      v = Word w ∧ get_real_addr c st w = SOME a ∧
      word_mem_eq (a + bytes_in_word) words dm m = SOME (i = j) ∧
      encode_header c 3 (LENGTH words) = SOME (h:'a word) ∧
      if dimindex (:'a) < 64 then
        words = [(63 >< 32) j; (31 >< 0) j]
      else
        words = [(63 >< 0) j]
Proof
  strip_tac
  \\ rpt_drule (memory_rel_Word64_IMP |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ fs [word_bit] \\ strip_tac \\ gvs []
  \\ CASE_TAC \\ gvs []
  \\ fs [word_mem_eq_def,isWord_def]
  \\ simp [GSYM PULL_EXISTS]
  \\ (reverse conj_tac THEN1
   (gvs [memory_rel_def,word_ml_inv_def,abs_ml_inv_def,
         bc_stack_ref_inv_def,v_inv_def]
    \\ imp_res_tac heap_lookup_SPLIT
    \\ gvs [heap_in_memory_store_def,word_heap_APPEND,Word64Rep_def,
            word_heap_def,word_el_def,word_payload_def]
    \\ qpat_abbrev_tac ‘pp = encode_header _ _ _’
    \\ Cases_on ‘pp’ \\ fs [SEP_CLAUSES] \\ fs [SEP_F_def]))
  \\ gvs [encode_header_def,WORD_MUL_LSL,isWord_def]
  \\ simp [AllCaseEqs()]
  \\ gvs [good_dimindex_def]
  \\ Cases_on ‘i’ \\ Cases_on ‘j’ \\ fs []
  \\ fs [wordsTheory.word_extract_n2w]
  \\ gvs [bitTheory.BITS_THM,dimword_def]
  \\ ‘n DIV 4294967296 < 4294967296’ by fs [DIV_LT_X]
  \\ ‘n' DIV 4294967296 < 4294967296’ by fs [DIV_LT_X]
  \\ fs []
  \\ ‘0 < 4294967296n’ by fs []
  \\ drule DIVISION
  \\ disch_then (fn th =>
        strip_assume_tac (Q.SPEC ‘n’ th) \\ strip_assume_tac (Q.SPEC ‘n'’ th))
  \\ Cases_on ‘n = n'’ \\ fs []
QED

Triviality or_seven_eq:
  (w << k) ≠ (v << k) ∧ 2 < k ⇒
  ((w << k) || 7w) ≠ ((v << k) || 7w)
Proof
  fs [fcpTheory.CART_EQ] \\ rw []
  \\ qexists_tac ‘i’
  \\ gvs [word_lsl_def,word_or_def,fcpTheory.FCP_BETA]
  \\ Cases_on ‘k ≤ i’ \\ fs []
  \\ fs [word_index]
QED

Theorem make_byte_header_eq:
  byte_len (:α) m < 2 ** c.len_size ∧
  byte_len (:α) m < 2 ** (dimindex (:α) − 4) ∧
  byte_len (:α) n < 2 ** c.len_size ∧
  byte_len (:α) n < 2 ** (dimindex (:α) − 4) ∧
  good_dimindex (:'a) ∧
  2 < dimindex (:'a) - (if dimindex (:'a) = 32 then 2 else 3) − c.len_size ⇒
  (make_byte_header c T m = make_byte_header c T n:'a word ⇔ m = n)
Proof
  strip_tac \\ Cases_on ‘m = n’ \\ fs [make_byte_header_def]
  \\ rw [] \\ gvs [good_dimindex_def]
  \\ irule_at Any or_seven_eq \\ fs []
  \\ fs [WORD_MUL_LSL,word_mul_n2w]
  \\ fs [dimword_def]
  \\ fs [byte_len_def]
  \\ fs [ADD_DIV_EQ]
  \\ fs [DIV_LT_X]
  THEN1
   (‘(m + 4) * 2 ** (30 − c.len_size) < 2 ** ((c.len_size + 2) + (30 − c.len_size))’ by
      (simp [Once EXP_ADD] \\ fs [EXP_ADD])
    \\ ‘(n + 4) * 2 ** (30 − c.len_size) < 2 ** ((c.len_size + 2) + (30 − c.len_size))’ by
      (simp [Once EXP_ADD] \\ fs [EXP_ADD])
    \\ ‘((c.len_size + 2) + (30 − c.len_size)) = dimindex (:'a)’ by fs []
    \\ qpat_x_assum ‘dimindex (:α) = _’ assume_tac \\ fs [])
  THEN1
   (‘(m + 8) * 2 ** (61 − c.len_size) < 2 ** ((c.len_size + 3) + (61 − c.len_size))’ by
      (simp [Once EXP_ADD] \\ fs [EXP_ADD])
    \\ ‘(n + 8) * 2 ** (61 − c.len_size) < 2 ** ((c.len_size + 3) + (61 − c.len_size))’ by
      (simp [Once EXP_ADD] \\ fs [EXP_ADD])
    \\ ‘((c.len_size + 3) + (61 − c.len_size)) = dimindex (:'a)’ by fs []
    \\ qpat_x_assum ‘dimindex (:α) = _’ assume_tac \\ fs [])
QED

Theorem memory_rel_String_const_test:
  memory_rel c be ts refs sp st m dm ((RefPtr bl i,v)::vars) /\
  lookup i refs = SOME (ByteArray T other) /\
  good_dimindex (:'a) ==>
  let t = implode (MAP (CHR o w2n) other) in
    (part_to_words c LN (Str s) (0w:'a word) = NONE ⇒ s ≠ t) ∧
    ∀x res.
      part_to_words c LN (Str s) 0w = SOME (x,res) ⇒
      ∃(w:'a word) a.
        v = Word w ∧ get_real_addr c st w = SOME a ∧
        word_mem_eq a (MAP (get_Word o SND) res) dm m = SOME (s = t)
Proof
  strip_tac
  \\ drule_all memory_rel_ByteArray_IMP
  \\ strip_tac
  \\ Cases_on ‘part_to_words c LN (Str s) 0w’ \\ fs []
  THEN1
   (strip_tac \\ gvs [] \\ pop_assum mp_tac
    \\ simp [part_to_words_def]
    \\ gvs [good_dimindex_def,byte_len_def]
    \\ fs [DECIDE “k ≠ 0 ⇒ (n + 1 < k ⇔ n < k - 1:num)”]
    \\ gvs [DIV_LT_X,make_byte_header_def]
    \\ gvs [memory_rel_def,word_ml_inv_def,abs_ml_inv_def,
         bc_stack_ref_inv_def,v_inv_def]
    \\ ‘reachable_refs (RefPtr bl i::MAP FST vars) refs i’ by
       (fs [reachable_refs_def]
        \\ qexists_tac ‘RefPtr bl i’ \\ fs [get_refs_def])
    \\ first_x_assum drule
    \\ simp[bc_ref_inv_def]
    \\ Cases_on ‘FLOOKUP f i’ \\ fs [Bytes_def]
    \\ strip_tac
    \\ imp_res_tac heap_lookup_SPLIT
    \\ gvs [heap_in_memory_store_def,word_heap_APPEND,
            word_heap_def,word_el_def,word_payload_def]
    \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
    \\ qpat_x_assum ‘LENGTH other + _ < 2 ** (c.len_size + _)’ assume_tac
    \\ fs [EXP_ADD])
  \\ rw [] \\ gvs [part_to_words_def]
  \\ fs [word_mem_eq_def,isWord_def]
  \\ ‘make_byte_header c T (LENGTH other) = make_byte_header c T (strlen s) ⇔
      (LENGTH other) = (strlen s)’ by
   (irule make_byte_header_eq \\ fs [] \\ fs [byte_len_def]
    \\ gvs [good_dimindex_def]
    \\ fs [ADD_DIV_EQ]
    \\ fs [DIV_LT_X]
    \\ gvs [memory_rel_def,word_ml_inv_def,abs_ml_inv_def,
         bc_stack_ref_inv_def,v_inv_def]
    \\ ‘reachable_refs (RefPtr bl i::MAP FST vars) refs i’ by
       (fs [reachable_refs_def]
        \\ qexists_tac ‘RefPtr bl i’ \\ fs [get_refs_def])
    \\ first_x_assum drule
    \\ simp[bc_ref_inv_def]
    \\ Cases_on ‘FLOOKUP f i’ \\ fs [Bytes_def]
    \\ strip_tac
    \\ imp_res_tac heap_lookup_SPLIT
    \\ gvs [heap_in_memory_store_def,word_heap_APPEND,
            word_heap_def,word_el_def,word_payload_def]
    \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
    \\ qpat_x_assum ‘LENGTH other + _ < 2 ** (c.len_size + _)’ assume_tac
    \\ fs [EXP_ADD])
  \\ asm_rewrite_tac []
  \\ IF_CASES_TAC \\ fs []
  THEN1 (CCONTR_TAC \\ fs [] \\ qpat_x_assum ‘_ ≠ strlen _’ mp_tac \\ fs [])
  \\ gvs [memory_rel_def,word_ml_inv_def,abs_ml_inv_def,
          bc_stack_ref_inv_def,v_inv_def]
  \\ ‘reachable_refs (RefPtr bl i::MAP FST vars) refs i’ by
    (fs [reachable_refs_def]
     \\ qexists_tac ‘RefPtr bl i’ \\ fs [get_refs_def])
  \\ first_x_assum drule
  \\ simp[bc_ref_inv_def]
  \\ Cases_on ‘FLOOKUP f i’ \\ fs [Bytes_def]
  \\ strip_tac
  \\ imp_res_tac heap_lookup_SPLIT
  \\ gvs [heap_in_memory_store_def,word_heap_APPEND,
          word_heap_def,word_el_def,word_payload_def,word_list_def]
  \\ qpat_x_assum ‘_ (fun2set (m,dm))’ mp_tac
  \\ fs [MAP_MAP_o,o_DEF]
  \\ qpat_abbrev_tac ‘aaa = word_list _ (MAP Word _)’
  \\ fs [AC STAR_COMM STAR_ASSOC]
  \\ rename [‘(_ * ff) (fun2set _)’]
  \\ fs [Abbr‘aaa’]
  \\ gvs [be_ok_def]
  \\ qmatch_goalsub_abbrev_tac
         ‘word_list a1 (MAP Word (write_bytes bs1 (REPLICATE n1 _) _))’
  \\ qmatch_goalsub_abbrev_tac
         ‘word_mem_eq a2 (write_bytes bs2 (REPLICATE n2 _) _)’
  \\ ‘n1 = n2’ by (unabbrev_all_tac \\ fs [byte_len_def] \\ fs [good_dimindex_def])
  \\ var_eq_tac
  \\ ‘a1 = a2’ by
   (unabbrev_all_tac
    \\ drule_all get_real_addr_get_addr
    \\ fs [word_addr_def] \\ gvs []
    \\ disch_then (qspec_then ‘(Word 0w)’ mp_tac)
    \\ gvs [FLOOKUP_DEF])
  \\ var_eq_tac
  \\ strip_tac
  \\ drule_then (qspec_then ‘write_bytes bs2 (REPLICATE n1 0w) c.be’ mp_tac) word_mem_eq_thm
  \\ impl_tac THEN1 fs [LENGTH_write_bytes]
  \\ strip_tac \\ fs []
  \\ irule EQ_TRANS
  \\ irule_at Any write_bytes_inj
  \\ fs [] \\ unabbrev_all_tac
  \\ Cases_on ‘s’ \\ fs [mlstringTheory.explode_def,mlstringTheory.implode_def]
  \\ (conj_tac THEN1
   (fs [good_dimindex_def] \\ rename [‘STRLEN sss’]
    \\ ‘0 < if dimindex(:'a) = 32 then 4 else 8n’ by rw []
    \\ drule_then (qspec_then ‘STRLEN sss’ strip_assume_tac) DIVISION
    \\ rfs [LEFT_ADD_DISTRIB,Excl"MOD_LESS"]))
  \\ eq_tac \\ rw []
  \\ fs [MAP_MAP_o,o_DEF]
QED

val word_1_and_eq_0 = prove(
  ``((1w && w) = 0w) <=> ~(word_bit 0 w)``,
  fs [word_bit_test]);

Theorem memory_rel_Number_single_mul:
   memory_rel c be ts refs sp st m dm
      ((Number i1,Word (w1:'a word))::(Number i2,Word w2)::vars) /\
    good_dimindex(:'a) ==>
      let (lw,hw) = single_mul w1 (w2 >>> 1) 0w in
        (hw || ((w1 || w2) && 1w)) = 0w ==>
        memory_rel c be ts refs sp st m dm ((Number (i1 * i2),Word (lw >>> 1))::vars)
Proof
  Cases_on `i2 = 0` \\ fs []
  \\ rpt strip_tac \\ fs [word_or_eq_0,word_bit_or]
  THEN1
   (drule memory_rel_swap \\ strip_tac
    \\ rpt_drule memory_rel_Number_const_test
    \\ disch_then (qspec_then `0` mp_tac)
    \\ `small_int (:α) 0` by
     (fs [good_dimindex_def,dimword_def,small_int_def])
    \\ fs [Smallnum_def] \\ strip_tac \\ rveq
    \\ fs [multiwordTheory.single_mul_def]
    \\ strip_tac \\ first_x_assum (fn th => mp_tac th THEN
         match_mp_tac memory_rel_rearrange) \\ fs [] \\ rw [] \\ fs [])
  \\ Cases_on `i1 = 0` \\ fs []
  \\ rpt strip_tac \\ fs [word_or_eq_0,word_bit_or]
  THEN1
   (rpt_drule memory_rel_Number_const_test
    \\ disch_then (qspec_then `0` mp_tac)
    \\ `small_int (:α) 0` by
     (fs [good_dimindex_def,dimword_def,small_int_def])
    \\ fs [Smallnum_def] \\ strip_tac \\ rveq
    \\ fs [multiwordTheory.single_mul_def]
    \\ strip_tac \\ first_x_assum (fn th => mp_tac th THEN
         match_mp_tac memory_rel_rearrange) \\ fs [] \\ rw [] \\ fs [])
  \\ pairarg_tac \\ fs []
  \\ rpt_drule memory_rel_any_Number_IMP \\ strip_tac
  \\ drule memory_rel_tl \\ strip_tac
  \\ rpt_drule memory_rel_any_Number_IMP \\ strip_tac
  \\ reverse (Cases_on `small_int (:'a) i1`) \\ fs [word_1_and_eq_0]
  THEN1 (fs [word_bit_or] \\fs [word_bit_def])
  \\ reverse (Cases_on `small_int (:'a) i2`) \\ fs [word_1_and_eq_0]
  THEN1 (fs [word_bit_or] \\fs [word_bit_def])
  \\ strip_tac \\ rveq \\ fs []
  \\ rpt_drule memory_rel_Number_IMP
  \\ qpat_x_assum `memory_rel c be ts refs sp st m dm _` kall_tac
  \\ qpat_x_assum `small_int (:α) i2` mp_tac
  \\ rpt_drule memory_rel_Number_IMP
  \\ rw [] \\ fs []
  \\ fs [multiwordTheory.single_mul_def]
  \\ `w2n ((Smallnum i1):'a word) * w2n ((Smallnum i2 ⋙ 1):'a word)
      DIV dimword (:α) < dimword (:'a)` by
   (simp_tac std_ss [DIV_LT_X,ZERO_LT_dimword]
    \\ match_mp_tac bitTheory.LESS_MULT_MONO2 \\ fs [w2n_lt] \\ NO_TAC)
  \\ fs [] \\ fs [DIV_EQ_X] \\ rveq
  \\ `4 <= w2n ((Smallnum i1):'a word)` by
   (Cases_on `i1` \\ fs [small_int_def,Smallnum_def,word_2comp_n2w]
    \\ `(4 * n) < dimword (:α)` by
      (rfs [good_dimindex_def,dimword_def,small_int_def] \\ rfs [] \\ NO_TAC)
    \\ fs []
    \\ rfs [good_dimindex_def,dimword_def,small_int_def] \\ rfs [])
  \\ `4 <= w2n ((Smallnum i2):'a word)` by
   (Cases_on `i2` \\ fs [small_int_def,Smallnum_def,word_2comp_n2w]
    \\ `(4 * n) < dimword (:α)` by
      (rfs [good_dimindex_def,dimword_def,small_int_def] \\ rfs [] \\ NO_TAC)
    \\ fs []
    \\ rfs [good_dimindex_def,dimword_def,small_int_def] \\ rfs [])
  \\ `2 <= w2n ((Smallnum i2 >>> 1):'a word)` by fs [w2n_lsr,X_LE_DIV]
  \\ reverse (Cases_on `i2`) \\ fs [Smallnum_def]
  \\ fs [GSYM Smallnum_def |> SIMP_RULE (srw_ss()) []]
  THEN1
   (fs [DIV_LT_X]
    \\ `dimword (:'a) DIV 4 <= w2n ((-n2w (4 * n) ⋙ 1):'a word)` by
     (fs [w2n_lsr,word_2comp_n2w] \\ fs [X_LE_DIV]
      \\ `(4 * n) < dimword (:α)` by
        (rfs [good_dimindex_def,dimword_def,small_int_def] \\ rfs [] \\ NO_TAC)
      \\ fs [] \\ rfs [good_dimindex_def,dimword_def,small_int_def] \\ rfs [])
    \\ sg `F` \\ fs []
    \\ qpat_x_assum `_ < dimword (:α)` mp_tac \\ fs [NOT_LESS]
    \\ match_mp_tac LESS_EQ_TRANS
    \\ qexists_tac `4 * (dimword (:α) DIV 4)`
    \\ conj_tac THEN1 fs [good_dimindex_def,dimword_def]
    \\ match_mp_tac LESS_MONO_MULT2 \\ fs [])
  \\ reverse (Cases_on `i1`) \\ fs [Smallnum_def]
  THEN1
   (fs [DIV_LT_X]
    \\ `dimword (:'a) DIV 2 <= w2n ((-n2w (4 * n')):'a word)` by
     (fs [w2n_lsr,word_2comp_n2w] \\ fs [X_LE_DIV]
      \\ `(4 * n') < dimword (:α)` by
        (rfs [good_dimindex_def,dimword_def,small_int_def] \\ rfs [] \\ NO_TAC)
      \\ fs [] \\ rfs [good_dimindex_def,dimword_def,small_int_def] \\ rfs [])
    \\ sg `F` \\ fs []
    \\ qpat_x_assum `_ < dimword (:α)` mp_tac \\ fs [NOT_LESS]
    \\ match_mp_tac LESS_EQ_TRANS
    \\ qexists_tac `(dimword (:α) DIV 2) * 2`
    \\ conj_tac THEN1 fs [good_dimindex_def,dimword_def]
    \\ match_mp_tac LESS_MONO_MULT2 \\ fs [])
  \\ `(2 * n) < dimword (:'a) /\ (4 * n') < dimword (:α) /\
      (4 * n) < dimword (:α)` by
    (rfs [good_dimindex_def,dimword_def,small_int_def] \\ rfs [] \\ NO_TAC)
  \\ `n2w (4 * n) ⋙ 1 = n2w (2 * n):'a word` by
       (rewrite_tac [GSYM w2n_11,w2n_lsr] \\ fs [] \\ fs [DIV_EQ_X])
  \\ fs [] \\ fs [word_mul_n2w]
  \\ `n2w (8 * (n * n')) >>> 1 = n2w (n * n') << 2` by
       (rewrite_tac [GSYM w2n_11,w2n_lsr,WORD_MUL_LSL,word_mul_n2w]
        \\ fs [] \\ fs [DIV_EQ_X]) \\ fs []
  \\ match_mp_tac IMP_memory_rel_Number_num3
  \\ fs [] \\ rfs [good_dimindex_def,dimword_def] \\ rfs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
  \\ fs [] \\ rw [] \\ fs []
QED

Theorem memory_rel_bounds_check:
   memory_rel c be ts refs sp st m dm ((Number i1,Word (w1:'a word))::vars) /\
    small_int (:'a) (& n) /\ good_dimindex (:'a) ==>
    (word_ror w1 2 <+ n2w n <=> 0 <= i1 /\ i1 < & n) /\
    (word_ror w1 2 <=+ n2w n <=> 0 <= i1 /\ i1 <= & n)
Proof
  strip_tac \\ imp_res_tac memory_rel_any_Number_IMP
  \\ rveq \\ fs [] \\ rveq \\ fs []
  \\ `n < dimword (:'a) /\ n < dimword (:'a) DIV 4 /\ n < dimword (:'a) DIV 8` by
      (fs [small_int_def,good_dimindex_def,dimword_def] \\ fs [] \\ NO_TAC)
  \\ fs [WORD_LO,WORD_LS]
  \\ reverse (Cases_on `small_int (:α) i1`) \\ fs []
  THEN1
   (qsuff_tac `dimword (:α) DIV 4 <= w2n (w ⇄ 2)`
    THEN1 (fs [] \\ fs [small_int_def] \\ intLib.COOPER_TAC)
    \\ `(word_ror w 2) ' (dimindex (:'a) - 2)` by
      (fs [word_ror_def,fcpTheory.FCP_BETA,good_dimindex_def] \\ NO_TAC)
    \\ Cases_on `word_ror w 2` \\ fs []
    \\ fs [word_index]
    \\ fs [bitTheory.BIT_def,bitTheory.BITS_THM]
    \\ rfs [good_dimindex_def,dimword_def]
    \\ rfs [good_dimindex_def,dimword_def]
    \\ fs [good_dimindex_def,dimword_def]
    \\ rfs [good_dimindex_def,dimword_def]
    \\ CCONTR_TAC \\ fs [GSYM NOT_LESS,LESS_DIV_EQ_ZERO])
  \\ imp_res_tac memory_rel_Number_IMP
  \\ fs [] \\ rveq \\ fs []
  \\ Cases_on `i1 < 0` THEN1
   (qsuff_tac `dimword (:α) DIV 8 <= w2n ((Smallnum i1 ⇄ 2) :'a word)`
    THEN1 (fs [] \\ fs [small_int_def] \\ intLib.COOPER_TAC)
    \\ `(if dimindex (:'a) = 32
         then i1 <> - 536870912
         else i1 <> - 2305843009213693952) ==>
        ((Smallnum i1 ⇄ 2):'a word) ' (dimindex (:'a) - 3)` by
      (strip_tac
       \\ fs [word_ror_def,fcpTheory.FCP_BETA,good_dimindex_def]
       \\ fs [Smallnum_def]
       \\ assume_tac (GSYM word_msb_def) \\ rfs []
       \\ match_mp_tac (MP_CANON
           (TWO_COMP_POS |> REWRITE_RULE [METIS_PROVE [] ``b\/c <=> ~b==>c``]))
       \\ fs [dimword_def]
       \\ rfs [word_msb_n2w,bitTheory.BIT_def,bitTheory.BITS_THM2]
       \\ Cases_on `i1` \\ rfs [small_int_def,dimword_def]
       \\ fs [DIV_EQ_X]
       \\ CCONTR_TAC \\ fs [] \\ NO_TAC)
    \\ qmatch_assum_abbrev_tac `abb ==> _`
    \\ reverse (Cases_on `abb`) THEN1
     (rfs [markerTheory.Abbrev_def,good_dimindex_def,dimword_def]
      \\ rfs [Smallnum_def,word_2comp_n2w,dimword_def,word_ror_n2w])
    \\ fs []
    \\ Cases_on `word_ror ((Smallnum i1):'a word) 2` \\ fs []
    \\ fs [word_index]
    \\ fs [bitTheory.BIT_def,bitTheory.BITS_THM]
    \\ rfs [good_dimindex_def,dimword_def]
    \\ rfs [good_dimindex_def,dimword_def]
    \\ fs [good_dimindex_def,dimword_def]
    \\ rfs [good_dimindex_def,dimword_def]
    \\ CCONTR_TAC \\ fs [GSYM NOT_LESS,LESS_DIV_EQ_ZERO])
  \\ reverse (Cases_on `i1`) \\ fs []
  \\ fs [Smallnum_def,small_int_def]
  \\ fs [word_ror_n2w,bitTheory.BIT_def,bitTheory.BITS_THM2]
  \\ fs [good_dimindex_def,dimword_def] \\ rfs []
  \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
  \\ rfs []
QED

Theorem memory_rel_ByteArray_IMP_store:
   memory_rel c be ts refs sp st m dm ((RefPtr bl p,Word (w:'a word))::vars) ∧
    lookup p refs = SOME (ByteArray fl vals) ∧ good_dimindex (:α) /\
    get_real_addr c st w = SOME a /\ i < LENGTH vals ==>
    ?m1. mem_store_byte_aux m dm be (a + bytes_in_word + n2w i) b = SOME m1 /\
         memory_rel c be ts (insert p (ByteArray fl (LUPDATE b i vals)) refs) sp st m1 dm
           ((RefPtr bl p,Word (w:'a word))::vars)
Proof
  rw [] \\ rpt_drule memory_rel_ByteArray_IMP
  \\ fs [mem_load_byte_aux_def,mem_store_byte_aux_def]
  \\ rw [] \\ ntac 2 (first_x_assum drule)
  \\ TOP_CASE_TAC \\ fs [theWord_def]
QED

(* copy forward *)

Definition word_copy_fwd_def:
  word_copy_fwd be (n:'a word) a b (m:'a word -> 'a word_loc) dm =
    if dimword (:'a) <= 4 then NONE else
    if n <+ 4w then
      if n <+ 2w then
        if n = 0w then SOME m else
          OPTION_BIND (mem_load_byte_aux m dm be a)
                      (\w. mem_store_byte_aux m dm be b w)
      else
        OPTION_BIND (mem_load_byte_aux m dm be a) (\w1.
        OPTION_BIND (mem_load_byte_aux m dm be (a+1w)) (\w2.
          if n = 2w then
            OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
            OPTION_BIND (mem_store_byte_aux m dm be (b+1w) w2) (\m. SOME m))
          else
            OPTION_BIND (mem_load_byte_aux m dm be (a+2w)) (\w3.
            OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
            OPTION_BIND (mem_store_byte_aux m dm be (b+1w) w2) (\m.
            OPTION_BIND (mem_store_byte_aux m dm be (b+2w) w3) (\m. SOME m))))))
    else
      OPTION_BIND (mem_load_byte_aux m dm be a) (\w1.
      OPTION_BIND (mem_load_byte_aux m dm be (a+1w)) (\w2.
      OPTION_BIND (mem_load_byte_aux m dm be (a+2w)) (\w3.
      OPTION_BIND (mem_load_byte_aux m dm be (a+3w)) (\w4.
      OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
      OPTION_BIND (mem_store_byte_aux m dm be (b+1w) w2) (\m.
      OPTION_BIND (mem_store_byte_aux m dm be (b+2w) w3) (\m.
      OPTION_BIND (mem_store_byte_aux m dm be (b+3w) w4) (\m.
        word_copy_fwd be (n-4w) (a+4w) (b+4w) m dm))))))))
Termination
  WF_REL_TAC `measure (w2n o FST o SND)`
  \\ Cases_on `n` \\ fs [] \\ rw []
  \\ fs [WORD_LO] \\ rfs [NOT_LESS]
  \\ rewrite_tac [addressTheory.word_arith_lemma2,GSYM word_sub_def] \\ fs []
End

Definition list_copy_fwd_def:
  list_copy_fwd n xp xs yp ys =
    if xp + n <= LENGTH xs /\ yp + n <= LENGTH ys then
      if n = 0 then SOME ys else
      if n = 1 then SOME (LUPDATE (EL xp xs) yp ys) else
      if n = 2 then SOME ((LUPDATE (EL (xp+1) xs) (yp+1) o
                           LUPDATE (EL (xp+0) xs) (yp+0)) ys) else
      if n = 3 then SOME ((LUPDATE (EL (xp+2) xs) (yp+2) o
                           LUPDATE (EL (xp+1) xs) (yp+1) o
                           LUPDATE (EL (xp+0) xs) (yp+0)) ys) else
        list_copy_fwd (n-4) (xp+4) xs (yp+4)
                         ((LUPDATE (EL (xp+3) xs) (yp+3) o
                           LUPDATE (EL (xp+2) xs) (yp+2) o
                           LUPDATE (EL (xp+1) xs) (yp+1) o
                           LUPDATE (EL (xp+0) xs) (yp+0)) ys)
    else NONE
End

Definition list_copy_fwd_alias_def:
  list_copy_fwd_alias n xp yp ys =
    if xp + n <= LENGTH ys /\ yp + n <= LENGTH ys then
      if n = 0 then SOME ys else
      if n = 1 then SOME (LUPDATE (EL xp ys) yp ys) else
      if n = 2 then SOME ((LUPDATE (EL (xp+1) ys) (yp+1) o
                           LUPDATE (EL (xp+0) ys) (yp+0)) ys) else
      if n = 3 then SOME ((LUPDATE (EL (xp+2) ys) (yp+2) o
                           LUPDATE (EL (xp+1) ys) (yp+1) o
                           LUPDATE (EL (xp+0) ys) (yp+0)) ys) else
        list_copy_fwd_alias (n-4) (xp+4) (yp+4)
                         ((LUPDATE (EL (xp+3) ys) (yp+3) o
                           LUPDATE (EL (xp+2) ys) (yp+2) o
                           LUPDATE (EL (xp+1) ys) (yp+1) o
                           LUPDATE (EL (xp+0) ys) (yp+0)) ys)
    else NONE
End

Theorem word_copy_fwd_thm:
   !n xp yp ys ys1 m.
      memory_rel c be ts (insert p2 (ByteArray fl_ys ys) refs)
        sp st m dm ((RefPtr bl1 p1,v1)::(RefPtr bl2 p2,v2)::vars) /\
      lookup p1 refs = SOME (ByteArray fl_xs xs) /\
      list_copy_fwd n xp xs yp ys = SOME ys1 /\
      good_dimindex (:'a) /\ n < dimword (:'a) /\ p1 <> p2 ==>
      ?w1 (w2:'a word) a1 a2 m1.
        v1 = Word w1 /\ v2 = Word w2 /\
        get_real_addr c st w1 = SOME a1 /\
        get_real_addr c st w2 = SOME a2 /\
        word_copy_fwd be (n2w n) (a1 + bytes_in_word + n2w xp)
          (a2 + bytes_in_word + n2w yp) m dm = SOME m1 /\
        memory_rel c be ts (insert p2 (ByteArray fl_ys ys1) refs)
          sp st m1 dm ((RefPtr bl1 p1,v1)::(RefPtr bl2 p2,v2)::vars)
Proof
  completeInduct_on `n` \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ once_rewrite_tac [list_copy_fwd_def]
  \\ rpt strip_tac
  \\ `4 < dimword (:'a)` by fs [good_dimindex_def,dimword_def]
  \\ Cases_on `n=0` \\ fs []
  THEN1
   (once_rewrite_tac [word_copy_fwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert]
    \\ drule memory_rel_swap \\ strip_tac
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert])
  \\ Cases_on `n=1` \\ fs []
  THEN1
   (once_rewrite_tac [word_copy_fwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert]
    \\ drule memory_rel_swap \\ strip_tac
    \\ rpt_drule memory_rel_RefPtr_IMP \\ strip_tac \\ rveq \\ fs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp`,`EL xp xs`] mp_tac) \\ strip_tac \\ rfs []
    \\ drule memory_rel_swap \\ metis_tac [insert_insert])
  \\ Cases_on `n=2` \\ fs []
  THEN1
   (once_rewrite_tac [word_copy_fwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert,addressTheory.word_arith_lemma1]
    \\ drule memory_rel_swap \\ strip_tac
    \\ rpt_drule memory_rel_RefPtr_IMP \\ strip_tac \\ rveq \\ fs [PULL_EXISTS]
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp`,`EL xp xs`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp+1`,`EL (xp+1) xs`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ drule memory_rel_swap \\ metis_tac [insert_insert])
  \\ Cases_on `n=3` \\ fs []
  THEN1
   (once_rewrite_tac [word_copy_fwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert,addressTheory.word_arith_lemma1]
    \\ drule memory_rel_swap \\ strip_tac
    \\ rpt_drule memory_rel_RefPtr_IMP \\ strip_tac \\ rveq \\ fs [PULL_EXISTS]
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp`,`EL xp xs`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp+1`,`EL (xp+1) xs`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp+2`,`EL (xp+2) xs`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ drule memory_rel_swap \\ metis_tac [insert_insert])
  \\ once_rewrite_tac [word_copy_fwd_def] \\ fs [] \\ rw []
  \\ fs [WORD_LO,PULL_EXISTS]
  \\ rpt_drule memory_rel_ByteArray_IMP
  \\ strip_tac \\ rfs [lookup_insert,addressTheory.word_arith_lemma1]
  \\ drule memory_rel_swap \\ strip_tac
  \\ rpt_drule memory_rel_RefPtr_IMP \\ strip_tac \\ rveq \\ fs []
  \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
  \\ disch_then (qspecl_then [`yp`,`EL xp xs`] mp_tac)
  \\ strip_tac \\ rfs []
  \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
  \\ disch_then (qspecl_then [`yp+1`,`EL (xp+1) xs`] mp_tac)
  \\ strip_tac \\ rfs []
  \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
  \\ disch_then (qspecl_then [`yp+2`,`EL (xp+2) xs`] mp_tac)
  \\ strip_tac \\ rfs []
  \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
  \\ disch_then (qspecl_then [`yp+3`,`EL (xp+3) xs`] mp_tac)
  \\ strip_tac \\ rfs []
  \\ drule memory_rel_swap \\ strip_tac
  \\ rewrite_tac [GSYM word_sub_def,addressTheory.word_arith_lemma2]
  \\ fs [] \\ first_x_assum match_mp_tac
  \\ fs [] \\ metis_tac [insert_insert]
QED

Theorem word_copy_fwd_alias_thm:
   !n xp yp ys ys1 m.
      memory_rel c be ts (insert p2 (ByteArray fl_ys ys) refs)
        sp st m dm ((RefPtr bl p2,v2)::vars) /\
      list_copy_fwd_alias n xp yp ys = SOME ys1 /\
      good_dimindex (:'a) /\ n < dimword (:'a) ==>
      ?(w2:'a word) a2 m1.
        v2 = Word w2 /\
        get_real_addr c st w2 = SOME a2 /\
        word_copy_fwd be (n2w n) (a2 + bytes_in_word + n2w xp)
          (a2 + bytes_in_word + n2w yp) m dm = SOME m1 /\
        memory_rel c be ts (insert p2 (ByteArray fl_ys ys1) refs)
          sp st m1 dm ((RefPtr bl p2,v2)::vars)
Proof
  completeInduct_on `n` \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ once_rewrite_tac [list_copy_fwd_alias_def]
  \\ rpt strip_tac
  \\ `4 < dimword (:'a)` by fs [good_dimindex_def,dimword_def]
  \\ Cases_on `n=0` \\ fs []
  THEN1
   (once_rewrite_tac [word_copy_fwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert])
  \\ Cases_on `n=1` \\ fs []
  THEN1
   (once_rewrite_tac [word_copy_fwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert] \\ rveq \\ fs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store
    \\ fs [lookup_insert,Once insert_insert])
  \\ Cases_on `n=2` \\ fs []
  THEN1
   (once_rewrite_tac [word_copy_fwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert,addressTheory.word_arith_lemma1]
    \\ rfs [lookup_insert] \\ rveq \\ fs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp`,`EL xp ys`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp+1`,`EL (xp+1) ys`] mp_tac)
    \\ strip_tac \\ rfs [] \\ metis_tac [insert_insert])
  \\ Cases_on `n=3` \\ fs []
  THEN1
   (once_rewrite_tac [word_copy_fwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert,addressTheory.word_arith_lemma1]
    \\ rfs [lookup_insert] \\ rveq \\ fs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp`,`EL xp ys`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp+1`,`EL (xp+1) ys`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp+2`,`EL (xp+2) ys`] mp_tac)
    \\ strip_tac \\ rfs [] \\ metis_tac [insert_insert])
  \\ once_rewrite_tac [word_copy_fwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
  \\ rpt_drule memory_rel_ByteArray_IMP
  \\ strip_tac \\ rfs [lookup_insert,addressTheory.word_arith_lemma1]
  \\ rfs [lookup_insert] \\ rveq \\ fs []
  \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
  \\ disch_then (qspecl_then [`yp`,`EL xp ys`] mp_tac)
  \\ strip_tac \\ rfs []
  \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
  \\ disch_then (qspecl_then [`yp+1`,`EL (xp+1) ys`] mp_tac)
  \\ strip_tac \\ rfs []
  \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
  \\ disch_then (qspecl_then [`yp+2`,`EL (xp+2) ys`] mp_tac)
  \\ strip_tac \\ rfs []
  \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
  \\ disch_then (qspecl_then [`yp+3`,`EL (xp+3) ys`] mp_tac)
  \\ strip_tac \\ rfs []
  \\ rewrite_tac [GSYM word_sub_def,addressTheory.word_arith_lemma2]
  \\ fs [] \\ first_x_assum match_mp_tac
  \\ fs [] \\ metis_tac [insert_insert]
QED

(* copy backward *)

Definition word_copy_bwd_def:
  word_copy_bwd be (n:'a word) a b (m:'a word -> 'a word_loc) dm =
    if dimword (:'a) <= 4 then NONE else
    if n <+ 4w then
      if n <+ 2w then
        if n = 0w then SOME m else
          OPTION_BIND (mem_load_byte_aux m dm be a)
                      (\w. mem_store_byte_aux m dm be b w)
      else
        OPTION_BIND (mem_load_byte_aux m dm be a) (\w1.
        OPTION_BIND (mem_load_byte_aux m dm be (a-1w)) (\w2.
          if n = 2w then
            OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
            OPTION_BIND (mem_store_byte_aux m dm be (b-1w) w2) (\m. SOME m))
          else
            OPTION_BIND (mem_load_byte_aux m dm be (a-2w)) (\w3.
            OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
            OPTION_BIND (mem_store_byte_aux m dm be (b-1w) w2) (\m.
            OPTION_BIND (mem_store_byte_aux m dm be (b-2w) w3) (\m. SOME m))))))
    else
      OPTION_BIND (mem_load_byte_aux m dm be a) (\w1.
      OPTION_BIND (mem_load_byte_aux m dm be (a-1w)) (\w2.
      OPTION_BIND (mem_load_byte_aux m dm be (a-2w)) (\w3.
      OPTION_BIND (mem_load_byte_aux m dm be (a-3w)) (\w4.
      OPTION_BIND (mem_store_byte_aux m dm be b w1) (\m.
      OPTION_BIND (mem_store_byte_aux m dm be (b-1w) w2) (\m.
      OPTION_BIND (mem_store_byte_aux m dm be (b-2w) w3) (\m.
      OPTION_BIND (mem_store_byte_aux m dm be (b-3w) w4) (\m.
        word_copy_bwd be (n-4w) (a-4w) (b-4w) m dm))))))))
Termination
  WF_REL_TAC `measure (w2n o FST o SND)`
  \\ Cases_on `n` \\ fs [] \\ rw []
  \\ fs [WORD_LO] \\ rfs [NOT_LESS]
  \\ rewrite_tac [addressTheory.word_arith_lemma2,GSYM word_sub_def] \\ fs []
End

Definition minus_def:
  minus m n = m - n:num
End

Definition list_copy_bwd_def:
  list_copy_bwd (n:num) xp xs yp ys =
    if n <= xp +1 /\ xp < LENGTH xs /\ n <= yp+1 /\ yp < LENGTH ys then
      if n = 0 then SOME ys else
      if n = 1 then SOME (LUPDATE (EL xp xs) yp ys) else
      if n = 2 then SOME ((LUPDATE (EL (minus xp 1) xs) (minus yp 1) o
                           LUPDATE (EL (minus xp 0) xs) (minus yp 0)) ys) else
      if n = 3 then SOME ((LUPDATE (EL (minus xp 2) xs) (minus yp 2) o
                           LUPDATE (EL (minus xp 1) xs) (minus yp 1) o
                           LUPDATE (EL (minus xp 0) xs) (minus yp 0)) ys) else
        list_copy_bwd (n-4) (minus xp 4) xs (minus yp 4)
                         ((LUPDATE (EL (minus xp 3) xs) (minus yp 3) o
                           LUPDATE (EL (minus xp 2) xs) (minus yp 2) o
                           LUPDATE (EL (minus xp 1) xs) (minus yp 1) o
                           LUPDATE (EL (minus xp 0) xs) (minus yp 0)) ys)
    else NONE
End

val list_copy_bwd_def = list_copy_bwd_def |> REWRITE_RULE [minus_def];

Definition list_copy_bwd_alias_def:
  list_copy_bwd_alias n xp yp ys =
    if n <= xp +1 /\ xp < LENGTH ys /\ n <= yp+1 /\ yp < LENGTH ys then
      if n = 0 then SOME ys else
      if n = 1 then SOME (LUPDATE (EL xp ys) yp ys) else
      if n = 2 then SOME ((LUPDATE (EL (minus xp 1) ys) (minus yp 1) o
                           LUPDATE (EL (minus xp 0) ys) (minus yp 0)) ys) else
      if n = 3 then SOME ((LUPDATE (EL (minus xp 2) ys) (minus yp 2) o
                           LUPDATE (EL (minus xp 1) ys) (minus yp 1) o
                           LUPDATE (EL (minus xp 0) ys) (minus yp 0)) ys) else
        list_copy_bwd_alias (n-4) (minus xp 4) (minus yp 4)
                         ((LUPDATE (EL (minus xp 3) ys) (minus yp 3) o
                           LUPDATE (EL (minus xp 2) ys) (minus yp 2) o
                           LUPDATE (EL (minus xp 1) ys) (minus yp 1) o
                           LUPDATE (EL (minus xp 0) ys) (minus yp 0)) ys)
    else NONE
End
val list_copy_bwd_alias_def = list_copy_bwd_alias_def
                                |> REWRITE_RULE [minus_def];

Theorem word_copy_bwd_thm:
   !n xp yp ys ys1 m.
      memory_rel c be ts (insert p2 (ByteArray fl_ys ys) refs)
        sp st m dm ((RefPtr bl1 p1,v1)::(RefPtr bl2 p2,v2)::vars) /\
      lookup p1 refs = SOME (ByteArray fl_xs xs) /\
      list_copy_bwd n xp xs yp ys = SOME ys1 /\
      good_dimindex (:'a) /\ n < dimword (:'a) /\ p1 <> p2 ==>
      ?w1 (w2:'a word) a1 a2 m1.
        v1 = Word w1 /\ v2 = Word w2 /\
        get_real_addr c st w1 = SOME a1 /\
        get_real_addr c st w2 = SOME a2 /\
        word_copy_bwd be (n2w n) (a1 + bytes_in_word + n2w xp)
          (a2 + bytes_in_word + n2w yp) m dm = SOME m1 /\
        memory_rel c be ts  (insert p2 (ByteArray fl_ys ys1) refs)
          sp st m1 dm ((RefPtr bl1 p1,v1)::(RefPtr bl2 p2,v2)::vars)
Proof
  completeInduct_on `n` \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ once_rewrite_tac [list_copy_bwd_def]
  \\ rpt strip_tac
  \\ `4 < dimword (:'a)` by fs [good_dimindex_def,dimword_def]
  \\ Cases_on `n=0` \\ fs []
  THEN1
   (once_rewrite_tac [word_copy_bwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert]
    \\ drule memory_rel_swap \\ strip_tac
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert])
  \\ Cases_on `n=1` \\ fs []
  THEN1
   (once_rewrite_tac [word_copy_bwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert]
    \\ drule memory_rel_swap \\ strip_tac
    \\ rpt_drule memory_rel_RefPtr_IMP \\ strip_tac \\ rveq \\ fs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp`,`EL xp xs`] mp_tac) \\ strip_tac \\ rfs []
    \\ drule memory_rel_swap \\ metis_tac [insert_insert])
  \\ Cases_on `n=2` \\ fs []
  THEN1
   (once_rewrite_tac [word_copy_bwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert,addressTheory.word_arith_lemma1]
    \\ rewrite_tac [addressTheory.word_arith_lemma4,GSYM word_sub_def]
    \\ fs []
    \\ drule memory_rel_swap \\ strip_tac
    \\ rpt_drule memory_rel_RefPtr_IMP \\ strip_tac \\ rveq \\ fs [PULL_EXISTS]
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp`,`EL xp xs`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp-1`,`EL (xp-1) xs`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ drule memory_rel_swap \\ metis_tac [insert_insert])
  \\ Cases_on `n=3` \\ fs []
  THEN1
   (once_rewrite_tac [word_copy_bwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert,addressTheory.word_arith_lemma1]
    \\ rewrite_tac [addressTheory.word_arith_lemma4,GSYM word_sub_def]
    \\ fs []
    \\ drule memory_rel_swap \\ strip_tac
    \\ rpt_drule memory_rel_RefPtr_IMP \\ strip_tac \\ rveq \\ fs [PULL_EXISTS]
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp`,`EL xp xs`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp-1`,`EL (xp-1) xs`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp-2`,`EL (xp-2) xs`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ drule memory_rel_swap \\ metis_tac [insert_insert])
  \\ once_rewrite_tac [word_copy_bwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
  \\ rpt_drule memory_rel_ByteArray_IMP
  \\ strip_tac \\ rfs [lookup_insert,addressTheory.word_arith_lemma1]
  \\ rewrite_tac [addressTheory.word_arith_lemma4,GSYM word_sub_def]
  \\ fs []
  \\ drule memory_rel_swap \\ strip_tac
  \\ rpt_drule memory_rel_RefPtr_IMP \\ strip_tac \\ rveq \\ fs [PULL_EXISTS]
  \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
  \\ disch_then (qspecl_then [`yp`,`EL xp xs`] mp_tac)
  \\ strip_tac \\ rfs []
  \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
  \\ disch_then (qspecl_then [`yp-1`,`EL (xp-1) xs`] mp_tac)
  \\ strip_tac \\ rfs []
  \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
  \\ disch_then (qspecl_then [`yp-2`,`EL (xp-2) xs`] mp_tac)
  \\ strip_tac \\ rfs []
  \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
  \\ disch_then (qspecl_then [`yp-3`,`EL (xp-3) xs`] mp_tac)
  \\ strip_tac \\ rfs []
  \\ drule memory_rel_swap \\ strip_tac
  \\ rewrite_tac [GSYM word_sub_def,addressTheory.word_arith_lemma2]
  \\ fs []
  \\ IF_CASES_TAC
  >-
    (`n-4 = 0` by fs[]>>
    fs[Once word_copy_bwd_def,WORD_LO,Once list_copy_bwd_def]>>
    rw[] \\ metis_tac [insert_insert])
  \\ IF_CASES_TAC
  >-
    (`n-4 = 0` by fs[]>>
    fs[Once word_copy_bwd_def,WORD_LO,Once list_copy_bwd_def]>>
    rw[] \\ metis_tac [insert_insert])
  \\ first_x_assum match_mp_tac
  \\ fs [] \\ metis_tac [insert_insert]
QED

Theorem word_copy_bwd_alias_thm:
   !n xp yp ys ys1 m.
      memory_rel c be ts (insert p2 (ByteArray fl_ys ys) refs)
        sp st m dm ((RefPtr bl p2,v2)::vars) /\
      list_copy_bwd_alias n xp yp ys = SOME ys1 /\
      good_dimindex (:'a) /\ n < dimword (:'a) ==>
      ?(w2:'a word) a2 m1.
        v2 = Word w2 /\
        get_real_addr c st w2 = SOME a2 /\
        word_copy_bwd be (n2w n) (a2 + bytes_in_word + n2w xp)
          (a2 + bytes_in_word + n2w yp) m dm = SOME m1 /\
        memory_rel c be ts (insert p2 (ByteArray fl_ys ys1) refs)
          sp st m1 dm ((RefPtr bl p2,v2)::vars)
Proof
  completeInduct_on `n` \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ once_rewrite_tac [list_copy_bwd_alias_def]
  \\ rpt strip_tac
  \\ `4 < dimword (:'a)` by fs [good_dimindex_def,dimword_def]
  \\ Cases_on `n=0` \\ fs []
  THEN1
   (once_rewrite_tac [word_copy_bwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert])
  \\ Cases_on `n=1` \\ fs []
  THEN1
   (once_rewrite_tac [word_copy_bwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert] \\ rveq \\ fs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ metis_tac [insert_insert])
  \\ Cases_on `n=2` \\ fs []
  THEN1
   (once_rewrite_tac [word_copy_bwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert,addressTheory.word_arith_lemma1]
    \\ rewrite_tac [addressTheory.word_arith_lemma4,GSYM word_sub_def]
    \\ fs [] \\ rveq \\ fs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp`,`EL xp ys`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp-1`,`EL (xp-1) ys`] mp_tac)
    \\ strip_tac \\ rfs [] \\ metis_tac [insert_insert])
  \\ Cases_on `n=3` \\ fs []
  THEN1
   (once_rewrite_tac [word_copy_bwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
    \\ rpt_drule memory_rel_ByteArray_IMP
    \\ strip_tac \\ rfs [lookup_insert,addressTheory.word_arith_lemma1]
    \\ rewrite_tac [addressTheory.word_arith_lemma4,GSYM word_sub_def]
    \\ fs [] \\ rveq \\ fs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp`,`EL xp ys`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp-1`,`EL (xp-1) ys`] mp_tac)
    \\ strip_tac \\ rfs []
    \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
    \\ disch_then (qspecl_then [`yp-2`,`EL (xp-2) ys`] mp_tac)
    \\ strip_tac \\ rfs [] \\ metis_tac [insert_insert])
  \\ once_rewrite_tac [word_copy_bwd_def] \\ fs [] \\ rw [] \\ fs [WORD_LO]
  \\ rpt_drule memory_rel_ByteArray_IMP
  \\ strip_tac \\ rfs [lookup_insert,addressTheory.word_arith_lemma1]
  \\ rewrite_tac [addressTheory.word_arith_lemma4,GSYM word_sub_def]
  \\ fs [] \\ rveq \\ fs []
  \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
  \\ disch_then (qspecl_then [`yp`,`EL xp ys`] mp_tac)
  \\ strip_tac \\ rfs []
  \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
  \\ disch_then (qspecl_then [`yp-1`,`EL (xp-1) ys`] mp_tac)
  \\ strip_tac \\ rfs []
  \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
  \\ disch_then (qspecl_then [`yp-2`,`EL (xp-2) ys`] mp_tac)
  \\ strip_tac \\ rfs []
  \\ rpt_drule memory_rel_ByteArray_IMP_store \\ fs [lookup_insert]
  \\ disch_then (qspecl_then [`yp-3`,`EL (xp-3) ys`] mp_tac)
  \\ strip_tac \\ rfs []
  \\ rewrite_tac [GSYM word_sub_def,addressTheory.word_arith_lemma2]
  \\ Cases_on`xp < 4`
  >-
    (`n-4 = 0` by fs[]
    \\ simp[]
    \\ simp[Once word_copy_bwd_def,WORD_LO]
    \\ fs[Once list_copy_bwd_alias_def] \\ rw[]
    \\ metis_tac [insert_insert])
  \\ Cases_on`yp < 4`
  >-
    (`n-4 = 0` by fs[]
    \\ simp[]
    \\ simp[Once word_copy_bwd_def,WORD_LO,Once list_copy_bwd_def]
    \\ fs[Once list_copy_bwd_alias_def] \\ rw[]
    \\ metis_tac [insert_insert])
  \\ simp[]
  \\ first_x_assum match_mp_tac
  \\ fs [] \\ metis_tac [insert_insert]
QED

(* copy array *)

Definition list_copy_def:
  list_copy n xp xs yp ys =
    if yp <= xp ∨ n+xp = 0
    then list_copy_fwd n xp xs yp ys
    else list_copy_bwd n (xp+n-1) xs (yp+n-1) ys
End

Definition list_copy_alias_def:
  list_copy_alias n xp yp ys =
    if yp <= xp ∨ n+xp = 0
    then list_copy_fwd_alias n xp yp ys
    else list_copy_bwd_alias n (xp+n-1) (yp+n-1) ys
End

Triviality list_copy_fwd_eq:
  ∀n xp xs yp ys.
  xp + n <= LENGTH xs ∧
  yp + n <= LENGTH ys ⇒
  list_copy_fwd n xp xs yp ys =
    SOME
      (TAKE yp ys ++
      TAKE n (DROP xp xs) ++
      DROP (n+yp) ys)
Proof
  ho_match_mp_tac (fetch "-""list_copy_fwd_ind")>>rw[]>>
  simp[Once list_copy_fwd_def]>>
  rpt(IF_CASES_TAC)>>fs[]>>
  rw[LIST_EQ_REWRITE,EL_LUPDATE,EL_APPEND_EQN]>>
  rpt(IF_CASES_TAC>>
  simp[EL_TAKE,EL_DROP])>>
  simp[EL_LUPDATE]>>
  rw[]>>
  Cases_on`x=yp`>>fs[]
QED

Triviality list_copy_bwd_eq:
  ∀n xp xs yp ys.
  n ≤ xp+1 ∧ xp < LENGTH xs ∧
  n ≤ yp+1 ∧ yp < LENGTH ys ⇒
  list_copy_bwd n xp xs yp ys =
    SOME
      (TAKE (yp+1-n) ys ++
      TAKE n (DROP (xp+1-n) xs) ++
      DROP (yp+1) ys)
Proof
  ho_match_mp_tac (fetch "-""list_copy_bwd_ind")>>rw[]>>
  simp[Once list_copy_bwd_def]>>
  fs[minus_def]>>
  reverse(rpt(IF_CASES_TAC))>>fs[]
  >-
    (last_x_assum kall_tac>>
    Cases_on`yp = 3`
    >-
      (`n=4` by fs[]>>
      simp[]>>
      rw[LIST_EQ_REWRITE,EL_LUPDATE,EL_APPEND_EQN]>>
      rpt(IF_CASES_TAC>>
      simp[EL_TAKE,EL_DROP]))>>
    Cases_on`xp=3`
    >-
      (`n=4` by fs[]>>
      simp[]>>
      rw[LIST_EQ_REWRITE,EL_LUPDATE,EL_APPEND_EQN]>>
      rpt(IF_CASES_TAC>>
      simp[EL_TAKE,EL_DROP]))>>
    simp[]>>
    rw[LIST_EQ_REWRITE,EL_LUPDATE,EL_APPEND_EQN]>>
    rpt(IF_CASES_TAC>>
    simp[EL_TAKE,EL_DROP])>>
    simp[EL_LUPDATE]>>
    rpt(IF_CASES_TAC)>>
    simp[]>>
    Cases_on`x=yp`>>fs[])
  >>
  rw[LIST_EQ_REWRITE,EL_LUPDATE,EL_APPEND_EQN]>>
  rpt(IF_CASES_TAC>>
  simp[EL_TAKE,EL_DROP])
QED

Theorem list_copy_thm:
   !xs ys xp yp n ys1.
      copy_array (xs, &xp) (& n) (SOME (ys, &yp)) = SOME ys1 ==>
      list_copy n xp xs yp ys = SOME ys1
Proof
  rw[semanticPrimitivesTheory.copy_array_def,list_copy_def]>>
  fs[integerTheory.INT_ADD,integerTheory.INT_ABS_NUM]
  >-
    (match_mp_tac list_copy_fwd_eq>>
    simp[])
  >-
    simp[Once list_copy_fwd_def]
  >>
    Q.ISPECL_THEN [`n`,`n+xp-1`,`xs`,`n+yp-1`,`ys`] mp_tac list_copy_bwd_eq>>
    impl_tac >-
      simp[]>>
    rw[]>>
    simp[]
QED

(* see more interesting theorem below *)

Triviality list_copy_fwd_alias_eq:
  ∀n xp yp ys.
  yp ≤ xp ∧
  xp + n <= LENGTH ys ∧
  yp + n <= LENGTH ys ⇒
  list_copy_fwd_alias n xp yp ys =
    SOME
      (TAKE yp ys ++
      TAKE n (DROP xp ys) ++
      DROP (n+yp) ys)
Proof
  ho_match_mp_tac (fetch "-""list_copy_fwd_alias_ind")>>rw[]>>
  simp[Once list_copy_fwd_alias_def]>>
  rpt(IF_CASES_TAC)>>fs[]>>
  rw[LIST_EQ_REWRITE,EL_LUPDATE,EL_APPEND_EQN]>>
  rpt(IF_CASES_TAC>>
  simp[EL_TAKE,EL_DROP])>>
  simp[EL_LUPDATE]>>
  rw[]>>
  Cases_on`x=yp`>>fs[]
QED

Triviality list_copy_bwd_alias_eq:
  ∀n xp yp ys.
  xp <= yp ∧
  n ≤ xp +1 ∧ xp < LENGTH ys ∧
  n ≤ yp +1 ∧ yp < LENGTH ys ⇒
  list_copy_bwd_alias n xp yp ys =
    SOME
      (TAKE (yp+1-n) ys ++
      TAKE n (DROP (xp+1-n) ys) ++
      DROP (yp+1) ys)
Proof
  ho_match_mp_tac (fetch "-""list_copy_bwd_alias_ind")>>rw[]>>
  simp[Once list_copy_bwd_alias_def]>>
  fs[minus_def]>>
  reverse(rpt(IF_CASES_TAC))>>fs[]
  >-
    (last_x_assum kall_tac>>
    Cases_on`yp = 3`
    >-
      (`n=4` by fs[]>>
      simp[]>>
      rw[LIST_EQ_REWRITE,EL_LUPDATE,EL_APPEND_EQN]>>
      rpt(IF_CASES_TAC>>
      simp[EL_TAKE,EL_DROP]))>>
    Cases_on`xp=3`
    >-
      (`n=4` by fs[]>>
      simp[]>>
      rw[LIST_EQ_REWRITE,EL_LUPDATE,EL_APPEND_EQN]>>
      rpt(IF_CASES_TAC>>
      simp[EL_TAKE,EL_DROP]))>>
    simp[]>>
    rw[LIST_EQ_REWRITE,EL_LUPDATE,EL_APPEND_EQN]>>
    rpt(IF_CASES_TAC>>
    simp[EL_TAKE,EL_DROP])>>
    simp[EL_LUPDATE]>>
    rpt(IF_CASES_TAC)>>
    simp[]>>
    Cases_on`x=yp`>>fs[])
  >>
  rw[LIST_EQ_REWRITE,EL_LUPDATE,EL_APPEND_EQN]>>
  rpt(IF_CASES_TAC>>
  simp[EL_TAKE,EL_DROP])
QED

Theorem list_copy_alias_thm:
   !ys xp yp n ys1.
      copy_array (ys, &xp) (& n) (SOME (ys, &yp)) = SOME ys1 ==>
      list_copy_alias n xp yp ys = SOME ys1
Proof
  rw[semanticPrimitivesTheory.copy_array_def,list_copy_alias_def]>>
  fs[integerTheory.INT_ADD,integerTheory.INT_ABS_NUM]
  >-
    (match_mp_tac list_copy_fwd_alias_eq>>simp[])
  >-
    simp[Once list_copy_fwd_alias_def]
  >>
    (Q.ISPECL_THEN [`n`,`n+xp-1`,`n+yp-1`,`ys`] mp_tac list_copy_bwd_alias_eq>>
    impl_tac >-
      simp[]>>
    rw[])
QED

Theorem copy_array_NONE_IMP:
   !xs ys xp n.
      copy_array (xs, &xp) (& n) NONE = SOME ys ==>
      list_copy_fwd n xp xs 0 (REPLICATE n 0w) = SOME ys
Proof
  rw[semanticPrimitivesTheory.copy_array_def,list_copy_alias_def]>>
  fs[integerTheory.INT_ADD,integerTheory.INT_ABS_NUM]>>
  Q.ISPECL_THEN [`n`,`xp`,`xs`,`0`,`REPLICATE n 0w`] mp_tac list_copy_fwd_eq>>
  simp[DROP_LENGTH_NIL_rwt]
QED

(*

val xs = EVAL ``GENLIST I 20`` |> concl |> rand

fun cross [] xs = []
  | cross (y::ys) xs = map (fn x => (y,x)) xs @ cross ys xs

val nums = xs |> listSyntax.dest_list |> fst

val inputs = cross nums (cross nums nums)

fun test (n1,(n2,n3)) =
  (ISPEC xs list_copy_alias_thm
   |> Q.SPECL [`1`,`4`,`18`] |> SPEC_ALL
   |> CONV_RULE (RATOR_CONV EVAL THENC RAND_CONV EVAL)
   |> GEN_ALL |> SIMP_RULE std_ss [] |> concl) = T

val (n1,(n2,n3)) = first (not o test) inputs

*)

Definition word_copy_array_def:
  word_copy_array be n a a1 b b1 (m:'a word -> 'a word_loc) dm =
    if b1 <=+ a1 then
      word_copy_fwd be n (a+a1) (b+b1) m dm
    else
      word_copy_bwd be n (a+a1+n-1w) (b+b1+n-1w) m dm
End

val word_copy_bwd_0 = prove(
  ``good_dimindex (:'a) ==>
    word_copy_bwd be (0w:'a word) a1 a2 m dm = SOME m``,
  rw [good_dimindex_def]
  \\ once_rewrite_tac [word_copy_bwd_def] \\ fs [dimword_def,WORD_LO]);

Theorem word_copy_array_thm:
   !n xp yp xs ys ys1 m.
      memory_rel c be ts refs sp st m dm ((RefPtr bl1 p1,v1)::(RefPtr bl2 p2,v2)::vars) /\
      lookup p1 refs = SOME (ByteArray fl_xs xs) /\
      lookup p2 refs = SOME (ByteArray fl_ys ys) /\
      copy_array (xs, &xp) (& n) (SOME (ys, &yp)) = SOME ys1 /\
      good_dimindex (:'a) /\ p1 <> p2 ==>
      ?w1 (w2:'a word) a1 a2 m1.
        v1 = Word w1 /\ v2 = Word w2 /\
        get_real_addr c st w1 = SOME a1 /\
        get_real_addr c st w2 = SOME a2 /\
        word_copy_array be (n2w n) (a1 + bytes_in_word) (n2w xp)
          (a2 + bytes_in_word) (n2w yp) m dm = SOME m1 /\
        memory_rel c be ts (insert p2 (ByteArray fl_ys ys1) refs)
          sp st m1 dm ((RefPtr bl1 p1,v1)::(RefPtr bl2 p2,v2)::vars)
Proof
  rw [] \\ drule list_copy_thm
  \\ fs [list_copy_def]
  \\ `n + xp <= LENGTH xs /\ n + yp <= LENGTH ys` by
     (fs [semanticPrimitivesTheory.copy_array_def,NOT_LESS]
      \\ intLib.COOPER_TAC)
  \\ `LENGTH xs < dimword (:'a) /\ LENGTH ys < dimword (:'a)` by
   (rpt_drule memory_rel_ByteArray_IMP \\ strip_tac
    \\ drule memory_rel_swap \\ strip_tac
    \\ rpt_drule memory_rel_ByteArray_IMP \\ strip_tac
    \\ fs [good_dimindex_def,dimword_def] \\ rfs [])
  \\ `memory_rel c be ts (insert p2 (ByteArray fl_ys ys) refs) sp st m dm
        ((RefPtr bl1 p1,v1)::(RefPtr bl2 p2,v2)::vars)` by
   (qsuff_tac `insert p2 (ByteArray fl_ys ys) refs = refs` \\ fs []
    \\ fs [fmap_EXT,EXTENSION,lookup_def,insert_unchanged])
  \\ IF_CASES_TAC
  >-
    (fs [] \\  rw[]
    \\ rpt_drule word_copy_fwd_thm \\  rw[]
    \\ fs [word_copy_array_def,WORD_LS] \\ rfs []
    \\ IF_CASES_TAC \\  fs[]
    \\ fs[word_copy_bwd_0,Once list_copy_fwd_def])
  \\ rw[] \\ fs[]
  \\ (rpt_drule word_copy_bwd_thm
  \\ strip_tac \\ fs [word_copy_array_def,WORD_LS] \\ rfs []
  \\ rewrite_tac [GSYM WORD_ADD_ASSOC]
  \\ qsuff_tac `(n2w n + (n2w xp + -1w)) = n2w (n + xp − 1) :'a word /\
                (n2w n + (n2w yp + -1w)) = n2w (n + yp − 1) :'a word`
  THEN1 (strip_tac \\ asm_rewrite_tac [] \\ fs [])
  \\ fs [WORD_ADD_ASSOC,word_add_n2w]
  \\ rewrite_tac [GSYM word_sub_def,addressTheory.word_arith_lemma2]
  \\ fs [])
QED

Theorem word_copy_array_alias_thm:
   !n xp yp ys ys1 m.
      memory_rel c be ts refs sp st m dm ((RefPtr bl p2,v2)::vars) /\
      lookup p2 refs = SOME (ByteArray fl_ys ys) /\
      copy_array (ys, &xp) (& n) (SOME (ys, &yp)) = SOME ys1 /\
      good_dimindex (:'a) ==>
      ?(w2:'a word) a2 m1.
        v2 = Word w2 /\
        get_real_addr c st w2 = SOME a2 /\
        word_copy_array be (n2w n) (a2 + bytes_in_word) (n2w xp)
          (a2 + bytes_in_word) (n2w yp) m dm = SOME m1 /\
        memory_rel c be ts (insert p2 (ByteArray fl_ys ys1) refs)
          sp st m1 dm ((RefPtr bl p2,v2)::vars)
Proof
  rw [] \\ drule list_copy_alias_thm
  \\ fs [list_copy_alias_def]
  \\ `n + xp <= LENGTH ys /\ n + yp <= LENGTH ys` by
     (fs [semanticPrimitivesTheory.copy_array_def,NOT_LESS]
      \\ intLib.COOPER_TAC)
  \\ `LENGTH ys < dimword (:'a)` by
   (rpt_drule memory_rel_ByteArray_IMP \\ strip_tac
    \\ fs [good_dimindex_def,dimword_def] \\ rfs [])
  \\ `memory_rel c be ts (insert p2 (ByteArray fl_ys ys) refs) sp st m dm
        ((RefPtr bl p2,v2)::vars)` by
   (qsuff_tac `insert p2 (ByteArray fl_ys ys) refs = refs` \\ fs []
    \\ fs [fmap_EXT,EXTENSION,lookup_insert,insert_unchanged]
    \\ rw [] \\ fs [] \\ eq_tac \\ rw [] \\ fs [])
  \\ IF_CASES_TAC
  >-
    (fs [] >> rw[]>>
    rpt_drule word_copy_fwd_alias_thm>> rw[]>>
    fs [word_copy_array_def,WORD_LS] \\ rfs []>>
    IF_CASES_TAC>> fs[]>>
    fs[word_copy_bwd_0,Once list_copy_fwd_alias_def])
  \\ rw[] \\ fs[]
  \\ (rpt_drule word_copy_bwd_alias_thm
  \\ strip_tac \\ fs [word_copy_array_def,WORD_LS] \\ rfs []
  \\ rewrite_tac [GSYM WORD_ADD_ASSOC]
  \\ qsuff_tac `(n2w n + (n2w xp + -1w)) = n2w (n + xp − 1) :'a word /\
                (n2w n + (n2w yp + -1w)) = n2w (n + yp − 1) :'a word`
  THEN1 (strip_tac \\ asm_rewrite_tac [] \\ fs [])
  \\ fs [WORD_ADD_ASSOC,word_add_n2w]
  \\ rewrite_tac [GSYM word_sub_def,addressTheory.word_arith_lemma2]
  \\ fs [])
QED

Theorem word_of_byte_0:
   word_of_byte 0w = 0w
Proof
  rw [word_of_byte_def]
QED

Theorem last_bytes_0:
   !nb a. last_bytes nb 0w a 0w be = 0w
Proof
  Induct_on `nb`
  \\ once_rewrite_tac [last_bytes_def] \\ fs [] \\ rw []
  \\ fs [set_byte_def]
  \\ fs [word_slice_alt_def]
  \\ fs [word_0,word_or_def,fcpTheory.FCP_BETA,fcpTheory.CART_EQ]
QED

Theorem LUPDATE_REPLICATE[simp]:
   !n a. LUPDATE x a (REPLICATE n x) = REPLICATE n x
Proof
  Induct \\ rewrite_tac [REPLICATE,LUPDATE_def]
  \\ Cases \\ asm_rewrite_tac [REPLICATE,LUPDATE_def]
QED

val memory_rel_copy_array_NONE_lemma =
  memory_rel_RefByte_alt
  |> Q.INST [`w`|->`0w`]
  |> SIMP_RULE (srw_ss()) [w2w_def,w2n_n2w,word_of_byte_0,last_bytes_0,
       LET_THM,LUPDATE_REPLICATE]

Theorem memory_rel_copy_array_NONE:
   memory_rel c be ts refs sp st m dm ((RefPtr bl p1,v1:'a word_loc)::vars) ∧
    new ∉ (domain refs) ∧
    lookup p1 refs = SOME (ByteArray fl_xs xs) /\
    copy_array (xs, &xp) (& n) NONE = SOME ys /\
    byte_len (:α) n < sp ∧ byte_len (:α) n < 2 ** (dimindex (:α) − 4) ∧
    byte_len (:α) n < 2 ** c.len_size ∧ good_dimindex (:α) ⇒
    ∃free curr a1 a2 m1 m2 w1 w2.
      v1 = Word w1 /\
      get_real_addr c st w1 = SOME a1 /\
      make_ptr c (free - curr) 0w (byte_len (:α) n) = Word w2 /\
      get_real_addr c st w2 = SOME a2 /\
      FLOOKUP st NextFree = SOME (Word free) ∧
      FLOOKUP st CurrHeap = SOME (Word curr) ∧
      store_list free
        (Word (make_byte_header c fl n)::
             REPLICATE (byte_len (:α) n) (Word 0w)) m dm = SOME m1 /\
      word_copy_fwd be (n2w n) (a1 + bytes_in_word + n2w xp)
        (a2 + bytes_in_word) m1 dm = SOME m2 /\
      memory_rel c be ts (insert new (ByteArray fl ys) refs)
       (sp − (byte_len (:α) n + 1))
       (st |+ (NextFree,
               Word (free + bytes_in_word * n2w (byte_len (:α) n + 1)))) m2 dm
       ((RefPtr T new,Word w2)::vars)
Proof
  rw [] \\ rpt_drule memory_rel_copy_array_NONE_lemma
  \\ disch_then (qspec_then `fl` mp_tac) \\ strip_tac
  \\ fs []
  \\ drule memory_rel_swap \\ strip_tac
  \\ drule copy_array_NONE_IMP \\ strip_tac
  \\ rpt_drule word_copy_fwd_thm
  \\ impl_tac THEN1
   (rfs [FLOOKUP_DEF,dimword_def,good_dimindex_def,byte_len_def,DIV_LT_X]
    \\ fs [FLOOKUP_DEF,dimword_def,good_dimindex_def,byte_len_def,DIV_LT_X,ADD_DIV_EQ]
    \\ CCONTR_TAC \\ fs [domain_lookup])
  \\ strip_tac \\ fs []
  \\ fs [get_real_addr_def,FLOOKUP_UPDATE] \\ rfs []
  \\ pop_assum mp_tac
  \\ match_mp_tac memory_rel_rearrange \\ fs []
QED

Theorem write_bytearray_isWord:
   ∀ls a m x.
   isWord (m x) ⇒
   isWord (write_bytearray a ls m dm be x)
Proof
  Induct \\ rw[wordSemTheory.write_bytearray_def]
  \\ rw[wordSemTheory.mem_store_byte_aux_def]
  \\ every_case_tac \\ fs[]
  \\ simp[APPLY_UPDATE_THM]
  \\ rw[isWord_def]
QED

Theorem write_bytearray_append:
  ∀xs ys a m dm be.
    (∀i. i < LENGTH xs + LENGTH ys ⇒
         ∃b. mem_load_byte_aux m dm be (a + n2w i) = SOME b) ⇒
    write_bytearray a (xs ++ ys) m dm be =
    write_bytearray a xs (write_bytearray (a + n2w (LENGTH xs)) ys m dm be) dm be
Proof
  Induct \\ gvs [wordSemTheory.write_bytearray_def,ADD1,GSYM word_add_n2w]
  \\ rw []
  \\ first_assum $ qspec_then ‘0’ mp_tac
  \\ last_x_assum $ DEP_REWRITE_TAC o single
  \\ conj_tac
  >- (rw [] \\ first_x_assum $ qspec_then ‘i+1’ mp_tac \\ gvs [GSYM word_add_n2w])
  \\ strip_tac \\ fs []
  \\ CASE_TAC \\ gvs []
  \\ last_x_assum $ kall_tac
  \\ gvs []
  \\ gvs [wordSemTheory.mem_store_byte_aux_def,AllCaseEqs()]
  \\ gvs [wordSemTheory.mem_load_byte_aux_def,AllCaseEqs()]
  \\ metis_tac [write_bytearray_isWord,isWord_def]
QED

Theorem memory_rel_write_bytearray_lemma[local]:
  ∀rest bytes bytes0 m refs.
    memory_rel c be stm refs sp st m dm ((RefPtr b n,Word (w:'a word))::vs) ∧
    lookup n refs = SOME (ByteArray F (bytes0 ++ rest)) ∧ LENGTH bytes = LENGTH bytes0 ∧
    get_real_simple_addr c st w = SOME a ∧ good_dimindex (:'a) ⇒
    memory_rel c be stm (insert n (ByteArray F (bytes ++ rest)) refs) sp st
      (write_bytearray (a + bytes_in_word) bytes m dm be)
      dm ((RefPtr b n,Word w)::vs)
Proof
  Induct_on ‘bytes’ using SNOC_INDUCT \\ rpt strip_tac
  >- (gvs [wordSemTheory.write_bytearray_def,insert_unchanged])
  \\ drule_all memory_rel_ByteArray_IMP \\ simp []
  \\ strip_tac
  \\ rename [‘SNOC new_b _’]
  \\ Cases_on ‘bytes0’ using SNOC_CASES >- gvs [SNOC_APPEND]
  \\ fs [SNOC_APPEND]
  \\ first_x_assum $ qspecl_then [‘LENGTH bytes’,‘new_b’] mp_tac
  \\ gvs [] \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ simp [EL_APPEND2]
  \\ rpt strip_tac
  \\ last_x_assum drule \\ simp []
  \\ disch_then $ qspecl_then [‘new_b::rest’,‘l’] mp_tac
  \\ impl_tac
  >- (gvs [] \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND])
  \\ simp [Once insert_insert]
  \\ match_mp_tac (METIS_PROVE [] “x = y ⇒ (x ⇒ y)”)
  \\ rpt AP_THM_TAC \\ rpt AP_TERM_TAC
  \\ DEP_REWRITE_TAC [write_bytearray_append]
  \\ conj_tac >- rw []
  \\ rpt AP_THM_TAC \\ rpt AP_TERM_TAC
  \\ gvs [wordSemTheory.write_bytearray_def]
  \\ first_x_assum $ qspec_then ‘LENGTH l’ mp_tac
  \\ impl_tac >- gvs []
  \\ strip_tac
  \\ gvs [AllCaseEqs(),wordSemTheory.mem_load_byte_aux_def]
  \\ gvs [wordSemTheory.mem_store_byte_aux_def,theWord_def]
QED

Theorem memory_rel_write_bytearray =
  memory_rel_write_bytearray_lemma |> Q.SPEC ‘[]’ |> SRULE [] |> SPEC_ALL;

Theorem memory_rel_space_max:
   memory_rel c be ts refs old_sp st m dm vars ==>
    ?next_free trig_gc sp.
      FLOOKUP st NextFree = SOME (Word next_free) /\
      FLOOKUP st TriggerGC = SOME (Word trig_gc) /\
      trig_gc - next_free = bytes_in_word * n2w sp :'a word /\ old_sp <= sp /\
      memory_rel c be ts refs sp st m dm vars /\
      (good_dimindex (:'a) ==> (dimindex (:α) DIV 8) * sp < dimword (:'a))
Proof
  fs [memory_rel_def,heap_in_memory_store_def] \\ strip_tac \\ fs []
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ qexists_tac `sp` \\ fs []
  \\ fs [PULL_EXISTS]
  \\ rpt (asm_exists_tac \\ fs [])
  \\ qexists_tac `limit` \\ fs []
  \\ qexists_tac `a` \\ fs []
  \\ qexists_tac `sp` \\ fs []
  \\ qexists_tac `sp1` \\ fs []
  \\ qexists_tac `gens` \\ fs []
  \\ rw [] \\ fs [good_dimindex_def]
  \\ fs [word_ml_inv_def,abs_ml_inv_def,unused_space_inv_def,heap_ok_def]
  \\ rfs [] \\ rveq \\ fs []
QED

Theorem get_lowerbits_ptrbits:
   get_lowerbits c (Word (ptr_bits c x y)) = (ptr_bits c x y || 1w)
Proof
  rw [get_lowerbits_def, fcpTheory.CART_EQ, fcpTheory.FCP_BETA, ptr_bits_def,
      small_shift_length_def]
  \\ eq_tac \\ rw [] \\ fs []
  \\ rfs [word_or_def, word_lsl_def, word_bits_def, fcpTheory.FCP_BETA]
  \\ imp_res_tac maxout_bits_IMP \\ fs []
QED

Definition append_writes_def:
  append_writes c ptr hdr [] l = ARB /\
  append_writes c ptr (hdr:'a word) (x::xs) l =
    Word hdr :: x ::
      if xs = [] then [l] else
        let ptr = ptr + (3w << shift_length c) in
          Word ptr ::
          append_writes c ptr hdr xs l
End

Theorem append_writes_LENGTH:
   !xs ptr.
   xs <> [] ==> LENGTH (append_writes c ptr hdr xs l) = 3 * LENGTH xs
Proof
   Induct \\ rw [append_writes_def]
QED

Theorem ptr_bits_or_1_add_1:
  ptr_bits c tag len ‖ 1w = ptr_bits c tag len + 1w
Proof
  match_mp_tac (GSYM WORD_ADD_OR)
  \\ simp_tac std_ss [fcpTheory.CART_EQ,word_0,word_and_def,fcpTheory.FCP_BETA,
       word_1comp_def,n2w_def] \\ fs []
  \\ fs [ptr_bits_def,word_or_def,fcpTheory.FCP_BETA]
  \\ rw [maxout_bits_def]
  \\ fs [word_lsl_def,fcpTheory.FCP_BETA,all_ones_bit]
QED

Theorem all_ones_n2w:
  all_ones (l + b) b = n2w (2 ** l - 1) << b
Proof
  simp_tac std_ss [all_ones_def]
  \\ IF_CASES_TAC THEN1 (Cases_on `l` \\ fs [])
  \\ simp_tac std_ss [fcpTheory.CART_EQ,word_slice_def,fcpTheory.FCP_BETA,word_lsl_def,
        word_1comp_def,word_0]
  \\ simp [n2w_def,bitTheory.BIT_EXP_SUB1,fcpTheory.FCP_BETA]
QED

Theorem ptr_bits_lemma:
   (w << shift_length conf || ptr_bits conf 0 2 || 1w) =
   w << shift_length conf + ptr_bits conf 0 2 + 1w
Proof
  once_rewrite_tac [GSYM WORD_ADD_ASSOC]
  \\ once_rewrite_tac [GSYM ptr_bits_or_1_add_1]
  \\ irule (SPEC_ALL WORD_ADD_OR |> PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ])
  \\ rw [word_0, fcpTheory.CART_EQ] \\ strip_tac
  \\ rfs [fcpTheory.FCP_BETA, word_lsl_def, word_or_def, word_and_def, ptr_bits_def]
  \\ imp_res_tac maxout_bits_IMP \\ fs []
  \\ imp_res_tac word_bit
  \\ fsrw_tac [wordsLib.WORD_BIT_EQ_ss] [word_index, word_bit_test, shift_length_def]
QED

Theorem encode_header_lemma:
   1 < c.len_size /\ c.len_size + 5 < dimindex (:'a) /\
   good_dimindex (:'a)
   ==>
   decode_length c (make_header c 0w 2) = (2w: 'a word) /\
   encode_header c 0 2 = SOME (make_header c (0w: 'a word) 2)
Proof
  strip_tac
  \\ reverse conj_asm2_tac
  >- fs [encode_header_def, good_dimindex_def, dimword_def]
  \\ imp_res_tac encode_header_IMP \\ fs []
QED

Theorem append_writes_list_to_BlockReps:
   !xs ws x w offset init_ptr.
     LENGTH xs = LENGTH ws /\
     good_dimindex (:'a) /\
     1 < c.len_size /\ c.len_size + 5 < dimindex (:'a) /\
     shift (:'a) <= shift_length c /\
     LIST_REL (\v w. word_addr c v = w) (x::xs) (w::ws) /\
     Word init_ptr = make_cons_ptr c (bytes_in_word * (n2w offset: 'a word)) 0 2
     ==>
     word_list (curr + bytes_in_word * (n2w offset :'a word))
       (append_writes c init_ptr
          (make_header c 0w 2) (w::ws) (word_addr c v)) =
     word_heap (curr + bytes_in_word * n2w offset :'a word)
       (list_to_BlockReps c v offset (x::xs)) c
Proof
  Induct \\ rw []
  >- rw [append_writes_def, list_to_BlockReps_def, BlockRep_def, word_heap_def,
         el_length_def, word_el_def, word_payload_def,
         backend_commonTheory.cons_tag_def, word_list_def, word_addr_def,
         get_addr_def, get_lowerbits_ptrbits, encode_header_lemma, SEP_CLAUSES,
         WORD_LEFT_ADD_DISTRIB, GSYM word_add_n2w, AC STAR_COMM STAR_ASSOC]
  \\ rw [Once append_writes_def, Once list_to_BlockReps_def, BlockRep_def,
         word_heap_def, el_length_def, word_el_def, word_payload_def,
         backend_commonTheory.cons_tag_def, word_list_def, word_addr_def,
         get_addr_def, get_lowerbits_ptrbits, encode_header_lemma, SEP_CLAUSES,
         WORD_LEFT_ADD_DISTRIB, GSYM word_add_n2w, AC STAR_COMM STAR_ASSOC]
  \\ fs []
  \\ first_x_assum (qspecl_then [`ys`,`h`,`offset+3`] mp_tac) \\ fs [] \\ rw []
  \\ fs [make_cons_ptr_thm]
  \\ rfs [get_lowerbits_ptrbits, bytes_in_word_mul_eq_shift,
         PURE_ONCE_REWRITE_RULE [WORD_MULT_COMM] bytes_in_word_mul_eq_shift]
  \\ fs [] \\ rw [] \\ fs []
  \\ fs [ptr_bits_lemma]
  \\ once_rewrite_tac [GSYM WORD_ADD_LSL]
  \\ once_rewrite_tac [GSYM WORD_ADD_ASSOC]
  \\ once_rewrite_tac [GSYM WORD_ADD_LSL]
  \\ once_rewrite_tac [word_add_n2w]
  \\ pop_assum (fn th => fs [GSYM th])
  \\ fs [AC STAR_COMM STAR_ASSOC, ptr_bits_lemma]
QED

Theorem bind_each_eq_tf:
  ∀k tf ts n i x.
    (∀t. t ∈ FDOM tf ⇒ t < ts) ∧ x < ts
    ⇒ bind_each tf ts n i k ' x = tf ' x
Proof
  Induct
  \\ rw [bind_each_def,FAPPLY_FUPDATE_THM]
  \\ first_x_assum ho_match_mp_tac
  \\ rw [] \\ first_x_assum drule
  \\ rw []
QED

Theorem bind_each_FDOM:
  ∀n tf ts k i.
   FDOM (bind_each tf ts k i n) = FDOM tf ∪ { x | ts ≤ x ∧ x < ts + n}
Proof
 Induct \\ rw [bind_each_def,Once INSERT_SING_UNION]
 \\ qmatch_goalsub_abbrev_tac `_ ∪ (_ ∪ s1) = _ ∪ s2`
 \\ `s2 = {ts}  ∪ s1`
    suffices_by  metis_tac [UNION_ASSOC,UNION_COMM]
 \\ ONCE_REWRITE_TAC [GSYM INSERT_SING_UNION]
 \\ UNABBREV_ALL_TAC \\ rw [INSERT_DEF,FUN_EQ_THM]
QED

Theorem bind_each_eq_tf_FDOM:
  ∀k tf ts n i x.
    (∀t. t ∈ FDOM tf ⇒ t < ts) ∧ x < ts ∧ x ∈ FDOM (bind_each tf ts n i k)
    ⇒  x ∈ FDOM tf
Proof
  rw [bind_each_FDOM] \\  fs []
QED

Theorem bind_each_eq_lt_FAPPLY:
  ∀n tf ts k i x.
   bind_each tf ts k i n ' x < k
   ⇒ bind_each tf ts k i n ' x = tf ' x
Proof
  Induct
  \\ rw [bind_each_def]
  \\ Cases_on `x = ts`
  \\ fs [bind_each_def,FAPPLY_FUPDATE_THM]
QED

Theorem bind_each_eq_lt_FDOM:
  ∀n tf ts k i x.
   x ∈ FDOM (bind_each tf ts k i n)
   ∧ bind_each tf ts k i n ' x < k
   ⇒ x ∈ FDOM tf
Proof
  Induct \\ rw [bind_each_def,FAPPLY_FUPDATE_THM]
  \\ first_x_assum ho_match_mp_tac
  \\ asm_exists_tac
  \\ rw []
QED

Theorem bind_each_eq_gt_FAPPLY:
  ∀n tf ts k i x.
   i*n + k < bind_each tf ts k i n ' x
   ⇒ bind_each tf ts k i n ' x = tf ' x
Proof
  Induct
  \\ rw [bind_each_def]
  \\ Cases_on `x = ts`
  \\ fs [bind_each_def,FAPPLY_FUPDATE_THM]
  \\ first_x_assum ho_match_mp_tac
  \\ rw []
  \\ `i + (k + i * n) = k + i * SUC n` suffices_by rw []
  \\ rw [MULT_SUC]
QED

Theorem bind_each_eq_gt_FDOM:
  ∀n tf ts k i x.
   x ∈ FDOM (bind_each tf ts k i n)
   ∧ i*n + k < bind_each tf ts k i n ' x
   ⇒ x ∈ FDOM tf
Proof
  Induct \\ rw [bind_each_def,FAPPLY_FUPDATE_THM]
  \\ first_x_assum ho_match_mp_tac
  \\ asm_exists_tac
  \\ rw []
  \\ `i + (k + i * n) = k + i * SUC n` suffices_by rw []
  \\ rw [MULT_SUC]
QED

Theorem bind_each_eq_ge_FDOM:
  ∀n tf ts k i x.
   x ∈ FDOM (bind_each tf ts k i n)
   ∧ i*n + k ≤ bind_each tf ts k i n ' x
   ∧ i ≠ 0
   ⇒ x ∈ FDOM tf
Proof
  Induct \\ rw [bind_each_def,FAPPLY_FUPDATE_THM]
  \\ first_x_assum ho_match_mp_tac >- fs [MULT_SUC]
  \\ asm_exists_tac
  \\ rw []
  \\ `i + (k + i * n) = k + i * SUC n` suffices_by rw []
  \\ rw [MULT_SUC]
QED

Theorem bind_each_fdom_limit:
  ∀k tf ts n i x.
    (∀t. t ∈ FDOM tf ⇒ t < ts) ∧ ts + k < x
    ⇒ x ∉ FDOM (bind_each tf ts n i k)
Proof
  Induct \\ rw [bind_each_def]
  >- (CCONTR_TAC \\ fs [] \\ first_x_assum drule \\ rw [])
  \\ first_x_assum ho_match_mp_tac
  \\ rw [] \\ RES_TAC \\ rw []
QED

Theorem bind_each_FUPDATE:
  ∀n i tf ts1 ts2 k1 k2.
   ts1 < ts2 ∧ k1 < k2
   ⇒ bind_each (tf |+ (ts1,k1)) ts2 k2 i n = bind_each tf ts2 k2 i n |+ (ts1,k1)
Proof
  Induct \\ rw [bind_each_def]
  \\ qmatch_goalsub_abbrev_tac `f1 |+ _ |+ _`
  \\ ho_match_mp_tac FUPDATE_COMMUTES
  \\ rw []
QED

Theorem bind_each_MINUS:
  ∀n tf ts x k1 k2 i.
   (∀t. t ∈ FDOM tf ⇒ t < ts)
   ∧ x ∈ { x | ts ≤ x ∧ x < ts + n}
   ∧ k2 ≤ k1
   ⇒ bind_each tf ts k1 i n ' x - k2 = bind_each tf ts (k1 - k2) i n ' x
Proof
  Induct \\ rw [bind_each_def]
  \\ Cases_on `x = ts` >- (EVAL_TAC \\ rw [])
  \\ rw [FAPPLY_FUPDATE_THM]
  \\ first_x_assum ho_match_mp_tac
  \\ rw []
  \\ first_x_assum drule
  \\ rw []
QED

Theorem isSomeDataElement_heap_lookup[allow_rebind]:
  ∀n a sp b.
   isSomeDataElement (heap_lookup n (a ++ [Unused sp] ++ b))
   ⇒ n < heap_length a ∨ el_length (Unused sp) + heap_length a ≤ n
Proof
  rw [heap_lookup_APPEND,heap_length_APPEND]
  \\ fs [heap_lookup_def,NOT_LESS,heap_length_def]
  \\ every_case_tac \\ fs [isSomeDataElement_def]
  \\ fs [el_length_def]
QED

Theorem isSomeDataElement_heap_lookup_eq:
  ∀ls n p k1 k2 conf.
   isSomeDataElement (heap_lookup n
     ((list_to_BlockReps conf p k2 ls) : (α word_loc, tag # β list) heap_element list))
   ⇒ isSomeDataElement (heap_lookup n
     ((list_to_BlockReps conf p k1 ls) : (α word_loc, tag # β list) heap_element list))
Proof
  Induct \\ rw [list_to_BlockReps_def]
  \\ every_case_tac \\  fs [heap_lookup_def]
  \\ every_case_tac
  \\ fs [heap_lookup_def,isSomeDataElement_def,BlockRep_def,el_length_def]
  \\ first_x_assum ho_match_mp_tac
  \\ asm_exists_tac \\ rw []
QED

Theorem bind_each_isSomeDataElement:
  ∀l tf ts x p k conf.
   l ≠ []
   ∧ x ∈ { x | ts ≤ x ∧ x < ts + (LENGTH l)}
   ∧ (∀t. t ∈ FDOM tf ⇒ t < ts)
   ⇒ isSomeDataElement (heap_lookup ((bind_each tf ts 0 3 (LENGTH l) ' x))
                       (list_to_BlockReps conf p k l))
Proof
  Induct \\ rw []
  \\ Cases_on `l` >- (EVAL_TAC \\ fs [])
  \\ rw [bind_each_def]
  \\ Cases_on `x = ts` >- (EVAL_TAC \\ rw[])
  \\ first_x_assum (qspecl_then [`tf`,`ts + 1`,`x`,`p`,`k`,`conf`] mp_tac)
  \\ impl_tac
  >- (fs [] \\ rw [] \\ rw []
     \\ ho_match_mp_tac LESS_TRANS \\ qexists_tac `ts` \\ rw [])
  \\ rw [bind_each_FUPDATE]
  \\ fs [FAPPLY_FUPDATE_THM]
  \\ every_case_tac
  >- (fs [list_to_BlockReps_def
        , BlockRep_def
        , heap_lookup_def
        , el_length_def]
     \\ every_case_tac
     \\ rw [heap_lookup_def,isSomeDataElement_def])
  \\ rw [list_to_BlockReps_def,heap_lookup_def]
  >- rw [isSomeDataElement_def,BlockRep_def]
  >- (fs [el_length_def,BlockRep_def]
     \\ `x ∉ FDOM tf` by (CCONTR_TAC \\ fs [] \\ first_x_assum drule \\ rw [])
     \\ `x ∈ FDOM (bind_each tf (ts + 2) 6 3 (LENGTH t))`
        by rw [bind_each_FDOM]
     \\ drule bind_each_eq_lt_FDOM
     \\ impl_tac \\ rw [])
  \\ fs [el_length_def,BlockRep_def]
  \\ qspecl_then [`LENGTH t`,`tf`,`ts+2`,`x`,`6`,`3`,`3`] mp_tac bind_each_MINUS
  \\ impl_tac \\ rw []
  >- (first_x_assum drule \\ rw [])
  \\ fs [list_to_BlockReps_def]
  \\ every_case_tac \\ fs [bind_each_def,BlockRep_def]
  \\ fs [heap_lookup_def] \\ reverse every_case_tac
  >- (fs [el_length_def]
     \\ qmatch_goalsub_abbrev_tac `heap_lookup n1 (list_to_BlockReps _ _ k1 ls)`
     \\ qmatch_asmsub_abbrev_tac `list_to_BlockReps conf p k2 _`
     \\ ho_match_mp_tac isSomeDataElement_heap_lookup_eq
     \\ asm_exists_tac \\ rw [])
  \\ fs [isSomeDataElement_def,el_length_def]
QED

Theorem bind_each_eq_INJ:
  ∀n x y tf ts k i.
  bind_each tf ts k i n ' x = bind_each tf ts k i n ' y
  ∧ i ≠ 0
  ∧ x ∈ { x | ts ≤ x ∧ x < ts + n} ∧ x ∉ FDOM tf
  ∧ y ∈ { x | ts ≤ x ∧ x < ts + n} ∧ y ∉ FDOM tf
  ⇒ x = y
Proof
  Induct \\ rw [bind_each_def]
  \\ fs [FAPPLY_FUPDATE_THM]
  \\ every_case_tac \\ fs []
  >- (qspecl_then [`n`,`tf`,`ts+1`,`i + k`,`i`,`y`] mp_tac bind_each_eq_lt_FDOM
     \\ impl_tac \\ rw [] \\ fs [bind_each_FDOM])
  >- (qspecl_then [`n`,`tf`,`ts+1`,`i + k`,`i`,`x`] mp_tac bind_each_eq_lt_FDOM
     \\ impl_tac \\ rw [] \\ fs [bind_each_FDOM])
  \\ first_x_assum ho_match_mp_tac
  \\ map_every qexists_tac [`tf |+ (ts,k)`,`ts + 1`,`k+i`,`i`]
  \\ rw [FAPPLY_FUPDATE_THM,bind_each_FUPDATE]
QED

Theorem all_ts_list_to_v_SUBSET:
  ∀xs ts (refs: v ref num_map) t.
   {x | ts <= x ∧ x < ts + LENGTH xs} ⊆ all_ts refs [list_to_v ts t xs]
Proof
  Induct \\ rw [list_to_v_def,all_ts_cons]
  \\ fs [SUBSET_DEF]
  \\ Cases_on `h` \\ rw [all_ts_cons_no_block]
  \\ Cases_on `x = ts` \\ rw []
  \\ rw [all_ts_cons]
  \\ Cases_on `x = n0` \\ rw []
  \\ rw [all_ts_append]
QED

Theorem all_ts_SUBSET_list_to_v:
  !refs t xs stack ts.
    all_ts refs (t::(xs ++ stack)) ⊆
    all_ts refs (list_to_v ts t xs::stack)
Proof
  Induct_on `xs` \\ fs [list_to_v_def,all_ts_cons] \\ rw []
  \\ pop_assum (qspecl_then [`refs`,`t`,`h::stack`,`ts+1`] mp_tac)
  \\ fs [all_ts_def,SUBSET_DEF]
  \\ simp [AC DISJ_COMM DISJ_ASSOC]
  \\ rw []
  \\ DISJ2_TAC
  \\ first_x_assum match_mp_tac
  \\ fs []
  \\ metis_tac []
QED

Theorem new_all_ts_SUBSET_list_to_v:
  !refs t xs stack ts.
    {x | ts <= x ∧ x < ts + LENGTH xs} ⊆
    all_ts refs (list_to_v ts t xs::stack)
Proof
  Induct_on `xs` \\ fs [list_to_v_def,all_ts_cons] \\ rw []
  \\ pop_assum (qspecl_then [`refs`,`t`,`h::stack`,`ts+1`] mp_tac)
  \\ fs [all_ts_def,SUBSET_DEF]
  \\ ntac 2 strip_tac
  \\ Cases_on `x = ts` \\ simp [ADD1]
  \\ rw []
  \\ `ts + 1 <= x` by fs []
  \\ metis_tac []
QED

Theorem FDOM_bind_each_lemma:
  !tf k ts h.
    FDOM tf ⊆ {n | n < ts} ⇒
    FDOM (bind_each tf ts h n k) ⊆ {n | n < ts + k}
Proof
  Induct_on `k` \\ fs [bind_each_def,ADD1] \\ rw []
  \\ first_x_assum match_mp_tac
  \\ fs [SUBSET_DEF] \\ rw [] \\ res_tac \\ fs []
QED

Theorem cons_multi_thm:
  abs_ml_inv conf (t::xs ++ stack) refs (roots,heap,be,a,sp,sp1,gens) limit ts /\
  3 * LENGTH xs <= sp /\ xs <> [] ==>
     ?rt rs roots2 heap1 heap2.
       let Allocd = list_to_BlockReps conf rt a rs in
         (roots = rt::rs ++ roots2) /\ (LENGTH rs = LENGTH xs) /\
         heap = heap1 ++ heap_expand (sp + sp1) ++ heap2 /\
         a = heap_length heap1 /\
         abs_ml_inv conf
           (list_to_v ts t xs :: stack) refs
           (Pointer a (Word (ptr_bits conf cons_tag 2))::roots2,
            heap1 ++ Allocd
                  ++ heap_expand (sp + sp1 - heap_length Allocd)
                  ++ heap2, be,
            a + heap_length Allocd, sp - heap_length Allocd, sp1, gens) limit (ts + LENGTH xs)
Proof
  rw [abs_ml_inv_def]
  \\ qpat_x_assum `bc_stack_ref_inv _ _ _ _ _` mp_tac
  \\ simp [Once bc_stack_ref_inv_def] \\ strip_tac
  \\ imp_res_tac LIST_REL_SPLIT1 \\ rw []
  \\ imp_res_tac LIST_REL_LENGTH \\ fs [] \\ rfs []
  \\ qexists_tac `ys1` \\ fs []
  \\ `sp > 0 /\ ys1 <> []` by (Cases_on `xs` \\ fs [])
  \\ qpat_x_assum `unused_space_inv _ _ _` mp_tac
  \\ rw [unused_space_inv_def]
  \\ imp_res_tac heap_lookup_SPLIT \\ fs [] \\ rw []
  \\ qexists_tac `ha` \\ fs []
  \\ simp [heap_expand_def] \\ rveq
  \\ qmatch_goalsub_abbrev_tac `ha ++ Allocd ++ _`
  \\ sg `3 * LENGTH ys1 = heap_length Allocd`
  >- metis_tac [list_to_BlockReps_heap_length]
  \\ pop_assum (fn th => fs [th])
  \\ sg `heap_length Allocd > 0`
  >-
   (unabbrev_all_tac
    \\ Cases_on `ys1`
    \\ fs [list_to_BlockReps_heap_length])
  \\ conj_tac
  >- (* roots_ok *)
   (fs [roots_ok_def] \\ rw []
    \\ TRY
     (unlength_tac [heap_lookup_APPEND, heap_length_APPEND,
                    list_to_BlockReps_heap_lookup_0, Abbr`Allocd`]
      \\ fs [list_to_BlockReps_def, list_to_BlockReps_heap_length,
             list_to_BlockReps_heap_lookup_0]
      \\ NO_TAC)
    \\ first_assum (qspecl_then [`ptr`,`u`] assume_tac) \\ rfs []
    \\ pop_assum mp_tac
    \\ unlength_tac [heap_lookup_APPEND, heap_length_APPEND]
    \\ rw [] \\ fs[]
    \\ TRY (fs [heap_lookup_def, isSomeDataElement_def])
    \\ `sp1 = 0 /\ sp = heap_length Allocd` by fs [] \\ fs [])
  \\ conj_tac
  >- (* heap_ok *)
   (fs [heap_ok_def]
    \\ conj_asm1_tac
    >- (rw [] \\ unlength_tac [])
    \\ conj_tac
    >-
     (fs [FILTER_APPEND]
      \\ rw [] >- metis_tac [list_to_BlockReps_ForwardPointer]
      \\ fs [isForwardPointer_def])
    \\ rpt strip_tac
    \\ TRY
     (rw [] \\ fs []
      \\ first_x_assum (qspecl_then [`xs'`,`l`,`d`,`ptr`,`u`] mp_tac)
      \\ TRY (`sp1 = 0 /\ sp = heap_length Allocd` by fs [] \\ fs [])
      \\ unlength_tac [heap_lookup_APPEND, heap_length_APPEND]
      \\ rw [] \\ fs [isSomeDataElement_def, heap_lookup_def]
      \\ NO_TAC)
    \\ drule (GEN_ALL
      (INST_TYPE [beta|->``:'a word_loc``] list_to_BlockReps_Pointer))
    \\ fs [Abbr`Allocd`]
    \\ rpt (disch_then drule)
    \\ qmatch_goalsub_abbrev_tac `ha ++ hm ++ _`
    \\ rw [] \\ fs [heap_lookup_APPEND, heap_length_APPEND]
    \\ rw [] \\ fs [roots_ok_def]
    \\ last_x_assum (qspecl_then [`ptr`,`u`] mp_tac)
    \\ rw [heap_lookup_APPEND, heap_length_APPEND, heap_lookup_def]
    \\ fs [isSomeDataElement_def])
  \\ conj_tac
  >- (* gc_kind_inv *)
   (fs [gc_kind_inv_def]
    \\ Cases_on `conf.gc_kind` \\ fs []
    \\ Cases_on `gens` \\ fs []
    \\ fs [gen_state_ok_def]
    \\ `h1 = ha ++ [Unused (sp + sp1 - 1)] /\ h2 = hb` by
      unlength_tac [heap_split_APPEND_if, heap_length_APPEND]
    \\ fs [] \\ rveq
    \\ reverse conj_tac
    >-
     (`EVERY (\x. ~isRef x) (ha ++ Allocd)` by
        metis_tac [EVERY_APPEND, list_to_BlockReps_Ref]
      \\ qmatch_goalsub_abbrev_tac `_++Allocd++el`
      \\ qexists_tac `ha++Allocd++el`
      \\ qexists_tac `h2`
      \\ unlength_tac [heap_split_APPEND_if, heap_length_APPEND, Abbr`el`]
      \\ rw [] \\ unlength_tac [heap_split_def, isRef_def]
      \\ `sp1 = 0 /\ sp = heap_length Allocd` by fs [] \\ fs [])
    \\ conj_tac >- (fs [EVERY_MEM] \\ rw [] \\ last_x_assum drule \\ rw [])
    \\ fs [EVERY_MEM]
    \\ rpt strip_tac
    \\ first_x_assum drule
    \\ unlength_tac [gen_start_ok_def, heap_split_APPEND_if, heap_length_APPEND]
    \\ fs [PULL_EXISTS]
    \\ rpt strip_tac
    \\ rfs []
    \\ rpt IF_CASES_TAC \\ fs []
    \\ TRY
     (fs [case_eq_thms] \\ rw []
      \\ first_x_assum drule
      \\ disch_then drule \\ fs [])
    \\ TRY (`sp1 = 0 /\ sp = heap_length Allocd` by fs [] \\ fs [])
    \\ unlength_tac [heap_split_def, case_eq_thms, PULL_EXISTS] \\ rw []
    \\ TRY (`e = heap_length h1` by fs [] \\ fs [] \\ rw [])
    \\ TRY
     (Cases_on `Allocd`
      \\ fs [list_to_BlockReps_NULL, heap_length_def, el_length_def]
      \\ NO_TAC)
    \\ first_x_assum drule
    \\ TRY (disch_then drule) \\ rw []
    \\ unlength_tac [])
  \\ conj_tac
  >- (* heap_lookup list_to_BlockReps *)
    unlength_tac [heap_lookup_def, heap_length_APPEND, heap_lookup_APPEND]
  \\ conj_tac
  >- (* heap_length *) rw [heap_length_APPEND, heap_length_def, el_length_def]
  \\ conj_tac
  >- (* data_up_to *)
   (rw []
    \\ `heap_length Allocd + heap_length ha = heap_length (ha ++ Allocd)` by
      fs [heap_length_APPEND]
    \\ pop_assum (fn th => fs [th, data_up_to_APPEND])
    \\ unlength_tac [data_up_to_def, heap_split_APPEND_if] \\ rveq
    \\ unabbrev_all_tac
    \\ irule (SIMP_RULE (srw_ss()) [] list_to_BlockReps_data_up_to) \\ fs [])
  \\ fs [bc_stack_ref_inv_def]
  \\ qexists_tac `f`
  \\ qexists_tac `bind_each tf ts (heap_length ha) 3 (LENGTH xs)`
  \\ conj_tac
  >-
   (match_mp_tac INJ_SUBSET
    \\ fs [heap_expand_def]
    \\ asm_exists_tac \\ fs [] \\ rw []
    \\ TRY (`sp1 = 0 /\ sp = heap_length Allocd` by fs [] \\ fs [])
    \\ unlength_tac [heap_lookup_APPEND, heap_lookup_def]
    \\ simp [SUBSET_DEF, isSomeDataElement_def] \\ rw [] \\ fs [])
  \\ fs []
  \\ conj_tac
  >- (qpat_x_assum `INJ _ (FDOM tf) _` assume_tac
     \\ qpat_x_assum `heap_length _ <= sp` assume_tac
     \\ qmatch_goalsub_abbrev_tac `INJ _ _ a0`
     \\ drule_then (qspecl_then [`FDOM tf`,`a0`] mp_tac) INJ_SUBSET
     \\ impl_tac
     >- (rw [Abbr `a0`]
        \\ rw [SUBSET_DEF]
        \\ unlength_tac [heap_lookup_APPEND, heap_length_APPEND]
        \\ every_case_tac \\ rw [] \\ fs []
        \\ fs [heap_lookup_def,isSomeDataElement_def]
        \\ map_every qexists_tac [`ys`,`l`,`d`]
        \\ qmatch_goalsub_abbrev_tac `heap_lookup x0 hb`
        \\ qmatch_asmsub_abbrev_tac `heap_lookup x1 hb`
        \\ `x0 = x1` suffices_by fs []
        \\ UNABBREV_ALL_TAC \\ fs [])
     \\ rw [Abbr `a0`]
     \\ pop_assum mp_tac
     \\ ONCE_REWRITE_TAC [GSYM APPEND_ASSOC]
     \\ ONCE_REWRITE_TAC [GSYM APPEND_ASSOC]
     \\ qmatch_goalsub_abbrev_tac `(ha ++ (Allocd ++ hb1))`
     \\ strip_tac
     \\ `∀t. t ∈ FDOM tf ⇒ t < ts` by (fs [SUBSET_DEF])
     \\ ntac 21 (last_x_assum (K all_tac)) (* make proofs faster *)
     \\ (fs [INJ_DEF] \\ rw []
     >- (Cases_on `x' < ts`
        >- (drule bind_each_eq_tf
           \\ disch_then drule \\ rw []
           \\ first_x_assum ho_match_mp_tac
           \\ ho_match_mp_tac bind_each_eq_tf_FDOM
           \\ metis_tac [])
        \\ qmatch_goalsub_abbrev_tac `isSomeDataElement (heap_lookup tf1 _)`
        \\ `heap_length Allocd = 3 * LENGTH ys1`
           by rw [Abbr`Allocd`, list_to_BlockReps_heap_length]
        \\ Cases_on `tf1 < heap_length ha`
        >- (fs [Abbr `tf1`] \\ drule bind_each_eq_lt_FAPPLY \\ rw []
           \\ first_x_assum ho_match_mp_tac \\ ho_match_mp_tac bind_each_eq_lt_FDOM
           \\ asm_exists_tac \\ rw [])
        \\ fs [NOT_LESS]
        \\ Cases_on `heap_length ha +  heap_length Allocd < tf1`
        >- (fs [Abbr `tf1`] \\ rfs [] \\ drule bind_each_eq_gt_FAPPLY \\ rw []
           \\ first_x_assum ho_match_mp_tac \\ ho_match_mp_tac bind_each_eq_gt_FDOM
           \\ asm_exists_tac \\ rw [])
        \\ fs [NOT_LESS]
        \\ `x' ∉ FDOM tf` by (CCONTR_TAC \\ fs [] \\ first_x_assum drule \\ rw [])
        \\ fs [heap_lookup_APPEND,heap_length_APPEND]
        \\ every_case_tac \\ fs []
        \\ rw []
        \\ fs [heap_length_def,el_length_def]
        >- (rw[Abbr`tf1`]
           \\ drule_then (qspecl_then [ `LENGTH ys1`,`x'`
                                      , `SUM (MAP el_length ha)`
                                      , `SUM (MAP el_length ha)`
                                      , `3`] mp_tac) bind_each_MINUS
           \\ impl_tac >- fs [bind_each_FDOM]
           \\ rw[Abbr`Allocd`]
           \\ ho_match_mp_tac bind_each_isSomeDataElement
           \\ rw [] \\ fs [bind_each_FDOM])
        \\ fs[NOT_LESS,Abbr`tf1`]
        \\ drule bind_each_eq_ge_FDOM
        \\ rw [])
        \\ rpt (qpat_x_assum `_ ∈ FDOM _`
                        (fn asm => assume_tac (SIMP_RULE std_ss [bind_each_FDOM] asm)
                                    \\ mp_tac asm))
        \\ rpt (strip_tac)
        \\ fs []
        >- (RES_TAC \\ first_x_assum ho_match_mp_tac
           \\ IMP_RES_TAC bind_each_eq_tf
           \\ fs [])
        >- (first_assum drule \\ strip_tac
           \\ drule bind_each_eq_tf \\ disch_then drule
           \\ strip_tac \\ fs []
           \\ RES_TAC \\ fs []
           \\ drule isSomeDataElement_heap_lookup \\ strip_tac
           \\ `x' ∉ FDOM tf` by (CCONTR_TAC \\ fs [] \\ first_x_assum drule \\ rw [])
           \\ qpat_x_assum `y ∈ FDOM (bind_each _ _ _ _ _)` (K all_tac)
           >- (qpat_x_assum `bind_each _ _ _ _ _ ' x' = _` (assume_tac o GSYM)
              \\ fs [] \\ drule bind_each_eq_lt_FDOM \\ rw [])
           \\ TRY (`sp1 = 0 /\ sp = heap_length Allocd` by fs []) \\ fs []
           \\ drule bind_each_eq_ge_FDOM
           \\ rw [] \\ fs [el_length_def]
           \\ ho_match_mp_tac LESS_EQ_TRANS
           \\ qexists_tac `heap_length Allocd - 1 + 1 + heap_length ha`
           \\ rw [] \\ rw [Abbr`Allocd`,list_to_BlockReps_heap_length])
        >- (first_assum drule \\ strip_tac
           \\ drule bind_each_eq_tf \\ disch_then drule
           \\ strip_tac \\ fs []
           \\ RES_TAC \\ fs []
           \\ drule isSomeDataElement_heap_lookup \\ strip_tac
           \\ `y ∉ FDOM tf` by (CCONTR_TAC \\ fs [] \\ first_x_assum drule \\ rw [])
           \\ qpat_x_assum `x' ∈ FDOM (bind_each _ _ _ _ _)` (K all_tac)
           >- (fs [] \\ drule bind_each_eq_lt_FDOM \\ rw [])
           \\ TRY (`sp1 = 0 /\ sp = heap_length Allocd` by fs []) \\ fs []
           \\ drule bind_each_eq_ge_FDOM
           \\ rw [] \\ fs [el_length_def]
           \\ ho_match_mp_tac LESS_EQ_TRANS
           \\ qexists_tac `heap_length Allocd - 1 + 1 + heap_length ha`
           \\ rw [] \\ rw [Abbr`Allocd`,list_to_BlockReps_heap_length])
        \\ ho_match_mp_tac bind_each_eq_INJ
        \\ asm_exists_tac \\ rw [] \\ CCONTR_TAC
        \\ fs [] \\ first_x_assum drule \\ rw []))
  \\ conj_tac
  >- (rw [bind_each_FDOM]
     \\ imp_res_tac LIST_REL_LENGTH \\ fs []
     \\ imp_res_tac LIST_REL_LENGTH \\ fs []
     \\ TRY (qpat_x_assum `LENGTH xs = _` (assume_tac o GSYM))
     \\ fs [new_all_ts_SUBSET_list_to_v]
     \\ ho_match_mp_tac SUBSET_TRANS
     \\ qexists_tac `all_ts refs (t::(xs++stack))` \\ rw []
     \\ fs [all_ts_SUBSET_list_to_v])
  \\ conj_tac
  >- (match_mp_tac FDOM_bind_each_lemma \\ fs [])
  \\ reverse conj_tac
  >-
   (rpt strip_tac
    \\ first_x_assum (qspec_then `n` mp_tac)
    \\ impl_tac \\ fs []
    >-
      (fs [reachable_refs_def] \\ rveq
       \\ metis_tac [list_to_v_get_refs])
    \\ simp [bc_ref_inv_def] \\ fs []
    \\ fs [RefBlock_def, Bytes_def]
    \\ ntac 3 TOP_CASE_TAC \\ fs []
    \\ unlength_tac [heap_lookup_APPEND, heap_length_APPEND]
    \\ `0 < heap_length Allocd /\ heap_length Allocd <= sp + sp1` by fs []
    \\ drule (GEN_ALL v_inv_LIST_REL)
    \\ disch_then drule
    \\ fs [heap_expand_def]
    \\ rw []
    \\ TRY (`sp1 = 0 /\ sp = heap_length Allocd` by fs [] \\ fs [])
    \\ TRY (fs [heap_lookup_def] \\ NO_TAC)
    \\ TRY (asm_exists_tac \\ rw [])
    \\ TRY (qexists_tac `zs` \\ conj_tac >- unlength_tac [] )
    \\ TRY
     (first_x_assum drule \\ rw []
      \\ unlength_tac []
      \\ pop_assum mp_tac
      \\ ho_match_mp_tac  LIST_REL_mono \\ rw []
      \\ pop_assum (mp_then Any ho_match_mp_tac (GEN_ALL v_inv_SUBMAP))
      \\ rw [heap_store_rel_def]
      \\ ho_match_mp_tac bind_each_SUBMAP
      \\ fs [SUBSET_DEF]
      \\ NO_TAC)
    \\ TRY
     (first_x_assum drule \\ rw [])
    \\ unlength_tac [])
  \\ reverse conj_tac
  >-
   (`0 < heap_length Allocd /\ heap_length Allocd <= sp + sp1` by decide_tac
    \\ drule (GEN_ALL v_inv_LIST_REL)
    \\ disch_then drule
    \\ fs [heap_expand_def]
    \\ rw [] \\ fs []
    \\ ho_match_mp_tac EVERY2_SWAP
    \\ pop_assum ho_match_mp_tac
    \\ fs [LIST_REL_APPEND_EQ]
    \\ imp_res_tac EVERY2_SWAP \\ fs []
    \\ qpat_x_assum `LIST_REL _ _ stack` mp_tac
    \\ ho_match_mp_tac LIST_REL_mono \\ rw []
    \\ pop_assum (mp_then Any ho_match_mp_tac (GEN_ALL v_inv_SUBMAP))
    \\ rw [heap_store_rel_def]
    \\ ho_match_mp_tac bind_each_SUBMAP
    \\ fs [SUBSET_DEF])
  \\ qmatch_goalsub_abbrev_tac `ha ++ _ ++ hm ++ _`
  \\ `hm = heap_expand (sp+sp1 - heap_length Allocd)` by
    unlength_tac [Abbr`hm`, heap_expand_def]
  \\ pop_assum (fn th => fs [th])
  \\ qunabbrev_tac `Allocd`
  \\ `∀t. t ∈ FDOM tf ⇒ t < ts` by fs [SUBSET_DEF]
  \\ qpat_x_assum `LENGTH xs = _` (assume_tac o GSYM)
  \\ rw []
  \\ match_mp_tac (Q.INST [`sp`|->`sp+sp1`] (SPEC_ALL v_inv_list_to_v))
  \\ unlength_tac [heap_expand_def]
QED

Theorem memory_rel_append:
   memory_rel c be ts refs sp st m1 dm
      ((v,h)::ZIP (in1,ws) ++ vars) /\
    (word_list next_free
      (append_writes c init_ptr (make_header c 0w 2) ws h) * SEP_T)
      (fun2set (m1,dm)) /\
    1 < c.len_size  /\
    LENGTH in1 = LENGTH ws /\ in1 <> [] /\
    3 * LENGTH in1 <= sp /\ good_dimindex (:'a) /\
    Word init_ptr = make_cons_ptr c (next_free - curr) 0 2 /\
    FLOOKUP st CurrHeap = SOME (Word curr) /\
    FLOOKUP st NextFree = SOME (Word (next_free:'a word)) ==>
    memory_rel c be (ts + LENGTH in1) refs (sp - 3 * LENGTH in1)
       (st |+ (NextFree,
               Word (next_free + bytes_in_word * n2w (3 * LENGTH in1)))) m1 dm
       ((list_to_v ts v in1 ,Word init_ptr)::vars)
Proof
  rw []
  \\ qabbrev_tac `p1 = ptr_bits c 0 2`
  \\ qabbrev_tac `sl = shift_length c - shift (:'a)`
  \\ qmatch_asmsub_abbrev_tac `append_writes c nfs`
  \\ qhdtm_x_assum `memory_rel` (strip_assume_tac o REWRITE_RULE [memory_rel_def])
  \\ imp_res_tac MAP_ZIP
  \\ fs [word_ml_inv_def]
  \\ mp_tac (GEN_ALL cons_multi_thm)
  \\ disch_then (qspecl_then [`in1`,`ts`,`v`] mp_tac)
  \\ fs []
  \\ disch_then drule
  \\ impl_tac
  >- (Cases_on `ws` \\ Cases_on `in1` \\ fs [])
  \\ rw []
  \\ rw [memory_rel_def, word_ml_inv_def, PULL_EXISTS]
  \\ qmatch_asmsub_abbrev_tac `abs_ml_inv _ _ _ (r0::rs0,h0,_,a0,sp0,_) _ _`
  \\ Q.LIST_EXISTS_TAC [`h0`,`limit`,`a0`,`sp0`,`sp1`,`gens`,`r0`,`rs0`] \\ fs []
  \\ unabbrev_all_tac
  \\ reverse conj_tac
  >-
   (fs [abs_ml_inv_def, LIST_REL_APPEND_EQ]
    \\ reverse conj_tac
    >- (Cases_on `rs` \\ fs [list_to_BlockReps_heap_length])
    \\ fs [heap_in_memory_store_def, make_cons_ptr_thm] \\ rfs [] \\ rw []
    \\ once_rewrite_tac [GSYM WORD_NEG_MUL]
    \\ once_rewrite_tac [WORD_2COMP_LSL]
    \\ qmatch_goalsub_abbrev_tac `-x` \\ fs [] (* really? *)
    \\ rw [word_addr_def, get_addr_def, backend_commonTheory.cons_tag_def]
    \\ fs [get_lowerbits_ptrbits, bytes_in_word_mul_eq_shift])
  \\ qhdtm_x_assum `heap_in_memory_store` mp_tac
  \\ fs [heap_in_memory_store_def]
  \\ Cases_on `rs`
  \\ fs [list_to_BlockReps_heap_length, heap_length_heap_expand,
         heap_length_APPEND, FLOOKUP_UPDATE, word_heap_heap_expand,
         word_heap_APPEND]
  \\ rw [] \\ rfs [] \\ rveq
  \\ conj_tac
  >- fs [WORD_LEFT_ADD_DISTRIB, GSYM word_add_n2w]
  \\ last_x_assum assume_tac
  \\ fs [] \\ rveq
  \\ fs [AC STAR_COMM STAR_ASSOC]
  \\ drule (GEN_ALL word_list_AND_word_list_exists_IMP
       |> SIMP_RULE std_ss [Once STAR_COMM])
  \\ qmatch_asmsub_abbrev_tac `(word_heap _ _ _ * (Q * _))`
  \\ fs [AC STAR_COMM STAR_ASSOC]
  \\ unabbrev_all_tac
  \\ simp [Once STAR_COMM]
  \\ disch_then drule
  \\ Cases_on `ws` \\ fs [append_writes_LENGTH] \\ fs []
  \\ fs [AC STAR_COMM STAR_ASSOC]
  \\ qpat_abbrev_tac `PAT1 = word_list _ (append_writes _ _ _ _ _)`
  \\ qpat_abbrev_tac `PAT2 = word_heap _ (list_to_BlockReps _ _ _ _) _`
  \\ qsuff_tac `PAT1 = PAT2`
  >- fs [AC STAR_COMM STAR_ASSOC, WORD_LEFT_ADD_DISTRIB, GSYM word_add_n2w]
  \\ unabbrev_all_tac \\ rfs []
  \\ irule append_writes_list_to_BlockReps \\ fs []
  \\ metis_tac [LIST_REL_APPEND_IMP]
QED

(* --- ML lists cannot exceed heap size: --- *)

Definition walk_def:
  walk conf heap ptr n =
    if n = 0n then []
    else if n = 1 then [ptr] else
      case some p.
        ?x y.
        heap_lookup ptr heap = SOME (BlockRep cons_tag [x; y]) /\
        y = Pointer p (Word (ptr_bits conf cons_tag 2)) of
        NONE => []
      | SOME p =>
          ptr::walk conf heap p (n-1)
End

Theorem v_inv_v_to_list_lemma:
   v_inv c v (y,f,tf,heap) /\
   v_to_list v = SOME vs /\
   vs <> [] ==>
    ?p ys. y = Pointer p (Word (ptr_bits c cons_tag 2)) /\
               heap_lookup p heap = SOME (BlockRep cons_tag ys)
Proof
  rw [] \\ Cases_on `vs` \\ fs [v_to_list_def] \\ rw []
  \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac \\ fs []
  \\ fs [BlockRep_def,v_inv_def]
QED

Theorem walk_LENGTH:
   !vs ptr ps v ts.
     v_inv c v (Pointer ptr (Word (ptr_bits c cons_tag 2)),f,tf,heap) /\
     v_to_list v = SOME vs /\
     vs <> [] /\
     walk c heap ptr (LENGTH vs) = ps
     ==>
     LENGTH ps = LENGTH vs
Proof
  Induct \\ rw []
  \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
  \\ fs [] \\ rveq \\ fs []
  \\ fs [v_inv_def] \\ rveq
  \\ drule (GEN_ALL v_inv_v_to_list_lemma) \\ fs []
  \\ Cases_on `vs` \\ fs []
  >- (once_rewrite_tac [walk_def] \\ fs [])
  \\ rw []
  \\ first_x_assum drule \\ strip_tac
  \\ once_rewrite_tac [walk_def] \\ fs []
  \\ fs [some_def, BlockRep_def]
QED

Theorem BlockRep_heap_length[simp]:
   heap_length [BlockRep tag [x;y]] = 3
Proof
  EVAL_TAC
QED

Theorem ALL_DISTINCT_FILTER_LENGTH:
   ALL_DISTINCT xs
   ==>
   LENGTH (FILTER ($~ o P) xs) + LENGTH (FILTER P xs) = LENGTH xs
Proof
  Induct_on `xs` \\ rw [] \\ fs []
QED

Theorem heap_length_Blocks:
   !ps (heap: 'a ml_heap).
     ALL_DISTINCT ps /\
     EVERY (\p. ?x y. heap_lookup p heap = SOME (BlockRep cons_tag [x;y])) ps
     ==>
     3 * LENGTH ps <= heap_length heap
Proof
  gen_tac \\ completeInduct_on `LENGTH ps`
  \\ Cases \\ rw [] \\ fs [EVERY_MEM]
  \\ imp_res_tac heap_lookup_SPLIT \\ fs [] \\ rveq
  \\ qabbrev_tac `t1 = FILTER (\x. x < heap_length ha) t`
  \\ qabbrev_tac `t2 = FILTER (\x. ~(x < heap_length ha)) t`
  \\ sg `ALL_DISTINCT t1 /\ ALL_DISTINCT t2`
  >- fs [FILTER_ALL_DISTINCT, Abbr`t1`, Abbr`t2`]
  \\ sg `!p. MEM p t2 ==> heap_length ha + 2 < p`
  >-
   (rw [MEM_FILTER, Abbr`t2`]
    \\ CCONTR_TAC \\ fs []
    \\ Cases_on `p = heap_length ha` \\ fs []
    \\ res_tac \\ rfs [heap_lookup_APPEND, heap_lookup_def, heap_length_APPEND])
  \\ qabbrev_tac `t3 = MAP (\x. x - 3) t2`
  \\ sg `ALL_DISTINCT t3`
  >- (fs [Abbr`t3`] \\ irule ALL_DISTINCT_MAP_INJ \\ rw [] \\ res_tac \\ fs [])
  \\ sg `ALL_DISTINCT (t1 ++ t3)`
  >-
   (simp [ALL_DISTINCT_APPEND, Abbr`t1`, Abbr`t2`, Abbr`t3`]
    \\ rw [MEM_FILTER, MEM_MAP] \\ CCONTR_TAC \\ fs [] \\ rveq
    \\ rename1 `MEM z t`
    \\ qabbrev_tac `len = heap_length ha`
    \\ `z = len \/ z = len + 1 \/ z = len + 2` by decide_tac \\ fs [] \\ rveq
    \\ last_x_assum kall_tac
    \\ res_tac \\ fs [] \\ rfs [] \\ rw []
    \\ qunabbrev_tac `len` \\ fs []
    \\ fs [heap_lookup_APPEND, heap_length_APPEND, heap_lookup_def])
  \\ last_x_assum (qspec_then `LENGTH (t1++t3)` mp_tac) \\ fs []
  \\ sg `LENGTH (t1++t3) = LENGTH t`
  >- (unabbrev_all_tac \\ fs [] \\ metis_tac [o_DEF, ALL_DISTINCT_FILTER_LENGTH])
  \\ fs []
  \\ disch_then (qspec_then `t1++t3` mp_tac) \\ fs []
  \\ disch_then (qspec_then `ha++hb` mp_tac)
  \\ impl_tac
  >-
   (unabbrev_all_tac \\ rw []
    \\ fs [MEM_FILTER, MEM_MAP] \\ rveq
    \\ res_tac \\ fs []
    \\ rfs [heap_lookup_APPEND, heap_length_APPEND, BlockRep_def])
  \\ fs [LEFT_ADD_DISTRIB, heap_length_APPEND, ADD1, LESS_EQ_TRANS]
QED

Theorem walk_heap_lookup:
   !vs p ps v ts.
     v_inv c v
       (Pointer p (Word (ptr_bits c cons_tag 2)),f,tf,heap) /\
     v_to_list v = SOME vs /\
     vs <> [] /\
     walk c heap p (LENGTH vs) = ps
     ==>
     EVERY (\p. ?x y. heap_lookup p heap = SOME (BlockRep cons_tag [x; y])) ps
Proof
  Induct \\ rw []
  \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
  \\ fs [] \\ rveq \\ fs []
  \\ fs [v_inv_def] \\ rveq
  \\ drule (GEN_ALL v_inv_v_to_list_lemma) \\ fs []
  \\ Cases_on `vs` \\ fs []
  >- (once_rewrite_tac [walk_def] \\ fs [BlockRep_def])
  \\ rw []
  \\ first_x_assum drule \\ rw [EVERY_MEM]
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [walk_def] \\ fs []
  \\ CASE_TAC \\ fs [] \\ rw []
  \\ fs [BlockRep_def]
QED

Theorem walk_MEM:
   v_inv c v (Pointer ptr (Word (ptr_bits c cons_tag 2)),f,tf,heap) /\
   v_to_list v = SOME vs /\
   vs <> []
   ==>
   MEM ptr (walk c heap ptr (LENGTH vs))
Proof
  Cases_on `vs` \\ rw []
  \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
  \\ fs [] \\ rveq \\ fs []
  \\ rpt (pop_assum mp_tac)
  \\ simp [Once walk_def, v_inv_def, some_def, BlockRep_def]
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ rename1 `z <> Pointer _ _`
  \\ Cases_on `z` \\ fs []
  \\ qhdtm_x_assum `v_inv` mp_tac
  \\ Cases_on `t`
  \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
  \\ fs [] \\ rveq \\ fs []
  \\ rw [v_inv_def, v_to_list_def, BlockRep_def]
  \\ CCONTR_TAC \\ fs [] \\ rveq \\ fs []
QED

Theorem walk_EL:
   !vs ptr ps v ts.
     v_inv c v (Pointer ptr (Word (ptr_bits c cons_tag 2)),f,tf,heap) /\
     v_to_list v = SOME vs /\
     vs <> [] /\
     walk c heap ptr (LENGTH vs) = ps
     ==>
     !n. SUC n < LENGTH vs ==>
       ?x.
         heap_lookup (EL n ps) heap =
           SOME (BlockRep cons_tag [x;
             Pointer (EL (SUC n) ps) (Word (ptr_bits c cons_tag 2))])
Proof
  Induct >- rw [] \\ ntac 6 strip_tac
  \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
  \\ fs [] \\ rveq \\ fs []
  \\ Induct \\ rw []
  \\ qhdtm_x_assum `v_inv` mp_tac
  \\ rw [v_to_list_def, v_inv_def]
  \\ Cases_on `vs` \\ fs [] \\ rveq
  \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
  \\ fs [] \\ rveq \\ fs []
  \\ drule (GEN_ALL v_inv_v_to_list_lemma) \\ fs [] \\ rw []
  \\ first_x_assum drule \\ fs []
  >-
   (disch_then (qspec_then `0` mp_tac)
    \\ Cases_on `t` \\ fs [] \\ rw []
    \\ ntac 2 (once_rewrite_tac [walk_def] \\ fs [BlockRep_def])
    \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
    \\ fs [] \\ rveq \\ fs []
    \\ qhdtm_x_assum `v_inv` mp_tac
    \\ rw [v_inv_def] \\ fs [BlockRep_def]
    \\ rveq \\ fs [])
  \\ disch_then drule \\ rw []
  \\ once_rewrite_tac [walk_def] \\ fs [BlockRep_def]
QED

Theorem v_to_list_same_LENGTH:
   !xs x ys v1 v2 ts1 ts2.
     v_inv c v1 (x,f,tf,heap) /\
     v_inv c v2 (x,f,tf,heap) /\
     v_to_list v1 = SOME xs   /\
     v_to_list v2 = SOME ys
     ==>
     LENGTH xs = LENGTH ys
Proof
  Induct \\ rw [v_to_list_SOME_NIL_IFF]
  >- (fs [v_inv_def] \\ rveq \\ fs []
     \\ Cases_on `ys`
     \\ fs [v_inv_def, v_to_list_def]
     \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
     \\ fs [] \\ rveq \\ fs [v_inv_def])
  \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
  \\ fs [] \\ rveq \\ fs [v_inv_def] \\ rveq
  \\ Cases_on `ys`
  >- (fs [v_to_list_SOME_NIL_IFF]
     \\ rveq \\ fs [v_inv_def])
  \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
  \\ fs [] \\ rveq \\ fs [v_inv_def]
  \\ first_x_assum ho_match_mp_tac
  \\ fs [BlockRep_def] \\ rveq
  \\ metis_tac []
QED

Definition block_drop_def:
  block_drop 0 v                           = SOME v
∧ block_drop (SUC n) (Block ts tag [h;vl]) = block_drop n vl
∧ block_drop _ _                           = NONE
End

Theorem v_to_list_DROP:
   !vs ptr ps k v ts.
   v_inv c v (Pointer ptr (Word (ptr_bits c cons_tag 2)),f,tf,heap) /\
   v_to_list v = SOME vs /\
   vs <> [] /\
   walk c heap ptr (LENGTH vs) = ps /\
   ALL_DISTINCT ps /\
   k < LENGTH vs
   ==>
   v_inv c (THE (block_drop k v))
     (Pointer (EL k ps) (Word (ptr_bits c cons_tag 2)),f,tf,heap)
Proof
  Induct >- rw []
  \\ ntac 3 strip_tac
  \\ Induct \\ rw []
  >-
   (Cases_on `vs = []` \\ fs []
    >-
     (fs [v_inv_def,block_drop_def]
      \\ once_rewrite_tac [walk_def] \\ fs [PULL_EXISTS]
      \\ fs [BlockRep_def])
    \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
    \\ fs [] \\ rveq \\ fs []
    \\ qhdtm_x_assum `v_inv` mp_tac
    \\ rw [v_inv_def] \\ fs []
    \\ drule (GEN_ALL v_inv_v_to_list_lemma) \\ fs [] \\ rw []
    \\ first_x_assum drule
    \\ disch_then (qspec_then `0` mp_tac)
    \\ simp [block_drop_def] \\ rw []
    \\ rw [v_inv_def, PULL_EXISTS]
    \\ once_rewrite_tac [walk_def] \\ fs [BlockRep_def])
  \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
  \\ fs [] \\ rveq \\ fs []
  \\ qhdtm_x_assum `v_inv` mp_tac
  \\ rw [v_inv_def] \\ fs []
  \\ Cases_on `vs = []` \\ fs []
  \\ drule (GEN_ALL v_inv_v_to_list_lemma) \\ fs [] \\ rw []
  \\ qpat_x_assum `∀ts. _ ==> _` mp_tac
  \\ simp [v_inv_def, PULL_EXISTS, BlockRep_def]
  \\ first_x_assum drule
  \\ disch_then (qspec_then `k` mp_tac)
  \\ impl_tac
  >-
   (fs [v_to_list_def] \\ rw [] \\ last_x_assum mp_tac
    \\ simp [Once walk_def, BlockRep_def])
  \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once walk_def, BlockRep_def]
  \\ Cases_on `vs` \\ fs []
  \\ qpat_x_assum `v_to_list (Block ts' _ _) = _`  assume_tac
  \\ disch_then (first_x_assum o mp_then Any mp_tac)
  \\ Cases_on `k = 0` \\ fs []
  >- (rw [] \\ once_rewrite_tac [ONE]
     \\ fs [block_drop_def,v_inv_def]
     \\ simp [v_inv_def, PULL_EXISTS, BlockRep_def, Once walk_def])
  \\ strip_tac
  \\ Cases_on `k` \\ fs []
  \\ once_rewrite_tac [walk_def] \\ fs [BlockRep_def]
  \\ fs [block_drop_def]
QED

Theorem block_drop_DROP:
  ∀n v vs. v_to_list v = SOME vs ∧ n < LENGTH vs
  ⇒ v_to_list (THE (block_drop n v)) = SOME (DROP n vs)
Proof
 Induct \\ rw [block_drop_def,DROP]
 \\ Cases_on `vs` \\ fs []
 \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
 \\ fs [] \\ rveq \\ fs [block_drop_def]
QED

Theorem walk_ALL_DISTINCT:
   !vs ptr ps v ts.
     v_inv c v (Pointer ptr (Word (ptr_bits c cons_tag 2)),f,tf,heap) /\
     v_to_list v = SOME vs /\
     vs <> [] /\
     walk c heap ptr (LENGTH vs) = ps
     ==>
     ALL_DISTINCT ps
Proof
  Induct \\ rw []
  \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
  \\ fs [] \\ rveq \\ fs []
  \\ fs [v_inv_def] \\ rveq \\ fs []
  \\ rename1 `(y,f,tf,heap)`
  \\ rename1 `SUC (LENGTH vs)`
  \\ drule (GEN_ALL v_inv_v_to_list_lemma)
  \\ disch_then drule \\ strip_tac
  \\ Cases_on `vs = []` \\ fs [] \\ rveq
  \\ once_rewrite_tac [walk_def] \\ fs [BlockRep_def]
  \\ Cases_on `ptr = p` \\ fs [] \\ rveq
  >-
   (first_x_assum drule \\ rw []
   \\ Cases_on `vs` \\ fs [] \\ rw [Once walk_def]
   \\ drule v_to_list_SOME_CONS_IMP \\ strip_tac
   \\ fs [v_to_list_SOME_NIL_IFF,v_to_list_def] \\ rveq \\ fs [v_to_list_def]
   \\ fs [v_inv_def, BlockRep_def]
   \\ rfs [Once walk_def, BlockRep_def] \\ fs []
   \\ metis_tac [walk_MEM])
  \\ reverse conj_tac
  >- (first_x_assum ho_match_mp_tac \\ asm_exists_tac \\ rw [])
  \\ CCONTR_TAC \\ fs []
  \\ qabbrev_tac `ps = walk c heap p (LENGTH vs)`
  \\ first_x_assum drule \\ disch_then drule \\ strip_tac
  \\ fs [MEM_EL]
  \\ `LENGTH ps = LENGTH vs` by metis_tac [walk_LENGTH]
  \\ sg `v_inv c (THE (block_drop n ys))
           (Pointer ptr (Word (ptr_bits c cons_tag 2)),f,tf,heap)`
  >- (rpt_drule (GEN_ALL v_to_list_DROP) \\ fs [])
  \\ sg `v_inv c (Block ts' cons_tag [h;ys])
           (Pointer ptr (Word (ptr_bits c cons_tag 2)),f,tf,heap)`
  >- rw [v_inv_def, BlockRep_def]
  \\ sg `LENGTH (h::vs) = LENGTH (DROP n vs)`
  >- (drule v_to_list_same_LENGTH \\ disch_then ho_match_mp_tac
     \\ drule_then (qspec_then `n` mp_tac) block_drop_DROP \\ strip_tac
     \\ rfs [] \\ metis_tac [])
  \\ fs [LENGTH_DROP,Abbr`ps`]
QED

Theorem v_to_list_heap_length:
   v_inv c v (x,f,tf,heap) /\
   v_to_list v = SOME vs /\
   vs <> []
   ==>
   3 * LENGTH vs <= heap_length heap
Proof
  metis_tac [walk_heap_lookup, walk_LENGTH, walk_ALL_DISTINCT,
              heap_length_Blocks, v_inv_v_to_list_lemma]
QED

(* ------------------------------------------------------------------------- *)

Theorem memory_rel_list_limit:
   memory_rel c be ts refs sp0 st m dm ((v, (w: 'a word_loc))::vars) /\
   v_to_list v = SOME xs /\
   good_dimindex (:'a)
   ==>
   3 * (LENGTH xs + 1) * (dimindex (:'a) DIV 8) < dimword (:'a)
Proof
  rw [memory_rel_def, word_ml_inv_def, abs_ml_inv_def, bc_stack_ref_inv_def,
      heap_ok_def, heap_in_memory_store_def]
  \\ drule (GEN_ALL v_to_list_heap_length)
  \\ Cases_on `xs` \\ fs [dimword_def, good_dimindex_def] \\ rw [] \\ fs []
QED

Definition build_part_words_def:
  build_part_words c m (Int i) offset =
    (if small_int (:'a) i then  SOME (Word (Smallnum i),[])
     else let (sign,ws) = i2mw i in
            case encode_header c (w2n (b2w sign ≪ 2 ‖ 3w:'a word)) (LENGTH ws) of
            | NONE => NONE
            | SOME hd => SOME (make_ptr c offset (0w:'a word) (LENGTH ws),
                               MAP Word (hd::ws))) ∧
  build_part_words c m (Con t ns) (offset:'a word) =
    (if NULL ns then
       if t < dimword (:'a) DIV 16 then SOME (Word (n2w (16 * t + 2)),[]) else NONE
     else
       case encode_header c (4 * t) (LENGTH ns) of
       | NONE => NONE
       | SOME hd => SOME (make_cons_ptr c offset t (LENGTH ns),
                          Word hd::(MAP m ns))) ∧
  build_part_words c m (W64 w) offset =
    (let ws = (if dimindex (:α) < 64
               then [((63 >< 32) w); ((31 >< 0) w)]
               else [((63 >< 0) w):'a word]) in
       case encode_header c 3 (LENGTH ws) of
       | NONE => NONE
       | SOME hd => SOME (make_ptr c offset (0w:'a word) (LENGTH ws),
                          MAP Word (hd::ws))) ∧
  build_part_words c m (Str s) offset =
    (let bytes = MAP (n2w o ORD) (explode s) in
     let n = LENGTH bytes in
     let hd = make_byte_header c T n in
     let ws = write_bytes bytes (REPLICATE (byte_len (:α) n) 0w) c.be in
       if byte_len (:α) n < 2 ** (dimindex (:α) − 4) ∧
          byte_len (:α) n < 2 ** c.len_size
       then SOME (make_ptr c offset (0w:'a word) (byte_len (:α) n),MAP Word (hd::ws))
       else NONE)
End

Definition build_words_def:
  build_words c m i [] off = SOME (m (i - 1:num), []) ∧
  build_words c m i (x::parts) (off:'a word) =
    case build_part_words c m x off of
    | NONE => NONE
    | SOME (w,xs) =>
      case build_words c ((i =+ w) m) (i+1) parts (off + bytes_in_word * n2w (LENGTH xs)) of
      | NONE => NONE
      | SOME (r,ys) => SOME (r,xs ++ ys)
End

Theorem do_part_SOME_IMP_SOME:
  do_part map0 h refs (SOME ts) = (x,s1,ts1) ⇒ ∃ts'. ts1 = SOME ts'
Proof
  Cases_on ‘h’ \\ rw [do_part_def]
QED

Theorem memory_rel_IMP_MAP_UPDATE:
  memory_rel c be ts refs sp st m dm
          ((b,w) :: MAP (λk. (map0 k, map0' k)) ks ++ vars) ⇒
  memory_rel c be ts refs sp st m dm
          (MAP (λk. (map0⦇i ↦ b⦈ k, (map0'⦇i ↦ w⦈ k))) ks ++ vars)
Proof
  match_mp_tac memory_rel_rearrange
  \\ fs [MEM_MAP] \\ rw [APPLY_UPDATE_THM] \\ fs [] \\ metis_tac []
QED

Triviality ZIP_MAP_MAP:
  ∀xs. ZIP (MAP f xs, MAP g xs) = MAP (λk. (f k, g k)) xs
Proof
  Induct \\ fs []
QED

Triviality LENGTH_n2mw_LE_num_size:
  ∀n m. good_dimindex (:'a) ∧ n ≤ m ⇒ SUC (LENGTH (n2mw n : 'a word list)) ≤ num_size m
Proof
  ho_match_mp_tac multiwordTheory.n2mw_ind \\ rw []
  \\ once_rewrite_tac [multiwordTheory.n2mw_def,data_spaceTheory.num_size_def]
  \\ Cases_on ‘n=0’ \\ fs []
  \\ fs [GSYM ADD1]
  \\ IF_CASES_TAC
  THEN1 (fs [Once multiwordTheory.n2mw_def] \\ gvs [good_dimindex_def,dimword_def,DIV_EQ_X])
  \\ fs [] \\ first_x_assum irule
  \\ match_mp_tac LESS_EQ_TRANS
  \\ qexists_tac ‘n DIV 4294967296’
  \\ fs [DIV_LE_MONOTONE]
  \\ irule multiwordTheory.DIV_thm1
  \\ gvs [good_dimindex_def,dimword_def]
QED

Theorem least_notin_domain:
  (LEAST ptr. ptr ∉ domain refs) ∉ domain (refs:'a num_map)
Proof
  qabbrev_tac ‘pp = λptr. ptr ∉ domain refs’
  \\ qsuff_tac ‘pp ($LEAST pp)’ THEN1 fs [Abbr‘pp’]
  \\ match_mp_tac LEAST_INTRO \\ fs [Abbr‘pp’]
  \\ ‘FINITE (domain refs)’ by fs [FINITE_domain]
  \\ rename [‘FINITE s’]
  \\ CCONTR_TAC \\ gvs []
  \\ assume_tac pred_setTheory.INFINITE_NUM_UNIV
  \\ ‘𝕌(:num) SUBSET s’ by fs [SUBSET_DEF,EXTENSION]
  \\ imp_res_tac SUBSET_FINITE_I
QED

val _ = Parse.hide "free";

Theorem memory_rel_do_build:
  ∀parts i st free curr sp map0 map0' refs ts refs1 v m v ws.
    do_build map0 i parts refs (SOME ts) = (v,refs1,SOME ts1) ∧
    build_words c map0' i parts (free − curr :'a word) = SOME (w,ws) ∧
    SUM (MAP part_space_req parts) ≤ sp ∧
    FLOOKUP st NextFree = SOME (Word free) ∧
    FLOOKUP st CurrHeap = SOME (Word curr) ∧
    (∀ks. memory_rel c be ts refs sp st m dm (MAP (λk. (map0 k, (map0' k))) ks ++ vars)) ∧
    good_dimindex (:'a) ==>
    ∃m1.
      let nf = free + bytes_in_word * n2w (LENGTH ws) in
        memory_rel c be ts1 refs1 (sp − LENGTH ws)
          (st |+ (NextFree,Word nf)) m1 dm ((v,w)::vars) ∧
        store_list free ws m dm = SOME m1
Proof
  Induct
  THEN1
   (fs [do_build_def,build_words_def,store_list_def] \\ rw []
    \\ first_x_assum (qspec_then ‘[i-1]’ mp_tac) \\ fs []
    \\ fs [memory_rel_def]
    \\ rw [] \\ rpt (first_x_assum $ irule_at Any)
    \\ fs [heap_in_memory_store_def,FLOOKUP_UPDATE]
    \\ gvs [])
  \\ fs [do_build_def,build_words_def,store_list_def] \\ rw []
  \\ gvs [AllCaseEqs()]
  \\ pairarg_tac \\ gvs []
  \\ imp_res_tac do_part_SOME_IMP_SOME \\ gvs []
  \\ last_x_assum drule \\ strip_tac
  \\ fs [store_list_append]
  \\ Cases_on ‘∃t. h = Con t []’
  THEN1
   (gvs [do_part_def,AllCaseEqs()]
    \\ gvs [build_part_words_def,data_spaceTheory.part_space_req_def]
    \\ last_x_assum $ drule_then $ drule_then $ drule_then drule
    \\ fs [store_list_def]
    \\ disch_then irule \\ rw []
    \\ irule memory_rel_IMP_MAP_UPDATE
    \\ first_x_assum (qspec_then ‘ks’ assume_tac)
    \\ drule_all memory_rel_Cons_empty
    \\ fs [BlockNil_def,WORD_MUL_LSL,word_mul_n2w,word_add_n2w])
  \\ Cases_on ‘∃n l. h = Con n l’
  THEN1
   (gvs [do_part_def,AllCaseEqs()]
    \\ gvs [build_part_words_def,data_spaceTheory.part_space_req_def,NULL_EQ]
    \\ gvs [AllCaseEqs()]
    \\ qabbrev_tac ‘vals = MAP map0 l’
    \\ qabbrev_tac ‘ws = MAP (map0') l’
    \\ ‘memory_rel c be ts refs sp st m dm (ZIP (vals,ws) ++ vars) ∧
         LENGTH vals = LENGTH ws ∧ LENGTH ws = LENGTH l’ by
           (unabbrev_all_tac \\ fs [ZIP_MAP_MAP])
    \\ drule (GEN_ALL memory_rel_Cons1) \\ fs []
    \\ disch_then (qspec_then ‘n’ mp_tac) \\ fs []
    \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
    \\ strip_tac \\ fs [PULL_EXISTS] \\ fs [MAP_MAP_o]
    \\ qabbrev_tac ‘st1 = (st |+ (NextFree,Word (free + bytes_in_word * n2w (LENGTH l + 1))))’
    \\ first_x_assum (qspec_then ‘st1’ mp_tac)
    \\ fs [Abbr‘st1’] \\ fs [FLOOKUP_UPDATE]
    \\ disch_then (qspec_then ‘sp - SUC (LENGTH l)’ mp_tac)
    \\ rewrite_tac [GSYM SUB_PLUS] \\ fs [ADD1]
    \\ fs [GSYM word_add_n2w,GSYM word_mul_n2w,WORD_LEFT_ADD_DISTRIB,WORD_ADD_ASSOC]
    \\ disch_then irule
    \\ first_x_assum $ irule_at $ Pos last \\ fs []
    \\ rw []
    \\ irule memory_rel_IMP_MAP_UPDATE
    \\ rewrite_tac [make_cons_ptr_def,wordSemTheory.theWord_def]
    \\ rewrite_tac [GSYM make_cons_ptr_def,wordSemTheory.theWord_def]
    \\ ‘memory_rel c be ts refs sp st m dm (ZIP (vals,ws) ++
           (MAP (λk. (map0 k,(map0' k))) ks ++ vars))’ by
           (unabbrev_all_tac \\ fs [ZIP_MAP_MAP]
            \\ last_x_assum (qspec_then ‘l ++ ks’ mp_tac) \\ fs [])
    \\ drule (GEN_ALL memory_rel_Cons1) \\ fs []
    \\ disch_then (qspec_then ‘n’ mp_tac) \\ fs []
    \\ impl_tac THEN1 (CCONTR_TAC \\ fs [])
    \\ fs [GSYM word_add_n2w,GSYM word_mul_n2w,WORD_LEFT_ADD_DISTRIB,WORD_ADD_ASSOC])
  \\ Cases_on ‘∃ww. h = W64 ww’
  THEN1
   (gvs [do_part_def,build_part_words_def,AllCaseEqs()] \\ rw [] \\ fs []
    THEN1
     (qabbrev_tac ‘st1 = (st |+ (NextFree,Word (free + 3w * bytes_in_word)))’
      \\ first_x_assum (qspec_then ‘st1’ mp_tac)
      \\ fs [Abbr‘st1’] \\ fs [FLOOKUP_UPDATE]
      \\ disch_then (qspec_then ‘sp - 3’ mp_tac)
      \\ rewrite_tac [GSYM SUB_PLUS] \\ fs [ADD1,data_spaceTheory.part_space_req_def]
      \\ disch_then drule
      \\ first_assum (qspec_then ‘[]’ (mp_tac o SIMP_RULE std_ss [MAP,APPEND]))
      \\ strip_tac
      \\ drule (memory_rel_Word64_alt |> Q.INST [‘vs’|->‘[]’]
           |> SIMP_RULE std_ss [APPEND] |> GEN_ALL)
      \\ fs [Word64Rep_def]
      \\ disch_then (qspec_then ‘ww’ strip_assume_tac) \\ gvs []
      \\ fs [GSYM word_add_n2w,GSYM word_mul_n2w,WORD_LEFT_ADD_DISTRIB,WORD_ADD_ASSOC]
      \\ disch_then match_mp_tac \\ rw []
      \\ match_mp_tac memory_rel_IMP_MAP_UPDATE
      \\ first_x_assum (qspec_then ‘ks’ assume_tac)
      \\ drule (memory_rel_Word64_alt |> Q.INST [‘vs’|->‘[]’]
           |> SIMP_RULE std_ss [APPEND] |> GEN_ALL)
      \\ fs [Word64Rep_def]
      \\ disch_then (qspec_then ‘ww’ strip_assume_tac) \\ gvs [])
    THEN1
     (qabbrev_tac ‘st1 = (st |+ (NextFree,Word (free + 2w * bytes_in_word)))’
      \\ first_x_assum (qspec_then ‘st1’ mp_tac)
      \\ fs [Abbr‘st1’] \\ fs [FLOOKUP_UPDATE]
      \\ disch_then (qspec_then ‘sp - 2’ mp_tac)
      \\ rewrite_tac [GSYM SUB_PLUS] \\ fs [ADD1,data_spaceTheory.part_space_req_def]
      \\ disch_then drule
      \\ first_assum (qspec_then ‘[]’ (mp_tac o SIMP_RULE std_ss [MAP,APPEND]))
      \\ strip_tac
      \\ drule (memory_rel_Word64_alt |> Q.INST [‘vs’|->‘[]’]
           |> SIMP_RULE std_ss [APPEND] |> GEN_ALL)
      \\ fs [Word64Rep_def]
      \\ disch_then (qspec_then ‘ww’ strip_assume_tac) \\ gvs []
      \\ fs [GSYM word_add_n2w,GSYM word_mul_n2w,WORD_LEFT_ADD_DISTRIB,WORD_ADD_ASSOC]
      \\ disch_then match_mp_tac \\ rw []
      \\ match_mp_tac memory_rel_IMP_MAP_UPDATE
      \\ first_x_assum (qspec_then ‘ks’ assume_tac)
      \\ drule (memory_rel_Word64_alt |> Q.INST [‘vs’|->‘[]’]
           |> SIMP_RULE std_ss [APPEND] |> GEN_ALL)
      \\ fs [Word64Rep_def]
      \\ disch_then (qspec_then ‘ww’ strip_assume_tac) \\ gvs []))
  \\ Cases_on ‘∃j. h = Int j’
  THEN1
   (gvs [] \\ Cases_on ‘small_int (:α) j’ \\ fs []
    THEN1
     (gvs [build_part_words_def,store_list_def,do_part_def]
      \\ first_x_assum irule
      \\ fs [data_spaceTheory.part_space_req_def]
      \\ first_x_assum $ irule_at Any \\ rw []
      \\ first_x_assum (qspec_then ‘ks’ assume_tac)
      \\ match_mp_tac memory_rel_IMP_MAP_UPDATE
      \\ drule_all IMP_memory_rel_Number \\ fs [])
    \\ first_assum (qspec_then ‘[]’ (mp_tac o SIMP_RULE std_ss [MAP,APPEND]))
    \\ strip_tac
    \\ drule (GEN_ALL IMP_memory_rel_bignum_alt) \\ fs []
    \\ fs [Bignum_def]
    \\ disch_then drule
    \\ pairarg_tac \\ fs []
    \\ gvs [build_part_words_def,AllCaseEqs(),data_spaceTheory.part_space_req_def]
    \\ disch_then (qspec_then ‘payload’ mp_tac) \\ fs []
    \\ ‘~(Num (ABS j) < 536870912)’ by
      (Cases_on ‘j’ \\ gvs [small_int_def,good_dimindex_def,dimword_def])
    \\ ‘SUC (LENGTH payload) ≤ num_size (Num (ABS j))’ by
      (gvs [multiwordTheory.i2mw_def] \\ irule LENGTH_n2mw_LE_num_size \\ fs [])
    \\ impl_tac THEN1 fs []
    \\ strip_tac \\ gvs []
    \\ qabbrev_tac ‘st1 = (st |+ (NextFree,Word (free +
                                  bytes_in_word * n2w (SUC (LENGTH payload)))))’
    \\ first_x_assum (qspec_then ‘st1’ mp_tac)
    \\ fs [Abbr‘st1’] \\ fs [FLOOKUP_UPDATE]
    \\ disch_then (qspec_then ‘sp - SUC (LENGTH payload)’ mp_tac)
    \\ fs [GSYM word_add_n2w,GSYM word_mul_n2w,WORD_LEFT_ADD_DISTRIB,WORD_ADD_ASSOC]
    \\ disch_then match_mp_tac \\ rw []
    \\ first_assum $ irule_at Any \\ fs []
    \\ rw []
    \\ match_mp_tac memory_rel_IMP_MAP_UPDATE
    \\ first_x_assum (qspec_then ‘ks’ assume_tac)
    \\ drule (GEN_ALL IMP_memory_rel_bignum_alt) \\ fs []
    \\ disch_then drule
    \\ fs [Bignum_def,ADD1]
    \\ disch_then $ drule_at $ Pos last \\ fs []
    \\ gvs [do_part_def])
  \\ ‘∃z. h = Str z’ by (Cases_on ‘h’ \\ gvs []) \\ gvs []
  \\ gvs [do_part_def,data_spaceTheory.part_space_req_def]
  \\ first_assum (qspec_then ‘[]’ (mp_tac o SIMP_RULE std_ss [MAP,APPEND]))
  \\ strip_tac
  \\ drule (GEN_ALL memory_rel_RefByte_content) \\ fs []
  \\ disch_then (qspecl_then [‘LEAST ptr. ptr ∉ domain refs’,
       ‘T’,‘MAP (n2w ∘ ORD) (explode z)’] mp_tac)
  \\ fs [] \\ impl_keep_tac
  THEN1
   (gvs [build_part_words_def,AllCaseEqs(),least_notin_domain]
    \\ gvs [byte_len_def,good_dimindex_def]
    \\ qsuff_tac ‘strlen z DIV 8 ≤ strlen z DIV 4’ THEN1 gvs []
    \\ irule multiwordTheory.DIV_thm1 \\ fs [])
  \\ strip_tac
  \\ ‘c.be = be’ by
    fs [memory_rel_def,word_ml_inv_def,abs_ml_inv_def,bc_stack_ref_inv_def,be_ok_def]
  \\ gvs [build_part_words_def,AllCaseEqs(),least_notin_domain]
  \\ qabbrev_tac ‘st1 = (st |+ (NextFree,Word (free +
        bytes_in_word * n2w (SUC (byte_len (:α) (strlen z))))))’
  \\ first_x_assum (qspec_then ‘st1’ mp_tac)
  \\ fs [Abbr‘st1’] \\ fs [FLOOKUP_UPDATE]
  \\ disch_then (qspec_then ‘sp - SUC (byte_len (:α) (strlen z))’ mp_tac)
  \\ fs [GSYM word_add_n2w,GSYM word_mul_n2w,WORD_LEFT_ADD_DISTRIB,WORD_ADD_ASSOC]
  \\ disch_then match_mp_tac \\ rw []
  \\ first_assum $ irule_at Any \\ fs []
  \\ conj_tac THEN1
   (gvs [byte_len_def,good_dimindex_def]
    \\ qsuff_tac ‘strlen z DIV 8 ≤ strlen z DIV 4’ THEN1 gvs []
    \\ irule multiwordTheory.DIV_thm1 \\ fs [])
  \\ rw []
  \\ match_mp_tac memory_rel_IMP_MAP_UPDATE
  \\ first_x_assum (qspec_then ‘ks’ assume_tac)
  \\ drule (GEN_ALL memory_rel_RefByte_content) \\ fs []
  \\ disch_then (qspecl_then [‘LEAST ptr. ptr ∉ domain refs’,
       ‘T’,‘MAP (n2w ∘ ORD) (explode z)’] mp_tac)
  \\ fs [] \\ impl_tac THEN1 (fs [least_notin_domain])
  \\ rw [] \\ fs [ADD1]
QED

Theorem word_and_lsr_0:
  (∀i. k ≤ i ∧ i < dimindex (:'a) ⇒ ~w ' i) ⇒ w && n ≪ k = (0w:'a word)
Proof
  fs [fcpTheory.CART_EQ,word_and_def,fcpTheory.FCP_BETA,word_lsl_def]
  \\ rw [] \\ res_tac
  \\ Cases_on ‘i < k’ \\ fs [word_0]
QED

Theorem byte_aligned_IMP_shift:
  byte_aligned (w:'a word) ∧ good_dimindex (:'a) ⇒
  ∃v. w = v << shift (:'a)
Proof
  rw [good_dimindex_def,backend_commonTheory.word_shift_def]
  \\ gvs [byte_aligned_def]
  \\ qexists_tac ‘w >>> (shift (:'a))’
  \\ rw [good_dimindex_def,backend_commonTheory.word_shift_def]
  \\ rewrite_tac [GSYM align_shift]
  \\ fs [align_aligned]
QED

Theorem make_cons_ptr_add:
  byte_aligned n ∧ good_dimindex (:'a) ∧ shift (:α) ≤ shift_length c ⇒
  make_cons_ptr c n tag len =
  Word (n ≪ (shift_length c − shift (:α)) +
        get_lowerbits c (Word (ptr_bits c tag len)) :'a word)
Proof
  strip_tac
  \\ drule_all byte_aligned_IMP_shift \\ rw []
  \\ fs [make_cons_ptr_def,get_lowerbits_def]
  \\ fs [GSYM get_lowerbits_def] \\ rw []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ irule wordsTheory.WORD_ADD_OR
  \\ irule word_and_lsr_0
  \\ fs [get_lowerbits_def]
  \\ fs [fcpTheory.FCP_BETA,word_or_def,word_bits_def,word_index]
  \\ CCONTR_TAC \\ gvs []
  \\ fs [small_shift_length_def,shift_length_def]
QED

Theorem make_ptr_add:
  byte_aligned n ∧ good_dimindex (:'a) ∧ shift (:α) ≤ shift_length c ⇒
  make_ptr c n tag len =
  Word (n ≪ (shift_length c − shift (:'a)) + 1w:'a word)
Proof
  strip_tac
  \\ drule_all byte_aligned_IMP_shift \\ rw []
  \\ rw [make_ptr_def,get_lowerbits_def]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ irule wordsTheory.WORD_ADD_OR
  \\ fs [fcpTheory.FCP_BETA,word_or_def,word_bits_def,word_index,fcpTheory.CART_EQ,
         word_and_def,word_lsl_def,word_0,shift_length_def]
QED

Definition word_cond_add_def[simp]:
  word_cond_add c a (F,x) = (x:'a word_loc) ∧
  word_cond_add c a (T,Word w) = Word (w + a ≪ (shift_length c − shift (:'a))) ∧
  word_cond_add c a (T,other) = other
End

Theorem part_to_words_add:
  ∀part m off a w ws m1.
    byte_aligned off ∧ byte_aligned a ∧
    good_dimindex (:'a) ∧ shift (:α) ≤ shift_length c ⇒
    part_to_words c m part (off:'a word) = SOME (w,ws) ∧
    (∀i. SND (lookup_mem m1 i) = word_cond_add c a (lookup_mem m i)) ⇒
    ∃v vs. part_to_words c m1 part (off + a:'a word) = SOME (v,vs) ∧
           MAP SND vs = MAP (word_cond_add c a) ws ∧
           SND v = word_cond_add c a w
Proof
  Cases
  \\ rw [part_to_words_def] \\ gvs [AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs()]
  \\ ‘byte_aligned (a + off)’ by fs [alignmentTheory.byte_aligned_add]
  \\ drule_all make_cons_ptr_add
  \\ fs [make_cons_ptr_def,get_lowerbits_ptrbits]
  \\ disch_then (assume_tac o GSYM)
  \\ gvs [make_cons_ptr_add,make_ptr_add,wordSemTheory.theWord_def]
  \\ fs [MAP_MAP_o] \\ fs [MAP_EQ_f]
QED

Theorem byte_aligned_bytes_in_word:
  good_dimindex (:'a) ⇒
  byte_aligned (bytes_in_word:'a word)
Proof
  rw [good_dimindex_def,bytes_in_word_def] \\ gvs []
  \\ EVAL_TAC \\ fs [] \\ EVAL_TAC
QED

Theorem byte_align_mult_bytes_in_word:
  good_dimindex (:'a) ⇒
  byte_aligned (w * bytes_in_word:'a word) ∧
  byte_aligned (bytes_in_word * w:'a word)
Proof
  qsuff_tac ‘good_dimindex (:'a) ⇒ byte_aligned (w * bytes_in_word:'a word)’
  THEN1 (simp [] \\ fs [])
  \\ Cases_on ‘w’ \\ Induct_on ‘n’ \\ fs [] THEN1 EVAL_TAC
  \\ rw [] \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ irule byte_aligned_add \\ fs [byte_aligned_bytes_in_word]
QED

Theorem parts_to_words_add:
  ∀parts m i off a w ws m1.
    parts_to_words c m i parts (off:'a word) = SOME (w,ws) ∧
    byte_aligned off ∧ byte_aligned a ∧
    good_dimindex (:'a) ∧ shift (:α) ≤ shift_length c ∧
    (∀i. SND (lookup_mem m1 i) = word_cond_add c a (lookup_mem m i)) ⇒
    ∃v vs. parts_to_words c m1 i parts (off + a:'a word) = SOME (v,vs) ∧
           MAP SND vs = MAP (word_cond_add c a) ws ∧
           SND v = word_cond_add c a w
Proof
  Induct \\ fs [parts_to_words_def]
  \\ fs [AllCaseEqs()] \\ rw [PULL_EXISTS]
  \\ drule_all part_to_words_add
  \\ rw [] \\ fs []
  \\ first_x_assum drule
  \\ disch_then (qspecl_then [‘a’,‘insert i v m1’] mp_tac)
  \\ impl_tac
  THEN1
   (fs [lookup_mem_def,lookup_insert] \\ rw []
    \\ irule byte_aligned_add \\ fs [byte_align_mult_bytes_in_word])
  \\ strip_tac \\ fs []
  \\ ‘LENGTH (MAP SND vs) = LENGTH (MAP (word_cond_add c a) xs)’ by asm_rewrite_tac []
  \\ fs []
QED

Theorem part_to_words_IMP_build_words:
  part_to_words c m p (off:'a word) = SOME (w,ws) ∧ good_dimindex (:'a) ∧
  byte_aligned off ∧ shift (:α) ≤ shift_length c ⇒
  build_part_words c (λi. SND (lookup_mem m i)) p off = SOME (SND w,MAP SND ws)
Proof
  Cases_on ‘p’
  \\ fs [part_to_words_def,build_part_words_def]
  \\ rw [] \\ gvs [AllCaseEqs()]
  \\ gvs [MAP_MAP_o,o_DEF]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs()]
  \\ gvs [MAP_MAP_o,o_DEF,SF ETA_ss]
  \\ fs [make_cons_ptr_add,get_lowerbits_ptrbits]
  \\ Cases_on ‘sign’ \\ fs [b2w_def,WORD_MUL_LSL]
  \\ gvs [good_dimindex_def,dimword_def]
QED

Theorem parts_to_words_IMP_build_words:
  ∀c m i parts (off:'a word) w ws.
    parts_to_words c m i parts off = SOME (w,ws) ∧ good_dimindex (:'a) ∧
    byte_aligned off ∧ shift (:α) ≤ shift_length c ⇒
    build_words c (λi. SND (lookup_mem m i)) i parts off = SOME (SND w,MAP SND ws)
Proof
  Induct_on ‘parts’ \\ fs [parts_to_words_def,build_words_def]
  \\ fs [AllCaseEqs()] \\ rw [] \\ fs [PULL_EXISTS]
  \\ drule_all part_to_words_IMP_build_words \\ fs []
  \\ last_x_assum drule \\ fs []
  \\ impl_tac THEN1
   (irule byte_aligned_add
    \\ fs [byte_align_mult_bytes_in_word])
  \\ strip_tac
  \\ pop_assum (fn th => once_rewrite_tac [GSYM th])
  \\ strip_tac
  \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
  \\ rw [FUN_EQ_THM,lookup_mem_def,lookup_insert,APPLY_UPDATE_THM]
  \\ rw [FUN_EQ_THM,lookup_mem_def,lookup_insert,APPLY_UPDATE_THM]
QED

Theorem LESS_EQ_num_size:
  good_dimindex (:α) ⇒
  ∀m n. n ≤ m ⇒ SUC (LENGTH (n2mw n:'a word list)) ≤ num_size m
Proof
  strip_tac
  \\ ho_match_mp_tac data_spaceTheory.num_size_ind
  \\ rw []
  \\ simp [Once data_spaceTheory.num_size_def]
  \\ once_rewrite_tac [multiwordTheory.n2mw_def]
  \\ IF_CASES_TAC \\ fs []
  \\ IF_CASES_TAC \\ fs []
  THEN1
   (fs [good_dimindex_def,dimword_def,LESS_DIV_EQ_ZERO]
    \\ once_rewrite_tac [multiwordTheory.n2mw_def] \\ fs [])
  \\ fs [GSYM ADD1]
  \\ last_x_assum irule
  \\ irule LESS_EQ_TRANS
  \\ qexists_tac ‘n DIV 4294967296’
  \\ irule_at Any DIV_LE_MONOTONE \\  fs[]
  \\ irule multiwordTheory.DIV_thm1 \\ fs []
  \\ fs [good_dimindex_def,dimword_def,LESS_DIV_EQ_ZERO]
QED

Theorem part_to_words_LENGTH:
  part_to_words c m h a = SOME ((w:bool # 'a word_loc),ws) ∧
  good_dimindex (:'a) ⇒
  LENGTH ws ≤ part_space_req h
Proof
  Cases_on ‘h’ \\ fs [part_to_words_def,AllCaseEqs()]
  \\ strip_tac \\ gvs [wordSemTheory.isWord_def,data_spaceTheory.part_space_req_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ TRY (Cases_on ‘l’) \\ fs [make_cons_ptr_def,wordSemTheory.isWord_def,EVERY_MAP,make_ptr_def]
  \\ gvs [AllCaseEqs(),wordSemTheory.isWord_def,EVERY_MAP]
  \\ rw [] \\ gvs []
  THEN1 (gvs [small_int_def,good_dimindex_def,dimword_def] \\ intLib.COOPER_TAC)
  \\ TRY (gvs [byte_len_def,good_dimindex_def,dimword_def,ADD1]
          \\ irule multiwordTheory.DIV_thm1 \\ fs [])
  \\ gvs [multiwordTheory.i2mw_def]
  \\ irule LESS_EQ_num_size \\ fs []
QED

Theorem const_parts_to_words_LENGTH:
  const_parts_to_words c parts = SOME ((w:bool # 'a word_loc),ws) ∧
  good_dimindex (:'a) ⇒
  LENGTH ws ≤ SUM (MAP part_space_req parts)
Proof
  fs [const_parts_to_words_def]
  \\ qpat_abbrev_tac ‘m = LN’
  \\ last_x_assum kall_tac
  \\ rename [‘parts_to_words c _ k parts a’]
  \\ EVERY (map qid_spec_tac [‘m’,‘c’,‘k’,‘parts’,‘a’,‘w’,‘ws’])
  \\ rewrite_tac [AND_IMP_INTRO]
  \\ Induct_on ‘parts’
  \\ fs [parts_to_words_def]
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [AllCaseEqs()]
  \\ drule part_to_words_LENGTH \\ fs []
  \\ strip_tac
  \\ last_x_assum (drule_at Any)
  \\ rw [lookup_mem_def,lookup_insert]
  \\ CASE_TAC \\ fs [wordSemTheory.isWord_def,lookup_mem_def]
  \\ last_x_assum (qspec_then ‘k'’ mp_tac) \\ fs []
QED

Definition good_loc_def:
  good_loc code (Loc n m) = (m = 0 ∧ n IN code) ∧
  good_loc _ _ = T
End

Theorem const_parts_to_words_good_loc:
  const_parts_to_words c parts = SOME ((y0,y1),y2) ⇒
  good_loc s y1 ∧ EVERY (good_loc s ∘ SND) y2
Proof
  fs [const_parts_to_words_def]
  \\ qpat_abbrev_tac ‘m = LN’
  \\ ‘∀y0 y1 k. lookup_mem m k = (y0,y1) ⇒ good_loc s y1’ by
         fs [Abbr‘m’,lookup_mem_def,lookup_def,good_loc_def]
  \\ pop_assum mp_tac
  \\ last_x_assum kall_tac
  \\ rename [‘parts_to_words c _ k parts a’]
  \\ EVERY (map qid_spec_tac [‘m’,‘c’,‘k’,‘parts’,‘a’,‘y1’,‘y0’,‘y2’])
  \\ rewrite_tac [AND_IMP_INTRO]
  \\ Induct_on ‘parts’
  \\ fs [parts_to_words_def]
  THEN1 (rw [] \\ res_tac \\ fs [])
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [AllCaseEqs()]
  \\ last_x_assum (drule_at (Pos $ el 2))
  \\ qsuff_tac ‘EVERY (good_loc s ∘ SND) xs ∧ good_loc s (SND w)’
  THEN1
   (strip_tac \\ fs [] \\ impl_tac \\ fs []
    \\ fs [lookup_mem_def,lookup_insert] \\ rw []
    \\ gvs [AllCaseEqs(),good_loc_def] \\ res_tac \\ fs [])
  \\ Cases_on ‘h’ \\ gvs [part_to_words_def,AllCaseEqs(),good_loc_def]
  \\ rpt (pairarg_tac \\ gvs [AllCaseEqs()])
  \\ fs [make_ptr_def,good_loc_def,EVERY_MAP]
  \\ fs [EVERY_MEM] \\ rw []
  \\ Cases_on ‘lookup_mem m x’ \\ res_tac \\ fs []
QED

Theorem memory_rel_do_build_const:
  do_build_const parts refs (SOME ts) = (v,refs1,SOME ts1) ∧
  const_parts_to_words c parts = SOME (w,ws) ∧
  memory_rel c be ts refs sp st m dm vars ∧
  SUM (MAP part_space_req parts) ≤ sp ∧
  FLOOKUP st NextFree = SOME (Word free) ∧
  FLOOKUP st CurrHeap = SOME (Word curr) ∧
  good_dimindex (:'a) ==>
  ∃m1.
    let nf = free + bytes_in_word * n2w (LENGTH ws) in
    let adjust = word_cond_add c (free − curr :'a word) in
      memory_rel c be ts1 refs1 (sp − LENGTH ws)
        (st |+ (NextFree,Word nf)) m1 dm ((v,adjust w)::vars) ∧
      store_list free (MAP adjust ws) m dm = SOME m1
Proof
  assume_tac (GEN_ALL memory_rel_do_build) \\ fs []
  \\ strip_tac
  \\ qabbrev_tac ‘ws1 = (MAP (word_cond_add c (free - curr)) ws)’
  \\ fs []
  \\ ‘LENGTH ws = LENGTH ws1’ by fs [Abbr ‘ws1’]
  \\ fs []
  \\ last_x_assum irule \\ fs []
  \\ fs [do_build_const_def]
  \\ last_x_assum $ irule_at Any
  \\ qexists_tac ‘(λn. Word 0w)’ \\ fs []
  \\ conj_tac
  THEN1
   (Induct \\ fs []
    \\ (IMP_memory_rel_Number |> Q.INST [‘i’|->‘0’]
          |> SIMP_RULE std_ss [EVAL “Smallnum 0”] |> irule) \\ fs []
    \\ EVAL_TAC \\ fs [good_dimindex_def,dimword_def])
  \\ fs [const_parts_to_words_def]
  \\ drule_at Any parts_to_words_add
  \\ disch_then drule
  \\ fs [word_cond_add_def]
  \\ disch_then (qspecl_then [‘free-curr’,‘LN’] mp_tac)
  \\ impl_tac THEN1
   (fs [lookup_mem_def,lookup_def]
    \\ qsuff_tac ‘byte_aligned (free - curr)’
    THEN1 (fs [memory_rel_def,heap_in_memory_store_def] \\ EVAL_TAC)
    \\ ‘byte_aligned free ∧ byte_aligned curr’ by
         (gvs [memory_rel_def,heap_in_memory_store_def]
          \\ irule byte_aligned_add
          \\ fs [byte_align_mult_bytes_in_word])
    \\ ntac 2 (pop_assum mp_tac)
    \\ rewrite_tac [byte_aligned_def]
    \\ rpt strip_tac
    \\ imp_res_tac aligned_add_sub_cor)
  \\ strip_tac
  \\ drule parts_to_words_IMP_build_words \\ fs [lookup_mem_def,lookup_def]
  \\ disch_then irule
  \\ fs [memory_rel_def,heap_in_memory_store_def,byte_align_mult_bytes_in_word]
QED

Definition read_word_def:
  read_word dm m a = (theWord (m a), a ∈ dm ∧ isWord (m a))
End

Definition word_xor_bytes_def:
  word_xor_bytes (a1:'a word) (a2:'a word) (len:'a word) dm m =
    if len <+ 2w ∨ ~ good_dimindex (:'a) then
      if len = 0w then SOME m else
        let (w1a,c1) = read_word dm m a1 in
        let (w2a,c2) = read_word dm m a2 in
        let a = word_xor w1a w2a in
        let m = (a2 =+ Word (a:'a word)) m in
          if c1 ∧ c2 then SOME m else NONE
    else
      let (w1a,c1) = read_word dm m a1 in
      let (w2a,c2) = read_word dm m a2 in
      let (w1b,c3) = read_word dm m (a1 + bytes_in_word) in
      let (w2b,c4) = read_word dm m (a2 + bytes_in_word) in
      let a = word_xor w1a w2a in
      let b = word_xor w1b w2b in
      let m = (a2 + bytes_in_word =+ Word b) ((a2 =+ Word a) m) in
        if c1 ∧ c2 ∧ c3 ∧ c4 then
          word_xor_bytes (a1 + 2w * bytes_in_word) (a2 + 2w * bytes_in_word)
            (len - 2w) dm m
        else NONE
Termination
  WF_REL_TAC ‘measure $ λ(a1,a2,len,dm,m). w2n len’
  \\ Cases_on ‘len’ \\ gvs [WORD_LO]
  \\ rewrite_tac [GSYM word_sub_def,addressTheory.word_arith_lemma2]
  \\ Cases_on ‘good_dimindex (:α)’ \\ simp []
  \\ gvs [dimword_def,good_dimindex_def]
End

Definition make_zeros_def:
  make_zeros (vals:word8 list) =
    REPLICATE (LENGTH vals DIV (dimindex (:α) DIV 8) + 1) (0w:'a word)
End

Definition xor_words_def:
  xor_words [] ys = SOME ys ∧
  xor_words xs [] = NONE ∧
  xor_words (x::xs) (y::ys) =
    case xor_words xs ys of
    | NONE => NONE
    | SOME rest => SOME (word_xor (x:'a word) y :: rest)
End

Theorem word_xor_set_byte:
  word_xor (set_byte a h1 w1 be) (set_byte a h2 w2 be) =
  set_byte a (word_xor h1 h2) (word_xor w1 w2) be
Proof
  gvs [set_byte_def,fcpTheory.CART_EQ,word_or_def,fcpTheory.FCP_BETA,
      word_lsl_def,w2w,word_xor_def,word_slice_alt_def,SF CONJ_ss]
  \\ rpt strip_tac
  \\ Cases_on ‘h1 ' (i − byte_index a be)’
  \\ Cases_on ‘h2 ' (i − byte_index a be)’
  \\ Cases_on ‘w1 ' i’
  \\ Cases_on ‘w2 ' i’
  \\ gvs []
QED

Triviality xor_bytes_bytes_to_word:
  ∀k vals1 vals2 res_vals a.
    xor_bytes vals1 vals2 = SOME res_vals ⇒
    bytes_to_word k a vals1 0w be ⊕
    bytes_to_word k a vals2 0w be =
    bytes_to_word k a res_vals 0w be
Proof
  Induct \\ gvs []
  \\ once_rewrite_tac [bytes_to_word_def] \\ simp []
  \\ Cases \\ Cases_on ‘vals2’ \\ simp [semanticPrimitivesTheory.xor_bytes_def]
  \\ simp [CaseEq"option",PULL_EXISTS]
  \\ rpt strip_tac
  \\ last_x_assum drule
  \\ disch_then $ rewrite_tac o single o GSYM
  \\ gvs [word_xor_set_byte]
QED

Theorem xor_bytes_length:
  ∀xs ys zs.
    xor_bytes xs ys = SOME zs ⇒
    LENGTH xs ≤ LENGTH zs ∧ LENGTH zs = LENGTH ys
Proof
  Induct \\ Cases_on ‘ys’ \\ gvs [semanticPrimitivesTheory.xor_bytes_def]
  \\ rw [CaseEq"option"] \\ gvs [] \\ res_tac \\ gvs []
QED

Triviality xor_bytes_drop:
  ∀n xs ys zs.
    xor_bytes xs ys = SOME zs ⇒
    xor_bytes (DROP n xs) (DROP n ys) = SOME (DROP n zs)
Proof
  Induct_on ‘xs’ \\ Cases_on ‘ys’ \\ gvs [semanticPrimitivesTheory.xor_bytes_def]
  \\ Cases_on ‘n’ \\ gvs []  \\ gvs []
  \\ gvs [semanticPrimitivesTheory.xor_bytes_def,CaseEq"option"]
  \\ rw [] \\ gvs []
QED

Triviality xor_bytes_xor_words:
  ∀zs1 zs2 vals1 vals2 res_vals.
    xor_bytes vals1 vals2 = SOME res_vals ∧ good_dimindex (:'a) ∧
    EVERY (λw. w = 0w) zs1 ∧ EVERY (λw. w = 0w) zs2 ∧
    LENGTH zs1 = LENGTH vals1 DIV (dimindex (:α) DIV 8) + 1 ∧
    LENGTH zs2 = LENGTH vals2 DIV (dimindex (:α) DIV 8) + 1 ⇒
    xor_words (write_bytes vals1 zs1 be)
              (write_bytes vals2 zs2 be) =
    SOME (write_bytes res_vals zs2 be : 'a word list)
Proof
  Cases_on ‘good_dimindex (:'a)’ \\ fs []
  \\ Induct_on ‘zs1’ \\ Cases_on ‘zs2’ \\ gvs []
  \\ rpt strip_tac \\ gvs [ADD1]
  \\ gvs [write_bytes_def,xor_words_def,CaseEq"option"]
  \\ irule_at Any xor_bytes_bytes_to_word
  \\ simp []
  \\ drule xor_bytes_drop
  \\ disch_then $ qspec_then ‘dimindex (:α) DIV 8’ assume_tac
  \\ Cases_on ‘LENGTH vals1 < (dimindex (:α) DIV 8)’
  >- (gvs [LESS_DIV_EQ_ZERO]
      \\ ‘DROP (dimindex (:α) DIV 8) vals1 = []’ by
           (irule DROP_LENGTH_TOO_LONG \\ gvs [])
      \\ gvs [write_bytes_def,xor_words_def,semanticPrimitivesTheory.xor_bytes_def])
  \\ gvs [NOT_LESS]
  \\ last_x_assum irule \\ gvs []
  \\ ‘dimindex (:α) DIV 8 ≤ LENGTH vals2’ by
    (imp_res_tac xor_bytes_length \\ decide_tac)
  \\ imp_res_tac LESS_EQ_LENGTH \\ gvs []
  \\ DEP_REWRITE_TAC [ADD_DIV_EQ]
  \\ gvs [good_dimindex_def]
QED

Theorem xor_bytes_xor_words:
  xor_bytes vals1 vals2 = SOME res_vals ∧ good_dimindex (:'a) ⇒
  xor_words (write_bytes vals1 (make_zeros vals1) be)
            (write_bytes vals2 (make_zeros vals2) be) =
  SOME (write_bytes res_vals (make_zeros vals2) be : 'a word list)
Proof
  rw [] \\ irule xor_bytes_xor_words \\ gvs []
  \\ simp [make_zeros_def]
  \\ DEP_REWRITE_TAC [GSYM DIV_LT_X]
  \\ simp [] \\ gvs [good_dimindex_def]
QED

Theorem xor_words_word_list:
  ∀vals1 vals2 res_vals a1 a2 be frame m.
    xor_words vals1 vals2 = SOME res_vals ∧
    good_dimindex (:'a) ∧ LENGTH vals1 < dimword (:'a) ∧
    (word_list a1 (MAP Word vals1) *
     word_list a2 (MAP Word vals2) *
     frame) (fun2set (m,dm)) ⇒
    ∃m1.
      (word_list a1 (MAP Word vals1) *
       word_list a2 (MAP Word res_vals) *
       frame) (fun2set (m1,dm: 'a word set)) ∧
      word_xor_bytes a1 a2 (n2w (LENGTH vals1)) dm m = SOME m1
Proof
  gen_tac \\ completeInduct_on ‘LENGTH vals1’
  \\ rpt strip_tac \\ gvs [PULL_FORALL]
  \\ Cases_on ‘vals1’ \\ gvs [xor_words_def]
  >-
   (simp [Once word_xor_bytes_def]
    \\ gvs [good_dimindex_def,WORD_LO,dimword_def])
  \\ Cases_on ‘vals2’ \\ gvs [xor_words_def,CaseEq"option"]
  \\ rename [‘xor_words xs ys = SOME zs’]
  \\ Cases_on ‘xs’
  >-
   (simp [Once word_xor_bytes_def,WORD_LO]
    \\ reverse IF_CASES_TAC
    >-
     (qsuff_tac ‘F’ >- fs []
      \\ gvs [good_dimindex_def,WORD_LO,dimword_def])
    \\ gvs [word_list_def,SEP_CLAUSES,read_word_def]
    \\ SEP_R_TAC \\ gvs [isWord_def,theWord_def]
    \\ SEP_W_TAC \\ gvs [AC STAR_ASSOC STAR_COMM]
    \\ gvs [xor_words_def])
  \\ Cases_on ‘ys’ \\ gvs [xor_words_def,CaseEq"option"]
  \\ rename [‘xor_words xs ys = SOME zs’]
  \\ simp [Once word_xor_bytes_def]
  \\ IF_CASES_TAC
  >-
   (qsuff_tac ‘F’ >- fs []
    \\ gvs [good_dimindex_def,WORD_LO,dimword_def])
  \\ gvs [word_list_def,SEP_CLAUSES,read_word_def]
  \\ SEP_R_TAC \\ gvs [isWord_def,theWord_def]
  \\ simp [ADD1,GSYM word_add_n2w]
  \\ SEP_W_TAC
  \\ last_x_assum $ drule_at $ Pos $ el 2
  \\ simp []
  \\ disch_then $ qspecl_then [‘a1 + 2w * bytes_in_word’,‘a2 + 2w * bytes_in_word’] assume_tac
  \\ SEP_F_TAC
  \\ strip_tac \\ gvs []
  \\ gvs [AC STAR_ASSOC STAR_COMM]
QED

Theorem xor_words_word_list_alias:
  ∀vals1 res_vals a1 be frame m.
    xor_words vals1 vals1 = SOME res_vals ∧
    good_dimindex (:'a) ∧ LENGTH vals1 < dimword (:'a) ∧
    (word_list a1 (MAP Word vals1) *
     frame) (fun2set (m,dm)) ⇒
    ∃m1.
      (word_list a1 (MAP Word res_vals) *
       frame) (fun2set (m1,dm: 'a word set)) ∧
      word_xor_bytes a1 a1 (n2w (LENGTH vals1)) dm m = SOME m1
Proof
  gen_tac \\ completeInduct_on ‘LENGTH vals1’
  \\ rpt strip_tac \\ gvs [PULL_FORALL]
  \\ Cases_on ‘vals1’ \\ gvs [xor_words_def]
  >-
   (simp [Once word_xor_bytes_def]
    \\ gvs [good_dimindex_def,WORD_LO,dimword_def])
  \\ gvs [xor_words_def,CaseEq"option"]
  \\ rename [‘xor_words xs _ = SOME zs’]
  \\ Cases_on ‘xs’
  >-
   (simp [Once word_xor_bytes_def]
    \\ reverse IF_CASES_TAC
    >-
     (qsuff_tac ‘F’ >- fs []
      \\ gvs [good_dimindex_def,WORD_LO,dimword_def])
    \\ gvs [word_list_def,SEP_CLAUSES,read_word_def,xor_words_def]
    \\ SEP_R_TAC \\ gvs [isWord_def,theWord_def]
    \\ SEP_W_TAC \\ gvs [AC STAR_ASSOC STAR_COMM]
    \\ gvs [xor_words_def])
  \\ gvs [xor_words_def,CaseEq"option"]
  \\ rename [‘xor_words xs _ = SOME zs’]
  \\ simp [Once word_xor_bytes_def]
  \\ IF_CASES_TAC
  >-
   (qsuff_tac ‘F’ >- fs []
    \\ gvs [good_dimindex_def,WORD_LO,dimword_def])
  \\ gvs [word_list_def,SEP_CLAUSES,read_word_def]
  \\ SEP_R_TAC \\ gvs [isWord_def,theWord_def]
  \\ simp [ADD1,GSYM word_add_n2w]
  \\ SEP_W_TAC
  \\ last_x_assum $ drule_at $ Pos $ el 2
  \\ simp []
  \\ disch_then $ qspecl_then [‘a1 + 2w * bytes_in_word’] assume_tac
  \\ SEP_F_TAC
  \\ strip_tac \\ gvs []
  \\ gvs [AC STAR_ASSOC STAR_COMM]
QED

Theorem xor_bytes_word_list:
  ∀a1 a2 be frame.
    xor_bytes vals1 vals2 = SOME res_vals ∧
    good_dimindex (:'a) ∧ LENGTH (make_zeros vals1 :'a word list) < dimword (:'a) ∧
    (word_list a1 (MAP Word (write_bytes vals1 (make_zeros vals1) be)) *
     word_list a2 (MAP Word (write_bytes vals2 (make_zeros vals2) be)) *
     frame) (fun2set (m,dm)) ⇒
    ∃m1.
      (word_list a1 (MAP Word (write_bytes vals1 (make_zeros vals1 :'a word list) be)) *
       word_list a2 (MAP Word (write_bytes res_vals (make_zeros vals2 :'a word list) be)) *
       frame) (fun2set (m1,dm: 'a word set)) ∧
      word_xor_bytes a1 a2 (n2w (LENGTH (make_zeros vals1 :'a word list))) dm m = SOME m1
Proof
  rpt strip_tac
  \\ drule_at (Pos last) xor_words_word_list
  \\ rewrite_tac [LENGTH_write_bytes]
  \\ disch_then irule
  \\ asm_rewrite_tac []
  \\ irule xor_bytes_xor_words
  \\ asm_rewrite_tac []
QED

Theorem xor_bytes_word_list_alias:
  ∀a1 be frame.
    xor_bytes vals1 vals1 = SOME res_vals1 ∧
    good_dimindex (:'a) ∧ LENGTH (make_zeros vals1 :'a word list) < dimword (:'a) ∧
    (word_list a1 (MAP Word (write_bytes vals1 (make_zeros vals1) be)) *
     frame) (fun2set (m,dm)) ⇒
    ∃m1.
      (word_list a1 (MAP Word (write_bytes res_vals1 (make_zeros vals1 :'a word list) be)) *
       frame) (fun2set (m1,dm: 'a word set)) ∧
      word_xor_bytes a1 a1 (n2w (LENGTH (make_zeros vals1 :'a word list))) dm m = SOME m1
Proof
  rpt strip_tac
  \\ drule_at (Pos last) xor_words_word_list_alias
  \\ rewrite_tac [LENGTH_write_bytes]
  \\ disch_then irule
  \\ asm_rewrite_tac []
  \\ irule xor_bytes_xor_words
  \\ asm_rewrite_tac []
QED

(*
Theorem xor_bytes_length:
  ∀xs ys zs. xor_bytes xs ys = SOME zs ⇒ LENGTH zs = LENGTH ys
Proof
  Induct \\ Cases_on ‘ys’ \\ gvs [semanticPrimitivesTheory.xor_bytes_def,AllCaseEqs()]
  \\ rw [] \\ gvs []
QED
*)

Theorem el_length_Bytes:
  el_length (Bytes be fl vals zeros) = LENGTH zeros + 1
Proof
  gvs [el_length_def,Bytes_def]
QED

Triviality v_inv_alt_ind =
  v_inv_ind |> Q.SPEC ‘λx (a,b,c,d). P x a’ |> SRULE [];

Theorem memory_rel_xor_bytes:
   memory_rel c be ts refs sp st m dm
     ((RefPtr bl1 p1,v1:'a word_loc)::(RefPtr bl2 p2,v2:'a word_loc)::vars) ∧
   lookup p1 refs = SOME (ByteArray fl1 vals1) ∧
   lookup p2 refs = SOME (ByteArray fl2 vals2) ∧
   xor_bytes vals1 vals2 = SOME res_vals ∧
   good_dimindex (:'a)
   ⇒
   ?w1 a1 w2 a2 x1 m1.
     v1 = Word w1 ∧
     v2 = Word w2 ∧
     get_real_addr c st w1 = SOME a1 ∧
     get_real_addr c st w2 = SOME a2 ∧
     m a1 = Word x1 ∧ a1 ∈ dm ∧
     word_xor_bytes (a1 + bytes_in_word) (a2 + bytes_in_word)
                    (decode_length c x1) dm m = SOME m1 ∧
     memory_rel c be ts (insert p2 (ByteArray fl2 res_vals) refs) sp st m1 dm
       ((RefPtr bl1 p1,v1:'a word_loc)::(RefPtr bl2 p2,v2:'a word_loc)::vars)
Proof
  strip_tac
  \\ ‘∃w2 a2. v2 = Word w2 ∧ get_real_addr c st w2 = SOME a2’ by
    (drule memory_rel_tl \\ strip_tac
     \\ drule_all memory_rel_ByteArray_IMP \\ strip_tac \\ simp [])
  \\ ‘∃w1 a1 x1.
        v1 = Word w1 ∧ get_real_addr c st w1 = SOME a1 ∧
        LENGTH (make_zeros vals1 :'a word list) < dimword (:'a) ∧
        m a1 = Word x1 ∧ a1 ∈ dm’ by
    (drule_all memory_rel_ByteArray_IMP \\ strip_tac \\ simp []
     \\ gvs [make_zeros_def,good_dimindex_def,dimword_def]
     \\ irule $ DECIDE “l ≠ 0 ∧ n < l - 1 ⇒ n + 1 < l:num”
     \\ gvs [DIV_LT_X])
  \\ gvs [memory_rel_def,PULL_EXISTS]
  \\ first_assum $ irule_at $ Pos last
  \\ first_assum $ irule_at $ Pos last
  \\ qrefinel [‘sp1’,‘_’,‘_’,‘gens’,‘a’]
  \\ gvs [word_ml_inv_def,PULL_EXISTS]
  \\ first_assum $ irule_at $ Pos last
  \\ first_assum $ irule_at $ Pos last
  \\ first_assum $ irule_at $ Pos last
  \\ gvs [abs_ml_inv_def,bc_stack_ref_inv_def,PULL_EXISTS]
  \\ qrefinel [‘_’,‘_’,‘f’,‘tf’] \\ gvs []
  \\ ‘∃curr. FLOOKUP st CurrHeap = SOME (Word curr) ∧
             heap_length heap ≤ dimword (:α) DIV 2 ** shift_length c’ by
    gvs [heap_in_memory_store_def]
  \\ ‘bc_ref_inv c p1 refs (f,tf,heap,be) ∧
      bc_ref_inv c p2 refs (f,tf,heap,be)’ by
   (conj_tac
    \\ first_x_assum irule
    \\ gvs [reachable_refs_def,SF DNF_ss,get_refs_def])
  \\ pop_assum mp_tac \\ simp [Once bc_ref_inv_def]
  \\ Cases_on ‘FLOOKUP f p2’ \\ gvs []
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac \\ simp [Once bc_ref_inv_def]
  \\ Cases_on ‘FLOOKUP f p1’ \\ gvs []
  \\ rpt strip_tac
  \\ gvs [GSYM make_zeros_def]
  \\ drule_all get_real_addr_get_addr
  \\ pop_assum mp_tac
  \\ drule_all get_real_addr_get_addr
  \\ rpt strip_tac \\ gvs []
  \\ gvs [v_inv_def,word_addr_def]
  \\ gvs [TO_FLOOKUP,FLOOKUP_SIMP]
  \\ rename [‘word_xor_bytes (curr + bytes_in_word + bytes_in_word * n2w k1)
                             (curr + bytes_in_word + bytes_in_word * n2w k2)’]
  \\ ntac 2 $ qpat_x_assum ‘∀w. _’ kall_tac
  \\ ‘decode_length c x1 = n2w (LENGTH (make_zeros vals1 :'a word list))’ by
   (qpat_x_assum ‘heap_lookup k1 _ = _’ assume_tac
    \\ dxrule heap_lookup_SPLIT \\ strip_tac
    \\ last_x_assum mp_tac
    \\ simp [heap_in_memory_store_def,word_heap_APPEND,word_heap_def]
    \\ strip_tac \\ pop_assum mp_tac
    \\ simp [Bytes_def,word_el_def,word_payload_def]
    \\ simp_tac (std_ss++sep_cond_ss) [cond_STAR,word_list_def]
    \\ strip_tac
    \\ qpat_x_assum ‘m _ = Word x1’ mp_tac
    \\ SEP_R_TAC \\ strip_tac \\ gvs [])
  \\ qmatch_goalsub_abbrev_tac ‘word_xor_bytes a1 a2’
  \\ dxrule heap_lookup_SPLIT \\ strip_tac \\ gvs []
  \\ qabbrev_tac ‘heap0 = ha ++ Bytes be fl2 vals2 (make_zeros vals2)::hb’
  \\ qabbrev_tac ‘heap1 = ha ++ Bytes be fl2 res_vals (make_zeros vals2)::hb’
  \\ qrefinel [‘_’,‘heap1’]
  \\ qsuff_tac
     ‘∃m1. word_xor_bytes a1 a2 (n2w (LENGTH (make_zeros vals1 :'a word list))) dm m
             = SOME m1 ∧
           heap_in_memory_store heap1 a sp' sp1 gens c st m1 dm limit’
  >- (strip_tac \\ ntac 2 $ pop_assum $ irule_at Any
      \\ ‘(∀a. heap_lookup a heap0 = NONE ⇔ heap_lookup a heap1 = NONE) ∧
          (∀a z. heap_lookup a heap0 = SOME (Unused z) ⇔
                 heap_lookup a heap1 = SOME (Unused z)) ∧
          (∀a x y z. heap_lookup a heap0 = SOME (ForwardPointer x y z) ⇔
                     heap_lookup a heap1 = SOME (ForwardPointer x y z)) ∧
          (∀a t x y z.
            (∀t1 t2. t ≠ BytesTag t1 t2) ⇒
            (heap_lookup a heap0 = SOME (DataElement x y (t,z)) ⇔
             heap_lookup a heap1 = SOME (DataElement x y (t,z)))) ∧
          (∀a t x xs y z. heap_lookup a heap0 = SOME (DataElement (x::xs) y (t,z)) ⇔
                          heap_lookup a heap1 = SOME (DataElement (x::xs) y (t,z)))’
              by (simp [Abbr‘heap0’,Abbr‘heap1’,heap_lookup_APPEND]
                  \\ rw [heap_lookup_def,el_length_Bytes]
                  \\ gvs [Bytes_def])
      \\ ‘∀a. isSomeDataElement (heap_lookup a heap1) =
              isSomeDataElement (heap_lookup a heap0)’
        by (simp [isSomeDataElement_def]
            \\ simp [Abbr‘heap0’,Abbr‘heap1’,heap_lookup_APPEND]
            \\ rw [heap_lookup_def,el_length_Bytes]
            \\ gvs [Bytes_def])
      \\ ‘heap_length heap1 = heap_length heap0 ∧ heap_ok heap1 limit’ by
        (gvs [heap_ok_def,Abbr‘heap0’,Abbr‘heap1’,heap_lookup_APPEND]
         \\ gvs [heap_length_def,FILTER_APPEND,el_length_Bytes]
         \\ gvs [Bytes_def,isForwardPointer_def]
         \\ gvs [SF DNF_ss, SF SFY_ss])
      \\ ‘gc_kind_inv c a sp' sp1 gens heap1’ by
        (qpat_x_assum ‘gc_kind_inv c a sp' sp1 gens heap0’ mp_tac
         \\ gvs [gc_kind_inv_def]
         \\ Cases_on ‘c.gc_kind’ \\ simp []
         \\ rpt strip_tac
         >- (Cases_on ‘gens’ \\ gvs [gen_state_ok_def]
             \\ gvs [EVERY_MEM,gen_start_ok_def]
             \\ rpt strip_tac \\ first_x_assum drule
             \\ simp [Abbr‘heap0’,Abbr‘heap1’]
             \\ rewrite_tac [APPEND,GSYM APPEND_ASSOC]
             \\ simp [heap_split_APPEND_if]
             \\ IF_CASES_TAC \\ simp []
             >-
              (simp [AllCaseEqs()]
               \\ rw [] \\ gvs [SF SFY_ss])
             \\ gvs [heap_split_def,el_length_Bytes]
             \\ simp [AllCaseEqs()]
             \\ rw [] \\ gvs [SF SFY_ss]
             \\ gvs [SF DNF_ss,Bytes_def,SF SFY_ss])
         \\ qpat_x_assum ‘heap_split (a + (sp' + sp1)) heap0 = SOME (h1,h2)’ mp_tac
         \\ simp [Abbr‘heap0’,Abbr‘heap1’]
         \\ rewrite_tac [APPEND,GSYM APPEND_ASSOC]
         \\ gvs [heap_split_APPEND_if]
         \\ IF_CASES_TAC \\ simp []
         >-
          (simp [AllCaseEqs()]
           \\ rw [] \\ gvs [SF SFY_ss]
           \\ gvs [Bytes_def,isRef_def])
         \\ gvs [heap_split_def,el_length_Bytes]
         \\ IF_CASES_TAC \\ gvs []
         >- (rw [] \\ gvs [isRef_def,Bytes_def])
         \\ IF_CASES_TAC \\ gvs []
         \\ simp [AllCaseEqs()]
         \\ rpt strip_tac \\ gvs []
         \\ gvs [Bytes_def,isRef_def])
      \\ ‘unused_space_inv a (sp' + sp1) heap1’ by
        (gvs [unused_space_inv_def,SF DNF_ss]
         \\ gvs [data_up_to_def]
         \\ qpat_x_assum ‘heap_split a heap0 = SOME (h1,h2)’ mp_tac
         \\ simp [Abbr‘heap0’,Abbr‘heap1’]
         \\ rewrite_tac [APPEND,GSYM APPEND_ASSOC]
         \\ gvs [heap_split_APPEND_if]
         \\ IF_CASES_TAC \\ simp []
         >- (simp [AllCaseEqs()] \\ rw [] \\ gvs [SF SFY_ss])
         \\ simp [heap_split_def,el_length_Bytes]
         \\ IF_CASES_TAC \\ simp []
         \\ simp [AllCaseEqs()]
         \\ rw [] \\ gvs [SF SFY_ss]
         \\ gvs [Bytes_def,isRef_def])
      \\ ‘all_ts (insert p2 (ByteArray fl2 res_vals) refs) =
          all_ts refs’ by
        (gvs [all_ts_def,FUN_EQ_THM,lookup_insert,CaseEq"bool"]
         \\ ‘∀n l. lookup n refs = SOME (ValueArray l) ⇔
                     lookup n refs = SOME (ValueArray l) ∧ n ≠ p2’ by
           (rw [] \\ eq_tac \\ rw [] \\ gvs []
            \\ CCONTR_TAC \\ gvs [])
            \\ rpt gen_tac
         \\ pop_assum (fn th => CONV_TAC (RAND_CONV $ ONCE_REWRITE_CONV [th]))
         \\ simp [AC CONJ_ASSOC CONJ_COMM])
      \\ ‘∀v x. v_inv c v (x,f,tf,heap1) = v_inv c v (x,f,tf,heap0)’ by
        (ho_match_mp_tac v_inv_alt_ind
         \\ simp [v_inv_def,Bignum_def,i2mw_def,Word64Rep_def]
         \\ conj_tac >- gvs [good_dimindex_def]
         \\ rw [] \\ gvs [BlockRep_def]
         \\ gvs [LIST_REL_EL_EQN,MEM_EL,PULL_EXISTS]
         \\ eq_tac \\ rw []
         \\  metis_tac [])
      \\ ‘∀vs. reachable_refs vs (insert p2 (ByteArray fl2 res_vals) refs) =
               reachable_refs vs refs’ by
        (gen_tac
         \\ ‘refs = insert p2 (ByteArray fl2 vals2) refs’ by
           (irule (GSYM sptreeTheory.insert_unchanged) \\ gvs [])
         \\ pop_assum (fn th => CONV_TAC (RAND_CONV $ ONCE_REWRITE_CONV [th]))
         \\ rewrite_tac [reachable_refs_def,FUN_EQ_THM]
         \\ ‘ref_edge (insert p2 (ByteArray fl2 res_vals) refs) =
             ref_edge (insert p2 (ByteArray fl2 vals2) refs)’ by
           (gvs [FUN_EQ_THM,ref_edge_def] \\ rw [lookup_insert])
         \\ asm_rewrite_tac [])
      \\ ‘p2 INSERT domain refs = domain refs’ by
        (simp [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ simp [domain_lookup])
      \\ simp [] \\ gvs [roots_ok_def,SF DNF_ss, SF SFY_ss]
      \\ gen_tac \\ strip_tac
      \\ first_x_assum drule
      \\ simp [bc_ref_inv_def,lookup_insert]
      \\ IF_CASES_TAC \\ gvs []
      >-
       (gvs [Abbr‘heap1’,heap_lookup_APPEND,heap_lookup_def,heap_length_APPEND]
        \\ gvs [heap_length_def,el_length_Bytes,make_zeros_def]
        \\ imp_res_tac xor_bytes_length \\ gvs [])
      \\ TOP_CASE_TAC \\ gvs []
      \\ TOP_CASE_TAC \\ gvs []
      \\ TOP_CASE_TAC \\ gvs []
      \\ gvs [RefBlock_def]
      \\ ‘x ≠ heap_length ha’ by
        (qpat_x_assum ‘INJ ($' f) (FDOM f) _’ mp_tac
         \\ simp [INJ_DEF]
         \\ rpt strip_tac \\ CCONTR_TAC \\ gvs []
         \\ pop_assum $ qspecl_then [‘n’,‘p2’] mp_tac
         \\ gvs [FLOOKUP_DEF])
      \\ simp [Abbr‘heap0’,Abbr‘heap1’]
      \\ rewrite_tac [APPEND,GSYM APPEND_ASSOC]
      \\ simp [heap_lookup_APPEND,heap_lookup_def,el_length_Bytes])
  \\ ‘heap_length heap1 = heap_length heap0’ by
    simp [Abbr‘heap1’,Abbr‘heap0’,heap_length_APPEND,heap_length_def,el_length_Bytes]
  \\ ‘LENGTH res_vals = LENGTH vals2’ by imp_res_tac xor_bytes_length
  \\ full_simp_tac std_ss [heap_in_memory_store_def,wordLangTheory.word_loc_11]
  \\ qpat_x_assum ‘_ (fun2set (m,dm))’ mp_tac
  \\ gvs [Abbr‘heap0’,Abbr‘heap1’]
  \\ rename [‘(_ * frame) (fun2set _)’]
  \\ gvs [word_heap_def,word_heap_APPEND]
  \\ simp [Bytes_def,word_el_def,word_payload_def,el_length_def]
  \\ simp_tac (std_ss++sep_cond_ss) [cond_STAR,word_list_def]
  \\ strip_tac \\ pop_assum mp_tac \\ gvs []
  \\ Cases_on ‘p1 = p2’ >-
   (gvs [] \\ strip_tac
    \\ old_drule xor_bytes_word_list_alias
    \\ disch_then $ qspecl_then [‘a1’,‘be’] assume_tac
    \\ SEP_F_TAC
    \\ strip_tac \\ simp []
    \\ gvs [SEP_CLAUSES]
    \\ gvs [AC STAR_COMM STAR_ASSOC])
  \\ gvs [heap_lookup_APPEND,CaseEq"bool"]
  >-
   (dxrule heap_lookup_SPLIT \\ strip_tac \\ gvs []
    \\ gvs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def,Bytes_def]
    \\ simp_tac (std_ss++sep_cond_ss) [cond_STAR,word_list_def]
    \\ gvs [] \\ strip_tac
    \\ old_drule xor_bytes_word_list
    \\ disch_then $ qspecl_then [‘a1’,‘a2’,‘be’] assume_tac
    \\ SEP_F_TAC
    \\ strip_tac \\ simp []
    \\ gvs [SEP_CLAUSES]
    \\ gvs [AC STAR_COMM STAR_ASSOC])
  \\ gvs [NOT_LESS]
  \\ qpat_x_assum ‘heap_length ha ≤ k1’ mp_tac
  \\ simp [Once LESS_EQ_EXISTS]
  \\ strip_tac \\ gvs []
  \\ rename [‘FLOOKUP f p1 = SOME (extra + heap_length ha)’]
  \\ ‘extra ≠ 0’ by
   (qpat_x_assum ‘p1 ≠ p2’ mp_tac
    \\ qpat_x_assum ‘INJ ($' f) _ _ ’ mp_tac
    \\ rpt $ qpat_x_assum ‘FLOOKUP f _ = _’ mp_tac
    \\ rpt $ pop_assum kall_tac
    \\ Cases_on ‘extra’ \\ gvs []
    \\ rpt strip_tac
    \\ gvs [INJ_DEF,TO_FLOOKUP])
  \\ gvs [heap_lookup_def,GSYM word_add_n2w]
  \\ gvs [NOT_LESS]
  \\ qpat_x_assum ‘_ ≤ extra’ mp_tac
  \\ simp [Once LESS_EQ_EXISTS]
  \\ strip_tac \\ gvs [el_length_Bytes]
  >-
   (dxrule heap_lookup_SPLIT \\ strip_tac \\ gvs []
    \\ gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ gvs [word_heap_APPEND,word_heap_def,word_el_def,word_payload_def,Bytes_def,el_length_def]
    \\ simp_tac (std_ss++sep_cond_ss) [cond_STAR,word_list_def]
    \\ gvs [] \\ strip_tac
    \\ old_drule xor_bytes_word_list
    \\ disch_then $ qspecl_then [‘a1’,‘a2’,‘be’] assume_tac
    \\ SEP_F_TAC
    \\ strip_tac \\ simp []
    \\ gvs [SEP_CLAUSES]
    \\ gvs [AC STAR_COMM STAR_ASSOC])
QED

val _ = export_theory();
