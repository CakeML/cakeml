open HolKernel boolLib bossLib Parse;
val _ = new_theory "ml_heap";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open wordsTheory wordsLib integer_wordTheory;

open bytecodeTheory;
open ml_copying_gcTheory;

infix \\ val op \\ = op THEN;

val EVERY2_IMP_EVERY2 = prove(
  ``!xs ys P1 P2.
      (!x y. MEM x xs /\ MEM y ys /\ P1 x y ==> P2 x y) ==>
      EVERY2 P1 xs ys ==> EVERY2 P2 xs ys``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ METIS_TAC []);

val EVERY2_APPEND_IMP = prove(
  ``!xs1 xs2 ys.
      EVERY2 P (xs1 ++ xs2) ys ==>
      ?ys1 ys2. (ys = ys1 ++ ys2) /\ EVERY2 P xs1 ys1 /\ EVERY2 P xs2 ys2``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ METIS_TAC [LIST_REL_def,APPEND]);

val MEM_EVERY2_IMP = prove(
  ``!l x zs P. MEM x l /\ EVERY2 P zs l ==> ?z. MEM z zs /\ P z x``,
  Induct \\ Cases_on `zs` \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);

val EVERY2_LENGTH = LIST_REL_LENGTH
val EVERY2_IMP_LENGTH = EVERY2_LENGTH

val EVERY2_APPEND_CONS = prove(
  ``!xs y ys zs P. EVERY2 P (xs ++ y::ys) zs ==>
                   ?t1 t t2. (zs = t1 ++ t::t2) /\ (LENGTH t1 = LENGTH xs) /\
                             EVERY2 P xs t1 /\ P y t /\ EVERY2 P ys t2``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `zs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`h::t1`,`t'`,`t2`]
  \\ FULL_SIMP_TAC (srw_ss()) []);

val EVERY2_SWAP = prove(
  ``!xs ys. EVERY2 P xs ys ==> EVERY2 (\y x. P x y) ys xs``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) []);

val EVERY2_APPEND_IMP_APPEND = prove(
  ``!xs1 xs2 ys P.
      EVERY2 P (xs1 ++ xs2) ys ==>
      ?ys1 ys2. (ys = ys1 ++ ys2) /\ EVERY2 P xs1 ys1 /\ EVERY2 P xs2 ys2``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`h::ys1`,`ys2`]
  \\ FULL_SIMP_TAC std_ss [APPEND,LIST_REL_def] \\ METIS_TAC[]);

val EVERY2_IMP_APPEND = rich_listTheory.EVERY2_APPEND_suff
val IMP_EVERY2_APPEND = EVERY2_IMP_APPEND

val EVERY2_EQ_EL = LIST_REL_EL_EQN

val EVERY2_IMP_EL = METIS_PROVE[EVERY2_EQ_EL]
  ``!xs ys P. EVERY2 P xs ys ==> !n. n < LENGTH ys ==> P (EL n xs) (EL n ys)``

val EVERY2_MAP_FST_SND = prove(
  ``!xs. EVERY2 P (MAP FST xs) (MAP SND xs) = EVERY (\(x,y). P x y) xs``,
  Induct \\ SRW_TAC [] [LIST_REL_def] \\ Cases_on `h` \\ SRW_TAC [] []);

(* refinement invariant *)

val small_int_def = Define `
  small_int i = - & (2 ** 61) < i /\ (i:int) < & (2 ** 61)`;

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

val bc_value_inv_def = tDefine "bc_value_inv" `
  (bc_value_inv (Number i) (x,f,heap:('a,'b) ml_heap) =
     if small_int i then
       (x = Data (((2w * (if i < 0 then 0w - n2w (Num (-i)) else n2w (Num i))))))
     else
       ?ptr. (x = Pointer ptr) /\
             (heap_lookup ptr heap =
                SOME (DataOnly (i < 0) ((mw (Num (ABS i))):'b word list)))) /\
  (bc_value_inv (CodePtr n) (x,f,heap) = (x = Data (n2w n))) /\
  (bc_value_inv (RefPtr n) (x,f,heap) =
     (x = Pointer (f ' n)) /\ n IN FDOM f) /\
  (bc_value_inv (Block n vs) (x,f,heap) =
     if vs = [] then (x = Data ((2w * n2w n + 1w):'a word)) /\ (n < 2 ** 61) else
       ?ptr xs.
         EVERY2 (\v x. bc_value_inv v (x,f,heap)) vs xs /\
         (x = Pointer ptr) /\ n < 4096 /\ LENGTH vs < 2**32 /\
         (heap_lookup ptr heap =
            SOME (BlockRep n xs))) /\
  (bc_value_inv (StackPtr n) (x,f,heap) = (x = Data (n2w n)))`
 (WF_REL_TAC `measure (bc_value_size o FST)` \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC bc_value_size_LEMMA \\ DECIDE_TAC);

val get_refs_def = tDefine "get_refs" `
  (get_refs (Number _) = []) /\
  (get_refs (StackPtr _) = []) /\
  (get_refs (CodePtr _) = []) /\
  (get_refs (RefPtr p) = [p]) /\
  (get_refs (Block tag vs) = FLAT (MAP get_refs vs))`
 (WF_REL_TAC `measure (bc_value_size)` \\ REPEAT STRIP_TAC \\ Induct_on `vs`
  \\ SRW_TAC [] [bc_value_size_def] \\ RES_TAC \\ DECIDE_TAC);

val ref_edge_def = Define `
  ref_edge (refs:num |-> ref_value) (x:num) (y:num) =
    case FLOOKUP refs x of
    | SOME (ValueArray ys) => MEM y (get_refs (Block ARB ys))
    | _ => F`

val reachable_refs_def = Define `
  reachable_refs roots refs t =
    ?x r. MEM x roots /\ MEM r (get_refs x) /\ RTC (ref_edge refs) r t`;

val RefBlock_def = Define `
  RefBlock xs = DataElement xs (LENGTH xs) (RefTag,[])`;

val bc_ref_inv_def = Define `
  bc_ref_inv n (refs:num |-> ref_value) (f,heap) =
    case (FLOOKUP f n, FLOOKUP refs n) of
    | (SOME x, SOME (ValueArray ys)) =>
        (?zs. (heap_lookup x heap = SOME (RefBlock zs)) /\
              EVERY2 (\z y. bc_value_inv y (z,f,heap)) zs ys)
    | _ => F`;

val bc_stack_ref_inv_def = Define `
  bc_stack_ref_inv stack refs (roots, heap) =
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

val MEM_IMP_bc_value_size = prove(
  ``!l a. MEM a l ==> bc_value_size a < 1 + bc_value1_size l``,
  Induct \\ FULL_SIMP_TAC std_ss [MEM,bc_value_size_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ DECIDE_TAC);

val EL_ADDR_MAP = prove(
  ``!xs n f.
      n < LENGTH xs ==> (EL n (ADDR_MAP f xs) = ADDR_APPLY f (EL n xs))``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [] \\ Cases_on `n` \\ Cases_on `h`
  \\ FULL_SIMP_TAC (srw_ss()) [ADDR_MAP_def,ADDR_APPLY_def]);

val _ = augment_srw_ss [rewrites [LIST_REL_def]];

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
    (FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def,ADDR_APPLY_def,get_refs_def]));

val EVERY2_ADDR_MAP = prove(
  ``!zs l. EVERY2 P (ADDR_MAP g zs) l <=>
           EVERY2 (\x y. P (ADDR_APPLY g x) y) zs l``,
  Induct \\ Cases_on `l`
  \\ FULL_SIMP_TAC std_ss [LIST_REL_def,ADDR_MAP_def] \\ Cases
  \\ FULL_SIMP_TAC std_ss [LIST_REL_def,ADDR_MAP_def,ADDR_APPLY_def]);

val bc_ref_inv_related = prove(
  ``gc_related g heap1 heap2 /\
    bc_ref_inv n refs (f,heap1) /\ (f ' n) IN FDOM g ==>
    bc_ref_inv n refs (g f_o_f f,heap2)``,
  FULL_SIMP_TAC std_ss [bc_ref_inv_def] \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ MP_TAC bc_value_inv_related \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [f_o_f_DEF,gc_related_def,RefBlock_def] \\ RES_TAC
  \\ Cases_on `FLOOKUP f n` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `FLOOKUP refs n` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF,f_o_f_DEF]
  \\ Cases_on `x'` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ RES_TAC \\ FULL_SIMP_TAC (srw_ss()) [LENGTH_ADDR_MAP,EVERY2_ADDR_MAP]
  \\ REPEAT STRIP_TAC \\ Q.PAT_ASSUM `EVERY2 qqq zs l` MP_TAC
  \\ MATCH_MP_TAC EVERY2_IMP_EVERY2 \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ Cases_on `x'` \\ FULL_SIMP_TAC (srw_ss()) [ADDR_APPLY_def]);

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
  \\ FULL_SIMP_TAC std_ss [bc_ref_inv_def,RefBlock_def,RTC_REFL]
  \\ Cases_on `FLOOKUP f r` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `FLOOKUP f r'` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `FLOOKUP refs r` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `FLOOKUP refs r'` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `x''` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `x'''` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC bc_value_inv_related
  \\ FULL_SIMP_TAC std_ss [ref_edge_def]
  \\ FULL_SIMP_TAC std_ss [gc_related_def,INJ_DEF,GSPECIFICATION]
  \\ FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF] \\ SRW_TAC [] []
  \\ Cases_on `refs ' r` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `refs ' r'` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [get_refs_def] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss [MEM_FLAT,MEM_MAP] \\ SRW_TAC [] []
  \\ FULL_SIMP_TAC std_ss [ref_edge_def,EVERY_MEM]
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL,AND_IMP_INTRO]
  \\ RES_TAC \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
  \\ SRW_TAC [] [] \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `!xx yy. bbb` MATCH_MP_TAC
  \\ IMP_RES_TAC MEM_EVERY2_IMP
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`z`,`a`]
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ SRW_TAC [] []);

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
  \\ `n IN FDOM f` by ALL_TAC THEN1 (CCONTR_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [bc_ref_inv_def,FLOOKUP_DEF])
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
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC full_gc_related
  \\ NTAC 3 (POP_ASSUM (K ALL_TAC))
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
  \\ Cases_on`n < el_length x` THEN SRW_TAC[][]
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
   (FULL_SIMP_TAC std_ss [rich_listTheory.FILTER_APPEND,FILTER,isForwardPointer_def,APPEND_NIL]
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

(* cons *)

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

val cons_thm = store_thm("cons_thm",
  ``abs_ml_inv (xs ++ stack) refs (roots,heap,a,sp) limit /\
    LENGTH xs < sp /\ xs <> [] /\ tag < 4096 /\ LENGTH xs < 2**32 ==>
    ?rs roots2 heap2.
      (roots = rs ++ roots2) /\ (LENGTH rs = LENGTH xs) /\
      (heap_store_unused a sp (BlockRep tag rs) heap = (heap2,T)) /\
      abs_ml_inv ((Block tag xs)::stack) refs
                 (Pointer (a + sp - el_length (BlockRep tag rs))::roots2,heap2,a,
                  sp-el_length (BlockRep tag rs)) limit``,
  SIMP_TAC std_ss [abs_ml_inv_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_stack_ref_inv_def,LIST_REL_def]
  \\ IMP_RES_TAC EVERY2_APPEND_IMP \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`ys1`,`ys2`] \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC EVERY2_LENGTH \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `unused_space_inv a sp heap` (fn th =>
    MATCH_MP (IMP_heap_store_unused |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> GEN_ALL) th
    |> ASSUME_TAC)
  \\ POP_ASSUM (MP_TAC o Q.SPEC `(BlockRep tag ys1)`) \\ MATCH_MP_TAC miscLib.IMP_IMP
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
    \\ FIRST_ASSUM (miscLib.match_exists_tac o concl)
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
  \\ Cases_on `FLOOKUP f n` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `FLOOKUP refs n` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `x'` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC heap_store_rel_lemma \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Q.PAT_ASSUM `EVERY2 PP zs l` MP_TAC
  \\ MATCH_MP_TAC EVERY2_IMP_EVERY2 \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ IMP_RES_TAC bc_value_inv_SUBMAP
  \\ `f SUBMAP f` by FULL_SIMP_TAC std_ss [SUBMAP_REFL] \\ RES_TAC)

val cons_thm_EMPTY = store_thm("cons_thm_EMPTY",
  ``abs_ml_inv stack refs (roots,heap:('a,'b) ml_heap,a,sp) limit /\
    tag < 2 ** 61 ==>
    abs_ml_inv ((Block tag [])::stack) refs
                (Data (2w * n2w tag + 1w)::roots,heap,a,sp) limit``,
  SIMP_TAC std_ss [abs_ml_inv_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [bc_stack_ref_inv_def,LIST_REL_def]
  \\ FULL_SIMP_TAC (srw_ss()) [roots_ok_def,MEM]
  \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def]
  \\ REPEAT STRIP_TAC \\ `reachable_refs stack refs n` by ALL_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [reachable_refs_def]
  \\ Cases_on `x = Block tag []` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [get_refs_def] \\ METIS_TAC []);

(* update ref *)

val ref_edge_ValueArray = prove(
  ``ref_edge (refs |+ (ptr,ValueArray xs)) x y =
    if x = ptr then MEM y (get_refs (Block ARB xs)) else ref_edge refs x y``,
  SIMP_TAC std_ss [FUN_EQ_THM,ref_edge_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
  \\ Cases_on `x = ptr` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `ptr IN FDOM refs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `refs ' ptr` \\ FULL_SIMP_TAC (srw_ss()) []);

val reachable_refs_UPDATE = prove(
  ``reachable_refs (xs ++ RefPtr ptr::stack) (refs |+ (ptr,ValueArray xs)) n ==>
    reachable_refs (xs ++ RefPtr ptr::stack) refs n``,
  FULL_SIMP_TAC std_ss [reachable_refs_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `?m. MEM m (get_refs (Block ARB xs)) /\
        RTC (ref_edge refs) m n` THEN1
   (FULL_SIMP_TAC std_ss [get_refs_def,MEM_FLAT,MEM_MAP]
    \\ SRW_TAC [] [] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [METIS_PROVE [] ``~b \/ c = b ==> c``]
  \\ FULL_SIMP_TAC std_ss [] \\ Q.LIST_EXISTS_TAC [`x`,`r`]
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [RTC_eq_NRC]
  \\ Q.ABBREV_TAC `k = n'` \\ POP_ASSUM (K ALL_TAC) \\ Q.EXISTS_TAC `k`
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Q.SPEC_TAC (`r`,`r`) \\ Induct_on `k`
  \\ FULL_SIMP_TAC std_ss [NRC]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
  \\ Q.EXISTS_TAC `z` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [ref_edge_ValueArray]
  \\ REVERSE (Cases_on `r = ptr`)
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC);

val isRefBlock_def = Define `
  isRefBlock x = ?p. x = RefBlock p`;

val RefBlock_inv_def = Define `
  RefBlock_inv heap heap2 =
    (!n x. (heap_lookup n heap = SOME x) /\ ~(isRefBlock x) ==>
           (heap_lookup n heap2 = SOME x)) /\
    (!n x. (heap_lookup n heap2 = SOME x) /\ ~(isRefBlock x) ==>
           (heap_lookup n heap = SOME x))`;

val heap_store_RefBlock_thm = prove(
  ``!ha. (LENGTH x = LENGTH y) ==>
         (heap_store (heap_length ha) [RefBlock x] (ha ++ RefBlock y::hb) =
           (ha ++ RefBlock x::hb,T))``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [heap_store_def,heap_length_def]
  THEN1 FULL_SIMP_TAC std_ss [RefBlock_def,el_length_def] \\ STRIP_TAC
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `~(el_length h + SUM (MAP el_length ha) < el_length h) /\ el_length h <> 0` by
       (Cases_on `h` \\ FULL_SIMP_TAC std_ss [el_length_def] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [LET_DEF]);

val heap_lookup_RefBlock_lemma = prove(
  ``(heap_lookup n (ha ++ RefBlock y::hb) = SOME x) =
      if n < heap_length ha then
        (heap_lookup n ha = SOME x)
      else if n = heap_length ha then
        (x = RefBlock y)
      else if heap_length ha + (LENGTH y + 1) <= n then
        (heap_lookup (n - heap_length ha - (LENGTH y + 1)) hb = SOME x)
      else F``,
  Cases_on `n < heap_length ha` \\ FULL_SIMP_TAC std_ss [LESS_IMP_heap_lookup]
  \\ FULL_SIMP_TAC std_ss [NOT_LESS_IMP_heap_lookup]
  \\ FULL_SIMP_TAC std_ss [heap_lookup_def]
  \\ Cases_on `n <= heap_length ha` \\ FULL_SIMP_TAC std_ss []
  THEN1 (`heap_length ha = n` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ `heap_length ha <> n` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `0 < el_length (RefBlock y)` by FULL_SIMP_TAC std_ss [el_length_def,RefBlock_def]
  \\ FULL_SIMP_TAC std_ss [] \\ SRW_TAC [] []
  THEN1 DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [el_length_def,RefBlock_def,NOT_LESS]
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
   (FULL_SIMP_TAC (srw_ss()) [rich_listTheory.FILTER_APPEND,FILTER,isForwardPointer_def,RefBlock_def])
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
  ``abs_ml_inv (xs ++ (RefPtr ptr)::stack) refs (roots,heap,a,sp) limit /\
    (FLOOKUP refs ptr = SOME (ValueArray xs1)) /\ (LENGTH xs = LENGTH xs1) ==>
    ?p rs roots2 heap2.
      (roots = rs ++ Pointer p :: roots2) /\
      (heap_store p [RefBlock rs] heap = (heap2,T)) /\
      abs_ml_inv (xs ++ (RefPtr ptr)::stack) (refs |+ (ptr,ValueArray xs))
        (roots,heap2,a,sp) limit``,
  SIMP_TAC std_ss [abs_ml_inv_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_stack_ref_inv_def]
  \\ IMP_RES_TAC EVERY2_APPEND_CONS
  \\ FULL_SIMP_TAC std_ss [bc_value_inv_def]
  \\ Q.LIST_EXISTS_TAC [`f ' ptr`,`t1`,`t2`]
  \\ FULL_SIMP_TAC std_ss []
  \\ `reachable_refs (xs ++ RefPtr ptr::stack) refs ptr` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [reachable_refs_def] \\ Q.EXISTS_TAC `RefPtr ptr`
    \\ FULL_SIMP_TAC (srw_ss()) [get_refs_def])
  \\ RES_TAC \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [Once bc_ref_inv_def]
  \\ Cases_on `FLOOKUP refs ptr` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `FLOOKUP f ptr` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC heap_store_RefBlock \\ POP_ASSUM (MP_TAC o Q.SPEC `t1`)
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC EVERY2_IMP_LENGTH
  \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF]
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [roots_ok_def])
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [heap_ok_def] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [RefBlock_def] \\ SRW_TAC [] []
    \\ Q.ABBREV_TAC `p1 = ptr'` \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `p1 = f ' ptr` \\ FULL_SIMP_TAC std_ss []
    THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss [roots_ok_def,MEM_APPEND])
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [unused_space_inv_def] \\ REPEAT STRIP_TAC
    \\ RES_TAC \\ Cases_on `a = f ' ptr` \\ FULL_SIMP_TAC (srw_ss()) []
    THEN1 FULL_SIMP_TAC (srw_ss()) [RefBlock_def]
    \\ FULL_SIMP_TAC std_ss [RefBlock_inv_def]
    \\ RES_TAC \\ FULL_SIMP_TAC (srw_ss()) [isRefBlock_def,RefBlock_def])
  \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss []
  \\ MP_TAC bc_value_inv_Ref
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF])
  \\ `reachable_refs (xs ++ RefPtr ptr::stack) refs n` by ALL_TAC
  THEN1 IMP_RES_TAC reachable_refs_UPDATE
  \\ Cases_on `n = ptr` \\ FULL_SIMP_TAC (srw_ss()) [bc_ref_inv_def] THEN1
   (SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF,RefBlock_def]
    \\ IMP_RES_TAC EVERY2_SWAP \\ FULL_SIMP_TAC std_ss []) \\ RES_TAC
  \\ Cases_on `FLOOKUP f n` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `FLOOKUP refs n` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `x'''` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
  \\ SRW_TAC [] []
  \\ Q.EXISTS_TAC `zs'` \\ FULL_SIMP_TAC std_ss []
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [INJ_DEF]
  \\ METIS_TAC []);

(* -- works up to this point -- *)

(* new ref *)

val new_ref_thm = store_thm("new_ref_thm",
  ``abs_ml_inv (xs ++ stack) refs (roots,heap,a,sp) limit /\
    ~(ptr IN FDOM refs) /\ LENGTH xs + 1 <= sp ==>
    ?p rs roots2 heap2.
      (roots = rs ++ roots2) /\
      (heap_store_unused a sp (RefBlock rs) heap = (heap2,T)) /\
      abs_ml_inv (xs ++ (RefPtr ptr)::stack) (refs |+ (ptr,ValueArray xs))
                 (rs ++ Pointer (a+sp-(LENGTH xs + 1))::roots2,heap2,a,
                  sp - (LENGTH xs + 1)) limit``,
  SIMP_TAC std_ss [abs_ml_inv_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_stack_ref_inv_def]
  \\ IMP_RES_TAC EVERY2_APPEND_IMP_APPEND
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Q.LIST_EXISTS_TAC [`ys1`,`ys2`] \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC EVERY2_IMP_LENGTH
  \\ `el_length (RefBlock ys1) <= sp` by ALL_TAC
  THEN1 (FULL_SIMP_TAC std_ss [el_length_def,RefBlock_def])
  \\ Q.PAT_ASSUM `unused_space_inv a sp heap` (fn th =>
    MATCH_MP (IMP_heap_store_unused
    |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> GEN_ALL) th
    |> ASSUME_TAC)
  \\ POP_ASSUM (MP_TAC o Q.SPEC `RefBlock ys1`) \\ MATCH_MP_TAC miscLib.IMP_IMP
  \\ STRIP_TAC THEN1 FULL_SIMP_TAC std_ss [RefBlock_def,el_length_def]
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `unused_space_inv a (sp - (LENGTH ys1 + 1)) heap2` by ALL_TAC
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
  \\ Q.EXISTS_TAC `f |+ (ptr,a+sp-(LENGTH ys1 + 1))`
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC (srw_ss()) [FDOM_FUPDATE]
    \\ `(FAPPLY (f |+ (ptr,a + sp - (LENGTH ys1 + 1)))) =
          (ptr =+ (a+sp-(LENGTH ys1 + 1))) (FAPPLY f)` by
     (FULL_SIMP_TAC std_ss [FUN_EQ_THM,FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM]
      \\ METIS_TAC []) \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC (METIS_PROVE [] ``!y. (x = y) /\ f y ==> f x``)
    \\ Q.EXISTS_TAC `(a + sp - (LENGTH ys1 + 1)) INSERT
         {a | isSomeDataElement (heap_lookup a heap)}`
    \\ STRIP_TAC
    THEN1 (FULL_SIMP_TAC (srw_ss()) [RefBlock_def,isDataElement_def,el_length_def])
    \\ MATCH_MP_TAC INJ_UPDATE \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [RefBlock_def,el_length_def])
  \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF,FDOM_FUPDATE] \\ METIS_TAC [])
  \\ Q.ABBREV_TAC `f1 = f |+ (ptr,a + sp - (LENGTH ys1 + 1))`
  \\ `f SUBMAP f1` by ALL_TAC THEN1
   (Q.UNABBREV_TAC `f1` \\ FULL_SIMP_TAC (srw_ss()) [SUBMAP_DEF,FAPPLY_FUPDATE_THM]
    \\ METIS_TAC [])
  \\ STRIP_TAC THEN1
   (MATCH_MP_TAC EVERY2_IMP_APPEND
    \\ FULL_SIMP_TAC std_ss [LIST_REL_def]
    \\ MATCH_MP_TAC (METIS_PROVE [] ``p2 /\ (p1 /\ p3) ==> p1 /\ p2 /\ p3``)
    \\ STRIP_TAC THEN1 (UNABBREV_ALL_TAC \\ EVAL_TAC)
    \\ FULL_SIMP_TAC (srw_ss()) [bc_value_inv_def,FAPPLY_FUPDATE_THM]
    \\ FULL_SIMP_TAC std_ss [EVERY2_EQ_EL]
    \\ IMP_RES_TAC EVERY2_IMP_LENGTH
    \\ METIS_TAC [bc_value_inv_SUBMAP])
  \\ REPEAT STRIP_TAC
  \\ Cases_on `n = ptr` THEN1
   (Q.UNABBREV_TAC `f1` \\ ASM_SIMP_TAC (srw_ss()) [bc_ref_inv_def,FDOM_FUPDATE,
      FAPPLY_FUPDATE_THM] \\ FULL_SIMP_TAC std_ss [el_length_def,RefBlock_def]
    \\ FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF,EVERY2_EQ_EL]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC bc_value_inv_SUBMAP \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ `reachable_refs (xs ++ RefPtr ptr::stack) refs n` by ALL_TAC
  THEN1 IMP_RES_TAC reachable_refs_UPDATE
  \\ Q.PAT_ASSUM `reachable_refs (xs ++ RefPtr ptr::stack)
        (refs |+ (ptr,x)) n` (K ALL_TAC)
  \\ `reachable_refs (xs ++ stack) refs n` by ALL_TAC THEN1
    (FULL_SIMP_TAC std_ss [reachable_refs_def]
     \\ REVERSE (Cases_on `x = RefPtr ptr`)
     THEN1 (FULL_SIMP_TAC std_ss [MEM,MEM_APPEND] \\ METIS_TAC [])
     \\ FULL_SIMP_TAC std_ss [get_refs_def,MEM]
     \\ SRW_TAC [] []
     \\ IMP_RES_TAC RTC_NRC
     \\ Cases_on `n'` \\ FULL_SIMP_TAC std_ss [NRC]
     \\ FULL_SIMP_TAC std_ss [ref_edge_def,FLOOKUP_DEF]
     \\ REV_FULL_SIMP_TAC std_ss [])
  \\ RES_TAC \\ Q.UNABBREV_TAC `f1` \\ FULL_SIMP_TAC std_ss [bc_ref_inv_def]
  \\ Cases_on `FLOOKUP f n` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `FLOOKUP refs n` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [FDOM_FUPDATE,FAPPLY_FUPDATE_THM,FLOOKUP_DEF]
  \\ Cases_on `x'` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ `isSomeDataElement (heap_lookup (f ' n) heap)` by
    (FULL_SIMP_TAC std_ss [RefBlock_def] \\ EVAL_TAC
     \\ SIMP_TAC (srw_ss()) [] \\ NO_TAC)
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC (srw_ss()) [RefBlock_def]
  \\ Q.PAT_ASSUM `n IN FDOM f` ASSUME_TAC
  \\ Q.PAT_ASSUM `n IN FDOM refs` ASSUME_TAC
  \\ Q.PAT_ASSUM `refs ' n = ValueArray l` ASSUME_TAC
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [RefBlock_def]
  \\ IMP_RES_TAC heap_store_rel_lemma
  \\ RES_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Q.PAT_ASSUM `EVERY2 PPP zs l` MP_TAC
  \\ MATCH_MP_TAC EVERY2_IMP_EVERY2
  \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC bc_value_inv_SUBMAP
  \\ FULL_SIMP_TAC (srw_ss()) []);

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
    ?r roots2 ts.
      (roots = r::roots2) /\ (refs ' ptr = ValueArray ts) /\ ptr IN FDOM refs /\
      !n. n < LENGTH ts ==>
          ?y t. (heap_el r n heap = (y,T)) /\
                abs_ml_inv (t::RefPtr ptr::stack) refs
                  (y::roots,heap,a,sp) limit``,
  FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `roots` \\ FULL_SIMP_TAC (srw_ss()) [LIST_REL_def]
  \\ FULL_SIMP_TAC std_ss [bc_value_inv_def]
  \\ `reachable_refs (RefPtr ptr::stack) refs ptr` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [reachable_refs_def,MEM] \\ Q.EXISTS_TAC `RefPtr ptr`
    \\ ASM_SIMP_TAC (srw_ss()) [get_refs_def])
  \\ RES_TAC \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [Once bc_ref_inv_def]
  \\ FULL_SIMP_TAC (srw_ss()) [FLOOKUP_DEF]
  \\ Cases_on `ptr IN FDOM refs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `refs ' ptr` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ NTAC 3 STRIP_TAC
  \\ IMP_RES_TAC EVERY2_IMP_LENGTH
  \\ ASM_SIMP_TAC (srw_ss()) [heap_el_def,RefBlock_def]
  \\ Q.EXISTS_TAC `EL n l` \\ SRW_TAC [] [] THEN1
   (FULL_SIMP_TAC std_ss [roots_ok_def,heap_ok_def]
    \\ IMP_RES_TAC heap_lookup_MEM
    \\ STRIP_TAC \\ ONCE_REWRITE_TAC [MEM] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [RefBlock_def]
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [MEM]
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ METIS_TAC [MEM_EL])
  \\ Q.EXISTS_TAC `f` \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC EVERY2_IMP_EL
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ Q.PAT_ASSUM `reachable_refs (RefPtr ptr::stack) refs ptr` (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [reachable_refs_def]
  \\ REVERSE (Cases_on `x = EL n l`)
  THEN1 (FULL_SIMP_TAC std_ss [MEM] \\ METIS_TAC [])
  \\ Q.EXISTS_TAC `RefPtr ptr` \\ SIMP_TAC std_ss [MEM,get_refs_def]
  \\ ONCE_REWRITE_TAC [RTC_CASES1] \\ DISJ2_TAC
  \\ Q.EXISTS_TAC `r` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (srw_ss()) [ref_edge_def,FLOOKUP_DEF,get_refs_def]
  \\ FULL_SIMP_TAC (srw_ss()) [MEM_FLAT,MEM_MAP,PULL_EXISTS]
  \\ Q.EXISTS_TAC `(EL n l)` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [MEM_EL] \\ METIS_TAC []);

(* el *)

val el_thm = store_thm("el_thm",
  ``abs_ml_inv (Block n xs::stack) refs (roots,heap,a,sp) limit /\ i < LENGTH xs ==>
    ?r roots2 y.
      (roots = r :: roots2) /\ (heap_el r i heap = (y,T)) /\
      abs_ml_inv (EL i xs::Block n xs::stack) refs (y::roots,heap,a,sp) limit``,
  FULL_SIMP_TAC std_ss [abs_ml_inv_def,bc_stack_ref_inv_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `roots` \\ FULL_SIMP_TAC (srw_ss()) [LIST_REL_def]
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
