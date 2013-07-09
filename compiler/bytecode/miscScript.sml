open HolKernel bossLib boolLib boolSimps listTheory pred_setTheory finite_mapTheory alistTheory rich_listTheory arithmeticTheory pairTheory sortingTheory lcsymtacs
(* Misc. lemmas (without any compiler constants) *)
val _ = new_theory "misc"

(* TODO: move/categorize *)

val EL_LENGTH_APPEND_rwt = store_thm("EL_LENGTH_APPEND_rwt",
  ``¬NULL l2 ∧ (n = LENGTH l1) ⇒  (EL n (l1++l2) = HD l2)``,
  metis_tac[EL_LENGTH_APPEND])

val MAP_FST_funs = store_thm("MAP_FST_funs",
  ``MAP (λ(x,y,z). x) funs = MAP FST funs``,
  lrw[MAP_EQ_f,FORALL_PROD])

val PERM_PART = store_thm("PERM_PART",
  ``∀P L l1 l2 p q. ((p,q) = PART P L l1 l2) ⇒ PERM (L ++ (l1 ++ l2)) (p++q)``,
  GEN_TAC THEN Induct >>
  simp[PART_DEF] >> rw[] >- (
    first_x_assum(qspecl_then[`h::l1`,`l2`,`p`,`q`]mp_tac) >>
    simp[] >>
    REWRITE_TAC[Once CONS_APPEND] >>
    strip_tac >>
    REWRITE_TAC[Once CONS_APPEND] >>
    full_simp_tac std_ss [APPEND_ASSOC] >>
    metis_tac[PERM_REWR,PERM_APPEND] ) >>
  first_x_assum(qspecl_then[`l1`,`h::l2`,`p`,`q`]mp_tac) >>
  simp[] >>
  REWRITE_TAC[Once CONS_APPEND] >>
  strip_tac >>
  REWRITE_TAC[Once CONS_APPEND] >>
  full_simp_tac std_ss [APPEND_ASSOC] >>
  metis_tac[PERM_REWR,PERM_APPEND,APPEND_ASSOC] )

val PERM_PARTITION = store_thm("PERM_PARTITION",
  ``∀P L A B. ((A,B) = PARTITION P L) ==> PERM L (A ++ B)``,
  METIS_TAC[PERM_PART,PARTITION_DEF,APPEND_NIL])

val EVERY2_REVERSE = store_thm("EVERY2_REVERSE",
  ``!R l1 l2. EVERY2 R l1 l2 ==> EVERY2 R (REVERSE l1) (REVERSE l2)``,
  rw[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_REVERSE] >>
  first_x_assum match_mp_tac >>
  simp[])

val transitive_LESS = store_thm("transitive_LESS",
  ``transitive ($< : (num->num->bool))``,
  rw[relationTheory.transitive_def] >> PROVE_TAC[LESS_TRANS])
val _ = export_rewrites["transitive_LESS"]

val BIGUNION_IMAGE_set_SUBSET = store_thm("BIGUNION_IMAGE_set_SUBSET",
  ``(BIGUNION (IMAGE f (set ls)) ⊆ s) =
    (∀x. MEM x ls ⇒ f x ⊆ s)``,
  srw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[])

val OPTION_EVERY_def = Define`
  (OPTION_EVERY P NONE = T) /\
  (OPTION_EVERY P (SOME v) = P v)`
val _ = export_rewrites["OPTION_EVERY_def"]
val OPTION_EVERY_cong = store_thm("OPTION_EVERY_cong",
  ``!o1 o2 P1 P2. (o1 = o2) /\ (!x. (o2 = SOME x) ==> (P1 x = P2 x)) ==>
                  (OPTION_EVERY P1 o1 = OPTION_EVERY P2 o2)``,
  Cases THEN SRW_TAC[][] THEN SRW_TAC[][])
val _ = DefnBase.export_cong"OPTION_EVERY_cong"
val OPTION_EVERY_mono = store_thm("OPTION_EVERY_mono",
  ``(!x. P x ==> Q x) ==> OPTION_EVERY P op ==> OPTION_EVERY Q op``,
  Cases_on `op` THEN SRW_TAC[][])
val _ = IndDefLib.export_mono"OPTION_EVERY_mono"

val MEM_LUPDATE = store_thm("MEM_LUPDATE",
  ``!l x y i. MEM x (LUPDATE y i l) ==> (x = y) \/ MEM x l``,
  Induct THEN SRW_TAC[][LUPDATE_def] THEN
  Cases_on`i`THEN FULL_SIMP_TAC(srw_ss())[LUPDATE_def] THEN
  PROVE_TAC[])

val option_case_NONE_F = store_thm("option_case_NONE_F",
  ``(case X of NONE => F | SOME x => P x) = (∃x. (X = SOME x) ∧ P x)``,
  Cases_on`X`>>rw[])

val IS_PREFIX_THM = store_thm("IS_PREFIX_THM",
 ``!l2 l1. IS_PREFIX l1 l2 <=> (LENGTH l2 <= LENGTH l1) /\ !n. n < LENGTH l2 ==> (EL n l2 = EL n l1)``,
 Induct THEN SRW_TAC[][IS_PREFIX] THEN
 Cases_on`l1`THEN SRW_TAC[][EQ_IMP_THM] THEN1 (
   Cases_on`n`THEN SRW_TAC[][EL_CONS] THEN
   FULL_SIMP_TAC(srw_ss()++ARITH_ss)[] )
 THEN1 (
   POP_ASSUM(Q.SPEC_THEN`0`MP_TAC)THEN SRW_TAC[][] )
 THEN1 (
   FIRST_X_ASSUM(Q.SPEC_THEN`SUC n`MP_TAC)THEN SRW_TAC[][] ))

val SUM_MAP_PLUS = store_thm("SUM_MAP_PLUS",
  ``∀f g ls. SUM (MAP (λx. f x + g x) ls) = SUM (MAP f ls) + SUM (MAP g ls)``,
  ntac 2 gen_tac >> Induct >> simp[])

val TAKE_PRE_LENGTH = store_thm("TAKE_PRE_LENGTH",
  ``!ls. ls <> [] ==> (TAKE (PRE (LENGTH ls)) ls = FRONT ls)``,
  Induct THEN SRW_TAC[][LENGTH_NIL] THEN
  FULL_SIMP_TAC(srw_ss())[FRONT_DEF,PRE_SUB1])

val DROP_LENGTH_NIL_rwt = store_thm("DROP_LENGTH_NIL_rwt",
  ``!l m. (m = LENGTH l) ==> (DROP m l = [])``,
  lrw[DROP_LENGTH_NIL])

val TAKE_LENGTH_ID_rwt = store_thm("TAKE_LENGTH_ID_rwt",
  ``!l m. (m = LENGTH l) ==> (TAKE m l = l)``,
  lrw[TAKE_LENGTH_ID])

val DROP_EL_CONS = store_thm("DROP_EL_CONS",
  ``!ls n. n < LENGTH ls ==> (DROP n ls = EL n ls :: DROP (n + 1) ls)``,
  Induct >> lrw[EL_CONS,PRE_SUB1])

val TAKE_EL_SNOC = store_thm("TAKE_EL_SNOC",
  ``!ls n. n < LENGTH ls ==> (TAKE (n + 1) ls = SNOC (EL n ls) (TAKE n ls))``,
  HO_MATCH_MP_TAC SNOC_INDUCT >>
  CONJ_TAC THEN1 SRW_TAC[][] THEN
  REPEAT STRIP_TAC THEN
  Cases_on`n = LENGTH ls` THEN1 (
    lrw[EL_LENGTH_SNOC,TAKE_SNOC,TAKE_APPEND1,EL_APPEND1,EL_APPEND2,TAKE_APPEND2] ) THEN
  `n < LENGTH ls` by fsrw_tac[ARITH_ss][ADD1] THEN
  lrw[TAKE_SNOC,TAKE_APPEND1,EL_APPEND1])

val ZIP_DROP = store_thm("ZIP_DROP",
  ``!a b n. n <= LENGTH a /\ (LENGTH a = LENGTH b) ==>
      (ZIP (DROP n a,DROP n b) = DROP n (ZIP (a,b)))``,
  Induct THEN SRW_TAC[][LENGTH_NIL_SYM,ADD1] THEN
  Cases_on`b` THEN FULL_SIMP_TAC(srw_ss())[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FULL_SIMP_TAC(srw_ss()++ARITH_ss)[])

val EVERY2_DROP = store_thm("EVERY2_DROP",
  ``∀R l1 l2 n. EVERY2 R l1 l2 ∧ n <= LENGTH l1 ==> EVERY2 R (DROP n l1) (DROP n l2)``,
  rw[EVERY2_EVERY,ZIP_DROP] >>
  match_mp_tac (MP_CANON EVERY_DROP) >>
  rw[] >> PROVE_TAC[])

val REVERSE_DROP = store_thm("REVERSE_DROP",
  ``!ls n. n <= LENGTH ls ==> (REVERSE (DROP n ls) = REVERSE (LASTN (LENGTH ls - n) ls))``,
  HO_MATCH_MP_TAC SNOC_INDUCT THEN
  SRW_TAC[][LASTN] THEN
  Cases_on`n = SUC (LENGTH ls)` THEN1 (
    lrw[DROP_LENGTH_NIL_rwt,ADD1,LASTN] ) THEN
  lrw[DROP_APPEND1,LASTN_APPEND1])

val FUPDATE_LIST_CANCEL = store_thm("FUPDATE_LIST_CANCEL",
  ``!ls1 fm ls2.
    (!k. MEM k (MAP FST ls1) ==> MEM k (MAP FST ls2))
    ==> (fm |++ ls1 |++ ls2 = fm |++ ls2)``,
  Induct THEN SRW_TAC[][FUPDATE_LIST_THM] THEN
  Cases_on`h` THEN
  MATCH_MP_TAC FUPDATE_FUPDATE_LIST_MEM THEN
  FULL_SIMP_TAC(srw_ss())[])

val FUPDATE_LIST_SNOC = store_thm("FUPDATE_LIST_SNOC",
  ``!xs x fm. fm |++ SNOC x xs = (fm |++ xs) |+ x``,
  Induct >> rw[FUPDATE_LIST_THM])

val FUPDATE_EQ_FUNION = store_thm("FUPDATE_EQ_FUNION",
  ``∀fm kv. fm |+ kv = (FEMPTY |+ kv) ⊌ fm``,
  gen_tac >> Cases >>
  simp[GSYM fmap_EQ_THM,FDOM_FUPDATE,FAPPLY_FUPDATE_THM,FUNION_DEF] >>
  simp[EXTENSION])

val GENLIST_EL = store_thm("GENLIST_EL",
  ``!ls f n. (n = LENGTH ls) /\ (!i. i < n ==> (f i = EL i ls)) ==>
             (GENLIST f n = ls)``,
  lrw[LIST_EQ_REWRITE])

val fmap_rel_OPTREL_FLOOKUP = store_thm("fmap_rel_OPTREL_FLOOKUP",
  ``fmap_rel R f1 f2 = ∀k. OPTREL R (FLOOKUP f1 k) (FLOOKUP f2 k)``,
  rw[fmap_rel_def,optionTheory.OPTREL_def,FLOOKUP_DEF,EXTENSION] >>
  PROVE_TAC[])

val FUPDATE_LIST_APPEND_COMMUTES = store_thm("FUPDATE_LIST_APPEND_COMMUTES",
  ``!l1 l2 fm. DISJOINT (set (MAP FST l1)) (set (MAP FST l2)) ⇒ (fm |++ l1 |++ l2 = fm |++ l2 |++ l1)``,
  Induct >- rw[FUPDATE_LIST_THM] >>
  Cases >> rw[FUPDATE_LIST_THM] >>
  metis_tac[FUPDATE_FUPDATE_LIST_COMMUTES])

val LENGTH_FILTER_LESS = store_thm("LENGTH_FILTER_LESS",
  ``!P ls. EXISTS ($~ o P) ls ==> LENGTH (FILTER P ls) < LENGTH ls``,
  GEN_TAC THEN Induct THEN SRW_TAC[][] THEN
  MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC THEN
  MATCH_ACCEPT_TAC LENGTH_FILTER_LEQ)

val EVERY2_trans = store_thm("EVERY2_trans",
  ``(!x y z. R x y /\ R y z ==> R x z) ==>
    !x y z. EVERY2 R x y /\ EVERY2 R y z ==> EVERY2 R x z``,
  SRW_TAC[][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] THEN
  REPEAT (Q.PAT_ASSUM`LENGTH X = Y`MP_TAC) THEN
  REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()++DNF_ss) [MEM_ZIP] THEN
  METIS_TAC[])

val EVERY2_sym = store_thm("EVERY2_sym",
  ``(!x y. R1 x y ==> R2 y x) ==> !x y. EVERY2 R1 x y ==> EVERY2 R2 y x``,
  SRW_TAC[][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] THEN
  (Q.PAT_ASSUM`LENGTH X = Y`MP_TAC) THEN
  STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()++DNF_ss) [MEM_ZIP])

val EVERY2_LUPDATE_same = store_thm("EVERY2_LUPDATE_same",
  ``!P l1 l2 v1 v2 n. P v1 v2 /\ EVERY2 P l1 l2 ==>
    EVERY2 P (LUPDATE v1 n l1) (LUPDATE v2 n l2)``,
  GEN_TAC THEN Induct THEN
  SRW_TAC[][LUPDATE_def] THEN
  Cases_on`n`THEN SRW_TAC[][LUPDATE_def] THEN
  Cases_on`l2`THEN FULL_SIMP_TAC(srw_ss())[LUPDATE_def])

val EVERY2_refl = store_thm("EVERY2_refl",
  ``(!x. MEM x ls ==> R x x) ==> (EVERY2 R ls ls)``,
  Induct_on`ls` >>rw[])

val EVERY2_APPEND = store_thm("EVERY2_APPEND",
  ``EVERY2 R l1 l2 /\ EVERY2 R l3 l4 <=> EVERY2 R (l1 ++ l3) (l2 ++ l4) /\ (LENGTH l1 = LENGTH l2) /\ (LENGTH l3 = LENGTH l4)``,
  rw[EVERY2_EVERY,EVERY_MEM] >>
  metis_tac[ZIP_APPEND,MEM_APPEND])

val EVERY2_APPEND_suff = store_thm("EVERY2_APPEND_suff",
  ``EVERY2 R l1 l2 ∧ EVERY2 R l3 l4 ⇒ EVERY2 R (l1 ++ l3) (l2 ++ l4)``,
  metis_tac[EVERY2_APPEND])

val SWAP_REVERSE = store_thm("SWAP_REVERSE",
  ``!l1 l2. (l1 = REVERSE l2) = (l2 = REVERSE l1)``,
  SRW_TAC[][EQ_IMP_THM])

val SWAP_REVERSE_SYM = store_thm("SWAP_REVERSE_SYM",
  ``!l1 l2. (REVERSE l1 = l2) = (l1 = REVERSE l2)``,
  metis_tac[SWAP_REVERSE])

val EVERY2_THM = store_thm("EVERY2_THM",
  ``(!P ys. EVERY2 P [] ys = (ys = [])) /\
    (!P yys x xs. EVERY2 P (x::xs) yys = ?y ys. (yys = y::ys) /\ (P x y) /\ (EVERY2 P xs ys)) /\
    (!P xs. EVERY2 P xs [] = (xs = [])) /\
    (!P xxs y ys. EVERY2 P xxs (y::ys) = ?x xs. (xxs = x::xs) /\ (P x y) /\ (EVERY2 P xs ys))``,
  REPEAT CONJ_TAC THEN GEN_TAC THEN TRY (
    SRW_TAC[][EVERY2_EVERY,LENGTH_NIL] THEN
    SRW_TAC[][EQ_IMP_THM] THEN NO_TAC ) THEN
  Cases THEN SRW_TAC[][EVERY2_EVERY])
val _ = export_rewrites["EVERY2_THM"]

val EVERY2_RC_same = store_thm("EVERY2_RC_same",
  ``EVERY2 (RC R) l l``,
  srw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP,relationTheory.RC_DEF])
val _ = export_rewrites["EVERY2_RC_same"]

val CARD_UNION_LE = store_thm("CARD_UNION_LE",
  ``FINITE s ∧ FINITE t ⇒ CARD (s ∪ t) ≤ CARD s + CARD t``,
  rw[] >> imp_res_tac CARD_UNION >> fsrw_tac[ARITH_ss][])

val IMAGE_SUBSET_gen = store_thm("IMAGE_SUBSET_gen",
  ``∀f s u t. s ⊆ u ∧ (IMAGE f u ⊆ t) ⇒ IMAGE f s ⊆ t``,
  simp[SUBSET_DEF] >> metis_tac[])

val REVERSE_INV = store_thm("REVERSE_INV",
  ``!l1 l2. (REVERSE l1 = REVERSE l2) = (l1 = l2)``,
  Induct THEN SRW_TAC[][] THEN
  Cases_on`l2` THEN SRW_TAC[][EQ_IMP_THM])
val _ = export_rewrites["REVERSE_INV"]

val FLOOKUP_DRESTRICT = store_thm("FLOOKUP_DRESTRICT",
  ``!fm s k. FLOOKUP (DRESTRICT fm s) k = if k IN s then FLOOKUP fm k else NONE``,
  SRW_TAC[][FLOOKUP_DEF,DRESTRICT_DEF] THEN FULL_SIMP_TAC std_ss [])

val IMAGE_EL_count_LENGTH = store_thm("IMAGE_EL_count_LENGTH",
  ``∀f ls. IMAGE (λn. f (EL n ls)) (count (LENGTH ls)) = IMAGE f (set ls)``,
  rw[EXTENSION,MEM_EL] >> PROVE_TAC[])

val GENLIST_EL_MAP = store_thm("GENLIST_EL_MAP",
  ``!f ls. GENLIST (λn. f (EL n ls)) (LENGTH ls) = MAP f ls``,
  gen_tac >> Induct >> rw[GENLIST_CONS,combinTheory.o_DEF])

val LENGTH_FILTER_LEQ_MONO = store_thm("LENGTH_FILTER_LEQ_MONO",
  ``!P Q. (!x. P x ==> Q x) ==> !ls. (LENGTH (FILTER P ls) <= LENGTH (FILTER Q ls))``,
  rpt gen_tac >> strip_tac >>
  Induct >> rw[] >>
  fsrw_tac[ARITH_ss][] >>
  PROVE_TAC[])

val CARD_REST = store_thm("CARD_REST",
  ``!s. FINITE s /\ s <> {} ==> (CARD (REST s) = CARD s - 1)``,
  SRW_TAC[][] THEN
  IMP_RES_TAC CHOICE_INSERT_REST THEN
  POP_ASSUM (fn th => CONV_TAC (RAND_CONV (REWRITE_CONV [Once(SYM th)]))) THEN
  Q.SPEC_THEN`REST s`MP_TAC CARD_INSERT THEN SRW_TAC[][] THEN
  FULL_SIMP_TAC(srw_ss())[REST_DEF])

val LIST_EQ_MAP_PAIR = store_thm("LIST_EQ_MAP_PAIR",
  ``!l1 l2. (MAP FST l1 = MAP FST l2) /\ (MAP SND l1 = MAP SND l2) ==> (l1 = l2)``,
  SRW_TAC[][MAP_EQ_EVERY2,EVERY2_EVERY,EVERY_MEM,LIST_EQ_REWRITE,FORALL_PROD] THEN
  REV_FULL_SIMP_TAC (srw_ss()++DNF_ss) [MEM_ZIP] THEN
  METIS_TAC[pair_CASES,PAIR_EQ])

val FUPDATE_LIST_ALL_DISTINCT_PERM = store_thm("FUPDATE_LIST_ALL_DISTINCT_PERM",
  ``!ls ls' fm. ALL_DISTINCT (MAP FST ls) /\ PERM ls ls' ==> (fm |++ ls = fm |++ ls')``,
  Induct >> rw[] >>
  fs[sortingTheory.PERM_CONS_EQ_APPEND] >>
  rw[FUPDATE_LIST_THM] >>
  PairCases_on`h` >> fs[] >>
  imp_res_tac FUPDATE_FUPDATE_LIST_COMMUTES >>
  match_mp_tac EQ_TRANS >>
  qexists_tac `(fm |++ (M ++ N)) |+ (h0,h1)` >>
  conj_tac >- metis_tac[sortingTheory.ALL_DISTINCT_PERM,sortingTheory.PERM_MAP] >>
  rw[FUPDATE_LIST_APPEND] >>
  `h0 ∉ set (MAP FST N)` by metis_tac[sortingTheory.PERM_MEM_EQ,MEM_MAP,MEM_APPEND] >>
  imp_res_tac FUPDATE_FUPDATE_LIST_COMMUTES >>
  rw[FUPDATE_LIST_THM])

val ALL_DISTINCT_MEM_ZIP_MAP = store_thm("ALL_DISTINCT_MEM_ZIP_MAP",
  ``!f x ls. ALL_DISTINCT ls ==> (MEM x (ZIP (ls, MAP f ls)) <=> MEM (FST x) ls /\ (SND x = f (FST x)))``,
  GEN_TAC THEN Cases THEN
  SRW_TAC[][MEM_ZIP,FORALL_PROD] THEN
  SRW_TAC[][EQ_IMP_THM] THEN
  SRW_TAC[][EL_MAP,MEM_EL] THEN
  FULL_SIMP_TAC (srw_ss()) [EL_ALL_DISTINCT_EL_EQ,MEM_EL] THEN
  METIS_TAC[EL_MAP])

val IMAGE_FRANGE = store_thm("IMAGE_FRANGE",
  ``!f fm. IMAGE f (FRANGE fm) = FRANGE (f o_f fm)``,
  SRW_TAC[][EXTENSION] THEN
  EQ_TAC THEN1 PROVE_TAC[o_f_FRANGE] THEN
  SRW_TAC[][FRANGE_DEF] THEN
  SRW_TAC[][o_f_FAPPLY] THEN
  PROVE_TAC[])

val SUBMAP_mono_FUPDATE = store_thm("SUBMAP_mono_FUPDATE",
  ``!f g x y. f \\ x SUBMAP g \\ x ==> f |+ (x,y) SUBMAP g |+ (x,y)``,
  SRW_TAC[][SUBMAP_FUPDATE])

val SUBMAP_DOMSUB_gen = store_thm("SUBMAP_DOMSUB_gen",
  ``!f g k. f \\ k SUBMAP g <=> f \\ k SUBMAP g \\ k``,
  SRW_TAC[][SUBMAP_DEF,EQ_IMP_THM,DOMSUB_FAPPLY_THM])

val DOMSUB_SUBMAP = store_thm("DOMSUB_SUBMAP",
  ``!f g x. f SUBMAP g /\ x NOTIN FDOM f ==> f SUBMAP g \\ x``,
  SRW_TAC[][SUBMAP_DEF,DOMSUB_FAPPLY_THM] THEN
  SRW_TAC[][] THEN METIS_TAC[])

val DRESTRICT_DOMSUB = store_thm("DRESTRICT_DOMSUB",
  ``!f s k. DRESTRICT f s \\ k = DRESTRICT f (s DELETE k)``,
  SRW_TAC[][GSYM fmap_EQ_THM,FDOM_DRESTRICT] THEN1 (
    SRW_TAC[][EXTENSION] THEN METIS_TAC[] ) THEN
  SRW_TAC[][DOMSUB_FAPPLY_THM] THEN
  SRW_TAC[][DRESTRICT_DEF])

val fmap_rel_trans = store_thm("fmap_rel_trans",
  ``(!x y z. R x y /\ R y z ==> R x z) ==>
    !x y z. fmap_rel R x y /\ fmap_rel R y z ==>
              fmap_rel R x z``,
  SRW_TAC[][fmap_rel_def] THEN METIS_TAC[])

val fmap_rel_sym = store_thm("fmap_rel_sym",
  ``(!x y. R x y ==> R y x) ==>
    !x y. fmap_rel R x y ==> fmap_rel R y x``,
  SRW_TAC[][fmap_rel_def])

val FOLDL_invariant = store_thm("FOLDL_invariant",
  ``!P f ls a. (P a) /\ (!x y . MEM y ls /\ P x ==> P (f x y)) ==> P (FOLDL f a ls)``,
  NTAC 2 GEN_TAC THEN
  Induct THEN SRW_TAC[][])

val FOLDL_invariant_rest = store_thm("FOLDL_invariant_rest",
  ``∀P f ls a. P ls a ∧ (∀x n. n < LENGTH ls ∧ P (DROP n ls) x ⇒ P (DROP (SUC n) ls) (f x (EL n ls))) ⇒ P [] (FOLDL f a ls)``,
  ntac 2 gen_tac >>
  Induct >> rw[] >>
  first_x_assum match_mp_tac >>
  conj_tac >- (
    first_x_assum (qspecl_then[`a`,`0`] mp_tac) >> rw[] ) >>
  rw[] >> first_x_assum (qspecl_then[`x`,`SUC n`] mp_tac) >> rw[])

val between_def = Define`
  between x y z ⇔ x:num ≤ z ∧ z < y`

val TAKE_SUM = store_thm("TAKE_SUM",
  ``!n m l. n + m <= LENGTH l ==> (TAKE (n + m) l = TAKE n l ++ TAKE m (DROP n l))``,
  Induct_on `l` THEN SRW_TAC[][] THEN SRW_TAC[][] THEN
  Cases_on `n` THEN FULL_SIMP_TAC(srw_ss()++ARITH_ss)[ADD1])

val ALL_DISTINCT_FILTER_EL_IMP = store_thm("ALL_DISTINCT_FILTER_EL_IMP",
  ``!P l n1 n2. ALL_DISTINCT (FILTER P l) /\
    n1 < LENGTH l /\ n2 < LENGTH l /\
    (P (EL n1 l)) /\ (EL n1 l = EL n2 l) ==> (n1 = n2)``,
  GEN_TAC THEN Induct THEN1 SRW_TAC[][] THEN
  SRW_TAC[][] THEN FULL_SIMP_TAC(srw_ss())[MEM_FILTER]
  THEN1 PROVE_TAC[] THEN
  Cases_on `n1` THEN Cases_on `n2` THEN
  FULL_SIMP_TAC(srw_ss())[MEM_EL] THEN
  PROVE_TAC[] )

val SUC_LEAST = store_thm("SUC_LEAST",
  ``!x. P x ==> (SUC ($LEAST P) = LEAST x. 0 < x /\ P (PRE x))``,
  GEN_TAC THEN STRIP_TAC THEN
  numLib.LEAST_ELIM_TAC THEN
  STRIP_TAC THEN1 PROVE_TAC[] THEN
  numLib.LEAST_ELIM_TAC THEN
  STRIP_TAC THEN1 (
    Q.EXISTS_TAC `SUC x` THEN
    SRW_TAC[][] ) THEN
  Q.X_GEN_TAC`nn` THEN
  STRIP_TAC THEN
  Q.X_GEN_TAC`m` THEN
  `?n. nn = SUC n` by ( Cases_on `nn` THEN SRW_TAC[][] THEN DECIDE_TAC ) THEN
  SRW_TAC[][] THEN
  FULL_SIMP_TAC(srw_ss())[] THEN
  `~(n < m)` by PROVE_TAC[] THEN
  `~(SUC m < SUC n)` by (
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    RES_TAC THEN
    FULL_SIMP_TAC(srw_ss())[] ) THEN
  DECIDE_TAC)

val fmap_linv_def = Define`
  fmap_linv f1 f2 ⇔ (FDOM f2 = FRANGE f1) /\ (!x. x IN FDOM f1 ==> (FLOOKUP f2 (FAPPLY f1 x) = SOME x))`

val fmap_linv_unique = store_thm("fmap_linv_unique",
  ``!f f1 f2. fmap_linv f f1 /\ fmap_linv f f2 ==> (f1 = f2)``,
  SRW_TAC[][fmap_linv_def,GSYM fmap_EQ_THM] THEN
  FULL_SIMP_TAC(srw_ss())[FRANGE_DEF,FLOOKUP_DEF] THEN
  PROVE_TAC[])

val INJ_has_fmap_linv = store_thm("INJ_has_fmap_linv",
  ``INJ (FAPPLY f) (FDOM f) (FRANGE f) ==> ?g. fmap_linv f g``,
  STRIP_TAC THEN
  Q.EXISTS_TAC `FUN_FMAP (\x. @y. FLOOKUP f y = SOME x) (FRANGE f)` THEN
  SRW_TAC[][fmap_linv_def,FLOOKUP_FUN_FMAP,FRANGE_DEF] THEN1 PROVE_TAC[] THEN
  SELECT_ELIM_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [INJ_DEF,FRANGE_DEF,FLOOKUP_DEF])

val has_fmap_linv_inj = store_thm("has_fmap_linv_inj",
  ``(?g. fmap_linv f g) = (INJ (FAPPLY f) (FDOM f) (FRANGE f))``,
  Tactical.REVERSE EQ_TAC THEN1 PROVE_TAC[INJ_has_fmap_linv] THEN
  SRW_TAC[][fmap_linv_def,INJ_DEF,EQ_IMP_THM]
  THEN1 ( SRW_TAC[][FRANGE_DEF] THEN PROVE_TAC[] )
  THEN1 ( FULL_SIMP_TAC(srw_ss())[FLOOKUP_DEF] THEN PROVE_TAC[] ))

val fmap_linv_FAPPLY = store_thm("fmap_linv_FAPPLY",
  ``fmap_linv f g /\ x IN FDOM f ==> (g ' (f ' x) = x)``,
  SRW_TAC[][fmap_linv_def,FLOOKUP_DEF])

val FLAT_EQ_NIL = store_thm("FLAT_EQ_NIL",
  ``!ls. (FLAT ls = []) = (EVERY ($= []) ls)``,
  Induct THEN SRW_TAC[][EQ_IMP_THM])

val ALL_DISTINCT_MAP_INJ = store_thm("ALL_DISTINCT_MAP_INJ",
  ``!ls f. (!x y. MEM x ls /\ MEM y ls /\ (f x = f y) ==> (x = y)) /\ ALL_DISTINCT ls  ==> ALL_DISTINCT (MAP f ls)``,
  Induct THEN SRW_TAC[][MEM_MAP] THEN PROVE_TAC[])

val o_f_cong = store_thm("o_f_cong",
  ``!f fm f' fm'.
    (fm = fm') /\
    (!v. v IN FRANGE fm ==> (f v = f' v))
    ==> (f o_f fm = f' o_f fm')``,
  SRW_TAC[DNF_ss][GSYM fmap_EQ_THM,FRANGE_DEF])
val _ = DefnBase.export_cong"o_f_cong"

val DRESTRICT_SUBSET_SUBMAP_gen = store_thm("DRESTRICT_SUBSET_SUBMAP_gen",
  ``!f1 f2 s t. DRESTRICT f1 s ⊑ DRESTRICT f2 s ∧ t ⊆ s
    ==> DRESTRICT f1 t ⊑ DRESTRICT f2 t``,
  rw[SUBMAP_DEF,DRESTRICT_DEF,SUBSET_DEF])

val SUBSET_DIFF_EMPTY = store_thm("SUBSET_DIFF_EMPTY",
  ``!s t. (s DIFF t = {}) = (s SUBSET t)``,
  SRW_TAC[][EXTENSION,SUBSET_DEF] THEN PROVE_TAC[])

val DIFF_INTER_SUBSET = store_thm("DIFF_INTER_SUBSET",
  ``!r s t. r SUBSET s ==> (r DIFF s INTER t = r DIFF t)``,
  SRW_TAC[][EXTENSION,SUBSET_DEF] THEN PROVE_TAC[])

val UNION_DIFF_2 = store_thm("UNION_DIFF_2",
  ``!s t. (s UNION (s DIFF t) = s)``,
  SRW_TAC[][EXTENSION] THEN PROVE_TAC[])

val DRESTRICT_FUNION_SAME = store_thm("DRESTRICT_FUNION_SAME",
  ``!fm s. FUNION (DRESTRICT fm s) fm = fm``,
  SRW_TAC[][GSYM SUBMAP_FUNION_ABSORPTION])

val REVERSE_ZIP = store_thm("REVERSE_ZIP",
  ``!l1 l2. (LENGTH l1 = LENGTH l2) ==>
    (REVERSE (ZIP (l1,l2)) = ZIP (REVERSE l1, REVERSE l2))``,
  Induct THEN SRW_TAC[][LENGTH_NIL_SYM] THEN
  Cases_on `l2` THEN FULL_SIMP_TAC(srw_ss())[] THEN
  SRW_TAC[][GSYM ZIP_APPEND])

val LENGTH_o_REVERSE = store_thm("LENGTH_o_REVERSE",
  ``(LENGTH o REVERSE = LENGTH) /\
    (LENGTH o REVERSE o f = LENGTH o f)``,
  SRW_TAC[][FUN_EQ_THM])

val REVERSE_o_REVERSE = store_thm("REVERSE_o_REVERSE",
  ``(REVERSE o REVERSE o f = f)``,
  SRW_TAC[][FUN_EQ_THM])

val GENLIST_PLUS_APPEND = store_thm("GENLIST_PLUS_APPEND",
  ``GENLIST ($+ a) n1 ++ GENLIST ($+ (n1 + a)) n2 = GENLIST ($+ a) (n1 + n2)``,
  rw[Once ADD_SYM,SimpRHS] >>
  srw_tac[ARITH_ss][GENLIST_APPEND] >>
  srw_tac[ETA_ss][ADD_ASSOC])

val count_add = store_thm("count_add",
  ``!n m. count (n + m) = count n UNION IMAGE ($+ n) (count m)``,
  SRW_TAC[ARITH_ss][EXTENSION,EQ_IMP_THM] THEN
  Cases_on `x < n` THEN SRW_TAC[ARITH_ss][] THEN
  Q.EXISTS_TAC `x - n` THEN
  SRW_TAC[ARITH_ss][])

val plus_compose = store_thm("plus_compose",
  ``!n:num m. $+ n o $+ m = $+ (n + m)``,
  SRW_TAC[ARITH_ss][FUN_EQ_THM])

val LIST_TO_SET_GENLIST = store_thm("LIST_TO_SET_GENLIST",
  ``!f n. LIST_TO_SET (GENLIST f n) = IMAGE f (count n)``,
  SRW_TAC[][EXTENSION,MEM_GENLIST] THEN PROVE_TAC[])

val DRESTRICT_EQ_DRESTRICT_SAME = store_thm("DRESTRICT_EQ_DRESTRICT_SAME",
  ``(DRESTRICT f1 s = DRESTRICT f2 s) ⇔
    (s INTER FDOM f1 = s INTER FDOM f2) /\
    (!x. x IN FDOM f1 /\ x IN s ==> (f1 ' x = f2 ' x))``,
  SRW_TAC[][DRESTRICT_EQ_DRESTRICT,SUBMAP_DEF,DRESTRICT_DEF,EXTENSION] THEN
  PROVE_TAC[])

val MEM_ZIP_MEM_MAP = store_thm("MEM_ZIP_MEM_MAP",
  ``(LENGTH (FST ps) = LENGTH (SND ps)) /\ MEM p (ZIP ps)
    ==> MEM (FST p) (FST ps) /\ MEM (SND p) (SND ps)``,
  Cases_on `p` >> Cases_on `ps` >> SRW_TAC[][] >>
  REV_FULL_SIMP_TAC(srw_ss())[MEM_ZIP,MEM_EL] THEN
  PROVE_TAC[])

val DISJOINT_GENLIST_PLUS = store_thm("DISJOINT_GENLIST_PLUS",
  ``DISJOINT x (set (GENLIST ($+ n) (a + b))) ==>
    DISJOINT x (set (GENLIST ($+ n) a)) /\
    DISJOINT x (set (GENLIST ($+ (n + a)) b))``,
  rw[GSYM GENLIST_PLUS_APPEND] >>
  metis_tac[DISJOINT_SYM,ADD_SYM])

(* TODO: use for Cevaluate_any_env?*)
val DRESTRICT_FUNION_SUBSET = store_thm("DRESTRICT_FUNION_SUBSET",
  ``s2 ⊆ s1 ⇒ ∃h. (DRESTRICT f s1 ⊌ g = DRESTRICT f s2 ⊌ h)``,
  strip_tac >>
  qexists_tac `DRESTRICT f s1 ⊌ g` >>
  match_mp_tac EQ_SYM >>
  REWRITE_TAC[GSYM SUBMAP_FUNION_ABSORPTION] >>
  rw[SUBMAP_DEF,DRESTRICT_DEF,FUNION_DEF] >>
  fs[SUBSET_DEF])

(* TODO: move to optionTheory *)
val IF_NONE_EQUALS_OPTION = store_thm(
  "IF_NONE_EQUALS_OPTION",
  ``(((if P then X else NONE) = NONE) <=> (P ==> IS_NONE X)) /\
    (((if P then NONE else X) = NONE) <=> (IS_SOME X ==> P)) /\
    (((if P then X else NONE) = SOME x) <=> P /\ (X = SOME x)) /\
    (((if P then NONE else X) = SOME x) <=> ~P /\ (X = SOME x))``,
  SRW_TAC [][]);
val _ = export_rewrites ["IF_NONE_EQUALS_OPTION"]

(* TODO: move elsewhere? export as rewrite? *)
val IN_option_rwt = store_thm(
"IN_option_rwt",
``(x ∈ case opt of NONE => {} | SOME y => Q y) ⇔
  (∃y. (opt = SOME y) ∧ x ∈ Q y)``,
Cases_on `opt` >> rw[EQ_IMP_THM])

val IN_option_rwt2 = store_thm(
"IN_option_rwt2",
``x ∈ option_CASE opt {} s ⇔ ∃y. (opt = SOME y) ∧ x ∈ s y``,
Cases_on `opt` >> rw[])

(* Re-expressing folds *)

val FOLDL2_FUPDATE_LIST = store_thm(
"FOLDL2_FUPDATE_LIST",
``!f1 f2 bs cs a. (LENGTH bs = LENGTH cs) ⇒
  (FOLDL2 (λfm b c. fm |+ (f1 b c, f2 b c)) a bs cs =
   a |++ ZIP (MAP2 f1 bs cs, MAP2 f2 bs cs))``,
SRW_TAC[][FUPDATE_LIST,FOLDL2_FOLDL,MAP2_MAP,ZIP_MAP,MAP_ZIP,
          rich_listTheory.FOLDL_MAP,rich_listTheory.LENGTH_MAP2,
          LENGTH_ZIP,pairTheory.LAMBDA_PROD])

val FOLDL2_FUPDATE_LIST_paired = store_thm(
"FOLDL2_FUPDATE_LIST_paired",
``!f1 f2 bs cs a. (LENGTH bs = LENGTH cs) ⇒
  (FOLDL2 (λfm b (c,d). fm |+ (f1 b c d, f2 b c d)) a bs cs =
   a |++ ZIP (MAP2 (λb. UNCURRY (f1 b)) bs cs, MAP2 (λb. UNCURRY (f2 b)) bs cs))``,
rw[FOLDL2_FOLDL,MAP2_MAP,ZIP_MAP,MAP_ZIP,LENGTH_ZIP,
   pairTheory.UNCURRY,pairTheory.LAMBDA_PROD,FUPDATE_LIST,
   rich_listTheory.FOLDL_MAP])

val FOLDL_FUPDATE_LIST = store_thm(
"FOLDL_FUPDATE_LIST",
``!f1 f2 ls a. FOLDL (\fm k. fm |+ (f1 k, f2 k)) a ls =
  a |++ MAP (\k. (f1 k, f2 k)) ls``,
SRW_TAC[][FUPDATE_LIST,rich_listTheory.FOLDL_MAP])

val FOLDR_CONS_triple = store_thm(
"FOLDR_CONS_triple",
``!f ls a. FOLDR (\(x,y,z) w. f x y z :: w) a ls = (MAP (\(x,y,z). f x y z) ls)++a``,
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Q.X_GEN_TAC `p` THEN
PairCases_on `p` THEN
SRW_TAC[][])

val FOLDR_CONS_5tup = store_thm(
"FOLDR_CONS_5tup",
``!f ls a. FOLDR (\(c,d,x,y,z) w. f c d x y z :: w) a ls = (MAP (\(c,d,x,y,z). f c d x y z) ls)++a``,
GEN_TAC THEN
Induct THEN1 SRW_TAC[][] THEN
Q.X_GEN_TAC `p` THEN
PairCases_on `p` THEN
SRW_TAC[][])

val FOLDR_transitive_property = store_thm(
"FOLDR_transitive_property",
``!P ls f a. P [] a /\ (!n a. n < LENGTH ls /\ P (DROP (SUC n) ls) a ==> P (DROP n ls) (f (EL n ls) a)) ==> P ls (FOLDR f a ls)``,
GEN_TAC THEN Induct THEN SRW_TAC[][] THEN
`P ls (FOLDR f a ls)` by (
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SRW_TAC[][] THEN
  Q.MATCH_ASSUM_RENAME_TAC `P (DROP (SUC n) ls) b` [] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`SUC n`,`b`] MP_TAC) THEN
  SRW_TAC[][] ) THEN
FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
SRW_TAC[][])

(* Re-expressing curried lambdas *)

val FST_triple = store_thm(
"FST_triple",
``(λ(n,ns,b). n) = FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val FST_5tup = store_thm(
"FST_5tup",
``(λ(n,ns,b,x,y). n) = FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val SND_triple = store_thm(
"SND_triple",
``(λ(n,ns,b). f ns b) = UNCURRY f o SND``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val FST_pair = store_thm(
"FST_pair",
``(λ(n,v). n) = FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val SND_pair = store_thm(
"SND_pair",
``(λ(n,v). v) = SND``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val SND_FST_pair = store_thm(
"SND_FST_pair",
``(λ((n,m),c).m) = SND o FST``,
rw[FUN_EQ_THM,pairTheory.UNCURRY])

val MAP_ZIP_SND_triple = store_thm(
"MAP_ZIP_SND_triple",
``(LENGTH l1 = LENGTH l2) ⇒ (MAP (λ(x,y,z). f y z) (ZIP(l1,l2)) = MAP (UNCURRY f) l2)``,
strip_tac >> (
MAP_ZIP
|> Q.GEN`g`
|> Q.ISPEC `UNCURRY (f:'b->'c->'d)`
|> SIMP_RULE(srw_ss())[combinTheory.o_DEF,pairTheory.LAMBDA_PROD]
|> UNDISCH_ALL
|> CONJUNCTS
|> Lib.el 4
|> MATCH_ACCEPT_TAC))

(* Specialisations to identity function *)

val INJ_I = store_thm(
"INJ_I",
``∀s t. INJ I s t ⇔ s ⊆ t``,
SRW_TAC[][INJ_DEF,SUBSET_DEF])

val MAP_KEYS_I = store_thm(
"MAP_KEYS_I",
``∀fm. MAP_KEYS I fm = fm``,
rw[GSYM fmap_EQ_THM,MAP_KEYS_def,EXTENSION] >>
metis_tac[MAP_KEYS_def,INJ_I,SUBSET_UNIV,combinTheory.I_THM])
val _ = export_rewrites["MAP_KEYS_I"]

val MAP_EQ_ID = store_thm(
"MAP_EQ_ID",
``!f ls. (MAP f ls = ls) = (!x. MEM x ls ==> (f x = x))``,
PROVE_TAC[MAP_EQ_f,MAP_ID,combinTheory.I_THM])

(* Specialisations to FEMPTY *)

val FUN_FMAP_FAPPLY_FEMPTY_FAPPLY = store_thm(
"FUN_FMAP_FAPPLY_FEMPTY_FAPPLY",
``FINITE s ==> (FUN_FMAP ($FAPPLY FEMPTY) s ' x = FEMPTY ' x)``,
Cases_on `x IN s` >>
rw[FUN_FMAP_DEF,NOT_FDOM_FAPPLY_FEMPTY])
val _ = export_rewrites["FUN_FMAP_FAPPLY_FEMPTY_FAPPLY"]

(* FUPDATE_LIST stuff *)

val FUPDATE_LIST_APPLY_NOT_MEM_matchable = store_thm(
"FUPDATE_LIST_APPLY_NOT_MEM_matchable",
``!kvl f k v. ~MEM k (MAP FST kvl) /\ (v = f ' k) ==> ((f |++ kvl) ' k = v)``,
PROVE_TAC[FUPDATE_LIST_APPLY_NOT_MEM])

val FUPDATE_LIST_APPLY_HO_THM = store_thm(
"FUPDATE_LIST_APPLY_HO_THM",
``∀P f kvl k.
(∃n. n < LENGTH kvl ∧ (k = EL n (MAP FST kvl)) ∧ P (EL n (MAP SND kvl)) ∧
     (∀m. n < m ∧ m < LENGTH kvl ⇒ EL m (MAP FST kvl) ≠ k)) ∨
(¬MEM k (MAP FST kvl) ∧ P (f ' k))
⇒ (P ((f |++ kvl) ' k))``,
metis_tac[FUPDATE_LIST_APPLY_MEM,FUPDATE_LIST_APPLY_NOT_MEM])

val FUPDATE_SAME_APPLY = store_thm(
"FUPDATE_SAME_APPLY",
``(x = FST kv) \/ (fm1 ' x = fm2 ' x) ==> ((fm1 |+ kv) ' x = (fm2 |+ kv) ' x)``,
Cases_on `kv` >> rw[FAPPLY_FUPDATE_THM])

val FUPDATE_SAME_LIST_APPLY = store_thm(
"FUPDATE_SAME_LIST_APPLY",
``!kvl fm1 fm2 x. MEM x (MAP FST kvl) ==> ((fm1 |++ kvl) ' x = (fm2 |++ kvl) ' x)``,
ho_match_mp_tac SNOC_INDUCT >>
conj_tac >- rw[] >>
rw[FUPDATE_LIST,FOLDL_SNOC] >>
match_mp_tac FUPDATE_SAME_APPLY >>
qmatch_rename_tac `(y = FST p) \/ Z` ["Z"] >>
Cases_on `y = FST p` >> rw[] >>
first_x_assum match_mp_tac >>
fs[MEM_MAP] >>
PROVE_TAC[])

val FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM = store_thm(
"FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM",
``!P ls k v fm. ALL_DISTINCT (MAP FST ls) ∧
  MEM (k,v) ls ∧
  P v ⇒
  P ((fm |++ ls) ' k)``,
rw[] >>
ho_match_mp_tac FUPDATE_LIST_APPLY_HO_THM >>
disj1_tac >>
fs[EL_ALL_DISTINCT_EL_EQ,MEM_EL] >>
qpat_assum `(k,v) = X` (assume_tac o SYM) >>
qexists_tac `n` >> rw[EL_MAP] >>
first_x_assum (qspecl_then [`n`,`m`] mp_tac) >>
rw[EL_MAP] >> spose_not_then strip_assume_tac >>
rw[] >> fs[])

val FUPDATE_LIST_ALL_DISTINCT_REVERSE = store_thm("FUPDATE_LIST_ALL_DISTINCT_REVERSE",
  ``∀ls. ALL_DISTINCT (MAP FST ls) ⇒ ∀fm. fm |++ (REVERSE ls) = fm |++ ls``,
  Induct >- rw[] >>
  qx_gen_tac `p` >> PairCases_on `p` >>
  rw[FUPDATE_LIST_APPEND,FUPDATE_LIST_THM] >>
  fs[] >>
  rw[FUPDATE_FUPDATE_LIST_COMMUTES])

(* FRANGE subset stuff *)

val IN_FRANGE = store_thm(
"IN_FRANGE",
``!f v. v IN FRANGE f ⇔ ?k. k IN FDOM f /\ (f ' k = v)``,
SRW_TAC[][FRANGE_DEF])

val FRANGE_FUPDATE_LIST_SUBSET = store_thm(
"FRANGE_FUPDATE_LIST_SUBSET",
``∀ls fm. FRANGE (fm |++ ls) ⊆ FRANGE fm ∪ (set (MAP SND ls))``,
Induct >- rw[FUPDATE_LIST_THM] >>
qx_gen_tac `p` >> qx_gen_tac `fm` >>
pop_assum (qspec_then `fm |+ p` mp_tac) >>
srw_tac[DNF_ss][SUBSET_DEF] >>
first_x_assum (qspec_then `x` mp_tac) >> fs[FUPDATE_LIST_THM] >>
rw[] >> fs[] >>
PairCases_on `p` >>
fsrw_tac[DNF_ss][FRANGE_FLOOKUP,FLOOKUP_UPDATE] >>
pop_assum mp_tac >> rw[] >>
PROVE_TAC[])

val IN_FRANGE_FUPDATE_LIST_suff = store_thm(
"IN_FRANGE_FUPDATE_LIST_suff",
``(∀v. v ∈ FRANGE fm ⇒ P v) ∧ (∀v. MEM v (MAP SND ls) ⇒ P v) ⇒
    ∀v. v ∈ FRANGE (fm |++ ls) ⇒ P v``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_FUPDATE_LIST_SUBSET) >>
PROVE_TAC[])

val FRANGE_FUNION_SUBSET = store_thm(
"FRANGE_FUNION_SUBSET",
``FRANGE (f1 ⊌ f2) ⊆ FRANGE f1 ∪ FRANGE f2``,
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,FUNION_DEF] >>
PROVE_TAC[])

val IN_FRANGE_FUNION_suff = store_thm(
"IN_FRANGE_FUNION_suff",
``(∀v. v ∈ FRANGE f1 ⇒ P v) ∧ (∀v. v ∈ FRANGE f2 ⇒ P v) ⇒
  (∀v. v ∈ FRANGE (f1 ⊌ f2) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_FUNION_SUBSET) >>
PROVE_TAC[])

val FRANGE_DOMSUB_SUBSET = store_thm(
"FRANGE_DOMSUB_SUBSET",
``FRANGE (fm \\ k) ⊆ FRANGE fm``,
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,DOMSUB_FAPPLY_THM] >>
PROVE_TAC[])

val IN_FRANGE_DOMSUB_suff = store_thm(
"IN_FRANGE_DOMSUB_suff",
``(∀v. v ∈ FRANGE fm ⇒ P v) ⇒ (∀v. v ∈ FRANGE (fm \\ k) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_DOMSUB_SUBSET) >>
PROVE_TAC[])

val FRANGE_DRESTRICT_SUBSET = store_thm(
"FRANGE_DRESTRICT_SUBSET",
``FRANGE (DRESTRICT fm s) ⊆ FRANGE fm``,
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,DRESTRICT_DEF] >>
PROVE_TAC[])

val IN_FRANGE_DRESTRICT_suff = store_thm(
"IN_FRANGE_DRESTRICT_suff",
``(∀v. v ∈ FRANGE fm ⇒ P v) ⇒ (∀v. v ∈ FRANGE (DRESTRICT fm s) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_DRESTRICT_SUBSET) >>
PROVE_TAC[])

val FRANGE_alist_to_fmap_SUBSET = store_thm(
"FRANGE_alist_to_fmap_SUBSET",
``FRANGE (alist_to_fmap ls) ⊆ IMAGE SND (set ls)``,
srw_tac[DNF_ss][FRANGE_DEF,SUBSET_DEF,pairTheory.EXISTS_PROD] >>
qmatch_assum_rename_tac `MEM z (MAP FST ls)`[] >>
qexists_tac `z` >>
match_mp_tac alist_to_fmap_FAPPLY_MEM >>
rw[])

val IN_FRANGE_alist_to_fmap_suff = store_thm(
"IN_FRANGE_alist_to_fmap_suff",
``(∀v. MEM v (MAP SND ls) ⇒ P v) ⇒ (∀v. v ∈ FRANGE (alist_to_fmap ls) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_alist_to_fmap_SUBSET) >>
fs[MEM_MAP] >>
PROVE_TAC[])

val FRANGE_FUPDATE_SUBSET = store_thm(
"FRANGE_FUPDATE_SUBSET",
``FRANGE (fm |+ kv) ⊆ FRANGE fm ∪ {SND kv}``,
Cases_on `kv` >>
rw[FRANGE_DEF,SUBSET_DEF,DOMSUB_FAPPLY_THM] >>
rw[] >> PROVE_TAC[])

val IN_FRANGE_FUPDATE_suff = store_thm(
"IN_FRANGE_FUPDATE_suff",
`` (∀v. v ∈ FRANGE fm ⇒ P v) ∧ (P (SND kv))
⇒ (∀v. v ∈ FRANGE (fm |+ kv) ⇒ P v)``,
rw[] >>
imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]FRANGE_FUPDATE_SUBSET) >>
fs[])

val IN_FRANGE_o_f_suff = store_thm("IN_FRANGE_o_f_suff",
  ``(∀v. v ∈ FRANGE fm ⇒ P (f v)) ⇒ ∀v. v ∈ FRANGE (f o_f fm) ⇒ P v``,
  rw[IN_FRANGE] >> rw[] >> first_x_assum match_mp_tac >> PROVE_TAC[])

(* DRESTRICT stuff *)

val DRESTRICT_SUBMAP_gen = store_thm(
"DRESTRICT_SUBMAP_gen",
``f SUBMAP g ==> DRESTRICT f P SUBMAP g``,
SRW_TAC[][SUBMAP_DEF,DRESTRICT_DEF])

val DRESTRICT_SUBSET_SUBMAP = store_thm(
"DRESTRICT_SUBSET_SUBMAP",
``s1 SUBSET s2 ==> DRESTRICT f s1 SUBMAP DRESTRICT f s2``,
SRW_TAC[][SUBMAP_DEF,SUBSET_DEF,DRESTRICT_DEF])

val DRESTRICTED_FUNION = store_thm(
"DRESTRICTED_FUNION",
``∀f1 f2 s. DRESTRICT (f1 ⊌ f2) s = DRESTRICT f1 s ⊌ DRESTRICT f2 (s DIFF FDOM f1)``,
rw[GSYM fmap_EQ_THM,DRESTRICT_DEF,FUNION_DEF] >> rw[] >>
rw[EXTENSION] >> PROVE_TAC[])

val FRANGE_DRESTRICT_SUBSET = store_thm(
"FRANGE_DRESTRICT_SUBSET",
``FRANGE (DRESTRICT fm s) ⊆ FRANGE fm``,
SRW_TAC[][FRANGE_DEF,SUBSET_DEF,DRESTRICT_DEF] THEN
SRW_TAC[][] THEN PROVE_TAC[])

val DRESTRICT_FDOM = store_thm(
"DRESTRICT_FDOM",
``!f. DRESTRICT f (FDOM f) = f``,
SRW_TAC[][GSYM fmap_EQ_THM,DRESTRICT_DEF])

(* alist MAP stuff *)

val alist_to_fmap_MAP_matchable = store_thm(
"alist_to_fmap_MAP_matchable",
``∀f1 f2 al mal v. INJ f1 (set (MAP FST al)) UNIV ∧
  (mal = MAP (λ(x,y). (f1 x,f2 y)) al) ∧
  (v = MAP_KEYS f1 (f2 o_f alist_to_fmap al)) ⇒
  (alist_to_fmap mal = v)``,
METIS_TAC[alist_to_fmap_MAP])

val MAP_values_fmap_to_alist = store_thm(
"MAP_values_fmap_to_alist",
``∀f fm. MAP (λ(k,v). (k, f v)) (fmap_to_alist fm) = fmap_to_alist (f o_f fm)``,
rw[fmap_to_alist_def,MAP_MAP_o,MAP_EQ_f])

val alist_to_fmap_MAP_values = store_thm(
"alist_to_fmap_MAP_values",
``∀f al. alist_to_fmap (MAP (λ(k,v). (k, f v)) al) = f o_f (alist_to_fmap al)``,
rw[] >>
Q.ISPECL_THEN [`I:γ->γ`,`f`,`al`] match_mp_tac alist_to_fmap_MAP_matchable >>
rw[INJ_I])

val set_MAP_FST_fmap_to_alist = store_thm(
"set_MAP_FST_fmap_to_alist",
``set (MAP FST (fmap_to_alist fm)) = FDOM fm``,
METIS_TAC[fmap_to_alist_to_fmap,FDOM_alist_to_fmap])
val _ = export_rewrites["set_MAP_FST_fmap_to_alist"]

(* Misc. *)

val EVERY2_MAP = store_thm("EVERY2_MAP",
  ``(EVERY2 P (MAP f l1) l2 = EVERY2 (λx y. P (f x) y) l1 l2) ∧
    (EVERY2 Q l1 (MAP g l2) = EVERY2 (λx y. Q x (g y)) l1 l2)``,
  rw[EVERY2_EVERY] >>
  Cases_on `LENGTH l1 = LENGTH l2` >> fs[] >>
  rw[ZIP_MAP,EVERY_MEM,MEM_MAP] >>
  srw_tac[DNF_ss][pairTheory.FORALL_PROD] >>
  PROVE_TAC[])

val exists_list_GENLIST = store_thm(
"exists_list_GENLIST",
``(∃ls. P ls) = (∃n f. P (GENLIST f n))``,
rw[EQ_IMP_THM] >- (
  map_every qexists_tac [`LENGTH ls`,`combin$C EL ls`] >>
  qmatch_abbrev_tac `P ls2` >>
  qsuff_tac `ls2 = ls` >- rw[] >>
  rw[LIST_EQ_REWRITE,Abbr`ls2`] ) >>
PROVE_TAC[])

val LESS_1 = store_thm(
"LESS_1",
``x < 1 ⇔ (x = 0:num)``,
DECIDE_TAC)
val _ = export_rewrites["LESS_1"]

val IMAGE_EQ_SING = store_thm("IMAGE_EQ_SING",
  ``(IMAGE f s = {z}) <=> (s <> {}) /\ !x. x IN s ==> (f x = z)``,
  EQ_TAC >>
  srw_tac[DNF_ss][EXTENSION] >>
  PROVE_TAC[])

val EVERY_MEM_MONO = store_thm("EVERY_MEM_MONO",
  ``∀P Q l. (∀x. MEM x l ∧ P x ⇒ Q x) ∧ EVERY P l ⇒ EVERY Q l``,
  ntac 2 gen_tac >> Induct >> rw[])

val EVERY2_MEM_MONO = store_thm("EVERY2_MEM_MONO",
  ``∀P Q l1 l2. (∀x. MEM x (ZIP (l1,l2)) ∧ UNCURRY P x ⇒ UNCURRY Q x) ∧ EVERY2 P l1 l2 ⇒ EVERY2 Q l1 l2``,
  rw[EVERY2_EVERY] >> match_mp_tac EVERY_MEM_MONO >> PROVE_TAC[])

val DRESTRICT_SUBSET = store_thm("DRESTRICT_SUBSET",
  ``∀f1 f2 s t.
    (DRESTRICT f1 s = DRESTRICT f2 s) ∧ t ⊆ s ⇒
    (DRESTRICT f1 t = DRESTRICT f2 t)``,
  rw[DRESTRICT_EQ_DRESTRICT]
    >- metis_tac[DRESTRICT_SUBSET_SUBMAP,SUBMAP_TRANS]
    >- metis_tac[DRESTRICT_SUBSET_SUBMAP,SUBMAP_TRANS] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,EXTENSION] >>
  metis_tac[])

val f_o_f_FUPDATE_compose = store_thm("f_o_f_FUPDATE_compose",
  ``∀f1 f2 k x v. x ∉ FDOM f1 ∧ x ∉ FRANGE f2 ⇒
    (f1 |+ (x,v) f_o_f f2 |+ (k,x) = (f1 f_o_f f2) |+ (k,v))``,
  rw[GSYM fmap_EQ_THM,f_o_f_DEF,FAPPLY_FUPDATE_THM] >>
  simp[] >> rw[] >> fs[] >> rw[EXTENSION] >>
  fs[IN_FRANGE] >> rw[]
  >- PROVE_TAC[]
  >- PROVE_TAC[] >>
  qmatch_assum_rename_tac`y <> k`[] >>
  `y ∈ FDOM (f1 f_o_f f2)` by rw[f_o_f_DEF] >>
  rw[f_o_f_DEF])

val _ = export_theory()
