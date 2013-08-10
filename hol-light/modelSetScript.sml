open HolKernel boolLib boolSimps bossLib lcsymtacs pred_setTheory cardinalTheory pairTheory
val _ = numLib.prefer_num()
val _ = new_theory"modelSet"

val ind_model_exists = prove(
  ``∃x. (@s:num->bool. s ≠ {} ∧ FINITE s) x``,
    metis_tac[IN_DEF, MEMBER_NOT_EMPTY, IN_SING, FINITE_DEF])

val ind_model_ty =
  new_type_definition ("ind_model",ind_model_exists)
val ind_model_bij = define_new_type_bijections
  {ABS="mk_ind",REP="dest_ind",name="ind_model_bij",tyax=ind_model_ty}
val mk_ind_11     = prove_abs_fn_one_one ind_model_bij
val mk_ind_onto   = prove_abs_fn_onto    ind_model_bij
val dest_ind_11   = prove_rep_fn_one_one ind_model_bij
val dest_ind_onto = prove_rep_fn_onto    ind_model_bij

val inacc_exists = prove(
  ``∃x:num. UNIV x``,
  metis_tac[IN_UNIV,IN_DEF])

val inacc_ty =
  new_type_definition ("I",inacc_exists)
val inacc_bij = define_new_type_bijections
  {ABS="mk_I",REP="dest_I",name="inacc_bij",tyax=inacc_ty}
val mk_I_11     = prove_abs_fn_one_one inacc_bij
val mk_I_onto   = prove_abs_fn_onto    inacc_bij
val dest_I_11   = prove_rep_fn_one_one inacc_bij
val dest_I_onto = prove_rep_fn_onto    inacc_bij

val FINITE_CARD_LT = store_thm("FINITE_CARD_LT",
  ``∀s. FINITE s ⇔ s ≺ 𝕌(:num)``,
  metis_tac[INFINITE_Unum])

val lemma = prove(
  ``∀s. s ≺ 𝕌(:I) ⇔ FINITE s``,
  rw[FINITE_CARD_LT] >>
  match_mp_tac CARDEQ_CARDLEQ >>
  simp[cardeq_REFL] >>
  match_mp_tac cardleq_ANTISYM >>
  simp[cardleq_def,INJ_DEF] >>
  metis_tac[inacc_bij,dest_I_11,mk_I_11,IN_UNIV,IN_DEF])

val I_AXIOM = store_thm("I_AXIOM",
  ``𝕌(:ind_model) ≺ 𝕌(:I) ∧
    ∀s. s ≺ 𝕌(:I) ⇒ POW s ≺ 𝕌(:I)``,
  simp[lemma,FINITE_POW] >>
  `UNIV = IMAGE mk_ind (@s. s ≠ {} ∧ FINITE s)` by (
    simp[Once EXTENSION,IN_DEF,ind_model_bij] >>
    metis_tac[ind_model_bij]) >>
  metis_tac[IMAGE_FINITE,NOT_INSERT_EMPTY,FINITE_EMPTY,FINITE_INSERT])

(* TODO: move *)

val POW_EMPTY = store_thm("POW_EMPTY",
  ``POW x ≠ {}``,
  SRW_TAC[][EXTENSION,IN_POW] THEN
  METIS_TAC[EMPTY_SUBSET])
val _ = export_rewrites["POW_EMPTY"]

val CARDLEQ_FINITE = store_thm("CARDLEQ_FINITE",
  ``∀s1 s2. FINITE s2 ∧ s1 ≼ s2 ⇒ FINITE s1``,
  metis_tac[cardleq_def,FINITE_INJ])

val CARDLEQ_CARD = store_thm("CARDLEQ_CARD",
  ``FINITE s1 ∧ FINITE s2 ⇒ (s1 ≼ s2 ⇔ CARD s1 ≤ CARD s2)``,
  rw[EQ_IMP_THM] >-
    metis_tac[cardleq_def,INJ_CARD] >>
  Cases_on`CARD s1 = CARD s2` >-
    metis_tac[cardleq_lteq,CARDEQ_CARD_EQN] >>
  simp[Once cardleq_lteq] >> disj1_tac >>
  simp[cardleq_def] >>
  gen_tac >> match_mp_tac PHP >>
  fsrw_tac[ARITH_ss][])

val CARD_LT_CARD = store_thm("CARD_LT_CARD",
  ``FINITE s1 ∧ FINITE s2 ⇒ (s1 ≺ s2 ⇔ CARD s1 < CARD s2)``,
  rw[] >> simp[cardlt_lenoteq,CARDLEQ_CARD,CARDEQ_CARD_EQN])

val cardlt_leq_trans = store_thm("cardlt_leq_trans",
  ``∀r s t. r ≺ s ∧ s ≼ t ⇒ r ≺ t``,
  rw[cardlt_lenoteq] >- metis_tac[cardleq_TRANS] >>
  metis_tac[CARDEQ_CARDLEQ,cardeq_REFL,cardleq_ANTISYM])

val cardleq_lt_trans = store_thm("cardleq_lt_trans",
  ``∀r s t. r ≼ s ∧ s ≺ t ⇒ r ≺ t``,
  rw[cardlt_lenoteq] >- metis_tac[cardleq_TRANS] >>
  metis_tac[CARDEQ_CARDLEQ,cardeq_REFL,cardleq_ANTISYM])

val cardleq_empty = store_thm("cardleq_empty",
  ``x ≼ {} ⇔ x = {}``,
  simp[cardleq_lteq,CARDEQ_0])

val CROSS_EMPTY_EQN = store_thm("CROSS_EMPTY_EQN",
  ``s × t = {} ⇔ s = {} ∨ t = {}``,
  rw[EQ_IMP_THM] >> rw[CROSS_EMPTY] >>
  fs[EXTENSION,pairTheory.FORALL_PROD] >>
  metis_tac[])

val CARDEQ_CROSS_SYM = store_thm("CARDEQ_CROSS_SYM",
  ``s × t ≈ t × s``,
  simp[cardeq_def] >>
  qexists_tac`λp. (SND p,FST p)` >>
  simp[BIJ_IFF_INV] >>
  qexists_tac`λp. (SND p,FST p)` >>
  simp[])

val CARD_MUL_ABSORB_LE = store_thm("CARD_MUL_ABSORB_LE",
  ``∀s t. INFINITE t ∧ s ≼ t ⇒ s × t ≼ t``,
  metis_tac[CARDLEQ_CROSS_CONG,SET_SQUARED_CARDEQ_SET,
            cardleq_lteq,cardleq_TRANS,cardleq_REFL])

val CARD_MUL_LT_LEMMA = store_thm("CARD_MUL_LT_LEMMA",
  ``∀s t. s ≼ t ∧ t ≺ u ∧ INFINITE u ⇒ s × t ≺ u``,
  rw[] >>
  Cases_on`FINITE t` >- (
    metis_tac[CARDLEQ_FINITE,FINITE_CROSS] ) >>
  metis_tac[CARD_MUL_ABSORB_LE,cardleq_lt_trans])

val CARD_MUL_LT_INFINITE = store_thm("CARD_MUL_LT_INFINITE",
  ``∀s t. s ≺ t ∧ t ≺ u ∧ INFINITE u ⇒ s × t ≺ u``,
  metis_tac[CARD_MUL_LT_LEMMA,cardleq_lteq])

val I_INFINITE = store_thm("I_INFINITE",
  ``INFINITE 𝕌(:I)``,
  DISCH_TAC >>
  Q.ISPEC_THEN`count (CARD 𝕌(:I) - 1)`mp_tac (CONJUNCT2 I_AXIOM) >>
  simp[] >>
  simp[CARD_LT_CARD,CARDLEQ_CARD,FINITE_POW] >>
  conj_asm1_tac >- (
    imp_res_tac CARD_EQ_0 >>
    fs[EXTENSION] >> DECIDE_TAC ) >>
  match_mp_tac(DECIDE``a - 1 < b ∧ 0 < a ==> a <= b``) >>
  reverse conj_tac >- pop_assum ACCEPT_TAC >>
  qmatch_abbrev_tac`n < CARD (POW (count n))` >>
  rpt (pop_assum kall_tac) >>
  Induct_on`n` >>
  simp[COUNT_SUC,POW_EQNS] >>
  qmatch_abbrev_tac`SUC n < CARD (a ∪ b)` >>
  `FINITE a ∧ FINITE b` by simp[Abbr`a`,Abbr`b`,IMAGE_FINITE,FINITE_POW] >>
  `∀s. s ∈ b ⇒ ∀x. x ∈ s ⇒ x < n` by (
    simp[Abbr`b`,IN_POW,SUBSET_DEF] ) >>
  `∀s. s ∈ a ⇒ n ∈ s` by (
    simp[Abbr`a`,GSYM LEFT_FORALL_IMP_THM] ) >>
  `a ∩ b = {}` by (
    simp[Once EXTENSION] >>
    metis_tac[prim_recTheory.LESS_REFL] ) >>
  qsuff_tac`SUC n < CARD a + CARD b`>-
    metis_tac[DECIDE``a + 0 = a``,CARD_EMPTY,CARD_UNION] >>
  fs[Abbr`b`,CARD_POW] >>
  qsuff_tac`CARD a ≠ 0`>-DECIDE_TAC>>
  simp[CARD_EQ_0,Abbr`a`] >>
  simp[EXTENSION,IN_POW] >>
  qexists_tac`{}`>>simp[])

val I_PAIR_EXISTS = prove(
  ``∃f:I#I->I. !x y. (f x = f y) ==> (x = y)``,
  qsuff_tac `𝕌(:I#I) ≼ 𝕌(:I)` >-
    simp[cardleq_def,INJ_DEF] >>
  match_mp_tac CARDEQ_SUBSET_CARDLEQ >>
  qsuff_tac`𝕌(:I#I) = 𝕌(:I) × 𝕌(:I)` >-
    metis_tac[cardeq_TRANS,SET_SQUARED_CARDEQ_SET,I_INFINITE] >>
  simp[EXTENSION])

val INJ_LEMMA = METIS_PROVE[]``(!x y. (f x = f y) ==> (x = y)) <=> (!x y. (f x = f y) <=> (x = y))``

val I_PAIR_def =
  new_specification("I_PAIR_def",["I_PAIR"],
    REWRITE_RULE[INJ_LEMMA] I_PAIR_EXISTS)

val CARD_BOOL_LT_I = store_thm("CARD_BOOL_LT_I",
  ``𝕌(:bool) ≺ 𝕌(:I)``,
  strip_tac >> mp_tac I_INFINITE >> simp[] >>
  match_mp_tac (INST_TYPE[beta|->``:bool``]CARDLEQ_FINITE) >>
  HINT_EXISTS_TAC >> simp[UNIV_BOOL])

val I_BOOL_EXISTS = prove(
  ``∃f:bool->I. !x y. (f x = f y) ==> (x = y)``,
  `𝕌(:bool) ≼ 𝕌(:I)` by metis_tac[CARD_BOOL_LT_I,cardlt_lenoteq] >>
  fs[cardleq_def,INJ_DEF] >> metis_tac[])

val I_BOOL_def =
  new_specification("I_BOOL_def",["I_BOOL"],
    REWRITE_RULE[INJ_LEMMA] I_BOOL_EXISTS)

val I_IND_EXISTS = prove(
  ``∃f:ind_model->I. !x y. (f x = f y) ==> (x = y)``,
  `𝕌(:ind_model) ≼ 𝕌(:I)` by metis_tac[I_AXIOM,cardlt_lenoteq] >>
  fs[cardleq_def,INJ_DEF] >> metis_tac[])

val I_IND_def =
  new_specification("I_IND_def",["I_IND"],
    REWRITE_RULE[INJ_LEMMA] I_IND_EXISTS)

val I_SET_EXISTS = prove(
  ``∀s:I->bool. s ≺ 𝕌(:I) ⇒ ∃f:(I->bool)->I. !x y. x ⊆ s ∧ y ⊆ s ∧ (f x = f y) ==> (x = y)``,
  gen_tac >> disch_then(strip_assume_tac o MATCH_MP(CONJUNCT2 I_AXIOM)) >>
  fs[cardlt_lenoteq] >>
  fs[cardleq_def,INJ_DEF,IN_POW] >>
  metis_tac[])

val I_SET_def =
  new_specification("I_SET_def",["I_SET"],
    SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] I_SET_EXISTS)

val _ = Hol_datatype`
  setlevel = Ur_bool
           | Ur_ind
           | Powerset of setlevel
           | Cartprod of setlevel => setlevel`

val setlevel_def = Define`
  setlevel Ur_bool = IMAGE I_BOOL UNIV ∧
  setlevel Ur_ind = IMAGE I_IND UNIV ∧
  setlevel (Cartprod l1 l2) =
    IMAGE I_PAIR (setlevel l1 × setlevel l2) ∧
  setlevel (Powerset l) =
    IMAGE (I_SET (setlevel l)) (POW (setlevel l))`

val setlevel_CARD = store_thm("setlevel_CARD",
  ``∀l. setlevel l ≺ 𝕌(:I)``,
  Induct >> simp_tac std_ss [setlevel_def]
  >- (
    strip_tac >>
    match_mp_tac (ISPEC``𝕌(:I)``(GEN_ALL cardlt_REFL)) >>
    metis_tac[cardleq_TRANS,IMAGE_cardleq,cardleq_lt_trans,CARD_BOOL_LT_I])
  >- (
    strip_tac >>
    match_mp_tac (ISPEC``𝕌(:I)``(GEN_ALL cardlt_REFL)) >>
    metis_tac[cardleq_TRANS,IMAGE_cardleq,cardleq_lt_trans,I_AXIOM])
  >- (
    strip_tac >>
    match_mp_tac (ISPEC``𝕌(:I)``(GEN_ALL cardlt_REFL)) >>
    metis_tac[cardleq_TRANS,IMAGE_cardleq,cardleq_lt_trans,I_AXIOM])
  >- (
    strip_tac >>
    match_mp_tac (ISPEC``𝕌(:I)``(GEN_ALL cardlt_REFL)) >>
    qmatch_assum_abbrev_tac`𝕌(:I) ≼ IMAGE I_PAIR (s × t)` >>
    `𝕌(:I) ≼ s × t` by metis_tac[IMAGE_cardleq,cardleq_TRANS] >>
    qsuff_tac`s × t ≺ 𝕌(:I) ∨ t × s ≺ 𝕌(:I)` >-
      metis_tac[cardleq_lt_trans,CARDEQ_CROSS_SYM,cardleq_TRANS,cardleq_lteq] >>
    metis_tac[cardleq_dichotomy,CARD_MUL_LT_LEMMA,I_INFINITE]))

val I_SET_SETLEVEL = store_thm("I_SET_SETLEVEL",
  ``∀l s t. s ⊆ setlevel l ∧ t ⊆ setlevel l ∧
            (I_SET (setlevel l) s = I_SET (setlevel l) t)
            ⇒ s = t``,
  metis_tac[setlevel_CARD,I_SET_def])

val universe_def = Define`
  universe = {(t,x) | x ∈ setlevel t}`

val v_exists = prove(
  ``∃a. a ∈ universe``,
  qexists_tac`Ur_bool,I_BOOL T` >>
  rw[universe_def,setlevel_def])

val v_ty =
  new_type_definition ("V",SIMP_RULE std_ss [IN_DEF]v_exists)
val v_bij = define_new_type_bijections
  {ABS="mk_V",REP="dest_V",name="v_bij",tyax=v_ty}
val mk_V_11     = prove_abs_fn_one_one v_bij
val mk_V_onto   = prove_abs_fn_onto    v_bij
val dest_V_11   = prove_rep_fn_one_one v_bij
val dest_V_onto = prove_rep_fn_onto    v_bij

val universe_IN = prove(
  ``universe x ⇔ x ∈ universe``,
  rw[IN_DEF])

val V_bij = store_thm("V_bij",
  ``∀l e. e ∈ setlevel l ⇔ dest_V(mk_V(l,e)) = (l,e)``,
  rw[GSYM(CONJUNCT2 v_bij)] >>
  rw[universe_IN,universe_def])

val droplevel_def = Define`
  droplevel (Powerset l) = l`

val isasetlevel = Define`
  isasetlevel (Powerset _) = T ∧
  isasetlevel _ = F`

val level_def = Define`
  level x = FST(dest_V x)`

val element_def = Define`
  element x = SND(dest_V x)`

val ELEMENT_IN_LEVEL = store_thm("ELEMENT_IN_LEVEL",
  ``∀x. (element x) ∈ setlevel (level x)``,
  rw[element_def,level_def,V_bij,v_bij])

val SET = store_thm("SET",
  ``∀x. mk_V(level x,element x) = x``,
  rw[level_def,element_def,v_bij])

val set_def = Define`
  set x = @s. s ⊆ (setlevel(droplevel(level x))) ∧
              I_SET (setlevel(droplevel(level x))) s = element x`

val isaset_def = Define`
  isaset x ⇔ ∃l. level x = Powerset l`

val _ = Parse.add_infix("<:",425,Parse.NONASSOC)

val inset_def = xDefine"inset"
  `x <: s ⇔ level s = Powerset(level x) ∧ element x ∈ set s`

val _ = Parse.add_infix("<=:",450,Parse.NONASSOC)

val subset_def = xDefine"subset"`
  s <=: t ⇔ level s = level t ∧ ∀x. x <: s ⇒ x <: t`

val MEMBERS_ISASET = store_thm("MEMBERS_ISASET",
  ``∀x s. x <: s ⇒ isaset s``,
  rw[inset_def,isaset_def])

val LEVEL_NONEMPTY = store_thm("LEVEL_NONEMPTY",
  ``∀l. ∃x. x ∈ setlevel l``,
  simp[MEMBER_NOT_EMPTY] >>
  Induct >> rw[setlevel_def,CROSS_EMPTY_EQN])

val LEVEL_SET_EXISTS = store_thm("LEVEL_SET_EXISTS",
  ``∀l. ∃s. level s = l``,
  mp_tac LEVEL_NONEMPTY >>
  simp[V_bij,level_def] >>
  metis_tac[FST])

val MK_V_CLAUSES = store_thm("MK_V_CLAUSES",
  ``e ∈ setlevel l ⇒
      level(mk_V(l,e)) = l ∧ element(mk_V(l,e)) = e``,
  rw[level_def,element_def,V_bij])

val MK_V_SET = store_thm("MK_V_SET",
  ``s ⊆ setlevel l ⇒
    set(mk_V(Powerset l,I_SET (setlevel l) s)) = s ∧
    level(mk_V(Powerset l,I_SET (setlevel l) s)) = Powerset l ∧
    element(mk_V(Powerset l,I_SET (setlevel l) s)) = I_SET (setlevel l) s``,
  strip_tac >>
  `I_SET (setlevel l) s ∈ setlevel (Powerset l)` by (
    rw[setlevel_def,IN_POW] ) >>
  simp[MK_V_CLAUSES] >>
  simp[set_def,MK_V_CLAUSES,droplevel_def] >>
  SELECT_ELIM_TAC >>
  metis_tac[I_SET_SETLEVEL])

val EMPTY_EXISTS = prove(
  ``∀l. ∃s. level s = l ∧ ∀x. ¬(x <: s)``,
  Induct >> TRY (
    qexists_tac`mk_V(Powerset l,I_SET(setlevel l){})` >>
    simp[inset_def,MK_V_CLAUSES,MK_V_SET] >> NO_TAC ) >>
  metis_tac[LEVEL_SET_EXISTS,MEMBERS_ISASET,isaset_def,theorem"setlevel_distinct"])

val emptyset_def =
  new_specification("emptyset_def",["emptyset"],
    SIMP_RULE std_ss [SKOLEM_THM] EMPTY_EXISTS)

val COMPREHENSION_EXISTS = prove(
  ``∀s p. ∃t. level t = level s ∧ ∀x. x <: t ⇔ x <: s ∧ p x``,
  rpt gen_tac >>
  reverse(Cases_on`isaset s`) >- metis_tac[MEMBERS_ISASET] >>
  fs[isaset_def] >>
  qspec_then`s`mp_tac ELEMENT_IN_LEVEL >>
  simp[setlevel_def,IN_POW] >>
  disch_then(Q.X_CHOOSE_THEN`u`strip_assume_tac) >>
  qabbrev_tac`v = {i | i ∈ u ∧ p(mk_V(l,i))}` >>
  qexists_tac`mk_V(Powerset l,I_SET (setlevel l) v)` >>
  `v ⊆ setlevel l` by (
    fs[SUBSET_DEF,Abbr`v`] ) >>
  simp[MK_V_SET,inset_def] >>
  fs[Abbr`v`] >>
  metis_tac[SET,MK_V_SET])

val _ = Parse.add_infix("suchthat",9,Parse.LEFT)

val suchthat_def =
  new_specification("suchthat_def",["suchthat"],
    SIMP_RULE std_ss [SKOLEM_THM] COMPREHENSION_EXISTS)

val SETLEVEL_EXISTS = store_thm("SETLEVEL_EXISTS",
  ``∀l. ∃s. (level s = Powerset l) ∧
            ∀x. x <: s ⇔ level x = l ∧ element x ∈ setlevel l``,
  gen_tac >>
  qexists_tac`mk_V(Powerset l,I_SET (setlevel l) (setlevel l))` >>
  simp[MK_V_SET,inset_def] >> metis_tac[])

val SET_DECOMP = store_thm("SET_DECOMP",
  ``∀s. isaset s ⇒
        set s ⊆ setlevel(droplevel(level s)) ∧
        I_SET (setlevel(droplevel(level s))) (set s) = element s``,
  gen_tac >> simp[isaset_def] >> strip_tac >>
  simp[set_def] >>
  SELECT_ELIM_TAC >>
  simp[setlevel_def,droplevel_def] >>
  qspec_then`s`mp_tac ELEMENT_IN_LEVEL >>
  simp[setlevel_def,IN_POW] >>
  metis_tac[])

val SET_SUBSET_SETLEVEL = store_thm("SET_SUBSET_SETLEVEL",
  ``∀s. isaset s ⇒ set s ⊆ setlevel(droplevel(level s))``,
  metis_tac[SET_DECOMP])

val POWERSET_EXISTS = prove(
  ``∀s. ∃t. level t = Powerset(level s) ∧ ∀x. x <: t ⇔ x <=: s``,
  gen_tac >> Cases_on`isaset s` >- (
    fs[isaset_def] >>
    qspec_then`Powerset l`(Q.X_CHOOSE_THEN`t`strip_assume_tac)
      SETLEVEL_EXISTS >>
    qexists_tac`t suchthat (λx. x <=: s)` >>
    simp[suchthat_def,subset_def] >>
    metis_tac[ELEMENT_IN_LEVEL] ) >>
  fs[subset_def] >>
  metis_tac[MEMBERS_ISASET,SETLEVEL_EXISTS
           ,ELEMENT_IN_LEVEL,isaset_def])

val powerset_def =
  new_specification("powerset_def",["powerset"],
    SIMP_RULE std_ss [SKOLEM_THM] POWERSET_EXISTS)

val pair_def = Define`
  pair x y = mk_V(Cartprod (level x) (level y),
                  I_PAIR(element x,element y))`

val PAIR_IN_LEVEL = store_thm("PAIR_IN_LEVEL",
  ``∀x y l m. x ∈ setlevel l ∧ y ∈ setlevel m
              ⇒ I_PAIR(x,y) ∈ setlevel (Cartprod l m)``,
  simp[setlevel_def])

val DEST_MK_PAIR = store_thm("DEST_MK_PAIR",
  ``dest_V(pair x y) = (Cartprod (level x) (level y), I_PAIR(element x,element y))``,
  simp[pair_def,GSYM V_bij] >>
  simp[PAIR_IN_LEVEL,ELEMENT_IN_LEVEL])

val PAIR_INJ = store_thm("PAIR_INJ",
  ``∀x1 y1 x2 y2. (pair x1 y1 = pair x2 y2) ⇔ (x1 = x2) ∧ (y1 = y2)``,
  simp[EQ_IMP_THM] >> rpt gen_tac >>
  disch_then(assume_tac o AP_TERM``dest_V``) >>
  fs[DEST_MK_PAIR,I_PAIR_def] >>
  fs[level_def,element_def] >>
  metis_tac[v_bij,PAIR_EQ,FST,SND,pair_CASES])

val LEVEL_PAIR = store_thm("LEVEL_PAIR",
  ``∀x y. level(pair x y) = Cartprod (level x) (level y)``,
  rw[level_def,DEST_MK_PAIR])

val fst_def = Define`
  fst p = @x. ∃y. p = pair x y`

val snd_def = Define`
  snd p = @y. ∃x. p = pair x y`

val PAIR_CLAUSES = store_thm("PAIR_CLAUSES",
  ``∀x y. (fst(pair x y) = x) ∧ (snd(pair x y) = y)``,
  rw[fst_def,snd_def] >> metis_tac[PAIR_INJ])

val _ = export_theory()
