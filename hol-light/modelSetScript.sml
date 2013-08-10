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

(*
val cardlt_CROSS = store_thm("cardlt_CROSS",
  ``x1 ≺ x2 ∧ y ≠ {} ⇒ x1 × y ≺ x2 × y``,
  rw[cardleq_def] >>
  spose_not_then strip_assume_tac >>
  `INJ (λex. IMAGE (FST o CURRY f ex) y) x2 (POW x1)` by (
    fs[INJ_DEF,IN_POW] >>
    simp[SUBSET_DEF,EXTENSION] >>
    fs[FORALL_PROD,EXISTS_PROD] >>
    conj_tac >- metis_tac[] >>
    
  `∃ey. ey ∈ y` by metis_tac[MEMBER_NOT_EMPTY] >>
  first_x_assum(qspec_then`λex. FST(f(ex,ey))`mp_tac) >>
  fs[INJ_DEF] >> rw[]

val cardlt_CROSS_cong = store_thm("cardlt_CROSS_cong",
  ``x1 ≺ x2 ∧ y1 ≺ y2 ⇒ x1 × y1 ≺ x2 × y2``,
  rw[cardlt_lenoteq] >- metis_tac[CARDLEQ_CROSS_CONG] >>
  CARDEQ_CROSS
  fs[cardeq_def,cardleq_def,BIJ_DEF] >>
  qx_gen_tac`g` >>
  spose_not_then strip_assume_tac >>
  `x2 ≠ {}` by metis_tac[INJ_EMPTY,SURJ_EMPTY] >>
  `y2 ≠ {}` by metis_tac[INJ_EMPTY,SURJ_EMPTY] >>
  `x2 × y2 ≠ {}` by metis_tac[CROSS_EMPTY_EQN] >>
  `x1 × y1 ≠ {}` by metis_tac[SURJ_EMPTY] >>
  `x1 ≠ {} ∧ y1 ≠ {}` by metis_tac[CROSS_EMPTY_EQN] >>
  `∃y. y ∈ y1` by metis_tac[MEMBER_NOT_EMPTY] >>
  hr
  `INJ (FST o (λx. g (x,y))) x1 x2` by (
    match_mp_tac INJ_COMPOSE >>
    qexists_tac`x2 × y2` >>
    conj_tac >- (
      fs[INJ_DEF,FORALL_PROD] >>
      metis_tac[] ) >>
    simp[INJ_DEF,FORALL_PROD]
    fs[INJ_DEF,Abbr`h`] >>
    map_every qx_gen_tac[`a`,`b`] >> strip_tac >>
    first_x_assum(qspecl_then[`a,y`,`b,y`]mp_tac) >>
    simp[]
    first
  `INJ (λ
  CROSS_EMPTY
  print_apropos``{} = x × y ``
  SURJ_EMPTY
  Cases_on`INJ g 
  rw[]
  INJ_CROSS
*)

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

val _ = export_theory()
