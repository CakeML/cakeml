open HolKernel bossLib boolLib boolSimps SatisfySimps listTheory rich_listTheory pairTheory pred_setTheory finite_mapTheory alistTheory relationTheory arithmeticTheory sortingTheory lcsymtacs quantHeuristicsLib quantHeuristicsLibAbbrev
open miscTheory libTheory evalPropsTheory miscLib bytecodeTheory bytecodeTerminationTheory bytecodeEvalTheory bytecodeExtraTheory bytecodeLabelsTheory intLangTheory toBytecodeTheory compilerTerminationTheory intLangExtraTheory
open exhLangProofTheory patLangProofTheory
val _ = new_theory "bytecodeProof"
val _ = numLib.prefer_num()
val _ = Parse.bring_to_front_overload"++"{Name="APPEND",Thy="list"}

(* Cv_bv relation *)

val _ = Hol_datatype`refs_data = <| sm : num list; cls : num |-> (Cv list # def list # num) |>`

val with_same_sm = store_thm("with_same_sm",
  ``rd with sm := rd.sm = rd``,
  rw[theorem"refs_data_component_equality"])
val _ = export_rewrites["with_same_sm"]

val (Cv_bv_rules,Cv_bv_ind,Cv_bv_cases) = Hol_reln`
  (Cv_bv pp (CLitv (IntLit k)) (Number k)) ∧
  (Cv_bv pp (CLitv (Word8 w)) (Number (&w2n w))) ∧
  (Cv_bv pp (CLitv (StrLit s)) (Block string_tag (MAP (Number o $& o ORD) s))) ∧
  (Cv_bv pp (CLitv (Bool b)) (bool_to_val b)) ∧
  (Cv_bv pp (CLitv Unit) unit_val) ∧
  ((el_check m (FST pp).sm = SOME p) ⇒ Cv_bv pp (CLoc m) (RefPtr p)) ∧
  (EVERY2 (Cv_bv pp) vs bvs ⇒ Cv_bv pp (CConv cn vs) (Block (cn+block_tag) bvs)) ∧
  (EVERY2 (Cv_bv pp) vs bvs ⇒ Cv_bv pp (CVectorv vs) (Block vector_tag bvs)) ∧
  ((pp = (rd,l2a)) ∧
   (el_check n defs = SOME (SOME (l,cc,(recs,envs)),azb)) ∧
   EVERY (λn. n < LENGTH defs) recs ∧
   EVERY (λn. n < LENGTH env) envs ∧
   (l2a l = SOME a) ∧
   benv_bvs pp bvs (recs,envs) env defs
   ⇒ Cv_bv pp (CRecClos env defs n) (Block closure_tag [CodePtr a; Block 0 bvs])) ∧
  ((pp = (rd,l2a)) ∧
   (ce= (recs,envs)) ∧
   (LENGTH bvs = LENGTH recs + LENGTH envs) ∧
   (∀i x bv. i < LENGTH recs ∧ (x = EL i recs) ∧ (bv = EL i bvs) ⇒
     x < LENGTH defs ∧
     ∃p. (bv = RefPtr p) ∧ ∃jenv jdefs jx. (FLOOKUP rd.cls p = SOME (jenv,jdefs,jx)) ∧ syneq (CRecClos jenv jdefs jx) (CRecClos env defs x)) ∧
   (∀i x bv. i < LENGTH envs ∧ (x = EL i envs) ∧ (bv = EL (LENGTH recs + i) bvs) ⇒
       x < LENGTH env ∧ Cv_bv pp (EL x env) bv)
   ⇒ benv_bvs pp bvs ce env defs)`

val Cv_bv_only_ind =
  Cv_bv_ind
|> SPEC_ALL
|> UNDISCH
|> CONJUNCT1
|> DISCH_ALL
|> Q.GEN`benv_bvs'`
|> Q.SPEC`K(K(K(K T)))`
|> SIMP_RULE std_ss []
|> GEN_ALL

(* TODO - need a different approach to printing to avoid confusing words with integers
val Cv_bv_ov = store_thm("Cv_bv_ov",
  ``∀m pp Cv bv. Cv_bv pp Cv bv ⇒ (Cv_to_ov Cv = bv_to_ov bv)``,
  ntac 2 gen_tac >>
  ho_match_mp_tac Cv_bv_only_ind >>
  strip_tac >- rw[bv_to_ov_def] >>
  strip_tac >- rw[bv_to_ov_def] >>
  strip_tac >- (
    rw[bv_to_ov_def] >>
    rw[bvs_to_chars_thm,EVERY_MAP] >>
    rw[LIST_EQ_REWRITE,
       stringTheory.IMPLODE_EXPLODE_I,
       integerTheory.INT_ABS_NUM,
       EL_MAP,stringTheory.CHR_ORD]) >>
  strip_tac >- (
    rw[bv_to_ov_def] >>
    Cases_on `b` >> fs[] ) >>
  strip_tac >- rw[bv_to_ov_def] >>
  strip_tac >- rw[bv_to_ov_def,el_check_def] >>
  strip_tac >- (
    rw[bv_to_ov_def] >>
    fsrw_tac[ARITH_ss][] >>
    rw[MAP_EQ_EVERY2] >>
    fs[EVERY2_EVERY] ) >>
  rw[bv_to_ov_def])
*)

val Cv_bv_strongind = theorem"Cv_bv_strongind"

val Cv_bv_syneq = store_thm("Cv_bv_syneq",
  ``(∀v1 bv. Cv_bv pp v1 bv ⇒ ∀v2. syneq v1 v2 ⇒ Cv_bv pp v2 bv) ∧
    (∀bvs ce env1 defs1. benv_bvs pp bvs ce env1 defs1 ⇒
      ∀env2 defs2 V U n1 n2 l cc azb.
        syneq_defs (LENGTH env1) (LENGTH env2) V defs1 defs2 U ∧ n1 < LENGTH defs1 ∧ n2 < LENGTH defs2 ∧ U n1 n2 ∧
        (EL n1 defs1 = (SOME (l,cc,ce),azb)) ∧ EVERY (λn. n < LENGTH defs1) (FST ce) ∧ EVERY (λn. n < LENGTH env1) (SND ce) ∧
        (∀v1 v2. V v1 v2 ⇒ v1 < LENGTH env1 ∧ v2 < LENGTH env2 ∧ syneq (EL v1 env1) (EL v2 env2))
        ⇒ benv_bvs pp bvs ce env2 defs2)``,
  ho_match_mp_tac (Cv_bv_strongind) >>
  strip_tac >- ( simp[Once Cv_bv_cases] ) >>
  strip_tac >- ( simp[Once Cv_bv_cases] ) >>
  strip_tac >- ( simp[Once Cv_bv_cases] ) >>
  strip_tac >- ( simp[Once Cv_bv_cases] ) >>
  strip_tac >- ( simp[Once Cv_bv_cases] ) >>
  strip_tac >- ( simp[Once Cv_bv_cases] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >>
    rw[Once Cv_bv_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    rfs[MEM_ZIP] >> fs[MEM_ZIP] >>
    fsrw_tac[DNF_ss][] ) >>
  strip_tac >- (
    rw[] >> pop_assum mp_tac >>
    simp[Once syneq_cases] >>
    rw[Once Cv_bv_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    rfs[MEM_ZIP] >> fs[MEM_ZIP] >>
    fsrw_tac[DNF_ss][] ) >>
  strip_tac >- (
    rw[el_check_def,FLOOKUP_DEF] >>
    rator_x_assum`syneq`mp_tac >>
    simp[Once syneq_cases] >> rw[] >>
    simp[Once Cv_bv_cases,el_check_def,FLOOKUP_DEF] >>
    rator_assum`syneq_defs`mp_tac >>
    simp_tac(srw_ss())[Once syneq_exp_cases,EVERY_MEM] >>
    simp[] >> strip_tac >>
    first_x_assum(qspecl_then[`n`,`d2`]mp_tac) >>
    simp[] >> strip_tac >>
    simp[] >>
    Cases_on`azb` >> rfs[] >> fs[syneq_cb_aux_def] >> rfs[EVERY_MEM] >>
    first_x_assum match_mp_tac >>
    HINT_EXISTS_TAC >>
    HINT_EXISTS_TAC >>
    qexists_tac`n` >>
    srw_tac[SATISFY_ss][]) >>
  rw[] >>
  simp[Once Cv_bv_cases] >>
  rator_assum`syneq_defs`mp_tac >>
  simp_tac(srw_ss())[Once syneq_exp_cases,EVERY_MEM] >>
  strip_tac >>
  first_x_assum(qspecl_then[`n1`,`n2`]mp_tac) >>
  simp[] >>
  qabbrev_tac`p = EL n1 defs1`>>PairCases_on`p` >>
  Cases_on`p0`>>fs[]>>PairCases_on`x` >>
  strip_tac >>
  ntac 2 (qpat_assum`X = Y`(mp_tac o SYM)) >>
  simp[syneq_cb_aux_def] >>
  strip_tac >> strip_tac >> fs[] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  `b` by (
    fs[syneq_cb_aux_def] >> rw[] >> rfs[] ) >>
  fs[] >>
  conj_tac >- (
    gen_tac >> strip_tac >>
    last_x_assum(qspec_then`i`mp_tac) >>
    simp[] >> strip_tac >>
    conj_asm1_tac >- (
      fs[syneq_cb_aux_def] >> rw[] >> rfs[] >>
      fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] ) >>
    qsuff_tac`syneq (CRecClos env1 defs1 (EL i recs)) (CRecClos env2 defs2 (EL i recs))`>-(
      metis_tac[syneq_trans] ) >>
    simp[Once syneq_cases] >>
    HINT_EXISTS_TAC >>
    qexists_tac`U` >>
    simp[] >> conj_tac >- metis_tac[] >>
    first_x_assum match_mp_tac >>
    simp[MEM_EL] >> metis_tac[] ) >>
  gen_tac >> strip_tac >>
  qpat_assum`∀i. i < LENGTH envs ⇒ P ∧ Q`(qspec_then`i`mp_tac) >>
  simp[] >> strip_tac >>
  conj_asm1_tac >- (
    fs[syneq_cb_aux_def,EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] ) >>
  first_x_assum match_mp_tac >>
  fsrw_tac[DNF_ss][] >>
  first_x_assum match_mp_tac >>
  first_x_assum match_mp_tac >>
  simp[MEM_EL] >> metis_tac[])

val Cv_bv_SUBMAP = store_thm("Cv_bv_SUBMAP",
  ``∀pp.
    (∀v bv. Cv_bv pp v bv ⇒
      ∀rd l2a pp' rd'.
        (pp = (rd,l2a)) ∧
        (pp' = (rd',l2a)) ∧
        (rd.sm ≼ rd'.sm) ∧ (rd.cls ⊑ rd'.cls) ∧
        (∀p. p ∈ FDOM rd.cls ∧ p ∉ set rd.sm ⇒ p ∉ set rd'.sm)
        ⇒
        Cv_bv pp' v bv) ∧
    (∀benv cd env defs. benv_bvs pp benv cd env defs ⇒
      ∀rd l2a pp' rd'.
        (pp = (rd,l2a)) ∧
        (pp' = (rd',l2a)) ∧
        (rd.sm ≼ rd'.sm) ∧ (rd.cls ⊑ rd'.cls) ∧
        (∀p. p ∈ FDOM rd.cls ∧ p ∉ set rd.sm ⇒ p ∉ set rd'.sm)
        ⇒
        benv_bvs pp' benv cd env defs)``,
  gen_tac >> ho_match_mp_tac Cv_bv_ind >>
  strip_tac >- rw[Once Cv_bv_cases,LENGTH_NIL] >>
  strip_tac >- rw[Once Cv_bv_cases,LENGTH_NIL] >>
  strip_tac >- rw[Once Cv_bv_cases,LENGTH_NIL] >>
  strip_tac >- rw[Once Cv_bv_cases,LENGTH_NIL] >>
  strip_tac >- rw[Once Cv_bv_cases,LENGTH_NIL] >>
  strip_tac >- (
    rw[Once Cv_bv_cases,LENGTH_NIL] >>
    fs[el_check_def,IS_PREFIX_THM,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,LENGTH_NIL] >>
    PROVE_TAC[LESS_LESS_EQ_TRANS]) >>
  strip_tac >- (
    rw[] >> rw[Once Cv_bv_cases,LENGTH_NIL] >>
    fs[FLOOKUP_DEF,IS_PREFIX_THM,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,LENGTH_NIL] ) >>
  strip_tac >- (
    rw[] >> rw[Once Cv_bv_cases,LENGTH_NIL] >>
    fs[FLOOKUP_DEF,IS_PREFIX_THM,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,LENGTH_NIL] ) >>
  strip_tac >- ( rw[] >> simp[Once Cv_bv_cases] >> metis_tac[] ) >>
  rpt gen_tac >> strip_tac >> fs[] >>
  rpt gen_tac >> strip_tac >>
  simp[Once Cv_bv_cases] >>
  simp[GSYM FORALL_AND_THM] >> gen_tac >>
  rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
  metis_tac[FLOOKUP_SUBMAP,ADD_SYM])

(* TODO: Cv_bv is no longer injective because of representation of words. How much of a problem is this?
val no_closures_Cv_bv_equal = store_thm("no_closures_Cv_bv_equal",
  ``∀pp cv bv. Cv_bv pp cv bv ⇒
      ∀cv' bv'. Cv_bv pp cv' bv' ∧
        no_closures cv ∧
        no_closures cv' ∧
        ALL_DISTINCT (FST pp).sm
        ⇒ ((cv = cv') = (bv = bv'))``,
  gen_tac >> ho_match_mp_tac Cv_bv_only_ind >> rw[]
  >- (
    rw[EQ_IMP_THM] >> rw[] >>
    fs[Once Cv_bv_cases] )
  >- (
    rw[EQ_IMP_THM] >> rw[] >>
    fs[Once Cv_bv_cases] >>
    rw[] >> (TRY(Cases_on`b`)) >> fsrw_tac[ARITH_ss][] >>
    fs[LIST_EQ_REWRITE] >> rfs[EL_MAP] >>
    metis_tac[stringTheory.ORD_11])
  >- (
    rw[EQ_IMP_THM] >> rw[] >>
    Cases_on `b` >>
    fsrw_tac[ARITH_ss][Once Cv_bv_cases] >>
    Cases_on `b` >> fs[])
  >- (
    rw[EQ_IMP_THM] >>
    fs[Once Cv_bv_cases] >>
    fsrw_tac[ARITH_ss][] >>
    Cases_on`b` >> fsrw_tac[ARITH_ss][] )
  >- (
    rw[EQ_IMP_THM] >>
    fs[Once Cv_bv_cases,el_check_def] >> rw[] >>
    fs[EL_ALL_DISTINCT_EL_EQ] >>
    metis_tac[]) >>
  rw[EQ_IMP_THM] >- (
    fs[Once (Q.SPEC`CConv cn vs`(CONJUNCT1 (SPEC_ALL Cv_bv_cases)))] >>
    rw[LIST_EQ_REWRITE] >>
    fs[EVERY2_EVERY] >>
    qpat_assum`LENGTH X = LENGTH bvs` assume_tac >>
    fsrw_tac[DNF_ss][EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
    qpat_assum`LENGTH vs = X` assume_tac >>
    fsrw_tac[DNF_ss][MEM_EL] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    metis_tac[EL_ZIP] ) >>
  qpat_assum`Cv_bv X Y Z` mp_tac >>
  rw[Once Cv_bv_cases] >>
  fsrw_tac[ARITH_ss][] >>
  TRY (Cases_on `b` >> fsrw_tac[ARITH_ss][]) >>
  fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  rpt (qpat_assum `LENGTH X = Y` mp_tac) >> rpt strip_tac >>
  fsrw_tac[DNF_ss][MEM_ZIP] >>
  rw[LIST_EQ_REWRITE] >> fsrw_tac[DNF_ss][MEM_EL] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
  metis_tac[])
*)

val Cv_bv_l2a_mono = store_thm("Cv_bv_l2a_mono",
  ``∀pp.
    (∀Cv bv. Cv_bv pp Cv bv ⇒ ∀pp' l2a.
     (∀x y. ((SND pp) x = SOME y) ⇒ (l2a x = SOME y))
     ∧ (pp' = (FST pp, l2a))
     ⇒ Cv_bv pp' Cv bv) ∧
    (∀benv fs env defs.
     benv_bvs pp benv fs env defs ⇒ ∀pp' l2a.
     (∀x y. ((SND pp) x = SOME y) ⇒ (l2a x = SOME y))
     ∧ (pp' = (FST pp, l2a))
     ⇒ benv_bvs pp' benv fs env defs)``,
  gen_tac >>
  PairCases_on `pp` >> simp[] >>
  ho_match_mp_tac Cv_bv_ind >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- (
    rw[] >>
    rw[Once Cv_bv_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once Cv_bv_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] ) >>
  strip_tac >- (
    simp[] >> rpt gen_tac >> strip_tac >> strip_tac >>
    simp[Once Cv_bv_cases] >>
    strip_tac >>
    map_every qexists_tac[`fs`,`l`] >> simp[] >>
    fs[el_check_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  rw[Once Cv_bv_cases] >>
  fs[])

val Cv_bv_l2a_mono_mp = save_thm("Cv_bv_l2a_mono_mp",MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_l2a_mono))))

val Cv_bv_not_env = store_thm("Cv_bv_not_env",
  ``∀pp Cv bv. Cv_bv pp Cv bv ⇒ ∀vs. (bv = Block 0 vs) ⇒ (vs = [])``,
  gen_tac >> ho_match_mp_tac Cv_bv_only_ind >> simp[])

val Cv_bv_cases_lit =
  Cv_bv_cases |> SPEC_ALL |> CONJUNCT1
  |> Q.SPEC`CLitv X` |> SIMP_RULE (srw_ss())[]

val Cv_bv_cases_conv =
  Cv_bv_cases |> SPEC_ALL |> CONJUNCT1
  |> Q.SPEC`CConv X Y` |> SIMP_RULE (srw_ss())[]

val Cv_bv_cases_vectorv =
  Cv_bv_cases |> SPEC_ALL |> CONJUNCT1
  |> Q.SPEC`CVectorv Y` |> SIMP_RULE (srw_ss())[]

val no_closures_Cv_bv = store_thm("no_closures_Cv_bv",
  ``∀Cv. no_closures Cv ⇒ ∀bv pp pp'. (FST pp').sm = (FST pp).sm ∧ Cv_bv pp Cv bv ⇒ Cv_bv pp' Cv bv``,
  ho_match_mp_tac compilerTerminationTheory.no_closures_ind >>
  simp[] >> rw[] >>
  TRY (
    simp[Once Cv_bv_cases] >>
    fs[Once Cv_bv_cases] >>
    NO_TAC) >>
  fs[Cv_bv_cases_conv,Cv_bv_cases_vectorv] >>
  fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >>
  rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >> rw[] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  metis_tac[MEM_EL])

(* s_refs relation *)

val _ = Parse.overload_on("mk_pp", ``λrd bs.
  (rd
  ,combin$C (bc_find_loc_aux bs.code bs.inst_length) 0
  )``)

val sv_refv_rel_def = Define`
  sv_refv_rel R (Refv v) (ValueArray [bv]) = R v bv ∧
  sv_refv_rel R (W8array ws) (ByteArray bvs) = (bvs = ws) ∧
  sv_refv_rel R _ _ = F`
val _ = export_rewrites["sv_refv_rel_def"]

val sv_refv_rel_cases = store_thm("sv_refv_rel_cases",
  ``sv_refv_rel R x y ⇔
    (∃v bv. x = Refv v ∧ y = ValueArray [bv] ∧ R v bv) ∨
    (∃ws. x = W8array ws ∧ y = ByteArray ws)``,
  Cases_on`x`>>Cases_on`y`>>rw[]>>
  Cases_on`l`>>rw[]>>Cases_on`t`>>rw[])

val sv_refv_rel_mono = store_thm("sv_refv_rel_mono",
  ``(∀x y. P x y ⇒ Q x y) ⇒ sv_refv_rel P x y ⇒ sv_refv_rel Q x y``,
  Cases_on`x`>>Cases_on`y`>>rw[]>>fs[sv_refv_rel_cases])

val good_rd_def = Define`
  good_rd rd bs =
    FEVERY (λ(p,(env,defs,j)).
      p ∉ set rd.sm ∧
      ∃v. FLOOKUP bs.refs p = SOME (ValueArray [v]) ∧
      Cv_bv (mk_pp rd bs) (CRecClos env defs j) v)
    rd.cls`

val s_refs_def = Define`
  s_refs rd s bs ⇔
  (∀n. bs.clock = SOME n ⇒ FST (FST s) = n) ∧
  good_rd rd bs ∧
  (LENGTH rd.sm = LENGTH (SND (FST s))) ∧
  EVERY (λp. p ∈ FDOM bs.refs) rd.sm ∧
  ALL_DISTINCT rd.sm ∧
  EVERY2 (sv_refv_rel (Cv_bv (mk_pp rd bs))) (SND (FST s)) (MAP (FAPPLY bs.refs) rd.sm) ∧
  EVERY2 (OPTREL (Cv_bv (mk_pp rd bs))) (SND s) bs.globals`

val s_refs_with_pc = store_thm("s_refs_with_pc",
  ``s_refs rd s (bs with pc := p) = s_refs rd s bs``,
  rw[s_refs_def,good_rd_def])

val s_refs_with_stack = store_thm("s_refs_with_stack",
  ``s_refs rd s (bs with stack := p) = s_refs rd s bs``,
  rw[s_refs_def,good_rd_def])

val s_refs_with_irr = store_thm("s_refs_with_irr",
  ``∀rd s bs bs'.
    s_refs rd s bs ∧ (bs'.refs = bs.refs) ∧ (bs'.inst_length = bs.inst_length) ∧
    (bs'.code = bs.code) ∧ (bs'.clock = bs.clock) ∧ (bs'.globals = bs.globals)
    ⇒
    s_refs rd s bs'``,
  rw[s_refs_def,good_rd_def])

val s_refs_append_code = store_thm("s_refs_append_code",
  ``∀rd s bs bs' ls.
     s_refs rd s bs ∧ (bs' = (bs with code := bs.code ++ ls))
    ⇒ s_refs rd s bs'``,
  rw[s_refs_def,fmap_rel_def,good_rd_def,FEVERY_DEF,UNCURRY] >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >> rpt strip_tac >>
  res_tac >>
  TRY (first_assum(match_exists_tac o concl) >> rw[]) >>
  TRY (match_mp_tac (GEN_ALL (MP_CANON optionTheory.OPTREL_MONO)) >> HINT_EXISTS_TAC >> rw[]) >>
  TRY (match_mp_tac (GEN_ALL (MP_CANON sv_refv_rel_mono)) >> HINT_EXISTS_TAC >> rw[]) >>
  match_mp_tac Cv_bv_l2a_mono_mp >>
  qexists_tac `mk_pp rd bs` >>
  rw[] >> metis_tac[bc_find_loc_aux_append_code])

(* compiler-environment variable lookup *)

val lookup_cc_def = Define`
  lookup_cc sz st rs (CCArg n) = el_check (sz + n) st ∧
  lookup_cc sz st rs (CCEnv n) =
    OPTION_BIND (el_check sz st)
    (λv. case v of Block 0 vs => el_check n vs | _ => NONE) ∧
  lookup_cc sz st rs (CCRef n) =
    OPTION_BIND (el_check sz st)
    (λv. case v of Block 0 vs =>
       OPTION_BIND (el_check n vs)
       (λv. case v of RefPtr p =>
              (case FLOOKUP rs p of
               | SOME (ValueArray [bv]) => SOME bv
               | _ => NONE)
            | _ => NONE)
     | _ => NONE)`

val lookup_ct_def = Define`
  (lookup_ct sz st rs gv (CTLet n) = if sz < n then NONE else el_check (sz - n) st) ∧
  lookup_ct sz st rs gv (CTDec n) = OPTION_JOIN (el_check n gv) ∧
  lookup_ct sz st rs gv (CTEnv cc) = lookup_cc sz st rs cc`
val _ = export_rewrites["lookup_cc_def","lookup_ct_def"]

val lookup_ct_imp_incsz = store_thm("lookup_ct_imp_incsz",
  ``(lookup_ct sz st refs gv b = SOME v) ⇒
    (lookup_ct (sz+1) (x::st) refs gv b = SOME v)``,
  fs[GSYM ADD1] >>
  Cases_on `b` >> rw[el_check_def] >>
  fsrw_tac[ARITH_ss][EL_CONS,PRE_SUB1,ADD1,EL_APPEND1] >>
  Cases_on`c`>>rw[el_check_def] >>
  fsrw_tac[ARITH_ss][EL_CONS,PRE_SUB1,ADD1,el_check_def])

val lookup_ct_imp_incsz_many = store_thm("lookup_ct_imp_incsz_many",
  ``∀sz st refs gv b v st' sz' ls.
    (lookup_ct sz st refs gv b = SOME v) ∧
     sz ≤ sz' ∧ (st' = ls ++ st) ∧ (LENGTH ls = sz' - sz)
   ⇒ (lookup_ct sz' st' refs gv b = SOME v)``,
  Induct_on`sz' - sz` >- (
    rw[] >> `sz = sz'` by srw_tac[ARITH_ss][] >> fs[LENGTH_NIL] ) >>
  rw[] >> Cases_on`ls`>>fs[] >- fsrw_tac[ARITH_ss][] >>
  Cases_on`sz'`>>fs[ADD1] >>
  match_mp_tac lookup_ct_imp_incsz >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  qexists_tac`sz` >>
  fsrw_tac[ARITH_ss][])

val lookup_ct_change_refs = store_thm("lookup_ct_change_refs",
  ``∀sz st rf rf' gv gv' ct.
    (∀n vs p. (ct = CTEnv (CCRef n)) ∧ sz < LENGTH st ∧ (EL sz st = Block 0 vs) ∧ n < LENGTH vs ∧ (EL n vs = RefPtr p) ⇒
       (FLOOKUP rf' p = FLOOKUP rf p)) ∧
    (*
    LENGTH gv ≤ LENGTH gv' ∧
    (∀n. LENGTH gv ≤ n ∧ n < LENGTH gv' ⇒ EL n gv' = NONE) ∧
    *)
    (∀n. (ct = CTDec n) ⇒ n < LENGTH gv ∧ n < LENGTH gv' ∧ EL n gv' = EL n gv)
    ⇒ (lookup_ct sz st rf' gv' ct = lookup_ct sz st rf gv ct)``,
  rw[LET_THM] >>
  Cases_on`ct`>>fs[] >> rw[el_check_def] >> fs[] >>
  fsrw_tac[ARITH_ss][] >>
  Cases_on`c`>>fs[el_check_def]>>
  Cases_on`EL sz st`>>fs[] >> rw[]>>fs[]>>
  rpt(BasicProvers.CASE_TAC>>fs[]))

val lookup_ct_incsz = store_thm("lookup_ct_incsz",
  ``(lookup_ct (sz+1) (x::st) refs gv b =
     if (b = CTLet (sz+1)) then SOME x else
     lookup_ct sz st refs gv b)``,
  fs[GSYM ADD1] >>
  Cases_on `b` >> rw[] >>
  fsrw_tac[ARITH_ss][el_check_def] >>
  rw[SUB,GSYM ADD_SUC] >>
  fsrw_tac[ARITH_ss][EL_APPEND1,EL_APPEND2] >>
  Cases_on`c`>>rw[el_check_def]>>
  fsrw_tac[ARITH_ss][EL_CONS,PRE_SUB1,ADD1])

(* Cenv_bs relation *)

val env_renv_def = Define`
  env_renv rd sz bs Cenv renv ⇔
    (EVERY2
       (λCv b. case lookup_ct sz bs.stack (DRESTRICT bs.refs (FDOM rd.cls)) bs.globals b of NONE => F
             | SOME bv => Cv_bv (mk_pp rd bs) Cv bv)
     Cenv renv)`

val Cenv_bs_def = Define`
  Cenv_bs rd s Cenv (renv:ctenv) sz bs ⇔
    env_renv rd sz bs Cenv renv ∧ s_refs rd s bs`

val env_renv_with_irr = store_thm("env_renv_with_irr",
  ``∀rd rsz bs x y bs'. env_renv rd rsz bs x y
    ∧ bs'.stack = bs.stack
    ∧ bs'.refs = bs.refs
    ∧ bs'.code = bs.code
    ∧ bs'.globals = bs.globals
    ∧ bs'.inst_length = bs.inst_length
    ⇒ env_renv rd rsz bs' x y``,
  rw[env_renv_def])

val fmap_rel_env_renv_with_irr = store_thm("fmap_rel_env_renv_with_irr",
  ``∀rd rsz bs x y bs'. fmap_rel (env_renv rd rsz bs) x y
    ∧ bs'.stack = bs.stack
    ∧ bs'.refs = bs.refs
    ∧ bs'.code = bs.code
    ∧ bs'.globals = bs.globals
    ∧ bs'.inst_length = bs.inst_length
    ⇒ fmap_rel (env_renv rd rsz bs') x y``,
  rw[fmap_rel_def,env_renv_def])

val Cenv_bs_with_irr = store_thm("Cenv_bs_with_irr",
  ``∀rd s env cenv sz bs bs'.
    Cenv_bs rd s env cenv sz bs ∧
    (bs'.stack = bs.stack) ∧ (bs'.refs = bs.refs) ∧
    (bs'.code = bs.code) ∧ (bs'.inst_length = bs.inst_length) ∧
    (bs'.globals = bs.globals) ∧
    (bs'.clock = bs.clock)
    ⇒
    Cenv_bs rd s env cenv sz bs'``,
  rw[Cenv_bs_def,s_refs_def,good_rd_def,env_renv_def,fmap_rel_def] >>
  rfs[o_f_FAPPLY])

val Cenv_bs_syneq_store = store_thm("Cenv_bs_syneq_store",
  ``∀rd s Cenv renv sz bs s'. csg_rel syneq s s' ∧ Cenv_bs rd s Cenv renv sz bs ⇒
           Cenv_bs rd s' Cenv renv sz bs``,
  rw[Cenv_bs_def] >>
  full_simp_tac pure_ss [s_refs_def] >>
  PairCases_on`s`>>PairCases_on`s'`>>fs[csg_rel_def] >>
  simp_tac std_ss [] >>
  conj_tac >- metis_tac[] >>
  conj_asm1_tac >- metis_tac[EVERY2_EVERY] >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  rfs[MEM_ZIP] >> fs[MEM_ZIP] >>
  fs[GSYM LEFT_FORALL_IMP_THM] >>
  conj_tac >- (
    rw[] >>
    rpt (first_x_assum(qspec_then`n`mp_tac)) >>
    simp[sv_rel_cases] >> strip_tac >> simp[sv_refv_rel_cases] >>
    metis_tac[Cv_bv_syneq,FST,SND] ) >>
  rw[] >>
  qmatch_assum_rename_tac`LENGTH bs.globals = LENGTH z`[] >>
  rpt (first_x_assum(qspec_then`n`mp_tac)) >>
  Cases_on`EL n z`>>fs[optionTheory.OPTREL_def] >> rw[] >> fs[] >>
  metis_tac[Cv_bv_syneq,FST,SND])

val env_renv_APPEND_suff = store_thm("env_renv_APPEND_suff",
  ``∀rd sz bs l1 l2 l3 l4.
    env_renv rd sz bs l1 l3 ∧ env_renv rd sz bs l2 l4 ⇒ env_renv rd sz bs (l1 ++ l2) (l3 ++ l4)``,
  rw[env_renv_def] >>
  match_mp_tac EVERY2_APPEND_suff >>
  simp[])

val env_renv_imp_incsz = store_thm("env_renv_imp_incsz",
  ``∀rd sz bs menv env bs' v. env_renv rd sz bs menv env ∧
    (bs' = bs with stack := v::bs.stack)
    ⇒
    env_renv rd (sz+1) bs' menv env``,
  rw[env_renv_def] >> rw[] >> fs[] >>
  match_mp_tac(GEN_ALL(MP_CANON EVERY2_mono)) >>
  HINT_EXISTS_TAC >> simp[] >>
  rpt gen_tac >>
  BasicProvers.CASE_TAC >>
  imp_res_tac lookup_ct_imp_incsz >>
  simp[])

val env_renv_imp_incsz_many = store_thm("env_renv_imp_incsz_many",
  ``∀rd sz bs l1 l2 sz' bs' ls. env_renv rd sz bs l1 l2 ∧
    bs' = bs with stack := ls ++ bs.stack ∧
    sz' = sz + LENGTH ls ⇒
    env_renv rd sz' bs' l1 l2``,
  Induct_on`ls` >- simp[] >>
  simp[ADD1] >> rw[] >>
  REWRITE_TAC[ADD_ASSOC] >>
  match_mp_tac env_renv_imp_incsz >>
  qexists_tac`bs with stack := ls++bs.stack` >>
  simp[bc_state_component_equality] >>
  first_x_assum match_mp_tac >>
  qexists_tac`sz` >>
  qexists_tac`bs` >>
  simp[bc_state_component_equality])

val Cenv_bs_imp_incsz = store_thm("Cenv_bs_imp_incsz",
  ``∀rd s env renv rsz bs bs' v.
    Cenv_bs rd s env renv rsz bs ∧
    (bs' = bs with stack := v::bs.stack)
    ⇒
    Cenv_bs rd s env renv (rsz+1) bs'``,
  simp[Cenv_bs_def,s_refs_def,good_rd_def,ADD1] >> rw[] >>
  match_mp_tac env_renv_imp_incsz >>
  metis_tac[] )

val Cenv_bs_imp_incsz_irr = store_thm("Cenv_bs_imp_incsz_irr",
  ``∀rd s env renv rsz bs bs' v.
    Cenv_bs rd s env renv rsz bs ∧
    bs'.refs = bs.refs ∧ bs'.code = bs.code ∧ bs'.inst_length = bs.inst_length ∧ bs'.stack = v::bs.stack
    ∧ bs'.clock = bs.clock ∧ bs'.globals = bs.globals
    ⇒
    Cenv_bs rd s env renv (rsz+1) bs'``,
  rw[] >>
  match_mp_tac Cenv_bs_with_irr >>
  qexists_tac`bs with stack := v::bs.stack` >> simp[] >>
  match_mp_tac Cenv_bs_imp_incsz >>
  qexists_tac`bs` >> simp[bc_state_component_equality])

val env_renv_imp_decsz = store_thm("env_renv_imp_decsz",
  ``∀rd rsz bs env renv bs' v.
    env_renv rd (rsz+1) bs env renv ∧
    (bs = bs' with stack := v::bs'.stack) ∧
    (CTLet (rsz+1) ∉ set renv)
    ⇒
    env_renv rd rsz bs' env renv``,
  rw[env_renv_def] >> fs[] >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  rpt strip_tac >> res_tac >> pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  pop_assum mp_tac >>
  rw[lookup_ct_incsz] >>
  rfs[MEM_ZIP,MEM_EL] >>
  metis_tac[])

val Cenv_bs_imp_decsz = store_thm("Cenv_bs_imp_decsz",
  ``∀rd s env renv rsz bs bs' v.
    Cenv_bs rd s env renv (rsz+1) bs ∧
      (CTLet (rsz+1) ∉ set renv) ∧
      (bs = bs' with stack := v::bs'.stack) ⇒
    Cenv_bs rd s env renv rsz bs'``,
  rw[Cenv_bs_def,fmap_rel_def,s_refs_def,FDOM_DRESTRICT,good_rd_def,ADD1] >> fs[] >>
  TRY (
    match_mp_tac env_renv_imp_decsz >>
    res_tac >> HINT_EXISTS_TAC >>
    simp[bc_state_component_equality] >>
    fs[IN_FRANGE] >> metis_tac[]) >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[ADD1] >>
  fsrw_tac[ARITH_ss][])

val env_renv_CTLet_bound = store_thm("env_renv_CTLet_bound",
  ``env_renv rd rsz bs env renv ∧ CTLet n ∈ set renv ⇒ n ≤ rsz``,
  rw[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,env_renv_def] >>
  rfs[MEM_ZIP,MEM_EL] >> fsrw_tac[DNF_ss][] >>
  qmatch_assum_abbrev_tac `z < LENGTH E`>>
  first_x_assum (qspec_then `z` mp_tac) >>
  qpat_assum`CTLet n = X`(assume_tac o SYM) >>
  simp[el_check_def] >>
  srw_tac[ARITH_ss][])

val Cenv_bs_CTLet_bound = store_thm("Cenv_bs_CTLet_bound",
  ``Cenv_bs rd s env renv rsz bs ∧ (CTLet n) ∈ set renv ⇒ n ≤ rsz``,
  rw[Cenv_bs_def,fmap_rel_def,IN_FRANGE] >>
  match_mp_tac (GEN_ALL env_renv_CTLet_bound) >>
  metis_tac[])

val env_renv_CTDec_bound = store_thm("env_renv_CTDec_bound",
  ``env_renv rd rsz bs env renv ∧ CTDec n ∈ set renv ⇒ n < LENGTH bs.globals``,
  rw[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,env_renv_def] >>
  rfs[MEM_ZIP,MEM_EL] >> fsrw_tac[DNF_ss][] >>
  qmatch_assum_abbrev_tac `z < LENGTH E`>>
  first_x_assum (qspec_then `z` mp_tac) >>
  qpat_assum`CTDec n = X`(assume_tac o SYM) >>
  simp[el_check_def] >>
  srw_tac[ARITH_ss][])

val Cenv_bs_CTDec_bound = store_thm("Cenv_bs_CTDec_bound",
  ``Cenv_bs rd s env renv rsz bs ∧ (CTDec n) ∈ set renv ⇒ n < LENGTH bs.globals``,
  rw[Cenv_bs_def] >>
  match_mp_tac (GEN_ALL env_renv_CTDec_bound) >>
  metis_tac[])

val CTDec_bound_lemma =
  CONJ (prove(``∀x y. (x with code := y).stack = x.stack``,simp[]))
       (SIMP_RULE(srw_ss())[]Cenv_bs_CTDec_bound)

(*
val env_renv_imp_incsz_CTDec = store_thm("env_renv_imp_incsz_CTDec",
  ``∀rd sz bs menv cmnv bs' vs.
    env_renv rd sz bs menv (MAP CTDec cmnv) ∧ (bs' = bs with stack := vs ++ bs.stack) ⇒
    env_renv rd sz bs' menv (MAP CTDec cmnv)``,
  rw[env_renv_def] >>
  match_mp_tac(GEN_ALL(MP_CANON EVERY2_MEM_MONO)) >>
  HINT_EXISTS_TAC >> simp[] >>
  fs[EVERY2_EVERY] >> simp[MEM_ZIP] >>
  simp_tac(srw_ss()++DNF_ss)[FORALL_PROD] >>
  simp[option_case_NONE_F,GSYM AND_IMP_INTRO,GSYM LEFT_FORALL_IMP_THM,EL_MAP,el_check_def,EL_REVERSE,PRE_SUB1,EL_APPEND2])

val fmap_rel_env_renv_CTDec = store_thm("fmap_rel_env_renv_CTDec",
  ``∀rd sz bs menv cmnv bs' vs.
      fmap_rel (env_renv rd sz bs) menv (MAP CTDec o_f cmnv) ∧
      (bs' = bs with stack := vs ++ bs.stack)
      ⇒
      fmap_rel (env_renv rd sz bs') menv (MAP CTDec o_f cmnv)``,
   rw[fmap_rel_def] >>
   match_mp_tac env_renv_imp_incsz_CTDec >>
   qexists_tac`bs` >>
   simp[bc_state_component_equality] >>
   metis_tac[o_f_FAPPLY])
*)

val Cenv_bs_pops = store_thm("Cenv_bs_pops",
  ``∀vs rd s env renv rsz bs bs'.
    Cenv_bs rd s env renv (rsz + LENGTH vs) bs ∧
    (∀n. (CTLet n) ∈ set renv ⇒ n ≤ rsz) ∧
    (bs = bs' with stack := vs ++ bs'.stack)
    ⇒ Cenv_bs rd s env renv rsz bs'``,
  Induct >> rw[] >- fs[] >>
  first_x_assum match_mp_tac >>
  simp[bc_state_component_equality] >>
  match_mp_tac Cenv_bs_imp_decsz >>
  fsrw_tac[ARITH_ss][ADD1,bc_state_component_equality] >>
  HINT_EXISTS_TAC >> simp[] >>
  spose_not_then strip_assume_tac >>
  res_tac >> fsrw_tac[ARITH_ss][] )

val env_renv_append_code = store_thm("env_renv_append_code",
  ``∀rd sz bs l1 l2 bs' ls. env_renv rd sz bs l1 l2  ∧ bs' = bs with code := bs.code ++ ls ⇒
     env_renv rd sz bs' l1 l2``,
  rw[env_renv_def] >>
  match_mp_tac (GEN_ALL (MP_CANON EVERY2_mono)) >>
  HINT_EXISTS_TAC >>
  simp[] >> rpt gen_tac >> BasicProvers.CASE_TAC >>
  strip_tac >>
  match_mp_tac Cv_bv_l2a_mono_mp >>
  qexists_tac `mk_pp rd bs` >>
  rw[] >> metis_tac[bc_find_loc_aux_append_code])

val Cenv_bs_append_code = store_thm("Cenv_bs_append_code",
  ``∀rd s env env0 sz0 bs bs' ls.
    Cenv_bs rd s env env0 sz0 bs ∧ (bs' = (bs with code := bs.code ++ ls)) ⇒
    Cenv_bs rd s env env0 sz0 bs'``,
  reverse(rw[Cenv_bs_def]) >- PROVE_TAC[s_refs_append_code] >>
  fs[Cenv_bs_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,s_refs_def,env_renv_def,fmap_rel_def] >> rw[] >>
  res_tac >>
  BasicProvers.CASE_TAC >> fs[] >>
  TRY (
    qmatch_assum_rename_tac`MEM (a,b) X`["X"]>>
    first_x_assum(qspecl_then[`b`,`a`]mp_tac) >>
    simp[] >> strip_tac) >>
  match_mp_tac Cv_bv_l2a_mono_mp >>
  qexists_tac `mk_pp rd bs` >>
  rw[] >> metis_tac[bc_find_loc_aux_append_code])

val Cenv_bs_FUPDATE = store_thm("Cenv_bs_FUPDATE",
  ``∀rd s env env0 sz0 bs v bv bs'.
    Cenv_bs rd s env env0 sz0 bs ∧
    Cv_bv (mk_pp rd bs') v bv ∧
    (bs' = bs with stack := bv::bs.stack)
    ⇒
    Cenv_bs rd s (v::env) ((CTLet (sz0 + 1))::env0) (sz0 + 1) bs'``,
  rpt gen_tac >>
  simp[Cenv_bs_def,ADD1] >>
  reverse(reverse(rw[Cenv_bs_def,s_refs_def]) >> fs[el_check_def] >- fs[good_rd_def]) >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,env_renv_def,fmap_rel_def,el_check_def] >>
  rpt strip_tac >> res_tac >>
  pop_assum mp_tac >> BasicProvers.CASE_TAC >>
  imp_res_tac lookup_ct_imp_incsz >>
  simp[] )

val Cenv_bs_FUPDATE_LIST = store_thm("Cenv_bs_FUPDATE_LIST",
  ``∀vs rd s env cenv sz bs bs bvs bs' env' cenv' sz'.
  Cenv_bs rd s env cenv sz bs ∧
  (bs' = bs with stack := bvs ++ bs.stack) ∧
  EVERY2 (Cv_bv (mk_pp rd bs')) vs bvs ∧
  (env' = vs++env) ∧
  (cenv' = (REVERSE(GENLIST(λm. CTLet(sz+m+1))(LENGTH vs)))++cenv) ∧
  (sz' = sz + LENGTH vs)
  ⇒
  Cenv_bs rd s env' cenv' sz' bs'``,
  Induct >- (
    simp[LENGTH_NIL,FUPDATE_LIST_THM] ) >>
  rw[] >>
  rw[GENLIST,REVERSE_SNOC] >> simp[ADD1] >>
  REWRITE_TAC[ADD_ASSOC] >>
  match_mp_tac Cenv_bs_FUPDATE >>
  qexists_tac`bs with stack := ys ++ bs.stack` >>
  simp[bc_state_component_equality] >>
  conj_tac >- (
    first_x_assum match_mp_tac >>
    simp[] >>
    qexists_tac`bs` >> simp[] >>
    qexists_tac`ys` >> simp[] >>
    match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
    HINT_EXISTS_TAC >>
    simp[] ) >>
  match_mp_tac Cv_bv_l2a_mono_mp >>
  HINT_EXISTS_TAC >>
  simp[])

(*
val Cenv_bs_FUPDATE_CTDec = store_thm("Cenv_bs_FUPDATE_CTDec",
  ``∀rd menv s env rmenv renv rsz csz bs v bv bs' n.
    Cenv_bs rd menv s env rmenv renv rsz csz bs ∧
    Cv_bv (mk_pp rd bs') v bv ∧
    bs' = bs with stack := bv::bs.stack ∧
    n = LENGTH bs.stack
    ⇒
    Cenv_bs rd menv s (v::env) rmenv ((CTDec n)::renv) (rsz+1) csz bs'``,
  rpt gen_tac >>
  simp[Cenv_bs_def] >>
  reverse(reverse(rw[Cenv_bs_def,s_refs_def]) >> fs[compilerLibTheory.el_check_def] >- fs[good_rd_def]) >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,env_renv_def,fmap_rel_def,compilerLibTheory.el_check_def] >>
  simp[EL_LENGTH_APPEND_rwt,ADD1] >>
  rpt strip_tac >> res_tac >>
  pop_assum mp_tac >> BasicProvers.CASE_TAC >>
  imp_res_tac lookup_ct_imp_incsz >>
  simp[] >>
  qmatch_assum_rename_tac`MEM (a,b) X`["X"] >>
  TRY(
    map_every qexists_tac[`b`,`a`] >>
    simp[]) >>
  strip_tac >>
  fs[option_case_NONE_F] >>
  metis_tac[optionTheory.SOME_11])

val Cenv_bs_FUPDATE_LIST_CTDec = store_thm("Cenv_bs_FUPDATE_LIST_CTDec",
  ``∀vs rd menv s env rmenv cenv sz csz bs bvs bs' env' cenv' sz'.
  Cenv_bs rd menv s env rmenv cenv sz csz bs ∧
  (bs' = bs with stack := bvs ++ bs.stack) ∧
  EVERY2 (Cv_bv (mk_pp rd bs')) vs bvs ∧
  (env' = vs++env) ∧
  (cenv' = (REVERSE(GENLIST(λm. CTDec(LENGTH bs.stack+m))(LENGTH vs)))++cenv) ∧
  (sz' = sz + LENGTH vs)
  ⇒
  Cenv_bs rd menv s env' rmenv cenv' sz' csz bs'``,
  Induct >- ( simp[LENGTH_NIL] ) >>
  rw[] >>
  rw[GENLIST,REVERSE_SNOC] >> simp[ADD1] >>
  REWRITE_TAC[ADD_ASSOC] >>
  match_mp_tac Cenv_bs_FUPDATE_CTDec >>
  qexists_tac`bs with stack := ys ++ bs.stack` >>
  simp[bc_state_component_equality] >>
  conj_tac >- (
    first_x_assum match_mp_tac >>
    simp[] >>
    qexists_tac`cenv`>>
    qexists_tac`bs` >> simp[] >>
    qexists_tac`ys` >> simp[] >>
    match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
    HINT_EXISTS_TAC >>
    simp[] ) >>
  reverse conj_tac >- fs[EVERY2_EVERY] >>
  match_mp_tac Cv_bv_l2a_mono_mp >>
  HINT_EXISTS_TAC >>
  simp[])
*)

val Cenv_bs_DOMSUB = store_thm("Cenv_bs_DOMSUB",
  ``∀rd s env renv rsz bs.
    Cenv_bs rd s env renv rsz bs ∧ (env ≠ []) ∧ (renv ≠ []) ⇒
    Cenv_bs rd s (TL env) (TL renv) rsz bs``,
  ntac 2 gen_tac >> Cases >> simp[] >> Cases >> simp[] >>
  rw[Cenv_bs_def,EVERY2_EVERY,env_renv_def,fmap_rel_def] >>
  metis_tac[o_f_FAPPLY])

val gvrel_def = Define`
  gvrel gv1 gv2 ⇔ LENGTH gv1 ≤ LENGTH gv2 ∧
    (∀n x. n < LENGTH gv1 ∧ (EL n gv1 = SOME x) ⇒ (EL n gv2 = SOME x))`

val gvrel_refl = store_thm("gvrel_refl",
  ``gvrel g g``, rw[gvrel_def])
val _ = export_rewrites["gvrel_refl"]

val gvrel_trans = store_thm("gvrel_trans",
  ``gvrel gv1 gv2 ∧ gvrel gv2 gv3 ⇒ gvrel gv1 gv3``,
  rw[gvrel_def] >> fsrw_tac[ARITH_ss][])

val env_renv_change_store = store_thm("env_renv_change_store",
  ``env_renv rd rsz bs env renv ∧
    (bs' = bs with <| refs := rfs'; clock := ck'; globals := gv'|>) ∧
    s_refs rd s bs ∧
    s_refs rd' s' bs' ∧
    rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls ∧ gvrel bs.globals gv' ∧
    DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rfs' (COMPL (set rd'.sm))
    ⇒
    env_renv rd' rsz bs' env renv``,
  rw[env_renv_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  res_tac >> pop_assum mp_tac >> BasicProvers.CASE_TAC >> strip_tac >>
  qho_match_abbrev_tac`case X of NONE => F | SOME Y => Z Y` >>
  qmatch_assum_abbrev_tac`X' = SOME x` >>
  `X = X'` by (
    unabbrev_all_tac >>
    match_mp_tac lookup_ct_change_refs >>
    conj_tac >- (
      rpt gen_tac >> strip_tac >>
      fs[s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY,el_check_def] >>
      fs[SUBMAP_DEF,FDOM_DRESTRICT,FLOOKUP_DEF,DRESTRICT_DEF] >>
      rw[] >> fs[] >> fs[] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      metis_tac[] ) >>
    rpt gen_tac >> strip_tac >>
    rfs[s_refs_def,EVERY2_EVERY,gvrel_def] >>
    fs[option_case_NONE_F] >> res_tac >>
    fs[el_check_def] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    fsrw_tac[ARITH_ss][] ) >>
  simp[Abbr`Z`] >>
  match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
  HINT_EXISTS_TAC >>
  simp[] >>
  fs[s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY] >>
  fs[SUBMAP_DEF,SUBSET_DEF,DRESTRICT_DEF,IN_FRANGE] )

val Cenv_bs_change_store = store_thm("Cenv_bs_change_store",
  ``∀rd s env renv rsz bs rd' s' bs' rfs' ck' gv'.
    Cenv_bs rd s env renv rsz bs ∧
    s_refs rd' s' bs' ∧
    (bs' = bs with <| refs := rfs'; clock := ck'; globals := gv' |>) ∧
    DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rfs' (COMPL (set rd'.sm)) ∧
    rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls ∧ gvrel bs.globals gv'
    ⇒
    Cenv_bs rd' s' env renv rsz bs'``,
  rw[Cenv_bs_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,fmap_rel_def] >>
  match_mp_tac (GEN_ALL env_renv_change_store) >>
  first_assum (match_exists_tac o concl) >> simp[] >>
  metis_tac[])

val Cenv_bs_perm = store_thm("Cenv_bs_perm",
  ``∀rd s env cenv sz bs cenv' env'.
  Cenv_bs rd s env cenv sz bs ∧
  LENGTH env' = LENGTH env ∧
  LENGTH cenv' = LENGTH cenv ∧
  PERM (ZIP(env,cenv)) (ZIP(env',cenv'))
  ⇒
  Cenv_bs rd s env' cenv' sz bs``,
  simp[Cenv_bs_def,env_renv_def,EVERY2_EVERY] >>
  rw[] >>
  fs[EVERY_MEM] >>
  metis_tac[PERM_MEM_EQ])

(*
val env_renv_shift = store_thm("env_renv_shift",
  ``∀rd sz bs env renv sz' bs' renv' st' ls ls'.
      env_renv rd sz bs env renv
      ∧ bs' = bs with stack := st'
      ∧ renv = MAP CTDec ls
      ∧ renv' = MAP CTDec ls'
      ∧ EVERY2 (λi i'. i < LENGTH bs.stack ⇒ i' < LENGTH st' ∧ EL i' (REVERSE st') = EL i (REVERSE bs.stack)) ls ls'
      ⇒
      env_renv rd sz' bs' env renv'``,
  rw[env_renv_def] >>
  fs[EVERY2_EVERY,EVERY_MEM] >>
  rpt(qpat_assum`X = Y`mp_tac) >> ntac 2 strip_tac >>
  fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
  fs[compilerLibTheory.el_check_def,option_case_NONE_F])
*)

val env_renv_append_imp = store_thm("env_renv_append_imp",
  ``∀rd sz bs l1 l2 l3 l4. env_renv rd sz bs (l1 ++ l2) (l3 ++ l4) ∧ LENGTH l1 = LENGTH l3 ∧ LENGTH l2 = LENGTH l4 ⇒
    env_renv rd sz bs l1 l3 ∧ env_renv rd sz bs l2 l4``,
  rw[] >>
  fs[env_renv_def] >>
  metis_tac[EVERY2_APPEND])

val env_renv_syneq = store_thm("env_renv_syneq",
  ``∀rd sz bs l1 l2 l3.
    env_renv rd sz bs l2 l3 ∧ LIST_REL syneq l2 l1
    ⇒
    env_renv rd sz bs l1 l3``,
  rw[] >>
  fs[env_renv_def,option_case_NONE_F] >> rw[] >>
  fs[EVERY2_EVERY,EVERY_MEM] >> rfs[] >>
  `LENGTH l2 = LENGTH l1` by metis_tac[] >>
  fs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
  rw[] >>
  first_x_assum(qspec_then`n`mp_tac) >>
  first_x_assum(qspec_then`n`mp_tac) >>
  simp[] >> rw[] >> simp[] >>
  metis_tac[Cv_bv_syneq])

val Cenv_bs_bind_fv = store_thm("Cenv_bs_bind_fv",
  ``∀cenv ccenv benv bve ret bvs a st fenv defs ix recs envs env pp rd bs s vs az e l e'.
    (cenv = MAP CTEnv ccenv) ∧
    (benv = Block 0 bve) ∧
    (bs.stack = benv::CodePtr ret::(REVERSE bvs)++(Block closure_tag [CodePtr a;benv])::st) ∧
    (env = REVERSE vs ++ [CRecClos fenv defs ix] ++ MAP (CRecClos fenv defs) recs ++ MAP (λn. EL n fenv) envs) ∧
    (bind_fv (az,e) (LENGTH defs) ix = (ccenv,(recs,envs),e')) ∧
    (pp = mk_pp rd bs) ∧
    benv_bvs pp bve (recs,envs) fenv defs ∧
    s_refs rd s bs ∧
    ix < LENGTH defs ∧
    (FST(EL ix defs) = SOME (l,ccenv,recs,envs)) ∧
    (bc_find_loc_aux bs.code bs.inst_length l 0 = SOME a) ∧
    EVERY2 (Cv_bv pp) vs bvs ∧ (az = LENGTH vs)
    ⇒ Cenv_bs rd s env cenv 0 bs``,
  simp[Cenv_bs_def,ADD1] >>
  rw[] >>
  simp[env_renv_def,EVERY2_EVERY] >>
  conj_asm1_tac >- (
    fsrw_tac[ARITH_ss][bind_fv_def,LET_THM] >>
    srw_tac[ARITH_ss][]) >>
  simp[EVERY_MEM,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
  gen_tac >> strip_tac >>
  simp[EL_MAP] >>
  simp[option_case_NONE_F] >>
  Cases_on`n< LENGTH vs` >- (
    fs[bind_fv_def,LET_THM] >> rw[] >>
    simp[EL_APPEND1,EL_REVERSE,PRE_SUB1,el_check_def,ADD1] >>
    fsrw_tac[ARITH_ss][EVERY2_EVERY] >>
    simp[EL_CONS,PRE_SUB1,EL_APPEND1,EL_REVERSE] >>
    fs[EVERY_MEM] >> rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
    first_x_assum match_mp_tac >> simp[] ) >>
  Cases_on`n = LENGTH vs` >- (
    fs[bind_fv_def,LET_THM] >> rw[] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    simp[EL_APPEND2,EL_APPEND1,el_check_def,ADD1,EL_CONS,PRE_SUB1] >>
    fsrw_tac[ARITH_ss][EVERY2_EVERY] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    simp[EL_APPEND2] >>
    simp[Once Cv_bv_cases,el_check_def] >>
    qexists_tac`SND (EL ix defs)` >>
    Cases_on`EL ix defs`>>fs[] >>
    conj_tac >- simp[EVERY_FILTER,EVERY_GENLIST,EVERY_MAP] >>
    fs[Once Cv_bv_cases] >>
    simp[EVERY_MEM,MEM_EL] >>
    metis_tac[] ) >>
  fs[bind_fv_def,LET_THM] >> rw[] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  simp[EL_APPEND2] >>
  Q.PAT_ABBREV_TAC`lrecs = LENGTH (FILTER X Y)` >>
  Q.PAT_ABBREV_TAC`recs:Cv list = MAP X (FILTER Y( GENLIST A Z))` >>
  `lrecs = LENGTH recs` by ( unabbrev_all_tac >> rw[]) >>
  Cases_on`n < LENGTH vs + 1 + LENGTH recs` >- (
    simp[EL_APPEND1,EL_MAP,el_check_def] >>
    rator_x_assum`benv_bvs`mp_tac >>
    simp[Once Cv_bv_cases] >> strip_tac >>
    qpat_assum`∀i. i < LENGTH recs ⇒ X`(qspec_then`n - (LENGTH vs + 1)` mp_tac) >>
    simp[] >> strip_tac >> simp[] >>
    fs[FLOOKUP_DEF,DRESTRICT_DEF] >>
    fs[s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY] >>
    qpat_assum`∀x. x ∈ FDOM rd.cls ⇒ X`(qspec_then`p`mp_tac) >>
    simp[] >> strip_tac >>
    fs[FLOOKUP_DEF] >>
    match_mp_tac (MP_CANON (CONJUNCT1 Cv_bv_syneq)) >>
    HINT_EXISTS_TAC >>
    simp[] >>
    qmatch_assum_abbrev_tac`syneq X Y` >>
    qmatch_abbrev_tac`syneq X Z` >>
    qsuff_tac`Y = Z`>-PROVE_TAC[syneq_refl] >>
    simp[Abbr`Y`,Abbr`Z`,Abbr`recs`] >>
    match_mp_tac (GSYM EL_MAP) >>
    fs[] >> DECIDE_TAC ) >>
  Q.PAT_ABBREV_TAC`lenvs = LENGTH (FILTER P (free_vars X))` >>
  Q.PAT_ABBREV_TAC`envs:num list = MAP X (FILTER Y Z)` >>
  `lenvs = LENGTH envs` by ( simp[Abbr`lenvs`,Abbr`envs`]) >>
  qunabbrev_tac`lrecs` >> fs[] >>
  qmatch_assum_abbrev_tac`n < LENGTH vs + 1 + lrecs + LENGTH envs` >>
  `lrecs = LENGTH recs` by simp[Abbr`lrecs`] >> fs[] >>
  simp[EL_APPEND2,EL_GENLIST,EL_MAP,el_check_def] >>
  rator_x_assum`benv_bvs`mp_tac >>
  simp[Once Cv_bv_cases] >> strip_tac >>
  qpat_assum`∀i. i < LENGTH envs ⇒ X`(qspec_then`n - (LENGTH recs + (LENGTH vs + 1))` mp_tac) >>
  simp[] >> strip_tac >> simp[] )

(* compile_varref *)

val compile_varref_thm = store_thm("compile_varref_thm",
  ``∀bs bc0 code bc1 cls sz cs b bv bs'.
      ((compile_varref sz cs b).out = REVERSE code ++ cs.out) ∧
      (bs.code = bc0 ++ code ++ bc1) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      (lookup_ct sz bs.stack (DRESTRICT bs.refs cls) bs.globals b = SOME bv) ∧
      (bs' = bs with <| stack := bv::bs.stack ; pc := next_addr bs.inst_length (bc0 ++ code)|>)
      ⇒
      bc_next^* bs bs'``,
  ntac 7 gen_tac >> Cases >> rw[] >>
  TRY(Cases_on`c`>>fs[])>>
  qpat_assum`X = REVERSE code`(assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
  qmatch_assum_abbrev_tac `code = x::ls1` >>
  `bc_fetch bs = SOME x` by (
    match_mp_tac bc_fetch_next_addr >>
    map_every qexists_tac [`bc0`,`ls1++bc1`] >>
    rw[Abbr`x`,Abbr`ls1`]) >>
  TRY (
    qmatch_abbrev_tac `bc_next^* bs bs'` >>
    `(bc_eval1 bs = SOME bs')` by (
      rw[bc_eval1_def,Abbr`x`] >>
      rfs[el_check_def] >>
      TRY (qpat_assum`OPTION_JOIN X = SOME bv`mp_tac >> rw[el_check_def]) >>
      rw[bc_eval_stack_def] >>
      srw_tac[ARITH_ss][bump_pc_def,SUM_APPEND,FILTER_APPEND,ADD1,Abbr`bs'`,Abbr`ls1`,bc_state_component_equality] >>
      NO_TAC) >>
    metis_tac[bc_eval1_thm,RTC_CASES1] )
  >- (
    rfs[el_check_def] >>
    qmatch_abbrev_tac `bc_next^* bs bs'` >>
    qpat_assum `X = SOME bv` mp_tac >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    qpat_assum `X = SOME bv` mp_tac >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    srw_tac[DNF_ss][RTC_eq_NRC] >>
    qexists_tac `SUC (SUC (SUC (SUC ZERO)))` >> rw[NRC] >>
    srw_tac[DNF_ss][ALT_ZERO] >>
    rw[bc_eval1_thm] >>
    rw[Once bc_eval1_def,Abbr`x`] >>
    srw_tac[DNF_ss][] >>
    rw[bc_eval_stack_def] >>
    Q.PAT_ABBREV_TAC `bs0 = bump_pc bs with stack := st` >>
    qunabbrev_tac`ls1` >>
    fs[] >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x;y;z;w] ++ bc1` >>
    `bc_fetch bs0 = SOME y` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac [`ls0++[x]`,`z::w::bc1`] >>
      rw[Abbr`bs0`,Abbr`y`,bump_pc_def] >>
      srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND,Abbr`x`] ) >>
    rw[Once bc_eval1_def,Abbr`y`] >>
    srw_tac[DNF_ss][] >>
    rw[bc_eval_stack_def,Abbr`bs0`] >>
    Q.PAT_ABBREV_TAC`bs0 = bump_pc X with stack := Y` >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x;y;z;w] ++ bc1` >>
    `bc_fetch bs0 = SOME z` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac [`ls0++[x;y]`,`w::bc1`] >>
      rw[Abbr`bs0`,bump_pc_def,Abbr`z`] >>
      srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND,Abbr`y`,Abbr`x`] ) >>
    rw[Once bc_eval1_def,Abbr`z`,bc_eval_stack_def,bump_pc_def] >>
    qunabbrev_tac`bs0` >>
    qmatch_abbrev_tac`bc_eval1 bs0 = SOME bs2` >>
    `bc_fetch bs0 = SOME w` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac `ls0++[x;y;Stack(PushInt 0)]` >>
      simp[Abbr`bs0`,bump_pc_def,Abbr`w`,Abbr`x`,Abbr`y`] >>
      srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND] ) >>
    simp[bc_eval1_def,Abbr`w`,Abbr`bs0`,bump_pc_def] >>
    fs[FLOOKUP_DEF] >>
    unabbrev_all_tac >>
    fs[FDOM_DRESTRICT,DRESTRICT_DEF] >>
    rfs[] >>
    simp[bc_state_component_equality] >>
    srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND,ADD1] )
  >- (
    rfs[el_check_def] >>
    qmatch_abbrev_tac `bc_next^* bs bs'` >>
    qpat_assum `X = SOME bv` mp_tac >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    rw[RTC_eq_NRC] >>
    qexists_tac `SUC (SUC ZERO)` >> rw[NRC] >>
    srw_tac[DNF_ss][ALT_ZERO] >>
    rw[bc_eval1_thm] >>
    rw[Once bc_eval1_def,Abbr`x`] >>
    rfs[el_check_def] >>
    rw[bc_eval_stack_def] >>
    qunabbrev_tac`ls1` >> fs[] >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x;y] ++ bc1` >>
    qmatch_abbrev_tac `bc_eval1 bs0 = SOME bs'` >>
    `bc_fetch bs0 = SOME y` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac [`ls0++[x]`,`bc1`] >>
      unabbrev_all_tac >> rw[bump_pc_def] >>
      srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND] ) >>
    rw[bc_eval1_def,Abbr`y`] >>
    rw[bc_eval_stack_def,Abbr`bs0`,Abbr`bs'`] >>
    unabbrev_all_tac >>
    srw_tac[ARITH_ss][bump_pc_def,FILTER_APPEND,SUM_APPEND,ADD1] ))

val compile_envref_next_label_inc = store_thm("compile_envref_next_label_inc",
  ``∀sz cs b. (compile_envref sz cs b).next_label = cs.next_label``,
  ntac 2 gen_tac >> Cases >> rw[])
val _ = export_rewrites["compile_envref_next_label_inc"]

val compile_varref_next_label_inc = store_thm("compile_varref_next_label_inc",
  ``∀sz cs b. (compile_varref sz cs b).next_label = cs.next_label``,
  ntac 2 gen_tac >> Cases >> rw[])
val _ = export_rewrites["compile_varref_next_label_inc"]

val compile_envref_append_out = store_thm("compile_envref_append_out",
  ``∀sz cs b. ∃bc. ((compile_envref sz cs b).out = bc ++ cs.out) ∧ (EVERY ($~ o is_Label) bc) ∧ code_labels_ok bc``,
  ho_match_mp_tac compile_envref_ind >> rw[] >>
  rpt(match_mp_tac code_labels_ok_cons >> simp[]))

val compile_varref_append_out = store_thm("compile_varref_append_out",
  ``∀sz cs b. ∃bc. ((compile_varref sz cs b).out = bc ++ cs.out) ∧ (EVERY ($~ o is_Label) bc) ∧ code_labels_ok bc``,
  ntac 2 gen_tac >> Cases >> rw[compile_envref_append_out] >>
  rpt(match_mp_tac code_labels_ok_cons >> simp[]))

(* prim1 and prim2 *)

val bool_to_tag_inj = Q.prove (
`!b1 b2. (bool_to_tag b1 = bool_to_tag b2) = (b1 = b2)`,
  Cases_on `b1` >>
  Cases_on `b2` >>
  rw []);

val helper_tac =
   rw [] >>
   fs [Once Cv_bv_cases] >>
   rw [bc_equal_def] >>
   full_simp_tac (srw_ss()++ARITH_ss) [bool_to_tag_inj, el_check_def] >>
   rw [] >>
   TRY (TRY (Cases_on `b`) >> TRY (Cases_on `b'`) >> TRY (Cases_on `b''`) >> full_simp_tac (srw_ss()++ARITH_ss) [] >> NO_TAC);

val bc_equal_list_Number = prove(
  ``∀f. (∀x y. f x = f y ⇔ x = y) ⇒
      ∀l1 l2. bc_equal_list (MAP (Number o f) l1) (MAP (Number o f) l2) = Eq_val (l1 = l2)``,
  gen_tac >> strip_tac >> Induct >> TRY Cases >> simp[bc_equal_def] >>
  gen_tac >> Cases >> simp[bc_equal_def] >> rw[])

val do_Ceq_to_bc_equal = Q.prove (
  `ALL_DISTINCT (FST pp).sm ⇒
   (!v1 v2 bv1 bv2.
    Cv_bv pp v1 bv1 ∧ Cv_bv pp v2 bv2 ⇒
    (!b. (do_Ceq v1 v2 = Eq_val b) ⇒  (bc_equal bv1 bv2 = Eq_val b)) ∧
    ((do_Ceq v1 v2 = Eq_closure) ⇒  (bc_equal bv1 bv2 = Eq_closure))) ∧
   (!vs1 vs2 bvs1 bvs2.
    LIST_REL (Cv_bv pp) vs1 bvs1 ∧ LIST_REL (Cv_bv pp) vs2 bvs2 ⇒
    (!b. (do_Ceq_list vs1 vs2 = Eq_val b) ⇒  (bc_equal_list bvs1 bvs2 = Eq_val b)) ∧
    ((do_Ceq_list vs1 vs2 = Eq_closure) ⇒ (bc_equal_list bvs1 bvs2 = Eq_closure)))`,
  strip_tac >>
  ho_match_mp_tac do_Ceq_ind >>
  rw [] >-
  (helper_tac >> TRY(fs[semanticPrimitivesTheory.lit_same_type_def,LIST_EQ_REWRITE]>>NO_TAC) >>
   match_mp_tac bc_equal_list_Number >> rw[stringTheory.ORD_11] ) >-
  (helper_tac >> metis_tac [ALL_DISTINCT_EL_IMP]) >-
  (helper_tac >> fs[EVERY2_EVERY] >> metis_tac []) >-
  (helper_tac >> fs[EVERY2_EVERY] >> metis_tac []) >-
  (helper_tac >> fs[EVERY2_EVERY]) >-
  (helper_tac >> fs[EVERY2_EVERY]) >-
  (helper_tac >> fs[EVERY2_EVERY]) >-
  (helper_tac >> fs[EVERY2_EVERY]) >-
  helper_tac >-
  helper_tac >-
  helper_tac >-
  helper_tac >-
  (Cases_on `do_Ceq v1 v2` >>
    fs [] >>
    Cases_on `b'` >>
    fs [] >>
    rw [bc_equal_def]) >-
  (Cases_on `do_Ceq v1 v2` >>
    fs [] >>
    TRY (Cases_on `b'`) >>
    fs [] >>
    rw [bc_equal_def] >>
    fs []) >-
  rw [bc_equal_def] >-
  rw [bc_equal_def]);

val is_Label_prim2_to_bc = store_thm("is_Label_prim2_to_bc",
  ``∀op. ¬is_Label (prim2_to_bc op)``,
  Cases >> Cases_on`C` >> rw[])
val _ = export_rewrites["is_Label_prim2_to_bc"]

val inst_uses_label_prim2_to_bc = store_thm("inst_uses_label_prim2_to_bc",
  ``∀l op. ¬inst_uses_label l (prim2_to_bc op)``,
  Cases_on`op`>>Cases_on`C`>>
  rw[inst_uses_label_def])
val _ = export_rewrites["inst_uses_label_prim2_to_bc"]

val prim2_to_bc_thm = store_thm("prim2_to_bc_thm",
  ``∀s op v1 v2 s' v bs bce bc0 bc1 st bv1 bv2 pp.
    (bs.code = bc0 ++ [(prim2_to_bc op)] ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (v2 = CLitv(IntLit &0) ⇒ (op ≠ P2p CDiv) ∧ (op ≠ P2p CMod)) ∧
    s_refs (FST pp) s (bs with code := bce) ∧
    (CevalPrim2 s op v1 v2 = (s', Rval v)) ∧
    Cv_bv pp v1 bv1 ∧ Cv_bv pp v2 bv2 ∧
    (bs.stack = bv2::bv1::st) ∧
    ALL_DISTINCT (FST pp).sm
    ⇒ ∃rd rf bv.
      Cv_bv (rd,SND pp) v bv ∧
      let bs' = bump_pc (bs with <|stack := bv::st; refs := rf|>) in
      bc_next bs bs' ∧
      s_refs rd s' (bs' with code := bce) ∧
      DRESTRICT bs.refs (COMPL (set (FST pp).sm)) ⊑ DRESTRICT rf (COMPL (set rd.sm)) ∧
      rd.cls = (FST pp).cls ∧
      (FST pp).sm ≼ rd.sm``,
  simp[] >> rw[] >>
  `bc_fetch bs = SOME (prim2_to_bc op)` by (
    match_mp_tac bc_fetch_next_addr >>
    map_every qexists_tac[`bc0`,`bc1`] >>
    rw[]) >>
  rw[bc_eval1_thm] >>
  simp[bc_eval1_def] >>
  Cases_on`op` >- (
    qmatch_assum_rename_tac`bc_fetch bs = SOME (prim2_to_bc (P2p op))`[] >>
    qexists_tac`FST pp`>>
    qexists_tac`bs.refs` >> simp[] >>
    (Cases_on`op`)>>fs[bump_pc_with_stack] >>
    TRY (
      Cases_on `do_Ceq v1 v2` >>
      fs [] >>
      rw [Once Cv_bv_cases, bc_eval_stack_def,bc_state_component_equality] >>
      imp_res_tac do_Ceq_to_bc_equal >>
      rw [bump_pc_def,bc_fetch_with_refs] >>
      simp[s_refs_with_stack] >>
      match_mp_tac s_refs_with_irr >>
      simp[] >>
      HINT_EXISTS_TAC >> simp[]) >>
    simp[bump_pc_def,s_refs_with_pc,s_refs_with_stack] >>
    Cases_on `v1` >> TRY (Cases_on `l`) >>
    Cases_on `v2` >> TRY (Cases_on `l`) >>
    fs[] >> rw[] >> fs[Cv_bv_cases_lit,Cv_bv_cases_conv,Cv_bv_cases_vectorv] >> rw[] >>
    BasicProvers.EVERY_CASE_TAC >>
    rw[bc_eval_stack_def] >> fs[] >>
    TRY (Cases_on `b` >> rw[]) >>
    TRY (Cases_on `b'` >> rw[]) >>
    srw_tac[ARITH_ss][] >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    fsrw_tac[DNF_ss][EL_ALL_DISTINCT_EL_EQ,el_check_def] >>
    fs[s_refs_def,good_rd_def] >>
    simp[bc_state_component_equality] >>
    fs[integerTheory.INT_NOT_LT] >>
    rfs[GSYM integerTheory.INT_ABS_EQ_ID] >>
    simp[arithmeticTheory.ADD1] >>
    Cases_on`Num i`>>simp[] >>
    first_x_assum match_mp_tac >>
    simp[MEM_ZIP] >>
    metis_tac[arithmeticTheory.LESS_EQ]) >>
  qmatch_assum_rename_tac`bc_fetch bs = SOME (prim2_to_bc (P2s op))`[] >>
  PairCases_on`s` >>
  Cases_on`op`>>simp[bump_pc_with_stack] >>
  fs[LET_THM,UNCURRY] >> rw[] >>
  Cases_on `v2` >> TRY (Cases_on `l`) >> fs[] >>
  Cases_on `v1` >> TRY (Cases_on `l`) >> fs[] >>
  fs[Q.SPECL[`CLitv X`](CONJUNCT1 (Q.SPEC`pp`Cv_bv_cases))] >>
  fs[Q.SPEC`CLoc X`(CONJUNCT1 (Q.SPEC`pp`Cv_bv_cases))] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rpt(qpat_assum`X = Rval v`mp_tac >>
      BasicProvers.CASE_TAC >> strip_tac) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[bump_pc_def,bc_fetch_with_refs,bc_state_component_equality] >>
  simp[Once Cv_bv_cases] >>
  fs[el_check_def] >- (
    `LENGTH (FST pp).sm = LENGTH s1` by fs[s_refs_def] >>
    qexists_tac`FST pp with sm := (FST pp).sm ++ [(LEAST n. n ∉ FDOM bs.refs)]` >>
    simp[EL_APPEND2] >>
    simp[wordsTheory.w2n_lt,integerTheory.int_le] >>
    simp[s_refs_with_stack,s_refs_with_pc] >>
    Q.PAT_ABBREV_TAC`n = LEAST n. n ∉ FDOM bs.refs` >>
    `n ∉ FDOM bs.refs` by (
      unabbrev_all_tac >>
      numLib.LEAST_ELIM_TAC >>
      simp[] >>
      metis_tac[NOT_IN_FINITE,INFINITE_NUM_UNIV,FDOM_FINITE] ) >>
    fs[s_refs_def] >>
    simp[GSYM CONJ_ASSOC] >>
    conj_tac >- (
      fs[good_rd_def,FEVERY_DEF,UNCURRY,FLOOKUP_UPDATE] >>
      gen_tac >> strip_tac >>
      first_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
      conj_asm1_tac >- (spose_not_then strip_assume_tac >> fs[FLOOKUP_DEF]) >>
      simp[] >>
      match_mp_tac(MP_CANON(GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
      first_assum(match_exists_tac o concl) >>
      simp[] >>
      fs[EVERY_MEM,FLOOKUP_DEF] >>
      metis_tac[] ) >>
    conj_tac >- fs[EVERY_MEM] >>
    conj_tac >- (
      fs[ALL_DISTINCT_APPEND,EVERY_MEM] >>
      metis_tac[] ) >>
    simp[integerTheory.INT_ABS] >>
    simp[CONJ_ASSOC] >>
    reverse conj_tac >- (
      simp[SUBMAP_DEF,DRESTRICT_DEF] >> rw[] >> rw[] ) >>
    conj_tac >>
    match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    TRY (
      first_assum(match_exists_tac o concl) >>
      simp[] >>
      Cases >> simp[optionTheory.OPTREL_def,PULL_EXISTS] >>
      rw[] >>
      match_mp_tac(MP_CANON(GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
      first_assum(match_exists_tac o concl) >>
      simp[] >>
      fs[EVERY_MEM,FLOOKUP_DEF,good_rd_def,FEVERY_DEF,UNCURRY] >>
      metis_tac[] ) >>
    qmatch_assum_abbrev_tac`LIST_REL R s1 Y` >>
    qexists_tac`R` >>
    simp[Abbr`R`,UNCURRY,Abbr`Y`] >>
    fs[LIST_REL_EL_EQN] >> rw[] >>
    match_mp_tac (MP_CANON (GEN_ALL sv_refv_rel_mono)) >>
    TRY(first_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
        simp[EL_MAP] >> strip_tac)>>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    simp[FAPPLY_FUPDATE_THM] >>
    TRY(
      BasicProvers.CASE_TAC >- (
        fs[EVERY_MEM] >>
        metis_tac[MEM_EL] )) >>
    first_assum(match_exists_tac o concl) >>
    simp[] >> rw[] >>
    match_mp_tac(MP_CANON(GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
    first_assum(match_exists_tac o concl) >>
    simp[] >>
    fs[EVERY_MEM,FLOOKUP_DEF,good_rd_def,FEVERY_DEF,UNCURRY] >>
    metis_tac[] ) >>
  simp[s_refs_with_stack,s_refs_with_pc] >>
  qexists_tac`FST pp` >>
  qexists_tac`bs.refs` >>
  simp[] >>
  fs[s_refs_def,FLOOKUP_DEF,EVERY_MEM] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[good_rd_def] >>
  conj_asm1_tac >- (
    first_x_assum match_mp_tac >>
    metis_tac[MEM_EL] ) >>
  fs[LIST_REL_EL_EQN] >>
  rpt(first_x_assum(qspec_then`n`mp_tac)) >>
  simp[sv_refv_rel_cases,EL_MAP,bc_state_component_equality] >>
  rfs[integerTheory.int_le,integerTheory.INT_ABS] >>
  rw[] >> DECIDE_TAC)

val is_Label_prim1_to_bc = store_thm("is_Label_prim1_to_bc",
  ``∀uop. EVERY ($~ o is_Label) (prim1_to_bc uop)``,
  Cases >> rw[])
val _ = export_rewrites["is_Label_prim1_to_bc"]

val contains_primitives_def = Define`
  contains_primitives code ⇔
  ∃bc0 bc1.
    code = bc0 ++ VfromListCode ++ bc1 ∧
    ALL_DISTINCT (FILTER is_Label code)`

fun next_addr_tac [QUOTE s] =
    match_mp_tac bc_fetch_next_addr >> simp[Abbr`bs1`] >>
    qexists_tac`bc0 ++ (DROP 2 (TAKE ^(Parse.Term [QUOTE (s^":num")]) VfromListCode))` >>
    simp[VfromListCode_def] >>
    REWRITE_TAC[SUM_APPEND,FILTER_APPEND,MAP_APPEND] >>
    EVAL_TAC >> simp[]

val VfromListCode_aux_correct = prove(
  ``∀vl ls bs bc0 bc1 bvl st cnt pp loopcode.
      loopcode = DROP 2 (TAKE 20 VfromListCode) ∧
      bs.code = bc0 ++ loopcode ++ bc1 ∧
      ALL_DISTINCT (FILTER is_Label (bc0 ++ loopcode)) ∧
      bs.stack = Number cnt::bvl::st ∧
      bs.pc = next_addr bs.inst_length bc0 ∧
      Cv_bv pp vl bvl ∧
      CvFromList vl = SOME ls
      ⇒
      ∃bls.
      let bs' = bs with <| pc := next_addr bs.inst_length (bc0++loopcode);
                           stack := Number (cnt + &LENGTH ls)::(REVERSE bls)++st |> in
      bc_next^* bs bs' ∧
      LIST_REL (Cv_bv pp) ls bls``,
  ho_match_mp_tac CvFromList_ind >>
  simp[CvFromList_def] >>
  conj_tac >- (
    rw[Cv_bv_cases_conv] >>
    srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
    `bc_fetch bs = SOME (Stack (Load 1))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0++[Label(VfromListLab+1)]` >> simp[] >>
      simp[FILTER_APPEND,SUM_APPEND] >>
      simp[VfromListCode_def] ) >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def,bc_eval_stack_def] >>
    qho_match_abbrev_tac`bc_next^* bs1 bs2` >>
    srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
    `bc_fetch bs1 = SOME (Stack (TagEq (block_tag+nil_tag)))` by (
      match_mp_tac bc_fetch_next_addr >> simp[Abbr`bs1`] >>
      qexists_tac`bc0 ++ (DROP 2 (TAKE 4 VfromListCode))` >>
      simp[VfromListCode_def] >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def,bc_eval_stack_def,Abbr`bs1`] >>
    qho_match_abbrev_tac`bc_next^* bs1 bs2` >>
    `bc_fetch bs1 = SOME (JumpIf (Lab (VfromListLab+2)))` by (
      match_mp_tac bc_fetch_next_addr >> simp[Abbr`bs1`] >>
      qexists_tac`bc0 ++ (DROP 2 (TAKE 5 VfromListCode))` >>
      simp[VfromListCode_def] >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,PULL_EXISTS] >>
    qexists_tac`next_addr bs.inst_length (bc0 ++ DROP 2 (TAKE 19 VfromListCode))` >>
    conj_tac >- (
      simp[bc_find_loc_def] >>
      match_mp_tac bc_find_loc_aux_append_code >>
      match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
      qexists_tac`LENGTH bc0 + 16` >>
      rfs[] >>
      simp[VfromListCode_def,EL_APPEND1,EL_APPEND2] >>
      simp[TAKE_APPEND1,TAKE_APPEND2] >>
      REWRITE_TAC[FILTER_APPEND] >>
      EVAL_TAC ) >>
    match_mp_tac RTC_SUBSET >>
    qho_match_abbrev_tac`bc_next bs1 bs2` >>
    `bc_fetch bs1 = SOME (Stack (Pops 1))` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs1`] >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`bc1` >>
      simp[VfromListCode_def] ) >>
    simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,bc_eval_stack_def,bump_pc_def] >>
    simp[Abbr`bs2`,bc_state_component_equality] >>
    simp[VfromListCode_def] >>
    REWRITE_TAC[SUM_APPEND,FILTER_APPEND,MAP_APPEND] >>
    EVAL_TAC >> simp[]) >>
  rw[] >>
  Cases_on`CvFromList vl`>>fs[]>>rw[]>>
  simp[PULL_EXISTS] >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs = SOME (Stack (Load 1))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++[Label(VfromListLab+1)]` >> simp[] >>
    simp[FILTER_APPEND,SUM_APPEND] >>
    simp[VfromListCode_def] ) >>
  simp[bc_eval1_thm,bc_eval1_def,bump_pc_def,bc_eval_stack_def] >>
  qho_match_abbrev_tac`∃v vs. bc_next^* bs1 (bs2 v vs) ∧ P v vs` >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs1 = SOME (Stack (TagEq (block_tag+nil_tag)))` by (next_addr_tac`4`) >>
  fs[Cv_bv_cases_conv] >> rw[] >>
  simp[bc_eval1_thm,bc_eval1_def,bump_pc_def,bc_eval_stack_def,Abbr`bs1`] >>
  `cons_tag ≠ nil_tag` by EVAL_TAC >> simp[] >> pop_assum kall_tac >>
  qho_match_abbrev_tac`∃v vs. bc_next^* bs1 (bs2 v vs) ∧ P v vs` >>
  `bc_fetch bs1 = SOME (JumpIf (Lab (VfromListLab+2)))` by (next_addr_tac`5`) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,PULL_EXISTS] >>
  CONV_TAC(RESORT_EXISTS_CONV(sort_vars["n"])) >>
  qexists_tac`next_addr bs.inst_length (bc0 ++ DROP 2 (TAKE 19 VfromListCode))` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    simp[bc_find_loc_def] >>
    match_mp_tac bc_find_loc_aux_append_code >>
    match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
    qexists_tac`LENGTH bc0 + 16` >>
    rfs[] >>
    simp[VfromListCode_def,EL_APPEND1,EL_APPEND2] >>
    simp[TAKE_APPEND1,TAKE_APPEND2] >>
    REWRITE_TAC[FILTER_APPEND] >>
    EVAL_TAC ) >>
  simp[bump_pc_with_stack] >>
  fs[bump_pc_def,bc_fetch_with_stack] >>
  qho_match_abbrev_tac`∃v vs. bc_next^* bs1 (bs2 v vs) ∧ P v vs` >>
  `bc_fetch bs1 = SOME (Stack (PushInt 1))` by (next_addr_tac`6`) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,bc_eval_stack_def,bump_pc_def] >>
  ntac 3 (pop_assum kall_tac) >>
  qho_match_abbrev_tac`∃v vs. bc_next^* bs1 (bs2 v vs) ∧ P v vs` >>
  `bc_fetch bs1 = SOME (Stack Add)` by (next_addr_tac`7`) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,bc_eval_stack_def,bump_pc_def] >>
  pop_assum kall_tac >>
  qho_match_abbrev_tac`∃v vs. bc_next^* bs1 (bs2 v vs) ∧ P v vs` >>
  `bc_fetch bs1 = SOME (Stack (Load 1))` by (next_addr_tac`8`) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,bc_eval_stack_def,bump_pc_def] >>
  pop_assum kall_tac >>
  qho_match_abbrev_tac`∃v vs. bc_next^* bs1 (bs2 v vs) ∧ P v vs` >>
  `bc_fetch bs1 = SOME (Stack (El 1))` by (next_addr_tac`9`) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,bc_eval_stack_def,bump_pc_def] >>
  pop_assum kall_tac >>
  qho_match_abbrev_tac`∃v vs. bc_next^* bs1 (bs2 v vs) ∧ P v vs` >>
  `bc_fetch bs1 = SOME (Stack (Load 2))` by (next_addr_tac`10`) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,bc_eval_stack_def,bump_pc_def] >>
  pop_assum kall_tac >>
  qho_match_abbrev_tac`∃v vs. bc_next^* bs1 (bs2 v vs) ∧ P v vs` >>
  `bc_fetch bs1 = SOME (Stack (El 0))` by (next_addr_tac`11`) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,bc_eval_stack_def,bump_pc_def] >>
  pop_assum kall_tac >>
  qho_match_abbrev_tac`∃v vs. bc_next^* bs1 (bs2 v vs) ∧ P v vs` >>
  `bc_fetch bs1 = SOME (Stack (Store 2))` by (next_addr_tac`12`) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,bc_eval_stack_def,bump_pc_def] >>
  pop_assum kall_tac >>
  qho_match_abbrev_tac`∃v vs. bc_next^* bs1 (bs2 v vs) ∧ P v vs` >>
  `bc_fetch bs1 = SOME (Stack (Load 0))` by (next_addr_tac`13`) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,bc_eval_stack_def,bump_pc_def] >>
  pop_assum kall_tac >>
  qho_match_abbrev_tac`∃v vs. bc_next^* bs1 (bs2 v vs) ∧ P v vs` >>
  `bc_fetch bs1 = SOME (Stack (Load 2))` by (next_addr_tac`14`) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,bc_eval_stack_def,bump_pc_def] >>
  pop_assum kall_tac >>
  qho_match_abbrev_tac`∃v vs. bc_next^* bs1 (bs2 v vs) ∧ P v vs` >>
  `bc_fetch bs1 = SOME (Stack (Store 1))` by (next_addr_tac`15`) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,bc_eval_stack_def,bump_pc_def] >>
  pop_assum kall_tac >>
  qho_match_abbrev_tac`∃v vs. bc_next^* bs1 (bs2 v vs) ∧ P v vs` >>
  `bc_fetch bs1 = SOME (Stack (Store 1))` by (next_addr_tac`16`) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,bc_eval_stack_def,bump_pc_def] >>
  pop_assum kall_tac >>
  qho_match_abbrev_tac`∃v vs. bc_next^* bs1 (bs2 v vs) ∧ P v vs` >>
  `bc_fetch bs1 = SOME (Jump (Lab (VfromListLab + 1)))` by (next_addr_tac`17`) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,PULL_EXISTS] >>
  pop_assum kall_tac >>
  CONV_TAC(RESORT_EXISTS_CONV(sort_vars["n"])) >>
  qexists_tac`next_addr bs.inst_length bc0` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    simp[bc_find_loc_def] >>
    match_mp_tac bc_find_loc_aux_append_code >>
    match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
    qexists_tac`LENGTH bc0` >>
    rfs[] >>
    simp[VfromListCode_def,EL_APPEND1,EL_APPEND2] >>
    simp[TAKE_APPEND1,TAKE_APPEND2]) >>
  qho_match_abbrev_tac`∃v vs. bc_next^* bs1 (bs2 v vs) ∧ P v vs` >>
  first_x_assum(qspecl_then[`bs1`,`bc0`]mp_tac) >>
  rfs[] >> simp[Abbr`bs1`] >>
  disch_then(qspec_then`pp`mp_tac) >> simp[] >>
  strip_tac >>
  srw_tac[DNF_ss][Once RTC_CASES_RTC_TWICE] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
  simp[bc_state_component_equality,Abbr`bs2`,arithmeticTheory.ADD1] >>
  conj_tac >- intLib.COOPER_TAC >>
  simp[Abbr`P`])

val VfromListCode_correct = prove(
  ``∀bce. contains_primitives bce ⇒
      ∀bs bcr vl st bvl ls pp.
      bs.code = bce ++ bcr ∧
      bc_fetch bs = SOME (Call (Lab VfromListLab)) ∧
      bs.stack = bvl::st ∧
      Cv_bv pp vl bvl ∧
      CvFromList vl = SOME ls
      ⇒
      ∃bls.
      let bs' = bump_pc bs with stack := Block vector_tag bls :: st in
      bc_next^* bs bs' ∧
      LIST_REL (Cv_bv pp) ls bls``,
  simp[] >> rw[] >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  fs[contains_primitives_def,bc_find_loc_def] >>
  simp[PULL_EXISTS] >> CONV_TAC SWAP_EXISTS_CONV >>
  qexists_tac`next_addr bs.inst_length (TAKE (LENGTH bc0) bs.code)` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    BasicProvers.VAR_EQ_TAC >>
    match_mp_tac bc_find_loc_aux_append_code >>
    match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
    qexists_tac`LENGTH bc0` >> rfs[] >>
    simp[EL_APPEND1,EL_APPEND2,VfromListCode_def] >>
    simp[TAKE_APPEND1,TAKE_APPEND2]) >>
  simp[TAKE_APPEND1] >>
  qho_match_abbrev_tac`∃bls. bc_next^* bs1 (bs2 bls) ∧ P bls` >>
  `bc_fetch bs1 = SOME (Stack (PushInt 0))` by (
    match_mp_tac bc_fetch_next_addr >>
    simp[Abbr`bs1`] >>
    qexists_tac`bc0 ++ [HD VfromListCode]` >>
    simp[VfromListCode_def,SUM_APPEND,FILTER_APPEND] ) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,bump_pc_def] >>
  simp[Abbr`bs1`] >>
  qho_match_abbrev_tac`∃bls. bc_next^* bs1 (bs2 bls) ∧ P bls` >>
  qspec_then`vl`mp_tac VfromListCode_aux_correct >> simp[] >>
  `bs1.code = bs.code` by simp[Abbr`bs1`] >>
  disch_then(qspec_then`bs1`mp_tac) >> simp[] >>
  disch_then(qspec_then`bc0++(TAKE 2 VfromListCode)`mp_tac) >> simp[] >>
  simp[Once VfromListCode_def] >>
  simp[Once VfromListCode_def] >>
  simp[Once VfromListCode_def] >> rfs[] >>
  simp[Abbr`bs1`] >>
  disch_then(qspec_then`pp`mp_tac) >> simp[] >>
  discharge_hyps >- (
    rator_x_assum`ALL_DISTINCT`mp_tac >>
    simp[VfromListCode_def] >>
    REWRITE_TAC[SUM_APPEND,FILTER_APPEND,MAP_APPEND,ALL_DISTINCT_APPEND] >>
    EVAL_TAC >>
    strip_tac >> simp[]  >> rw[] >>
    spose_not_then strip_assume_tac >> res_tac >> fs[]) >>
  strip_tac >>
  qexists_tac`bls` >> simp[] >>
  qho_match_abbrev_tac`bc_next^* bs1 (bs2 bls)` >>
  qmatch_assum_abbrev_tac`bc_next^* bs1' bs3` >>
  `bs1' = bs1` by (
    simp[Abbr`bs1`,Abbr`bs1'`,bc_state_component_equality] >>
    simp[VfromListCode_def] >>
    REWRITE_TAC[SUM_APPEND,FILTER_APPEND,MAP_APPEND] >>
    EVAL_TAC >> simp[] ) >>
  simp[Once RTC_CASES_RTC_TWICE] >>
  qunabbrev_tac`bs1'`>>fs[] >> pop_assum kall_tac >>
  HINT_EXISTS_TAC >> simp[Abbr`bs1`] >>
  `bc_fetch bs3 = SOME (Stack (Cons2 vector_tag))` by (
    match_mp_tac bc_fetch_next_addr >>
    simp[Abbr`bs3`] >>
    qexists_tac`bc0 ++ (TAKE 20 VfromListCode)` >>
    simp[VfromListCode_def] >>
    REWRITE_TAC[FILTER_APPEND,SUM_APPEND,MAP_APPEND] >>
    EVAL_TAC >> simp[] ) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`bs3`,bc_eval_stack_def,bump_pc_def] >>
  fs[Abbr`P`] >> imp_res_tac LIST_REL_LENGTH >> simp[] >>
  simp[TAKE_APPEND1,TAKE_LENGTH_ID_rwt,DROP_APPEND1,DROP_LENGTH_NIL_rwt] >>
  qho_match_abbrev_tac`bc_next^* bs1 (bs2 bls)` >>
  `bc_fetch bs1 = SOME Return` by (
    match_mp_tac bc_fetch_next_addr >>
    simp[Abbr`bs1`] >>
    qexists_tac`bc0 ++ (FRONT VfromListCode)` >>
    simp[VfromListCode_def] >>
    REWRITE_TAC[FILTER_APPEND,SUM_APPEND,MAP_APPEND] >>
    EVAL_TAC >> simp[] ) >>
  match_mp_tac RTC_SUBSET >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,Abbr`bs2`,bump_pc_def])

val prim1_to_bc_thm = store_thm("prim1_to_bc_thm",
  ``∀rd op ck s v1 s' v bs bc0 bc1 bce bcr st bv1.
    (bs.code = bc0 ++ prim1_to_bc op ++ bc1) ∧
    (bs.code = bce ++ bcr) ∧
    contains_primitives bce ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (CevalPrim1 op s v1 = (s', Rval v)) ∧
    Cv_bv (mk_pp rd (bs with code := bce)) v1 bv1 ∧
    (bs.stack = bv1::st) ∧
    s_refs rd ((ck,FST s),SND s) (bs with code := bce)
    ⇒ ∃bv rf gv sm'.
      let bs' = bs with <|stack := bv::st; refs := rf; pc := next_addr bs.inst_length (bc0 ++ prim1_to_bc op); globals := gv|> in
      let rd' = rd with sm := sm' in
      bc_next^* bs bs' ∧
      Cv_bv (mk_pp rd' (bs' with <| code := bce |>)) v bv ∧
      s_refs rd' ((ck,FST s'),SND s') (bs' with code := bce) ∧
      DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf (COMPL (set sm')) ∧
      gvrel bs.globals gv ∧
      rd.sm ≼ sm'``,
  simp[] >> rw[] >>
  `bc_fetch bs = SOME (HD (prim1_to_bc op))` by (
    match_mp_tac bc_fetch_next_addr >>
    map_every qexists_tac[`bc0`,`(TL (prim1_to_bc op)) ++ bc1`] >>
    qpat_assum`bs.code = bce ++ bcr`kall_tac >>
    Cases_on`op`>>rw[] ) >>
  Cases_on`op = CVfromList` >- (
    fs[] >> rw[] >>
    Cases_on`CvFromList v1`>>fs[]>>rw[]>>
    qspec_then`bce`mp_tac VfromListCode_correct >>
    simp[] >>
    disch_then(qspecl_then[`bs`,`bcr`]mp_tac)>>simp[]>>
    disch_then(qspec_then`v1`mp_tac)>>simp[]>>
    qmatch_assum_abbrev_tac`Cv_bv pp v1 bv1` >>
    disch_then(qspec_then`pp`mp_tac)>>simp[]>>
    strip_tac >>
    simp[Cv_bv_cases_vectorv,PULL_EXISTS] >>
    map_every qexists_tac[`bs.refs`,`bs.globals`,`rd.sm`,`bls`] >>
    simp[] >>
    conj_tac >- (
      qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
      qmatch_abbrev_tac`bc_next^* bs bs1'` >>
      `bs1 = bs1'` by (
        simp[Abbr`bs1`,Abbr`bs1'`] >>
        simp[bump_pc_def,bc_state_component_equality] >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      rw[] ) >>
    match_mp_tac s_refs_with_irr >>
    HINT_EXISTS_TAC >> simp[]) >>
  simp[Once RTC_CASES1] >>
  srw_tac[DNF_ss][] >> disj2_tac >>
  simp[bc_eval1_thm] >>
  PairCases_on`s` >>
  Cases_on`op`>>
  simp[bc_eval1_def,bump_pc_def,bc_fetch_with_stack,bc_fetch_with_refs] >>
  fs[LET_THM] >- (
    qmatch_assum_abbrev_tac`CLoc n = v` >>
    simp[Once RTC_CASES1] >> srw_tac[DNF_ss][] >> disj2_tac >>
    simp[bc_eval_stack_def] >>
    Q.PAT_ABBREV_TAC`bs2:bc_state = X Y` >>
    `bc_fetch bs2 = SOME Ref` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac[`bc0 ++ [Stack(PushInt 1)]`,`bc1`] >>
      simp[Abbr`bs2`,FILTER_APPEND,SUM_APPEND]) >>
    simp[Once RTC_CASES1] >> srw_tac[DNF_ss][] >> disj1_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def,Abbr`bs2`] >>
    simp[bc_state_component_equality] >>
    Q.PAT_ABBREV_TAC`bn = LEAST n. n ∉ X` >>
    qexists_tac`rd.sm ++ [bn]` >>
    simp[Once Cv_bv_cases] >>
    `n = LENGTH rd.sm` by fs[s_refs_def] >>
    simp[el_check_def,EL_APPEND2] >>
    `bn ∉ FDOM bs.refs` by (
      unabbrev_all_tac >>
      numLib.LEAST_ELIM_TAC >>
      simp[] >>
      PROVE_TAC[NOT_IN_FINITE,INFINITE_NUM_UNIV,FDOM_FINITE] ) >>
    simp[SUM_APPEND,FILTER_APPEND] >>
    conj_tac >- (
      fs[s_refs_def] >>
      conj_tac >- (
        full_simp_tac std_ss [good_rd_def,theorem"refs_data_accfupds"] >>
        fs[FEVERY_DEF,DOMSUB_NOT_IN_DOM,UNCURRY] >>
        gen_tac >> strip_tac >>
        conj_asm1_tac >- (fs[FLOOKUP_DEF] >> metis_tac[]) >>
        simp[FLOOKUP_UPDATE] >>
        res_tac >> simp[] >>
        match_mp_tac(MP_CANON(GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
        qexists_tac`mk_pp rd (bs with code := bce)` >>
        simp[] >>
        fs[FLOOKUP_DEF] >>
        metis_tac[EVERY_MEM] ) >>
      conj_asm1_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF,FAPPLY_FUPDATE_THM,EXTENSION,EVERY_MEM] >>
        rw[] >> PROVE_TAC[] ) >>
      conj_tac >- (
        simp[ALL_DISTINCT_APPEND] >>
        fs[EVERY_MEM] >> PROVE_TAC[] ) >>
      conj_tac >- (
        conj_tac >- (
          fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
          qx_gen_tac`m`>>strip_tac >>
          qpat_assum`∀m. m < LENGTH rd.sm ⇒ Q`(qspec_then`m`mp_tac)>>
          simp[EL_MAP,FAPPLY_FUPDATE_THM] >> fs[MEM_EL] >>
          rw[] >- PROVE_TAC[] >>
          match_mp_tac (MP_CANON(GEN_ALL sv_refv_rel_mono)) >>
          HINT_EXISTS_TAC >> rw[] >>
          match_mp_tac(MP_CANON(GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
          qexists_tac`mk_pp rd (bs with code := bce)` >>
          simp[] >>
          fs[good_rd_def,FEVERY_DEF,UNCURRY,FLOOKUP_DEF] >>
          metis_tac[] ) >>
        REWRITE_TAC[ONE] >>
        simp[REPLICATE] >>
        match_mp_tac(MP_CANON(GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
        qexists_tac`mk_pp rd (bs with code := bce)` >>
        simp[] >>
        fs[good_rd_def,FEVERY_DEF,UNCURRY,FLOOKUP_DEF] >>
        metis_tac[] ) >>
      match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
      HINT_EXISTS_TAC >> simp[] >>
      rpt gen_tac >> match_mp_tac (GEN_ALL optionTheory.OPTREL_MONO) >>
      rpt gen_tac >> strip_tac >>
      match_mp_tac (MP_CANON(GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
      HINT_EXISTS_TAC >> simp[] >>
      fs[good_rd_def,FEVERY_DEF,UNCURRY,FLOOKUP_DEF] >> metis_tac[] ) >>
    simp[SUBMAP_DEF,DRESTRICT_DEF] >>
    rw[] >> rw[] >> fs[IN_FRANGE,DOMSUB_FAPPLY_THM] >> rw[] >> PROVE_TAC[])
  >- (
    simp[Once RTC_CASES1] >> srw_tac[DNF_ss][] >> disj2_tac >>
    simp[bc_eval_stack_def] >>
    simp[Once RTC_CASES1] >> srw_tac[DNF_ss][] >> disj1_tac >>
    Q.PAT_ABBREV_TAC`bs2:bc_state = X Y` >>
    `bc_fetch bs2 = SOME Deref` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac[`bc0 ++ [Stack(PushInt 0)]`,`bc1`] >>
      simp[Abbr`bs2`,FILTER_APPEND,SUM_APPEND]) >>
    Cases_on`v1`>>fs[] >>
    BasicProvers.EVERY_CASE_TAC>>fs[] >>
    fs[Q.SPEC`CLoc n`(CONJUNCT1(SPEC_ALL(Cv_bv_cases)))] >>
    rw[] >>
    simp[bc_eval1_thm,bc_eval1_def,Abbr`bs2`] >>
    `∃v. FLOOKUP bs.refs p = SOME (ValueArray [v]) ∧ Cv_bv (mk_pp rd (bs with code := bce)) a v` by (
      fs[s_refs_def,el_check_def,EVERY_MEM,FLOOKUP_DEF] >>
      first_x_assum(qspec_then`p`mp_tac) >>
      discharge_hyps >- metis_tac[MEM_EL] >> rw[] >>
      fs[LIST_REL_EL_EQN] >>
      rpt(first_x_assum(qspec_then`n`mp_tac)) >>
      simp[sv_refv_rel_cases,EL_MAP] ) >>
    simp[bump_pc_def] >>
    simp[bc_state_component_equality] >>
    qexists_tac`rd.sm` >>
    simp[s_refs_with_stack,s_refs_with_pc,SUM_APPEND,FILTER_APPEND] >>
    fs[] >>
    match_mp_tac s_refs_with_irr >>
    HINT_EXISTS_TAC >> simp[] )
  >- ((* The IsBlock instruction *)
    simp[Once RTC_CASES1] >> srw_tac[DNF_ss][] >> disj1_tac >>
    Cases_on `v1` >> fs [] >>
    rw [] >>
    Cases_on`l`>>fs[Once Cv_bv_cases] >>
    simp[bc_eval_stack_def,bc_state_component_equality] >>
    fs[s_refs_def] >> simp[SUM_APPEND,FILTER_APPEND] >>
    TRY(qexists_tac`rd.sm`) >> simp[] >> fs[good_rd_def])
  >- ((*Length*)
    Cases_on`v1`>>fs[]>>
    qpat_assum`X = Rval v`mp_tac >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    rw[] >>
    fs[Once Cv_bv_cases] >>
    `∃v. FLOOKUP bs.refs p = SOME (ValueArray [v])` by (
      fs[s_refs_def,el_check_def,EVERY_MEM,FLOOKUP_DEF] >>
      first_x_assum(qspec_then`p`mp_tac) >>
      discharge_hyps >- metis_tac[MEM_EL] >> rw[] >>
      fs[LIST_REL_EL_EQN] >>
      rpt(first_x_assum(qspec_then`n`mp_tac)) >>
      simp[sv_refv_rel_cases,EL_MAP] >>
      rw[] >> rw[]) >>
    simp[] >>
    simp[Once RTC_CASES1] >> srw_tac[DNF_ss][] >> disj1_tac >>
    simp[bc_state_component_equality] >>
    qexists_tac`rd.sm` >>
    simp[s_refs_with_stack,FILTER_APPEND,SUM_APPEND] >>
    match_mp_tac s_refs_with_irr >>
    HINT_EXISTS_TAC >> simp[] )
  >- ((*LengthByte*)
    Cases_on`v1`>>fs[]>>
    qpat_assum`X = Rval v`mp_tac >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    rw[] >>
    fs[Once Cv_bv_cases] >>
    `∃v. FLOOKUP bs.refs p = SOME (ByteArray v) ∧ LENGTH v = LENGTH l` by (
      fs[s_refs_def,el_check_def,EVERY_MEM,FLOOKUP_DEF] >>
      first_x_assum(qspec_then`p`mp_tac) >>
      discharge_hyps >- metis_tac[MEM_EL] >> rw[] >>
      fs[LIST_REL_EL_EQN] >>
      rpt(first_x_assum(qspec_then`n`mp_tac)) >>
      simp[sv_refv_rel_cases,EL_MAP]) >>
    simp[] >>
    simp[Once RTC_CASES1] >> srw_tac[DNF_ss][] >> disj1_tac >>
    simp[bc_state_component_equality] >>
    qexists_tac`rd.sm` >>
    simp[s_refs_with_stack,FILTER_APPEND,SUM_APPEND] >>
    match_mp_tac s_refs_with_irr >>
    HINT_EXISTS_TAC >> simp[] )
  >- ((*LengthBlock*)
    Cases_on`v1`>>fs[Cv_bv_cases_conv,Cv_bv_cases_vectorv]>>
    simp[bc_eval_stack_def] >>
    srw_tac[DNF_ss][Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality,FILTER_APPEND,SUM_APPEND] >>
    simp[Cv_bv_cases_lit] >>
    qexists_tac`rd.sm` >> simp[] >>
    imp_res_tac LIST_REL_LENGTH >> simp[] >>
    match_mp_tac s_refs_with_irr >>
    HINT_EXISTS_TAC >> simp[] )
  >- ( (*TagEq*)
    simp[Once RTC_CASES1] >> srw_tac[DNF_ss][] >> disj1_tac >>
    Cases_on`v1`>>fs[]>>rw[]>>
    fs[Q.SPEC`CConv X Y`(CONJUNCT1(SPEC_ALL(Cv_bv_cases)))] >>
    rw[bc_eval_stack_def] >> simp[bc_state_component_equality] >>
    simp[Once Cv_bv_cases] >>
    simp[FILTER_APPEND,SUM_APPEND] >>
    qexists_tac`rd.sm`>>simp[] >>
    fs[s_refs_def,good_rd_def] >>
    AP_TERM_TAC >> metis_tac[] )
  >- ( (*Proj*)
    simp[Once RTC_CASES1] >> srw_tac[DNF_ss][] >> disj1_tac >>
    Cases_on`v1`>>fs[]>>rw[]>>
    fs[Q.SPEC`CConv X Y`(CONJUNCT1(SPEC_ALL(Cv_bv_cases)))] >>
    rw[bc_eval_stack_def] >> simp[bc_state_component_equality] >>
    fs[el_check_def] >> BasicProvers.EVERY_CASE_TAC >> fs[] >>
    rfs[EVERY2_EVERY,EVERY_MEM] >> fs[MEM_ZIP,PULL_EXISTS] >> rw[] >>
    simp[FILTER_APPEND,SUM_APPEND] >>
    qexists_tac`rd.sm`>>simp[] >>
    fs[s_refs_def,good_rd_def] )
  >- ( (*Gupdate*)
    BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[] >>
    simp[Once RTC_CASES1] >> srw_tac[DNF_ss][] >> disj2_tac >>
    Q.PAT_ABBREV_TAC`bs2:bc_state = X Y` >>
    `bc_fetch bs2 = SOME (Stack (Cons unit_tag 0))` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac[`bc0 ++ [Gupdate n]`,`bc1`] >>
      simp[Abbr`bs2`,FILTER_APPEND,SUM_APPEND]) >>
    simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def] >>
    simp[Once RTC_CASES1] >> srw_tac[DNF_ss][] >> disj1_tac >>
    simp[bc_state_component_equality,Abbr`bs2`] >>
    simp[SUM_APPEND,FILTER_APPEND] >>
    simp[Once Cv_bv_cases] >>
    qexists_tac`rd.sm` >>
    fs[s_refs_def,good_rd_def] >>
    rfs[EVERY2_EVERY,EVERY_MEM] >>
    fs[MEM_ZIP,PULL_EXISTS] >>
    simp[gvrel_def,EL_LUPDATE] >> rw[] >>
    rw[optionTheory.OPTREL_def] >>
    fs[optionTheory.OPTREL_def] >>
    metis_tac[optionTheory.NOT_SOME_NONE]))

(* compile_closures *)

val FOLDL_emit_ceref_thm = store_thm("FOLDL_emit_ceref_thm",
  ``∀ls z sz s.
      let (z',s') = FOLDL (emit_ceref z) (sz,s) ls in
      ∃code.
      (z' = sz + LENGTH ls) ∧
      (s'.out = REVERSE code ++ s.out) ∧
      EVERY ($~ o is_Label) code ∧ code_labels_ok code ∧ (s'.next_label = s.next_label) ∧
      ∀bs bc0 bc1 fs st.
        (bs.code = bc0 ++ code ++ bc1) ∧ (bs.pc = next_addr bs.inst_length bc0) ∧
        z ≤ sz ∧ EVERY (λn. sz-z+n < LENGTH bs.stack) ls
        ⇒
        bc_next^* bs (bs with <| stack := REVERSE (MAP (λn. EL ((sz-z)+n) bs.stack) ls) ++ bs.stack
                               ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  Induct >- (
    rw[Once SWAP_REVERSE,LET_THM] >>
    rpt (first_x_assum (mp_tac o SYM)) >> rw[]) >>
  qx_gen_tac`e` >> rw[] >>
  qmatch_assum_abbrev_tac`FOLDL (emit_ceref z) (sz + 1, s1) ls = X` >>
  first_x_assum(qspecl_then[`z`,`sz+1`,`s1`]mp_tac) >>
  simp[Abbr`X`,Abbr`s1`] >>
  disch_then(Q.X_CHOOSE_THEN`bc`strip_assume_tac) >> rw[] >>
  simp[Once SWAP_REVERSE] >>
  conj_tac >- (
    match_mp_tac code_labels_ok_cons >> simp[] ) >>
  rw[] >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs = SOME(Stack(Load(sz-z+e)))` by (
    match_mp_tac bc_fetch_next_addr>>
    map_every qexists_tac[`bc0`,`bc++bc1`]>>
    simp[])>>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,bump_pc_def]>>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  first_x_assum(qspecl_then[`bs1`,`bc0++[Stack(Load(sz-z+e))]`,`bc1`]mp_tac)>>
  simp[Abbr`bs1`]>>
  discharge_hyps >- (
    simp[ADD1,SUM_APPEND,FILTER_APPEND] >>
    fsrw_tac[ARITH_ss][EVERY_MEM] >>
    rw[] >> res_tac >> DECIDE_TAC ) >>
  rw[] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qmatch_assum_abbrev_tac`bc_next^* bs1' bs2'` >>
  `bs1' = bs1` by simp[bc_state_component_equality,Abbr`bs1'`,Abbr`bs1`,FILTER_APPEND,SUM_APPEND]>>
  `bs2' = bs2` by (
    simp[bc_state_component_equality,Abbr`bs2'`,Abbr`bs2`,Abbr`bs1`,FILTER_APPEND,SUM_APPEND,MAP_EQ_f] >>
    lrw[EL_CONS,PRE_SUB1] ) >>
  rw[])

val FOLDL_emit_ceenv_thm = store_thm("FOLDL_emit_ceenv_thm",
  ``∀ec env0 z s.
     let (z',s') = FOLDL (emit_ceenv env0) (z,s) ec in
     ∃code.
     (s'.out = REVERSE code ++ s.out) ∧
     EVERY ($~ o is_Label) code ∧ code_labels_ok code ∧ (s'.next_label = s.next_label) ∧
     ∀bs bc0 bc1 cls j.
       (bs.code = bc0 ++ code ++ bc1) ∧
       (bs.pc = next_addr bs.inst_length bc0) ∧
       EVERY (λn. n < LENGTH env0) ec ∧ j ≤ z ∧ j ≤ LENGTH bs.stack ∧
       EVERY (λn. IS_SOME (lookup_ct (z-j) (DROP j bs.stack) (DRESTRICT bs.refs cls) bs.globals (EL n env0))) ec
       ⇒
       bc_next^* bs (bs with <|
         stack := (REVERSE (MAP (λn. THE (lookup_ct (z-j) (DROP j bs.stack) (DRESTRICT bs.refs cls) bs.globals (EL n env0))) ec))++bs.stack
       ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  Induct >- (
    rw[Once SWAP_REVERSE,LET_THM] >>
    rpt (first_x_assum (mp_tac o SYM)) >> rw[]) >>
  qx_gen_tac`e` >> rw[] >>
  qmatch_assum_abbrev_tac`FOLDL (emit_ceenv env0) (z + 1, s1) ec = X` >>
  first_x_assum(qspecl_then[`env0`,`z+1`,`s1`]mp_tac) >>
  simp[Abbr`X`,Abbr`s1`] >>
  disch_then(Q.X_CHOOSE_THEN`bc`strip_assume_tac) >> rw[] >>
  Q.PAT_ABBREV_TAC`ell:ctbind = X` >>
  qspecl_then[`z`,`s`,`ell`]mp_tac compile_varref_append_out >>
  disch_then(Q.X_CHOOSE_THEN`bcv`strip_assume_tac) >> rw[] >>
  simp[Once SWAP_REVERSE] >>
  simp[EVERY_REVERSE] >>
  conj_tac >- (
    match_mp_tac code_labels_ok_append >> simp[] ) >> rw[] >>
  `ell = EL e env0` by (
    simp[Abbr`ell`,el_check_def] ) >> rw[] >>
  Cases_on`lookup_ct (z-j) (DROP j bs.stack) (DRESTRICT bs.refs cls) bs.globals (EL e env0)`>>fs[] >>
  `lookup_ct z bs.stack (DRESTRICT bs.refs cls) bs.globals (EL e env0) = SOME x` by (
    match_mp_tac lookup_ct_imp_incsz_many >>
    map_every qexists_tac[`z-j`,`DROP j bs.stack`,`TAKE j bs.stack`] >>
    simp[LENGTH_TAKE] ) >>
  qspecl_then[`bs`,`bc0`,`REVERSE bcv`,`bc++bc1`,`cls`,`z`,`s`,`EL e env0`,`x`]mp_tac compile_varref_thm >>
  simp[] >> strip_tac >>
  match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
  HINT_EXISTS_TAC >> simp[] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  first_x_assum(qspecl_then[`bs1`,`bc0++REVERSE bcv`,`bc1`,`cls`,`j+1`]mp_tac) >>
  discharge_hyps >- ( simp[Abbr`bs1`] ) >>
  rw[] >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2'` >>
  `bs2' = bs2` by (
    rw[Abbr`bs2'`,Abbr`bs2`,Abbr`bs1`] >>
    simp[bc_state_component_equality,MAP_EQ_f] ) >>
  fs[])

val cons_closure_thm = store_thm("cons_closure_thm",
  ``∀env0 sz nk s k refs envs.
      let (s',k') = cons_closure env0 sz nk (s,k) (refs,envs) in
      ∃code.
      (s'.out = REVERSE code ++ s.out) ∧
      EVERY ($~ o is_Label) code ∧ code_labels_ok code ∧ (s'.next_label = s.next_label) ∧
      (k' = k + 1) ∧
      ∀bs bc0 bc1 cls.
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        k < LENGTH bs.stack ∧ nk + nk ≤ LENGTH bs.stack ∧
        EVERY (λn. nk + n < LENGTH bs.stack) refs ∧
        EVERY (λn. n < LENGTH env0) envs ∧
        EVERY (λn. IS_SOME (lookup_ct sz (DROP (nk+nk) bs.stack) (DRESTRICT bs.refs cls) bs.globals (EL n env0))) envs
        ⇒
        bc_next^* bs (bs with <| stack :=
          LUPDATE
          (Block closure_tag
            [EL k bs.stack;
             Block 0 (MAP (λn. EL (nk+n) bs.stack) refs ++
                      MAP (λn. THE (lookup_ct sz (DROP (nk+nk) bs.stack) (DRESTRICT bs.refs cls) bs.globals (EL n env0))) envs)])
          k bs.stack
                               ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  simp[cons_closure_def,UNCURRY] >> rpt gen_tac >>
  Q.PAT_ABBREV_TAC`s0 = s with out := X` >>
  qspecl_then[`refs`,`nk+sz`,`2 * nk + (sz + 1)`,`s0`]mp_tac FOLDL_emit_ceref_thm >>
  simp[UNCURRY] >>
  disch_then(Q.X_CHOOSE_THEN`bc`strip_assume_tac) >>
  Q.PAT_ABBREV_TAC`s1 = FOLDL (emit_ceref Y) X refs` >>
  PairCases_on`s1` >> pop_assum (assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >>
  Q.PAT_ABBREV_TAC`s2 = FOLDL (emit_ceenv X) Y envs` >>
  PairCases_on`s2` >> pop_assum (assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >>
  qspecl_then[`envs`,`env0`,`s10`,`s11`]mp_tac FOLDL_emit_ceenv_thm >>
  simp[UNCURRY] >>
  disch_then(Q.X_CHOOSE_THEN`bc1`strip_assume_tac) >>
  fs[Abbr`s0`,Once SWAP_REVERSE] >>
  conj_tac >- (
    match_mp_tac code_labels_ok_cons >> simp[] >>
    match_mp_tac code_labels_ok_append >> simp[] >>
    conj_tac >- (
      match_mp_tac code_labels_ok_append >> simp[] ) >>
    match_mp_tac code_labels_ok_cons >> simp[] >>
    match_mp_tac code_labels_ok_cons >> simp[] >>
    match_mp_tac code_labels_ok_cons >> simp[] ) >>
  rpt (qpat_assum `X = Y.next_label` kall_tac) >>
  rpt(qpat_assum`X.out = Y`kall_tac) >>
  rpt gen_tac >> strip_tac >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs = SOME (Stack (Load k))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0`>>rw[] ) >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def] >>
  simp[bump_pc_def] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  last_x_assum(qspecl_then[`bs1`,`bc0 ++ [Stack (Load k)]`]mp_tac) >>
  simp[Abbr`bs1`] >>
  discharge_hyps >- (
    simp[SUM_APPEND,FILTER_APPEND,ADD1] >>
    fsrw_tac[ARITH_ss][EVERY_MEM] >>
    rw[] >> res_tac >> DECIDE_TAC ) >>
  simp_tac (srw_ss()) [FILTER_APPEND,SUM_APPEND,ADD1] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs3` >>
  qsuff_tac`bc_next^* bs3 bs2` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
  qpat_assum`bc_next^* bs1 bs3` kall_tac >>
  qunabbrev_tac`bs1` >>
  qpat_assum`bc_fetch bs = X`kall_tac >>
  match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
  qpat_assum`bs.code = X` mp_tac >>
  Q.PAT_ABBREV_TAC`bc2:bc_inst list = [x;y;z]` >> strip_tac >>
  first_x_assum(qspecl_then[`bs3`,`bc0 ++ [Stack (Load k)] ++ bc`,`bc2 ++ bc1'`,`cls`,`LENGTH refs + 1 + 2 * nk`]mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`bs3`,SUM_APPEND,FILTER_APPEND] >>
    fs[EVERY_MEM] >> simp[DROP_APPEND2] ) >>
  strip_tac >> HINT_EXISTS_TAC >> simp[] >>
  pop_assum kall_tac >>
  qpat_assum`bs.code = X`mp_tac >>
  qunabbrev_tac`bc2` >>
  Q.PAT_ABBREV_TAC`x = Cons 0 j` >>
  strip_tac >>
  simp[Abbr`bs3`] >>
  qmatch_abbrev_tac`bc_next^* bs3 bs2` >>
  `bc_fetch bs3 = SOME (Stack x)` by (
    match_mp_tac bc_fetch_next_addr >>
    rw[Abbr`bs3`] >>
    qexists_tac`bc0 ++ [Stack (Load k)] ++ bc ++ bc1` >>
    lrw[SUM_APPEND,FILTER_APPEND] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp_tac(srw_ss()++DNF_ss)[] >>
  qpat_assum`Abbrev (bs3 = X)`mp_tac >>
  Q.PAT_ABBREV_TAC`evs:bc_value list = (REVERSE (MAP X envs)) ++ Y` >>
  strip_tac >>
  qabbrev_tac`env = Block 0 (REVERSE evs)` >>
  qexists_tac`env::EL k bs.stack::bs.stack` >>
  conj_tac >- (
    simp[Abbr`x`,bc_eval_stack_def,Abbr`bs3`,ADD1] >>
    conj_tac >- simp[Abbr`evs`] >>
    `LENGTH envs + LENGTH refs = LENGTH evs` by simp[Abbr`evs`] >>
    pop_assum SUBST1_TAC >>
    REWRITE_TAC[Once CONS_APPEND] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    REWRITE_TAC[DROP_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
    simp[Abbr`env`] ) >>
  rw[bump_pc_def,Abbr`bs3`] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qmatch_abbrev_tac`bc_next^* bs3 bs2` >>
  `bc_fetch bs3 = SOME (Stack (Cons 3 2))` by (
    match_mp_tac bc_fetch_next_addr >>
    rw[Abbr`bs3`] >>
    Q.PAT_ABBREV_TAC`ls = X ++ bc` >>
    qexists_tac`ls ++ bc1 ++ [Stack x]` >>
    lrw[SUM_APPEND,FILTER_APPEND,ADD1,Abbr`ls`] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,Abbr`bs3`,bump_pc_def] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  qmatch_abbrev_tac`bc_next^* bs3 bs2` >>
  `bc_fetch bs3 = SOME (Stack (Store k))` by (
    match_mp_tac bc_fetch_next_addr >>
    rw[Abbr`bs3`] >>
    Q.PAT_ABBREV_TAC`ls = X ++ bc` >>
    qexists_tac`ls ++ bc1 ++ [Stack x; Stack (Cons 3 2)]` >>
    lrw[SUM_APPEND,FILTER_APPEND,ADD1,Abbr`ls`] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[bc_eval_stack_def,Abbr`bs3`,bump_pc_def] >>
  qpat_assum`bc_fetch X = Y`kall_tac >>
  simp[Once RTC_CASES1] >> disj1_tac >>
  simp[Abbr`bs2`,bc_state_component_equality] >>
  simp[FILTER_APPEND,SUM_APPEND] >>
  simp[LIST_EQ_REWRITE] >>
  qx_gen_tac`z` >> strip_tac >>
  simp[EL_LUPDATE] >>
  rw[] >- (
    lrw[EL_APPEND1,EL_APPEND2,Abbr`env`,Abbr`evs`] >>
    qmatch_abbrev_tac`a++b=c++d` >>
    `a = c` by (
      lrw[Abbr`a`,Abbr`c`,MAP_EQ_f,EL_CONS,PRE_SUB1] ) >>
    simp[Abbr`a`,Abbr`c`,Abbr`d`,Abbr`b`] >>
    lrw[MAP_EQ_f,DROP_APPEND1,DROP_APPEND2] ) >>
  Cases_on`z < k`>> lrw[EL_APPEND1,EL_APPEND2,EL_TAKE,EL_DROP] )

val num_fold_make_ref_thm = store_thm("num_fold_make_ref_thm",
  ``∀x nz s.
    let s' = num_fold (λs. s with out := Ref::Stack (PushInt 1)::Stack (PushInt x)::s.out) s nz in
    ∃code.
    (s'.out = REVERSE code ++ s.out) ∧
    EVERY ($~ o is_Label) code ∧
    code_labels_ok code ∧
    (s'.next_label = s.next_label) ∧
    ∀bs bc0 bc1.
    (bs.code = bc0 ++ code ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0)
    ⇒
    ∃ps.
    (LENGTH ps = nz)∧
    ALL_DISTINCT ps ∧
    (∀p. p ∈ set ps ⇒ p ∉ FDOM bs.refs) ∧
    bc_next^* bs
    (bs with <| stack := MAP RefPtr ps ++ bs.stack
              ; refs := bs.refs |++ REVERSE (MAP (λp. (p,ValueArray [Number x])) ps)
              ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  gen_tac >> Induct >- (
    rw[Once num_fold_def,Once SWAP_REVERSE] >> rw[] >>
    qexists_tac`[]` >> rw[FUPDATE_LIST_THM] >>
    rpt (pop_assum (mp_tac o SYM)) >> rw[] ) >>
  simp[Once num_fold_def] >> gen_tac >>
  Q.PAT_ABBREV_TAC`s' = s with out := X` >>
  first_x_assum(qspec_then`s'`mp_tac) >>
  simp[] >> rw[] >>
  fs[Abbr`s'`,Once SWAP_REVERSE] >>
  conj_tac >- (
    rpt(match_mp_tac code_labels_ok_cons >> simp[]) ) >>
  rw[] >>
  simp[Once RTC_CASES1] >>
  fsrw_tac[DNF_ss][] >> disj2_tac >>
  `bc_fetch bs = SOME (Stack (PushInt x))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0`>>rw[] ) >>
  rw[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def] >>
  simp[Once RTC_CASES1] >>
  fsrw_tac[DNF_ss][] >> disj2_tac >>
  REWRITE_TAC[CONJ_ASSOC] >>
  qho_match_abbrev_tac`∃ps u. (P0 ps ∧ bc_next bs1 u) ∧ P ps u` >>
  `bc_fetch bs1 = SOME (Stack (PushInt 1))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++[Stack (PushInt x)]`>>rw[Abbr`bs1`] >>
    simp[SUM_APPEND,FILTER_APPEND]) >>
  rw[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def,Abbr`bs1`,LET_THM,Abbr`P`] >>
  qho_match_abbrev_tac`∃ps. P0 ps ∧ bc_next^* bs1 (bs2 ps)` >>
  `bc_fetch bs1 = SOME Ref` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++[Stack (PushInt x);Stack (PushInt 1)]`>>rw[Abbr`bs1`] >>
    simp[SUM_APPEND,FILTER_APPEND]) >>
  srw_tac[DNF_ss][Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def,Abbr`bs1`,LET_THM] >>
  qho_match_abbrev_tac`∃ps. P0 ps ∧ bc_next^* bs1 (bs2 ps)` >>
  first_x_assum(qspecl_then[`bs1`,`bc0 ++ [Stack (PushInt x);Stack (PushInt 1);Ref]`,`bc1`]mp_tac) >>
  simp[Abbr`bs1`,SUM_APPEND,FILTER_APPEND] >>
  disch_then(Q.X_CHOOSE_THEN`ps`strip_assume_tac) >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs3` >>
  qabbrev_tac`pps = ps ++ [LEAST n. n ∉ FDOM bs.refs]` >>
  qexists_tac`pps` >>
  `bs3 = bs2 pps` by (
    simp[Abbr`bs3`,Abbr`bs2`,bc_state_component_equality,FILTER_APPEND,SUM_APPEND,Abbr`pps`] >>
    simp[REVERSE_APPEND,FUPDATE_LIST_THM] >>
    REWRITE_TAC[ONE] >> simp[REPLICATE]) >>
  fs[Abbr`P0`] >>
  simp[Abbr`pps`,ALL_DISTINCT_APPEND] >> rw[] >> fs[] >>
  numLib.LEAST_ELIM_TAC >> simp[] >>
  metis_tac[NOT_IN_FINITE,FDOM_FINITE,INFINITE_NUM_UNIV])

val FOLDL_push_lab_thm = store_thm("FOLDL_push_lab_thm",
 ``∀(defs:def list) s ls s' ls'.
   (FOLDL push_lab (s,ls) defs = (s',ls'))
   ⇒
   ∃code.
   (s'.out = REVERSE code ++ s.out) ∧
   EVERY ($~ o is_Label) code ∧
   (s'.next_label = s.next_label) ∧
   (∀l. uses_label code l ⇒ MEM l (MAP (FST o THE o FST) defs)) ∧
   ∀bs bc0 bc1.
     (bs.code = bc0 ++ code ++ bc1) ∧
     (bs.pc = next_addr bs.inst_length bc0) ∧
     EVERY (IS_SOME o FST) defs ∧
     EVERY (IS_SOME o bc_find_loc bs o Lab o FST o THE o FST) defs
     ⇒
     (ls' = (REVERSE (MAP (SND o SND o THE o FST) defs)) ++ ls) ∧
     bc_next^* bs (bs with <| stack :=  (REVERSE (MAP (CodePtr o THE o bc_find_loc bs o Lab o FST o THE o FST) defs))++bs.stack
                            ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  Induct >- (
    rw[Once SWAP_REVERSE] >>
    pop_assum(assume_tac o SYM) >> fs[] ) >>
  qx_gen_tac`def` >>
  PairCases_on`def` >>
  Cases_on`def0`>> TRY(PairCases_on`x`)>>rw[push_lab_def] >- (
    fs[] >> res_tac >> fs[] ) >>
  qmatch_assum_abbrev_tac`FOLDL push_lab (ss,lss) defs = (s',ls')` >>
  first_x_assum(qspecl_then[`ss`,`lss`,`s'`,`ls'`]mp_tac) >> simp[] >>
  strip_tac >> fs[Abbr`ss`,Once SWAP_REVERSE,Abbr`lss`] >>
  conj_tac >- ( rw[] >> fs[uses_label_thm] ) >>
  rpt gen_tac >> strip_tac >>
  `bc_fetch bs = SOME (PushPtr (Lab x0))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0`>>rw[] ) >>
  simp[Once RTC_CASES1] >>
  simp_tac (srw_ss()++DNF_ss)[] >> disj2_tac >>
  rw[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
  Cases_on`bc_find_loc bs (Lab x0)`>>fs[] >>
  simp[CONJ_ASSOC] >>
  qmatch_abbrev_tac`P ∧ bc_next^* bs1 bs2` >>
  first_x_assum(qspecl_then[`bs1`,`bc0 ++ [PushPtr (Lab x0)]`,`bc1`]mp_tac) >>
  discharge_hyps >- (
    unabbrev_all_tac >>
    simp[FILTER_APPEND,SUM_APPEND,ADD1] >>
    rfs[EVERY_MEM,bc_find_loc_def] ) >>
  simp[Abbr`P`] >> strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2'` >>
  `bs2' = bs2` by (
    unabbrev_all_tac >>
    srw_tac[ARITH_ss][bc_state_component_equality,MAP_EQ_f,bc_find_loc_def,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
  rw[])

val FOLDL_cons_closure_thm = store_thm("FOLDL_cons_closure_thm",
  ``∀ecs env0 sz nk s k.
    let (s',k') = FOLDL (cons_closure env0 sz nk) (s,k) ecs in
    ∃code.
    (s'.out = REVERSE code ++ s.out) ∧
    EVERY ($~ o is_Label) code ∧ code_labels_ok code ∧ (s'.next_label = s.next_label) ∧
    (k' = k + LENGTH ecs) ∧
    ∀bs bc0 bc1 cls.
    (bs.code = bc0 ++ code ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (LENGTH ecs = nk - k) ∧ k ≤ nk ∧ nk + nk ≤ LENGTH bs.stack ∧
    EVERY (λ(recs,envs).
      EVERY (λn. n < LENGTH env0) envs ∧
      EVERY (λn. IS_SOME (lookup_ct sz (DROP (nk + nk) bs.stack) (DRESTRICT bs.refs cls) bs.globals (EL n env0))) envs ∧
      EVERY (λn. nk + n < LENGTH bs.stack) recs) ecs
    ⇒
    let bvs = MAP2 (λp (recs,envs). Block closure_tag [p;
        Block 0
          (MAP (λn. EL (nk + n) bs.stack) recs ++
           MAP (λn. THE (lookup_ct sz (DROP (nk + nk) bs.stack) (DRESTRICT bs.refs cls) bs.globals (EL n env0))) envs)])
              (TAKE (nk-k) (DROP k bs.stack)) ecs in
    bc_next^* bs
    (bs with <| stack := TAKE k bs.stack ++ bvs ++ (DROP nk bs.stack)
              ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  Induct >- (
    simp[Once SWAP_REVERSE,LENGTH_NIL_SYM,LENGTH_NIL] >> rw[] >>
    rpt (first_x_assum (mp_tac o SYM)) >> simp[] >>
    `k = nk` by fsrw_tac[ARITH_ss][] >> simp[]) >>
  qx_gen_tac`e` >> PairCases_on`e` >>
  fs[LET_THM,UNCURRY] >>
  rpt gen_tac >>
  qspecl_then[`env0`,`sz`,`nk`,`s`,`k`,`e0`,`e1`]mp_tac cons_closure_thm >>
  simp[UNCURRY] >>
  disch_then(Q.X_CHOOSE_THEN`bc`strip_assume_tac) >> simp[] >>
  qmatch_assum_abbrev_tac`(FST p).out = REVERSE bc ++ s.out` >>
  first_x_assum(qspecl_then[`env0`,`sz`,`nk`,`FST p`,`SND p`]mp_tac) >>
  disch_then(Q.X_CHOOSE_THEN`bcf`strip_assume_tac) >>
  PairCases_on`p`>>fs[Once SWAP_REVERSE,ADD1] >> simp[] >>
  conj_tac >- (
    match_mp_tac code_labels_ok_append >> simp[] ) >>
  rpt gen_tac >> strip_tac >>
  last_x_assum(qspecl_then[`bs`,`bc0`,`bcf ++ bc1`,`cls`]mp_tac) >>
  simp[] >>
  rw[] >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
  qexists_tac`bs1` >> simp[] >>
  qpat_assum`Abbrev(bs1 = X)`mp_tac >>
  Q.PAT_ABBREV_TAC`f1 = Block 3 Y` >> strip_tac >>
  first_x_assum(qspecl_then[`bs1`,`bc0 ++ bc`,`bc1`,`cls`]mp_tac) >>
  `DROP (2 * nk) (LUPDATE f1 k bs.stack) = DROP (2 * nk) bs.stack` by (
    lrw[LIST_EQ_REWRITE,EL_DROP,EL_LUPDATE] ) >>
  discharge_hyps >- ( simp[Abbr`bs1`] ) >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2' ⇒ bc_next^* bs1 bs2` >>
  qsuff_tac`bs2' = bs2`>-rw[] >>
  simp[Abbr`bs2'`,Abbr`bs2`,bc_state_component_equality,Abbr`bs1`,MAP2_MAP] >>
  simp[LIST_EQ_REWRITE] >>
  qx_gen_tac`z` >> strip_tac >>
  Cases_on`z<k`>>lrw[EL_APPEND1,EL_TAKE,EL_LUPDATE] >>
  `TAKE (nk-k) (DROP k bs.stack) = EL k bs.stack::(TAKE(nk-k-1) (DROP (k+1) bs.stack))` by (
    lrw[LIST_EQ_REWRITE,EL_TAKE,EL_DROP] >>
    Cases_on`x=0`>>lrw[EL_CONS,PRE_SUB1,EL_TAKE,EL_DROP] ) >>
  simp[] >>
  Cases_on`z=k`>>lrw[EL_APPEND1,EL_APPEND2,EL_TAKE,EL_LUPDATE] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  lrw[EL_APPEND2,EL_CONS,PRE_SUB1] >>
  `DROP nk (LUPDATE f1 k bs.stack) = DROP nk bs.stack` by (
    lrw[LIST_EQ_REWRITE,EL_DROP,EL_LUPDATE] ) >>
  `DROP (k+1) (LUPDATE f1 k bs.stack) = DROP (k+1) bs.stack` by (
    lrw[LIST_EQ_REWRITE,EL_DROP,EL_LUPDATE] ) >>
  simp[])

val num_fold_update_refptr_thm = store_thm("num_fold_update_refptr_thm",
  ``∀nz nk s k.
    let (s',k') = num_fold (update_refptr nk) (s,k) nz in
    ∃code.
    (s'.out = REVERSE code ++ s.out) ∧
    EVERY ($~ o is_Label) code ∧
    code_labels_ok code ∧
    (s'.next_label = s.next_label) ∧
    (k' = k + nz) ∧
    ∀bs bc0 bc1 vs rs st.
    (bs.code = bc0 ++ code ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (bs.stack = vs ++ (MAP RefPtr rs) ++ st) ∧
    (∀r. MEM r rs ⇒ ∃v. FLOOKUP bs.refs r = SOME (ValueArray [v])) ∧ ALL_DISTINCT rs ∧
    (LENGTH rs = nk) ∧ (LENGTH vs = nk) ∧
    (k + nz = nk)
    ⇒
    bc_next^* bs
    (bs with <| refs := bs.refs |++ ZIP (DROP k rs,MAP (λv. ValueArray [v]) (DROP k vs))
              ; pc := next_addr bs.inst_length (bc0 ++ code)|>)``,
  Induct >- (
    rw[Once num_fold_def,Once SWAP_REVERSE,LENGTH_NIL,FUPDATE_LIST_THM] >>
    rw[] >> fsrw_tac[ARITH_ss][FUPDATE_LIST_THM] >>
    metis_tac[DROP_LENGTH_NIL,ZIP,FUPDATE_LIST_THM,with_same_pc,with_same_refs,RTC_CASES1,MAP2,MAP]) >>
  rw[Once num_fold_def,update_refptr_def] >>
  first_x_assum(qspecl_then[`nk`,`s'''`,`k+1`]mp_tac) >>
  simp[] >> unabbrev_all_tac >> simp[] >>
  disch_then strip_assume_tac >>
  simp[Once SWAP_REVERSE] >>
  conj_tac >- (
    rpt(match_mp_tac code_labels_ok_cons >> simp[]) ) >>
  ntac 3 strip_tac >>
  map_every qx_gen_tac[`vvs`,`rrs`] >> rpt strip_tac >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ ls ++ code ++ bc1` >>
  qpat_assum`X = (s'''',k')`kall_tac >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  qmatch_assum_abbrev_tac`Abbrev (ls = [x1;x2;x3;x4])` >>
  `bc_fetch bs = SOME x1` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0`>>rw[Abbr`x1`,Abbr`ls`] ) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`x1`,bc_eval_stack_def,ADD1] >>
  fsrw_tac[ARITH_ss][ADD1] >>
  simp[bump_pc_def,EL_CONS,EL_APPEND1,PRE_SUB1,EL_APPEND2] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs1 = SOME x2` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0 ++ [HD ls]` >>
    lrw[Abbr`bs1`,Abbr`ls`,Abbr`x2`,SUM_APPEND,FILTER_APPEND] ) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`x2`,bc_eval_stack_def] >>
  simp[Abbr`bs1`,bump_pc_def] >>
  lrw[EL_CONS,PRE_SUB1,EL_APPEND1] >>
  rpt (qpat_assum `bc_fetch X = Y` kall_tac) >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs1 = SOME x3` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0 ++ [HD ls; HD(TL ls)]` >>
    lrw[Abbr`bs1`,Abbr`ls`,Abbr`x3`,SUM_APPEND,FILTER_APPEND] ) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`x3`,bc_eval_stack_def,Abbr`bs1`,bump_pc_def] >>
  fsrw_tac[DNF_ss,ARITH_ss][] >>
  qpat_assum `bc_fetch X = Y` kall_tac >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs1 = SOME x4` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0 ++ FRONT ls` >>
    lrw[Abbr`bs1`,Abbr`ls`,Abbr`x4`,SUM_APPEND,FILTER_APPEND] ) >>
  simp[bc_eval1_thm,bc_eval1_def,Abbr`x4`,Abbr`bs1`] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[EL_MAP] >>
  first_assum(qspec_then`EL k rrs`mp_tac) >>
  discharge_hyps >- (
    simp[MEM_EL] >>
    qexists_tac`k`>>simp[]) >>
  strip_tac >> simp[] >>
  simp[bump_pc_def] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  first_x_assum(qspecl_then[`bs1`,`bc0 ++ ls`,`bc1`,`vvs`,`rrs`,`st`]mp_tac) >>
  simp[Abbr`bs1`,Abbr`ls`,FILTER_APPEND,SUM_APPEND,ADD1] >>
  discharge_hyps >- (
    simp[FLOOKUP_UPDATE] >> rw[] >>
    simp[LUPDATE_def] ) >>
  qmatch_abbrev_tac`bc_next^* bs3 bs4 ⇒ bc_next^* bs3 bs2` >>
  qsuff_tac `bs4 = bs2` >- rw[] >>
  unabbrev_all_tac >>
  simp[bc_state_component_equality,FILTER_APPEND,SUM_APPEND] >>
  `DROP k rrs = EL k rrs :: DROP (k + 1) rrs` by (
     simp[GSYM ADD1,DROP_CONS_EL] ) >>
  `DROP k vvs = EL k vvs :: DROP (k + 1) vvs` by (
     simp[GSYM ADD1,DROP_CONS_EL] ) >>
  simp[FUPDATE_LIST_THM,LUPDATE_def,EL_CONS,PRE_SUB1,EL_APPEND1])

val num_fold_store_thm = store_thm("num_fold_store_thm",
  ``∀nz k s. let s' = num_fold (λs. s with out := Stack (Store k)::s.out) s nz in
    ∃code.
      (s'.out = REVERSE code ++ s.out) ∧
      (s'.next_label = s.next_label) ∧
      EVERY ($~ o is_Label) code ∧
      code_labels_ok code ∧
      ∀bs bc0 bc1 vs ws st.
      (bs.code = bc0 ++ code ++ bc1) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      (bs.stack = vs ++ ws ++ st) ∧
      (LENGTH vs -1 = k) ∧ nz ≤ LENGTH vs ∧ nz ≤ LENGTH ws
      ⇒
      bc_next^* bs
      (bs with <| stack := (DROP nz vs) ++ (TAKE nz vs) ++ (DROP nz ws) ++ st
                ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  Induct >- (
    rw[Once num_fold_def,Once SWAP_REVERSE] >>
    lrw[] >>
    metis_tac[RTC_CASES1,with_same_stack,with_same_pc] ) >>
  simp[Once num_fold_def] >> rw[] >>
  Q.PAT_ABBREV_TAC`s' = s with out := Y` >>
  first_x_assum(qspecl_then[`k`,`s'`]mp_tac) >>
  simp[] >>
  disch_then strip_assume_tac >>
  simp[Abbr`s'`,Once SWAP_REVERSE] >>
  conj_tac >- (
    match_mp_tac code_labels_ok_cons >> simp[] ) >>
  rpt strip_tac >>
  Cases_on`vs=[]` >- (
    fsrw_tac[ARITH_ss][ADD1] ) >>
  `bc_fetch bs = SOME (Stack (Store k))`  by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >> rw[] ) >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm,bc_eval1_def] >>
  Cases_on`vs`>>fs[] >>
  simp[bc_eval_stack_def,bump_pc_def,ADD1] >>
  lrw[TAKE_APPEND1,DROP_APPEND1,DROP_APPEND2,ADD1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  fsrw_tac[ARITH_ss][ADD1] >>
  qmatch_assum_rename_tac`bs.stack = (v::(vs ++ ws ++ st))`[] >>
  rfs[] >>
  first_x_assum(qspecl_then[`bs1`,`bc0++[Stack (Store (LENGTH vs))]`,`bc1`,`vs++[v]`,`(DROP 1 ws)`,`st`]mp_tac) >>
  simp[Abbr`bs1`,SUM_APPEND,FILTER_APPEND] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs4 ⇒ bc_next^* bs1 bs2` >>
  `bs4 = bs2` by (
    unabbrev_all_tac >>
    simp[bc_state_component_equality,SUM_APPEND,FILTER_APPEND] >>
    lrw[TAKE_TAKE,TAKE_APPEND1,DROP_DROP,DROP_APPEND1] ) >>
  rw[])

val compile_closures_thm = store_thm("compile_closures_thm",
  ``∀env sz s (defs:def list).
    let s' = compile_closures env sz s defs in
    ∃code.
      (s'.out = REVERSE code ++ s.out) ∧
      EVERY ($~ o is_Label) code ∧ (s'.next_label = s.next_label) ∧
      (∀l. uses_label code l ⇒ MEM (Label l) code ∨ MEM l (MAP (FST o THE o FST) defs)) ∧
      ∀bs bc0 bc1 cls.
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        EVERY (IS_SOME o FST) defs ∧
        EVERY (IS_SOME o bc_find_loc bs o Lab o FST o THE o FST) defs ∧
        EVERY ((λ(recs,envs).
          EVERY (λn. n < LENGTH env) envs ∧
          EVERY (λn. IS_SOME (lookup_ct sz bs.stack (DRESTRICT bs.refs cls) bs.globals (EL n env))) envs ∧
          EVERY (λn. n < LENGTH defs) recs)
               o SND o SND o THE o FST) defs
        ⇒
        ∃rs.
        let bvs = MAP
        ((λ(l,cc,(recs,envs)). Block closure_tag
          [CodePtr (THE (bc_find_loc bs (Lab l)))
          ; Block 0 (MAP (λn. RefPtr (EL n rs)) recs ++
                     MAP (λn. THE (lookup_ct sz bs.stack (DRESTRICT bs.refs cls) bs.globals (EL n env))) envs)])
        o THE o FST) defs in
        (LENGTH rs = LENGTH defs) ∧ ALL_DISTINCT rs ∧ (∀r. MEM r rs ⇒ r ∉ FDOM bs.refs) ∧
        bc_next^* bs
        (bs with <| stack := bvs++bs.stack
                  ; pc := next_addr bs.inst_length (bc0 ++ code)
                  ; refs := bs.refs |++ ZIP(rs,MAP (λv. ValueArray [v]) bvs)
                  |>)``,
  rw[compile_closures_def] >>
  qspecl_then[`&0`,`nk`,`s`]mp_tac num_fold_make_ref_thm >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`bmr`strip_assume_tac) >>
  qpat_assum`Abbrev (s' = X)`kall_tac >>
  qspecl_then[`REVERSE defs`,`s'`,`[]`,`s''`,`ecs`]mp_tac FOLDL_push_lab_thm >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`bpl`strip_assume_tac) >>
  qpat_assum`FOLDL (push_lab) X Y = Z`kall_tac >>
  qspecl_then[`ecs`,`env`,`sz`,`nk`,`s''`,`0`]mp_tac FOLDL_cons_closure_thm >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`bcc`strip_assume_tac) >>
  qpat_assum`FOLDL X Y ecs = Z`kall_tac >>
  qspecl_then[`nk`,`nk`,`s'''`,`0`]mp_tac num_fold_update_refptr_thm >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`bur`strip_assume_tac) >>
  qspecl_then[`nk`,`k`,`s''''`]mp_tac num_fold_store_thm >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`bsr`strip_assume_tac) >>
  simp[Once SWAP_REVERSE] >>
  conj_tac >- (
    strip_tac >> fs[EVERY_REVERSE,MAP_REVERSE,code_labels_ok_def,uses_label_thm] >>
    metis_tac[] ) >>
  rpt gen_tac >> strip_tac >>
  last_x_assum(qspecl_then[`bs`,`bc0`,`bpl ++ bcc ++ bur ++ bsr ++ bc1`]mp_tac)>>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`rs`strip_assume_tac) >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  last_x_assum(qspecl_then[`bs1`,`bc0++bmr`,`bcc ++ bur ++ bsr ++ bc1`]mp_tac)>>
  discharge_hyps >- (
    simp[Abbr`bs1`,EVERY_REVERSE] >>
    rfs[EVERY_MEM,bc_find_loc_def] ) >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
  last_x_assum(qspecl_then[`bs2`,`bc0++bmr++bpl`,`bur ++ bsr ++ bc1`,`cls`]mp_tac)>>
  discharge_hyps >- (
    simp[Abbr`bs2`] >>
    conj_tac >- simp[Abbr`bs1`] >>
    conj_tac >- simp[Abbr`bs1`] >>
    simp[EVERY_REVERSE,MAP_REVERSE] >>
    fs[EVERY_MEM,MEM_MAP,GSYM LEFT_FORALL_IMP_THM] >>
    qx_gen_tac`e` >> strip_tac >>
    first_x_assum(qspec_then`e`mp_tac) >>
    simp[UNCURRY,Abbr`bs1`] >> strip_tac >>
    reverse conj_tac >- (
      rpt strip_tac >>
      `n < nk` by PROVE_TAC[]>>
      simp[] ) >>
    rpt strip_tac >>
    qmatch_abbrev_tac`IS_SOME lc` >>
    qsuff_tac`lc = lookup_ct sz bs.stack (DRESTRICT bs.refs cls) bs.globals (EL n env)`>-rw[] >>
    simp[Abbr`lc`] >>
    Q.PAT_ABBREV_TAC`ls:bc_value list = DROP (2 * nk) st` >>
    `ls = bs.stack` by (
      lrw[Abbr`ls`,LIST_EQ_REWRITE,EL_DROP,EL_APPEND2] ) >>
    simp[] >>
    match_mp_tac lookup_ct_change_refs >>
    reverse conj_tac >- (
      rw[] >>
      ntac 2 (first_x_assum(qspec_then`n`mp_tac)) >>
      simp[el_check_def] >> rw[] ) >>
    rw[] >>
    simp[FLOOKUP_DEF,FDOM_FUPDATE_LIST,MEM_MAP,EXISTS_PROD,DRESTRICT_DEF] >>
    `¬MEM p rs` by (
      `IS_SOME (lookup_ct sz bs.stack (DRESTRICT bs.refs cls) bs.globals (EL n env))` by (
        first_x_assum match_mp_tac >> rw[] ) >>
      pop_assum mp_tac >>
      qpat_assum`EL n env = X`SUBST1_TAC >>
      simp[el_check_def,FLOOKUP_DEF,DRESTRICT_DEF] >> rw[] >>
      metis_tac[] ) >>
    simp[] >> rw[] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
    simp[MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF] ) >>
  strip_tac >> rfs[] >>
  qmatch_assum_abbrev_tac`bc_next^* bs2 bs3` >>
  qpat_assum`Abbrev(bs3=X)`mp_tac >>
  simp[MAP_REVERSE] >>
  Q.PAT_ABBREV_TAC`vs:bc_value list = MAP2 X Y Z` >> strip_tac >>
  last_x_assum(qspecl_then[`bs3`,`bc0++bmr++bpl++bcc`,`bsr++bc1`,`vs`,`rs`,`bs.stack`]mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`bs3`,Abbr`bs2`,Abbr`bs1`,GSYM MAP_REVERSE] >>
    conj_tac >- (
      REWRITE_TAC[GSYM APPEND_ASSOC] >>
      Q.PAT_ABBREV_TAC`ls = X ++ bs.stack` >>
      simp[Abbr`nk`,DROP_APPEND2] ) >>
    simp[FDOM_FUPDATE_LIST,MAP_REVERSE,MEM_MAP,EXISTS_PROD] >>
    simp[Abbr`vs`,Abbr`nk`,LENGTH_MAP2] >>
    simp[flookup_fupdate_list] >> rw[] >>
    BasicProvers.CASE_TAC >- (
      imp_res_tac ALOOKUP_FAILS >>
      fs[MEM_MAP] ) >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP]) >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs3 bs4` >>
  last_x_assum(qspecl_then[`bs4`,`bc0++bmr++bpl++bcc++bur`,`bc1`,`vs`,`MAP RefPtr rs`,`bs.stack`]mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`bs4`,Abbr`bs3`,Abbr`bs2`,Abbr`bs1`,Abbr`k`,GSYM MAP_REVERSE,Abbr`nk`] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    Q.PAT_ABBREV_TAC`ls = MAP RefPtr rs ++ X` >>
    simp[DROP_APPEND2,Abbr`vs`,LENGTH_MAP2] ) >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs4 bs5` >>
  simp[markerTheory.Abbrev_def] >>
  qexists_tac`rs` >> simp[] >>
  qho_match_abbrev_tac`bc_next^* bs bs6` >>
  qsuff_tac`bs5 = bs6` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
  simp[Abbr`bs1`,Abbr`bs2`,Abbr`bs3`,Abbr`bs4`,Abbr`bs5`,Abbr`bs6`,bc_state_component_equality] >>
  rpt(qpat_assum`bc_next^* X Y`kall_tac)>>
  conj_asm1_tac >- (
    simp[Abbr`vs`,GSYM MAP_REVERSE,Abbr`nk`,TAKE_LENGTH_ID_rwt,DROP_LENGTH_NIL_rwt] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    Q.PAT_ABBREV_TAC`ls = MAP RefPtr rs ++ X` >>
    simp[TAKE_APPEND2,EL_APPEND1,DROP_APPEND2,MAP2_MAP,TAKE_LENGTH_ID_rwt,DROP_LENGTH_NIL_rwt] >>
    simp[ZIP_MAP,MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f,UNCURRY] >>
    simp[bc_find_loc_def] >>
    simp[APPEND_LENGTH_EQ,MAP_EQ_f] >>
    gen_tac >> strip_tac >>
    conj_tac >> rpt strip_tac >- (
      simp[EL_APPEND2,Abbr`ls`] >>
      Cases_on`n < LENGTH rs`>>simp[EL_APPEND1,EL_MAP] >>
      fs[EVERY_MEM,UNCURRY] >>
      metis_tac[prim_recTheory.LESS_REFL] ) >>
    simp[Abbr`ls`,DROP_APPEND2] >>
    AP_TERM_TAC >>
    match_mp_tac lookup_ct_change_refs >>
    reverse conj_tac >- (
      rw[] >>
      fs[EVERY_MEM] >>
      res_tac >> fs[UNCURRY] >>
      ntac 2 (first_x_assum(qspec_then`n`mp_tac)) >>
      simp[el_check_def] >> rw[] ) >>
    simp[] >> rw[] >> fs[FLOOKUP_DEF] >>
    simp[DRESTRICT_DEF,FDOM_FUPDATE_LIST,MEM_MAP,EXISTS_PROD] >>
    `¬MEM p rs` by (
      fs[EVERY_MEM,UNCURRY] >>
      spose_not_then strip_assume_tac >>
      res_tac >> rfs[el_check_def,FLOOKUP_DEF,DRESTRICT_DEF] ) >>
    rw[] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
    simp[MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF] ) >>
  pop_assum (SUBST1_TAC o SYM) >>
  `LENGTH vs = LENGTH defs` by simp[Abbr`vs`,LENGTH_MAP2] >>
  simp[Abbr`nk`,DROP_LENGTH_NIL_rwt,TAKE_LENGTH_ID_rwt] >>
  match_mp_tac FUPDATE_LIST_CANCEL >>
  lrw[MEM_MAP,MEM_ZIP,EXISTS_PROD] >>
  fs[MEM_EL] >> PROVE_TAC[] )

val compile_closures_next_label_inc = store_thm("compile_closures_next_label_inc",
  ``∀env sz cs (defs:def list). (compile_closures env sz cs defs).next_label = cs.next_label``,
  rpt gen_tac >>
  qspecl_then[`env`,`sz`,`cs`,`defs`]strip_assume_tac compile_closures_thm >>
  fs[LET_THM])
val _ = export_rewrites["compile_closures_next_label_inc"]

(* stackshift *)

val stackshiftaux_thm = store_thm("stackshiftaux_thm",
  ``∀n i j bs bc0 bc1 xs ys z0 zs st.
      let code = MAP Stack (stackshiftaux n i j) in
      bs.code = bc0 ++ code ++ bc1 ∧
      bs.pc = next_addr bs.inst_length bc0 ∧
      bs.stack = xs++ys++z0++zs++st ∧
      LENGTH xs = i ∧
      LENGTH ys = n ∧
      LENGTH zs = n ∧
      j = i + n + LENGTH z0
      ⇒
      bc_next^* bs (bs with <|stack := xs++ys++z0++ys++st; pc := next_addr bs.inst_length (bc0++code)|>)``,
  ho_match_mp_tac stackshiftaux_ind >>
  rpt gen_tac >> strip_tac >>
  simp[Once stackshiftaux_def] >>
  Cases_on`n=0`>>simp[LENGTH_NIL]>-(
    rw[] >> simp[Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality] ) >>
  rw[] >> fs[] >>
  `bc_fetch bs = SOME (Stack(Load (LENGTH xs)))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >>
    simp[] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm] >>
  simp[bc_eval1_def,bc_eval_stack_def,bump_pc_def,EL_APPEND1,EL_APPEND2] >>
  Cases_on`zs`>>fs[]>>
  Cases_on`ys`>>fs[]>>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_fetch bs1 = SOME (Stack (Store (LENGTH xs + LENGTH z0 + LENGTH t + 1)))` by (
    match_mp_tac bc_fetch_next_addr >>
    qmatch_assum_abbrev_tac`bc_fetch bs = SOME i` >>
    qexists_tac`bc0++[i]` >>
    simp[Abbr`bs1`,SUM_APPEND,FILTER_APPEND,Abbr`i`] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm] >>
  simp[bc_eval1_def,bc_eval_stack_def,bump_pc_def,Abbr`bs1`] >>
  simp[TAKE_APPEND1,TAKE_APPEND2,DROP_APPEND1,DROP_APPEND2] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qmatch_assum_abbrev_tac`bc_fetch bs = SOME i1` >>
  qmatch_assum_abbrev_tac`bc_fetch bs0 = SOME i2` >>
  first_x_assum(qspecl_then[`bs1`,`bc0++[i1;i2]`]mp_tac) >>
  simp[Abbr`bs1`,Abbr`i2`] >>
  disch_then(qspecl_then[`xs++[h']`,`t'`,`z0++[h']`]mp_tac) >>
  simp[SUM_APPEND,FILTER_APPEND,Abbr`i1`] >>
  disch_then(qspec_then`t`mp_tac) >>
  simp[ADD1] >>
  qmatch_abbrev_tac`bc_next^* bs3' bs2' ⇒ bc_next^* bs3 bs2` >>
  `bs3 = bs3'` by (
    simp[Abbr`bs3`,Abbr`bs3'`,bc_state_component_equality] ) >>
  `bs2 = bs2'` by (
    simp[Abbr`bs2`,Abbr`bs2'`,bc_state_component_equality] >>
    simp[SUM_APPEND,FILTER_APPEND,ADD1] ) >>
  rw[] )

val GENLIST_Store_thm = store_thm("GENLIST_Store_thm",
  ``∀n k bs bc0 bc1 xs ys zs.
    let code = MAP Stack (GENLIST (λi. Store k) n) in
    bs.code = bc0 ++ code ++ bc1 ∧
    bs.pc = next_addr bs.inst_length bc0 ∧
    bs.stack = xs ++ ys ++ zs ∧
    LENGTH xs = n ∧
    LENGTH ys = SUC k ∧
    n ≤ SUC k
    ⇒
    bc_next^* bs (bs with <| stack := TAKE (SUC k - n) ys ++ xs ++ zs; pc := next_addr bs.inst_length (bc0++code) |>)``,
  Induct >- (
    simp[LENGTH_NIL,TAKE_LENGTH_ID_rwt] >>
    rw[Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality] ) >>
  simp[GENLIST_CONS] >> rw[] >>
  Q.PAT_ABBREV_TAC`f = λi:num. Store k` >>
  `f o SUC = f` by simp[Abbr`f`,FUN_EQ_THM] >> fs[] >>
  `bc_fetch bs = SOME (Stack (Store k))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >> simp[] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  Cases_on`xs`>>fs[]>>
  simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def] >>
  simp[TAKE_APPEND1,TAKE_APPEND2,DROP_APPEND2,DROP_APPEND1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  first_x_assum(qspecl_then[`k`,`bs1`,`bc0++[Stack(Store k)]`]mp_tac) >>
  simp[Abbr`bs1`,SUM_APPEND,FILTER_APPEND] >>
  disch_then(qspecl_then[`t`]mp_tac) >> simp[] >>
  disch_then(mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
  disch_then(qspecl_then[`zs`]mp_tac) >> simp[] >>
  simp[TAKE_APPEND1,TAKE_APPEND2,DROP_APPEND2,DROP_APPEND1] >>
  qmatch_abbrev_tac`bc_next^* bs3' bs2' ⇒ bc_next^* bs3 bs2` >>
  `bs3 = bs3'` by (
    simp[Abbr`bs3`,Abbr`bs3'`,bc_state_component_equality] ) >>
  `bs2 = bs2'` by (
    simp[Abbr`bs2`,Abbr`bs2'`,bc_state_component_equality] >>
    simp[SUM_APPEND,FILTER_APPEND,ADD1] ) >>
  rw[] )

val stackshift_thm = store_thm("stackshift_thm",
  ``∀j k bs bc0 bc1 xs ys st.
      let code = MAP Stack (stackshift j k) in
      bs.code = bc0 ++ code ++ bc1 ∧
      bs.pc = next_addr bs.inst_length bc0 ∧
      bs.stack = xs++ys++st ∧
      LENGTH xs = j ∧
      LENGTH ys = k
      ⇒
      bc_next^* bs (bs with <|stack := xs++st; pc := next_addr bs.inst_length (bc0++code)|>)``,
  ho_match_mp_tac stackshift_ind >>
  rpt gen_tac >> strip_tac >>
  simp[Once stackshift_def] >>
  rpt gen_tac >>
  Cases_on`k=0`>>simp[] >- (
    rw[LENGTH_NIL] >>
    simp[Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality] ) >>
  Cases_on`j=0`>>simp[] >- (
    rw[LENGTH_NIL] >>
    Cases_on`ys`>>fs[] >>
    `bc_fetch bs = SOME (Stack (Pops (LENGTH t)))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0` >>
      simp[] ) >>
    simp[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def,DROP_APPEND2] >>
    qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
    `bc_fetch bs1 = SOME (Stack Pop)` by (
      match_mp_tac bc_fetch_next_addr >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`bc1` >>
      simp[Abbr`bs1`,SUM_APPEND,FILTER_APPEND] ) >>
    simp[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def,Abbr`bs1`] >>
    simp[Once RTC_CASES1] >> disj1_tac >>
    simp[Abbr`bs2`,bc_state_component_equality,SUM_APPEND,FILTER_APPEND] ) >>
  Cases_on`j=1`>>simp[] >- (
    rw[] >>
    Cases_on`xs`>>fs[LENGTH_NIL] >>
    Cases_on`ys`>>fs[] >>
    qmatch_assum_abbrev_tac`bs.code = bc0 ++ [xi] ++ bc1` >>
    `bc_fetch bs = SOME xi` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0` >> simp[Abbr`xi`] ) >>
    match_mp_tac RTC_SUBSET >>
    simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def,Abbr`xi`] >>
    simp[bc_state_component_equality,SUM_APPEND,FILTER_APPEND,DROP_APPEND1,DROP_LENGTH_NIL_rwt] ) >>
  fs[] >>
  Cases_on`j ≤ k` >> fsrw_tac[ARITH_ss][] >- (
    rw[] >>
    qmatch_assum_abbrev_tac`bs.code = bc0 ++ MAP Stack (GENLIST (λi. Store k) n) ++ bc10 ++ bc1` >>
    qspecl_then[`n`,`k`,`bs`,`bc0`,`bc10++bc1`]mp_tac GENLIST_Store_thm >>
    simp[Abbr`bc10`] >>
    disch_then(qspecl_then[`xs`,`ys`]mp_tac) >>
    simp[Abbr`n`,Abbr`k`] >>
    qmatch_abbrev_tac`bc_next^* bs bs1 ⇒ bc_next^* bs bs2` >>
    strip_tac >>
    qsuff_tac`bc_next^* bs1 bs2` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    first_x_assum(qspecl_then[`bs1`](mp_tac o CONV_RULE SWAP_FORALL_CONV)) >>
    disch_then(qspecl_then[`bc1`]mp_tac) >> simp[Abbr`bs1`,ADD1,LENGTH_NIL] >>
    disch_then(mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
    disch_then(qspecl_then[`xs++st`]mp_tac) >> simp[] ) >>
  rw[] >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ MAP Stack (stackshiftaux n i j) ++ MAP Stack (stackshift i n) ++ bc1` >>
  qunabbrev_tac`i` >> qabbrev_tac`i = j-n` >>
  qspecl_then[`n`,`i`,`j`,`bs`,`bc0`]mp_tac stackshiftaux_thm >>
  simp[] >>
  disch_then(qspecl_then[`TAKE i xs`,`DROP i xs`,`[]`]mp_tac) >> simp[] >>
  simp[Abbr`i`,Abbr`j`,Abbr`n`] >>
  disch_then(qspecl_then[`ys`]mp_tac) >> simp[] >>
  qmatch_abbrev_tac`bc_next^* bs bs1 ⇒ bc_next^* bs bs2` >>
  strip_tac >>
  qsuff_tac`bc_next^* bs1 bs2` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
  first_x_assum(qspecl_then[`bs1`](mp_tac o CONV_RULE SWAP_FORALL_CONV)) >>
  disch_then(qspecl_then[`bc1`]mp_tac) >> simp[Abbr`bs1`] >>
  disch_then(qspecl_then[`TAKE (LENGTH xs - LENGTH ys) xs`,`DROP (LENGTH xs - LENGTH ys) xs`]mp_tac) >> simp[])

val FOLDL_emit_append_out = prove(
  ``∀ls s. emit s ls = s with out := REVERSE ls ++ s.out``,
  Induct >> simp[compiler_result_component_equality] >> fs[])
  |> SIMP_RULE (srw_ss())[]

val FILTER_is_Label_Stack = prove(
  ``FILTER (is_Label o Stack) ls = []``,
  Induct_on `ls` >> simp[])

(* compile_append_out *)

val pushret_append_out = store_thm("pushret_append_out",
  ``∀t s. ∃bc. ((pushret t s).out = bc ++ s.out) ∧ EVERY ($~ o is_Label) bc ∧ code_labels_ok bc``,
  Cases >> rw[pushret_def] >> rpt(match_mp_tac code_labels_ok_cons >> simp[]))

val pushret_next_label = store_thm("pushret_next_label",
  ``∀t s. (pushret t s).next_label = s.next_label``,
  Cases >> rw[pushret_def])
val _ = export_rewrites["pushret_next_label"]

val tac =
  rw[compile_def] >>
  SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
  qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
  fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
  fs[code_labels_ok_def,uses_label_thm]

val tac2 =
  rw[compile_def,LET_THM,UNCURRY] >>
  SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
  qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
  fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
  fs[code_labels_ok_def,uses_label_thm] >>
  rw[] >> metis_tac[]

val compile_append_out = store_thm("compile_append_out",
  ``(∀env t sz cs exp.
      ∃bc. ((compile env t sz cs exp).out = bc ++ cs.out) ∧
           cs.next_label ≤ (compile env t sz cs exp).next_label ∧
           ALL_DISTINCT (FILTER is_Label bc) ∧
           EVERY (between cs.next_label (compile env t sz cs exp).next_label) (MAP dest_Label (FILTER is_Label bc))
           ∧ (all_labs exp ⇒ ∀l. uses_label bc l ⇒ l = VfromListLab ∨ MEM (Label l) bc ∨ MEM l (MAP (FST o FST o SND) (free_labs (LENGTH env) exp)))) ∧
    (∀env t sz exp n cs xs.
      ∃bc. ((compile_bindings env t sz exp n cs xs).out = bc ++ cs.out) ∧
           cs.next_label ≤ (compile_bindings env t sz exp n cs xs).next_label ∧
           ALL_DISTINCT (FILTER is_Label bc) ∧
           EVERY (between cs.next_label (compile_bindings env t sz exp n cs xs).next_label) (MAP dest_Label (FILTER is_Label bc))
           ∧ (all_labs exp ⇒ ∀l. uses_label bc l ⇒ l = VfromListLab ∨ MEM (Label l) bc ∨ MEM l (MAP (FST o FST o SND) (free_labs (LENGTH env + xs) exp)))) ∧
    (∀env sz cs exps.
      ∃bc. ((compile_nts env sz cs exps).out = bc ++ cs.out) ∧
           cs.next_label ≤ (compile_nts env sz cs exps).next_label ∧
           ALL_DISTINCT (FILTER is_Label bc) ∧
           EVERY (between cs.next_label (compile_nts env sz cs exps).next_label) (MAP dest_Label (FILTER is_Label bc))
           ∧ (all_labs_list exps ⇒ ∀l. uses_label bc l ⇒ l = VfromListLab ∨ MEM (Label l) bc ∨ MEM l (MAP (FST o FST o SND) (free_labs_list (LENGTH env) exps))))``,
  ho_match_mp_tac compile_ind >>
  strip_tac >- (
    simp[compile_def] >> rw[] >> rw[] >> fs[uses_label_thm]) >>
  strip_tac >- (
    simp[compile_def] >> rw[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    simp[] >>
    fsrw_tac[ARITH_ss,ETA_ss,DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,EVERY_MEM,MEM_MAP,is_Label_rwt,between_def] >>
    simp[CONJ_ASSOC] >>
    conj_tac >- (
      rw[] >> fs[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] >>
      `FILTER is_Label bc'' = []` by (simp[FILTER_EQ_NIL,EVERY_MEM,is_Label_rwt] >> metis_tac[]) >>
      fs[]) >>
    fs[uses_label_thm,code_labels_ok_def] >>
    rw[] >> metis_tac[] ) >>
  strip_tac >- tac >>
  strip_tac >- (
    simp[compile_def] >> rw[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"z"] >>
    qspecl_then[`t`,`z`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`z`] >>
    simp[FOLDL_emit_append_out,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
    fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF,EVERY_MAP,EVERY_REVERSE] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``ALL_DISTINCT``1"ls"] >>
    `ls = []` by simp[Abbr`ls`,FILTER_EQ_NIL,EVERY_MAP] >>
    fs[code_labels_ok_def,uses_label_thm,EXISTS_MEM,MEM_MAP,PULL_EXISTS] ) >>
  strip_tac >- tac >>
  strip_tac >- tac >>
  strip_tac >- tac >>
  strip_tac >- (
    rw[compile_def] >>
    Q.PAT_ABBREV_TAC`ell:ctbind = X` >>
    qspecl_then[`sz`,`cs`,`ell`]mp_tac compile_varref_append_out >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    rw[] >> fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    fs[FILTER_APPEND] >> rw[] >>
    fs[code_labels_ok_def,uses_label_thm]) >>
  strip_tac >- tac2 >>
  strip_tac >- tac2 >>
  strip_tac >- (
    rw[compile_def,LET_THM,UNCURRY] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    srw_tac[ARITH_ss][] >>
    fs[uses_label_thm] >>
    fs[FOLDL_emit_append_out] >>
    simp[FILTER_REVERSE,FILTER_APPEND,MAP_REVERSE,EVERY_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND,FILTER_MAP,EVERY_MAP] >>
    fs[FILTER_is_Label_Stack,MEM_MAP,EXISTS_REVERSE,EXISTS_MAP] >>
    fs[EVERY_MAP,MEM_FILTER,EVERY_MEM] >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
    fsrw_tac[ARITH_ss,DNF_ss][uses_label_thm] >> TRY (metis_tac[]) >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    fsrw_tac[ARITH_ss,ETA_ss,DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,EVERY_MEM,MEM_MAP,is_Label_rwt,between_def] >>
    simp[CONJ_ASSOC] >>
    reverse conj_tac >- (
      fs[code_labels_ok_def,uses_label_thm] >>
      rw[] >> metis_tac[] ) >>
    rw[] >> fs[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
  strip_tac >- (
    simp[compile_def,LET_THM] >>
    rpt strip_tac >> fs[] >>
    Q.ISPECL_THEN[`env`,`sz`,`cs`,`defs`]mp_tac compile_closures_thm >>
    simp[] >> strip_tac >> fs[] >>
    pop_assum kall_tac >>
    simp[FILTER_APPEND,ALL_DISTINCT_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF,ALL_DISTINCT_REVERSE,FILTER_REVERSE,MAP_REVERSE,EVERY_REVERSE] >>
    fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    fs[uses_label_thm,EXISTS_REVERSE] >>
    rw[] >> TRY(metis_tac[]) >>
    fsrw_tac[DNF_ss][free_labs_defs_MAP,MEM_MAP,MEM_FLAT,MEM_GENLIST] >>
    Cases_on`MEM (Label l) code`>>fs[]>>
    res_tac >> qmatch_assum_rename_tac`MEM def defs`[]>>PairCases_on`def`>>
    Cases_on`def0`>- (
      fs[EVERY_MEM] >> res_tac >> fs[] ) >>
    disj2_tac >> disj2_tac >> disj1_tac >>
    PairCases_on`x`>>fsrw_tac[DNF_ss][MEM_EL]>>
    pop_assum(assume_tac o SYM) >>
    qexists_tac`n`>>simp[]>>
    qexists_tac`0`>>simp[]) >>
  strip_tac >- (
    rw[compile_def,LET_THM,UNCURRY] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    srw_tac[ARITH_ss][] >>
    fs[uses_label_thm] >>
    fs[FOLDL_emit_append_out] >>
    simp[FILTER_REVERSE,FILTER_APPEND,MAP_REVERSE,EVERY_REVERSE,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND,FILTER_MAP,EVERY_MAP] >>
    fs[FILTER_is_Label_Stack,MEM_MAP,EXISTS_REVERSE,EXISTS_MAP] >>
    fs[EVERY_MAP]) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >> fs[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"a"] >>
    qspecl_then[`t`,`a`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`a`] >>
    Cases_on`uop`>>fs[]>>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >> rw[] >> fs[] >>
    fs[code_labels_ok_def,uses_label_thm] >>
    rw[] >> TRY(metis_tac[])) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >> fs[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
    rw[] >> fs[] >>
    fs[code_labels_ok_def,uses_label_thm] >>
    rw[] >> metis_tac[]) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >> fs[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
    rw[] >> fs[] >>
    fs[code_labels_ok_def,uses_label_thm] >>
    rw[] >> metis_tac[]) >>
  strip_tac >- (
    gen_tac >> Cases >> simp[compile_def] >> rw[] >> fs[] >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,MEM_MAP,between_def] >>
    fs[code_labels_ok_def,uses_label_thm] >>
    simp[CONJ_ASSOC] >> (
    reverse conj_tac >- (
      rw[] >> metis_tac[] ) >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC)) >>
  strip_tac >- tac2 >>
  strip_tac >- (
    gen_tac >> Cases >> simp[compile_def] >> rw[] >> fs[] >>
    rw[] >> fs[uses_label_thm] ) >>
  strip_tac >- (
    rw[compile_def,uses_label_thm] >>
    fsrw_tac[ARITH_ss][ADD1] ) >>
  strip_tac >- rw[compile_def] >>
  rw[compile_def] >> fs[] >>
  fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
  simp[CONJ_ASSOC] >>
  reverse conj_tac >- (
    fsrw_tac[ARITH_ss,DNF_ss][uses_label_thm] >>
    rw[] >> metis_tac[] ) >>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC)

(* retbc, jmpbc *)

val _ = Parse.overload_on("retbc",``λj k. [Stack (Pops (k + 1)); Stack (Load 1); Stack (Store (j + 2)); Stack (Pops (j + 1)); Return]``)

val retbc_thm = store_thm("retbc_thm",
  ``∀bs bc0 bc1 bv vs benv ret args x st bs'.
    (bs.stack = bv::vs++benv::CodePtr ret::args++x::st) ∧
    (bs.code = bc0 ++ retbc (LENGTH args) (LENGTH vs) ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (bs' = bs with <| stack := bv::st; pc := ret |>)
    ⇒ bc_next^* bs bs'``,
  rw[] >>
  qspecl_then[`bc0`,`bs`]mp_tac bc_fetch_next_addr >> simp[] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  lrw[DROP_APPEND1,DROP_APPEND2] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 1 (retbc (LENGTH args) (LENGTH vs)))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 2 (retbc (LENGTH args) (LENGTH vs)))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  simp_tac std_ss [bc_eval_stack_def] >>
  srw_tac[ARITH_ss][ADD1] >>
  rw[bump_pc_def] >>
  lrw[TAKE_APPEND1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 3 (retbc (LENGTH args) (LENGTH vs)))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  lrw[DROP_APPEND2,DROP_APPEND1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 4 (retbc (LENGTH args) (LENGTH vs)))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def])

val _ = Parse.overload_on("jmpbc",``λck n j k.
  [Stack (Load (n + k + 2)); Stack (Load (n + 1)); Stack (El 0); Stack (Load (n + 2)); Stack (El 1)]
  ++ (MAP Stack (stackshift (n + 4) (k + j + 3)))
  ++ (if ck then [Tick] else []) ++ [Return]``)

val code = ``jmpbc ck (LENGTH (args1 :bc_value list)) (LENGTH (args : bc_value list)) (LENGTH (vs : bc_value list))``
val jmpbc_thm = store_thm("jmpbc_thm",
  ``∀bs bc0 bc1 bv vs benv ret args cl ct x y ck args1 st bs'.
    (bs.stack = args1 ++ (Block ct [CodePtr x;y])::vs++benv::ret::args++cl::st) ∧
    (bs.code = bc0 ++ jmpbc ck (LENGTH args1) (LENGTH args) (LENGTH vs) ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (ck ⇒ ∀n. bs.clock = SOME n ⇒ n > 0) ∧
    (bs' = bs with <| stack := y::ret::args1++(Block ct [CodePtr x;y])::st; pc := x; clock := if ck then OPTION_MAP PRE bs.clock else bs.clock |>)
    ⇒ bc_next^* bs bs'``,
  rpt gen_tac >>
  Q.PAT_ABBREV_TAC`cka = if ck then X else bs.clock` >>
  strip_tac >>
  qspecl_then[`bc0`,`bs`]mp_tac bc_fetch_next_addr >> simp[] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  lrw[EL_APPEND2,EL_APPEND1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 1 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  lrw[EL_APPEND1,EL_APPEND2,EL_CONS] >>
  srw_tac[ARITH_ss][GSYM ADD1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 2 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND,ADD1] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  simp_tac std_ss [bc_eval_stack_def] >>
  srw_tac[ARITH_ss][ADD1] >>
  rw[bump_pc_def] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 3 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  lrw[EL_APPEND1,EL_APPEND2,EL_CONS] >>
  REWRITE_TAC[TWO,ONE,Once ADD_SYM,prim_recTheory.PRE] >>
  REWRITE_TAC[Once ADD_SYM] >>
  REWRITE_TAC[GSYM ADD_SUC] >>
  srw_tac[ARITH_ss][] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 4 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND,ADD1] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  rw[bump_pc_def] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`LENGTH args1 + 4`,`LENGTH args + LENGTH vs + 3`,`bs1`]mp_tac stackshift_thm >>
  simp[Abbr`bs1`] >>
  disch_then(mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
  disch_then(qspec_then`(if ck then [Tick] else []) ++ [Return] ++ bc1`mp_tac) >>
  simp[SUM_APPEND,FILTER_APPEND] >>
  disch_then(qspec_then`y::CodePtr x::ret::(args1++[Block ct [CodePtr x;y]])`mp_tac) >>
  simp[] >>
  disch_then(mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
  disch_then(qspec_then`st`mp_tac) >>
  simp[] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs3 ⇒ bc_next^* bs1' bs2` >>
  `bs1' = bs1` by (
    simp[Abbr`bs1`,Abbr`bs1'`,bc_state_component_equality] ) >>
  pop_assum SUBST1_TAC >> qunabbrev_tac`bs1'` >>
  qsuff_tac`bc_next^* bs3 bs2` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
  qunabbrev_tac`bs1` >> qunabbrev_tac`bs3` >> qunabbrev_tac`bs2` >>
  ntac 5 (pop_assum kall_tac) >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  Cases_on`ck`>-(
    qspecl_then[`bc0++(BUTLASTN 2 ^(subst[``ck:bool``|->``T``]code))`,`bs1`]mp_tac bc_fetch_next_addr >>
    simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND,ADD1,BUTLASTN_APPEND1,BUTLASTN_APPEND2,BUTLASTN_CONS,BUTLASTN] >>
    rw[Once RTC_CASES1] >> disj2_tac >>
    rw[bc_eval1_thm] >>
    rw[bc_eval1_def,Abbr`bs2`,Abbr`cka`] >>
    BasicProvers.CASE_TAC >> simp[bump_pc_def] >>
    qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
    qspecl_then[`bc0++(FRONT ^(subst[``ck:bool``|->``T``]code))`,`bs1`]mp_tac bc_fetch_next_addr >>
    simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND,ADD1,FRONT_CONS,FRONT_APPEND,FRONT_DEF] >>
    rw[Once RTC_CASES1] >> disj2_tac >>
    rw[bc_eval1_thm] >>
    rw[bc_eval1_def,Abbr`bs2`] >>
    REWRITE_TAC[GSYM CONS_APPEND,GSYM APPEND_ASSOC] >>
    rw[] >>
    rw[Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality]) >>
  qspecl_then[`bc0++(FRONT ^(subst[``ck:bool``|->``F``]code))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND,ADD1,FRONT_CONS,FRONT_APPEND,FRONT_DEF] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def,Abbr`bs2`] >>
  REWRITE_TAC[GSYM CONS_APPEND,GSYM APPEND_ASSOC] >>
  rw[Abbr`cka`] >>
  rw[Once RTC_CASES1] >> disj1_tac >>
  simp[bc_state_component_equality])

(* code_for_push, code_for_return *)

val code_for_push_def = Define`
  code_for_push rd bs bce bc0 code s' env vs renv rsz =
    ∃bvs rf rd' ck gv.
    let bs' = bs with <| stack := (REVERSE bvs)++bs.stack; pc := next_addr bs.inst_length (bc0 ++ code);
                         refs := rf; clock := ck; globals := gv |> in
    bc_next^* bs bs' ∧
    EVERY2 (Cv_bv (mk_pp rd' (bs' with code := bce))) vs bvs ∧
    Cenv_bs rd' s' env renv (rsz+(LENGTH vs)) (bs' with code := bce) ∧
    DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf (COMPL (set rd'.sm)) ∧
    rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls ∧ gvrel bs.globals gv`

val code_for_return_def = Define`
  code_for_return rd bs bce st ret sp v s' =
    ∃bv rf rd' ck gv.
    let bs' = bs with <| stack := bv::st; pc := ret; refs := rf; clock := ck; handler := sp; globals := gv |> in
    bc_next^* bs bs' ∧
    Cv_bv (mk_pp rd' (bs' with code := bce)) v bv ∧
    s_refs rd' s' (bs' with code := bce) ∧
    DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf (COMPL (set rd'.sm)) ∧
    rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls ∧ gvrel bs.globals gv`

val code_for_push_return = store_thm("code_for_push_return",
  ``∀rd bs bce bc0 code s' env v renv rsz bc1 args args1 bs' blvs benv st cl cl1 ret hdl.
    code_for_push rd bs bce bc0 code s' env [v] renv rsz ∧
    (bs.code = bc0 ++ code ++ retbc (LENGTH args) (LENGTH blvs) ++ bc1) ∧
    (bs.stack = blvs++benv::CodePtr ret::args++cl::st) ∧
    (bs.handler = hdl)
    ⇒
    code_for_return rd bs bce st ret hdl v s'``,
    rw[code_for_push_def,code_for_return_def,LET_THM] >>
    qmatch_assum_rename_tac `Cv_bv pp v bv`["pp"] >>
    map_every qexists_tac [`bv`,`rf`,`rd'`,`ck`,`gv`] >>
    fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    rw[] >>
    match_mp_tac (SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
    first_assum (exists_tac o rand o concl) >> fs[Abbr`bs0`] >>
    qpat_assum`bs.code = X`(assume_tac o SYM)>>fs[]>>
    match_mp_tac retbc_thm >>
    pop_assum(assume_tac o SYM) >>
    qexists_tac`bc0 ++ code` >> fs[Abbr`bs1`] >>
    qexists_tac`blvs`>>fs[]>>
    qexists_tac`args`>>fs[]>>
    simp[bc_state_component_equality])

val code_for_return_append_code = store_thm("code_for_return_append_code",
  ``∀rd bs bce st hdl sp v s' bs' bc1.
    code_for_return rd bs bce st hdl sp v s' ∧
    (bs' = bs with code := bs.code ++ bc1)
    ⇒
    code_for_return rd bs' bce st hdl sp v s'``,
  simp[code_for_return_def] >>
  rpt gen_tac >> strip_tac >>
  map_every qexists_tac[`bv`,`rf`,`rd'`,`ck`,`gv`] >> fs[] >>
  match_mp_tac RTC_bc_next_append_code >>
  qexists_tac`bs` >>
  HINT_EXISTS_TAC >>
  simp[bc_state_component_equality])

(* compiling strings *)

val compile_string_thm = store_thm("compile_string_thm",
  ``∀f ls code bs bc0 bc1 bs'.
      code = MAP (Stack o PushInt o f) ls ∧
      bs.code = bc0 ++ code ++ bc1 ∧
      bs.pc = next_addr bs.inst_length bc0 ∧
      bs' = bs with <| pc := next_addr bs.inst_length (bc0 ++ code)
                     ; stack := REVERSE (MAP (Number o f) ls) ++ bs.stack
                     |>
      ⇒ bc_next^* bs bs'``,
  gen_tac >> Induct >> simp[] >> rw[] >- (
    pop_assum (SUBST1_TAC o SYM) >> rw[] ) >>
  `bc_fetch bs = SOME (Stack (PushInt (f h)))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >> rw[] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  qexists_tac`bump_pc bs with stack := Number (f h) :: bs.stack` >>
  conj_tac >- (
    simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def] ) >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ c0 ++ c1 ++ bc1` >>
  first_x_assum(qspecl_then[`c1`,`bs1`,`bc0++c0`,`bc1`]mp_tac) >>
  simp[Abbr`bs1`,bump_pc_def,Abbr`c0`,SUM_APPEND,FILTER_APPEND] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2' ⇒ bc_next^* bs1 bs2` >>
  `bs2' = bs2` by (
    simp[Abbr`bs2`,Abbr`bs2'`,bc_state_component_equality,FILTER_APPEND,SUM_APPEND] )
  >> rw[])

(* compile *)

val compile_bindings_thm = store_thm("compile_bindings_thm",
  ``∀env t sz e n s m bc cc.
    ((compile_bindings env t sz e n s m).out = bc ++ s.out) ∧
    ((compile
       ((REVERSE(GENLIST(λi. CTLet (sz+n+1+i))m))++env)
       (case t of TCTail j k => TCTail j (k+(m+n)) | _ => t)
       (sz+(m+n))
       s e).out = cc++s.out) ⇒
    (bc = (case t of TCNonTail => [Stack(Pops (m + n))] | _ => [])++cc)``,
  Induct_on`m`>- (
    rw[compile_def,FUPDATE_LIST_THM]>>
    Cases_on`t`>>fs[]>>
    rw[]>>fs[]) >>
  rw[compile_def,GENLIST_CONS,combinTheory.o_DEF] >>
  qmatch_assum_abbrev_tac`(compile_bindings env0 t sz e n0 s m).out = bc ++ s.out` >>
  first_x_assum(qspecl_then[`env0`,`t`,`sz`,`e`,`n0`,`s`,`bc`,`cc`]mp_tac) >>
  simp[ADD1,Abbr`n0`] >>
  disch_then match_mp_tac >>
  unabbrev_all_tac >>
  pop_assum(SUBST1_TAC o SYM) >>
  simp[ADD1,FUPDATE_LIST_THM] >>
  rpt AP_TERM_TAC >> rpt AP_THM_TAC >>
  rpt AP_TERM_TAC >> rpt AP_THM_TAC >>
  rpt AP_TERM_TAC >> rpt AP_THM_TAC >>
  simp[FUN_EQ_THM] >>
  rpt AP_TERM_TAC >> rpt AP_THM_TAC >>
  rpt AP_TERM_TAC >> rpt AP_THM_TAC >>
  simp[FUN_EQ_THM])

(*
val compile_mvars_SUBMAP = store_thm("compile_mvars_SUBMAP",
  ``(∀menv env t sz s e menv'.
      menv ⊑ menv' ∧ (∀mn x. (mn,x) ∈ mvars e ⇒ ∃env. FLOOKUP menv mn = SOME env ∧ x < LENGTH env)
      ⇒ compile menv' env t sz s e = compile menv env t sz s e) ∧
    (∀menv env t sz e n cs xs menv'.
      menv ⊑ menv' ∧ (∀mn x. (mn,x) ∈ mvars e ⇒ ∃env. FLOOKUP menv mn = SOME env ∧ x < LENGTH env)
      ⇒ compile_bindings menv' env t sz e n cs xs = compile_bindings menv env t sz e n cs xs) ∧
    (∀menv env sz cs es menv'.
      menv ⊑ menv' ∧ (∀mn x. (mn,x) ∈ mvars_list es ⇒ ∃env. FLOOKUP menv mn = SOME env ∧ x < LENGTH env)
      ⇒ compile_nts menv' env sz cs es = compile_nts menv env sz cs es)``,
  ho_match_mp_tac compile_ind >>
  simp[compile_def] >> rw[] >>
  TRY (
    first_x_assum(qspec_then`menv'`mp_tac) >>
    discharge_hyps >- metis_tac[] >> rw[] >> NO_TAC)
  >- (
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >- (
      fs[SUBMAP_DEF,FLOOKUP_DEF] >>
      metis_tac[] ) >>
    fs[SUBMAP_DEF,FLOOKUP_DEF] ) >>
  BasicProvers.CASE_TAC >> fs[])
*)

val prefix_exists_lemma = store_thm("prefix_exists_lemma",
  ``∀st n. ∃ls. st = ls ++ DROP n st``,
  Induct >> simp[] >>
  gen_tac >> Cases >> fs[] >>
  first_x_assum(qspec_then`n'`strip_assume_tac) >>
  qexists_tac`h::ls` >> simp[])

val compile_labels_lemma = store_thm("compile_labels_lemma",
  ``∀env t sz cs exp bc0 cs1 cls1 code.
    (cs1 = compile env t sz cs exp) ∧
    (cs1.out = REVERSE code ++ cs.out) ∧
    (cls1 = bc0 ++ code) ∧
    ALL_DISTINCT (FILTER is_Label bc0) ∧
    EVERY (combin$C $< cs.next_label o dest_Label)
      (FILTER is_Label bc0)
    ⇒
    ALL_DISTINCT (FILTER is_Label cls1) ∧
    EVERY (combin$C $< cs1.next_label o dest_Label)
      (FILTER is_Label cls1)``,
  rpt gen_tac >> strip_tac >>
  qspecl_then[`env`,`t`,`sz`,`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
  disch_then(Q.X_CHOOSE_THEN`bc`strip_assume_tac) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fsrw_tac[DNF_ss][FILTER_APPEND,EVERY_MEM,MEM_FILTER,is_Label_rwt,
                   ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,
                   MEM_MAP,between_def] >>
  qpat_assum`bc = REVERSE code`mp_tac >>
  Q.ISPECL_THEN[`bc`,`code`]SUBST1_TAC SWAP_REVERSE >>
  rw[FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
  spose_not_then strip_assume_tac >>
  res_tac >> DECIDE_TAC)

val t1 = qspecl_then[`cenv`,`sz`,`cs`,`exps`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT2 (CONJUNCT2 compile_append_out))
val t2 = qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out)

fun tac18 t =
  simp[] >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  simp[compile_def,LET_THM,pushret_def] >>
  fsrw_tac[ETA_ss][] >>
  t >>
  simp[GSYM FORALL_AND_THM] >>
  gen_tac >>
  Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
  qspecl_then[`t`,`cs1`](Q.X_CHOOSE_THEN`cp`strip_assume_tac)pushret_append_out >> pop_assum kall_tac >>
  simp[Once SWAP_REVERSE,Abbr`cs1`] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cx`]mp_tac) >>
  simp[] >>
  TRY(disch_then(qspec_then`TCNonTail`mp_tac)) >>
  simp[] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum(qspecl_then[`ig`,`sp`,`hdl`,`st`]mp_tac) >>
  simp[] >>
  strip_tac >>
  match_mp_tac code_for_return_append_code >>
  HINT_EXISTS_TAC >>
  simp[bc_state_component_equality];

;val compile_val = store_thm("compile_val",
  ``(∀s env exp res. Cevaluate s env exp res ⇒
      ∀rd s' beh cs cenv sz bs bce bcr bc0 code bc1.
        (res = (s', beh)) ∧
        (bce ++ bcr = bc0 ++ code ++ bc1) ∧
        contains_primitives bce ∧
        all_vlabs_csg s ∧ all_vlabs_list env ∧ all_labs exp ∧
        EVERY (code_env_cd bce) (free_labs (LENGTH env) exp) ∧
        (∀cd. cd ∈ vlabs_list (store_vs (SND (FST s))) ⇒ code_env_cd bce cd) ∧
        (∀cd. cd ∈ vlabs_list env ⇒ code_env_cd bce cd) ∧
        (∀cd. cd ∈ vlabs_list (MAP THE (FILTER IS_SOME (SND s))) ⇒ code_env_cd bce cd) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.clock = SOME (FST (FST s))) ∧
        set (free_vars exp) ⊆ count (LENGTH cenv) ∧
        Cenv_bs rd s env cenv sz (bs with code := bce) ∧
        ALL_DISTINCT (FILTER is_Label bc0) ∧
        EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc0)
        ⇒
      (∀v.
         (beh = Rval v) ∧
         ((compile cenv TCNonTail sz cs exp).out = REVERSE code ++ cs.out)
           ⇒
         code_for_push rd bs bce bc0 code s' env [v] cenv sz) ∧
      (∀v az lz env0 defs vs klvs blvs benv ret args cl st.
         (beh = Rval v) ∧
         ((compile cenv (TCTail az lz) sz cs exp).out = REVERSE code ++ cs.out) ∧
         (az = LENGTH args) ∧ (lz = LENGTH klvs) ∧
         (env = klvs ++ REVERSE vs ++ env0) ∧
         EVERY2 (Cv_bv (mk_pp rd (bs with code := bce))) vs args ∧
         EVERY2 (Cv_bv (mk_pp rd (bs with code := bce))) klvs blvs ∧
         (bs.stack = blvs++benv::CodePtr ret::(REVERSE args)++cl::st)
           ⇒
         code_for_return rd bs bce st ret bs.handler v s') ∧
      (∀t err.
         (beh = Rerr err) ∧
         ((compile cenv t sz cs exp).out = REVERSE code ++ cs.out)
           ⇒
         (∀ig sp hdl st v. err = Rraise v ∧
           (case t of TCTail az lz => ∃blvs benv ret args cl ig'.
             (ig = blvs++benv::CodePtr ret::(REVERSE args)++cl::ig') ∧
             (az = LENGTH args) ∧ (lz = LENGTH blvs) | TCNonTail => T) ∧
           (bs.stack = ig++(StackPtr sp)::CodePtr hdl::st) ∧
           (bs.handler = LENGTH st + 1)
           ⇒
          code_for_return rd bs bce st hdl sp v s') ∧
         (err = Rtimeout_error ∧
            (case t of TCTail az lz => ∃blvs benv ret args cl st.
             (bs.stack = blvs++benv::CodePtr ret::(REVERSE args)++cl::st) ∧
             (az = LENGTH args) ∧ (lz = LENGTH blvs) | TCNonTail => T)
         ⇒
          ∃bs'. bc_next^* bs bs' ∧ (bs'.clock = SOME 0) ∧ (bc_fetch bs' = SOME Tick) ∧ bs'.output = bs.output))) ∧
    (∀s env exps ress. Cevaluate_list s env exps ress ⇒
      ∀rd s' beh cs cenv sz bs bce bcr bc0 code bc1.
        (ress = (s', beh)) ∧
        (bce ++ bcr = bc0 ++ code ++ bc1) ∧
        contains_primitives bce ∧
        all_vlabs_csg s ∧ all_vlabs_list env ∧ all_labs_list exps ∧
        EVERY (code_env_cd bce) (free_labs_list (LENGTH env) exps) ∧
        (∀cd. cd ∈ vlabs_list (store_vs (SND (FST s))) ⇒ code_env_cd bce cd) ∧
        (∀cd. cd ∈ vlabs_list env ⇒ code_env_cd bce cd) ∧
        (∀cd. cd ∈ vlabs_list (MAP THE (FILTER IS_SOME (SND s))) ⇒ code_env_cd bce cd) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.clock = SOME (FST (FST s))) ∧
        set (free_vars_list exps) ⊆ count (LENGTH cenv) ∧
        Cenv_bs rd s env cenv sz (bs with code := bce) ∧
        ALL_DISTINCT (FILTER is_Label bc0) ∧
        EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc0) ∧
        ((compile_nts cenv sz cs exps).out = REVERSE code ++ cs.out)
        ⇒
      (∀vs. (beh = Rval vs) ⇒
         code_for_push rd bs bce bc0 code s' env vs cenv sz) ∧
      (∀err.
        (beh = Rerr err)
          ⇒
        (∀v ig sp hdl st. err = Rraise v ∧
          (bs.stack = ig++(StackPtr sp)::CodePtr hdl::st) ∧
          (bs.handler = LENGTH st + 1)
          ⇒ code_for_return rd bs bce st hdl sp v s') ∧
        (err = Rtimeout_error ⇒
         ∃bs'. bc_next^* bs bs' ∧ (bs'.clock = SOME 0) ∧ (bc_fetch bs' = SOME Tick) ∧ bs'.output = bs.output)))``,
  ho_match_mp_tac Cevaluate_strongind >>
  strip_tac >- (
    simp[compile_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out)>>
    disch_then(Q.X_CHOOSE_THEN`cc`strip_assume_tac) >>
    simp[Once SWAP_REVERSE] >> strip_tac >>
    qx_gen_tac`t` >> strip_tac >>
    map_every qx_gen_tac[`ig`,`sp`,`hdl`,`st`] >> strip_tac >>
    first_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cc`,`[PopExc;Return]++bc1`]mp_tac) >>
    simp[] >>
    disch_then (mp_tac o CONJUNCT1) >>
    simp[code_for_push_def,code_for_return_def] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac[`rf`,`rd'`,`ck`,`gv`,`ev`] >> strip_tac >>
    map_every qexists_tac[`ev`,`rf`,`rd'`,`ck`,`gv`] >>
    conj_tac >- (
      qmatch_assum_abbrev_tac`bc_next^* bs bs2` >>
      match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
      HINT_EXISTS_TAC >> simp[] >>
      simp[RTC_eq_NRC] >>
      qexists_tac`SUC(SUC 0)` >>
      simp[NRC,Abbr`bs2`] >>
      qmatch_abbrev_tac`∃bs2. bc_next bs1 bs2 ∧ bc_next bs2 bs3` >>
      `bc_fetch bs1 = SOME PopExc` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs1`] >>
        qexists_tac`bc0++REVERSE cc`>>simp[] ) >>
      simp[bc_eval1_thm] >>
      simp[Once bc_eval1_def,Abbr`bs1`,EL_REVERSE,PRE_SUB1,EL_APPEND1,EL_APPEND2,bump_pc_def] >>
      simp[REVERSE_APPEND,TAKE_APPEND1,TAKE_APPEND2] >>
      qmatch_abbrev_tac`bc_eval1 bs2 = SOME bs3` >>
      `bc_fetch bs2 = SOME Return` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs2`] >>
        qexists_tac`bc0++REVERSE cc++[PopExc]`>>simp[SUM_APPEND,FILTER_APPEND] ) >>
      simp[bc_eval1_def,Abbr`bs2`] ) >>
    simp[] >>
    fs[Cenv_bs_def] >>
    fs[s_refs_def,good_rd_def] ) >>
  strip_tac >- (
    simp[compile_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out)>>
    disch_then(Q.X_CHOOSE_THEN`cc`strip_assume_tac) >>
    simp[Once SWAP_REVERSE] >> strip_tac >>
    rw[Once SWAP_REVERSE] >>
    first_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cc`,`PopExc::Return::bc1`]mp_tac) >>
    simp[] >>
    disch_then(qspec_then`TCNonTail`mp_tac)>>
    TRY(disch_then(qspec_then`ig`mp_tac))>>
    rw[]) >>
  strip_tac >- (
    simp[compile_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_result_out_fupd (K (PushExc::Y::Z)) U` >>
    qspecl_then[`cenv`,`TCNonTail`,`sz + 2`,`cs0`,`exp`](Q.X_CHOOSE_THEN`cc`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    simp[pushret_def] >>
    REWRITE_TAC[ONE] >>
    simp[compile_def] >>
    strip_tac >>
    conj_tac >- (
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd (K (Label X::Y::Z)) U` >>
      qspecl_then[`CTLet(sz+1)::cenv`,`TCNonTail`,`sz+1`,`cs1`,`e2`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      simp[Abbr`cs1`,Abbr`cs0`,Once SWAP_REVERSE] >>
      rpt gen_tac >> strip_tac >>
      `bc_fetch bs = SOME (PushPtr (Lab cs.next_label))` by (
        match_mp_tac bc_fetch_next_addr >>
        qexists_tac`bc0`>>simp[] ) >>
      `bc_next bs (bump_pc bs with stack := CodePtr (next_addr bs.inst_length (TAKE (LENGTH bc0 + 2 + LENGTH cc + 4) bs.code))::bs.stack)` by (
        simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
        simp[bc_state_component_equality,bc_find_loc_def] >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        qexists_tac`LENGTH bc0 + LENGTH cc + 5` >>
        simp[TAKE_APPEND1,TAKE_APPEND2,EL_APPEND1,EL_APPEND2,EL_CONS,PRE_SUB1,FILTER_APPEND,SUM_APPEND] >>
        fs[FILTER_REVERSE,ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
        fsrw_tac[DNF_ss][EVERY_MEM,between_def,MEM_FILTER,MEM_MAP] >>
        fsrw_tac[DNF_ss][is_Label_rwt] >>
        rpt(first_x_assum(qspec_then`rd`kall_tac)) >>
        rpt(qpat_assum`X.out = Y`kall_tac) >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][]) >>
      qmatch_assum_abbrev_tac`bc_next bs bs1` >>
      `bc_fetch bs1 = SOME PushExc` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs1`,bump_pc_def] >>
        qexists_tac`bc0 ++ [PushPtr (Lab cs.next_label)]` >>
        simp[FILTER_APPEND,SUM_APPEND] ) >>
      `bc_next bs1 (bump_pc bs1 with <| stack := StackPtr bs.handler::bs1.stack; handler := LENGTH bs1.stack |>)` by (
        simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
        simp[bc_state_component_equality] >>
        simp[Abbr`bs1`,bump_pc_def]) >>
      qmatch_assum_abbrev_tac`bc_next bs1 bs2` >>
      `bc_next^* bs bs2` by metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
      pop_assum mp_tac >>
      simp[Abbr`bs2`,bump_pc_def,Abbr`bs1`,ADD1] >>
      rpt(qpat_assum`bc_next X Y`kall_tac) >>
      rpt(qpat_assum`bc_fetch X = Y`kall_tac) >>
      strip_tac >>
      qmatch_assum_abbrev_tac`bc_next^* bs bss0` >>
      qmatch_assum_abbrev_tac`(compile cenv TCNonTail (sz + 2) cs0 exp).out = cc ++ cs0.out` >>
      first_x_assum(qspecl_then[`rd`,`cs0`,`cenv`,`sz+2`,`bss0`,`bce`,`bcr`,`TAKE (LENGTH bc0+2) bs.code`,`REVERSE cc`
                               ,`DROP (LENGTH bc0+2+LENGTH cc) bs.code`]mp_tac) >>
      discharge_hyps >- (
        simp[Abbr`bss0`] >>
        simp[SUM_APPEND,FILTER_APPEND,Abbr`cs0`,TAKE_APPEND1,TAKE_APPEND2,DROP_APPEND1,DROP_APPEND2,DROP_LENGTH_NIL_rwt] >>
        conj_tac >- (
          SUBST1_TAC(DECIDE``sz + 2 = (sz + 1) + 1``) >>
          qmatch_abbrev_tac`Cenv_bs rd s env cenv (sz + 1 + 1) bs0` >>
          match_mp_tac Cenv_bs_imp_incsz >>
          qexists_tac`bs0 with stack := TL bs0.stack` >>
          simp[Abbr`bs0`,bc_state_component_equality] >>
          qmatch_abbrev_tac`Cenv_bs rd s env cenv (sz + 1) bs0` >>
          match_mp_tac Cenv_bs_imp_incsz >>
          qexists_tac`bs0 with stack := TL bs0.stack` >>
          simp[Abbr`bs0`,bc_state_component_equality] >>
          match_mp_tac Cenv_bs_with_irr >>
          HINT_EXISTS_TAC >> simp[] ) >>
        fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt] >>
        rw[] >> res_tac >> simp[] ) >>
      disch_then(mp_tac o CONJUNCT1) >>
      simp[Abbr`bss0`,TAKE_APPEND1,TAKE_APPEND2] >>
      simp[code_for_push_def] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      map_every qx_gen_tac[`rf`,`rd'`,`ck`,`gv`,`bv`] >>
      strip_tac >>
      map_every qexists_tac[`rf`,`rd'`,`ck`,`gv`,`bv`] >>
      conj_tac >- (
        qmatch_assum_abbrev_tac`bc_next^* bs2 bs3` >>
        qmatch_abbrev_tac`bc_next^* bs bs5` >>
        qmatch_assum_abbrev_tac`bc_next^* bs bss0` >>
        `bs2 = bss0` by (
          simp[bc_state_component_equality,Abbr`bs2`,Abbr`bss0`,TAKE_APPEND1,TAKE_APPEND2] ) >>
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        qexists_tac`bss0` >> simp[] >>
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        fs[] >> HINT_EXISTS_TAC >> simp[] >>
        simp[RTC_eq_NRC] >>
        qexists_tac`SUC(SUC(SUC 0))` >>
        simp[NRC] >>
        qho_match_abbrev_tac`∃bs1. bc_next bs0 bs1 ∧ P bs1` >>
        `bc_fetch bs0 = SOME PopExc` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs0`,Abbr`bs3`,Abbr`bss0`] >>
          qexists_tac`bc0++[PushPtr(Lab cs.next_label);PushExc]++REVERSE cc` >>
          simp[] ) >>
        simp[bc_eval1_thm,bc_eval1_def,Abbr`bs0`,Abbr`bs3`,Abbr`bss0`,EL_APPEND1,EL_APPEND2,bump_pc_def] >>
        simp[Abbr`P`] >>
        qho_match_abbrev_tac`∃bs1. bc_next bs0 bs1 ∧ P bs1` >>
        `bc_fetch bs0 = SOME (Stack (Pops 1))` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs0`] >>
          Q.PAT_ABBREV_TAC`ls:bc_inst list = X` >>
          qexists_tac`TAKE (LENGTH bc0 + 2 + LENGTH cc + 1) ls` >>
          simp[Abbr`ls`,SUM_APPEND,FILTER_APPEND,TAKE_APPEND2,TAKE_APPEND1] ) >>
        simp[bc_eval1_def,bc_eval1_thm,Abbr`bs0`,bc_eval_stack_def,bump_pc_def] >>
        simp[TAKE_APPEND1,TAKE_APPEND2,REVERSE_APPEND,Abbr`P`] >>
        qmatch_abbrev_tac`bc_next bs0 bs1` >>
        `bc_fetch bs0 = SOME (Jump (Lab (cs.next_label + 1)))` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs0`] >>
          Q.PAT_ABBREV_TAC`ls:bc_inst list = X` >>
          qexists_tac`TAKE (LENGTH bc0 + 2 + LENGTH cc + 2) ls` >>
          simp[Abbr`ls`,SUM_APPEND,FILTER_APPEND,TAKE_APPEND1,TAKE_APPEND2] ) >>
        simp[bc_eval1_thm,bc_eval1_def,bc_find_loc_def,Abbr`bs0`,Abbr`bs1`,Abbr`bs5`,bc_state_component_equality] >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        REWRITE_TAC[GSYM APPEND_ASSOC] >>
        Q.PAT_ABBREV_TAC`ls:bc_inst list = bc0++X` >>
        qexists_tac`LENGTH ls - 1` >>
        simp[Abbr`ls`,EL_APPEND1,EL_APPEND2,EL_CONS,PRE_SUB1,ADD1,TAKE_APPEND1,TAKE_APPEND2,TAKE_LENGTH_ID_rwt] >>
        simp[SUM_APPEND,FILTER_APPEND] >>
        rpt(qpat_assum`bc_fetch A = X`kall_tac) >>
        rpt(qpat_assum`bc_next^* A X`kall_tac) >>
        rpt(qpat_assum`Cenv_bs a b c d e f`kall_tac) >>
        rpt(qpat_assum`Cv_bv a b f`kall_tac) >>
        unabbrev_all_tac >>
        simp[ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
        fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,between_def] >>
        fsrw_tac[DNF_ss,ARITH_ss][is_Label_rwt] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
      qmatch_assum_abbrev_tac`Cenv_bs rd' s2 env cenv (sz + 3) bs0` >>
      `Cenv_bs rd' s2 env cenv sz (bs0 with stack := DROP 3 bs0.stack)` by (
        match_mp_tac Cenv_bs_pops >>
        qexists_tac`TAKE 3 bs0.stack` >>
        simp[Abbr`bs0`] >>
        metis_tac[Cenv_bs_CTLet_bound]) >>
      fs[] >>
      match_mp_tac Cenv_bs_imp_incsz_irr >>
      HINT_EXISTS_TAC >>
      simp[bc_state_component_equality,Abbr`bs0`] ) >>
    rpt gen_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd (K (Label X::Y::Z)) U` >>
    Q.PAT_ABBREV_TAC`tt = TCTail X Y` >>
    qspecl_then[`CTLet(sz+1)::cenv`,`tt`,`sz+1`,`cs1`,`e2`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    simp[Abbr`cs1`,Abbr`cs0`,Once SWAP_REVERSE] >>
    strip_tac >>
    `bc_fetch bs = SOME (PushPtr (Lab cs.next_label))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0`>>simp[] ) >>
    `bc_next bs (bump_pc bs with stack := CodePtr (next_addr bs.inst_length (TAKE (LENGTH bc0 + 2 + LENGTH cc + 8) bs.code))::bs.stack)` by (
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[bc_state_component_equality,bc_find_loc_def] >>
      match_mp_tac bc_find_loc_aux_append_code >>
      match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
      qexists_tac`LENGTH bc0 + LENGTH cc + 10` >>
      simp[TAKE_APPEND1,TAKE_APPEND2,EL_APPEND1,EL_APPEND2,EL_CONS,PRE_SUB1,FILTER_APPEND,SUM_APPEND] >>
      fs[FILTER_REVERSE,ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
      fsrw_tac[DNF_ss][EVERY_MEM,between_def,MEM_FILTER,MEM_MAP] >>
      fsrw_tac[DNF_ss][is_Label_rwt] >>
      rpt(first_x_assum(qspec_then`rd`kall_tac)) >>
      rpt(qpat_assum`X.out = Y`kall_tac) >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][]) >>
    qmatch_assum_abbrev_tac`bc_next bs bs1` >>
    `bc_fetch bs1 = SOME PushExc` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs1`,bump_pc_def] >>
      qexists_tac`bc0 ++ [PushPtr (Lab cs.next_label)]` >>
      simp[FILTER_APPEND,SUM_APPEND] ) >>
    `bc_next bs1 (bump_pc bs1 with <| stack := StackPtr bs.handler::bs1.stack; handler := LENGTH bs1.stack |>)` by (
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[bc_state_component_equality] >>
      simp[Abbr`bs1`,bump_pc_def]) >>
    qmatch_assum_abbrev_tac`bc_next bs1 bs2` >>
    `bc_next^* bs bs2` by metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
    pop_assum mp_tac >>
    simp[Abbr`bs2`,bump_pc_def,Abbr`bs1`,ADD1] >>
    rpt(qpat_assum`bc_next X Y`kall_tac) >>
    rpt(qpat_assum`bc_fetch X = Y`kall_tac) >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs bss0` >>
    qmatch_assum_abbrev_tac`(compile cenv TCNonTail (sz + 2) cs0 exp).out = cc ++ cs0.out` >>
    first_x_assum(qspecl_then[`rd`,`cs0`,`cenv`,`sz+2`,`bss0`,`bce`,`bcr`,`TAKE (LENGTH bc0+2) bs.code`,`REVERSE cc`
                             ,`DROP (LENGTH bc0+2+LENGTH cc) bs.code`]mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`bss0`] >>
      simp[SUM_APPEND,FILTER_APPEND,Abbr`cs0`,TAKE_APPEND1,TAKE_APPEND2,DROP_APPEND1,DROP_APPEND2,DROP_LENGTH_NIL_rwt] >>
      conj_tac >- (
        SUBST1_TAC(DECIDE``sz + 2 = (sz + 1) + 1``) >>
        qmatch_abbrev_tac`Cenv_bs rd s eenv cenv (sz + 1 + 1) bs0` >>
        match_mp_tac Cenv_bs_imp_incsz >>
        qexists_tac`bs0 with stack := TL bs0.stack` >>
        simp[Abbr`bs0`,bc_state_component_equality] >>
        qmatch_abbrev_tac`Cenv_bs rd s eenv cenv (sz + 1) bs0` >>
        match_mp_tac Cenv_bs_imp_incsz >>
        qexists_tac`bs0 with stack := TL bs0.stack` >>
        simp[Abbr`bs0`,bc_state_component_equality] >>
        qpat_assum`bc_next^* X Y`kall_tac >>
        match_mp_tac Cenv_bs_with_irr >>
        qexists_tac`bs with code := bce` >>
        simp[] >> rw[]) >>
      fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt] >>
      rw[] >> res_tac >> simp[] ) >>
    disch_then(mp_tac o CONJUNCT1) >>
    simp[Abbr`bss0`,TAKE_APPEND1,TAKE_APPEND2] >>
    simp[code_for_push_def,code_for_return_def] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac[`rf`,`rd'`,`ck`,`gvv`,`bv`] >>
    strip_tac >>
    map_every qexists_tac[`bv`,`rf`,`rd'`,`ck`,`gvv`] >>
    conj_tac >- (
      qmatch_assum_abbrev_tac`bc_next^* bs2 bs3` >>
      qmatch_abbrev_tac`bc_next^* bss bs5` >>
      qmatch_assum_abbrev_tac`bc_next^* bss bss0` >>
      `(bs2 with code := bss0.code) = bss0` by (
        simp[bc_state_component_equality,Abbr`bs2`,Abbr`bss0`,Abbr`bss`,TAKE_APPEND1,TAKE_APPEND2] ) >>
      `bc_next^* bss0 (bs3 with code := bss0.code)` by (
        match_mp_tac RTC_bc_next_append_code >>
        map_every qexists_tac[`bs2`,`bs3`] >>
        rw[] >>
        simp[Abbr`bs2`,Abbr`bs3`,Abbr`bss0`,Abbr`bss`,bc_state_component_equality,TAKE_APPEND1,TAKE_APPEND2] ) >>
      match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
      qexists_tac`bss0` >> simp[] >>
      match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
      HINT_EXISTS_TAC >> simp[] >>
      match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
      qexists_tac`bs3 with <| pc := next_addr bs.inst_length (TAKE (LENGTH bc0 + LENGTH cc + 4) bss.code);
                              code := bss.code;
                              handler := bs.handler;
                              stack := bv::(DROP 3 bs3.stack)|>` >>
      reverse conj_tac >- (
        match_mp_tac retbc_thm >>
        simp[Abbr`bs3`,bc_state_component_equality,Abbr`bs5`,Abbr`bss`] >>
        simp[TAKE_APPEND1,TAKE_APPEND2] >>
        Q.PAT_ABBREV_TAC`bc00 = bc0 ++ X::Y::(Z++A)` >>
        qexists_tac`bc00` >>
        simp[Abbr`bc00`] >>
        qexists_tac`blvs` >>
        simp[] >> fs[EVERY2_EVERY] ) >>
      simp[RTC_eq_NRC] >>
      qexists_tac`SUC(SUC 0)` >>
      simp[NRC] >>
      qho_match_abbrev_tac`∃bs1. bc_next bs0 bs1 ∧ P bs1` >>
      `bc_fetch bs0 = SOME PopExc` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs0`,Abbr`bs3`,Abbr`bss0`,Abbr`bss`] >>
        qexists_tac`bc0++[PushPtr(Lab cs.next_label);PushExc]++REVERSE cc` >>
        simp[] ) >>
      simp[bc_eval1_thm,bc_eval1_def,Abbr`bs0`,Abbr`bs3`,Abbr`bss0`,EL_APPEND1,EL_APPEND2,bump_pc_def] >>
      simp[Abbr`P`,Abbr`bss`] >>
      qho_match_abbrev_tac`bc_next bs0 bs1` >>
      `bc_fetch bs0 = SOME (Stack (Pops 1))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs0`] >>
        Q.PAT_ABBREV_TAC`ls:bc_inst list = X` >>
        qexists_tac`TAKE (LENGTH bc0 + 2 + LENGTH cc + 1) ls` >>
        simp[Abbr`ls`,SUM_APPEND,FILTER_APPEND,TAKE_APPEND2,TAKE_APPEND1] ) >>
      simp[bc_eval1_def,bc_eval1_thm,Abbr`bs0`,bc_eval_stack_def,bump_pc_def] >>
      simp[bc_state_component_equality,Abbr`bs1`,TAKE_APPEND1,TAKE_APPEND2] >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    fs[] >>
    match_mp_tac s_refs_with_irr >>
    fs[Cenv_bs_def] >>
    HINT_EXISTS_TAC >>
    simp[] ) >>
  strip_tac >- (
    simp[compile_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_result_out_fupd (K (PushExc::Y::Z)) U` >>
    qspecl_then[`cenv`,`TCNonTail`,`sz + 2`,`cs0`,`exp`](Q.X_CHOOSE_THEN`cc`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    simp[pushret_def] >>
    strip_tac >>
    reverse(Cases_on`ALL_DISTINCT (FILTER is_Label (bc0 ++ code)) ∧
                     ∃cc1 cc2. code = [PushPtr(Lab cs.next_label);PushExc]++REVERSE cc++PopExc::Stack(Pops 1)::cc1++Label cs.next_label::cc2`) >- (
      conj_tac >- (
        Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd (K (Label X::Y::Z)) U` >>
        qspecl_then[`cenv`,`TCNonTail`,`sz`,`exp'`,`0`,`cs1`,`1`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 (CONJUNCT2 compile_append_out)) >>
        simp[Abbr`cs1`,Abbr`cs0`,Once SWAP_REVERSE] >>
        rw[] >> fs[] >> fs[MEM_SING_APPEND] >>
        qsuff_tac`F`>-rw[] >>
        qpat_assum`¬ALL_DISTINCT X`mp_tac >>
        simp[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
        fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,between_def,is_Label_rwt] >>
        rpt (first_x_assum(qspec_then`rd`kall_tac)) >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
      conj_tac >- (
        rpt gen_tac >>
        Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd (K (Label X::Y::Z)) U` >>
        Q.PAT_ABBREV_TAC`tt:call_context = X` >>
        qspecl_then[`cenv`,`tt`,`sz`,`exp'`,`0`,`cs1`,`1`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 (CONJUNCT2 compile_append_out)) >>
        simp[Abbr`cs1`,Abbr`cs0`,Once SWAP_REVERSE] >>
        rw[] >> fs[] >> fs[MEM_SING_APPEND] >>
        qsuff_tac`F`>-rw[] >>
        qpat_assum`¬ALL_DISTINCT X`mp_tac >>
        simp[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
        fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,between_def,is_Label_rwt] >>
        rpt (first_x_assum(qspec_then`rd`kall_tac)) >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
      rpt gen_tac >>
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd (K (Label X::Y::Z)) U` >>
      qspecl_then[`cenv`,`t`,`sz`,`exp'`,`0`,`cs1`,`1`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 (CONJUNCT2 compile_append_out)) >>
      simp[Abbr`cs1`,Abbr`cs0`] >>
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd (K X) U` >>
      qspecl_then[`t`,`cs1`](Q.X_CHOOSE_THEN`cp`strip_assume_tac)pushret_append_out >> pop_assum kall_tac >>
      simp[Abbr`cs1`,Once SWAP_REVERSE] >>
      rw[] >> fs[] >> fs[MEM_SING_APPEND] >>
      qsuff_tac`F`>-rw[] >>
      qpat_assum`¬ALL_DISTINCT X`mp_tac >>
      simp[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
      fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,between_def,is_Label_rwt] >>
      rpt (first_x_assum(qspec_then`rd`kall_tac)) >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
    pop_assum strip_assume_tac >>
    `bc_fetch bs = SOME (PushPtr (Lab cs.next_label))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0`>>simp[] ) >>
    `bc_next bs (bump_pc bs with stack := CodePtr (next_addr bs.inst_length (TAKE (LENGTH bc0 + 2 + LENGTH cc + 2 + LENGTH cc1) bs.code))::bs.stack)` by (
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[bc_state_component_equality,bc_find_loc_def] >>
      match_mp_tac bc_find_loc_aux_append_code >>
      match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
      qexists_tac`LENGTH bc0 + LENGTH cc + LENGTH cc1 + 4` >>
      simp[EL_APPEND1,EL_APPEND2,EL_CONS,PRE_SUB1,ADD1] >>
      simp[TAKE_APPEND1,TAKE_APPEND2] >>
      reverse conj_tac >- simp[FILTER_APPEND,SUM_APPEND] >>
      qmatch_abbrev_tac`ALL_DISTINCT (FILTER is_Label xxx)` >>
      qsuff_tac`xxx = bc0 ++ code`>-PROVE_TAC[] >>
      simp[Abbr`xxx`]) >>
    qmatch_assum_abbrev_tac`bc_next bs bs1` >>
    `bc_fetch bs1 = SOME PushExc` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs1`,bump_pc_def] >>
      qexists_tac`bc0 ++ [PushPtr (Lab cs.next_label)]` >>
      simp[FILTER_APPEND,SUM_APPEND] ) >>
    `bc_next bs1 (bump_pc bs1 with <| stack := StackPtr bs.handler::bs1.stack; handler := LENGTH bs1.stack |>)` by (
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[bc_state_component_equality] >>
      simp[Abbr`bs1`,bump_pc_def]) >>
    qmatch_assum_abbrev_tac`bc_next bs1 bs2` >>
    `bc_next^* bs bs2` by metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
    pop_assum mp_tac >>
    simp[Abbr`bs2`,bump_pc_def,Abbr`bs1`,ADD1] >>
    rpt(qpat_assum`bc_next X Y`kall_tac) >>
    rpt(qpat_assum`bc_fetch X = Y`kall_tac) >>
    Q.PAT_ABBREV_TAC`aa = next_addr bs.inst_length X` >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs bss0` >>
    last_x_assum(qspecl_then[`rd`,`cs0`,`cenv`,`sz+2`,`bss0`,`bce`,`bcr`,`bc0++(TAKE 2 code)`,`REVERSE cc`,`(DROP (2 + LENGTH cc) code) ++ bc1`]mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`bss0`,DROP_APPEND1,DROP_LENGTH_NIL_rwt] >>
      simp[SUM_APPEND,FILTER_APPEND,Abbr`cs0`] >>
      conj_tac >- (
        SUBST1_TAC(DECIDE``sz + 2 = (sz + 1) + 1``) >>
        qmatch_abbrev_tac`Cenv_bs rd s env cenv (sz + 1 + 1) bs0` >>
        match_mp_tac Cenv_bs_imp_incsz >>
        qexists_tac`bs0 with stack := TL bs0.stack` >>
        simp[Abbr`bs0`,bc_state_component_equality] >>
        qmatch_abbrev_tac`Cenv_bs rd s env cenv (sz + 1) bs0` >>
        match_mp_tac Cenv_bs_imp_incsz >>
        qexists_tac`bs0 with stack := TL bs0.stack` >>
        simp[Abbr`bs0`,bc_state_component_equality] >>
        match_mp_tac Cenv_bs_with_irr >>
        HINT_EXISTS_TAC >> simp[] ) >>
      fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt] >>
      rpt(qpat_assum`∀rd cs. P`kall_tac) >>
      rw[] >> res_tac >> simp[] ) >>
    disch_then(qspec_then`TCNonTail`mp_tac) >> simp[] >>
    disch_then(qspecl_then[`[]`,`bs.handler`,`aa`,`bs.stack`]mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`bss0`,TAKE_APPEND1,TAKE_APPEND2] >> fs[Cenv_bs_def]) >>
    disch_then(mp_tac o SIMP_RULE(srw_ss())[LET_THM,code_for_return_def]) >>
    disch_then(qx_choosel_then[`bv`,`rf`,`rd'`]strip_assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bss0 bs2` >>
    `bc_next^* bs bs2` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
    qpat_assum`bc_next^* bs bss0`kall_tac >>
    qpat_assum`bc_next^* bss0 bs2`kall_tac >>
    `all_vlabs_csg s' ∧ all_vlabs v ∧
     EVERY (code_env_cd bce) (free_labs (SUC (LENGTH env)) exp') ∧
     (∀cd. cd ∈ vlabs_list (store_vs (SND (FST s'))) ⇒ code_env_cd bce cd) ∧
     (∀cd. cd ∈ vlabs v ∨ cd ∈ vlabs_list env ⇒ code_env_cd bce cd) ∧
     (∀cd. cd ∈ vlabs_list (MAP THE (FILTER IS_SOME (SND s'))) ⇒ code_env_cd bce cd) ∧
     set (free_vars exp') ⊆ count (LENGTH (CTLet(sz+1)::cenv)) ∧
     Cenv_bs rd' s' (v::env) (CTLet(sz+1)::cenv) (sz+1) (bs2 with code := bce)` by (
      qspecl_then[`s`,`env`,`exp`,`s',Rerr(Rraise v)`]mp_tac(CONJUNCT1 Cevaluate_store_SUBSET) >>
      qspecl_then[`s`,`env`,`exp`,`s',Rerr(Rraise v)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
      qspecl_then[`s`,`env`,`exp`,`s',Rerr(Rraise v)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
      simp[] >> ntac 3 strip_tac >>
      first_x_assum(qspec_then`rd`kall_tac) >>
      simp[ADD1] >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF,vlabs_csg_def] >>
        metis_tac[EVERY_MEM] ) >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF,vlabs_csg_def] >>
        metis_tac[EVERY_MEM] ) >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF,vlabs_csg_def] >>
        metis_tac[EVERY_MEM] ) >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      match_mp_tac Cenv_bs_FUPDATE >>
      qexists_tac`bs2 with <| stack := bs.stack; code := bce|>` >>
      simp[bc_state_component_equality,Abbr`bs2`] >>
      match_mp_tac Cenv_bs_change_store >>
      map_every qexists_tac [`rd`,`s`,`bs with <| pc := aa; code := bce|>`,`rf`] >>
      simp[Abbr`bss0`,bc_state_component_equality] >>
      fs[s_refs_def,good_rd_def] >>
      match_mp_tac Cenv_bs_with_irr >>
      qexists_tac`bs with code := bce`>>simp[] ) >>
    fs[] >>
    conj_tac >- (
      REWRITE_TAC[ONE] >>
      simp[compile_def] >>
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd A B` >>
      Q.PAT_ABBREV_TAC`tt:call_context = A` >>
      qspecl_then[`CTLet(sz+1)::cenv`,`tt`,`sz+1`,`cs1`,`exp'`](Q.X_CHOOSE_THEN`cd`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      gen_tac >> simp[Abbr`cs1`,Abbr`cs0`] >>
      SUBST1_TAC(Q.prove(`REVERSE cc2 ++ [Label cs.next_label] ++ REVERSE cc1 = REVERSE(cc1++Label cs.next_label::cc2)`,lrw[])) >>
      REWRITE_TAC[Once SWAP_REVERSE] >>
      simp[] >> strip_tac >>
      qpat_assum`(A.out = cd ++ B)`mp_tac >>
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd A B` >> strip_tac >>
      `cc1 = [Jump (Lab (cs.next_label + 1))] ∧
       cc2 = REVERSE cd ++ [Stack (Pops 1); Label (cs.next_label + 1)]` by (
         match_mp_tac MEM_APPEND_lemma >>
         qexists_tac`Label cs.next_label` >>
         simp[] >>
         fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER] ) >>
      first_x_assum(qspecl_then[`rd'`,`cs1`,`CTLet (sz+1)::cenv`,`sz+1`,`bs2`,`bce`,`bcr`
                               ,`TAKE(LENGTH bc0+2+LENGTH cc+2+LENGTH cc1+1)bs.code`
                               ,`REVERSE cd`,`[Stack (Pops 1); Label (cs.next_label+1)]++bc1`]mp_tac) >>
      discharge_hyps >- (
        `bs2.clock = SOME (FST (FST s'))` by (
          imp_res_tac RTC_bc_next_clock_less >>
          rfs[optionTheory.OPTREL_def] >>
          fs[Cenv_bs_def,s_refs_def,Abbr`bs2`,Abbr`bss0`]) >>
        simp[TAKE_APPEND1,TAKE_APPEND2,Abbr`bs2`,Abbr`bss0`,Abbr`aa`] >>
        conj_tac >- PROVE_TAC[] >>
        fs[SUM_APPEND,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,EVERY_REVERSE] >>
        fsrw_tac[DNF_ss][MEM_FILTER,EVERY_MEM,is_Label_rwt,ALL_DISTINCT_REVERSE,MEM_MAP,between_def] >>
        fsrw_tac[ARITH_ss][Abbr`cs1`] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      simp[] >>
      disch_then(mp_tac o CONJUNCT1) >>
      simp[code_for_push_def] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      map_every qx_gen_tac[`rf'`,`rd''`,`ck'`,`gvv`,`br`] >>
      strip_tac >>
      map_every qexists_tac[`rf'`,`rd''`,`ck'`,`gvv`,`br`] >>
      conj_tac >- (
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        qexists_tac`bs2` >> simp[] >>
        qmatch_assum_abbrev_tac`bc_next^* bs2 bs4` >>
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        HINT_EXISTS_TAC >> simp[] >>
        fs[Abbr`bs4`] >>
        simp[Abbr`bs2`,Abbr`bss0`] >>
        ntac 5 (pop_assum kall_tac) >> rw[] >>
        ntac 9 (pop_assum kall_tac) >>
        match_mp_tac RTC_SUBSET >>
        qmatch_abbrev_tac`bc_next bs1 bs2` >>
        `bc_fetch bs1 = SOME (Stack (Pops 1))` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs1`] >>
          CONV_TAC SWAP_EXISTS_CONV >>
          qexists_tac`Label (cs.next_label + 1)::(bc1)` >>
          simp[TAKE_APPEND1,TAKE_APPEND2,SUM_APPEND,FILTER_APPEND] ) >>
        simp[bc_eval1_thm,bc_eval1_def,Abbr`bs1`,bump_pc_def,bc_eval_stack_def] >>
        simp[Abbr`bs2`,bc_state_component_equality] >>
        simp[SUM_APPEND,FILTER_APPEND,TAKE_APPEND1,TAKE_APPEND2] ) >>
      fs[Abbr`bs2`,Abbr`bss0`] >>
      reverse conj_tac >- metis_tac[IS_PREFIX_TRANS,SUBMAP_TRANS,gvrel_trans] >>
      match_mp_tac Cenv_bs_imp_incsz_irr >>
      qexists_tac`bs with <| refs := rf'; clock := ck'; code := bce; globals := gvv|>` >>
      simp[bc_state_component_equality] >>
      match_mp_tac Cenv_bs_pops >>
      qexists_tac`[br;bv]` >> simp[] >>
      reverse conj_tac >- (
        metis_tac[Cenv_bs_CTLet_bound]) >>
      match_mp_tac Cenv_bs_with_irr >>
      qmatch_assum_abbrev_tac`Cenv_bs rd'' s'' (v::env) (CTLet(sz+1)::cenv) (sz+2) bs0` >>
      qexists_tac`bs0` >>
      simp[Abbr`bs0`,bc_state_component_equality] >>
      `env = TL (v::env) ∧ cenv = TL (CTLet (sz+1)::cenv)` by simp[] >>
      ntac 2 (pop_assum SUBST1_TAC) >>
      match_mp_tac Cenv_bs_DOMSUB >> simp[] >>
      match_mp_tac Cenv_bs_with_irr >>
      HINT_EXISTS_TAC >> simp[]) >>
    conj_tac >- (
      REWRITE_TAC[ONE] >>
      simp[compile_def] >>
      rpt gen_tac >>
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd A B` >>
      Q.PAT_ABBREV_TAC`tt:call_context = A` >>
      qspecl_then[`CTLet(sz+1)::cenv`,`tt`,`sz+1`,`cs1`,`exp'`](Q.X_CHOOSE_THEN`cd`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      simp[Abbr`cs1`,Abbr`cs0`] >>
      SUBST1_TAC(Q.prove(`REVERSE cc2 ++ [Label cs.next_label] ++ REVERSE cc1 = REVERSE(cc1++Label cs.next_label::cc2)`,lrw[])) >>
      REWRITE_TAC[Once SWAP_REVERSE] >>
      simp[] >> strip_tac >>
      qpat_assum`(A.out = cd ++ B)`mp_tac >>
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd A B` >> strip_tac >>
      qmatch_assum_abbrev_tac`cc1 ++ [lab] ++ cc2 = co` >>
      `cc1 = TAKE 6 co ∧
       cc2 = DROP 7 co` by (
         match_mp_tac MEM_APPEND_lemma >>
         qexists_tac`lab` >>
         simp[Abbr`co`] >>
         fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,Abbr`lab`] ) >>
      first_x_assum(qspecl_then[`rd'`,`cs1`,`CTLet (sz+1)::cenv`,`sz+1`,`bs2`,`bce`,`bcr`
                               ,`TAKE(LENGTH bc0+2+LENGTH cc+2+LENGTH cc1+1)bs.code`
                               ,`REVERSE cd`,`[Label (cs.next_label+1)]++bc1`]mp_tac) >>
      discharge_hyps >- (
        `bs2.clock = SOME (FST (FST s'))` by (
          imp_res_tac RTC_bc_next_clock_less >>
          fs[optionTheory.OPTREL_def,s_refs_def,Abbr`bs2`,Abbr`bss0`] >> rfs[] ) >>
        simp[TAKE_APPEND1,TAKE_APPEND2,Abbr`bs2`,Abbr`bss0`,Abbr`aa`,Abbr`co`] >>
        conj_tac >- PROVE_TAC[] >>
        fs[SUM_APPEND,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,EVERY_REVERSE,Abbr`lab`] >>
        fsrw_tac[DNF_ss][MEM_FILTER,EVERY_MEM,is_Label_rwt,ALL_DISTINCT_REVERSE,MEM_MAP,between_def] >>
        fsrw_tac[ARITH_ss][Abbr`cs1`] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      simp[] >>
      disch_then(qspecl_then[`env0`,`vs`,`v::klvs`,`bv::blvs`,`benv`,`ret`,`args`,`cl`,`st`]mp_tac o CONJUNCT2) >>
      fs[Abbr`tt`,ADD1,Abbr`bs2`] >>
      discharge_hyps >- (
        fs[Abbr`bss0`] >>
        fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
        rw[] >>
        match_mp_tac(MP_CANON (GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
        simp[] >>
        qexists_tac`rd` >>
        simp[DRESTRICT_SUBSET_SUBMAP] >>
        fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,SUBMAP_DEF,DRESTRICT_DEF,UNCURRY]) >>
      simp[code_for_return_def] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      map_every qx_gen_tac[`br`,`rf'`,`rd''`,`ck'`,`gvv`] >>
      strip_tac >>
      map_every qexists_tac[`br`,`rf'`,`rd''`,`ck'`,`gvv`] >>
      conj_tac >- (
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        qmatch_assum_abbrev_tac`bc_next^* bs bs2` >>
        qexists_tac`bs2` >> simp[] >>
        qmatch_assum_abbrev_tac`bc_next^* bs2 bs4` >>
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        HINT_EXISTS_TAC >> simp[] >>
        fs[Abbr`bs4`] >>
        simp[Abbr`bs2`,Abbr`bss0`] ) >>
      fs[Abbr`bss0`] >>
      metis_tac[IS_PREFIX_TRANS,SUBMAP_TRANS,gvrel_trans]) >>
    rpt gen_tac >>
    Q.PAT_ABBREV_TAC`cs2 = compiler_result_out_fupd (K (Stack X::Y)) B` >>
    qspecl_then[`t`,`cs2`](Q.X_CHOOSE_THEN`cp`strip_assume_tac)pushret_append_out >> pop_assum kall_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
    qspecl_then[`cenv`,`t`,`sz`,`exp'`,`0`,`cs1`,`1`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 (CONJUNCT2 compile_append_out)) >>
    simp[Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
    SUBST1_TAC(Q.prove(`REVERSE cc2 ++ [Label cs.next_label] ++ REVERSE cc1 = REVERSE(cc1++Label cs.next_label::cc2)`,lrw[])) >>
    REWRITE_TAC[Once SWAP_REVERSE] >>
    simp[] >> strip_tac >>
    qpat_assum`(A.out = cb ++ B)`mp_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd A B` >> strip_tac >>
    `cc1 = REVERSE cp ++ [Jump (Lab (cs.next_label + 1))] ∧
     cc2 = REVERSE cb ++ [Label (cs.next_label + 1)]` by (
       match_mp_tac MEM_APPEND_lemma >>
       qexists_tac`Label (cs.next_label)` >>
       simp[] >>
       fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER] ) >>
    qabbrev_tac`tt = case t of TCNonTail => t | TCTail j k => TCTail j (k + 1)` >>
    qspecl_then[`CTLet(sz+1)::cenv`,`tt`,`sz+1`,`cs1`,`exp'`](Q.X_CHOOSE_THEN`cd`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    first_x_assum(qspecl_then[`rd'`,`cs1`,`CTLet (sz+1)::cenv`,`sz+1`,`bs2`,`bce`,`bcr`
                             ,`TAKE(LENGTH bc0+2+LENGTH cc+2+LENGTH cc1+1)bs.code`
                             ,`REVERSE cd`,`(DROP (LENGTH cd) cc2)++bc1`]mp_tac) >>
    discharge_hyps >- (
      `bs2.clock = SOME (FST (FST s'))` by (
        imp_res_tac RTC_bc_next_clock_less >>
        fs[optionTheory.OPTREL_def,s_refs_def,Abbr`bs2`,Abbr`bss0`] >> rfs[] ) >>
      simp[TAKE_APPEND1,TAKE_APPEND2,Abbr`bs2`,Abbr`bss0`,Abbr`aa`] >>
      conj_asm1_tac >- (
        qpat_assum`X = cb ++ cs1.out`mp_tac >>
        REWRITE_TAC[ONE] >>
        Cases_on`t`>>simp[compile_def,Abbr`tt`] >>
        fs[] >> rw[] >> simp[DROP_APPEND1,DROP_APPEND2,DROP_LENGTH_NIL_rwt] ) >>
      conj_tac >- PROVE_TAC[] >>
      fs[s_refs_def,SUM_APPEND,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,EVERY_REVERSE] >>
      fsrw_tac[DNF_ss][MEM_FILTER,EVERY_MEM,is_Label_rwt,ALL_DISTINCT_REVERSE,MEM_MAP,between_def] >>
      fsrw_tac[ARITH_ss][Abbr`cs1`] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
    simp[] >>
    disch_then(qspec_then`tt`mp_tac) >> simp[] >>
    reverse(Cases_on`err`)>>simp[]>-(
      simp[Abbr`tt`] >>
      Cases_on`t`>>simp[] >- (
        `bs2.output = bs.output` by simp[Abbr`bs2`,Abbr`bss0`] >>
        metis_tac[RTC_TRANSITIVE,transitive_def])>>
      strip_tac >> strip_tac >>
      qpat_assum`p ⇒ q`mp_tac >>
      discharge_hyps >- (
        simp[Abbr`bs2`] >>
        qexists_tac`bv::blvs`>>simp[] >>
        qexists_tac`args`>>simp[] ) >>
      `bs2.output = bs.output` by simp[Abbr`bs2`,Abbr`bss0`] >>
      metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
    strip_tac >> rpt gen_tac >> strip_tac >>
    first_x_assum(qspecl_then[`bv::ig`,`sp`,`hdl`,`st`]mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`bs2`] >>
      simp[Abbr`tt`] >>
      Cases_on`t`>>fs[] >>
      qexists_tac`bv::blvs`>>simp[] >>
      qexists_tac`args`>>simp[] ) >>
    simp[code_for_return_def] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac[`br`,`rf'`,`rd''`,`ck'`,`gvv`] >>
    strip_tac >>
    map_every qexists_tac[`br`,`rf'`,`rd''`,`ck'`,`gvv`] >>
    conj_tac >- (
      match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
      qmatch_assum_abbrev_tac`bc_next^* bs bs2` >>
      qexists_tac`bs2` >> simp[] >>
      qmatch_assum_abbrev_tac`bc_next^* bs2 bs4` >>
      qspecl_then[`cenv`,`t`,`sz`,`exp'`,`0`,`cs1`,`1`,`cb`,`cd`]mp_tac compile_bindings_thm >>
      simp[] >> strip_tac >>
      match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
      HINT_EXISTS_TAC >> simp[] >>
      fs[Abbr`bs4`] >>
      simp[Abbr`bs2`,Abbr`bss0`] ) >>
    fs[Abbr`bss0`,Abbr`bs2`] >>
    metis_tac[IS_PREFIX_TRANS,SUBMAP_TRANS,gvrel_trans]) >>
  strip_tac >- (
    simp[compile_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_result_out_fupd (K (PushExc::Y::Z)) U` >>
    qspecl_then[`cenv`,`TCNonTail`,`sz + 2`,`cs0`,`exp`](Q.X_CHOOSE_THEN`cc`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    simp[pushret_def] >>
    strip_tac >>
    reverse(Cases_on`ALL_DISTINCT (FILTER is_Label (bc0 ++ code)) ∧
                     ∃cc1 cc2. code = [PushPtr(Lab cs.next_label);PushExc]++REVERSE cc++PopExc::Stack(Pops 1)::cc1++Label cs.next_label::cc2`) >- (
      rpt gen_tac >>
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd (K (Label X::Y::Z)) U` >>
      qspecl_then[`cenv`,`t`,`sz`,`e2`,`0`,`cs1`,`1`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 (CONJUNCT2 compile_append_out)) >>
      simp[Abbr`cs1`,Abbr`cs0`] >>
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd (K X) U` >>
      qspecl_then[`t`,`cs1`](Q.X_CHOOSE_THEN`cp`strip_assume_tac)pushret_append_out >> pop_assum kall_tac >>
      simp[Abbr`cs1`,Once SWAP_REVERSE] >>
      rw[] >> fs[] >> fs[MEM_SING_APPEND] >>
      qsuff_tac`F`>-rw[] >>
      qpat_assum`¬ALL_DISTINCT X`mp_tac >>
      simp[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
      fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,between_def,is_Label_rwt] >>
      rpt (first_x_assum(qspec_then`rd`kall_tac)) >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
    pop_assum strip_assume_tac >>
    `bc_fetch bs = SOME (PushPtr (Lab cs.next_label))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0`>>simp[] ) >>
    `bc_next bs (bump_pc bs with stack := CodePtr (next_addr bs.inst_length (TAKE (LENGTH bc0 + 2 + LENGTH cc + 2 + LENGTH cc1) bs.code))::bs.stack)` by (
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[bc_state_component_equality,bc_find_loc_def] >>
      match_mp_tac bc_find_loc_aux_append_code >>
      match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
      qexists_tac`LENGTH bc0 + LENGTH cc + LENGTH cc1 + 4` >>
      simp[EL_APPEND1,EL_APPEND2,EL_CONS,PRE_SUB1,ADD1] >>
      simp[TAKE_APPEND1,TAKE_APPEND2] >>
      reverse conj_tac >- simp[FILTER_APPEND,SUM_APPEND] >>
      qmatch_abbrev_tac`ALL_DISTINCT (FILTER is_Label xxx)` >>
      qsuff_tac`xxx = bc0 ++ code`>-PROVE_TAC[] >>
      simp[Abbr`xxx`]) >>
    qmatch_assum_abbrev_tac`bc_next bs bs1` >>
    `bc_fetch bs1 = SOME PushExc` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs1`,bump_pc_def] >>
      qexists_tac`bc0 ++ [PushPtr (Lab cs.next_label)]` >>
      simp[FILTER_APPEND,SUM_APPEND] ) >>
    `bc_next bs1 (bump_pc bs1 with <| stack := StackPtr bs.handler::bs1.stack; handler := LENGTH bs1.stack |>)` by (
      simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
      simp[bc_state_component_equality] >>
      simp[Abbr`bs1`,bump_pc_def]) >>
    qmatch_assum_abbrev_tac`bc_next bs1 bs2` >>
    `bc_next^* bs bs2` by metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
    pop_assum mp_tac >>
    simp[Abbr`bs2`,bump_pc_def,Abbr`bs1`,ADD1] >>
    rpt(qpat_assum`bc_next X Y`kall_tac) >>
    rpt(qpat_assum`bc_fetch X = Y`kall_tac) >>
    Q.PAT_ABBREV_TAC`aa = next_addr bs.inst_length X` >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs bss0` >>
    last_x_assum(qspecl_then[`rd`,`cs0`,`cenv`,`sz+2`,`bss0`,`bce`,`bcr`,`bc0++(TAKE 2 code)`,`REVERSE cc`,`(DROP (2 + LENGTH cc) code) ++ bc1`]mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`bss0`,DROP_APPEND1,DROP_LENGTH_NIL_rwt] >>
      simp[SUM_APPEND,FILTER_APPEND,Abbr`cs0`] >>
      conj_tac >- (
        SUBST1_TAC(DECIDE``sz + 2 = (sz + 1) + 1``) >>
        qmatch_abbrev_tac`Cenv_bs rd s env cenv (sz + 1 + 1) bs0` >>
        match_mp_tac Cenv_bs_imp_incsz >>
        qexists_tac`bs0 with stack := TL bs0.stack` >>
        simp[Abbr`bs0`,bc_state_component_equality] >>
        qmatch_abbrev_tac`Cenv_bs rd s env cenv (sz + 1) bs0` >>
        match_mp_tac Cenv_bs_imp_incsz >>
        qexists_tac`bs0 with stack := TL bs0.stack` >>
        simp[Abbr`bs0`,bc_state_component_equality] >>
        match_mp_tac Cenv_bs_with_irr >>
        HINT_EXISTS_TAC >> simp[] ) >>
      fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt] >>
      rpt(qpat_assum`∀rd cs. P`kall_tac) >>
      rw[] >> res_tac >> simp[] ) >>
    Cases_on`err`>>simp[] >>
    disch_then(qspec_then`TCNonTail`mp_tac) >>
    simp[] >> rw[] >>
    qpat_assum`bc_next^* bs bss0`mp_tac >>
    `bss0.output = bs.output`by simp[Abbr`bss0`] >>
    simp[Abbr`bss0`] >>
    metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
  strip_tac >- (
    ntac 2 gen_tac >> qx_gen_tac`n` >> strip_tac >> simp[] >>
    rpt gen_tac >> strip_tac >> simp[compile_def,pushret_def] >>
    qpat_assum`bce ++ bcr = X`kall_tac>>
    qpat_assum`bs.code = X`mp_tac >> simp[IMP_CONJ_THM] >>
    map_every qid_spec_tac[`code`,`bc1`] >> simp[FORALL_AND_THM] >>
    conj_asm1_tac >- (
      ntac 2 gen_tac >>
      fs[code_for_push_def,Cenv_bs_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,env_renv_def] >>
      fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >> rfs[] >>
      pop_assum mp_tac >>
      first_assum(qspec_then `n` mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
      REWRITE_TAC[Once option_case_NONE_F] >> simp[EL_ZIP] >>
      disch_then(Q.X_CHOOSE_THEN`x`strip_assume_tac) >>
      strip_tac >>
      imp_res_tac Cv_bv_not_env >> strip_tac >>
      strip_tac >>
      map_every qexists_tac [`[x]`,`bs.refs`,`rd`,`bs.clock`,`bs.globals`] >> rw[s_refs_with_stack] >- (
        match_mp_tac compile_varref_thm >> fs[] >>
        simp[bc_state_component_equality] >>
        rfs[el_check_def] >>
        metis_tac[APPEND_NIL])
      >- (
        qmatch_assum_rename_tac `z < LENGTH cenv`[] >>
        qmatch_abbrev_tac`X` >>
        qpat_assum`∀x y z. X ⇒ Y`(qspec_then `z` mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
        simp[option_case_NONE_F,EL_ZIP] >> rw[] >>
        qunabbrev_tac`X` >>
        imp_res_tac lookup_ct_imp_incsz >>
        rfs[EL_ZIP]) >>
      fs[s_refs_def,good_rd_def]) >>
    rw[] >> fs[] >>
    match_mp_tac code_for_push_return >>
    rfs[el_check_def] >>
    qspecl_then[`sz`,`cs`,`EL n cenv`]strip_assume_tac compile_varref_append_out >> fs[] >>
    first_x_assum(qspec_then`REVERSE bc`mp_tac o CONV_RULE SWAP_FORALL_CONV) >> simp[] >>
    fs[Once SWAP_REVERSE] >> strip_tac >>
    qmatch_assum_abbrev_tac `code_for_push rd bs bce bc0 ccode s renv v cenv rsz` >>
    map_every qexists_tac [`bc0`,`ccode`,`renv`,`cenv`,`rsz`] >>
    simp[] >>
    qexists_tac `REVERSE args` >> fsrw_tac[ARITH_ss][EVERY2_EVERY]) >>
  strip_tac >- (
    ntac 2 gen_tac >> qx_gen_tac`n` >> gen_tac >> strip_tac >> simp[] >> strip_tac >>
    rpt gen_tac >> strip_tac >> simp[compile_def,pushret_def] >>
    qpat_assum`bce ++ bcr = X`kall_tac>>
    qpat_assum`bs.code = X`mp_tac >> simp[IMP_CONJ_THM] >>
    map_every qid_spec_tac[`code`,`bc1`] >> simp[FORALL_AND_THM] >>
    simp[Once SWAP_REVERSE] >>
    conj_asm1_tac >- (
      simp[code_for_push_def,PULL_EXISTS] >> rw[] >>
      map_every qexists_tac [`bs.refs`,`rd`,`bs.clock`,`bs.globals`,`THE (EL n bs.globals)`]  >>
      conj_tac >- (
        match_mp_tac RTC_SUBSET >>
        `bc_fetch bs = SOME (Gread n)` by (
          match_mp_tac bc_fetch_next_addr >>
          qexists_tac`bc0` >> simp[] ) >>
        simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def] >>
        simp[bc_state_component_equality,SUM_APPEND,FILTER_APPEND] >>
        rfs[Cenv_bs_def,s_refs_def,EVERY2_EVERY,EVERY_MEM] >>
        fs[MEM_ZIP,PULL_EXISTS,optionTheory.OPTREL_def] >>
        rpt (first_x_assum(qspec_then`n`mp_tac)) >>
        simp[] >> rw[] >> rw[]) >>
      conj_tac >- (
        rfs[Cenv_bs_def,s_refs_def,EVERY2_EVERY,EVERY_MEM] >>
        fs[MEM_ZIP,PULL_EXISTS,optionTheory.OPTREL_def] >>
        rpt (first_x_assum(qspec_then`n`mp_tac)) >>
        simp[] >> rw[] >> rw[]) >>
      fs[] >>
      match_mp_tac Cenv_bs_imp_incsz_irr >>
      HINT_EXISTS_TAC >> simp[] ) >>
    simp[Once SWAP_REVERSE] >>
    rw[] >> fs[] >>
    match_mp_tac code_for_push_return >>
    first_assum (match_exists_tac o concl) >>
    simp[] >>
    qexists_tac `REVERSE args` >> fsrw_tac[ARITH_ss][EVERY2_EVERY]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    qpat_assum`bce ++ bcr = X`kall_tac>>
    qpat_assum`bs.code = X`mp_tac >> simp[IMP_CONJ_THM] >>
    map_every qid_spec_tac[`code`,`bc1`] >> simp[FORALL_AND_THM] >>
    conj_asm1_tac >- (
      ntac 2 gen_tac >> strip_tac >>
      Cases_on`l`>>rw[compile_def,LET_THM,code_for_push_def,pushret_def,FOLDL_emit_append_out]>>
      qpat_assum`X = REVERSE code`(assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
      TRY (
        qmatch_assum_abbrev_tac `code = [x]` >>
        `bc_fetch bs = SOME x` by (
          match_mp_tac bc_fetch_next_addr >>
          qexists_tac `bc0` >>
          rw[Abbr`x`]) >> (
        rw[Once Cv_bv_cases] >>
        map_every qexists_tac [`bs.refs`,`rd`,`bs.clock`,`bs.globals`] >> reverse (rw[]) >- (
          match_mp_tac Cenv_bs_imp_incsz_irr >>
          qexists_tac`bs with code := bce` >>
          rw[bc_state_component_equality]  ) >>
        rw[RTC_eq_NRC] >>
        qexists_tac `SUC 0` >>
        rw[NRC] >>
        rw[bc_eval1_thm] >>
        rw[bc_eval1_def,Abbr`x`] >>
        rw[bc_eval_stack_def] >>
        srw_tac[ARITH_ss][bump_pc_def,FILTER_APPEND,SUM_APPEND,ADD1] >>
        simp[bc_state_component_equality])) >>
      simp[PULL_EXISTS,Once Cv_bv_cases] >>
      map_every qexists_tac[`bs.refs`,`rd`,`bs.clock`,`bs.globals`] >>
      conj_tac >- (
        Q.ISPECL_THEN[`$& o ORD`,`EXPLODE s'`]mp_tac compile_string_thm >>
        simp[] >> disch_then(qspecl_then[`bs`,`bc0`]mp_tac) >> simp[] >>
        qmatch_abbrev_tac`bc_next^* bs bs1 ⇒ bc_next^* bs bs2` >>
        strip_tac >>
        simp[Once RTC_CASES2] >> disj2_tac >>
        qexists_tac`bs1` >> simp[] >>
        `bc_fetch bs1 = SOME(Stack(Cons string_tag (STRLEN (EXPLODE s'))))` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs1`] >> CONV_TAC SWAP_EXISTS_CONV >>
          qexists_tac`bc1` >> simp[] ) >>
        simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def] >>
        simp[Abbr`bs1`,Abbr`bs2`,bc_state_component_equality,SUM_APPEND,FILTER_APPEND] >>
        simp[TAKE_APPEND2,DROP_APPEND2,stringTheory.IMPLODE_EXPLODE_I] ) >>
      simp[] >>
      match_mp_tac Cenv_bs_imp_incsz_irr >>
      qexists_tac`bs with code := bce` >>
      simp[]) >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`(CLit l)`]strip_assume_tac(CONJUNCT1 compile_append_out) >> fs[] >>
    fs[Once SWAP_REVERSE] >>
    `code = REVERSE bc ++ (retbc (LENGTH args) (LENGTH klvs))` by (
      Cases_on`l`>>fs[compile_def,pushret_def,LET_THM,FOLDL_emit_append_out] >>
      rw[] >> fs[Once SWAP_REVERSE]) >>
    match_mp_tac code_for_push_return >> simp[] >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    qexists_tac`REVERSE args`>>fsrw_tac[ARITH_ss][EVERY2_EVERY]) >>
  strip_tac >- (
    fsrw_tac[ETA_ss][FOLDL_UNION_BIGUNION] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def,LET_THM,pushret_def] >>
    fsrw_tac[ETA_ss][] >>
    qpat_assum`bce ++ bcr = X`mp_tac >>
    qpat_assum`bs.code = X`mp_tac >> simp[IMP_CONJ_THM] >>
    map_every qid_spec_tac[`bc1`,`code`] >> simp[FORALL_AND_THM] >>
    conj_asm1_tac >- (
      ntac 2 gen_tac >> strip_tac >>
      qspecl_then[`cenv`,`sz`,`cs`,`exps`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT2 (CONJUNCT2 compile_append_out)) >>
      fs[] >> strip_tac >>
      disch_then(assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
      qmatch_assum_abbrev_tac `code = ls0 ++ [x]` >>
      fsrw_tac[DNF_ss][] >>
      first_x_assum (qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`ls0`]mp_tac) >>
      simp[Abbr`ls0`] >>
      simp[code_for_push_def] >>
      disch_then(qx_choosel_then[`bvs`,`rf`,`rd'`,`ck`]strip_assume_tac) >>
      srw_tac[DNF_ss][Once Cv_bv_cases] >>
      map_every qexists_tac[`rf`,`rd'`,`ck`,`gv`,`bvs`] >>
      simp[] >>
      conj_tac >- (
        qmatch_assum_abbrev_tac `bc_next^* bs bs05` >>
        qmatch_abbrev_tac`bc_next^* bs bs2` >>
        rw[Once RTC_CASES2] >> disj2_tac >>
        HINT_EXISTS_TAC >>
        fs[Abbr`bs05`] >>
        qmatch_abbrev_tac`bc_next bs0 bs2` >>
        `bc_fetch bs0 = SOME x` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs0`,Abbr`x`] >>
          qexists_tac`bc0 ++ REVERSE cx` >> rw[] ) >>
        rw[bc_eval1_thm] >>
        rw[bc_eval1_def,Abbr`x`,bump_pc_def] >>
        imp_res_tac Cevaluate_list_LENGTH >>
        fs[EVERY2_EVERY] >>
        srw_tac[ARITH_ss][bc_eval_stack_def,Abbr`bs0`] >>
        unabbrev_all_tac >>
        srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] >>
        rw[bc_state_component_equality] >>
        metis_tac[TAKE_LENGTH_APPEND,REVERSE_REVERSE
                 ,DROP_LENGTH_APPEND,LENGTH_REVERSE]) >>
      qmatch_assum_abbrev_tac`Cenv_bs rd' s' denv cenv sz1 bs1` >>
      `Cenv_bs rd' s' denv cenv sz (bs1 with stack := bs.stack)` by (
        match_mp_tac Cenv_bs_pops >>
        map_every qexists_tac[`REVERSE bvs`,`bs1`] >>
        imp_res_tac Cevaluate_list_LENGTH >>
        fs[] >>
        simp[bc_state_component_equality,Abbr`bs1`] >>
        `LENGTH exps = LENGTH bvs` by fs[EVERY2_EVERY] >> fs[] >>
        metis_tac[Cenv_bs_CTLet_bound]) >>
      match_mp_tac Cenv_bs_imp_incsz_irr >>
      qexists_tac `bs1 with stack := bs.stack` >>
      rw[bc_state_component_equality,Abbr`bs1`] ) >>
    ntac 3 (rpt gen_tac >> strip_tac) >>
    match_mp_tac code_for_push_return >>
    first_x_assum(qspecl_then[`rd`]kall_tac) >>
    qspecl_then[`cenv`,`sz`,`cs`,`exps`]strip_assume_tac(CONJUNCT2(CONJUNCT2 compile_append_out)) >>
    fs[Once SWAP_REVERSE] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    qexists_tac`REVERSE args`>>fsrw_tac[ARITH_ss][EVERY2_EVERY]) >>
  strip_tac >- tac18 t1 >>
  (* Let *) strip_tac >- (
    (* Seq *) reverse(Cases_on`bd`) >- (
      simp[] >>
      rpt gen_tac >> strip_tac >>
      rpt gen_tac >> strip_tac >>
      simp[compile_def] >>
      qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cc`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      reverse(Cases_on`ALL_DISTINCT (FILTER is_Label (bc0 ++ code)) ∧ ∃cc1. code = REVERSE cc++(Stack Pop)::cc1`) >- (
        conj_tac >- (
          Q.PAT_ABBREV_TAC`cs0:compiler_result = X exp` >>
          Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
          qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs1`,`exp'`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
          simp[Abbr`cs1`,Once SWAP_REVERSE] >>
          rw[] >> fs[] >> fs[MEM_SING_APPEND] >>
          qsuff_tac`F`>-rw[] >>
          qpat_assum`¬ALL_DISTINCT X`mp_tac >>
          simp[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
          fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,between_def,is_Label_rwt] >>
          rpt (first_x_assum(qspec_then`rd`kall_tac)) >>
          rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
        conj_tac >- (
          rpt gen_tac >>
          Q.PAT_ABBREV_TAC`cs0:compiler_result = X exp` >>
          Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
          Q.PAT_ABBREV_TAC`tt:call_context = X` >>
          qspecl_then[`cenv`,`tt`,`sz`,`cs1`,`exp'`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
          simp[Abbr`cs1`,Once SWAP_REVERSE] >>
          rw[] >> fs[] >> fs[MEM_SING_APPEND] >>
          rpt (first_x_assum(qspec_then`rd`kall_tac)) >>
          qsuff_tac`F`>-rw[] >>
          qpat_assum`¬ALL_DISTINCT X`mp_tac >>
          simp[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
          fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,between_def,is_Label_rwt] >>
          rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
        rpt gen_tac >>
        Q.PAT_ABBREV_TAC`cs0:compiler_result = X exp` >>
        Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
        qspecl_then[`cenv`,`t`,`sz`,`cs1`,`exp'`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
        simp[Abbr`cs1`] >>
        simp[Once SWAP_REVERSE] >>
        rpt (first_x_assum(qspec_then`rd`kall_tac)) >>
        rw[] >> fs[] >> fs[MEM_SING_APPEND] >>
        qsuff_tac`F`>-rw[] >>
        qpat_assum`¬ALL_DISTINCT X`mp_tac >>
        simp[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
        fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
        fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,between_def,is_Label_rwt] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
      pop_assum strip_assume_tac >>
      last_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cc`,`(DROP (LENGTH cc) code) ++ bc1`]mp_tac) >>
      discharge_hyps >- (
        simp[DROP_APPEND1,DROP_LENGTH_NIL_rwt] ) >>
      simp[] >>
      disch_then (strip_assume_tac o SIMP_RULE(srw_ss())[LET_THM,code_for_push_def] o CONJUNCT1) >>
      qmatch_assum_rename_tac`bvs = [bv]`[] >> BasicProvers.VAR_EQ_TAC >>
      qmatch_assum_abbrev_tac`bc_next^* bs bs2` >>
      `bc_fetch bs2 = SOME (Stack Pop)` by (
        match_mp_tac bc_fetch_next_addr >>
        qexists_tac`bc0 ++ REVERSE cc` >>
        simp[Abbr`bs2`] ) >>
      qabbrev_tac`bs3 = bump_pc bs2 with stack := TL bs2.stack` >>
      `bc_next bs2 bs3` by (
        simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,Abbr`bs2`] >>
        simp[Abbr`bs3`,bc_state_component_equality] ) >>
      `all_vlabs_csg s' ∧ all_vlabs v ∧
       (∀cd. cd ∈ vlabs_list (store_vs (SND (FST s'))) ⇒ code_env_cd bce cd) ∧
       (∀cd. cd ∈ vlabs_list (MAP THE (FILTER IS_SOME (SND s'))) ⇒ code_env_cd bce cd) ∧
       Cenv_bs rd' s' env cenv sz (bs3 with code := bce)` by (
        qspecl_then[`s`,`env`,`exp`,`s',(Rval v)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
        qspecl_then[`s`,`env`,`exp`,`s',(Rval v)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
        simp[] >> ntac 2 strip_tac >>
        conj_tac >- (
          fsrw_tac[DNF_ss][SUBSET_DEF,vlabs_csg_def] >>
          metis_tac[EVERY_MEM] ) >>
        conj_tac >- (
          fsrw_tac[DNF_ss][SUBSET_DEF,vlabs_csg_def] >>
          metis_tac[EVERY_MEM] ) >>
        match_mp_tac Cenv_bs_change_store >>
        map_every qexists_tac[`rd`,`s`,`bs with <| pc := bs3.pc; code := bce|>`,`rf`] >>
        simp[Abbr`bs3`,bump_pc_def] >>
        simp[Abbr`bs2`,bc_state_component_equality] >>
        conj_tac >- (
          match_mp_tac Cenv_bs_with_irr >>
          first_assum (match_exists_tac o concl) >>
          simp[] ) >>
        fs[Cenv_bs_def,s_refs_def,good_rd_def] ) >>
      conj_tac >- (
        Q.PAT_ABBREV_TAC`cs0:compiler_result = X exp` >>
        Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
        qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs1`,`exp'`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
        fs[] >> rw[] >>
        first_x_assum(qspecl_then[`rd'`,`cs1`,`cenv`,`sz`,`bs3`,`bce`,`bcr`,`bc0++REVERSE cc++[Stack Pop]`,`REVERSE cb`,`bc1`]mp_tac) >>
        discharge_hyps >- (
          simp[] >>
          conj_asm1_tac >- fs[Abbr`cs1`,Abbr`cs0`] >>
          conj_tac >- (
            simp[Abbr`bs3`,bump_pc_def,Abbr`bs2`] >>
            simp[FILTER_APPEND,SUM_APPEND] ) >>
          conj_tac >- (
            simp[Abbr`bs3`,bump_pc_def,Abbr`bs2`] ) >>
          conj_tac >- (
            rfs[Abbr`bs3`,bump_pc_def,Abbr`bs2`] >>
            fs[Cenv_bs_def,s_refs_def] >>
            imp_res_tac bc_next_clock_less >>
            imp_res_tac RTC_bc_next_clock_less >>
            fs[optionTheory.OPTREL_def] >> fs[] ) >>
          fs[Abbr`cs1`,Abbr`cs0`] >>
          fs[Cenv_bs_def,s_refs_def,SUM_APPEND,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,EVERY_REVERSE] >>
          fsrw_tac[DNF_ss][MEM_FILTER,EVERY_MEM,is_Label_rwt,ALL_DISTINCT_REVERSE,MEM_MAP,between_def] >>
          fsrw_tac[ARITH_ss][] >>
          rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
        disch_then(mp_tac o CONJUNCT1) >>
        simp[code_for_push_def] >>
        simp[Abbr`bs3`,bump_pc_def,Abbr`bs2`] >>
        disch_then(qx_choosel_then[`bvs1`,`rf1`,`rd1`,`ck1`,`gv1`]strip_assume_tac) >>
        map_every qexists_tac [`bvs1`,`rf1`,`rd1`,`ck1`,`gv1`] >>
        simp[] >>
        conj_tac >- (
          qmatch_assum_abbrev_tac `bc_next^* bs bs05` >>
          qmatch_assum_abbrev_tac `bc_next bs05 bs06` >>
          qmatch_abbrev_tac`bc_next^* bs bs2` >>
          qmatch_assum_abbrev_tac`bc_next^* bs16 bs12` >>
          `bs16 = bs06` by (
            simp[Abbr`bs16`,Abbr`bs06`,bc_state_component_equality,bump_pc_def,Abbr`bs05`] ) >>
          `bs12 = bs2` by (
            simp[Abbr`bs2`,Abbr`bs12`,bc_state_component_equality] >>
            fs[Abbr`cs1`,Abbr`cs0`] >> simp[SUM_APPEND,FILTER_APPEND] ) >>
          metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
        rfs[SUM_APPEND,FILTER_APPEND,Abbr`cs1`,Abbr`cs0`] >>
        fsrw_tac[ARITH_ss][] >>
        metis_tac[IS_PREFIX_TRANS,SUBMAP_TRANS,gvrel_trans] ) >>
      conj_tac >- (
        Q.PAT_ABBREV_TAC`cs0:compiler_result = X exp` >>
        Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
        rpt gen_tac >>
        Q.PAT_ABBREV_TAC`tt:call_context = X` >>
        qspecl_then[`cenv`,`tt`,`sz`,`cs1`,`exp'`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
        fs[] >> rw[] >>
        first_x_assum(qspecl_then[`rd'`,`cs1`,`cenv`,`sz`,`bs3`,`bce`,`bcr`,`bc0++REVERSE cc++[Stack Pop]`,`REVERSE cb`,`bc1`]mp_tac) >>
        discharge_hyps >- (
          simp[] >>
          conj_asm1_tac >- fs[Abbr`cs1`,Abbr`cs0`] >>
          fsrw_tac[ARITH_ss][] >>
          conj_tac >- (
            simp[Abbr`bs3`,bump_pc_def,Abbr`bs2`] >>
            simp[FILTER_APPEND,SUM_APPEND] ) >>
          conj_tac >- (
            simp[Abbr`bs3`,bump_pc_def,Abbr`bs2`] ) >>
          conj_tac >- (
            rfs[Abbr`bs3`,bump_pc_def,Abbr`bs2`] >>
            fs[Cenv_bs_def,s_refs_def] >>
            imp_res_tac bc_next_clock_less >>
            imp_res_tac RTC_bc_next_clock_less >>
            fs[optionTheory.OPTREL_def] >> fs[] ) >>
          fs[Abbr`cs1`,Abbr`cs0`] >>
          fs[Cenv_bs_def,s_refs_def,SUM_APPEND,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,EVERY_REVERSE] >>
          fsrw_tac[DNF_ss][MEM_FILTER,EVERY_MEM,is_Label_rwt,ALL_DISTINCT_REVERSE,MEM_MAP,between_def] >>
          fsrw_tac[ARITH_ss][] >>
          rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
        disch_then (qspecl_then[`env0`,`vs`,`klvs`,`blvs`]mp_tac o CONJUNCT2) >>
        simp[Abbr`bs3`,bump_pc_def,Abbr`bs2`] >>
        disch_then(qspec_then`args`mp_tac)>>simp[] >>
        discharge_hyps >- (
          conj_tac >>
          match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
          ONCE_REWRITE_TAC[CONJ_COMM] >>
          first_assum(match_exists_tac o concl) >> rw[] >>
          match_mp_tac(GEN_ALL(MP_CANON(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
          first_assum(match_exists_tac o concl) >> simp[] >>
          fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,SUBMAP_DEF,DRESTRICT_DEF,UNCURRY]) >>
        simp[code_for_return_def] >>
        simp_tac(srw_ss()++DNF_ss)[] >>
        map_every qx_gen_tac[`br`,`rf'`,`rd''`,`ck'`,`gv'`] >>
        strip_tac >>
        map_every qexists_tac[`br`,`rf'`,`rd''`,`ck'`,`gv'`] >>
        conj_tac >- (
          qmatch_assum_abbrev_tac `bc_next^* bs bs05` >>
          qmatch_assum_abbrev_tac `bc_next bs05 bs06` >>
          qmatch_abbrev_tac`bc_next^* bs bs2` >>
          qmatch_assum_abbrev_tac`bc_next^* bs16 bs12` >>
          `bs16 = bs06` by (
            simp[Abbr`bs16`,Abbr`bs06`,bc_state_component_equality,bump_pc_def,Abbr`bs05`] ) >>
          metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
        fs[] >> metis_tac[IS_PREFIX_TRANS,SUBMAP_TRANS,gvrel_trans] ) >>
      rpt gen_tac >>
      Q.PAT_ABBREV_TAC`cs0:compiler_result = X exp` >>
      Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
      qspecl_then[`cenv`,`t`,`sz`,`cs1`,`exp'`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      fs[] >> strip_tac >>
      first_x_assum(qspecl_then[`rd'`,`cs1`,`cenv`,`sz`,`bs3`,`bce`,`bcr`,`bc0++REVERSE cc++[Stack Pop]`,`REVERSE cb`,`bc1`]mp_tac) >>
      discharge_hyps >- (
        simp[] >>
        conj_asm1_tac >- fs[Abbr`cs1`,Abbr`cs0`] >>
        fsrw_tac[ARITH_ss][] >>
        conj_tac >- (
          simp[Abbr`bs3`,bump_pc_def,Abbr`bs2`] >>
          simp[FILTER_APPEND,SUM_APPEND] ) >>
        conj_tac >- (
          simp[Abbr`bs3`,bump_pc_def,Abbr`bs2`] ) >>
        conj_tac >- (
          rfs[Abbr`bs3`,bump_pc_def,Abbr`bs2`] >>
          fs[Cenv_bs_def,s_refs_def] >>
          imp_res_tac bc_next_clock_less >>
          imp_res_tac RTC_bc_next_clock_less >>
          fs[optionTheory.OPTREL_def] >> fs[] ) >>
        fs[Abbr`cs1`,Abbr`cs0`] >>
        fs[Cenv_bs_def,s_refs_def,SUM_APPEND,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,EVERY_REVERSE] >>
        fsrw_tac[DNF_ss][MEM_FILTER,EVERY_MEM,is_Label_rwt,ALL_DISTINCT_REVERSE,MEM_MAP,between_def] >>
        fsrw_tac[ARITH_ss][] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      simp[] >>
      disch_then(qspec_then`t`mp_tac) >> simp[] >>
      Cases_on`err`>>simp[] >- (
        simp[Abbr`bs3`,bump_pc_def] >>
        simp[Abbr`bs2`] >> strip_tac >>
        rpt gen_tac >> strip_tac >>
        first_x_assum(qspecl_then[`ig`,`sp`,`hdl`,`st`]mp_tac) >>
        simp[] >>
        simp[code_for_return_def] >>
        simp_tac(srw_ss()++DNF_ss)[] >>
        map_every qx_gen_tac[`br`,`rf'`,`rd''`,`ck'`,`gv'`] >>
        strip_tac >>
        map_every qexists_tac[`br`,`rf'`,`rd''`,`ck'`,`gv'`] >>
        conj_tac >- (
          qmatch_assum_abbrev_tac `bc_next^* bs bs05` >>
          qmatch_assum_abbrev_tac `bc_next bs05 bs06` >>
          qmatch_abbrev_tac`bc_next^* bs bs2` >>
          qmatch_assum_abbrev_tac`bc_next^* bs16 bs12` >>
          `bs16 = bs06` by (
            simp[Abbr`bs16`,Abbr`bs06`,bc_state_component_equality,bump_pc_def,Abbr`bs05`] ) >>
          metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
        fs[] >> metis_tac[IS_PREFIX_TRANS,SUBMAP_TRANS,gvrel_trans] ) >>
      simp[Abbr`bs3`,bump_pc_def] >>
      simp[Abbr`bs2`] >> strip_tac >>
      rpt gen_tac >> strip_tac >> fs[] >>
      qexists_tac`bs'` >> simp[] >>
      qmatch_assum_abbrev_tac `bc_next^* bs bs05` >>
      qmatch_assum_abbrev_tac `bc_next bs05 bs06` >>
      qmatch_abbrev_tac`bc_next^* bs bs2` >>
      qmatch_assum_abbrev_tac`bc_next^* bs16 bs12` >>
      `bs16 = bs06` by (
        simp[Abbr`bs16`,Abbr`bs06`,bc_state_component_equality,bump_pc_def,Abbr`bs05`] ) >>
      metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def] >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cc`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    reverse(Cases_on`ALL_DISTINCT (FILTER is_Label (bc0 ++ code)) ∧ ∃cc1. code = REVERSE cc++cc1`) >- (
      conj_tac >- (
        Q.PAT_ABBREV_TAC`cs1:compiler_result = X exp` >>
        qspecl_then[`cenv`,`TCNonTail`,`sz`,`exp'`,`0`,`cs1`,`1`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 (CONJUNCT2 compile_append_out)) >>
        simp[Abbr`cs1`,Once SWAP_REVERSE] >>
        rw[] >> fs[] >> fs[MEM_SING_APPEND] >>
        qsuff_tac`F`>-rw[] >>
        qpat_assum`¬ALL_DISTINCT X`mp_tac >>
        simp[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
        fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,between_def,is_Label_rwt] >>
        rpt (first_x_assum(qspec_then`rd`kall_tac)) >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
      conj_tac >- (
        rpt gen_tac >>
        Q.PAT_ABBREV_TAC`cs1:compiler_result = X exp` >>
        Q.PAT_ABBREV_TAC`tt:call_context = X` >>
        qspecl_then[`cenv`,`tt`,`sz`,`exp'`,`0`,`cs1`,`1`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 (CONJUNCT2 compile_append_out)) >>
        simp[Abbr`cs1`,Once SWAP_REVERSE] >>
        rw[] >> fs[] >> fs[MEM_SING_APPEND] >>
        rpt (first_x_assum(qspec_then`rd`kall_tac)) >>
        qsuff_tac`F`>-rw[] >>
        qpat_assum`¬ALL_DISTINCT X`mp_tac >>
        simp[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
        fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,between_def,is_Label_rwt] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
      rpt gen_tac >>
      Q.PAT_ABBREV_TAC`cs1:compiler_result = X exp` >>
      qspecl_then[`cenv`,`t`,`sz`,`exp'`,`0`,`cs1`,`1`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 (CONJUNCT2 compile_append_out)) >>
      simp[Abbr`cs1`] >>
      simp[Once SWAP_REVERSE] >>
      rpt (first_x_assum(qspec_then`rd`kall_tac)) >>
      rw[] >> fs[] >> fs[MEM_SING_APPEND] >>
      qsuff_tac`F`>-rw[] >>
      qpat_assum`¬ALL_DISTINCT X`mp_tac >>
      simp[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
      fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,between_def,is_Label_rwt] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
    pop_assum strip_assume_tac >>
    last_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cc`,`(DROP (LENGTH cc) code) ++ bc1`]mp_tac) >>
    discharge_hyps >- (
      simp[DROP_APPEND1,DROP_LENGTH_NIL_rwt] ) >>
    simp[] >>
    disch_then (strip_assume_tac o SIMP_RULE(srw_ss())[LET_THM,code_for_push_def] o CONJUNCT1) >>
    qmatch_assum_rename_tac`bvs = [bv]`[] >> BasicProvers.VAR_EQ_TAC >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs2` >>
    `all_vlabs_csg s' ∧ all_vlabs v ∧
     EVERY (code_env_cd bce) (free_labs (SUC (LENGTH env)) exp') ∧
     (∀cd. cd ∈ vlabs_list (store_vs (SND (FST s'))) ⇒ code_env_cd bce cd) ∧
     (∀cd. cd ∈ vlabs v ∨ cd ∈ vlabs_list env ⇒ code_env_cd bce cd) ∧
     (∀cd. cd ∈ vlabs_list (MAP THE (FILTER IS_SOME (SND s'))) ⇒ code_env_cd bce cd) ∧
     set (free_vars exp') ⊆ count (LENGTH (CTLet(sz+1)::cenv)) ∧
     Cenv_bs rd' s' (v::env) (CTLet(sz+1)::cenv) (sz+1) (bs2 with code := bce)` by (
      qspecl_then[`s`,`env`,`exp`,`s',(Rval v)`]mp_tac(CONJUNCT1 Cevaluate_store_SUBSET) >>
      qspecl_then[`s`,`env`,`exp`,`s',(Rval v)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
      qspecl_then[`s`,`env`,`exp`,`s',(Rval v)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
      simp[] >> ntac 3 strip_tac >>
      first_x_assum(qspec_then`rd`kall_tac) >>
      simp[ADD1] >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF,vlabs_csg_def] >>
        metis_tac[EVERY_MEM] ) >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF,vlabs_csg_def] >>
        metis_tac[EVERY_MEM] ) >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF,vlabs_csg_def] >>
        metis_tac[EVERY_MEM] ) >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      match_mp_tac Cenv_bs_FUPDATE >>
      qexists_tac`bs2 with <| stack := bs.stack; code := bce|>` >>
      simp[bc_state_component_equality,Abbr`bs2`] >> fs[] >>
      match_mp_tac Cenv_bs_change_store >>
      map_every qexists_tac [`rd`,`s`,`bs with <| pc := next_addr bs.inst_length (bc0 ++ REVERSE cc); code := bce|>`,`rf`] >>
      simp[bc_state_component_equality] >>
      fs[Cenv_bs_def,s_refs_def,good_rd_def,env_renv_def,fmap_rel_def]) >>
    fs[] >>
    conj_tac >- (
      REWRITE_TAC[ONE] >> simp[compile_def] >>
      Q.PAT_ABBREV_TAC`cs1:compiler_result = X exp` >>
      qspecl_then[`CTLet(sz+1)::cenv`,`TCNonTail`,`sz+1`,`cs1`,`exp'`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      simp[Abbr`cs1`,Once SWAP_REVERSE] >> rw[] >>
      qmatch_assum_abbrev_tac`cs1.out = cc ++ cs.out` >>
      first_x_assum(qspecl_then[`rd'`,`cs1`,`CTLet(sz+1)::cenv`,`sz+1`,`bs2`,`bce`,`bcr`,`bc0++REVERSE cc`,`REVERSE cb`]mp_tac) >>
      simp[] >>
      discharge_hyps >- (
        simp[Abbr`bs2`] >>
        conj_tac >- PROVE_TAC[] >>
        conj_tac >- (
          imp_res_tac RTC_bc_next_clock_less >> rfs[optionTheory.OPTREL_def] >>
          fs[Cenv_bs_def,s_refs_def] ) >>
        fs[Cenv_bs_def,s_refs_def,SUM_APPEND,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,EVERY_REVERSE] >>
        fsrw_tac[DNF_ss][MEM_FILTER,EVERY_MEM,is_Label_rwt,ALL_DISTINCT_REVERSE,MEM_MAP,between_def] >>
        fsrw_tac[ARITH_ss][Abbr`cs1`] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      disch_then (strip_assume_tac o SIMP_RULE(srw_ss())[LET_THM,code_for_push_def] o CONJUNCT1) >>
      qmatch_assum_rename_tac`bvs = [bv']`[] >> BasicProvers.VAR_EQ_TAC >>
      qmatch_assum_abbrev_tac`bc_next^* bs2 bs4` >>
      `bc_next^* bs bs4` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
      pop_assum mp_tac >>
      rpt(qpat_assum`bc_next^* X Y`kall_tac) >>
      simp[Abbr`bs4`] >> strip_tac >>
      simp[code_for_push_def] >>
      map_every qexists_tac[`[bv']`,`rf'`,`rd''`,`ck'`,`gv'`] >>
      simp[] >>
      conj_tac >- (
        rw[Once RTC_CASES2] >> disj2_tac >>
        HINT_EXISTS_TAC >> simp[] >>
        pop_assum kall_tac >>
        qmatch_abbrev_tac`bc_next bs0 bs1` >>
        `bc_fetch bs0 = SOME (Stack (Pops 1))` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs0`,Abbr`bs2`] >>
          CONV_TAC SWAP_EXISTS_CONV >>
          qexists_tac`bc1`>>simp[] ) >>
        simp[bc_eval1_thm,bc_eval1_def,Abbr`bs0`,bump_pc_def] >>
        simp[bc_eval_stack_def,Abbr`bs2`,Abbr`bs1`,bc_state_component_equality] >>
        simp[SUM_APPEND,FILTER_APPEND] ) >>
      fs[Abbr`bs2`] >>
      reverse conj_tac >- metis_tac[IS_PREFIX_TRANS,SUBMAP_TRANS,gvrel_trans] >>
      match_mp_tac Cenv_bs_imp_incsz_irr >>
      qexists_tac`bs with <| refs := rf'; clock := ck'; code := bce; globals := gv'|>` >>
      simp[bc_state_component_equality] >>
      match_mp_tac Cenv_bs_pops >>
      qexists_tac`[bv';bv]` >> simp[] >> fsrw_tac[ARITH_ss][] >>
      reverse conj_tac >- (metis_tac[Cenv_bs_CTLet_bound]) >>
      qmatch_assum_abbrev_tac`Cenv_bs rd'' s'' (v::env) (CTLet(sz+1)::cenv) (sz+2) bs0` >>
      `env = TL (v::env) ∧ cenv = TL (CTLet (sz+1)::cenv)` by simp[] >>
      ntac 2 (pop_assum SUBST1_TAC) >>
      match_mp_tac Cenv_bs_DOMSUB >> simp[] >>
      match_mp_tac Cenv_bs_with_irr >>
      qexists_tac`bs0` >>
      simp[bc_state_component_equality,Abbr`bs0`]) >>
    conj_tac >- (
      REWRITE_TAC[ONE] >> simp[compile_def] >>
      rpt gen_tac >>
      Q.PAT_ABBREV_TAC`cs1:compiler_result = X exp` >>
      Q.PAT_ABBREV_TAC`tt:call_context = X` >>
      qspecl_then[`CTLet(sz+1)::cenv`,`tt`,`sz+1`,`cs1`,`exp'`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      simp[Abbr`cs1`,Once SWAP_REVERSE] >> rw[] >>
      qmatch_assum_abbrev_tac`cs1.out = cc ++ cs.out` >>
      first_x_assum(qspecl_then[`rd'`,`cs1`,`CTLet(sz+1)::cenv`,`sz+1`,`bs2`,`bce`,`bcr`,`bc0++REVERSE cc`,`REVERSE cb`]mp_tac) >>
      simp[] >>
      discharge_hyps >- (
        simp[Abbr`bs2`] >> fsrw_tac[ARITH_ss][] >>
        conj_tac >- PROVE_TAC[] >>
        conj_tac >- (
          imp_res_tac RTC_bc_next_clock_less >> rfs[optionTheory.OPTREL_def] >>
          fs[Cenv_bs_def,s_refs_def] ) >>
        fs[Cenv_bs_def,s_refs_def,SUM_APPEND,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,EVERY_REVERSE] >>
        fsrw_tac[DNF_ss][MEM_FILTER,EVERY_MEM,is_Label_rwt,ALL_DISTINCT_REVERSE,MEM_MAP,between_def] >>
        fsrw_tac[ARITH_ss][Abbr`cs1`] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      disch_then (qspecl_then[`env0`,`vs`,`v::klvs`,`bv::blvs`]mp_tac o CONJUNCT2) >>
      simp[Abbr`bs2`,ADD1] >>
      disch_then(qspec_then`args`mp_tac) >>
      simp[] >>
      discharge_hyps >- (
        fs[] >>
        fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
        rw[] >>
        match_mp_tac(MP_CANON (GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
        simp[] >>
        qexists_tac`rd` >>
        simp[DRESTRICT_SUBSET_SUBMAP] >>
        fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,SUBMAP_DEF,DRESTRICT_DEF,UNCURRY]) >>
      simp[code_for_return_def] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      map_every qx_gen_tac[`br`,`rf'`,`rd''`,`ck'`,`gv'`] >>
      strip_tac >>
      map_every qexists_tac[`br`,`rf'`,`rd''`,`ck'`,`gv'`] >>
      conj_tac >- (
        fs[] >> qmatch_abbrev_tac`bc_next^* bss bs5` >>
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        qmatch_assum_abbrev_tac`bc_next^* bss bs2` >>
        qexists_tac`bs2` >> simp[] ) >>
      fs[] >>
      metis_tac[IS_PREFIX_TRANS,SUBMAP_TRANS,gvrel_trans]) >>
    let
      val t1 =
        simp[code_for_return_def] >>
        simp_tac(srw_ss()++DNF_ss)[] >>
        map_every qx_gen_tac[`br`,`rf'`,`rd''`,`ck'`,`gv'`] >>
        strip_tac >>
        map_every qexists_tac[`br`,`rf'`,`rd''`,`ck'`,`gv'`] >>
        conj_tac >- (
          match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
          qmatch_assum_abbrev_tac`bc_next^* bs bs2` >>
          qexists_tac`bs2` >> simp[] >>
          qmatch_assum_abbrev_tac`bc_next^* bs2 bs4` >>
          qspecl_then[`cenv`,`t`,`sz`,`exp'`,`0`,`cs1`,`1`,`cb`,`cd`]mp_tac compile_bindings_thm >>
          simp[] >> strip_tac >>
          match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
          HINT_EXISTS_TAC >> simp[] >>
          fs[Abbr`bs4`] >>
          simp[Abbr`bs2`] ) >>
        fs[Abbr`bs2`] >>
        metis_tac[IS_PREFIX_TRANS,SUBMAP_TRANS,gvrel_trans]
      val t2 = `bs2.output = bs.output` by simp[Abbr`bs2`] >> metis_tac[RTC_TRANSITIVE,transitive_def]
    in
      rpt gen_tac >>
      Q.PAT_ABBREV_TAC`cs1:compiler_result = X exp` >>
      qspecl_then[`cenv`,`t`,`sz`,`exp'`,`0`,`cs1`,`1`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1 (CONJUNCT2 compile_append_out)) >>
      simp[Abbr`cs1`] >>
      REWRITE_TAC[Once SWAP_REVERSE] >>
      simp[] >> strip_tac >>
      qpat_assum`(A.out = cb ++ B)`mp_tac >>
      Q.PAT_ABBREV_TAC`cs1:compiler_result = X exp` >> strip_tac >>
      qabbrev_tac`tt = case t of TCNonTail => t | TCTail j k => TCTail j (k + 1)` >>
      qspecl_then[`CTLet(sz+1)::cenv`,`tt`,`sz+1`,`cs1`,`exp'`](Q.X_CHOOSE_THEN`cd`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      first_x_assum(qspecl_then[`rd'`,`cs1`,`CTLet (sz+1)::cenv`,`sz+1`,`bs2`,`bce`,`bcr`
                               ,`bc0 ++ REVERSE cc`
                               ,`REVERSE cd`,`(DROP (LENGTH cd) (REVERSE cb))++bc1`]mp_tac) >>
      discharge_hyps >- (
        simp[TAKE_APPEND1,TAKE_APPEND2,Abbr`bs2`] >>
        conj_asm1_tac >- (
          qspecl_then[`cenv`,`t`,`sz`,`exp'`,`0`,`cs1`,`1`,`cb`,`cd`]mp_tac compile_bindings_thm >>
          simp[DROP_APPEND1,DROP_LENGTH_NIL_rwt] ) >>
        conj_tac >- PROVE_TAC[] >>
        fs[Cenv_bs_def,s_refs_def,SUM_APPEND,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,EVERY_REVERSE] >>
        imp_res_tac RTC_bc_next_clock_less >> rfs[optionTheory.OPTREL_def] >>
        fsrw_tac[DNF_ss][MEM_FILTER,EVERY_MEM,is_Label_rwt,ALL_DISTINCT_REVERSE,MEM_MAP,between_def] >>
        fsrw_tac[ARITH_ss][Abbr`cs1`] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      simp[] >>
      disch_then(qspec_then`tt`mp_tac) >> simp[] >>
      reverse(Cases_on`err`)>>simp[] >- (
        simp[Abbr`tt`] >>
        Cases_on`t`>>simp[] >- t2 >>
        rpt strip_tac >>
        qpat_assum`p ⇒q`mp_tac >>
        discharge_hyps >- (
          simp[Abbr`bs2`] >>
          qexists_tac`bv::blvs` >>
          simp[] >>
          qexists_tac`args`>>simp[] ) >>
        t2 ) >>
      strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum(qspecl_then[`bv::ig`,`sp`,`hdl`,`st`]mp_tac) >>
      discharge_hyps >- (
        simp[Abbr`bs2`] >>
        simp[Abbr`tt`] >>
        Cases_on`t`>>fs[] >>
        qexists_tac`bv::blvs`>>simp[]>>
        qexists_tac`args`>>simp[]) >>
      t1
    end) >>
  strip_tac >- (
    Cases_on`bd` >> simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def,LET_THM] >>
    simp[GSYM FORALL_AND_THM] >>
    gen_tac >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    (Cases_on `¬∃cc1. code = REVERSE cx ++ cc1` >- (
      rpt gen_tac >> strip_tac >>
      qpat_assum`X = REVERSE code ++ cs.out`mp_tac >>
      REWRITE_TAC[ONE] >>
      Cases_on`t`>>simp[compile_def] >>
      Q.PAT_ABBREV_TAC`cs0:compiler_result = X exp` >>
      (Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` ORELSE qabbrev_tac`cs1 = cs0`) >>
      Q.PAT_ABBREV_TAC`tt:call_context = X` >>
      qspecl_then[`CTLet(sz+1)::cenv`,`tt`,`sz+1`,`cs1`,`b`](strip_assume_tac)(CONJUNCT1 compile_append_out)>>
      qspecl_then[`cenv`,`tt`,`sz`,`cs1`,`b`](strip_assume_tac)(CONJUNCT1 compile_append_out)>>
      simp[Once SWAP_REVERSE,Abbr`cs1`] >> rw[] >> fs[])) >> fs[] >>
    first_x_assum (qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cx`]mp_tac) >>
    simp[GSYM FORALL_AND_THM] >>
    disch_then(qspec_then`TCNonTail`mp_tac) >> simp[] >>
    Cases_on`err`>>simp[]>>
    strip_tac >> rpt gen_tac >>
    strip_tac >>
    first_assum(qspec_then`ig`mp_tac) >>
    simp[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def] >>
    Q.ISPECL_THEN[`cenv`,`sz`,`cs`,`defs`]mp_tac compile_closures_thm >>
    simp[] >>
    disch_then(Q.X_CHOOSE_THEN`cc`mp_tac) >>
    strip_tac >>
    reverse(Cases_on`∃bc10. bs.code = bc0 ++ cc ++ bc10`) >- (
      qmatch_assum_abbrev_tac`X.out = REVERSE cc ++ cs.out` >>
      rpt conj_tac >> rpt gen_tac >>
      Q.PAT_ABBREV_TAC`tt = Y:call_context`>>
      strip_tac >>
      qspecl_then[`cenv`,`tt`,`sz`,`exp`,`0`,`X`,`LENGTH defs`]mp_tac(CONJUNCT1 (CONJUNCT2 compile_append_out)) >>
      rw[Once SWAP_REVERSE_SYM] >> fs[] >> rfs[] ) >>
    fs[] >>
    first_x_assum(qspecl_then[`bs`,`bc0`,`bc10`,`FDOM rd.cls`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      qpat_assum`∀rd yy. Z`kall_tac >>
      fs[SUM_eq_0,MEM_MAP,GSYM LEFT_FORALL_IMP_THM,EVERY_MEM] >>
      conj_asm1_tac >- (
        fsrw_tac[DNF_ss][free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
        rpt strip_tac >> res_tac >>
        PairCases_on`e` >>
        Cases_on`e0`>>fs[]) >>
      fsrw_tac[DNF_ss][MEM_FLAT,MEM_MAP] >>
      simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM] >>
      qx_gen_tac`def` >> strip_tac >>
      `IS_SOME (FST def)` by metis_tac[] >>
      `∃n. n < LENGTH defs ∧ (EL n defs = def)` by metis_tac[MEM_EL] >>
      `code_env_cd bce ((LENGTH env,LENGTH defs,n),(THE(FST def)),(SND def))` by (
        last_x_assum match_mp_tac >>
        simp[free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
        simp_tac(srw_ss()++DNF_ss)[] >>
        qexists_tac`n` >>
        PairCases_on`def` >> Cases_on`def0` >> fs[] >>
        PairCases_on`x`>>simp[] ) >>
      PairCases_on`def`>>Cases_on`def0`>>fs[]>>PairCases_on`x`>>
      qpat_assum`X ++ A = Y ++ Z`(assume_tac o SYM) >>
      fs[code_env_cd_def,bc_find_loc_def] >>
      conj_tac >- (
        qmatch_abbrev_tac`IS_SOME X` >>
        Cases_on`X`>>rw[bc_find_loc_def]>>
        fs[markerTheory.Abbrev_def] >>
        imp_res_tac(GSYM bc_find_loc_aux_NONE)>>
        qpat_assum`X = bc0 ++ code ++ bc1`mp_tac >>
        REWRITE_TAC[GSYM APPEND_ASSOC] >>
        qpat_assum`code ++ bc1 = X`SUBST1_TAC >>
        REWRITE_TAC[APPEND_ASSOC] >>
        spose_not_then (strip_assume_tac o SYM) >>
        full_simp_tac std_ss [] >> fs[]) >>
      fs[good_cd_def] >>
      `LENGTH cenv = LENGTH env` by fs[Cenv_bs_def,EVERY2_EVERY,env_renv_def] >>
      fs[EVERY_MEM] >>
      qx_gen_tac`z` >>
      reverse conj_tac >- (
        fs[bind_fv_def,LET_THM,MEM_FILTER,MEM_GENLIST] ) >>
      rator_x_assum`Cenv_bs`mp_tac >>
      simp[Cenv_bs_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,env_renv_def] >>
      simp[option_case_NONE_F] >>
      metis_tac[optionTheory.IS_SOME_DEF] ) >>
    disch_then(Q.X_CHOOSE_THEN`rs`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    qabbrev_tac`rd' = rd with cls := rd.cls |++ (GENLIST (λi. (EL i rs, (env, defs, i))) (LENGTH rs))` >>
    `rd.cls ⊑ rd'.cls` by (
      simp[Abbr`rd'`] >>
      simp[SUBMAP_DEF,FDOM_FUPDATE_LIST] >>
      rw[] >> match_mp_tac EQ_SYM >>
      match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
      simp[MAP_GENLIST,combinTheory.o_DEF,MEM_GENLIST] >>
      fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY,FLOOKUP_DEF] >>
      metis_tac[MEM_EL]) >>
    Q.PAT_ABBREV_TAC`ccs = compile_closures cenv sz cs defs` >>
    qabbrev_tac`cenv' = REVERSE (GENLIST(λm. CTLet (sz+m+1))(LENGTH defs)) ++ cenv` >>
    `contains_primitives bce ∧
     EVERY all_vlabs (GENLIST (CRecClos env defs) (LENGTH defs)) ∧
     EVERY (code_env_cd bce) (free_labs (LENGTH defs + LENGTH env) exp) ∧
     (∀cd. cd ∈ vlabs_list (store_vs (SND (FST s))) ⇒ code_env_cd bce cd) ∧
     (∀cd. cd ∈ vlabs_list (GENLIST (CRecClos env defs) (LENGTH defs) ++ env) ⇒
           code_env_cd bce cd) ∧
        bs1.pc = next_addr bs1.inst_length (bc0++cc) ∧
     (∀cd. cd ∈ vlabs_list (MAP THE (FILTER IS_SOME (SND s))) ⇒ code_env_cd bce cd) ∧
     set (free_vars exp) ⊆ count (LENGTH cenv') ∧
     Cenv_bs rd' s (GENLIST (CRecClos env defs) (LENGTH defs) ++ env)
          cenv' (sz+LENGTH defs) (bs1 with code := bce) ∧
     ALL_DISTINCT (FILTER is_Label bc0) ∧
     EVERY (combin$C $< ccs.next_label o dest_Label) (FILTER is_Label (bc0++cc))` by (
      simp[] >>
      conj_tac >- simp[EVERY_GENLIST] >>
      conj_tac >- PROVE_TAC[ADD_SYM] >>
      conj_tac >- (
        fsrw_tac[DNF_ss][MEM_GENLIST,MEM_FLAT,MEM_MAP,vlabs_list_MAP] >>
        reverse conj_tac >- metis_tac[] >>
        conj_tac >- metis_tac[] >>
        fsrw_tac[DNF_ss][EVERY_MEM,MEM_FLAT,MEM_MAP] >>
        metis_tac[] ) >>
      conj_tac >- simp[Abbr`bs1`] >>
      conj_tac >- (
        first_x_assum(qspec_then`rd'`kall_tac) >>
        fsrw_tac[DNF_ss][SUBSET_DEF,FOLDL_UNION_BIGUNION,LET_THM,Abbr`cenv'`] >>
        rw[] >> res_tac >> fsrw_tac[ARITH_ss][]) >>
      conj_tac >- (
        qunabbrev_tac`cenv'` >>
        first_x_assum(qspec_then`rd'`kall_tac) >>
        match_mp_tac Cenv_bs_FUPDATE_LIST >>
        Q.PAT_ABBREV_TAC`vs = GENLIST (CRecClos env defs) Y` >>
        map_every qexists_tac[`vs`,`env`,`cenv`,`sz`] >>
        `LENGTH vs = LENGTH defs` by simp[Abbr`vs`] >>
        simp[] >>
        qexists_tac`bs1 with <| stack := bs.stack; code := bce |>` >>
        simp[bc_state_component_equality,Abbr`bs1`] >>
        reverse conj_asm2_tac >- (
          rator_x_assum`RTC`kall_tac >>
          simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
          qx_gen_tac`n`>>strip_tac >>
          simp[EL_MAP,Abbr`vs`] >>
          fsrw_tac[DNF_ss][EVERY_MEM,MEM_FLAT,MEM_MAP] >>
          qabbrev_tac`def = EL n defs` >>
          `MEM def defs` by metis_tac[MEM_EL] >>
          `code_env_cd bce ((LENGTH env,LENGTH defs,n),(THE(FST def)),(SND def))` by (
            last_x_assum match_mp_tac >>
            simp[free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
            simp_tac(srw_ss()++DNF_ss)[] >>
            qexists_tac`n` >>
            qunabbrev_tac`def` >> qabbrev_tac`def = EL n defs` >>
            res_tac >>
            PairCases_on`def` >> Cases_on`def0` >> fs[] >>
            PairCases_on`x`>>simp[] ) >>
          res_tac >>
          PairCases_on`def`>>Cases_on`def0`>>fs[]>>PairCases_on`x`>>
          qpat_assum`bce ++ A = Y ++ Z`(assume_tac o SYM) >>
          fs[code_env_cd_def,bc_find_loc_def,good_cd_def] >>
          simp[Once Cv_bv_cases,el_check_def] >>
          qpat_assum`X = bind_fv A B C` mp_tac >>
          simp[bind_fv_def] >>
          strip_tac >>
          conj_asm1_tac >- (
            rw[EVERY_FILTER,EVERY_GENLIST] ) >>
          conj_asm1_tac >- (
            qsuff_tac`MEM (Label x0) bce` >- (
              metis_tac[APPEND_ASSOC,bc_find_loc_aux_append_code,bc_find_loc_aux_NONE,optionTheory.option_CASES,optionTheory.THE_DEF] ) >>
            rw[]) >>
          simp[Once Cv_bv_cases] >>
          conj_tac >- (
            gen_tac >> strip_tac >>
            Q.PAT_ABBREV_TAC`recs:num list = FILTER X Y` >>
            conj_asm1_tac >- (
              rw[] >> fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] ) >>
            simp[EL_APPEND1,EL_MAP] >>
            map_every qexists_tac[`env`,`defs`,`EL i recs`] >>
            simp[FLOOKUP_DEF,Abbr`rd'`,FDOM_FUPDATE_LIST,MEM_MAP,MEM_GENLIST,EXISTS_PROD] >>
            conj_tac >- metis_tac[] >>
            qho_match_abbrev_tac`(fm |++ ls) ' k = X` >>
            qho_match_abbrev_tac`P ((fm |++ ls) ' k)` >>
            ho_match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
            `MAP FST ls = rs` by (
              simp[LIST_EQ_REWRITE,Abbr`ls`,EL_MAP] ) >>
            simp[] >>
            simp[MEM_EL,Abbr`ls`,Abbr`P`] >>
            qexists_tac`EL i recs` >>
            simp[Abbr`k`] ) >>
          gen_tac >> strip_tac >>
          Q.PAT_ABBREV_TAC`envs:num list = MAP X Y` >>
          `i < LENGTH envs` by rw[Abbr`envs`] >>
          simp[EL_APPEND2,EL_MAP] >>
          conj_asm1_tac >- (
            fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] ) >>
          rator_x_assum`Cenv_bs`mp_tac >>
          simp[Cenv_bs_def,env_renv_def,EVERY2_EVERY,EVERY_MEM] >> strip_tac >>
          rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
          qpat_assum`∀n. n < LENGTH cenv ⇒ P`(qspec_then`EL i envs`mp_tac) >>
          simp[option_case_NONE_F] >> rw[] >> simp[] >>
          match_mp_tac (GEN_ALL (MP_CANON (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
          HINT_EXISTS_TAC >> simp[] >>
          simp[Abbr`rd'`] ) >>
        match_mp_tac Cenv_bs_change_store >>
        Q.PAT_ABBREV_TAC`pc = next_addr il X` >>
        map_every qexists_tac[`rd`,`s`,`bs with <| pc := pc ; code := bce|>`] >>
        simp[bc_state_component_equality,Abbr`rd'`] >>
        conj_tac >- (
          match_mp_tac Cenv_bs_with_irr >>
          qexists_tac`bs with code := bce` >>
          simp[] ) >>
        fs[Cenv_bs_def,s_refs_def] >>
        reverse conj_tac >- (
          simp[SUBMAP_DEF,DRESTRICT_DEF,FDOM_FUPDATE_LIST] >>
          rw[] >>
          match_mp_tac EQ_SYM >>
          match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
          simp[MAP_ZIP] >>
          metis_tac[] ) >>
        fs[Cenv_bs_def,env_renv_def,s_refs_def,fmap_rel_def,good_rd_def] >>
        conj_tac >- (
          fs[FEVERY_DEF,UNCURRY,FDOM_FUPDATE_LIST] >>
          simp[MAP_GENLIST,combinTheory.o_DEF,MAP_ZIP,MEM_GENLIST] >>
          qx_gen_tac`x` >>
          Q.ISPECL_THEN[`rs`,`x`](mp_tac o SYM)MEM_EL >>
          simp[] >> disch_then kall_tac >>
          Cases_on`MEM x rs` >> simp[] >- (
            fs[EVERY_MEM] >>
            conj_asm1_tac >- metis_tac[] >>
            Q.PAT_ABBREV_TAC`cls = ((rd.cls |++ ls) ' x)` >>
            `∃i. i < LENGTH rs ∧ (x = EL i rs)` by metis_tac[MEM_EL] >>
            `cls = (env,defs,i)` by (
              qunabbrev_tac`cls` >>
              qho_match_abbrev_tac`(fm |++ ls) ' x = y` >>
              qho_match_abbrev_tac`P ((fm |++ ls) ' x)` >>
              ho_match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
              simp[Abbr`ls`,MAP_GENLIST,combinTheory.o_DEF,MEM_GENLIST] >>
              asm_simp_tac(srw_ss()++DNF_ss)[Abbr`P`,Abbr`y`] >> rfs[] >>
              qmatch_abbrev_tac`ALL_DISTINCT ls` >>
              `ls = rs` by (
                unabbrev_all_tac >>
                match_mp_tac GENLIST_EL >>
                simp[] ) >>
              simp[] ) >>
            simp[] >>
            simp[flookup_fupdate_list] >>
            BasicProvers.CASE_TAC >- (
              imp_res_tac ALOOKUP_FAILS >>
              rfs[MEM_ZIP] >> metis_tac[] ) >>
            imp_res_tac ALOOKUP_MEM >>
            rfs[MEM_ZIP,EL_MAP] >> fs[EL_MAP] >>
            fs[LIST_REL_EL_EQN] >>
            first_x_assum(qspec_then`n`mp_tac) >>
            simp[EL_MAP] >>
            simp[Abbr`vs`] >>
            `i = n` by metis_tac[EL_ALL_DISTINCT_EL_EQ] >>
            rw[] ) >>
          strip_tac >>
          `x ∈ FDOM bs.refs` by (
            fs[FLOOKUP_DEF] >> metis_tac[] ) >>
          simp[FLOOKUP_DEF,FDOM_FUPDATE_LIST] >>
          Q.PAT_ABBREV_TAC`bv = (bs.refs |++ ls) ' x` >>
          Q.PAT_ABBREV_TAC`dd = (rd.cls |++ ls) ' x` >>
          qsuff_tac`(bv = bs.refs ' x) ∧ (dd = rd.cls ' x)` >- (
            strip_tac >>
            first_x_assum(qspec_then`x`mp_tac) >>
            first_x_assum(qspec_then`x`mp_tac) >>
            first_x_assum(qspec_then`x`mp_tac) >>
            simp[FLOOKUP_DEF] >> rpt strip_tac >> simp[] >>
            match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
            qexists_tac`rd` >> simp[] >> rfs[]) >>
          map_every qunabbrev_tac[`bv`,`dd`] >>
          conj_tac >> match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
          simp[MAP_ZIP,MAP_GENLIST,combinTheory.o_DEF] >>
          simp[MEM_GENLIST] >>
          fs[MEM_EL] >> metis_tac[] ) >>
        conj_tac >- (
          simp[EVERY_MEM,FDOM_FUPDATE_LIST,MAP_ZIP] >>
          fs[EVERY_MEM] ) >>
        fs[Cenv_bs_def,s_refs_def,EVERY2_EVERY,good_rd_def,EVERY_MEM,FORALL_PROD] >>
        rator_x_assum`RTC`kall_tac >>
        simp[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
        reverse conj_tac >- (
          gen_tac >> strip_tac >>
          rfs[MEM_ZIP,PULL_EXISTS] >>
          match_mp_tac(MP_CANON(GEN_ALL optionTheory.OPTREL_MONO)) >>
          first_x_assum(qspec_then`n`kall_tac)>>
          qpat_assum`∀n. n < LENGTH bs.globals ⇒ X`(qspec_then`n`mp_tac) >>
          discharge_hyps >- simp[] >> strip_tac >>
          HINT_EXISTS_TAC >> simp[] >>
          rpt gen_tac >> strip_tac >>
          match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
          qexists_tac`rd` >> simp[] ) >>
        gen_tac >> strip_tac >> simp[EL_MAP] >>
        Q.PAT_ABBREV_TAC`bvs:ref_value list = MAP X Y` >>
        qsuff_tac`EL n rd.sm ∉ set (MAP FST (ZIP (rs,bvs)))` >- (
          strip_tac >>
          simp[FUPDATE_LIST_APPLY_NOT_MEM] >>
          match_mp_tac (MP_CANON (GEN_ALL sv_refv_rel_mono)) >>
          rfs[MEM_ZIP,PULL_EXISTS] >>
          qpat_assum`∀n. n < LENGTH rd.sm ⇒X`(qspec_then`n`mp_tac) >>
          simp[EL_MAP] >> strip_tac >>
          HINT_EXISTS_TAC >> simp[] >> rw[] >>
          match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
          qexists_tac`rd` >> simp[]) >>
        simp[MAP_ZIP,Abbr`bvs`] >>
        metis_tac[MEM_EL]) >>
      fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
      simp[ALL_DISTINCT_APPEND,FILTER_APPEND,Abbr`ccs`] ) >>
    Cases_on`beh`>>fs[] >- (
      conj_tac >- (
        qspecl_then[`cenv`,`TCNonTail`,`sz`,`exp`,`0`,`ccs`,`LENGTH defs`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1(CONJUNCT2 compile_append_out)) >>
        qspecl_then[`cenv'`,`TCNonTail`,`sz + LENGTH defs`,`ccs`,`exp`](Q.X_CHOOSE_THEN`ce`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
        `bs1.code = bs.code` by rw[Abbr`bs1`] >>
        simp[Once SWAP_REVERSE] >> strip_tac >>
        qspecl_then[`cenv`,`TCNonTail`,`sz`,`exp`,`0`,`ccs`,`LENGTH defs`]mp_tac compile_bindings_thm >>
        simp[] >>
        Q.PAT_ABBREV_TAC`cenv1 = ls ++ cenv` >>
        `cenv1 = cenv'` by simp[Abbr`cenv1`,Abbr`cenv'`,LIST_EQ_REWRITE] >>
        simp[] >> strip_tac >>
        first_x_assum(qspecl_then[`rd'`,`ccs`,`cenv'`,`sz+(LENGTH defs)`,`bs1`,`bce`,`bcr`,`bc0++cc`,`REVERSE ce`]mp_tac) >>
        simp[] >>
        discharge_hyps >- (
          rpt (BasicProvers.VAR_EQ_TAC) >>
          fs[Cenv_bs_def,s_refs_def,Abbr`bs1`,FILTER_APPEND,ALL_DISTINCT_APPEND] >>
          fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] ) >>
        disch_then(mp_tac o CONJUNCT1) >>
        simp[code_for_push_def] >>
        asm_simp_tac(srw_ss()++DNF_ss)[] >>
        map_every qx_gen_tac[`rf1`,`rd1`,`ck`,`gv1`,`bv1`] >>
        strip_tac >>
        map_every qexists_tac[`rf1`,`rd1`,`ck`,`gv1`,`bv1`] >>
        conj_tac >- (
          qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
          qmatch_abbrev_tac`bc_next^* bs bs3` >>
          qsuff_tac `bc_next bs2 bs3` >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
          simp[bc_eval1_thm] >>
          `bc_fetch bs2 = SOME (Stack (Pops (LENGTH defs)))` by (
            match_mp_tac bc_fetch_next_addr >>
            qpat_assum`bs.code = X`(assume_tac o SYM) >>
            `bs.code = bc0 ++ code ++ bc1` by metis_tac[APPEND_ASSOC] >>
            simp[Abbr`bs2`] >>
            qexists_tac`bc0 ++ cc ++ REVERSE ce` >>
            simp[] ) >>
          simp[bc_eval1_def] >>
          simp[bc_eval_stack_def,Abbr`bs2`,bump_pc_def] >>
          simp[Abbr`bs1`,Abbr`bs3`,bc_state_component_equality,SUM_APPEND,FILTER_APPEND] >>
          Q.PAT_ABBREV_TAC`f = (X:def->bc_value)` >>
          lrw[DROP_APPEND1,DROP_LENGTH_NIL_rwt] ) >>
        conj_tac >- fs[Abbr`bs1`] >>
        conj_asm2_tac >- (
          match_mp_tac Cenv_bs_imp_incsz_irr >>
          qexists_tac`bs with <| code := bce ; refs := rf1; clock := ck; globals := gv1 |>` >>
          simp[bc_state_component_equality] >>
          match_mp_tac Cenv_bs_change_store >>
          map_every qexists_tac[`rd`,`s`,`bs with code := bce`] >>
          simp[bc_state_component_equality] >>
          fs[Cenv_bs_def,s_refs_def,good_rd_def,Abbr`bs1`] ) >>
        fs[Abbr`rd'`] >>
        reverse conj_tac >- (
          conj_tac >- metis_tac[SUBMAP_TRANS] >>
          fs[Abbr`bs1`] ) >>
        match_mp_tac SUBMAP_TRANS >>
        qexists_tac`DRESTRICT bs1.refs (COMPL (set rd.sm))` >>
        simp[] >>
        simp[SUBMAP_DEF,DRESTRICT_DEF] >>
        rw[] >- (
          simp[Abbr`bs1`] >>
          match_mp_tac EQ_SYM >>
          match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
          simp[MAP_ZIP] >>
          fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY] >>
          metis_tac[] ) >>
        pop_assum mp_tac >>
        simp[Abbr`bs1`,FDOM_FUPDATE_LIST] ) >>
      rpt gen_tac >>
      Q.PAT_ABBREV_TAC`tt:call_context = X` >>
      qspecl_then[`cenv`,`tt`,`sz`,`exp`,`0`,`ccs`,`LENGTH defs`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1(CONJUNCT2 compile_append_out)) >>
      qspecl_then[`cenv'`,`TCTail (LENGTH args) (LENGTH klvs + LENGTH defs)`,`sz + LENGTH defs`,`ccs`,`exp`](Q.X_CHOOSE_THEN`ce`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      `bs1.code = bs.code` by rw[Abbr`bs1`] >>
      simp[Once SWAP_REVERSE] >> strip_tac >>
      qspecl_then[`cenv`,`tt`,`sz`,`exp`,`0`,`ccs`,`LENGTH defs`]mp_tac compile_bindings_thm >>
      simp[Abbr`tt`] >>
      Q.PAT_ABBREV_TAC`cenv1 = ls ++ cenv` >>
      `cenv1 = cenv'` by simp[Abbr`cenv1`,Abbr`cenv'`,LIST_EQ_REWRITE] >>
      simp[] >> strip_tac >>
      first_x_assum(qspecl_then[`rd'`,`ccs`,`cenv'`,`sz+(LENGTH defs)`,`bs1`,`bce`,`bcr`,`bc0++cc`,`REVERSE ce`]mp_tac) >>
      simp[] >>
      discharge_hyps >- (
        rpt (BasicProvers.VAR_EQ_TAC) >>
        fs[Cenv_bs_def,s_refs_def,Abbr`bs1`,FILTER_APPEND,ALL_DISTINCT_APPEND] >>
        fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] ) >>
      disch_then(qspecl_then[`env0`,`vs`]mp_tac o CONJUNCT2) >>
      fs[FOLDL_FUPDATE_LIST] >>
      simp[Abbr`cenv'`] >>
      Q.PAT_ABBREV_TAC`klvs2:Cv list = GENLIST X Y` >>
      qpat_assum`Abbrev(bs1 = X)`mp_tac >>
      Q.PAT_ABBREV_TAC`bvs:bc_value list = (MAP X defs)` >>
      strip_tac >>
      disch_then(qspecl_then[`bvs++blvs`]mp_tac) >>
      simp[Abbr`bs1`] >>
      disch_then(qspec_then`args`mp_tac) >>
      simp[] >>
      discharge_hyps >- (
        conj_tac >- simp[ADD_SYM] >>
        conj_tac >- (
          fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
          `rd'.sm = rd.sm` by rw[Abbr`rd'`] >>
          rw[] >>
          match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
          qexists_tac`rd` >> simp[] ) >>
        fs[EVERY2_EVERY] >>
        conj_asm1_tac >- simp[Abbr`klvs2`,Abbr`bvs`] >>
        simp[GSYM ZIP_APPEND] >>
        conj_tac >- (
          rator_x_assum`RTC`kall_tac >>
          simp[EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
          srw_tac[DNF_ss][EL_MAP,Abbr`klvs2`,EL_REVERSE,PRE_SUB1] >>
          fs[Abbr`bvs`,EL_MAP] >>
          qabbrev_tac`def = EL n defs` >>
          `MEM def defs` by metis_tac[MEM_EL] >>
          fs[EVERY_MEM] >>
          `code_env_cd bce ((LENGTH klvs + LENGTH vs + LENGTH env0,LENGTH defs,n),(THE(FST def)),(SND def))` by (
            last_x_assum match_mp_tac >>
            simp[free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
            simp_tac(srw_ss()++DNF_ss)[] >>
            qexists_tac`n` >>
            qunabbrev_tac`def` >> qabbrev_tac`def = EL n defs` >>
            res_tac >>
            PairCases_on`def` >> Cases_on`def0` >> fs[] >>
            PairCases_on`x`>>simp[] ) >>
          res_tac >>
          PairCases_on`def`>>Cases_on`def0`>>fs[]>>PairCases_on`x`>>
          qpat_assum`X ++ A = Y ++ Z`(assume_tac o SYM) >>
          fs[code_env_cd_def,bc_find_loc_def,good_cd_def] >>
          simp[Once Cv_bv_cases,el_check_def] >>
          qpat_assum`X = bind_fv A B C`mp_tac >>
          simp[bind_fv_def] >>
          strip_tac >>
          conj_asm1_tac >- (
            rw[EVERY_FILTER,EVERY_GENLIST] ) >>
          conj_asm1_tac >- (
            rw[] >> fsrw_tac[ARITH_ss][EVERY2_EVERY] >> rfs[] >>
            fsrw_tac[ARITH_ss][] ) >>
          conj_asm1_tac >- (
            qsuff_tac`MEM (Label x0) bce` >- (
              metis_tac[bc_find_loc_aux_append_code,bc_find_loc_aux_NONE,optionTheory.option_CASES,optionTheory.THE_DEF] ) >>
            rw[]) >>
          simp[Once Cv_bv_cases] >>
          conj_tac >- (
            gen_tac >> strip_tac >>
            Q.PAT_ABBREV_TAC`recs:num list = FILTER X Y` >>
            conj_asm1_tac >- (
              rw[] >> fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] ) >>
            simp[EL_APPEND1,EL_MAP] >>
            map_every qexists_tac[`klvs ++ REVERSE vs ++ env0`,`defs`,`EL i recs`] >>
            simp[FLOOKUP_DEF,Abbr`rd'`,FDOM_FUPDATE_LIST,MEM_MAP,MEM_GENLIST,EXISTS_PROD] >>
            conj_tac >- metis_tac[] >>
            qho_match_abbrev_tac`(fm |++ ls) ' k = X` >>
            qho_match_abbrev_tac`P ((fm |++ ls) ' k)` >>
            ho_match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
            `MAP FST ls = rs` by (
              simp[LIST_EQ_REWRITE,Abbr`ls`,EL_MAP] ) >>
            simp[] >>
            simp[MEM_EL,Abbr`ls`,Abbr`P`] >>
            qexists_tac`EL i recs` >>
            simp[Abbr`k`] ) >>
          gen_tac >> strip_tac >>
          Q.PAT_ABBREV_TAC`envs:num list = MAP X Y` >>
          `i < LENGTH envs` by rw[Abbr`envs`] >>
          simp[EL_APPEND2,EL_MAP] >>
          conj_asm1_tac >- (
            fs[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM] ) >>
          rator_x_assum`Cenv_bs`kall_tac >>
          rator_x_assum`Cenv_bs`mp_tac >>
          simp[Cenv_bs_def,env_renv_def,EVERY2_EVERY,EVERY_MEM] >> strip_tac >>
          `LENGTH blvs = LENGTH klvs` by rw[] >> fsrw_tac[ARITH_ss][] >>
          `LENGTH args = LENGTH vs` by rw[] >> fsrw_tac[ARITH_ss][] >>
          rev_full_simp_tac(srw_ss()++ARITH_ss)[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
          qpat_assum`∀n. n < LENGTH cenv ⇒ P`(qspec_then`EL i envs`mp_tac) >>
          simp[option_case_NONE_F] >> rw[] >> simp[] >>
          match_mp_tac (GEN_ALL (MP_CANON (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
          HINT_EXISTS_TAC >> simp[] >>
          simp[Abbr`rd'`] ) >>
        fs[EVERY_MEM,FORALL_PROD] >> rw[] >>
        match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
        qexists_tac`rd` >> simp[] >>
        simp[Abbr`rd'`] ) >>
      simp[code_for_return_def] >>
      asm_simp_tac(srw_ss()++DNF_ss)[] >>
      map_every qx_gen_tac[`bv1`,`rf1`,`rd1`,`ck`,`gv1`] >>
      strip_tac >>
      map_every qexists_tac[`bv1`,`rf1`,`rd1`,`ck`,`gv1`] >>
      conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
      fs[] >>
      fs[Abbr`rd'`] >>
      reverse conj_tac >- metis_tac[SUBMAP_TRANS] >>
      qmatch_assum_abbrev_tac`DRESTRICT xx yy ⊑ DRESTRICT rf1 zz` >>
      match_mp_tac SUBMAP_TRANS >>
      qexists_tac`DRESTRICT xx yy` >>
      simp[] >>
      simp[SUBMAP_DEF,DRESTRICT_DEF,Abbr`yy`] >>
      rw[] >- (
        simp[Abbr`xx`] >>
        match_mp_tac EQ_SYM >>
        match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
        simp[MAP_ZIP] >>
        fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY,Abbr`klvs2`] >>
        simp[MAP_ZIP,TAKE_LENGTH_ID_rwt,Abbr`bvs`] >>
        metis_tac[] ) >>
      fs[Abbr`xx`,FDOM_FUPDATE_LIST]) >>
    rpt gen_tac >>
    qspecl_then[`cenv`,`t`,`sz`,`exp`,`0`,`ccs`,`LENGTH defs`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1(CONJUNCT2 compile_append_out)) >>
    qspecl_then[`cenv`,`t`,`sz`,`exp`,`0`,`ccs`,`LENGTH defs`]mp_tac compile_bindings_thm >>
    Q.PAT_ABBREV_TAC`tt:call_context = call_context_CASE X Y Z` >>
    qspecl_then[`cenv'`,`tt`,`sz + LENGTH defs`,`ccs`,`exp`](Q.X_CHOOSE_THEN`ce`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    `bs1.code = bs.code` by rw[Abbr`bs1`] >>
    simp[Once SWAP_REVERSE] >>
    Q.PAT_ABBREV_TAC`cenv1 = ls ++ cenv` >>
    `cenv1 = cenv'` by simp[Abbr`cenv1`,Abbr`cenv'`,LIST_EQ_REWRITE] >>
    simp[] >> strip_tac >>
    reverse(rw[])>>
    first_x_assum(qspecl_then[`rd'`,`ccs`,`cenv'`,`sz+(LENGTH defs)`,`bs1`,`bce`,`bcr`,`bc0++cc`,`REVERSE ce`]mp_tac) >>
    simp[] >> (
    discharge_hyps >- (
      rpt (BasicProvers.VAR_EQ_TAC) >>
      fs[Cenv_bs_def,s_refs_def,Abbr`bs1`,FILTER_APPEND,ALL_DISTINCT_APPEND] >>
      fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >> NO_TAC)) >>
    disch_then(qspec_then`tt`mp_tac) >>
    simp[Abbr`bs1`] >>
    TRY(disch_then(qspec_then`st`mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
    simp[] >> (
    discharge_hyps >- (
      simp[Abbr`tt`] >>
      Cases_on`t`>>fs[] >>
      CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
      qexists_tac`ig'` >> simp[] >>
      qexists_tac`args`>>simp[] )))
    >- (
      qpat_assum`bc_next^* X Y`mp_tac >>
      simp[Abbr`tt`] >>
      Cases_on`t`>>simp[]>- metis_tac[RTC_TRANSITIVE,transitive_def] >>
      rpt strip_tac >> fs[] >> rfs[] >> pop_assum mp_tac >>
      discharge_hyps >- (
        CONV_TAC(RESORT_EXISTS_CONV(List.rev)) >>
        qexists_tac`st` >> simp[] >>
        qexists_tac`args`>>simp[] >>
        metis_tac[RTC_TRANSITIVE,transitive_def]) >>
      metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
    simp[code_for_return_def] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac[`bv`,`rf`,`rd''`,`ck`,`gv`] >> strip_tac >>
    map_every qexists_tac[`bv`,`rf`,`rd''`,`ck`,`gv`] >>
    fs[] >>
    reverse conj_tac >- (
      `rd'.sm = rd.sm` by simp[Abbr`rd'`] >>
      reverse conj_tac >- metis_tac[IS_PREFIX_TRANS,SUBMAP_TRANS] >>
      match_mp_tac SUBMAP_TRANS >> HINT_EXISTS_TAC >>
      simp[SUBMAP_DEF,FDOM_DRESTRICT,FDOM_FUPDATE_LIST] >>
      simp[DRESTRICT_DEF,FDOM_FUPDATE_LIST] >>
      rw[] >>
      match_mp_tac EQ_SYM >>
      match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
      simp[MAP_ZIP] >>
      fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF] >>
      metis_tac[] ) >>
    ntac 5 (pop_assum kall_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    metis_tac[RTC_TRANSITIVE,transitive_def]) >>
  strip_tac >- (
    simp[] >> ntac 6 gen_tac >> qx_gen_tac `fenv` >> rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    simp[compile_def,FOLDL_UNION_BIGUNION] >>
    Q.PAT_ABBREV_TAC`mtk = if ck then [Tick] else []` >>
    simp_tac(srw_ss()++ETA_ss)[] >>
    strip_tac >> rfs[] >> fs[] >>
    BasicProvers.VAR_EQ_TAC >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
    Q.PAT_ABBREV_TAC`cs0 = compile cenv X sz cs exp` >>
    qspecl_then[`cenv`,`sz+1`,`cs0`,`exps`](Q.X_CHOOSE_THEN`cxs`strip_assume_tac)(CONJUNCT2 (CONJUNCT2 compile_append_out)) >> fs[] >>
    reverse(Cases_on`∃bc10. code = REVERSE cx ++ REVERSE cxs ++ bc10`) >- (
      fsrw_tac[DNF_ss][] >>
      rpt conj_tac >> rpt gen_tac >>
      rw[FOLDL_emit_append_out,Once SWAP_REVERSE,Abbr`mtk`] >>
      TRY(Cases_on`t`)>>fs[Once SWAP_REVERSE]) >> fs[] >>
    reverse(Cases_on`bs.code = bc0 ++ REVERSE cx ++ REVERSE cxs ++ bc10 ++ bc1`) >- fs[] >>
    fs[Once SWAP_REVERSE] >>
    simp[FOLDL_emit_append_out] >>
    fs[Once SWAP_REVERSE] >>
    fs[Once SWAP_REVERSE] >>
    last_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cx`]mp_tac) >>
    `LENGTH (SND (FST s)) ≤ LENGTH (SND (FST s')) ∧ LENGTH (SND (FST s')) ≤ LENGTH s'' ∧ LENGTH s'' ≤ LENGTH (SND (FST s'''))` by
      metis_tac[Cevaluate_store_SUBSET,FST,SND] >>
    simp[] >>
    disch_then(mp_tac o SIMP_RULE(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] o CONJUNCT1) >>
    disch_then(qx_choosel_then[`rf`,`rd'`,`ck'`,`gv'`,`bf`]strip_assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    last_x_assum(qspecl_then[`rd'`,`cs0`,`cenv`,`sz+1`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE cx`,`REVERSE cxs`]mp_tac) >>
    simp[Abbr`bs1`] >>
    discharge_hyps >- (
      simp[Abbr`cs0`] >>
      fsrw_tac[DNF_ss][] >>
      qspecl_then[`s`,`env`,`exp`,`s',Rval(CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
      simp[] >> strip_tac >>
      qspecl_then[`s`,`env`,`exp`,`s',Rval(CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
      simp[] >> strip_tac >>
      conj_tac >- (  fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >> metis_tac[] ) >>
      conj_tac >- (  fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >> metis_tac[] ) >>
      conj_tac >- (
        imp_res_tac RTC_bc_next_clock_less >>
        rfs[Cenv_bs_def,s_refs_def,optionTheory.OPTREL_def]) >>
      match_mp_tac compile_labels_lemma >>
      map_every qexists_tac [`cenv`,`TCNonTail`,`sz`,`cs`,`exp`,`bc0`,`REVERSE cx`] >>
      rw[] ) >>
    disch_then(mp_tac o SIMP_RULE(srw_ss()++DNF_ss)[code_for_push_def,LET_THM]) >>
    disch_then(qx_choosel_then[`bvs`,`rfs`,`rd''`,`ck''`,`gv''`]strip_assume_tac) >>
    let
      fun tac0 t =
        qmatch_assum_abbrev_tac`Cv_bv (ps',l2a) cl bf` >>
        `Cv_bv (rd'', l2a) cl bf` by (
          match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
          qexists_tac`rd'` >>
          rw[] >>
          fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY,SUBMAP_DEF,SUBSET_DEF]) >>
        pop_assum mp_tac >>
        simp[Abbr`cl`,Once Cv_bv_cases,el_check_def] >>
        disch_then(qx_choosel_then[`a`,`azb`,`bve`,`cd`,`envs`,`l`,`recs`]strip_assume_tac) >>
        qho_match_abbrev_tac t >>
        qmatch_assum_abbrev_tac`bc_next^* bs0 bs3` >>
        qmatch_assum_abbrev_tac`bc_next^* bs bs0'` >>
        `bs0' = bs0` by (
          simp[Abbr`bs0`,Abbr`bs0'`,bc_state_component_equality] >>
          imp_res_tac RTC_bc_next_clock_less >>
          rfs[s_refs_def,Cenv_bs_def,optionTheory.OPTREL_def] )
      val tac5 =
        fs[el_check_def] >>
        qmatch_assum_rename_tac`EL n defs = (SOME (l,ccenv,recs,envs),azb)`[]>>
        qmatch_assum_abbrev_tac`EL n defs = (SOME cc,azb)`>>
        `code_env_cd bce ((LENGTH fenv,LENGTH defs,n),cc,azb)` by (
          qspecl_then[`s`,`env`,`exp`,`s',Rval(CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
          simp[] >> strip_tac >>
          fsrw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
          pop_assum(qspec_then`(LENGTH fenv,LENGTH defs,n),cc,azb`mp_tac) >>
          discharge_hyps >- (
            PairCases_on`azb`>>
            simp[Abbr`cc`,free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
            simp_tac(srw_ss()++DNF_ss)[] >>
            qexists_tac`n` >> simp[]) >>
          fs[EVERY_MEM,vlabs_csg_def] >>
          metis_tac[] ) >>
        pop_assum mp_tac >>
        qunabbrev_tac`cc` >>
        PairCases_on`azb` >>
        simp[code_env_cd_def] >>
        simp[GSYM AND_IMP_INTRO] >> strip_tac >>
        disch_then(qx_choosel_then[`csc`,`cb0`,`cc`,`cb1`] strip_assume_tac) >>
        pop_assum (assume_tac o SYM) >>
        first_x_assum (qspecl_then[`rd''`,`csc`,`MAP CTEnv ccenv`,`0`,`bs1`,`bce`,`bcr`,`cb0 ++ [Label l]`,`REVERSE cc`,`cb1 ++ bcr`]mp_tac) >>
        simp[] >>
        discharge_hyps >- (
          fs[good_cd_def] >>
          `ALL_DISTINCT (FILTER is_Label bce)` by fs[contains_primitives_def] >>
          conj_tac >- (
            qspecl_then[`s'`,`env`,`exps`,`((count',s''),g),Rval vs`]mp_tac(CONJUNCT2 Cevaluate_all_vlabs) >>
            qspecl_then[`s`,`env`,`exp`,`s',Rval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
            simp[all_vlabs_csg_def] ) >>
          conj_tac >- (
            simp[EVERY_REVERSE,EVERY_MAP] >>
            qspecl_then[`s`,`env`,`exp`,`s',Rval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
            qspecl_then[`s'`,`env`,`exps`,`((count',s''),g),Rval vs`]mp_tac(CONJUNCT2 Cevaluate_all_vlabs) >>
            simp[] >> fs[EVERY_MEM,all_vlabs_csg_def] >> metis_tac[MEM_EL] ) >>
          conj_tac >- (
            qspecl_then[`s`,`env`,`exp`,`s',Rval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
            simp[] >> simp[EVERY_MEM] >> strip_tac >>
            `all_labs_def (EL n defs)` by metis_tac[MEM_EL] >>
            pop_assum mp_tac >> simp[] ) >>
          conj_tac >- (
            qspecl_then[`s`,`env`,`exp`,`s',Rval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
            simp[] >> strip_tac >>
            qmatch_assum_abbrev_tac`set X ⊆ Y` >>
            simp[EVERY_MEM] >>
            qx_gen_tac`z` >> strip_tac >>
            qsuff_tac`z ∈ Y`>-(fs[EVERY_MEM,vlabs_csg_def]>>metis_tac[IN_UNION])>>
            qsuff_tac`MEM z X`>-metis_tac[SUBSET_DEF] >>
            simp[Abbr`X`,free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
            simp_tac(srw_ss()++DNF_ss)[] >>
            qexists_tac`n` >> simp[] ) >>
          conj_tac >- (
            qspecl_then[`s`,`env`,`exp`,`s',Rval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
            qspecl_then[`s'`,`env`,`exps`,`((count',s''),g),Rval vs`]mp_tac(CONJUNCT2 Cevaluate_vlabs) >>
            simp[] >>
            fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >>
            metis_tac[] ) >>
          conj_tac >- (
            qspecl_then[`s`,`env`,`exp`,`s',Rval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
            simp[] >> strip_tac >>
            simp[vlabs_list_MAP] >>
            fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,MEM_MAP] >>
            fsrw_tac[DNF_ss][vlabs_list_MAP,MEM_MAP,vlabs_csg_def] >>
            reverse conj_tac >- metis_tac[MEM_EL] >>
            reverse conj_tac >- metis_tac[MEM_EL] >>
            reverse conj_tac >- metis_tac[MEM_EL] >>
            qspecl_then[`s'`,`env`,`exps`,`((count',s''),g),Rval vs`]mp_tac(CONJUNCT2 Cevaluate_vlabs) >>
            simp[] >>
            fsrw_tac[DNF_ss][vlabs_list_MAP,MEM_MAP,SUBSET_DEF,vlabs_csg_def] >>
            qx_genl_tac[`cd`,`x`] >> rpt strip_tac >>
            first_x_assum(qspecl_then[`cd`,`x`]mp_tac) >>
            rw[] >> metis_tac[MEM_EL]) >>
          conj_tac >- (
            qspecl_then[`s`,`env`,`exp`,`s',Rval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
            qspecl_then[`s'`,`env`,`exps`,`((count',s''),g),Rval vs`]mp_tac(CONJUNCT2 Cevaluate_vlabs) >>
            simp[] >>
            fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >>
            metis_tac[] ) >>
          conj_asm1_tac >- (
            fs[Abbr`bs1`,Abbr`l2a`] >>
            qspecl_then[`bce`,`bs.inst_length`,`l`,`0`]mp_tac bc_find_loc_aux_ALL_DISTINCT >>
            simp[] >>
            disch_then(qspec_then`LENGTH cb0`mp_tac) >>
            srw_tac[ARITH_ss][] >>
            pop_assum mp_tac >>
            REWRITE_TAC[GSYM APPEND_ASSOC] >>
            rw[EL_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
            simp[FILTER_APPEND] ) >>
          conj_tac >- simp[Abbr`bs1`] >>
          conj_tac >- simp[Abbr`bs1`] >>
          conj_tac >- (
            match_mp_tac Cenv_bs_bind_fv >>
            qexists_tac`ccenv`>>simp[]>>
            simp[Abbr`bs1`]>>
            map_every qexists_tac[`bvs`,`a`,`bs.stack`] >> simp[] >>
            map_every qexists_tac[`fenv`,`defs`,`n`] >> simp[] >>
            qpat_assum`X = bind_fv A Z Y`(assume_tac o SYM) >>
            qexists_tac`e`>>simp[]>>
            fs[s_refs_def,Cenv_bs_def,good_rd_def] >>
            TRY (
            conj_tac >- (
              fsrw_tac[ARITH_ss][fmap_rel_def,env_renv_def] >>
              qx_gen_tac`mn`>>strip_tac >>
              first_x_assum(qspec_then`mn`mp_tac) >>
              first_x_assum(qspec_then`mn`mp_tac) >>
              simp[] >> strip_tac >> strip_tac >>
              match_mp_tac(GEN_ALL(MP_CANON(EVERY2_MEM_MONO))) >>
              HINT_EXISTS_TAC >> simp[] >>
              simp[FORALL_PROD] >> fs[EVERY2_EVERY] >>
              simp[MEM_ZIP] >> simp_tac(srw_ss()++DNF_ss)[] >>
              qx_gen_tac`m`>>strip_tac >> pop_assum mp_tac >>
              simp[EL_MAP,el_check_def,ADD1] >>
              BasicProvers.CASE_TAC >>
              simp[EL_APPEND1,REVERSE_APPEND] >>
              metis_tac[CONS_APPEND,APPEND_ASSOC] )) >>
            qspecl_then[`bce`,`bs.inst_length`,`l`,`0`]mp_tac bc_find_loc_aux_ALL_DISTINCT >>
            simp[] >>
            disch_then(qspec_then`LENGTH cb0`mp_tac) >>
            srw_tac[ARITH_ss][] >>
            pop_assum mp_tac >>
            REWRITE_TAC[GSYM APPEND_ASSOC] >>
            rw[EL_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
            simp[FILTER_APPEND] ) >>
          qpat_assum`X = bce`(assume_tac o SYM) >>
          fs[ALL_DISTINCT_APPEND,FILTER_APPEND] ) >>
        fs[]
      fun tac6 t =
        fs[] >> ntac 2 (pop_assum kall_tac) >>
        `bc_fetch bs3 = SOME (Stack (Load (LENGTH exps)))` by (
          match_mp_tac bc_fetch_next_addr >>
          rw[Abbr`bs3`,REVERSE_APPEND] >>
          qexists_tac`bc0 ++ REVERSE cx ++ REVERSE cxs` >>
          rw[] ) >>
        simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
        rw[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def] >>
        `LENGTH exps = LENGTH bvs` by (fs[EVERY2_EVERY] >> metis_tac[Cevaluate_list_LENGTH] ) >>
        simp[Abbr`bs3`] >>
        lrw[EL_APPEND2] >>
        simp[bump_pc_with_stack] >> fs[bc_fetch_with_stack] >>
        simp[bump_pc_def] >>
        qpat_assum`bc_fetch X = Y` kall_tac >>
        qho_match_abbrev_tac t >>
        `bc_fetch bs1 = SOME (Stack (El 1))` by (
          match_mp_tac bc_fetch_next_addr >>
          rw[Abbr`bs1`] >>
          Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
          qexists_tac`ls ++ [Stack (Load (LENGTH bvs))]` >>
          rw[Abbr`ls`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
        simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
        rw[bc_eval1_thm,bc_eval1_def] >>
        simp[Abbr`bs1`,bc_eval_stack_def] >>
        fs[bump_pc_with_stack,bc_fetch_with_stack] >>
        simp[bump_pc_def] >>
        qpat_assum`bc_fetch X = Y` kall_tac >>
        qho_match_abbrev_tac t >>
        `bc_fetch bs1 = SOME (Stack (Load (SUC(LENGTH bvs))))` by (
          match_mp_tac bc_fetch_next_addr >>
          rw[Abbr`bs1`] >>
          Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
          Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
          qexists_tac`ls ++ TAKE 2 l2` >>
          srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
        simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
        rw[bc_eval1_thm,bc_eval1_def] >>
        simp[Abbr`bs1`,bc_eval_stack_def] >>
        lrw[EL_APPEND2,EL_APPEND1] >>
        fs[bc_fetch_with_stack,bump_pc_with_stack] >>
        rw[bump_pc_def] >>
        qpat_assum`bc_fetch X = Y` kall_tac >>
        qho_match_abbrev_tac t >>
        `bc_fetch bs1 = SOME (Stack (El 0))` by (
          match_mp_tac bc_fetch_next_addr >>
          rw[Abbr`bs1`] >>
          Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
          Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
          qexists_tac`ls ++ TAKE 3 l2` >>
          srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
        simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
        rw[bc_eval1_thm,bc_eval1_def] >>
        simp[Abbr`bs1`,bc_eval_stack_def] >>
        fs[bc_fetch_with_stack,bump_pc_with_stack] >>
        fsrw_tac[ARITH_ss][] >>
        rw[bump_pc_def] >>
        qho_match_abbrev_tac t >>
        `bc_next^* bs1 (bs1 with <| clock := SOME cka; pc := next_addr bs.inst_length (BUTLASTN (1 + LENGTH bc1) bs.code) |>)` by (
          simp[Abbr`mtk`,Abbr`cka`] >>
          Cases_on`ck`>>simp[]>-(
            `bc_fetch bs1 = SOME Tick` by (
              match_mp_tac bc_fetch_next_addr >>
              rw[Abbr`bs1`] >>
              Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
              Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
              qexists_tac`ls ++ TAKE 4 l2` >>
              srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
            match_mp_tac RTC_SUBSET >>
            simp[bc_eval1_thm,bc_eval1_def] >>
            simp[bump_pc_def] >>
            simp[Abbr`bs1`,bc_state_component_equality] >>
            imp_res_tac RTC_bc_next_clock_less >>
            rfs[Cenv_bs_def,s_refs_def,optionTheory.OPTREL_def,bc_state_component_equality] >> fs[] >>
            simp[FILTER_APPEND,SUM_APPEND,BUTLASTN_APPEND1,BUTLASTN,ADD1] ) >>
          simp[Once RTC_CASES1] >> disj1_tac >>
          simp[bc_state_component_equality,Abbr`bs1`] >>
          simp[FILTER_APPEND,SUM_APPEND,BUTLASTN_APPEND1,BUTLASTN,ADD1] >>
          imp_res_tac RTC_bc_next_clock_less >>
          rfs[Cenv_bs_def,s_refs_def,optionTheory.OPTREL_def,bc_state_component_equality] >> fs[] ) >>
        qmatch_assum_abbrev_tac`bc_next^* bs1 bs3`
      val tac1 =
        tac0 `∃rf sm ck gv bv. bc_next^* bs (bs2 rf ck gv bv) ∧ P rf sm ck gv bv` >>
        qsuff_tac `∃rf sm ck gv bv. bc_next^* bs3 (bs2 rf ck gv bv) ∧ P rf sm ck gv bv` >-
          metis_tac[RTC_TRANSITIVE,transitive_def] >>
        tac6 `∃rf sm ck gv bv. bc_next^* bs1 (bs2 rf ck gv bv) ∧ P rf sm ck gv bv` >>
        qsuff_tac `∃rf sm ck gv bv. bc_next^* bs3 (bs2 rf ck gv bv) ∧ P rf sm ck gv bv` >-
          metis_tac[RTC_TRANSITIVE,transitive_def] >>
        `bc_fetch bs3 = SOME CallPtr` by (
          match_mp_tac bc_fetch_next_addr >>
          rw[Abbr`bs3`,Abbr`bs1`] >>
          Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
          Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
          qexists_tac`ls ++ l2 ++ mtk` >>
          srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] >>
          simp[BUTLASTN_APPEND1,BUTLASTN,SUM_APPEND,FILTER_APPEND]) >>
        simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
        rw[bc_eval1_thm,bc_eval1_def] >>
        simp[Abbr`bs1`,Abbr`bs3`] >>
        fs[bc_fetch_with_stack,bump_pc_with_stack] >>
        fsrw_tac[ARITH_ss][] >>
        rw[bump_pc_def] >> rfs[] >>
        qpat_assum`bc_fetch X = Y` kall_tac >>
        qpat_assum`bc_fetch X = Y` kall_tac >>
        Q.PAT_ABBREV_TAC`ret = x + 1` >>
        qho_match_abbrev_tac`∃rf sm ck gv bv. bc_next^* bs1 (bs2 rf ck gv bv) ∧ P rf sm ck gv bv` >>
        tac5
      val tac3 =
        disch_then(qspecl_then[`st`,`REVERSE bvs`]mp_tac o (CONV_RULE(RESORT_FORALL_CONV List.rev))) >> simp[] >>
        disch_then(qspecl_then[`ck`,`REVERSE args0`]mp_tac) >> simp[] >>
        `REVERSE mtk = mtk` by rw[Abbr`mtk`] >>
        disch_then(qspec_then`bc1`mp_tac) >> simp[] >>
        `(LENGTH exps = LENGTH bvs) ∧ (LENGTH klvs = LENGTH blvs)` by (
          fs[EVERY2_EVERY] >> imp_res_tac Cevaluate_list_LENGTH >> fs[] ) >>
        simp[]
      val tac20 =
        qmatch_assum_abbrev_tac`Cv_bv (ps',l2a) cl bf` >>
        `Cv_bv (rd'', l2a) cl bf` by (
          match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
          qexists_tac`rd'` >>
          rw[Abbr`ps'`] >>
          fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY,SUBMAP_DEF,SUBSET_DEF]) >>
        pop_assum mp_tac >>
        simp[Abbr`cl`,Once Cv_bv_cases,el_check_def] >>
        disch_then(qx_choosel_then[`a`,`azb`,`bve`,`cd`,`envs`,`l`,`recs`]strip_assume_tac) >>
        simp[code_for_return_def]
      val tac21 =
        `ck' = SOME(FST (FST s'))` by (
          imp_res_tac RTC_bc_next_clock_less >>
          rfs[Cenv_bs_def,s_refs_def,optionTheory.OPTREL_def] >> fs[] ) >>
        BasicProvers.VAR_EQ_TAC >>
        qmatch_assum_abbrev_tac`bc_next^* bs bs05` >>
        qmatch_assum_abbrev_tac`bc_next^* bs05 bs3`
      fun tac23 st =
        fs[el_check_def] >>
        qmatch_assum_rename_tac`EL n defs = (SOME (l,ccenv,recs,envs),azb)`[]>>
        qmatch_assum_abbrev_tac`EL n defs = (SOME cc,azb)`>>
        `code_env_cd bce ((LENGTH fenv,LENGTH defs,n),cc,azb)` by (
          qspecl_then[`s`,`env`,`exp`,`s',Rval(CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
          simp[] >> strip_tac >>
          fsrw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
          pop_assum(qspec_then`(LENGTH fenv,LENGTH defs,n),cc,azb`mp_tac) >>
          discharge_hyps >- (
            PairCases_on`azb`>>
            simp[Abbr`cc`,free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
            simp_tac(srw_ss()++DNF_ss)[] >>
            qexists_tac`n` >> simp[]) >>
          fs[EVERY_MEM,vlabs_csg_def] >>
          metis_tac[ADD_SYM,ADD_ASSOC] ) >>
        pop_assum mp_tac >>
        qunabbrev_tac`cc` >>
        PairCases_on`azb` >>
        simp[code_env_cd_def] >>
        simp[GSYM AND_IMP_INTRO] >> strip_tac >>
        disch_then(qx_choosel_then[`csc`,`cb0`,`cc`,`cb1`] strip_assume_tac) >>
        pop_assum (assume_tac o SYM) >>
        first_x_assum (qspecl_then[`rd''`,`csc`,`MAP CTEnv ccenv`,`0`,`bs1`,`bce`,`bcr`,`cb0 ++ [Label l]`,`REVERSE cc`,`cb1 ++ bcr`]mp_tac) >>
        simp[] >>
        discharge_hyps >- (
          fs[good_cd_def] >>
          `ALL_DISTINCT (FILTER is_Label bce)` by fs[contains_primitives_def] >>
          conj_tac >- (
            qspecl_then[`s'`,`env`,`exps`,`((count',s''),g),Rval vs`]mp_tac(CONJUNCT2 Cevaluate_all_vlabs) >>
            qspecl_then[`s`,`env`,`exp`,`s',Rval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
            simp[all_vlabs_csg_def] ) >>
          conj_tac >- (
            simp[EVERY_REVERSE,EVERY_MAP] >>
            qspecl_then[`s`,`env`,`exp`,`s',Rval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
            qspecl_then[`s'`,`env`,`exps`,`((count',s''),g),Rval vs`]mp_tac(CONJUNCT2 Cevaluate_all_vlabs) >>
            simp[] >> fs[EVERY_MEM,all_vlabs_csg_def] >> metis_tac[MEM_EL] ) >>
          conj_tac >- (
            qspecl_then[`s`,`env`,`exp`,`s',Rval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
            simp[] >> simp[EVERY_MEM] >> strip_tac >>
            `all_labs_def (EL n defs)` by metis_tac[MEM_EL] >>
            pop_assum mp_tac >> simp[] ) >>
          conj_tac >- (
            qspecl_then[`s`,`env`,`exp`,`s',Rval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
            simp[] >> strip_tac >>
            qmatch_assum_abbrev_tac`set X ⊆ Y` >>
            simp[EVERY_MEM] >>
            qx_gen_tac`z` >> strip_tac >>
            `LENGTH env0 + (LENGTH vs0 + LENGTH blvs) = LENGTH blvs + LENGTH vs0 + LENGTH env0` by simp[] >>
            qsuff_tac`z ∈ Y`>-(fs[EVERY_MEM,vlabs_csg_def]>>metis_tac[IN_UNION])>>
            qsuff_tac`MEM z X`>-metis_tac[SUBSET_DEF] >>
            simp[Abbr`X`,free_labs_defs_MAP,MEM_FLAT,MEM_GENLIST] >>
            simp_tac(srw_ss()++DNF_ss)[] >>
            qexists_tac`n` >> simp[] ) >>
          conj_tac >- (
            qspecl_then[`s`,`env`,`exp`,`s',Rval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
            qspecl_then[`s'`,`env`,`exps`,`((count',s''),g),Rval vs`]mp_tac(CONJUNCT2 Cevaluate_vlabs) >>
            simp[] >>
            fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >>
            metis_tac[] ) >>
          conj_tac >- (
            qspecl_then[`s`,`env`,`exp`,`s',Rval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
            simp[] >> strip_tac >>
            simp[vlabs_list_MAP] >>
            fsrw_tac[ARITH_ss,DNF_ss][SUBSET_DEF,EVERY_MEM,MEM_MAP] >>
            fsrw_tac[DNF_ss][vlabs_list_MAP,MEM_MAP,vlabs_csg_def] >>
            reverse conj_tac >- metis_tac[MEM_EL] >>
            reverse conj_tac >- metis_tac[MEM_EL] >>
            reverse conj_tac >- metis_tac[MEM_EL] >>
            qspecl_then[`s'`,`env`,`exps`,`((count',s''),g),Rval vs`]mp_tac(CONJUNCT2 Cevaluate_vlabs) >>
            simp[] >>
            fsrw_tac[DNF_ss][vlabs_list_MAP,MEM_MAP,SUBSET_DEF,vlabs_csg_def] >>
            qx_genl_tac[`cd`,`x`] >> rpt strip_tac >>
            first_x_assum(qspecl_then[`cd`,`x`]mp_tac) >>
            rw[] >> metis_tac[MEM_EL]) >>
          conj_tac >- (
            qspecl_then[`s`,`env`,`exp`,`s',Rval (CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
            qspecl_then[`s'`,`env`,`exps`,`((count',s''),g),Rval vs`]mp_tac(CONJUNCT2 Cevaluate_vlabs) >>
            simp[] >>
            fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >>
            metis_tac[] ) >>
          conj_asm1_tac >- (
            fs[Abbr`bs1`,Abbr`l2a`] >>
            qspecl_then[`bce`,`bs.inst_length`,`l`,`0`]mp_tac bc_find_loc_aux_ALL_DISTINCT >>
            simp[] >>
            disch_then(qspec_then`LENGTH cb0`mp_tac) >>
            srw_tac[ARITH_ss][] >>
            pop_assum mp_tac >>
            REWRITE_TAC[GSYM APPEND_ASSOC] >>
            rw[EL_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
            simp[FILTER_APPEND] ) >>
          conj_tac >- simp[Abbr`bs1`] >>
          conj_asm1_tac >- (
            TRY(qunabbrev_tac`cka`) >>
            simp[Abbr`bs1`] >>
            imp_res_tac RTC_bc_next_clock_less >>
            rfs[Abbr`bs05`,optionTheory.OPTREL_def,PRE_SUB1] >>
            rfs[Cenv_bs_def,s_refs_def] >> rw[] ) >>
          conj_tac >- (
            match_mp_tac Cenv_bs_bind_fv >>
            qexists_tac`ccenv`>>simp[]>>
            simp[Abbr`bs1`]>>
            map_every qexists_tac[`bvs`,`a`,st] >> simp[] >>
            map_every qexists_tac[`fenv`,`defs`,`n`] >> simp[] >>
            qpat_assum`X = bind_fv A Z Y`(assume_tac o SYM) >>
            (qexists_tac`e`ORELSE qexists_tac`e'`)>>simp[]>>
            fs[s_refs_def,Cenv_bs_def,good_rd_def] >>
            TRY (
            conj_tac >- (
              rator_x_assum`fmap_rel`mp_tac >>
              fs[EVERY2_EVERY] >>
              rpt(BasicProvers.VAR_EQ_TAC) >>
              simp[ADD1,DROP_APPEND1,DROP_APPEND2] >>
              rpt strip_tac >>
              match_mp_tac fmap_rel_env_renv_with_irr >>
              HINT_EXISTS_TAC >>
              simp[])
            ) >>
            qspecl_then[`bce`,`bs.inst_length`,`l`,`0`]mp_tac bc_find_loc_aux_ALL_DISTINCT >>
            simp[] >>
            disch_then(qspec_then`LENGTH cb0`mp_tac) >>
            srw_tac[ARITH_ss][] >>
            pop_assum mp_tac >>
            REWRITE_TAC[GSYM APPEND_ASSOC] >>
            rw[EL_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
            simp[FILTER_APPEND] ) >>
          qpat_assum`X = bce`(assume_tac o SYM) >>
          fs[ALL_DISTINCT_APPEND,FILTER_APPEND] ) >>
        fs[]
      fun tac2 tac3 st =
        tac20 >>
        qho_match_abbrev_tac`∃bv rf sm ck gv. bc_next^* bs (bs2 rf ck gv bv) ∧ P rf bv ck gv sm` >>
        tac21 >>
        qsuff_tac `∃rf bv sm ck gv. bc_next^* bs3 (bs2 rf ck gv bv) ∧ P rf bv ck gv sm` >-
          metis_tac[RTC_TRANSITIVE,transitive_def] >>
        qspec_then`bs3`mp_tac jmpbc_thm >>
        simp[Abbr`bs3`] >>
        tac3 >>
        discharge_hyps >- (
          imp_res_tac RTC_bc_next_clock_less >>
          strip_tac >>
          rfs[optionTheory.OPTREL_def] >>
          fs[Cenv_bs_def,s_refs_def] ) >>
        qmatch_abbrev_tac`bc_next^* bs1 bs3 ⇒ X` >> strip_tac >>
        qsuff_tac `∃rf bv sm ck gv. bc_next^* bs3 (bs2 rf ck gv bv) ∧ P rf bv ck gv sm` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
        map_every qunabbrev_tac[`X`,`bs3`,`bs1`] >>
        pop_assum kall_tac >>
        qho_match_abbrev_tac `∃rf bv sm ck gv. bc_next^* bs1 (bs2 rf ck gv bv) ∧ P rf bv ck gv sm` >>
        tac23 st
    in
      `∀a. (FOLDL (λs i. s with out := i::s.out) a mtk).out = mtk ++ a.out` by (
        simp[Abbr`mtk`] >> rw[] ) >>
      simp[FOLDL_APPEND] >>
      Cases_on`beh`>>fs[] >- (
        qmatch_assum_abbrev_tac`Cevaluate ((cka,s''),g) env' exp' (s''',Rval v)`>>
        pop_assum kall_tac >>
        conj_tac >- (
          srw_tac[DNF_ss][code_for_push_def,LET_THM,Once SWAP_REVERSE] >>
          tac1 >>
          disch_then(qspecl_then[`bs.stack`,`Block closure_tag [CodePtr a; Block 0 bve]`,`bvs`,`ret`,`Block 0 bve`,`[]`]mp_tac
                     o CONV_RULE (RESORT_FORALL_CONV List.rev) o CONJUNCT2) >>
          qpat_assum`X = azb0`(assume_tac o SYM) >>
          `LENGTH vs = LENGTH bvs` by metis_tac[EVERY2_EVERY] >> fs[] >>
          disch_then(qspec_then`vs`mp_tac) >> simp[] >>
          simp[Abbr`bs1`] >>
          simp[code_for_return_def] >>
          disch_then(qx_choosel_then[`bvr`,`rfr`,`smr`,`ckr`,`gvr`]strip_assume_tac) >>
          map_every qexists_tac [`rfr`,`smr`,`ckr`,`gvr`,`bvr`] >>
          simp[Abbr`bs2`] >>
          Q.PAT_ABBREV_TAC`ret' = next_addr X Y` >>
          `ret' = ret` by (
            map_every qunabbrev_tac[`ret`,`ret'`] >>
            srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND,ADD1,BUTLASTN_APPEND1,BUTLASTN] ) >>
          fs[] >>
          conj_tac >- (
            qmatch_assum_abbrev_tac`bc_next^* bsa bsb` >>
            qmatch_abbrev_tac`bc_next^* bsa bsb'` >>
            `bsb = bsb'` by simp[Abbr`bsb`,Abbr`bsb'`,bc_state_component_equality] >>
            rw[] ) >>
          simp[Abbr`P`] >>
          reverse conj_tac >- metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS,gvrel_trans] >>
          match_mp_tac Cenv_bs_imp_incsz_irr >>
          qunabbrev_tac`bs0` >>
          qmatch_assum_abbrev_tac`Cenv_bs rd s renv cenv sz bs0` >>
          qexists_tac`bs0 with <| refs := rfr; clock := ckr; globals := gvr|>` >>
          simp[Abbr`bs0`,bc_state_component_equality] >>
          match_mp_tac Cenv_bs_change_store >>
          qmatch_assum_abbrev_tac`Cenv_bs rd s renv cenv sz bs0` >>
          map_every qexists_tac[`rd`,`s`,`bs0`] >>
          simp[] >>
          fs[s_refs_def,Abbr`l2a`,good_rd_def] >>
          simp[Abbr`bs0`,bc_state_component_equality] >>
          conj_tac >- metis_tac[SUBMAP_TRANS] >>
          conj_tac >- metis_tac[IS_PREFIX_TRANS] >>
          fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
          metis_tac[SUBMAP_TRANS,gvrel_trans]) >>
        asm_simp_tac(srw_ss()++DNF_ss)[] >>
        map_every qx_gen_tac[`env0`,`vs0`,`klvs`,`blvs`,`benv`,`ret`,`args0`,`cl0`,`st`] >>
        simp[Once SWAP_REVERSE] >> strip_tac >>
        (tac2 tac3 `st`) >>
        disch_then(qspecl_then[`st`,`Block closure_tag [CodePtr a; Block 0 bve]`,`bvs`,`ret`,`Block 0 bve`,`[]`]mp_tac
                   o CONV_RULE (RESORT_FORALL_CONV List.rev) o CONJUNCT2) >>
        qpat_assum`X = azb0`(assume_tac o SYM) >>
        `LENGTH vs = LENGTH bvs` by metis_tac[EVERY2_EVERY] >> fs[] >>
        disch_then(qspec_then`vs`mp_tac) >> simp[] >>
        simp[Abbr`bs1`] >>
        simp[code_for_return_def] >>
        disch_then(qx_choosel_then[`bvr`,`rfr`,`smr`,`ckr`,`gvr`]strip_assume_tac) >>
        map_every qexists_tac [`rfr`,`bvr`,`smr`,`ckr`,`gvr`] >>
        simp[Abbr`bs2`,Abbr`P`] >> fs[] >>
        metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS,gvrel_trans]) >>
      rpt gen_tac >>
      Cases_on`t`>>simp[Once SWAP_REVERSE] >> strip_tac >- (
        conj_tac >- (
          rw[] >> simp[code_for_return_def] >>
          CONV_TAC (RESORT_EXISTS_CONV (fn ls => tl ls @ [hd ls])) >>
          qmatch_assum_abbrev_tac`Cevaluate ((cka,s''),g) env' exp' Z` >> qunabbrev_tac`Z` >>
          tac1 >>
          disch_then(qspec_then`TCTail azb0 0`mp_tac) >> simp[] >>
          disch_then(qspec_then`st`mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
          simp[Abbr`bs1`] >>
          discharge_hyps >- (
            CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
            qexists_tac`ig`>>simp[] >>
            qexists_tac`bvs`>>simp[]>>
            fs[EVERY2_EVERY] ) >>
          simp[code_for_return_def,Abbr`P`] >>
          disch_then(qx_choosel_then[`bv`,`rf'`,`rd'''`,`ck'''`,`gv3`]strip_assume_tac) >>
          map_every qexists_tac[`rf'`,`rd'''`,`ck'''`,`gv3`,`bv`] >>
          fs[] >>
          rfs[Abbr`bs2`] >>
          metis_tac[IS_PREFIX_TRANS,SUBMAP_TRANS,gvrel_trans]) >>
        rw[] >>
        qmatch_assum_abbrev_tac`Cevaluate ((cka,s''),g) env' exp' Z` >> qunabbrev_tac`Z` >>
        tac0 `∃bs'. bc_next^* bs bs' ∧ P bs'` >>
        qsuff_tac `∃bs'. bc_next^* bs3 bs' ∧ P bs'` >-
          metis_tac[RTC_TRANSITIVE,transitive_def] >>
        tac6 `∃bs'. bc_next^* bs1 bs' ∧ P bs'` >>
        qsuff_tac `∃bs'. bc_next^* bs3 bs' ∧ P bs'` >-
          metis_tac[RTC_TRANSITIVE,transitive_def] >>
        `bc_fetch bs3 = SOME CallPtr` by (
          match_mp_tac bc_fetch_next_addr >>
          rw[Abbr`bs3`,Abbr`bs1`] >>
          Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
          Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
          qexists_tac`ls ++ l2 ++ mtk` >>
          srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] >>
          simp[BUTLASTN_APPEND1,BUTLASTN,SUM_APPEND,FILTER_APPEND]) >>
        simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
        rw[bc_eval1_thm,bc_eval1_def] >>
        simp[Abbr`bs1`,Abbr`bs3`] >>
        fs[bc_fetch_with_stack,bump_pc_with_stack] >>
        fsrw_tac[ARITH_ss][] >>
        rw[bump_pc_def] >> rfs[] >>
        qpat_assum`bc_fetch X = Y` kall_tac >>
        qpat_assum`bc_fetch X = Y` kall_tac >>
        Q.PAT_ABBREV_TAC`ret = x + 1` >>
        qho_match_abbrev_tac`∃bs'. bc_next^* bs1 bs' ∧ P bs'` >>
        tac5 >>
        disch_then(qspec_then`TCTail azb0 0`mp_tac) >> simp[] >>
        simp[Abbr`P`]>>
        rpt strip_tac >>
        pop_assum mp_tac >>
        discharge_hyps >- (
          simp[Abbr`bs1`] >>
          qexists_tac`[]`>>simp[] >>
          qexists_tac`bvs`>>simp[] >>
          fs[EVERY2_EVERY] >>
          fs[Cenv_bs_def]) >>
        `bs1.output = bs.output` by simp[Abbr`bs1`] >>
        metis_tac[] ) >>
      conj_tac >- (
        rpt gen_tac >> strip_tac >>
        qmatch_assum_rename_tac`ig = blvs ++ [benv; CodePtr ret] ++ REVERSE args ++ [cl0] ++ ig'`[] >>
        (tac2 (
          disch_then(qspecl_then[`ig'++[StackPtr sp; CodePtr hdl]++st`,`REVERSE bvs`]mp_tac o (CONV_RULE(RESORT_FORALL_CONV List.rev))) >> simp[] >>
          disch_then(qspecl_then[`ck`,`REVERSE args`]mp_tac) >> simp[] >>
          `REVERSE mtk = mtk` by rw[Abbr`mtk`] >>
          disch_then(qspec_then`bc1`mp_tac) >> simp[] >>
          `(LENGTH exps = LENGTH bvs)` by (
            fs[EVERY2_EVERY] >> imp_res_tac Cevaluate_list_LENGTH >> fs[] ) >>
          simp[])
          `ig'++[StackPtr sp;CodePtr hdl]++st`) >>
        disch_then(qspec_then`TCTail azb0 0`mp_tac) >> simp[] >>
        disch_then(qspec_then`st`mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
        simp[Abbr`bs1`] >>
        discharge_hyps >- (
          qexists_tac`[]`>>simp[] >>
          qexists_tac`bvs`>>simp[]>>
          fs[EVERY2_EVERY] ) >>
        simp[code_for_return_def,Abbr`P`] >>
        disch_then(qx_choosel_then[`bv`,`rf'`,`rd'''`,`ck'''`,`gv3`]strip_assume_tac) >>
        map_every qexists_tac[`rf'`,`bv`,`rd'''`,`ck'''`,`gv3`] >>
        fs[] >> rfs[Abbr`bs2`] >>
        metis_tac[IS_PREFIX_TRANS,SUBMAP_TRANS,gvrel_trans]) >>
      simp[GSYM AND_IMP_INTRO] >> strip_tac >>
      tac20 >>
      strip_tac >>
      qho_match_abbrev_tac`∃bs'. bc_next^* bs bs' ∧ P bs'` >>
      tac21 >>
      qsuff_tac `∃bs'. bc_next^* bs3 bs' ∧ P bs'` >-
        metis_tac[RTC_TRANSITIVE,transitive_def] >>
      qspec_then`bs3`mp_tac jmpbc_thm >>
      simp[Abbr`bs3`] >>
      disch_then(qspecl_then[`st`]mp_tac o (CONV_RULE(RESORT_FORALL_CONV List.rev))) >> simp[] >>
      disch_then(qspecl_then[`REVERSE bvs`]mp_tac) >> simp[] >>
      disch_then(qspecl_then[`ck`]mp_tac) >> simp[] >>
      `REVERSE mtk = mtk` by rw[Abbr`mtk`] >>
      disch_then(qspecl_then[`REVERSE args`]mp_tac) >> simp[] >>
      disch_then(qspec_then`bc1`mp_tac) >> simp[] >>
      `(LENGTH exps = LENGTH bvs)` by (
        fs[EVERY2_EVERY] >> imp_res_tac Cevaluate_list_LENGTH >> fs[] ) >>
      simp[] >>
      discharge_hyps >- (
        imp_res_tac RTC_bc_next_clock_less >>
        strip_tac >>
        rfs[optionTheory.OPTREL_def] >>
        fs[Cenv_bs_def,s_refs_def] ) >>
      qmatch_abbrev_tac`bc_next^* bs1 bs3 ⇒ X` >> strip_tac >>
      qsuff_tac `∃bs'. bc_next^* bs3 bs' ∧ P bs'` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
      map_every qunabbrev_tac[`X`,`bs3`,`bs1`] >>
      pop_assum kall_tac >>
      qho_match_abbrev_tac `∃bs'. bc_next^* bs1 bs' ∧ P bs'` >>
      tac23 `st` >>
      disch_then(qspec_then`TCTail azb0 0`mp_tac) >> simp[] >>
      simp[Abbr`P`] >>
      `bs1.output = bs.output` by simp[Abbr`bs1`] >> simp[] >>
      disch_then match_mp_tac >>
      simp[Abbr`bs1`] >>
      CONV_TAC(RESORT_EXISTS_CONV(List.rev)) >>
      qexists_tac`st`>>simp[]>>
      qexists_tac`bvs`>>simp[]>>
      fs[EVERY2_EVERY]
    end ) >>
  strip_tac >- (
    simp[] >> ntac 5 gen_tac >> qx_gen_tac `fenv` >> rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    simp[compile_def,FOLDL_UNION_BIGUNION] >>
    simp_tac(srw_ss()++ETA_ss)[] >>
    strip_tac >> rfs[] >> fs[] >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
    Q.PAT_ABBREV_TAC`cs0 = compile cenv X sz cs exp` >>
    qspecl_then[`cenv`,`sz+1`,`cs0`,`exps`](Q.X_CHOOSE_THEN`cxs`strip_assume_tac)(CONJUNCT2 (CONJUNCT2 compile_append_out)) >> fs[] >>
    reverse(Cases_on`∃bc10. code = REVERSE cx ++ REVERSE cxs ++ bc10`) >- (
      fsrw_tac[DNF_ss][] >>
      rpt conj_tac >> rpt gen_tac >>
      rw[FOLDL_emit_append_out,Once SWAP_REVERSE] >>
      TRY(Cases_on`t`)>>fs[Once SWAP_REVERSE]) >> fs[] >>
    reverse(Cases_on`bs.code = bc0 ++ REVERSE cx ++ REVERSE cxs ++ bc10 ++ bc1`) >- fs[] >>
    last_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cx`]mp_tac) >>
    `LENGTH (SND (FST s)) ≤ LENGTH (SND (FST s')) ∧ LENGTH (SND (FST s')) ≤ LENGTH s''` by
      metis_tac[Cevaluate_store_SUBSET,FST,SND] >>
    simp[] >>
    disch_then(mp_tac o SIMP_RULE(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] o CONJUNCT1) >>
    disch_then(qx_choosel_then[`rf`,`rd'`,`ck'`,`gv'`,`bf`]strip_assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    last_x_assum(qspecl_then[`rd'`,`cs0`,`cenv`,`sz+1`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE cx`,`REVERSE cxs`]mp_tac) >>
    simp[Abbr`bs1`] >>
    discharge_hyps >- (
      simp[Abbr`cs0`] >>
      fsrw_tac[DNF_ss][] >>
      qspecl_then[`s`,`env`,`exp`,`s',Rval(CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
      simp[] >> strip_tac >>
      qspecl_then[`s`,`env`,`exp`,`s',Rval(CRecClos fenv defs n)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
      simp[] >> strip_tac >>
      conj_tac >- (  fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >> metis_tac[] ) >>
      conj_tac >- (  fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >> metis_tac[] ) >>
      conj_tac >- (
        imp_res_tac RTC_bc_next_clock_less >>
        rfs[Cenv_bs_def,s_refs_def,optionTheory.OPTREL_def]) >>
      match_mp_tac compile_labels_lemma >>
      map_every qexists_tac [`cenv`,`TCNonTail`,`sz`,`cs`,`exp`,`bc0`,`REVERSE cx`] >>
      rw[] ) >>
    disch_then(mp_tac o SIMP_RULE(srw_ss()++DNF_ss)[code_for_push_def,LET_THM]) >>
    disch_then(qx_choosel_then[`bvs`,`rfs`,`rd''`,`ck''`,`gv''`]strip_assume_tac) >>
    `ck''=SOME 0` by(
      imp_res_tac RTC_bc_next_clock_less >>
      rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
    BasicProvers.VAR_EQ_TAC >>
    qmatch_assum_abbrev_tac`Cv_bv (ps',l2a) cl bf` >>
    `Cv_bv (rd'', l2a) cl bf` by (
      match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
      qexists_tac`rd'` >>
      rw[] >>
      fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY,SUBMAP_DEF,SUBSET_DEF]) >>
    pop_assum mp_tac >>
    simp[Abbr`cl`,Once Cv_bv_cases,el_check_def] >>
    disch_then(qx_choosel_then[`a`,`azb`,`bve`,`cd`,`envs`,`l`,`recs`]strip_assume_tac) >>
    fs[FOLDL_emit_append_out,Once SWAP_REVERSE] >>
    Cases >> simp[Once SWAP_REVERSE] >> rpt strip_tac >>
    qho_match_abbrev_tac`∃bs'. bc_next^* bs bs' ∧ P bs'` >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    qmatch_assum_abbrev_tac`bc_next^* bs1' bs2` >>
    `bs1' = bs1` by (
      simp[bc_state_component_equality,Abbr`bs1`,Abbr`bs1'`] >>
      imp_res_tac RTC_bc_next_clock_less >>
      rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
    (qsuff_tac`∃bs'. bc_next^* bs2 bs' ∧ P bs'` >- metis_tac[RTC_TRANSITIVE,transitive_def]) >>
    fs[Abbr`bs1`,Abbr`bs1'`] >> pop_assum kall_tac >>
    `bc_fetch bs2 = SOME (EL 0 bc10)` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs2`] >>
      qexists_tac`bc0 ++ REVERSE cx ++ REVERSE cxs ++ TAKE 0 bc10` >>
      simp[SUM_APPEND,FILTER_APPEND] >>
      fs[FOLDL_emit_append_out,Once SWAP_REVERSE] >>
      NO_TAC) >>
    simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def] >>
    `LENGTH exps = LENGTH bvs` by (
      imp_res_tac Cevaluate_list_LENGTH >>
      fs[EVERY2_EVERY] ) >>
    simp[Abbr`bs2`] >>
    qho_match_abbrev_tac`∃bs'. bc_next^* bs2 bs' ∧ P bs'` >>
    qpat_assum`bc_fetch X = Y`kall_tac >>
    `bc_fetch bs2 = SOME (EL 1 bc10)` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs2`] >>
      qexists_tac`bc0 ++ REVERSE cx ++ REVERSE cxs ++ TAKE 1 bc10` >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs2`,EL_APPEND1,EL_APPEND2,EL_CONS,PRE_SUB1,bc_eval_stack_def] >>
    qho_match_abbrev_tac`∃bs'. bc_next^* bs2 bs' ∧ P bs'` >>
    qpat_assum`bc_fetch X = Y`kall_tac >>
    `bc_fetch bs2 = SOME (EL 2 bc10)` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs2`] >>
      qexists_tac`bc0 ++ REVERSE cx ++ REVERSE cxs ++ TAKE 2 bc10` >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs2`,EL_CONS,PRE_SUB1,EL_APPEND1,EL_APPEND2,bc_eval_stack_def] >>
    qho_match_abbrev_tac`∃bs'. bc_next^* bs2 bs' ∧ P bs'` >>
    qpat_assum`bc_fetch X = Y`kall_tac >>
    `bc_fetch bs2 = SOME (EL 3 bc10)` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs2`] >>
      qexists_tac`bc0 ++ REVERSE cx ++ REVERSE cxs ++ TAKE 3 bc10` >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs2`,bc_eval_stack_def,EL_CONS,PRE_SUB1,EL_APPEND2,EL_APPEND1] >>
    qho_match_abbrev_tac`∃bs'. bc_next^* bs2 bs' ∧ P bs'` >>
    qpat_assum`bc_fetch X = Y`kall_tac >>
    `bc_fetch bs2 = SOME (EL 4 bc10)` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs2`] >>
      qexists_tac`bc0 ++ REVERSE cx ++ REVERSE cxs ++ TAKE 4 bc10` >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    TRY (
      simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj1_tac >>
      simp[Abbr`P`,Abbr`bs2`] >> NO_TAC) >>
    simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs2`,EL_CONS,bc_eval_stack_def] >>
    qho_match_abbrev_tac`∃bs'. bc_next^* bs2 bs' ∧ P bs'` >>
    qpat_assum`bc_fetch X = Y`kall_tac >>
    qspecl_then[`LENGTH exps + 4`,`LENGTH args + LENGTH blvs + 3`,`bs2`]mp_tac stackshift_thm >>
    simp[Abbr`bs2`] >>
    disch_then(mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
    disch_then(qspec_then`[Tick;Return]++bc1`mp_tac) >> simp[] >>
    Q.PAT_ABBREV_TAC`xst = Block 0 bve::lll` >>
    disch_then(qspecl_then[`TAKE (LENGTH bvs + 4) xst`,`TAKE (LENGTH args + LENGTH blvs + 3) (DROP (LENGTH bvs + 4) xst)`]mp_tac) >>
    simp[Abbr`xst`,TAKE_APPEND1,TAKE_APPEND2,DROP_APPEND2,DROP_APPEND1] >>
    discharge_hyps >- simp[SUM_APPEND,FILTER_APPEND] >>
    qho_match_abbrev_tac`bc_next^* bs1 bs2 ⇒ ∃bs'. bc_next^* bs2' bs' ∧ P bs'` >>
    `bs1 = bs2'` by (
      simp[Abbr`bs1`,Abbr`bs2'`,bc_state_component_equality] >>
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    pop_assum SUBST1_TAC >>
    qunabbrev_tac`bs1` >>
    qsuff_tac`∃bs'. bc_next^* bs2 bs' ∧ P bs'` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    qunabbrev_tac`bs2'` >>
    `bc_fetch bs2 = SOME Tick` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs2`] >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`[Return]++bc1` >>
      simp[SUM_APPEND,FILTER_APPEND]) >>
    simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj1_tac >>
    simp[Abbr`P`,Abbr`bs2`]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    simp[compile_def,FOLDL_UNION_BIGUNION] >>
    simp_tac(srw_ss()++ETA_ss)[] >>
    strip_tac >> rfs[] >> fs[] >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
    Q.PAT_ABBREV_TAC`cs0 = compile cenv X sz cs exp` >>
    qspecl_then[`cenv`,`sz+1`,`cs0`,`exps`](Q.X_CHOOSE_THEN`cxs`strip_assume_tac)(CONJUNCT2 (CONJUNCT2 compile_append_out)) >> fs[] >>
    reverse(Cases_on`∃bc10. code = REVERSE cx ++ REVERSE cxs ++ bc10`) >- (
      fsrw_tac[DNF_ss][] >>
      rpt gen_tac >>
      rw[Once SWAP_REVERSE,FOLDL_emit_append_out] >>
      Cases_on`t`>>fs[Once SWAP_REVERSE]) >> fs[] >>
    reverse(Cases_on`bs.code = bc0 ++ REVERSE cx ++ REVERSE cxs ++ bc10 ++ bc1`) >- fs[] >>
    fs[Once SWAP_REVERSE] >>
    fs[Once SWAP_REVERSE] >>
    last_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cx`]mp_tac) >>
    `LENGTH (SND (FST s)) ≤ LENGTH (SND (FST s')) ∧ LENGTH (SND (FST s')) ≤ LENGTH (SND (FST s''))` by PROVE_TAC[Cevaluate_store_SUBSET,FST] >>
    simp[] >>
    disch_then(mp_tac o SIMP_RULE(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] o CONJUNCT1) >>
    disch_then(qx_choosel_then[`rf`,`rd'`,`ck'`,`gv'`,`bf`]strip_assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    last_x_assum(qspecl_then[`rd'`,`cs0`,`cenv`,`sz+1`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE cx`,`REVERSE cxs`]mp_tac) >>
    simp[Abbr`bs1`] >>
    discharge_hyps >- (
      simp[Abbr`cs0`] >>
      fsrw_tac[DNF_ss][] >>
      qspecl_then[`s`,`env`,`exp`,`s',Rval(v)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
      simp[] >> strip_tac >>
      qspecl_then[`s`,`env`,`exp`,`s',Rval(v)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
      simp[] >> strip_tac >>
      conj_tac >- (  fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >> metis_tac[] ) >>
      conj_tac >- (  fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >> metis_tac[] ) >>
      conj_tac >- (
        imp_res_tac RTC_bc_next_clock_less >>
        rfs[Cenv_bs_def,s_refs_def,optionTheory.OPTREL_def]) >>
      match_mp_tac compile_labels_lemma >>
      map_every qexists_tac [`cenv`,`TCNonTail`,`sz`,`cs`,`exp`,`bc0`,`REVERSE cx`] >>
      rw[] ) >>
    strip_tac >>
    rpt gen_tac >> strip_tac >>
    `ck' = SOME (FST (FST s'))` by (
      imp_res_tac RTC_bc_next_clock_less >>
      rfs[Cenv_bs_def,s_refs_def,optionTheory.OPTREL_def]) >>
    reverse(Cases_on`err`)>>simp[]>-(
      metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
    fs[] >>
    rpt gen_tac >> strip_tac >>
    first_x_assum(qspecl_then[`bf::ig`,`sp`,`hdl`,`st`]mp_tac) >>
    simp[] >>
    simp[code_for_return_def] >>
    disch_then(qx_choosel_then[`bv`,`rf'`,`rd''`,`ck''`,`gv''`]strip_assume_tac) >>
    map_every qexists_tac[`bv`,`rf'`,`rd''`,`ck''`,`gv''`] >>
    simp[] >>
    reverse conj_tac >- metis_tac[IS_PREFIX_TRANS,SUBMAP_TRANS,gvrel_trans] >>
    metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    simp[compile_def,FOLDL_UNION_BIGUNION] >>
    simp_tac(srw_ss()++ETA_ss)[] >>
    strip_tac >> rfs[] >> fs[] >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
    Q.PAT_ABBREV_TAC`cs0 = compile cenv X sz cs exp` >>
    qspecl_then[`cenv`,`sz+1`,`cs0`,`es`](Q.X_CHOOSE_THEN`cxs`strip_assume_tac)(CONJUNCT2 (CONJUNCT2 compile_append_out)) >> fs[] >>
    reverse(Cases_on`∃bc10. code = REVERSE cx ++ REVERSE cxs ++ bc10`) >- (
      fsrw_tac[DNF_ss][FOLDL_emit_append_out] >>
      conj_tac >> rpt gen_tac >>
      Cases_on`t`>>rw[]>>fs[Once SWAP_REVERSE]) >> fs[] >>
    reverse(Cases_on`bs.code = bc0 ++ REVERSE cx ++ REVERSE cxs ++ bc10 ++ bc1`) >- fs[] >>
    fs[Once SWAP_REVERSE] >>
    fs[Once SWAP_REVERSE] >>
    last_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cx`]mp_tac) >>
    `LENGTH (SND (FST s)) ≤ LENGTH (SND (FST s'))` by PROVE_TAC[Cevaluate_store_SUBSET,FST] >>
    simp[] >>
    strip_tac >>
    rpt gen_tac >> strip_tac >>
    first_x_assum(qspec_then`TCNonTail`mp_tac) >>
    simp[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[compile_def,pushret_def,FOLDL_emit_append_out] >>
    rpt gen_tac >> strip_tac >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`]strip_assume_tac (CONJUNCT1 compile_append_out) >>
    simp[Once SWAP_REVERSE] >>
    simp[Once SWAP_REVERSE] >>
    reverse(Cases_on`∃bc10. code = REVERSE bc ++ prim1_to_bc uop ++ bc10`) >- (
      rw[] >> fs[FOLDL_emit_append_out] >> rfs[] >>
      TRY(Cases_on`t`)>>fs[pushret_def,Once SWAP_REVERSE]) >>
    fs[] >>
    reverse(Cases_on`bs.code = bc0 ++ REVERSE bc ++ prim1_to_bc uop ++ bc10 ++ bc1`) >- (
      fs[]) >>
    first_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE bc`]mp_tac) >>
    simp[Once SWAP_REVERSE] >>
    disch_then(assume_tac o CONJUNCT1) >>
    Cases_on`res`>>fs[] >- (
      qmatch_abbrev_tac`(bc10 = [] ⇒ P) ∧ Q` >>
      `P` by (
        simp[Abbr`P`,Abbr`Q`] >>
        pop_assum mp_tac >>
        simp[code_for_push_def] >>
        fsrw_tac[DNF_ss][] >>
        map_every qx_gen_tac[`rf`,`rd'`,`ck`,`gv`,`bv`] >>
        strip_tac >>
        qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
        qspecl_then[`rd'`,`uop`,`count'`,`(s',g)`,`v`,`(s'',g')`,`a`,`bs1`,`bc0 ++ REVERSE bc`,`bc10++bc1`,`bce`,`bcr`,`bs.stack`,`bv`]
          mp_tac (INST_TYPE[alpha|->``:Cv``]prim1_to_bc_thm) >>
        simp[Abbr`bs1`] >>
        discharge_hyps >- fs[Cenv_bs_def] >>
        disch_then(qx_choosel_then[`bvr`,`rfr`,`gvr`,`smr`]strip_assume_tac) >>
        map_every qexists_tac[`rfr`,`rd' with sm := smr`,`ck`,`gvr`,`bvr`] >>
        simp[] >>
        qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
        qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
        conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
        reverse conj_tac >- metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS,gvrel_trans] >>
        match_mp_tac Cenv_bs_imp_incsz_irr >>
        qexists_tac`bs with <| code := bce; refs := rfr; clock := ck; globals := gvr|>`>>
        simp[bc_state_component_equality] >>
        match_mp_tac Cenv_bs_change_store >>
        map_every qexists_tac[`rd`,`s`,`bs with <| code := bce|>`]>>
        simp[bc_state_component_equality] >>
        fs[Cenv_bs_def,s_refs_def,good_rd_def,UNCURRY,FEVERY_DEF,SUBSET_DEF] >>
        metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS,gvrel_trans] ) >>
      srw_tac[DNF_ss][Abbr`P`,Abbr`Q`] >>
      match_mp_tac code_for_push_return >>
      first_assum (match_exists_tac o concl) >> simp[] >>
      qexists_tac `REVERSE args` >>
      fs[EVERY2_EVERY] ) >>
    Cases_on`uop`>>fs[]>>
    Cases_on`e`>>simp[]>>
    Cases_on`v`>>fs[] >> rw[]>>
    BasicProvers.EVERY_CASE_TAC >> fs[]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def,LET_THM,pushret_def,FOLDL_emit_append_out] >>
    fsrw_tac[ETA_ss][] >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    gen_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
    qspecl_then[`t`,`cs1`](Q.X_CHOOSE_THEN`cp`strip_assume_tac)pushret_append_out >> pop_assum kall_tac >>
    simp[Once SWAP_REVERSE,Abbr`cs1`] >> rw[] >>
    first_x_assum (qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cx`]mp_tac) >>
    simp[] >>
    disch_then(qspec_then`TCNonTail`mp_tac)>>simp[]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[Once CONJ_ASSOC] >>
    reverse conj_tac >- (
      PairCases_on`s'` >>
      rator_x_assum`CevalPrim2`mp_tac >>
      `∃op. p2 = P2p op ∨ ∃op. p2 = P2s op` by (
        Cases_on`p2`>>simp[] ) >>
      qmatch_assum_rename_tac`p2 = X op`["X"] >>
      Cases_on`op`>>simp[]>>
      Cases_on`v2`>>TRY(Cases_on`l`)>>simp[]>>rw[]>>
      Cases_on`v1`>>TRY(Cases_on`l`)>>fs[semanticPrimitivesTheory.lit_same_type_def]>>rw[]>>
      fs[UNCURRY] >>
      qpat_assum`X = Rerr Y`mp_tac >>
      BasicProvers.CASE_TAC >>
      BasicProvers.CASE_TAC >>
      BasicProvers.CASE_TAC >>
      BasicProvers.CASE_TAC) >>
    qpat_assum`bce++bcr=X`mp_tac>>
    qpat_assum`bs.code=X`mp_tac>>
    simp[IMP_CONJ_THM]>>
    map_every qid_spec_tac[`bc1`,`code`]>>
    simp[FORALL_AND_THM]>>
    conj_asm1_tac >- (
      rw[compile_def,LET_THM,pushret_def] >>
      qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`e1`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      qmatch_assum_abbrev_tac`cs0.out = cx ++ cs.out` >>
      qspecl_then[`cenv`,`TCNonTail`,`sz+1`,`cs0`,`e2`](Q.X_CHOOSE_THEN`cy`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      fs[Once SWAP_REVERSE] >>
      first_x_assum (qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
      simp[Abbr`cs0`,compile_def,Once SWAP_REVERSE] >>
      simp[code_for_push_def] >>
      disch_then (qx_choosel_then [`bvs`,`rfs`,`sms`,`cks`,`gvs`] strip_assume_tac) >>
      fs[EVERY2_EVERY] >>
      `∃bv0 bv1. bvs = [bv0;bv1]` by (
        Cases_on `bvs` >> fs[] >>
        Cases_on `t` >> fs[LENGTH_NIL] ) >> fs[] >> rw[] >>
      fsrw_tac[DNF_ss][] >>
      qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
      qmatch_assum_abbrev_tac `Cv_bv pp v1 bv0` >>
      qspecl_then[`s'`,`p2`,`v1`,`v2`,`s''`,`v`,`bs0`,`bce`,`bc0 ++ REVERSE cx ++ REVERSE cy`,`bc1`,`bs.stack`,`bv0`,`bv1`,`pp`]mp_tac
        (INST_TYPE[alpha|->``:Cv``]prim2_to_bc_thm) >>
      fs[Abbr`bs0`] >>
      `FST pp = sms` by rw[Abbr`pp`] >> fs[] >>
      imp_res_tac (CONJUNCT2 Cevaluate_store_SUBSET) >>
      fs[] >>
      `(LENGTH sms.sm = LENGTH (SND (FST s'))) ∧ ALL_DISTINCT sms.sm` by
        fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
      simp[] >>
      discharge_hyps >- (
        fs[Cenv_bs_def] >>
        match_mp_tac s_refs_append_code >>
        Q.PAT_ABBREV_TAC`bs1:bc_state = (X Y)` >>
        qexists_tac`bs1 with code := bce`>>
        simp[bc_state_component_equality,Abbr`bs1`] >>
        metis_tac[]) >>
      disch_then (qx_choosel_then[`rd1`,`rf1`,`bv`]strip_assume_tac) >>
      map_every qexists_tac [`rf1`,`rd1`,`cks`,`gvs`,`bv`] >> fs[] >>
      conj_tac >- (
        rw[Once RTC_CASES2] >> disj2_tac >>
        qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
        qexists_tac `bs0` >> rw[] >>
        qmatch_assum_abbrev_tac`bc_next bs0 bs11` >>
        qmatch_abbrev_tac `bc_next bs0 bs12` >>
        qsuff_tac `bs11 = bs12` >- metis_tac[bc_eval1_thm,optionTheory.SOME_11] >>
        rw[Abbr`bs11`,Abbr`bs12`] >>
        Q.PAT_ABBREV_TAC`x = prim2_to_bc Y` >>
        qmatch_abbrev_tac `bump_pc bs2 = bs1` >>
        `bc_fetch bs2 = SOME x` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs2`] >>
          qexists_tac `bc0 ++ REVERSE cx ++ REVERSE cy` >>
          unabbrev_all_tac >> rw[] ) >>
        rw[bump_pc_def] >>
        unabbrev_all_tac >>
        srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] >>
        rw[bc_state_component_equality]) >>
      conj_tac >- (
        match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
        HINT_EXISTS_TAC >> simp[Abbr`pp`] ) >>
      reverse conj_tac >- (
        metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS] ) >>
      qmatch_assum_abbrev_tac `Cenv_bs sms s' renv cenv (sz + 2) bs0` >>
      `Cenv_bs sms s' renv cenv sz (bs0 with stack := bs.stack)` by (
        match_mp_tac Cenv_bs_pops >>
        CONV_TAC SWAP_EXISTS_CONV >>
        qexists_tac`bs0` >>
        simp[bc_state_component_equality,Abbr`bs0`] >>
        metis_tac[Cenv_bs_CTLet_bound] ) >>
      `Cenv_bs rd1 s'' renv cenv sz (bs0 with <| stack := bs.stack; refs := rf1 |>)` by (
        match_mp_tac Cenv_bs_change_store >>
        first_assum(match_exists_tac o concl) >> simp[] >>
        simp[bc_state_component_equality] >>
        simp[Abbr`bs0`] >>
        match_mp_tac s_refs_with_irr >>
        HINT_EXISTS_TAC >>
        simp[bump_pc_def] >>
        BasicProvers.CASE_TAC >> simp[]) >>
      match_mp_tac Cenv_bs_imp_incsz_irr >>
      HINT_EXISTS_TAC >>
      simp[Abbr`bs0`] ) >>
    fs[Once compile_def,LET_THM,pushret_def] >>
    rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
    qspecl_then[`cenv`,`sz`,`cs`,`[e1;e2]`]strip_assume_tac(CONJUNCT2(CONJUNCT2 compile_append_out)) >>
    fs[Once SWAP_REVERSE] >> rw[] >> fs[] >>
    match_mp_tac code_for_push_return >>
    first_assum(match_exists_tac o concl) >>
    simp[] >>
    qexists_tac`REVERSE args`>>fs[EVERY2_EVERY]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def,LET_THM,pushret_def] >>
    fsrw_tac[ETA_ss][] >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`e1`](Q.X_CHOOSE_THEN`cx1`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    Q.PAT_ABBREV_TAC`cs0:compiler_result = X e1` >>
    qspecl_then[`cenv`,`TCNonTail`,`sz+1`,`cs0`,`e2`](Q.X_CHOOSE_THEN`cx2`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    gen_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
    qspecl_then[`t`,`cs1`](Q.X_CHOOSE_THEN`cp`strip_assume_tac)pushret_append_out >> pop_assum kall_tac >>
    simp[Once SWAP_REVERSE,Abbr`cs1`,Abbr`cs0`] >> rw[] >>
    first_x_assum (qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cx1 ++ REVERSE cx2`]mp_tac) >>
    simp[compile_def] >>
    metis_tac[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[Once CONJ_ASSOC] >>
    reverse conj_tac >- (
      qpat_assum`A = CevalUpd B X Y Z D`mp_tac>>
      Cases_on`b`>>Cases_on`v2`>>simp[CevalUpd_def]>>rw[]>>
      Cases_on`l`>>fs[]>>
      Cases_on`v1`>>fs[]>>
      qpat_assum`(X,Y) = Z`mp_tac>>
      Cases_on`v3`>>simp[]>>
      rpt BasicProvers.CASE_TAC >>
      Cases_on`l`>>simp[] >>
      rpt BasicProvers.CASE_TAC) >>
    qpat_assum`bce++bcr=X`mp_tac>>
    qpat_assum`bs.code=X`mp_tac>>
    simp[IMP_CONJ_THM]>>
    map_every qid_spec_tac[`bc1`,`code`]>>
    simp[FORALL_AND_THM]>>
    conj_asm1_tac >- (
      simp[compile_def,pushret_def] >>
      Q.PAT_ABBREV_TAC`U = if b then UpdateByte else Y` >> rw[] >>
      qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`e1`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      qmatch_assum_abbrev_tac`cs0.out = cx ++ cs.out` >>
      qspecl_then[`cenv`,`TCNonTail`,`sz+1`,`cs0`,`e2`](Q.X_CHOOSE_THEN`cy`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      qmatch_assum_abbrev_tac`cs1.out = cy ++ cs0.out` >>
      qspecl_then[`cenv`,`TCNonTail`,`sz+2`,`cs1`,`e3`](Q.X_CHOOSE_THEN`cz`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      fs[Once SWAP_REVERSE] >>
      first_x_assum (qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
      simp[Abbr`cs0`,compile_def,Once SWAP_REVERSE] >>
      simp[code_for_push_def] >>
      disch_then (qx_choosel_then [`bvs`,`rfs`,`sms`,`cks`,`gvs`] strip_assume_tac) >>
      fs[EVERY2_EVERY] >>
      `∃bv0 bv1 bv2. bvs = [bv0;bv1;bv2]` by (simp[]) >> fs[] >> rw[] >>
      fsrw_tac[DNF_ss][] >>
      qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
      `∃i n. v2 = CLitv (IntLit i) ∧ v1 = CLoc n ∧ v = CLitv Unit` by (
        Cases_on`b`>>Cases_on`v2`>>fs[]>>Cases_on`l`>>fs[]>>
        Cases_on`v1`>>fs[] >>
        qpat_assum`(X,Y) = Z`mp_tac >>
        TRY BasicProvers.CASE_TAC >>
        TRY BasicProvers.CASE_TAC >>
        TRY BasicProvers.CASE_TAC >>
        Cases_on`v3`>>simp[]>>
        Cases_on`l`>>simp[]>>
        rpt BasicProvers.CASE_TAC) >>
      fs[Q.SPEC`CLitv l`(CONJUNCT1(SPEC_ALL Cv_bv_cases))]>>
      fs[Q.SPEC`CLoc n`(CONJUNCT1(SPEC_ALL Cv_bv_cases))]>>
      rpt BasicProvers.VAR_EQ_TAC >>
      CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
      map_every qexists_tac[`gvs`,`cks`,`sms`] >>
      simp[] >>
      srw_tac[DNF_ss][Once RTC_CASES_RTC_TWICE] >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`bs0` >> simp[] >>
      rw[RTC_eq_NRC,PULL_EXISTS] >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`SUC(SUC 0)` >>
      srw_tac[DNF_ss][NRC] >>
      `bc_fetch bs0 = SOME U` by (
        match_mp_tac bc_fetch_next_addr >>
        qexists_tac`bc0 ++ REVERSE cx ++ REVERSE cy ++ REVERSE cz` >>
        simp[Abbr`bs0`] >>
        rw[Abbr`U`]) >>
      simp[bc_eval1_thm] >>
      rw[Once bc_eval1_def,Abbr`U`] >- (
        simp[Abbr`bs0`] >>
        qpat_assum`(X,Y) = Z`mp_tac >>
        Cases_on`v3`>>simp[]>>
        Cases_on`l`>>simp[]>>
        BasicProvers.CASE_TAC>>
        BasicProvers.CASE_TAC>>
        BasicProvers.CASE_TAC>>
        strip_tac >>
        fs[Q.SPEC`CLitv l`(CONJUNCT1(SPEC_ALL Cv_bv_cases))]>>
        rpt BasicProvers.VAR_EQ_TAC >>
        fs[el_check_def] >>
        qmatch_assum_rename_tac`EL n s1 = W8array ws`[] >>
        `FLOOKUP rfs p = SOME (ByteArray ws)` by (
          fs[Cenv_bs_def,s_refs_def] >>
          rator_x_assum`LIST_REL`kall_tac >>
          rator_x_assum`LIST_REL`mp_tac >>
          simp[LIST_REL_EL_EQN] >>
          disch_then(qspec_then`n`mp_tac) >>
          simp[sv_refv_rel_cases,EL_MAP,FLOOKUP_DEF] >>
          fs[EVERY_MEM] >> metis_tac[MEM_EL] ) >>
        simp[] >>
        rfs[integerTheory.INT_ABS,integerTheory.int_le,wordsTheory.w2n_lt] >>
        simp[bump_pc_def] >>
        Q.PAT_ABBREV_TAC`bs1:bc_state = X Y` >>
        `bc_fetch bs1 = SOME(Stack(Cons unit_tag 0))` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs1`] >>
          CONV_TAC SWAP_EXISTS_CONV >>
          qexists_tac`bc1`>>simp[] >>
          simp[FILTER_APPEND,SUM_APPEND] ) >>
        simp[bc_eval1_def,bc_eval_stack_def] >>
        simp[bump_pc_def] >>
        simp[Abbr`bs1`,bc_state_component_equality] >>
        conj_tac >- simp[FILTER_APPEND,SUM_APPEND] >>
        reverse conj_tac >- ( rw[] >> metis_tac[MEM_EL] ) >>
        Q.PAT_ABBREV_TAC`bs0:bc_state = X Y` >>
        match_mp_tac Cenv_bs_imp_incsz_irr >>
        qexists_tac`bs0 with stack := bs.stack` >>
        simp[Abbr`bs0`] >>
        qmatch_assum_abbrev_tac`Cenv_bs sms s0 env cenv (sz+3) bs0` >>
        `Cenv_bs sms s0 env cenv sz (bs0 with stack := bs.stack)` by (
          match_mp_tac Cenv_bs_pops >>
          CONV_TAC SWAP_EXISTS_CONV >>
          qexists_tac`bs0` >>
          simp[Abbr`bs0`,bc_state_component_equality] >>
          metis_tac[Cenv_bs_CTLet_bound] ) >>
        Q.PAT_ABBREV_TAC`bs1:bc_state = X Y` >>
        `Cenv_bs sms s0 env cenv sz (bs1 with refs := bs0.refs)` by (
          match_mp_tac Cenv_bs_with_irr >>
          HINT_EXISTS_TAC >>
          simp[Abbr`bs0`,Abbr`bs1`] ) >>
        match_mp_tac Cenv_bs_change_store >>
        first_assum (match_exists_tac o concl) >>
        simp[bc_state_component_equality] >>
        simp[Abbr`bs0`,Abbr`bs1`] >>
        conj_tac >- (
          fs[Cenv_bs_def,s_refs_def,Abbr`s0`] >>
          fs[good_rd_def,FLOOKUP_UPDATE] >>
          conj_tac >- (
            fs[FEVERY_DEF,UNCURRY] >>
            rw[] >> metis_tac[MEM_EL] ) >>
          conj_tac >- fs[EVERY_MEM] >>
          rator_x_assum`LIST_REL`kall_tac >>
          rator_x_assum`LIST_REL`mp_tac >>
          simp[LIST_REL_EL_EQN,EL_LUPDATE,EL_MAP,FAPPLY_FUPDATE_THM] >>
          rw[] >> rw[] >>
          metis_tac[EL_ALL_DISTINCT_EL_EQ] ) >>
        rw[FDOM_DRESTRICT] >>
        metis_tac[MEM_EL] ) >>
      simp[Abbr`bs0`] >>
      qpat_assum`(X,Y) = Z`mp_tac >>
      simp[] >>
      BasicProvers.CASE_TAC>>
      BasicProvers.CASE_TAC>>
      BasicProvers.CASE_TAC>>
      strip_tac >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[el_check_def] >>
      `∃v. FLOOKUP rfs p = SOME (ValueArray [v])` by (
        fs[Cenv_bs_def,s_refs_def] >>
        rator_x_assum`LIST_REL`kall_tac >>
        rator_x_assum`LIST_REL`mp_tac >>
        simp[LIST_REL_EL_EQN] >>
        disch_then(qspec_then`n`mp_tac) >>
        simp[sv_refv_rel_cases,EL_MAP,FLOOKUP_DEF] >>
        fs[EVERY_MEM] >> rw[] >> metis_tac[MEM_EL] ) >>
      simp[] >>
      simp[bump_pc_def] >>
      Q.PAT_ABBREV_TAC`bs1:bc_state = X Y` >>
      `bc_fetch bs1 = SOME(Stack(Cons unit_tag 0))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs1`] >>
        CONV_TAC SWAP_EXISTS_CONV >>
        qexists_tac`bc1`>>simp[] >>
        simp[FILTER_APPEND,SUM_APPEND] ) >>
      simp[bc_eval1_def,bc_eval_stack_def] >>
      simp[bump_pc_def] >>
      simp[Abbr`bs1`,bc_state_component_equality] >>
      conj_tac >- simp[FILTER_APPEND,SUM_APPEND] >>
      reverse conj_tac >- ( rw[] >> metis_tac[MEM_EL] ) >>
      Q.PAT_ABBREV_TAC`bs0:bc_state = X Y` >>
      match_mp_tac Cenv_bs_imp_incsz_irr >>
      qexists_tac`bs0 with stack := bs.stack` >>
      simp[Abbr`bs0`] >>
      qmatch_assum_abbrev_tac`Cenv_bs sms s0 env cenv (sz+3) bs0` >>
      `Cenv_bs sms s0 env cenv sz (bs0 with stack := bs.stack)` by (
        match_mp_tac Cenv_bs_pops >>
        CONV_TAC SWAP_EXISTS_CONV >>
        qexists_tac`bs0` >>
        simp[Abbr`bs0`,bc_state_component_equality] >>
        metis_tac[Cenv_bs_CTLet_bound] ) >>
      Q.PAT_ABBREV_TAC`bs1:bc_state = X Y` >>
      `Cenv_bs sms s0 env cenv sz (bs1 with refs := bs0.refs)` by (
        match_mp_tac Cenv_bs_with_irr >>
        HINT_EXISTS_TAC >>
        simp[Abbr`bs0`,Abbr`bs1`] ) >>
      match_mp_tac Cenv_bs_change_store >>
      first_assum (match_exists_tac o concl) >>
      simp[bc_state_component_equality] >>
      simp[Abbr`bs0`,Abbr`bs1`] >>
      conj_tac >- (
        fs[Cenv_bs_def,s_refs_def,Abbr`s0`] >>
        fs[good_rd_def,FLOOKUP_UPDATE] >>
        conj_tac >- (
          fs[FEVERY_DEF,UNCURRY] >>
          rw[] >> metis_tac[MEM_EL] ) >>
        conj_tac >- fs[EVERY_MEM] >>
        rator_x_assum`LIST_REL`kall_tac >>
        rator_x_assum`LIST_REL`mp_tac >>
        simp[LIST_REL_EL_EQN,EL_LUPDATE,EL_MAP,FAPPLY_FUPDATE_THM] >>
        rw[] >> rw[] >> rw[sv_refv_rel_cases,LUPDATE_def] >>
        metis_tac[EL_ALL_DISTINCT_EL_EQ] ) >>
      rw[FDOM_DRESTRICT] >>
      metis_tac[MEM_EL] ) >>
    fs[Once compile_def,LET_THM,pushret_def] >>
    qspecl_then[`cenv`,`sz`,`cs`,`[e1;e2;e3]`]strip_assume_tac(CONJUNCT2(CONJUNCT2 compile_append_out)) >>
    simp[Once SWAP_REVERSE] >> rw[] >>
    rfs[Once SWAP_REVERSE] >>
    match_mp_tac code_for_push_return >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    qexists_tac`REVERSE args`>>fs[EVERY2_EVERY]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def,LET_THM,pushret_def] >>
    fsrw_tac[ETA_ss][] >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`e1`](Q.X_CHOOSE_THEN`cx1`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    Q.PAT_ABBREV_TAC`cs0:compiler_result = X e1` >>
    qspecl_then[`cenv`,`TCNonTail`,`sz+1`,`cs0`,`e2`](Q.X_CHOOSE_THEN`cx2`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    Q.PAT_ABBREV_TAC`cs1:compiler_result = X e2` >>
    qspecl_then[`cenv`,`TCNonTail`,`sz+2`,`cs1`,`e3`](Q.X_CHOOSE_THEN`cx3`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    gen_tac >>
    Q.PAT_ABBREV_TAC`cs2 = compiler_result_out_fupd X Y` >>
    qspecl_then[`t`,`cs2`](Q.X_CHOOSE_THEN`cp`strip_assume_tac)pushret_append_out >> pop_assum kall_tac >>
    simp[Once SWAP_REVERSE,Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >> rw[] >>
    first_x_assum (qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cx1 ++ REVERSE cx2 ++ REVERSE cx3`]mp_tac) >>
    simp[compile_def] >>
    metis_tac[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    fs[compile_def,LET_THM] >>
    Q.PAT_ABBREV_TAC`cs0 = compile cenv t sz cs exp` >>
    qabbrev_tac`nl = cs0.next_label` >>
    full_simp_tac std_ss [prove(``w::x::y::cs0.out=[w;x;y]++cs0.out``,rw[])] >>
    full_simp_tac std_ss [prove(``x::y::(cs0).out=[x;y]++(cs0).out``,rw[])] >>
    Q.PAT_ABBREV_TAC`lc3 = [Label x;y]` >>
    Q.PAT_ABBREV_TAC`lc2 = [Label x;y;z]` >>
    qunabbrev_tac`cs0` >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`be1`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    qmatch_assum_abbrev_tac`cs0.out = be1 ++ cs.out` >>
    reverse(Cases_on`∃bc10. code = REVERSE be1 ++ REVERSE lc2 ++ bc10`) >- (
      conj_tac >> TRY conj_tac >> rpt gen_tac >> strip_tac >>
      qpat_assum`X = REVERSE code ++ cs.out`mp_tac >>
      Q.PAT_ABBREV_TAC`cs2 = compiler_result_out_fupd (K (lc2 ++ cs0.out)) Z` >>
      Q.PAT_ABBREV_TAC`tt:call_context = X` >>
      qspecl_then[`cenv`,`tt`,`sz`,`cs2`,`e2`](Q.X_CHOOSE_THEN`be2`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      Q.PAT_ABBREV_TAC`cs25:compiler_result = X e2` >>
      Q.PAT_ABBREV_TAC`cs3 = compiler_result_out_fupd X Y` >>
      qspecl_then[`cenv`,`tt`,`sz`,`cs3`,`e3`](Q.X_CHOOSE_THEN`be3`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      simp[Abbr`cs3`] >> rfs[] >>
      simp[Abbr`cs25`,Abbr`cs2`,Abbr`cs0`,Once SWAP_REVERSE] >>
      rw[] >> fs[] ) >>
    `LENGTH (SND (FST s)) ≤ LENGTH (SND (FST s')) ∧ LENGTH (SND (FST s')) ≤ LENGTH (SND (FST s''))` by (
      metis_tac[SIMP_RULE(srw_ss())[FORALL_PROD]Cevaluate_store_SUBSET,SND,FST,PAIR_EQ,pair_CASES] ) >>
    last_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE be1`]mp_tac) >>
    fs[] >>
    disch_then(CHOOSE_THEN strip_assume_tac o SIMP_RULE (srw_ss()) [code_for_push_def,LET_THM,Once Cv_bv_cases] o CONJUNCT1) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    let
      val tac1 =
        rw[] >>
        qpat_assum`Y::X.out = Z`mp_tac >>
        Q.PAT_ABBREV_TAC`cs2 = compiler_result_out_fupd (K (lc2 ++X  ++ Y)) Z` >>
        Q.PAT_ABBREV_TAC`tt:call_context = X` >>
        qspecl_then[`cenv`,`tt`,`sz`,`cs2`,`e2`](Q.X_CHOOSE_THEN`be2`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
        Q.PAT_ABBREV_TAC`cs25:compiler_result = X e2` >>
        Q.PAT_ABBREV_TAC`cs3 = compiler_result_out_fupd X Y` >>
        qspecl_then[`cenv`,`tt`,`sz`,`cs3`,`e3`](Q.X_CHOOSE_THEN`be3`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
        simp[Abbr`cs3`,Abbr`cs25`,Abbr`cs2`,Abbr`cs0`,Once SWAP_REVERSE] >> strip_tac >>
        fsrw_tac[ARITH_ss][] >>
        qpat_assum`X = Y ++ cs.out`mp_tac >>
        Q.PAT_ABBREV_TAC`cs2:compiler_result = compiler_result_out_fupd X Y` >> strip_tac
      val tac2 =
        first_x_assum(qspecl_then[`rd'`,`cs2`,`cenv`,`sz`,`bs1 with <|stack := bs.stack; pc := next_addr bs.inst_length (bc0 ++ REVERSE be1 ++ REVERSE lc2)|>`
                                 ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2`,`REVERSE be2`]mp_tac) >>
        simp[Abbr`bs1`,Once SWAP_REVERSE] >>
        discharge_hyps >- (
          qspecl_then[`s`,`env`,`exp`,`(s',Rval (CLitv (Bool T)))`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
          simp[] >> strip_tac >>
          qspecl_then[`s`,`env`,`exp`,`(s',Rval (CLitv (Bool T)))`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
          simp[] >> strip_tac >>
          conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >> metis_tac[] ) >>
          conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >> metis_tac[] ) >>
          conj_tac >- (
            imp_res_tac RTC_bc_next_clock_less >>
            rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
          conj_tac >- (
            fs[Abbr`cs2`] >>
            match_mp_tac Cenv_bs_imp_decsz >>
            qmatch_assum_abbrev_tac `Cenv_bs rd' s' renv cenv (sz + 1) bs1` >>
            Q.PAT_ABBREV_TAC`pc = next_addr X Y` >>
            qexists_tac`bs1 with pc := pc` >>
            simp[bc_state_component_equality,Abbr`bs1`] >>
            conj_tac >- (
              match_mp_tac Cenv_bs_with_irr >>
              HINT_EXISTS_TAC >> simp[] ) >>
            imp_res_tac Cenv_bs_CTLet_bound >>
            pop_assum(qspec_then`sz+1`mp_tac) >>
            imp_res_tac CTDec_bound_lemma >>
            pop_assum(qspec_then`LENGTH bs.stack`mp_tac) >>
            fs[Cenv_bs_def] >>
            srw_tac[ARITH_ss][ADD1] ) >>
          fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2`
                          ,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP] >>
          rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
        simp[Abbr`cs2`]
      val tac6 =
        qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
        qmatch_assum_abbrev_tac`bc_next^* bs2 bs3` >>
        qsuff_tac`bc_next bs1 bs2` >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
        rw[bc_eval1_thm] >>
        `bc_fetch bs1 = SOME (JumpIf (Lab nl))` by (
           match_mp_tac bc_fetch_next_addr >>
           simp[Abbr`bs1`,Abbr`lc2`] >>
           qexists_tac`bc0 ++ REVERSE be1` >>
           rw[]) >>
        rw[bc_eval1_def,Abbr`bs1`,LET_THM] >>
        rw[Abbr`bs2`,bc_state_component_equality] >>
        rw[bc_find_loc_def] >>
        qmatch_abbrev_tac`bc_find_loc_aux ls il nl 0 = SOME (next_addr il ls0)` >>
        `∃ls1. ls = ls0 ++ ls1` by rw[Abbr`ls`,Abbr`ls0`] >>
        pop_assum SUBST1_TAC >> qunabbrev_tac`ls` >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        `ALL_DISTINCT (FILTER is_Label ls0)` by (
          fsrw_tac[DNF_ss][ALL_DISTINCT_APPEND,FILTER_APPEND,Abbr`ls0`,FILTER_REVERSE,Abbr`nl`
                          ,ALL_DISTINCT_REVERSE,EVERY_MEM,Abbr`lc2`,MEM_MAP,MEM_FILTER,is_Label_rwt,between_def] >>
          rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
        qexists_tac`LENGTH bc0 + LENGTH be1 + 2` >>
        fsrw_tac[ARITH_ss][Abbr`ls0`,Abbr`lc2`] >>
        conj_tac >- lrw[EL_DROP,EL_CONS,EL_APPEND2] >>
        lrw[TAKE_APPEND2,FILTER_APPEND]
      val tac3 =
        map_every qx_gen_tac[`bv2`,`rf2`,`sm2`,`ck2`,`gv2`] >>
        strip_tac >>
        map_every qexists_tac[`bv2`,`rf2`,`sm2`,`ck2`,`gv2`] >>
        simp[] >>
        reverse conj_tac >- metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS,gvrel_trans] >>
        tac6
      val tac7 =
        qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
        qmatch_assum_abbrev_tac`bc_next^* bs2 bs3` >>
        qsuff_tac`bc_next^* bs1 bs2` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
        rw[RTC_eq_NRC] >>
        qexists_tac`SUC(SUC 0)` >>
        rw[NRC] >>
        rw[bc_eval1_thm] >>
        `bc_fetch bs1 = SOME (JumpIf (Lab nl))` by (
           match_mp_tac bc_fetch_next_addr >>
           simp[Abbr`bs1`,Abbr`lc2`] >>
           qexists_tac`bc0 ++ REVERSE be1` >>
           rw[]) >>
        rw[Once bc_eval1_def] >>
        rw[Abbr`bs1`,LET_THM] >>
        srw_tac[DNF_ss][] >>
        simp[LEFT_EXISTS_AND_THM] >>
        conj_tac >- (
          qmatch_abbrev_tac`∃n. X = SOME n` >>
          qsuff_tac`~(X = NONE)` >- ( Cases_on`X`>>rw[]) >>
          qunabbrev_tac`X` >>
          simp[bc_find_loc_def] >>
          spose_not_then strip_assume_tac >>
          imp_res_tac bc_find_loc_aux_NONE >>
          fs[] >> rfs[Abbr`lc2`] ) >>
        qmatch_abbrev_tac`bc_eval1 (bump_pc bs1) = SOME bs2` >>
        `bc_fetch bs1 = SOME (JumpIf (Lab nl))` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs1`,Abbr`lc2`] >>
          qexists_tac`bc0 ++ REVERSE be1` >>
          rw[] ) >>
        rw[bump_pc_def,Abbr`bs1`] >>
        qmatch_abbrev_tac`bc_eval1 bs1 = SOME bs2` >>
        `bc_fetch bs1 = SOME (Jump (Lab (nl+1)))` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs1`,Abbr`lc2`] >>
          qexists_tac`bc0 ++ REVERSE be1 ++ [JumpIf (Lab nl)]` >>
          srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND] ) >>
        rw[bc_eval1_def] >>
        rw[Abbr`bs2`,Abbr`bs1`,bc_state_component_equality] >>
        rw[bc_find_loc_def] >>
        qmatch_abbrev_tac`bc_find_loc_aux ls il nl1 0 = SOME (next_addr il ls2)` >>
        `∃ls1. ls = ls2 ++ ls1` by (
          rw[Abbr`ls2`,Abbr`ls`] ) >>
        pop_assum SUBST1_TAC >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        `ALL_DISTINCT (FILTER is_Label ls2)` by (
          fsrw_tac[DNF_ss,ARITH_ss]
            [FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`lc3`,Abbr`ls2`,Abbr`nl1`
            ,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP] >>
          rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
        qunabbrev_tac`ls2` >>
        Q.PAT_ABBREV_TAC`ls2 = X ++ REVERSE be2` >>
        qexists_tac`LENGTH ls2 + 1` >>
        lrw[EL_APPEND2,TAKE_APPEND2,FILTER_APPEND,Abbr`lc3`]
      val tac4 =
        simp[code_for_return_def] >>
        simp_tac(srw_ss()++DNF_ss)[] >>
        map_every qx_gen_tac[`bv2`,`rf2`,`sm2`,`ck2`,`gv2`] >>
        strip_tac >>
        map_every qexists_tac[`bv2`,`rf2`,`sm2`,`ck2`,`gv2`] >>
        simp[] >>
        reverse conj_tac >- metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS,gvrel_trans] >>
        tac7
      val tac5 =
        qmatch_assum_abbrev_tac`(compile cenv tt sz cs3 e3).out = X` >> qunabbrev_tac`X` >>
        first_x_assum(qspecl_then[`rd'`,`cs3`,`cenv`,`sz`,`bs1 with <| stack := bs.stack;
                                  pc := next_addr bs.inst_length (bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2 ++ REVERSE lc3) |>`
                                 ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2 ++ REVERSE lc3`,`REVERSE be3`]mp_tac) >>
        simp[Abbr`bs1`,Once SWAP_REVERSE] >>
        `ck = SOME (FST (FST s'))` by (
          imp_res_tac RTC_bc_next_clock_less >>
          rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
        discharge_hyps >- (
          qmatch_assum_abbrev_tac`Cevaluate s env exp (s',Rval(CLitv(Bool F)))` >>
          qspecl_then[`s`,`env`,`exp`,`(s',Rval (CLitv (Bool F)))`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
          simp[] >> strip_tac >>
          qspecl_then[`s`,`env`,`exp`,`(s',Rval (CLitv (Bool F)))`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
          simp[] >> strip_tac >>
          conj_tac >- ( fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >> metis_tac[] ) >>
          conj_tac >- ( fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >> metis_tac[] ) >>
          conj_tac >- (
            match_mp_tac Cenv_bs_imp_decsz >>
            qmatch_assum_abbrev_tac `Cenv_bs rd' s' renv cenv (sz + 1) bs1` >>
            Q.PAT_ABBREV_TAC`pc = next_addr X Y` >>
            qexists_tac`bs1 with pc := pc` >>
            simp[bc_state_component_equality,Abbr`bs1`] >>
            conj_tac >- (
              match_mp_tac Cenv_bs_with_irr >>
              HINT_EXISTS_TAC >> simp[] ) >>
            imp_res_tac Cenv_bs_CTLet_bound >>
            pop_assum(qspec_then`sz+1`mp_tac) >>
            imp_res_tac CTDec_bound_lemma >>
            pop_assum(qspec_then`LENGTH bs.stack`mp_tac) >>
            fs[Cenv_bs_def] >>
            srw_tac[ARITH_ss][]) >>
          fsrw_tac[DNF_ss,ARITH_ss]
            [FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2`,Abbr`lc3`,Abbr`cs3`
            ,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP] >>
          rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC )
    in
      conj_tac >- (
        tac1 >>
        Cases_on `b1` >> fs[] >- (
          tac2 >>
          disch_then(mp_tac o CONJUNCT1) >>
          simp_tac(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] >>
          map_every qx_gen_tac[`rfs2`,`sm2`,`ck2`,`gv2`,`b2`] >> strip_tac >>
          map_every qexists_tac[`rfs2`,`sm2`,`ck2`,`gv2`,`b2`] >>
          qmatch_assum_abbrev_tac`bc_next^* bs05 bs11` >>
          qmatch_assum_abbrev_tac`bc_next^* bs bs03` >>
          `bc_next^* bs03 bs05` by (
            rw[RTC_eq_NRC] >>
            qexists_tac `SUC 0` >>
            rw[] >>
            `bc_fetch bs03 = SOME (JumpIf (Lab nl))` by (
              match_mp_tac bc_fetch_next_addr >>
              simp[Abbr`bs03`,Abbr`lc2`] >>
              qexists_tac`bc0 ++ REVERSE be1` >>
              rw[]) >>
            rw[bc_eval1_thm] >>
            rw[bc_eval1_def,Abbr`bs03`,LET_THM] >>
            simp[Abbr`bs05`,bc_state_component_equality] >>
            reverse conj_tac >- (
              imp_res_tac RTC_bc_next_clock_less >>
              rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
            rw[bc_find_loc_def] >>
            qmatch_abbrev_tac`bc_find_loc_aux ls il nl 0 = SOME (next_addr il ls0)` >>
            `∃ls1. ls = ls0 ++ ls1` by rw[Abbr`ls`,Abbr`ls0`] >>
            pop_assum SUBST1_TAC >> qunabbrev_tac`ls` >>
            match_mp_tac bc_find_loc_aux_append_code >>
            match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
            `ALL_DISTINCT (FILTER is_Label ls0)` by (
              simp[Abbr`ls0`,FILTER_APPEND,FILTER_REVERSE,Abbr`lc2`,ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE] >>
              fsrw_tac[DNF_ss][MEM_FILTER,EVERY_MEM,is_Label_rwt,MEM_MAP,between_def,Abbr`nl`] >>
              rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
            qexists_tac`LENGTH bc0 + LENGTH be1 + 2` >>
            fsrw_tac[ARITH_ss][Abbr`ls0`,Abbr`lc2`] >>
            conj_tac >- lrw[EL_DROP,EL_CONS,EL_APPEND2] >>
            lrw[TAKE_APPEND2,FILTER_APPEND] ) >>
          conj_tac >- (
            qmatch_abbrev_tac`bc_next^* bs bs13` >>
            `bc_fetch bs11 = SOME (Jump (Lab (nl + 2)))` by (
              match_mp_tac bc_fetch_next_addr >>
              simp[Abbr`bs11`,Abbr`lc3`] >>
              Q.PAT_ABBREV_TAC`ls = X ++ REVERSE be2` >>
              qexists_tac`ls` >> srw_tac[ARITH_ss][]) >>
            `bc_next bs11 bs13` by (
              rw[bc_eval1_thm] >>
              rw[bc_eval1_def,Abbr`bs13`,Abbr`bs11`] >>
              rw[bc_state_component_equality] >>
              rw[bc_find_loc_def] >>
              Q.PAT_ABBREV_TAC`ls = X ++ REVERSE be3` >>
              match_mp_tac bc_find_loc_aux_append_code >>
              match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
              qexists_tac`LENGTH ls` >>
              conj_tac >- (
                fsrw_tac[DNF_ss,ARITH_ss]
                  [Abbr`ls`,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,MEM_FILTER,is_Label_rwt,EVERY_MEM
                  ,Abbr`lc2`,Abbr`lc3`,MEM_MAP,between_def,Abbr`nl`] >>
                rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
              lrw[TAKE_APPEND2,EL_APPEND2,FILTER_APPEND] ) >>
            metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
          simp[] >>
          conj_tac >- (
            match_mp_tac Cenv_bs_with_irr >>
            HINT_EXISTS_TAC >> simp[] ) >>
          metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS,gvrel_trans] ) >>
        qmatch_assum_abbrev_tac`(compile cenv tt sz cs3 e3).out = X` >> qunabbrev_tac`X` >>
        first_x_assum(qspecl_then[`rd'`,`cs3`,`cenv`,`sz`,`bs1 with <| stack := bs.stack;
                                  pc := next_addr bs.inst_length (bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2 ++ REVERSE lc3) |>`
                                 ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2 ++ REVERSE lc3`,`REVERSE be3`]mp_tac) >>
        simp[Abbr`bs1`,Once SWAP_REVERSE,Abbr`cs3`] >>
        discharge_hyps >- (
          qspecl_then[`s`,`env`,`exp`,`(s',Rval (CLitv (Bool F)))`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
          simp[] >> strip_tac >>
          qspecl_then[`s`,`env`,`exp`,`(s',Rval (CLitv (Bool F)))`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
          simp[] >> strip_tac >>
          conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >> metis_tac[] ) >>
          conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >> metis_tac[] ) >>
          conj_tac >- (
            imp_res_tac RTC_bc_next_clock_less >>
            rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
          conj_tac >- (
            match_mp_tac Cenv_bs_imp_decsz >>
            qmatch_assum_abbrev_tac `Cenv_bs rd' s' renv cenv (sz + 1) bs1` >>
            Q.PAT_ABBREV_TAC`pc = next_addr X Y` >>
            qexists_tac`bs1 with pc := pc` >>
            simp[bc_state_component_equality,Abbr`bs1`] >>
            conj_tac >- (
              match_mp_tac Cenv_bs_with_irr >>
              HINT_EXISTS_TAC >> simp[] ) >>
            imp_res_tac Cenv_bs_CTLet_bound >>
            pop_assum(qspec_then`sz+1`mp_tac) >>
            imp_res_tac CTDec_bound_lemma >>
            pop_assum(qspec_then`LENGTH bs.stack`mp_tac) >>
            fs[Cenv_bs_def] >>
            srw_tac[ARITH_ss][]) >>
          fsrw_tac[DNF_ss,ARITH_ss]
            [FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2`,Abbr`lc3`
            ,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP] >>
          rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
        disch_then(mp_tac o CONJUNCT1) >>
        simp_tac(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] >>
        map_every qx_gen_tac[`rfs3`,`sm3`,`ck3`,`gv3`,`b3`] >> strip_tac >>
        map_every qexists_tac[`rfs3`,`sm3`,`ck3`,`gv3`,`b3`] >>
        qmatch_assum_abbrev_tac`bc_next^* bs bs03` >>
        qmatch_assum_abbrev_tac`bc_next^* bs05 bs07` >>
        `bc_next^* bs03 bs05` by (
          `bc_fetch bs03 = SOME (JumpIf (Lab nl))` by (
            match_mp_tac bc_fetch_next_addr >>
            rw[Abbr`bs03`,Abbr`lc2`] >>
            qexists_tac`bc0 ++ REVERSE be1` >>
            rw[]) >>
          rw[RTC_eq_NRC] >>
          qexists_tac`SUC (SUC 0)` >>
          rw[NRC] >>
          rw[bc_eval1_thm] >>
          rw[Once bc_eval1_def] >>
          rw[Abbr`bs03`,LET_THM] >>
          srw_tac[DNF_ss][] >>
          rw[bc_find_loc_def] >>
          rw[LEFT_EXISTS_AND_THM] >- (
            qmatch_abbrev_tac`∃n. X = SOME n` >>
            qsuff_tac `X ≠ NONE` >- (Cases_on`X` >> rw[]) >>
            qunabbrev_tac`X` >>
            match_mp_tac (CONTRAPOS (SPEC_ALL bc_find_loc_aux_NONE)) >>
            fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,between_def,is_Label_rwt,MEM_FILTER,Abbr`lc2`]) >>
          qmatch_abbrev_tac`bc_eval1 (bump_pc bs03) = SOME bs06` >>
          `bc_fetch bs03 = SOME (JumpIf (Lab nl))` by (
            fs[bc_fetch_def,Abbr`bs03`] >> rfs[REVERSE_APPEND] ) >>
          rw[bump_pc_def] >>
          rw[Abbr`bs03`] >>
          qmatch_abbrev_tac`bc_eval1 bs03 = SOME bs06` >>
          `bc_fetch bs03 = SOME (Jump (Lab (nl + 1)))` by (
            match_mp_tac bc_fetch_next_addr >>
            rw[Abbr`bs03`,Abbr`lc2`] >>
            qexists_tac`bc0 ++ REVERSE be1 ++ [JumpIf (Lab nl)]` >>
            rw[REVERSE_APPEND,FILTER_APPEND,SUM_APPEND] >>
            srw_tac[ARITH_ss][] ) >>
          rw[bc_eval1_def] >>
          rw[Abbr`bs03`,Abbr`bs06`,Abbr`bs05`] >>
          simp[bc_state_component_equality] >>
          reverse conj_tac >- (
            imp_res_tac RTC_bc_next_clock_less >>
            rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
          rw[bc_find_loc_def] >>
          match_mp_tac bc_find_loc_aux_append_code >>
          match_mp_tac bc_find_loc_aux_append_code >>
          match_mp_tac bc_find_loc_aux_append_code >>
          match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
          simp[Abbr`lc3`] >>
          Q.PAT_ABBREV_TAC`ls = X ++ REVERSE be2` >>
          qexists_tac`LENGTH ls + 1` >>
          lrw[Abbr`ls`,EL_APPEND2] >>
          lrw[TAKE_APPEND2,FILTER_APPEND] >>
          fsrw_tac[DNF_ss][ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,EVERY_MEM,MEM_FILTER,is_Label_rwt,Abbr`lc2`,between_def,MEM_MAP,Abbr`nl`] >>
          rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
        conj_tac >- (
          qmatch_abbrev_tac`bc_next^* bs bs08` >>
          `bs08 = bs07` by (
            rw[Abbr`bs08`,Abbr`bs07`] >>
            rw[bc_state_component_equality] >>
            rw[FILTER_APPEND] ) >>
          metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
        simp[] >>
        conj_tac >- (
          match_mp_tac Cenv_bs_with_irr >>
          HINT_EXISTS_TAC >> simp[] ) >>
        metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS,gvrel_trans] ) >>
      conj_tac >- (
        tac1 >>
        Cases_on `b1` >> fs[] >- (
          first_x_assum(qspecl_then[`rd'`,`cs2`,`cenv`,`sz`,`bs1 with <| stack := bs.stack; pc := next_addr bs.inst_length (bc0 ++ REVERSE be1 ++ REVERSE lc2) |>`
                                   ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2`,`REVERSE be2`]mp_tac) >>
          simp[Abbr`bs1`] >>
          `ck = SOME (FST (FST s'))` by (
            imp_res_tac RTC_bc_next_clock_less >>
            rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
          discharge_hyps >- (
            qmatch_assum_abbrev_tac`Cevaluate s env exp (s',Rval(CLitv(Bool T)))` >>
            qspecl_then[`s`,`env`,`exp`,`(s',Rval (CLitv (Bool T)))`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
            simp[] >> strip_tac >>
            qspecl_then[`s`,`env`,`exp`,`(s',Rval (CLitv (Bool T)))`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
            simp[] >>
            discharge_hyps >- simp[Abbr`env`] >> simp[] >> strip_tac >>
            simp[] >>
            conj_tac >- ( fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,EVERY_MEM,Abbr`env`,vlabs_csg_def] >> metis_tac[] ) >>
            conj_tac >- ( fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,EVERY_MEM,Abbr`env`,vlabs_csg_def] >> metis_tac[] ) >>
            conj_tac >- (
              match_mp_tac Cenv_bs_imp_decsz >>
              qmatch_assum_abbrev_tac `Cenv_bs rd' s' renv cenv (sz + 1) bs1` >>
              Q.PAT_ABBREV_TAC`pc = next_addr X Y` >>
              qexists_tac`bs1 with pc := pc` >>
              simp[bc_state_component_equality,Abbr`bs1`] >>
              conj_tac >- (
                match_mp_tac Cenv_bs_with_irr >>
                HINT_EXISTS_TAC >> simp[] ) >>
              imp_res_tac Cenv_bs_CTLet_bound >>
              pop_assum(qspec_then`sz+1`mp_tac) >>
              imp_res_tac CTDec_bound_lemma >>
              pop_assum(qspec_then`LENGTH bs.stack`mp_tac) >>
              fs[Cenv_bs_def] >>
              srw_tac[ARITH_ss][] ) >>
            fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2`
                            ,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP] >>
            rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
          disch_then(mp_tac o CONJUNCT2) >>
          disch_then(mp_tac o CONV_RULE (RESORT_FORALL_CONV (op@ o partition (C mem ["args'","klvs'"] o fst o dest_var)))) >>
          disch_then(qspecl_then[`klvs`,`args`]mp_tac) >>
          fs[Abbr`tt`,Once SWAP_REVERSE] >>
          simp[Abbr`cs2`] >>
          disch_then(qspecl_then[`env0`,`vs`,`blvs`,`benv`,`ret`,`cl`,`st`]mp_tac) >>
          simp[] >>
          discharge_hyps >- (
            conj_tac >> (
            qmatch_abbrev_tac`EVERY2 Q l1 l2` >>
            ho_match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
            qmatch_assum_abbrev_tac`EVERY2 P l1 l2` >>
            qexists_tac`P`>>rw[Abbr`P`,Abbr`Q`] >>
            match_mp_tac (GEN_ALL (MP_CANON (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
            simp[] >>
            qexists_tac`rd` >>
            simp[] >>
            fs[SUBMAP_DEF,DRESTRICT_DEF,s_refs_def,good_rd_def,Cenv_bs_def,UNCURRY,FEVERY_DEF] )) >>
          simp[code_for_return_def] >>
          simp_tac(srw_ss()++DNF_ss)[] >>
          tac3) >>
        qmatch_assum_abbrev_tac`(compile cenv tt sz cs3 e3).out = X` >> qunabbrev_tac`X` >>
        first_x_assum(qspecl_then[`rd'`,`cs3`,`cenv`,`sz`,`bs1 with <| stack := bs.stack;
                                  pc := next_addr bs.inst_length (bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2 ++ REVERSE lc3) |>`
                                 ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2 ++ REVERSE lc3`,`REVERSE be3`]mp_tac) >>
        simp[Abbr`bs1`,Once SWAP_REVERSE] >>
        `ck = SOME (FST (FST s'))` by (
          imp_res_tac RTC_bc_next_clock_less >>
          rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
        discharge_hyps >- (
          qmatch_assum_abbrev_tac`Cevaluate s env exp (s',Rval(CLitv(Bool F)))` >>
          qspecl_then[`s`,`env`,`exp`,`(s',Rval (CLitv (Bool F)))`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
          simp[] >> strip_tac >>
          qspecl_then[`s`,`env`,`exp`,`(s',Rval (CLitv (Bool F)))`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
          simp[] >> discharge_hyps >- simp[Abbr`env`] >> simp[] >> strip_tac >>
          conj_tac >- ( fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,EVERY_MEM,Abbr`env`,vlabs_csg_def] >> metis_tac[] ) >>
          conj_tac >- ( fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,EVERY_MEM,Abbr`env`,vlabs_csg_def] >> metis_tac[] ) >>
          conj_tac >- (
            match_mp_tac Cenv_bs_imp_decsz >>
            qmatch_assum_abbrev_tac `Cenv_bs rd' s' renv cenv (sz + 1) bs1` >>
            Q.PAT_ABBREV_TAC`pc = next_addr X Y` >>
            qexists_tac`bs1 with pc := pc` >>
            simp[bc_state_component_equality,Abbr`bs1`] >>
            conj_tac >- (
              match_mp_tac Cenv_bs_with_irr >>
              HINT_EXISTS_TAC >> simp[] ) >>
            imp_res_tac Cenv_bs_CTLet_bound >>
            pop_assum(qspec_then`sz+1`mp_tac) >>
            imp_res_tac CTDec_bound_lemma >>
            pop_assum(qspec_then`LENGTH bs.stack`mp_tac) >>
            fs[Cenv_bs_def] >>
            srw_tac[ARITH_ss][]) >>
          fsrw_tac[DNF_ss,ARITH_ss]
            [FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2`,Abbr`lc3`,Abbr`cs3`
            ,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP] >>
          rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
        disch_then(mp_tac o CONJUNCT2) >>
        disch_then(mp_tac o CONV_RULE (RESORT_FORALL_CONV (op@ o partition (C mem ["args'","klvs'"] o fst o dest_var)))) >>
        disch_then(qspecl_then[`klvs`,`args`]mp_tac) >>
        simp[] >>
        simp[Abbr`cs3`] >>
        disch_then(qspecl_then[`env0`,`vs`,`blvs`,`benv`,`ret`,`cl`,`st`]mp_tac) >>
        simp[] >>
        discharge_hyps >- (
          conj_tac >> (
          qmatch_abbrev_tac`EVERY2 Q l1 l2` >>
          ho_match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
          qmatch_assum_abbrev_tac`EVERY2 P l1 l2` >>
          qexists_tac`P`>>rw[Abbr`P`,Abbr`Q`] >>
          match_mp_tac (GEN_ALL (MP_CANON (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
          simp[] >>
          qexists_tac`rd` >>
          simp[] >>
          fs[SUBMAP_DEF,DRESTRICT_DEF,good_rd_def,s_refs_def,Cenv_bs_def,UNCURRY,FEVERY_DEF] )) >>
        tac4) >>
      Cases >> rpt gen_tac >> fs[] >> strip_tac >- (
        tac1 >- (
          Cases_on `b1` >> fs[] >- (
            tac2 >>
            disch_then(qspec_then`tt`mp_tac) >> simp[Abbr`tt`] >>
            disch_then(qspecl_then[`ig`,`sp`,`hdl`,`st`]mp_tac) >>
            simp[] >>
            simp_tac(srw_ss()++DNF_ss)[code_for_return_def,LET_THM] >>
            `ck = SOME (FST (FST s'))` by (
              imp_res_tac RTC_bc_next_clock_less >>
              rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
            tac3 ) >>
          tac5 >>
          disch_then(qspec_then`tt`mp_tac) >> simp[] >>
          discharge_hyps >- simp[Abbr`cs3`] >>
          disch_then(qspecl_then[`ig`,`sp`,`hdl`,`st`]mp_tac) >>
          simp[Abbr`tt`,Abbr`cs3`] >>
          tac4) >>
        Cases_on `b1` >> fs[] >- (
          tac2 >>
          disch_then(qspec_then`tt`mp_tac) >> simp[Abbr`tt`] >>
          `ck = SOME (FST (FST s'))` by (
            imp_res_tac RTC_bc_next_clock_less >>
            rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
          strip_tac >> tac6) >>
        tac5 >>
        disch_then(qspec_then`tt`mp_tac) >> simp[] >>
        discharge_hyps >- simp[Abbr`cs3`] >>
        simp[Abbr`tt`,Abbr`cs3`] >>
        `ck = SOME (FST (FST s'))` by (
          imp_res_tac RTC_bc_next_clock_less >>
          rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
        qpat_assum`bc_next^* bs X`mp_tac >> simp[] >>
        ntac 2 strip_tac >>
        tac7) >>
      tac1 >- (
        Cases_on `b1` >> fs[] >- (
          tac2 >>
          disch_then(qspec_then`tt`mp_tac) >> simp[Abbr`tt`] >>
          simp_tac(srw_ss()++DNF_ss)[] >>
          disch_then(qspecl_then[`sp`,`hdl`,`st`,`blvs`]mp_tac) >> simp[] >>
          disch_then(qspecl_then[`args`]mp_tac) >> simp[] >>
          simp_tac(srw_ss()++DNF_ss)[code_for_return_def,LET_THM] >>
          `ck = SOME (FST (FST s'))` by (
            imp_res_tac RTC_bc_next_clock_less >>
            rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
          tac3 ) >>
        tac5 >>
        disch_then(qspec_then`tt`mp_tac) >> simp[Abbr`tt`] >>
        simp_tac(srw_ss()++DNF_ss)[] >>
        disch_then(qspecl_then[`sp`,`hdl`,`st`,`blvs`]mp_tac) >> simp[] >>
        disch_then(qspecl_then[`args`]mp_tac) >> simp[] >>
        simp[Abbr`cs3`] >>
        `ck = SOME (FST (FST s'))` by (
          imp_res_tac RTC_bc_next_clock_less >>
          rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
        tac4 ) >>
      Cases_on `b1` >> fs[] >- (
        tac2 >>
        disch_then(qspec_then`tt`mp_tac) >> simp[Abbr`tt`] >>
        simp_tac(srw_ss()++DNF_ss)[] >>
        disch_then(qspecl_then[`blvs`]mp_tac) >> simp[] >>
        disch_then(qspecl_then[`args`]mp_tac) >> simp[] >>
        simp_tac(srw_ss()++DNF_ss)[code_for_return_def,LET_THM] >>
        `ck = SOME (FST (FST s'))` by (
          imp_res_tac RTC_bc_next_clock_less >>
          rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
        qpat_assum`bc_next^* bs X`mp_tac >> simp[] >>
        rpt strip_tac >>
        tac6 ) >>
      tac5 >>
      disch_then(qspec_then`tt`mp_tac) >> simp[Abbr`tt`] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      disch_then(qspecl_then[`blvs`]mp_tac) >> simp[] >>
      disch_then(qspecl_then[`args`]mp_tac) >> simp[] >>
      simp[Abbr`cs3`] >>
      `ck = SOME (FST (FST s'))` by (
        imp_res_tac RTC_bc_next_clock_less >>
        rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
      qpat_assum`bc_next^* bs X`mp_tac >> simp[] >>
      rpt strip_tac >>
      tac7
    end) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def] >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`be1`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    Q.PAT_ABBREV_TAC`cs0 = compile cenv t sz cs exp` >>
    qabbrev_tac`nl = cs0.next_label` >>
    full_simp_tac std_ss [prove(``w::x::y::cs0.out=[w;x;y]++cs0.out``,rw[])] >>
    full_simp_tac std_ss [prove(``x::y::(cs0).out=[x;y]++(cs0).out``,rw[])] >>
    Q.PAT_ABBREV_TAC`lc3 = [Label x;y]` >>
    Q.PAT_ABBREV_TAC`lc2 = [Label x;y;z]` >>
    BasicProvers.VAR_EQ_TAC >> simp[] >> fs[] >>
    gen_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd (K (lc2++be1++Z)) Y` >>
    qspecl_then[`cenv`,`t`,`sz`,`cs1`,`e2`](Q.X_CHOOSE_THEN`be2`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    Q.PAT_ABBREV_TAC`cs2 = compiler_result_out_fupd X Y` >>
    qspecl_then[`cenv`,`t`,`sz`,`cs2`,`e3`](Q.X_CHOOSE_THEN`be3`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    simp[Once SWAP_REVERSE,Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
    rpt gen_tac >> strip_tac >>
    first_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE be1`]mp_tac) >>
    simp[] >>
    disch_then(qspec_then`TCNonTail`mp_tac) >>
    simp[] >>
    metis_tac[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> simp[compile_def,pushret_def] >>
    qpat_assum`bce ++ bcr = X`kall_tac>>
    qpat_assum`bs.code = X`mp_tac >> simp[IMP_CONJ_THM] >>
    map_every qid_spec_tac[`code`,`bc1`] >> simp[FORALL_AND_THM] >>
    conj_asm1_tac >- (
      simp[Once SWAP_REVERSE] >>
      rpt gen_tac >> strip_tac >>
      rpt gen_tac >> strip_tac >>
      `bc_fetch bs = SOME (Galloc n)` by (
        match_mp_tac bc_fetch_next_addr >>
        qexists_tac`bc0` >> simp[] ) >>
      simp[code_for_push_def] >>
      simp[Once RTC_CASES1] >>
      srw_tac[DNF_ss][] >> disj2_tac >>
      simp[bc_eval1_thm] >>
      simp[bc_eval1_def,bump_pc_def] >>
      simp[Once RTC_CASES2] >>
      srw_tac[DNF_ss][] >> disj2_tac >>
      simp[Once RTC_CASES2] >>
      srw_tac[DNF_ss][] >> disj1_tac >>
      Q.PAT_ABBREV_TAC`bs1:bc_state  = X Y` >>
      `bc_fetch bs1 = SOME(Stack(Cons unit_tag 0))` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs1`] >>
        qexists_tac`bc0++[Galloc n]` >>
        simp[FILTER_APPEND,SUM_APPEND] ) >>
      simp[bc_eval1_thm] >>
      simp[bc_eval1_def,bump_pc_def] >>
      simp[bc_eval_stack_def] >>
      simp[Abbr`bs1`,bc_state_component_equality] >>
      simp[SUM_APPEND,FILTER_APPEND] >>
      simp[Once Cv_bv_cases] >>
      qexists_tac`rd` >> simp[] >>
      reverse conj_asm2_tac >- (
        simp[gvrel_def,EL_APPEND1] ) >>
      match_mp_tac Cenv_bs_imp_incsz >>
      Q.PAT_ABBREV_TAC`bs1:bc_state  = X Y` >>
      qexists_tac`bs1 with stack := bs.stack` >>
      simp[Abbr`bs1`,bc_state_component_equality] >>
      match_mp_tac Cenv_bs_change_store >>
      Q.PAT_ABBREV_TAC`bs1:bc_state  = X Y` >>
      map_every qexists_tac[`rd`,`(cs,g)`,`bs1 with globals := bs.globals`] >>
      simp[Abbr`bs1`,bc_state_component_equality] >>
      conj_tac >- (
        match_mp_tac Cenv_bs_with_irr >>
        HINT_EXISTS_TAC >> simp[] )>>
      fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
      match_mp_tac EVERY2_APPEND_suff >>
      simp[] >> simp[EVERY2_EVERY] >>
      simp[EVERY_MEM,MEM_ZIP,PULL_EXISTS] >>
      simp[optionTheory.OPTREL_def] ) >>
    rw[] >> fs[Once SWAP_REVERSE] >>
    match_mp_tac code_for_push_return >>
    rfs[] >>
    first_assum (match_exists_tac o concl) >>
    simp[] >>
    qexists_tac`REVERSE args`>>simp[]>>
    fs[EVERY2_EVERY] ) >>
  strip_tac >- (
    simp[] >>
    simp[code_for_push_def,compile_def] >>
    rw[Once SWAP_REVERSE] >>
    map_every qexists_tac[`bs.refs`,`rd`,`bs.clock`,`bs.globals`] >>
    rw[RTC_eq_NRC] >>
    TRY (qexists_tac`0` >>rw[]) >>
    TRY (qmatch_abbrev_tac `Cenv_bs rd s B C D E` >>
         qmatch_assum_abbrev_tac `Cenv_bs rd s B C D E'` >>
         qsuff_tac`E = E'`>-rw[] >>
         unabbrev_all_tac) >>
    rw[bc_state_component_equality]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    fs[] >> BasicProvers.VAR_EQ_TAC >> simp[] >>
    pop_assum mp_tac >>
    simp[compile_def] >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`cs0.out = be ++ cs.out` >>
    qspecl_then[`cenv`,`sz+1`,`cs0`,`exps`]mp_tac(CONJUNCT2(CONJUNCT2 compile_append_out)) >>
    disch_then(Q.X_CHOOSE_THEN`bes`strip_assume_tac) >>
    simp[Once SWAP_REVERSE] >> strip_tac >>
    last_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE be`]mp_tac) >>
    simp[] >>
    disch_then(mp_tac o CONJUNCT1) >>
    simp[code_for_push_def] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`rfs`,`rd'`,`ck`,`gv`,`bv`] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    qmatch_assum_abbrev_tac`cs0.out = be ++ cs.out` >>
    first_x_assum(qspecl_then[`rd'`,`cs0`,`cenv`,`sz+1`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE be`,`REVERSE bes`]mp_tac) >>
    simp[Abbr`bs1`] >>
    `ck = SOME (FST (FST s'))` by (
      imp_res_tac RTC_bc_next_clock_less >>
      rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
    discharge_hyps >- (
      qspecl_then[`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
      simp[] >> strip_tac >>
      qspecl_then[`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
      simp[] >> strip_tac >>
      conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >> metis_tac[] ) >>
      conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >> metis_tac[] ) >>
      match_mp_tac compile_labels_lemma >> fs[Abbr`cs0`] >>
      map_every qexists_tac[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`,`bc0`] >>
      simp[]) >>
    simp[code_for_push_def] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`bvs`,`rf`,`rd''`,`ck'`,`gvv`] >>
    strip_tac >>
    map_every qexists_tac[`rf`,`rd''`,`ck'`,`gvv`,`bv`,`bvs`] >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
    conj_tac >- (
      qmatch_abbrev_tac `bc_next^* bs bs3` >>
      qsuff_tac `bs2 = bs3` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
      rw[Abbr`bs2`,Abbr`bs3`,bc_state_component_equality,REVERSE_APPEND] ) >>
    qpat_assum`X = vs'`(assume_tac o SYM) >>
    fsrw_tac[ARITH_ss][EVERY2_EVERY,ADD1] >> rfs[] >>
    conj_tac >- (
      match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
      qexists_tac `rd'` >>
      simp[] >>
      fs[SUBMAP_DEF,DRESTRICT_DEF,Cenv_bs_def,s_refs_def,good_rd_def,UNCURRY,FEVERY_DEF] ) >>
    conj_tac >- (
      qmatch_abbrev_tac `Cenv_bs rd'' s2 renv env0 sz0 bsx` >>
      qmatch_assum_abbrev_tac `Cenv_bs rd'' s2 renv env0 sz0 bsy` >>
      `bsx = bsy` by (
        rw[Abbr`bsx`,Abbr`bsy`,bc_state_component_equality,REVERSE_APPEND] ) >>
      rw[] ) >>
    metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS,gvrel_trans]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    fs[] >> BasicProvers.VAR_EQ_TAC >> simp[] >>
    pop_assum mp_tac >>
    simp[compile_def] >>
    qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`cs0.out = be ++ cs.out` >>
    qspecl_then[`cenv`,`sz+1`,`cs0`,`es`]mp_tac(CONJUNCT2(CONJUNCT2 compile_append_out)) >>
    disch_then(Q.X_CHOOSE_THEN`bes`strip_assume_tac) >>
    simp[Once SWAP_REVERSE] >> strip_tac >>
    last_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE be`]mp_tac) >>
    simp[] >>
    disch_then(qspec_then`TCNonTail`mp_tac) >>
    simp[] >>
    metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  fs[] >> BasicProvers.VAR_EQ_TAC >> simp[] >>
  pop_assum mp_tac >>
  simp[compile_def] >>
  qspecl_then[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
  disch_then(Q.X_CHOOSE_THEN`be`strip_assume_tac) >>
  qmatch_assum_abbrev_tac`cs0.out = be ++ cs.out` >>
  qspecl_then[`cenv`,`sz+1`,`cs0`,`exps`]mp_tac(CONJUNCT2(CONJUNCT2 compile_append_out)) >>
  disch_then(Q.X_CHOOSE_THEN`bes`strip_assume_tac) >>
  simp[Once SWAP_REVERSE] >> strip_tac >>
  last_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE be`]mp_tac) >>
  simp[] >>
  disch_then(mp_tac o CONJUNCT1) >>
  simp[code_for_push_def] >>
  disch_then(qx_choosel_then[`xxx`,`rfs`,`rd'`,`ck`,`gv`]mp_tac) >>
  strip_tac >>
  qmatch_assum_rename_tac`xxx = [bv0]`[] >>
  `ck = SOME (FST (FST s'))` by (
    imp_res_tac RTC_bc_next_clock_less >>
    rfs[optionTheory.OPTREL_def,Cenv_bs_def,s_refs_def] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  first_x_assum(qspecl_then[`rd'`,`cs0`,`cenv`,`sz+1`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE be`,`REVERSE bes`]mp_tac) >>
  simp[Abbr`bs1`] >>
  qmatch_assum_abbrev_tac`cs0.out = be ++ cs.out` >>
  discharge_hyps >- (
    qspecl_then[`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 Cevaluate_vlabs) >>
    simp[] >> strip_tac >>
    qspecl_then[`s`,`env`,`exp`,`(s',Rval v)`]mp_tac(CONJUNCT1 Cevaluate_all_vlabs) >>
    simp[] >> strip_tac >>
    conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >> metis_tac[] ) >>
    conj_tac >- ( fsrw_tac[DNF_ss][SUBSET_DEF,EVERY_MEM,vlabs_csg_def] >> metis_tac[] ) >>
    fs[] >> rfs[] >>
    match_mp_tac compile_labels_lemma >> fs[Abbr`cs0`] >>
    map_every qexists_tac[`cenv`,`TCNonTail`,`sz`,`cs`,`exp`,`bc0`] >>
    simp[]) >>
  reverse(Cases_on`err`)>>simp[] >- (
    fs[] >>
    metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
  strip_tac >> rpt strip_tac >>
  first_x_assum(qspecl_then[`bv0::ig`,`sp`,`hdl`,`st`]mp_tac) >>
  simp[] >>
  simp[code_for_return_def] >>
  fsrw_tac[DNF_ss][] >>
  map_every qx_gen_tac[`bv'`,`rf`,`rd''`,`ck'`,`gvv`] >>
  strip_tac >>
  map_every qexists_tac[`bv'`,`rf`,`rd''`,`ck'`,`gvv`] >>
  simp[] >>
  metis_tac[RTC_TRANSITIVE,transitive_def,SUBMAP_TRANS,IS_PREFIX_TRANS,gvrel_trans])

;val _ = export_theory ()
