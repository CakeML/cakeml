open HolKernel bossLib boolLib boolSimps SatisfySimps listTheory rich_listTheory pairTheory pred_setTheory finite_mapTheory alistTheory relationTheory arithmeticTheory lcsymtacs quantHeuristicsLib quantHeuristicsLibAbbrev
open MiniMLTerminationTheory miniMLExtraTheory miscTheory miscLib compileTerminationTheory intLangTheory bytecodeTerminationTheory evaluateEquationsTheory expToCexpTheory pmatchTheory labelClosuresTheory bytecodeEvalTheory bytecodeExtraTheory
val _ = numLib.prefer_num()
val _ = new_theory "compileCorrectness"

val exp_pred_def = tDefine "exp_pred"`
  (exp_pred (Raise _) = T) ∧
  (exp_pred (Handle _ _ _) = F) ∧
  (exp_pred (Lit _) = T) ∧
  (exp_pred (Con _ es) = EVERY exp_pred es) ∧
  (exp_pred (Var _ _) = T) ∧
  (exp_pred (Fun _ _ e) = exp_pred e) ∧
  (exp_pred (Uapp _ e) = exp_pred e) ∧
  (exp_pred (App _ e1 e2) = exp_pred e1 ∧ exp_pred e2) ∧
  (exp_pred (Log _ e1 e2) = exp_pred e1 ∧ exp_pred e2) ∧
  (exp_pred (If e1 e2 e3) = exp_pred e1 ∧ exp_pred e2 ∧ exp_pred e3) ∧
  (exp_pred (Mat e pes) = exp_pred e ∧ EVERY exp_pred (MAP SND pes)) ∧
  (exp_pred (Let _ _ _ e1 e2) = exp_pred e1 ∧ exp_pred e2) ∧
  (exp_pred (Letrec _ defs e) = EVERY exp_pred (MAP (SND o SND o SND o SND) defs) ∧ exp_pred e)`
  (WF_REL_TAC `measure (exp_size ARB)` >>
   srw_tac[ARITH_ss][exp8_size_thm,exp5_size_thm,SUM_MAP_exp7_size_thm,
                     exp1_size_thm,SUM_MAP_exp2_size_thm,SUM_MAP_exp3_size_thm,SUM_MAP_exp4_size_thm,SUM_MAP_exp6_size_thm] >>
   Q.ISPEC_THEN`exp_size ARB`imp_res_tac SUM_MAP_MEM_bound >>
   fsrw_tac[ARITH_ss][MAP_MAP_o,combinTheory.o_DEF])
val _ = export_rewrites["exp_pred_def"]

(* TODO: move *)
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

val SWAP_REVERSE_SYM = store_thm("SWAP_REVERSE_SYM",
  ``!l1 l2. (REVERSE l1 = l2) = (l1 = REVERSE l2)``,
  metis_tac[SWAP_REVERSE])

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

val Cexp_pred_def = tDefine "Cexp_pred"`
  (Cexp_pred (CDecl _) = T) ∧
  (Cexp_pred (CRaise _) = T) ∧
  (Cexp_pred (CHandle _ _) = F) ∧
  (Cexp_pred (CVar _) = T) ∧
  (Cexp_pred (CLit _) = T) ∧
  (Cexp_pred (CCon _ es) = EVERY Cexp_pred es) ∧
  (Cexp_pred (CTagEq e _) = Cexp_pred e) ∧
  (Cexp_pred (CProj e _) = Cexp_pred e) ∧
  (Cexp_pred (CLet e0 e) = Cexp_pred e0 ∧ Cexp_pred e) ∧
  (Cexp_pred (CLetrec defs e) = EVERY Cexp_pred (MAP (SND o OUTL) (FILTER ISL defs)) ∧ Cexp_pred e) ∧
  (Cexp_pred (CFun (INL (az,e))) = Cexp_pred e) ∧
  (Cexp_pred (CFun _) = T) ∧
  (Cexp_pred (CCall e es) = Cexp_pred e ∧ EVERY Cexp_pred es) ∧
  (Cexp_pred (CPrim1 _ e) = Cexp_pred e) ∧
  (Cexp_pred (CPrim2 _ e1 e2) = Cexp_pred e1 ∧ Cexp_pred e2) ∧
  (Cexp_pred (CUpd e1 e2) = Cexp_pred e1 ∧ Cexp_pred e2) ∧
  (Cexp_pred (CIf e1 e2 e3) = Cexp_pred e1 ∧ Cexp_pred e2 ∧ Cexp_pred e3)`
  (WF_REL_TAC `measure Cexp_size` >>
   srw_tac[ARITH_ss][Cexp4_size_thm,Cexp1_size_thm,SUM_MAP_Cexp2_size_thm] >>
   Q.ISPEC_THEN`Cexp_size`imp_res_tac SUM_MAP_MEM_bound >>
   fsrw_tac[ARITH_ss][MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,MEM_FILTER] >>
   rw[] >>
   simp[basicSizeTheory.pair_size_def,UNCURRY] >>
   simp[SUM_MAP_PLUS] )
val _ = export_rewrites["Cexp_pred_def"]
val Cexp_pred_ind = theorem"Cexp_pred_ind"

val Cexp_pred_mkshift = store_thm("Cexp_pred_mkshift",
  ``∀f k e . Cexp_pred e ⇒ Cexp_pred (mkshift f k e)``,
  ho_match_mp_tac mkshift_ind >> simp[] >> rw[] >>
  fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,MEM_FILTER] >>
  TRY gen_tac >>
  Cases_on`cb`>>TRY(PairCases_on`x`)>>fs[]>>
  strip_tac >> res_tac >>fs[])
val _ = export_rewrites["Cexp_pred_mkshift"]

val Cexp_pred_remove_mat_vp = store_thm("Cexp_pred_remove_mat_vp",
  ``(∀p fk sk v. Cexp_pred sk ⇒ Cexp_pred (remove_mat_vp fk sk v p)) ∧
    (∀ps fk sk v n. Cexp_pred sk ⇒ Cexp_pred (remove_mat_con fk sk v n ps))``,
  ho_match_mp_tac(TypeBase.induction_of(``:Cpat``)) >>
  rw[remove_mat_vp_def,shift_def] >> rw[] )

val Cexp_pred_remove_mat_var = store_thm("Cexp_pred_remove_mat_var",
  ``∀v pes. EVERY Cexp_pred (MAP SND pes) ⇒ Cexp_pred (remove_mat_var v pes)``,
  ho_match_mp_tac remove_mat_var_ind >>
  rw[remove_mat_var_def] >> rw[Cexp_pred_remove_mat_vp,shift_def])

val exp_pred_Cexp_pred = store_thm("exp_pred_Cexp_pred",
  ``∀m e. exp_pred e ⇒ Cexp_pred (exp_to_Cexp m e)``,
  ho_match_mp_tac exp_to_Cexp_nice_ind >>
  rw[exp_to_Cexp_def,LET_THM,exps_to_Cexps_MAP,EVERY_MAP,shift_def] >>
  TRY (
    BasicProvers.EVERY_CASE_TAC >>
    rw[] >> fs[] ) >>
  fs[EVERY_MEM,FORALL_PROD] >- (
    match_mp_tac Cexp_pred_remove_mat_var >>
    fsrw_tac[DNF_ss][EVERY_MEM,FORALL_PROD,MEM_MAP,pes_to_Cpes_MAP,LET_THM,UNCURRY] >>
    metis_tac[Cexp_pred_mkshift] )
  >- (
    fsrw_tac[DNF_ss][defs_to_Cdefs_MAP,EVERY_MEM,MEM_MAP,MEM_FILTER,FORALL_PROD] >>
    metis_tac[] ) >>
  Cases_on `pat_to_Cpat m p` >> fs[])

val repl_exp_contab = store_thm("repl_exp_contab",
  ``(repl_exp rs exp = (rs',c)) ==> (rs'.contab = rs.contab)``,
  rw[repl_exp_def,compile_Cexp_def,LET_THM,UNCURRY] >> rw[])

val lookup_cc_def = Define`
  (lookup_cc cl sz st rs (CCArg n) = el_check (sz + n) st) ∧
  (lookup_cc cl sz st rs (CCEnv n) =
   OPTION_BIND (el_check sz st)
   (λv. case v of Block 0 vs => el_check n vs | _ => NONE)) ∧
  (lookup_cc cl sz st rs (CCRef n) =
   OPTION_BIND (el_check sz st)
   (λv. case v of Block 0 vs =>
     OPTION_BIND (el_check n vs)
     (λv. case v of RefPtr p => if p ∈ cl then FLOOKUP rs p else NONE | _ => NONE)
     | _ => NONE))`
val lookup_ct_def = Define`
  (lookup_ct cl sz st rs (CTLet n) = if sz < n then NONE else el_check (sz - n) st) ∧
  (lookup_ct cl sz st rs (CTEnv cc) = lookup_cc cl sz st rs cc)`
val _ = export_rewrites["lookup_ct_def","lookup_cc_def"]

(*
val _ = Parse.overload_on("bundle_fvs", ``λc ns defs.
  BIGUNION (IMAGE (λ(xs,cb). cbod_fvs c cb DIFF set xs DIFF set ns) (set defs))``)
*)

val _ = Hol_datatype`refs_data = <| sm : num list; cls : num |-> (Cv list # def list # num) |>`

val (Cv_bv_rules,Cv_bv_ind,Cv_bv_cases) = Hol_reln`
  (Cv_bv pp (CLitv (IntLit k)) (Number k)) ∧
  (Cv_bv pp (CLitv (Bool b)) (bool_to_val b)) ∧
  (Cv_bv pp (CLitv Unit) unit_val) ∧
  ((el_check m (FST pp).sm = SOME p) ⇒ Cv_bv pp (CLoc m) (RefPtr p)) ∧
  (EVERY2 (Cv_bv pp) vs bvs ⇒ Cv_bv pp (CConv cn vs) (Block (cn+block_tag) bvs)) ∧
  ((pp = (rd,c,l2a)) ∧
   (∀i l. i < LENGTH defs ∧ (EL i defs = INR l) ⇒ l ∈ FDOM c ∧ ((c ' l).nz = LENGTH defs) ∧ ((c ' l).ez = LENGTH env) ∧ ((c ' l).ix = i)) ∧
   (el_check n defs = SOME (INR l)) ∧
   (l2a l = SOME a) ∧
   (FLOOKUP c l = SOME cd) ∧
   (cd.ix = n) ∧
   benv_bvs pp bvs cd env defs
   ⇒ Cv_bv pp (CRecClos env defs n) (Block closure_tag [CodePtr a; Block 0 bvs])) ∧
  ((pp = (rd,c,l2a)) ∧
   (cd.ceenv = (recs,envs)) ∧
   (LENGTH bvs = LENGTH recs + LENGTH envs) ∧
   (∀i x bv. i < LENGTH recs ∧ (x = EL i recs) ∧ (bv = EL i bvs) ⇒
     x < LENGTH defs ∧
     ∃p jenv jdefs jx.
       (bv = RefPtr p) ∧ jx < LENGTH jdefs ∧
       (FLOOKUP rd.cls p = SOME (jenv,jdefs,jx)) ∧
       syneq c (CRecClos jenv jdefs jx) (CRecClos env defs x)) ∧
   (∀i x bv. i < LENGTH envs ∧ (x = EL i envs) ∧ (bv = EL (LENGTH recs + i) bvs) ⇒
       x < LENGTH env ∧ Cv_bv pp (EL x env) bv)
   ⇒ benv_bvs pp bvs cd env defs)`

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

val Cv_bv_ov = store_thm("Cv_bv_ov",
  ``∀m pp Cv bv. Cv_bv pp Cv bv ⇒ ∀s. ((FST pp).sm = s) ⇒ (Cv_to_ov m s Cv = bv_to_ov m bv)``,
  ntac 2 gen_tac >>
  ho_match_mp_tac Cv_bv_only_ind >>
  strip_tac >- rw[bv_to_ov_def] >>
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

val v_to_Cv_ov = store_thm("v_to_Cv_ov",
  ``(∀m (v:α v) w s. (all_cns v ⊆ FDOM m) ∧ fmap_linv m w ==> (Cv_to_ov w s (v_to_Cv m v) = v_to_ov s v)) ∧
    (∀m (vs:α v list) w s. (BIGUNION (IMAGE all_cns (set vs)) ⊆ FDOM m) ∧ fmap_linv m w ==> (MAP (Cv_to_ov w s) (vs_to_Cvs m vs) = MAP (v_to_ov s) vs)) ∧
    (∀(m:string|->num) (env:α envE). T)``,
  ho_match_mp_tac v_to_Cv_ind >>
  rw[v_to_Cv_def] >> rw[Cv_to_ov_def] >>
  srw_tac[ETA_ss][fmap_linv_FAPPLY])

val labs_only_def = tDefine "labs_only"`
  (labs_only (CLitv _) = T) ∧
  (labs_only (CLoc _) = T) ∧
  (labs_only (CConv _ vs) = EVERY labs_only vs) ∧
  (labs_only (CRecClos env defs _) = EVERY labs_only env ∧ EVERY ISR defs)`
  (WF_REL_TAC`measure Cv_size` >>
   srw_tac[ARITH_ss][Cv1_size_thm] >>
   Q.ISPEC_THEN`Cv_size`imp_res_tac SUM_MAP_MEM_bound >>
   fsrw_tac[ARITH_ss][])
val _ = export_rewrites["labs_only_def"]

val _ = Parse.overload_on("mk_pp", ``λrd c bs.
  (rd
  ,c
  ,combin$C (bc_find_loc_aux bs.code bs.inst_length) 0
  )``)

val good_rd_def = Define`
  good_rd c rd bs =
    FEVERY (λ(p,(env,defs,j)).
      p ∈ FDOM bs.refs ∧
      p ∉ set rd.sm ∧
      Cv_bv (mk_pp rd c bs) (CRecClos env defs j) (bs.refs ' p))
    rd.cls`

val Cv_bv_syneq = store_thm("Cv_bv_syneq",
  ``(∀v1 bv. Cv_bv pp v1 bv ⇒ ∀v2. syneq (FST(SND pp)) v1 v2 ⇒ Cv_bv pp v2 bv) ∧
    (∀bvs cd env1 defs1. benv_bvs pp bvs cd env1 defs1 ⇒
      ∀env2 defs2 V U.
        syneq_defs (FST(SND pp)) (LENGTH env1) (LENGTH env2) V defs1 defs2 U ∧ U cd.ix cd.ix ∧
        (∀v1 v2. V v1 v2 ⇒ v1 < LENGTH env1 ∧ v2 < LENGTH env2 ∧ syneq (FST(SND pp)) (EL v1 env1) (EL v2 env2)) ∧
        (cd.nz = LENGTH defs1) ∧ (cd.ez = LENGTH env1) ∧
        cd.ix < LENGTH defs1 ∧ ISR (EL cd.ix defs1) ∧ (FLOOKUP (FST(SND pp)) (OUTR (EL cd.ix defs1)) = SOME cd)
        ⇒ benv_bvs pp bvs cd env2 defs2)``,
  ho_match_mp_tac (theorem"Cv_bv_strongind") >>
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
    rw[el_check_def,FLOOKUP_DEF] >>
    rator_x_assum`syneq`mp_tac >>
    simp[Once syneq_cases] >> rw[] >>
    simp[Once Cv_bv_cases,el_check_def,FLOOKUP_DEF] >>
    qexists_tac`l` >> simp[] >>
    rator_assum`syneq_defs`mp_tac >>
    simp_tac(srw_ss())[Once syneq_exp_cases,EVERY_MEM] >>
    simp_tac(srw_ss()++QUANT_INST_ss[sum_qp])[] >>
    simp[] >> strip_tac >>
    first_x_assum(qspecl_then[`(c ' l).ix`,`d2`]mp_tac) >>
    simp[] >> strip_tac >>
    conj_asm1_tac >-
      rev_full_simp_tac(srw_ss()++SATISFY_ss)[] >>
    BasicProvers.VAR_EQ_TAC >>
    rev_full_simp_tac(srw_ss()++SATISFY_ss)[] >>
    first_x_assum match_mp_tac >>
    HINT_EXISTS_TAC >>
    HINT_EXISTS_TAC >>
    srw_tac[SATISFY_ss][] ) >>
  rw[] >>
  simp[Once Cv_bv_cases] >>
  rator_assum`syneq_defs`mp_tac >>
  simp_tac(srw_ss())[Once syneq_exp_cases,EVERY_MEM] >>
  strip_tac >>
  first_x_assum(qspecl_then[`cd.ix`,`cd.ix`]mp_tac) >>
  simp[] >>
  Cases_on`EL cd.ix defs1`>>fs[] >>
  qmatch_assum_rename_tac`EL cd.ix defs1 = INR l`[] >>
  strip_tac >>
  ntac 2 (qpat_assum`X = Y`mp_tac) >>
  fs[FLOOKUP_DEF] >>
  simp[syneq_cb_aux_def,EVERY_MEM,MEM_EL] >>
  fsrw_tac[SATISFY_ss][GSYM LEFT_FORALL_IMP_THM] >>
  strip_tac >> fs[] >> strip_tac >> fs[] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  conj_tac >- (
    gen_tac >> strip_tac >>
    last_x_assum(qspec_then`i`mp_tac) >>
    simp[] >> strip_tac >>
    HINT_EXISTS_TAC >> simp[] >>
    qsuff_tac`syneq c (CRecClos env1 defs1 (EL i recs)) (CRecClos env2 defs2 (EL i recs))`
      >- metis_tac[syneq_trans] >>
    simp[Once syneq_cases] >>
    HINT_EXISTS_TAC >>
    qexists_tac`U` >>
    simp[] >> conj_tac >- metis_tac[] >>
    disj1_tac >>
    first_x_assum match_mp_tac >>
    simp[MEM_EL] >> metis_tac[] ) >>
  gen_tac >> strip_tac >>
  qpat_assum`∀i. i < LENGTH envs ⇒ P ∧ Q`(qspec_then`i`mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum match_mp_tac >>
  fsrw_tac[DNF_ss][] >>
  first_x_assum match_mp_tac >>
  first_x_assum match_mp_tac >>
  simp[MEM_EL] >> metis_tac[])

(*
val syneq_exp_relates_same_vars = store_thm("syneq_exp_relates_same_vars",
  ``(∀c z z2 V e e2. syneq_exp c z z2 V e e2 ⇒ (z2 = z) ∧ (e2 = e) ⇒ ∀v. v ∈ free_vars e ∧ v < z ⇒ V v v) ∧
    (∀c z z2 V defs defs2 U. syneq_defs c z z2 V defs defs2 U ⇒
      (z2 = z) ∧ (defs2 = defs) ∧ (∀n. n < LENGTH defs ∧ n ∈ BIGUNION (IMAGE cbod_fvs (set defs)) ⇒ U n n) ⇒
      ∀n. n < LENGTH defs ⇒
        ∀v. v ∈ cbod_fvs (EL n defs) ∧ v < z + LENGTH defs ∧ LENGTH defs ≤ v ⇒ V (v-LENGTH defs) (v-LENGTH defs))``,
  ho_match_mp_tac syneq_exp_ind >>
  strip_tac >- (
    simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,MEM_MAP,EXISTS_PROD] >>
    srw_tac[DNF_ss][MEM_EL] >>
    first_x_assum(qspec_then`n`mp_tac) >>
    simp[EL_MAP] >> qpat_assum`X = Y`(assume_tac o SYM) >> simp[]) >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[PRE_SUB1] >>
    rw[] >- metis_tac[] >>
    first_x_assum(qspec_then`x`mp_tac) >>
    simp[] ) >>
  strip_tac >- (
    simp[] >>
    metis_tac[NOT_LESS] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[FOLDL_UNION_BIGUNION,EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    cheat ) >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[PRE_SUB1] >>
    rw[] >- metis_tac[] >>
    first_x_assum(qspec_then`x`mp_tac) >>
    simp[] ) >>
  strip_tac >- (
    simp[FOLDL_UNION_BIGUNION] >>
    rw[] >- (
      first_x_assum (qspec_then`m`mp_tac) >>
      simp[] ) >>
    fs[] >>
    last_x_assum (qspec_then`m`mp_tac) >>
    simp[] >> disch_then match_mp_tac >>
    srw_tac[DNF_ss,SATISFY_ss][] ) >>
  strip_tac >- (
    simp[PRE_SUB1] >>
    rw[] >> fsrw_tac[ARITH_ss][] >>
    PROVE_TAC[] ) >>
  strip_tac >- cheat >>
  strip_tac >- cheat >>
  strip_tac >- cheat >>
  strip_tac >- cheat >>
  strip_tac >- cheat >>
  strip_tac >- (
    simp[] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    rpt gen_tac >> strip_tac >>
    strip_tac >>
    rw[] >- (
    syneq_exp_rules

val syneq_exp_Cv_bv = store_thm("syneq_exp_Cv_bv",
  ``(∀c z z2 V e e2. syneq_exp c z z2 V e e2 ⇒ (z2 = z) ∧ (e2 = e) ∧ (body_count e = 0) ⇒ ∀v. v ∈ free_vars e ∧ v < z ⇒ V v v) ∧
    (∀c z1 z2 V defs1 defs2 U. syneq_defs c z1 z2 V defs1 defs2 U ⇒
      ∀pp env1 d1 env2 d2 bv.
        (FST (SND pp) = c) ∧ Cv_bv pp (CRecClos env1 defs1 d1) bv ∧
        U d1 d2 ∧ d1 < LENGTH defs1 ∧ d2 < LENGTH defs2 ∧ (z1 = LENGTH env1) ∧ (z2 = LENGTH env2) ∧
        (∀v1 v2. V v1 v2 ⇒ v1 < LENGTH env1 ∧ v2 < LENGTH env2 ∧ syneq c (EL v1 env1) (EL v2 env2))
        ⇒
        Cv_bv pp (CRecClos env2 defs2 d2) bv)``,
  ho_match_mp_tac syneq_exp_ind >>
  strip_tac >- (
    simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,MEM_MAP,EXISTS_PROD] >>
    srw_tac[DNF_ss][MEM_EL] >>
    first_x_assum(qspec_then`n`mp_tac) >>
    simp[EL_MAP] >> qpat_assum`X = Y`(assume_tac o SYM) >> simp[]) >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[PRE_SUB1] >>
    rw[] >- metis_tac[] >> fs[] >>
    first_x_assum(qspec_then`x`mp_tac) >>
    simp[] ) >>
  strip_tac >- (
    simp[] >>
    metis_tac[NOT_LESS] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[FOLDL_UNION_BIGUNION,EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    srw_tac[DNF_ss][] >> fsrw_tac[DNF_ss][MEM_ZIP,MEM_EL,SUM_eq_0] >>
    metis_tac[EL_MAP]) >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[PRE_SUB1] >>
    rw[] >- metis_tac[] >> fs[] >>
    first_x_assum(qspec_then`x`mp_tac) >>
    simp[] ) >>
  strip_tac >- (
    simp[FOLDL_UNION_BIGUNION] >>
    rw[] >- (
      fs[] >>
      first_x_assum (qspec_then`m`mp_tac) >>
      simp[] ) >>
    Cases_on`cb`>>fs[SUM_eq_0,MEM_MAP]>>
    fsrw_tac[DNF_ss][] >> res_tac >>
    PairCases_on`x`>>fs[] ) >>
  strip_tac >- (
    simp[PRE_SUB1] >>
    rw[] >> fsrw_tac[ARITH_ss][] >>
    Cases_on`OUTL cb1`>>fs[]>>
    Cases_on`cb1`>>fs[]) >>
  strip_tac >- cheat >>
  strip_tac >- cheat >>
  strip_tac >- cheat >>
  strip_tac >- cheat >>
  strip_tac >- cheat >>
  simp[] >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rator_x_assum`Cv_bv`mp_tac >>
  simp[Once Cv_bv_cases,el_check_def,FLOOKUP_DEF] >>
  disch_then strip_assume_tac >> rw[] >>
  simp[Once Cv_bv_cases,el_check_def,FLOOKUP_DEF] >>
  `EL d2 defs2 = INR l` by PROVE_TAC[] >> simp[] >>
  fs[EVERY_MEM,RIGHT_FORALL_IMP_THM] >>
  full_simp_tac(srw_ss()++QUANT_INST_ss[sum_qp])[] >>
  rator_x_assum`benv_bvs`mp_tac >>
  simp[Once Cv_bv_cases] >>
  disch_then strip_assume_tac >> rw[] >>
  simp[Once Cv_bv_cases] >>
  map_every qexists_tac[`envs`,`recs`] >>
  simp[] >>
  last_x_assum(qspecl_then[`d1`,`d2`]mp_tac) >>
  simp[] >>
  `(LENGTH defs2 = LENGTH defs1) ∧ (LENGTH env2 = LENGTH env1)` by
    metis_tac[MEM_EL] >>
  simp[] >>
  qpat_assum`X = Y.ceenv`(assume_tac o SYM) >>
  simp[syneq_cb_aux_def,EVERY_MEM,MEM_EL]

val syneq_Cv_bv = store_thm("syneq_Cv_bv",
  ``∀c v1 v2. syneq c v1 v2 ⇒
    ∀pp bv. (FST(SND pp) = c) ∧ Cv_bv pp v1 bv ⇒ Cv_bv pp v2 bv``,
  ho_match_mp_tac CompileTheory.syneq_strongind >>
  strip_tac >- (
    simp[Once Cv_bv_cases] >>
    simp[Once Cv_bv_cases] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once Cv_bv_cases] >>
    simp[Once Cv_bv_cases] >>
    rw[] >>
    fs[EVERY2_EVERY,EVERY_MEM,UNCURRY] >>
    rpt(qpat_assum`LENGTH X = Y`mp_tac) >>
    last_x_assum mp_tac >>
    ntac 3 strip_tac >>
    fsrw_tac[DNF_ss][MEM_ZIP,MEM_EL]) >>
  strip_tac >- (
    rpt gen_tac >> reverse strip_tac >- (
      simp[Once Cv_bv_cases] >>
      simp[Once Cv_bv_cases,SimpR``$==>``] >>
      simp[FORALL_PROD,el_check_def] ) >>
    (*
    `syneq c (CRecClos env1 defs1 d1) (CRecClos env2 defs2 d2)` by (
      simp[Once syneq_cases] >> metis_tac[] ) >>
    *)
    simp[Once Cv_bv_cases] >>
    simp[el_check_def] >> rw[] >>
    rator_x_assum`syneq_defs`mp_tac >>
    simp[Once syneq_exp_cases] >> strip_tac >>
    fs[EVERY_MEM] >>
    full_simp_tac(srw_ss()++QUANT_INST_ss[])[] >>
    rfs[] >> rw[] >>
    first_x_assum(qspecl_then[`d1`,`d2`]mp_tac) >>
    simp[] >> strip_tac >> rfs[] >>
    `MEM (INR l) defs1 ∧ MEM (INR l) defs2` by (rw[MEM_EL] >> PROVE_TAC[]) >>
    `∃envs recs. cd.ceenv = (recs,envs)` by (
      Cases_on`cd.ceenv`>>rw[] ) >>
    fs[FLOOKUP_DEF] >> rw[] >>
    ntac 2(qpat_assum`(X,Z) = Y`mp_tac) >>
    simp[syneq_cb_aux_def] >> strip_tac >>
    `b` by (
      simp[] >>
      rator_x_assum`benv_bvs`mp_tac >>
      simp[Once Cv_bv_cases] >>
      simp[EVERY_MEM,MEM_EL] >>
      metis_tac[] ) >>
    fs[] >> rw[] >> fs[] >> rw[] >>
    simp[Once Cv_bv_cases,el_check_def,FLOOKUP_DEF] >>
    rator_x_assum`benv_bvs`mp_tac >>
    simp[Once Cv_bv_cases] >>
    simp[Once Cv_bv_cases,SimpR``$==>``] >>
    strip_tac >> simp[] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      res_tac >> simp[] >>
      rator_x_assum`syneq`mp_tac >>
      simp[Once syneq_cases] >>
      simp[Once syneq_cases,SimpR``$==>``] >>
      rator_x_assum`syneq`mp_tac >>
      simp[Once syneq_cases] >>
      disch_then(qx_choosel_then[`V1`,`U1`]strip_assume_tac) >>
      disch_then(qx_choosel_then[`V2`,`U2`]strip_assume_tac) >>
      syneq_exp_trans
      syneq_exp_mono_V

    rfs[syneq_cb_aux_def,LET_THM,FLOOKUP_DEF] >> fs[]

    simp[] >>
    rfs[] >>
    rfs[syneq_cb_aux_def,FLOOKUP_DEF,LET_THM] >> fs[] >>
    rpt (BasicProvers.VAR_EQ_TAC) >> strip_tac >>
    fs[EVERY_MEM]

    reverse conj_tac >- (
      gen_tac >> strip_tac >>
      hb
    strip_tac

    map_every qexists_tac[`cd`,`l`] >>
    fs[]
    fs[EVERY_MEM,Once FORALL_PROD] >>
    pop_assum mp_tac >>
    simp[Once Cv_bv_cases] >>
    simp[Once Cv_bv_cases,SimpR``$==>``] >>
    Q.PAT_ABBREV_TAC`fvs = SET_TO_LIST (free_vars c' e)` >>
    Q.PAT_ABBREV_TAC`evs = FILTER X fvs` >>
    strip_tac >> fs[] >>
    qx_gen_tac`z` >> strip_tac >>
    first_x_assum(qspec_then`z`mp_tac) >>
    simp[] >> strip_tac >>
    Cases_on`find_index (EL z evs) ns 0` >> fs[] >- (
      fsrw_tac[DNF_ss][MEM_EL] >>
      first_x_assum(qspecl_then[`xs`,`INR l`,`EL z evs`,`if ns = [] then 0 else i`]mp_tac) >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        unabbrev_all_tac >>
        Cases_on`ns=[]`>>fs[] >>
        imp_res_tac find_index_LESS_LENGTH >>
        fs[] ) >>
      simp[] >>
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac[`P`,`Q`,`R`] >>
        `MEM (EL z evs) evs` by (rw[MEM_EL] >> PROVE_TAC[]) >>
        qabbrev_tac`zz = EL z evs` >>
        qunabbrev_tac`evs` >> fs[MEM_FILTER] >>
        `¬MEM zz ns` by (Q.ISPECL_THEN[`ns`,`zz`,`0`]strip_assume_tac find_index_MEM >> fs[]) >>
        fs[MEM_EL,Abbr`fvs`,FLOOKUP_DEF] >> rw[] >>
        metis_tac[free_vars_DOMSUB,SUBSET_DEF,IN_UNION] ) >>
      simp[] >>
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      simp[optionTheory.OPTREL_def,FLOOKUP_DEF] ) >>
    qho_match_abbrev_tac`fmap_rel R (ev jenv) (ev env2)` >>
    qsuff_tac `fmap_rel R (ev env1) (ev env2)` >- metis_tac[fmap_rel_syneq_trans,fmap_rel_syneq_sym] >>
    simp[fmap_rel_OPTREL_FLOOKUP] >>
    fsrw_tac[DNF_ss][MEM_EL,Abbr`ev`,fmap_rel_def,FDOM_DRESTRICT] >>
    qx_gen_tac`k` >>
    Cases_on`ns=[]`>>fs[find_index_def] >>
    srw_tac[DNF_ss][FLOOKUP_DRESTRICT,EXISTS_PROD] >> fs[optionTheory.OPTREL_def] >>
    fs[MEM_EL] >>
    qmatch_assum_rename_tac`(p1,p2) = EL n defs`[] >>
    first_x_assum(qspecl_then[`p1`,`p2`,`k`,`n`]mp_tac) >>
    rfs[] >> rw[] >> fs[]) >>
  simp[Once Cv_bv_cases] >> rw[])

set_trace"goalstack print goal at top"0
*)

val s_refs_def = Define`
  s_refs c rd s bs =
  good_rd c rd bs ∧
  (LENGTH rd.sm = LENGTH s) ∧
  EVERY (λp. p ∈ FDOM bs.refs) rd.sm ∧
  ALL_DISTINCT rd.sm ∧
  EVERY2 (Cv_bv (mk_pp rd c bs)) s (MAP (FAPPLY bs.refs) rd.sm)`

val Cenv_bs_def = Define`
  Cenv_bs c rd s Cenv (renv:ctenv) sz bs =
    (EVERY2
       (λCv b. case lookup_ct (FDOM rd.cls) sz bs.stack bs.refs b of NONE => F
             | SOME bv => Cv_bv (mk_pp rd c bs) Cv bv)
     Cenv renv) ∧
    s_refs c rd s bs`

val env_rs_def = Define`
  env_rs env rs c rd s bs =
    let Cenv = env_to_Cenv (cmap rs.contab) env in
    Cenv_bs c rd s Cenv rs.renv rs.rsz bs`

val compile_varref_thm = store_thm("compile_varref_thm",
  ``∀bs bc0 code bc1 cls sz cs b bv bs'.
      ((compile_varref sz cs b).out = REVERSE code ++ cs.out) ∧
      (bs.code = bc0 ++ code ++ bc1) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      (lookup_ct cls sz bs.stack bs.refs b = SOME bv) ∧
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
    qexists_tac `SUC (SUC (SUC ZERO))` >> rw[NRC] >>
    srw_tac[DNF_ss][ALT_ZERO] >>
    rw[bc_eval1_thm] >>
    rw[Once bc_eval1_def,Abbr`x`] >>
    srw_tac[DNF_ss][] >>
    rw[bc_eval_stack_def] >>
    Q.PAT_ABBREV_TAC `bs0 = bump_pc bs with stack := st` >>
    qunabbrev_tac`ls1` >>
    fs[] >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x;y;z] ++ bc1` >>
    `bc_fetch bs0 = SOME y` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac [`ls0++[x]`,`z::bc1`] >>
      rw[Abbr`bs0`,Abbr`y`,bump_pc_def] >>
      srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND,Abbr`x`] ) >>
    rw[Once bc_eval1_def,Abbr`y`] >>
    srw_tac[DNF_ss][] >>
    rw[bc_eval_stack_def,Abbr`bs0`] >>
    Q.PAT_ABBREV_TAC`bs0 = bump_pc X with stack := Y` >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x;y;z] ++ bc1` >>
    `bc_fetch bs0 = SOME z` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac [`ls0++[x;y]`,`bc1`] >>
      rw[Abbr`bs0`,bump_pc_def,Abbr`z`] >>
      srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND,Abbr`y`,Abbr`x`] ) >>
    rw[bc_eval_stack_def] >>
    rw[bc_eval1_def,Abbr`bs0`,bump_pc_def,Abbr`z`] >>
    fs[FLOOKUP_DEF] >>
    unabbrev_all_tac >>
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

val no_closures_Cv_bv_equal = store_thm("no_closures_Cv_bv_equal",
  ``∀pp cv bv. Cv_bv pp cv bv ⇒
      ∀cv' bv'. Cv_bv pp cv' bv' ∧
        no_closures cv ∧
        no_closures cv' ∧
        all_Clocs cv ⊆ count (LENGTH (FST pp).sm) ∧
        all_Clocs cv' ⊆ count (LENGTH (FST pp).sm) ∧
        ALL_DISTINCT (FST pp).sm
        ⇒ ((cv = cv') = (bv = bv'))``,
  gen_tac >> ho_match_mp_tac Cv_bv_only_ind >> rw[]
  >- (
    rw[EQ_IMP_THM] >> rw[] >>
    fs[Once Cv_bv_cases] )
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
    fs[EL_ALL_DISTINCT_EL_EQ]) >>
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

val prim2_to_bc_thm = store_thm("prim2_to_bc_thm",
  ``∀op v1 v2 v bs bc0 bc1 st bv1 bv2 pp.
    (bs.code = bc0 ++ [Stack (prim2_to_bc op)] ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (CevalPrim2 op v1 v2 = Rval v) ∧
    Cv_bv pp v1 bv1 ∧ Cv_bv pp v2 bv2 ∧
    (bs.stack = bv2::bv1::st) ∧
    all_Clocs v1 ⊆ count (LENGTH (FST pp).sm) ∧
    all_Clocs v2 ⊆ count (LENGTH (FST pp).sm) ∧
    ALL_DISTINCT (FST pp).sm
    ⇒ ∃bv.
      Cv_bv pp v bv ∧
      bc_next bs (bump_pc (bs with <|stack := bv::st|>))``,
  rw[] >>
  `bc_fetch bs = SOME (Stack (prim2_to_bc op))` by (
    match_mp_tac bc_fetch_next_addr >>
    map_every qexists_tac[`bc0`,`bc1`] >>
    rw[] ) >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  srw_tac[DNF_ss][] >>
  rw[bump_pc_with_stack] >>
  Cases_on `op` >>
  Cases_on `v1` >> TRY (Cases_on `l`) >>
  Cases_on `v2` >> TRY (Cases_on `l`) >>
  fs[] >> rw[] >> fs[Once Cv_bv_cases] >> rw[] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw[bc_eval_stack_def] >> fs[i0_def] >>
  TRY (Cases_on `b` >> rw[]) >>
  TRY (Cases_on `b'` >> rw[]) >>
  srw_tac[ARITH_ss][] >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  TRY (
    fsrw_tac[DNF_ss][EL_ALL_DISTINCT_EL_EQ,el_check_def] >>
    AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> AP_THM_TAC >>
    AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
    metis_tac[] ) >>
  Cases_on `m=m'` >> rw[] >>
  AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> AP_THM_TAC >>
  AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
  rw[LIST_EQ_REWRITE] >>
  rfs[MEM_ZIP] >>
  fsrw_tac[DNF_ss][MEM_EL] >>
  Cases_on `LENGTH bvs = LENGTH bvs'` >> rw[] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
  metis_tac[SIMP_RULE(srw_ss()++DNF_ss)[SUBSET_DEF]no_closures_Cv_bv_equal] )

val is_Label_prim1_to_bc = store_thm("is_Label_prim1_to_bc",
  ``∀uop. ¬is_Label (prim1_to_bc uop)``,
  Cases >> rw[])
val _ = export_rewrites["is_Label_prim1_to_bc"]

val bc_fetch_with_stack = store_thm("bc_fetch_with_stack",
  ``bc_fetch (s with stack := st) = bc_fetch s``,
  rw[bc_fetch_def])

val bc_fetch_with_refs = store_thm("bc_fetch_with_refs",
  ``bc_fetch (s with refs := st) = bc_fetch s``,
  rw[bc_fetch_def])

(* TODO: move *)
val IS_PREFIX_THM = store_thm("IS_PREFIX_THM",
 ``!l2 l1. IS_PREFIX l1 l2 = (LENGTH l2 <= LENGTH l1) /\ !n. n < LENGTH l2 ==> (EL n l2 = EL n l1)``,
 Induct THEN SRW_TAC[][IS_PREFIX] THEN
 Cases_on`l1`THEN SRW_TAC[][EQ_IMP_THM] THEN1 (
   Cases_on`n`THEN SRW_TAC[][EL_CONS] THEN
   FULL_SIMP_TAC(srw_ss()++ARITH_ss)[] )
 THEN1 (
   POP_ASSUM(Q.SPEC_THEN`0`MP_TAC)THEN SRW_TAC[][] )
 THEN1 (
   FIRST_X_ASSUM(Q.SPEC_THEN`SUC n`MP_TAC)THEN SRW_TAC[][] ))

val Cv_bv_SUBMAP = store_thm("Cv_bv_SUBMAP",
  ``∀pp.
    (∀v bv. Cv_bv pp v bv ⇒
      ∀rd c l2a pp' rd'.
        (pp = (rd,c,l2a)) ∧
        (pp' = (rd',c,l2a)) ∧
        (rd.sm ≼ rd'.sm) ∧ (rd.cls ⊑ rd'.cls) ∧
        (∀p. p ∈ FDOM rd.cls ∧ p ∉ set rd.sm ⇒ p ∉ set rd'.sm)
        ⇒
        Cv_bv pp' v bv) ∧
    (∀benv cd env defs. benv_bvs pp benv cd env defs ⇒
      ∀rd c l2a pp' rd'.
        (pp = (rd,c,l2a)) ∧
        (pp' = (rd',c,l2a)) ∧
        (rd.sm ≼ rd'.sm) ∧ (rd.cls ⊑ rd'.cls) ∧
        (∀p. p ∈ FDOM rd.cls ∧ p ∉ set rd.sm ⇒ p ∉ set rd'.sm)
        ⇒
        benv_bvs pp' benv cd env defs)``,
  gen_tac >> ho_match_mp_tac Cv_bv_ind >>
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
  strip_tac >- ( rw[] >> simp[Once Cv_bv_cases] >> metis_tac[] ) >>
  rpt gen_tac >> strip_tac >> fs[] >>
  rpt gen_tac >> strip_tac >>
  simp[Once Cv_bv_cases] >>
  Cases_on`cd.ceenv`>>simp[]>>fs[]>>simp[]>>
  simp[GSYM FORALL_AND_THM] >> gen_tac >>
  rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
  metis_tac[FLOOKUP_SUBMAP,ADD_SYM])

(* TODO: move *)

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

val s_refs_with_pc = store_thm("s_refs_with_pc",
  ``s_refs c rd s (bs with pc := p) = s_refs c rd s bs``,
  rw[s_refs_def,good_rd_def])

val s_refs_with_stack = store_thm("s_refs_with_stack",
  ``s_refs c rd s (bs with stack := p) = s_refs c rd s bs``,
  rw[s_refs_def,good_rd_def])

val with_same_refs = store_thm("with_same_refs",
  ``(x with refs := x.refs) = x``,
  rw[bc_state_component_equality])
val _ = export_rewrites["with_same_refs"]

val with_same_code = store_thm("with_same_code",
  ``(x with code := x.code) = x``,
  rw[bc_state_component_equality])
val _ = export_rewrites["with_same_code"]

val with_same_pc = store_thm("with_same_pc",
  ``(x with pc := x.pc) = x``,
  rw[bc_state_component_equality])
val _ = export_rewrites["with_same_pc"]

val with_same_stack = store_thm("with_same_stack",
  ``(x with stack := x.stack) = x``,
  rw[bc_state_component_equality])
val _ = export_rewrites["with_same_stack"]

val with_same_sm = store_thm("with_same_sm",
  ``rd with sm := rd.sm = rd``,
  rw[theorem"refs_data_component_equality"])
val _ = export_rewrites["with_same_sm"]

val prim1_to_bc_thm = store_thm("prim1_to_bc_thm",
  ``∀c rd op s v1 s' v bs bc0 bc1 bce st bv1.
    (bs.code = bc0 ++ [prim1_to_bc op] ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (CevalPrim1 op s v1 = (s', Rval v)) ∧
    Cv_bv (mk_pp rd c (bs with code := bce)) v1 bv1 ∧
    (bs.stack = bv1::st) ∧
    s_refs c rd s (bs with code := bce)
    ⇒ ∃bv rf sm'.
      let bs' = bs with <|stack := bv::st; refs := rf; pc := next_addr bs.inst_length (bc0 ++ [prim1_to_bc op])|> in
      let rd' = rd with sm := sm' in
      bc_next bs bs' ∧
      Cv_bv (mk_pp rd' c (bs' with <| code := bce |>)) v bv ∧
      s_refs c rd' s' (bs' with code := bce) ∧
      DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf (COMPL (set sm')) ∧
      rd.sm ≼ sm'``,
  simp[] >> rw[] >>
  `bc_fetch bs = SOME (prim1_to_bc op)` by (
    match_mp_tac bc_fetch_next_addr >>
    map_every qexists_tac[`bc0`,`bc1`] >>
    rw[] ) >>
  simp[bc_eval1_thm] >>
  Cases_on`op`>>simp[bc_eval1_def,bump_pc_def,bc_fetch_with_stack,bc_fetch_with_refs] >>
  fs[LET_THM] >- (
    simp[bc_state_component_equality] >>
    qmatch_assum_abbrev_tac`CLoc n = v` >>
    Q.PAT_ABBREV_TAC`bn = LEAST n. n ∉ X` >>
    qexists_tac`rd.sm ++ [bn]` >>
    qpat_assum`X = s'`(assume_tac o SYM) >>
    qpat_assum`X = v`(assume_tac o SYM) >>
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
        rw[FAPPLY_FUPDATE_THM] >- PROVE_TAC[] >>
        match_mp_tac(MP_CANON(GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
        qexists_tac`mk_pp rd c (bs with code := bce)` >>
        simp[] >>
        metis_tac[EVERY_MEM] ) >>
      fs[fmap_rel_def,f_o_f_DEF,GSYM SUBSET_INTER_ABSORPTION] >>
      conj_asm1_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF,FAPPLY_FUPDATE_THM,EXTENSION,EVERY_MEM] >>
        rw[] >> PROVE_TAC[] ) >>
      conj_tac >- (
        simp[ALL_DISTINCT_APPEND] >>
        fs[EVERY_MEM] >> PROVE_TAC[] ) >>
      match_mp_tac EVERY2_APPEND_suff >>
      simp[] >>
      conj_tac >- (
        fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
        qx_gen_tac`m`>>strip_tac >>
        qpat_assum`∀m. m < LENGTH rd.sm ⇒ Q`(qspec_then`m`mp_tac)>>
        simp[EL_MAP,FAPPLY_FUPDATE_THM] >> fs[MEM_EL] >>
        rw[] >- PROVE_TAC[] >>
        match_mp_tac(MP_CANON(GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
        qexists_tac`mk_pp rd c (bs with code := bce)` >>
        simp[] >>
        fs[good_rd_def,FEVERY_DEF,UNCURRY] >>
        metis_tac[] ) >>
      match_mp_tac(MP_CANON(GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
      qexists_tac`mk_pp rd c (bs with code := bce)` >>
      simp[] >>
      fs[good_rd_def,FEVERY_DEF,UNCURRY] >>
      metis_tac[] ) >>
    simp[SUBMAP_DEF,DRESTRICT_DEF] >>
    rw[] >> rw[] >> fs[IN_FRANGE,DOMSUB_FAPPLY_THM] >> rw[] >> PROVE_TAC[]) >>
  Cases_on`v1`>>fs[] >>
  Cases_on`el_check n s`>>fs[]>>
  fs[Q.SPEC`CLoc n`(CONJUNCT1(SPEC_ALL(Cv_bv_cases)))] >>
  rw[] >> simp[bc_state_component_equality] >>
  qexists_tac`rd.sm`>>
  simp[s_refs_with_stack,s_refs_with_pc,SUM_APPEND,FILTER_APPEND] >>
  fs[s_refs_def,good_rd_def] >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,el_check_def] >>
  conj_tac >- metis_tac[MEM_EL] >>
  first_x_assum match_mp_tac >>
  simp[MEM_ZIP] >>
  qexists_tac`n` >>
  simp[EL_MAP])

val compile_envref_next_label_inc = store_thm("compile_envref_next_label_inc",
  ``∀sz cs b. (compile_envref sz cs b).next_label = cs.next_label``,
  ntac 2 gen_tac >> Cases >> rw[])
val _ = export_rewrites["compile_envref_next_label_inc"]

val compile_varref_next_label_inc = store_thm("compile_varref_next_label_inc",
  ``∀sz cs b. (compile_varref sz cs b).next_label = cs.next_label``,
  ntac 2 gen_tac >> Cases >> rw[])
val _ = export_rewrites["compile_varref_next_label_inc"]

val compile_decl_next_label_inc = store_thm("compile_decl_next_label_inc",
  ``∀env a vs.(FST (compile_decl env a vs)).next_label = (FST a).next_label``,
  rw[compile_decl_def] >>
  SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``FOLDL``1"f"] >>
  qho_match_abbrev_tac`P (FOLDL f a vs)` >>
  match_mp_tac FOLDL_invariant >>
  fs[Abbr`P`] >>
  qx_gen_tac `x` >> PairCases_on`x` >>
  qx_gen_tac`y` >> PairCases_on`y` >>
  rw[Abbr`f`] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw[])
val _ = export_rewrites["compile_decl_next_label_inc"]

val lookup_ct_incsz = store_thm("lookup_ct_incsz",
  ``(lookup_ct cls (sz+1) (x::st) refs b =
     if (b = CTLet (sz+1)) then SOME x else
     lookup_ct cls sz st refs b)``,
  fs[GSYM ADD1] >>
  Cases_on `b` >> rw[] >>
  fsrw_tac[ARITH_ss][el_check_def] >>
  rw[SUB,GSYM ADD_SUC] >>
  fsrw_tac[ARITH_ss][] >>
  Cases_on`c`>>rw[el_check_def]>>
  fsrw_tac[ARITH_ss][EL_CONS,PRE_SUB1,ADD1])

val lookup_ct_imp_incsz = store_thm("lookup_ct_imp_incsz",
  ``(lookup_ct cls sz st refs b = SOME v) ⇒
    (lookup_ct cls (sz+1) (x::st) refs b = SOME v)``,
  fs[GSYM ADD1] >>
  Cases_on `b` >> rw[el_check_def] >>
  fsrw_tac[ARITH_ss][EL_CONS,PRE_SUB1,ADD1] >>
  Cases_on`c`>>rw[el_check_def] >>
  fsrw_tac[ARITH_ss][EL_CONS,PRE_SUB1,ADD1,el_check_def])

val lookup_ct_imp_incsz_many = store_thm("lookup_ct_imp_incsz_many",
  ``∀cls sz st refs b v st' sz' ls.
    (lookup_ct cls sz st refs b = SOME v) ∧
     sz ≤ sz' ∧ (st' = ls ++ st) ∧ (LENGTH ls = sz' - sz)
   ⇒ (lookup_ct cls sz' st' refs b = SOME v)``,
  Induct_on`sz' - sz` >- (
    rw[] >> `sz = sz'` by srw_tac[ARITH_ss][] >> fs[LENGTH_NIL] ) >>
  rw[] >> Cases_on`ls`>>fs[] >- fsrw_tac[ARITH_ss][] >>
  Cases_on`sz'`>>fs[ADD1] >>
  match_mp_tac lookup_ct_imp_incsz >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  qexists_tac`sz` >>
  fsrw_tac[ARITH_ss][])

val lookup_ct_change_refs = store_thm("lookup_ct_change_refs",
  ``∀cl cl' sz st rf rf' ct.
    (∀n vs p. (ct = CTEnv (CCRef n)) ∧ sz < LENGTH st ∧ (EL sz st = Block 0 vs) ∧ n < LENGTH vs ∧ (EL n vs = RefPtr p) ⇒
      (p ∈ cl = p ∈ cl') ∧ (p ∈ cl ⇒ (FLOOKUP rf' p = FLOOKUP rf p)))
    ⇒ (lookup_ct cl' sz st rf' ct = lookup_ct cl sz st rf ct)``,
  rw[LET_THM] >>
  Cases_on`ct`>>fs[] >> rw[] >>
  Cases_on`c`>>fs[el_check_def]>>
  Cases_on`EL sz st`>>fs[] >> rw[]>>fs[]>>
  BasicProvers.CASE_TAC>>fs[]>>
  BasicProvers.CASE_TAC>>fs[]>>
  BasicProvers.CASE_TAC>>fs[]>>
  BasicProvers.CASE_TAC>>fs[])

val compile_envref_append_out = store_thm("compile_envref_append_out",
  ``∀sz cs b. ∃bc. ((compile_envref sz cs b).out = bc ++ cs.out) ∧ (EVERY ($~ o is_Label) bc)``,
  ho_match_mp_tac compile_envref_ind >> rw[])

val compile_varref_append_out = store_thm("compile_varref_append_out",
  ``∀sz cs b. ∃bc. ((compile_varref sz cs b).out = bc ++ cs.out) ∧ (EVERY ($~ o is_Label) bc)``,
  ntac 2 gen_tac >> Cases >> rw[compile_envref_append_out])

val FOLDL_emit_ceref_thm = store_thm("FOLDL_emit_ceref_thm",
  ``∀ls z sz s.
      let (z',s') = FOLDL (emit_ceref z) (sz,s) ls in
      ∃code.
      (z' = sz + LENGTH ls) ∧
      (s'.out = REVERSE code ++ s.out) ∧
      EVERY ($~ o is_Label) code ∧ (s'.next_label = s.next_label) ∧
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
  simp[Once SWAP_REVERSE] >> rw[] >>
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
     EVERY ($~ o is_Label) code ∧ (s'.next_label = s.next_label) ∧
     ∀bs bc0 bc1 cls j.
       (bs.code = bc0 ++ code ++ bc1) ∧
       (bs.pc = next_addr bs.inst_length bc0) ∧
       EVERY (λn. n < LENGTH env0) ec ∧ j ≤ z ∧ j ≤ LENGTH bs.stack ∧
       EVERY (λn. IS_SOME (lookup_ct cls (z-j) (DROP j bs.stack) bs.refs (EL n env0))) ec
       ⇒
       bc_next^* bs (bs with <| stack := (REVERSE (MAP (λn. THE (lookup_ct cls (z-j) (DROP j bs.stack) bs.refs (EL n env0))) ec))++bs.stack
                              ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  Induct >- (
    rw[Once SWAP_REVERSE,LET_THM] >>
    rpt (first_x_assum (mp_tac o SYM)) >> rw[]) >>
  qx_gen_tac`e` >> rw[] >>
  qmatch_assum_abbrev_tac`FOLDL (emit_ceenv env0) (z + 1, s1) ec = X` >>
  first_x_assum(qspecl_then[`env0`,`z+1`,`s1`]mp_tac) >>
  simp[Abbr`X`,Abbr`s1`] >>
  disch_then(Q.X_CHOOSE_THEN`bc`strip_assume_tac) >> rw[] >>
  qspecl_then[`z`,`s`,`EL e env0`]mp_tac compile_varref_append_out >>
  disch_then(Q.X_CHOOSE_THEN`bcv`strip_assume_tac) >> rw[] >>
  simp[Once SWAP_REVERSE] >> rw[EVERY_REVERSE] >>
  Cases_on`lookup_ct cls (z-j) (DROP j bs.stack) bs.refs (EL e env0)`>>fs[] >>
  `lookup_ct cls z bs.stack bs.refs (EL e env0) = SOME x` by (
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
      EVERY ($~ o is_Label) code ∧ (s'.next_label = s.next_label) ∧
      (k' = k + 1) ∧
      ∀bs bc0 bc1 cls.
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        k < LENGTH bs.stack ∧ nk + nk ≤ LENGTH bs.stack ∧
        EVERY (λn. nk + n < LENGTH bs.stack) refs ∧
        EVERY (λn. n < LENGTH env0) envs ∧
        EVERY (λn. IS_SOME (lookup_ct cls sz (DROP (nk+nk) bs.stack) bs.refs (EL n env0))) envs
        ⇒
        bc_next^* bs (bs with <| stack :=
          LUPDATE
          (Block closure_tag
            [EL k bs.stack;
             Block 0 (MAP (λn. EL (nk+n) bs.stack) refs ++
                      MAP (λn. THE (lookup_ct cls sz (DROP (nk+nk) bs.stack) bs.refs (EL n env0))) envs)])
          k bs.stack
                               ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  simp[cons_closure_def,UNCURRY] >> rpt gen_tac >>
  Q.PAT_ABBREV_TAC`s0 = s with out := X` >>
  qspecl_then[`refs`,`nk+sz`,`2 * nk + (sz + 1)`,`s0`]mp_tac FOLDL_emit_ceref_thm >>
  simp[UNCURRY] >>
  disch_then(Q.X_CHOOSE_THEN`bc`strip_assume_tac) >>
  Q.PAT_ABBREV_TAC`s1 = FOLDL (emit_ceref Y) X refs` >>
  qspecl_then[`envs`,`env0`,`FST s1`,`SND s1`]mp_tac FOLDL_emit_ceenv_thm >>
  simp[UNCURRY] >>
  disch_then(Q.X_CHOOSE_THEN`bc1`strip_assume_tac) >>
  fs[Abbr`s1`,Abbr`s0`,Once SWAP_REVERSE] >>
  rpt (qpat_assum `X = Y.next_label` kall_tac) >>
  qpat_assum`FST X = Y`kall_tac >>
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
    let s' = num_fold (λs. s with out := Ref::Stack (PushInt x)::s.out) s nz in
    ∃code.
    (s'.out = REVERSE code ++ s.out) ∧
    EVERY ($~ o is_Label) code ∧
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
              ; refs := bs.refs |++ REVERSE (MAP (λp. (p,Number x)) ps)
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
  `bc_fetch bs1 = SOME Ref` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0++[Stack (PushInt x)]`>>rw[Abbr`bs1`] >>
    simp[SUM_APPEND,FILTER_APPEND]) >>
  rw[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def,Abbr`bs1`,LET_THM,Abbr`P`] >>
  qho_match_abbrev_tac`∃ps. P0 ps ∧ bc_next^* bs1 (bs2 ps)` >>
  first_x_assum(qspecl_then[`bs1`,`bc0 ++ [Stack (PushInt x);Ref]`,`bc1`]mp_tac) >>
  simp[Abbr`bs1`,SUM_APPEND,FILTER_APPEND] >>
  disch_then(Q.X_CHOOSE_THEN`ps`strip_assume_tac) >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs3` >>
  qabbrev_tac`pps = ps ++ [LEAST n. n ∉ FDOM bs.refs]` >>
  qexists_tac`pps` >>
  `bs3 = bs2 pps` by (
    simp[Abbr`bs3`,Abbr`bs2`,bc_state_component_equality,FILTER_APPEND,SUM_APPEND,Abbr`pps`] >>
    simp[REVERSE_APPEND,FUPDATE_LIST_THM] ) >>
  fs[Abbr`P0`] >>
  simp[Abbr`pps`,ALL_DISTINCT_APPEND] >> rw[] >> fs[] >>
  numLib.LEAST_ELIM_TAC >> simp[] >>
  metis_tac[NOT_IN_FINITE,FDOM_FINITE,INFINITE_NUM_UNIV])

val FOLDL_push_lab_thm = store_thm("FOLDL_push_lab_thm",
 ``∀defs d s ls s' ls'.
   (FOLDL (push_lab d) (s,ls) defs = (s',ls'))
   ⇒
   ∃code.
   (s'.out = REVERSE code ++ s.out) ∧
   EVERY ($~ o is_Label) code ∧
   (s'.next_label = s.next_label) ∧
   ∀bs bc0 bc1.
     (bs.code = bc0 ++ code ++ bc1) ∧
     (bs.pc = next_addr bs.inst_length bc0) ∧
     EVERY ISR defs ∧
     EVERY (IS_SOME o bc_find_loc bs o Lab o OUTR) defs
     ⇒
     (ls' = (REVERSE (MAP (closure_data_ceenv o FAPPLY d o OUTR) defs)) ++ ls) ∧
     bc_next^* bs (bs with <| stack :=  (REVERSE (MAP (CodePtr o THE o bc_find_loc bs o Lab o OUTR) defs))++bs.stack
                            ; pc := next_addr bs.inst_length (bc0 ++ code) |>)``,
  Induct >- (
    rw[Once SWAP_REVERSE] >>
    pop_assum(assume_tac o SYM) >> fs[] ) >>
  qx_gen_tac`cb` >>
  Cases_on`cb` >> rw[push_lab_def] >>
  fs[] >- metis_tac[] >>
  qmatch_assum_abbrev_tac`FOLDL (push_lab d) (ss,lss) defs = (s',ls')` >>
  first_x_assum(qspecl_then[`d`,`ss`,`lss`,`s'`,`ls'`]mp_tac) >> simp[] >>
  strip_tac >> fs[Abbr`ss`,Once SWAP_REVERSE,Abbr`lss`] >>
  rpt gen_tac >> strip_tac >>
  `bc_fetch bs = SOME (PushPtr (Lab y))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0`>>rw[] ) >>
  simp[Once RTC_CASES1] >>
  simp_tac (srw_ss()++DNF_ss)[] >> disj2_tac >>
  rw[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
  Cases_on`bc_find_loc bs (Lab y)`>>fs[] >>
  qmatch_abbrev_tac`P ∧ bc_next^* bs1 bs2` >>
  first_x_assum(qspecl_then[`bs1`,`bc0 ++ [PushPtr (Lab y)]`,`bc1`]mp_tac) >>
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
    EVERY ($~ o is_Label) code ∧ (s'.next_label = s.next_label) ∧
    (k' = k + LENGTH ecs) ∧
    ∀bs bc0 bc1 cls.
    (bs.code = bc0 ++ code ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (LENGTH ecs = nk - k) ∧ k ≤ nk ∧ nk + nk ≤ LENGTH bs.stack ∧
    EVERY (λ(recs,envs).
      EVERY (λn. n < LENGTH env0) envs ∧
      EVERY (λn. IS_SOME (lookup_ct cls sz (DROP (nk + nk) bs.stack) bs.refs (EL n env0))) envs ∧
      EVERY (λn. nk + n < LENGTH bs.stack) recs) ecs
    ⇒
    let bvs = MAP2 (λp (recs,envs). Block closure_tag [p;
        Block 0
          (MAP (λn. EL (nk + n) bs.stack) recs ++
           MAP (λn. THE (lookup_ct cls sz (DROP (nk + nk) bs.stack) bs.refs (EL n env0))) envs)])
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
    (s'.next_label = s.next_label) ∧
    (k' = k + nz) ∧
    ∀bs bc0 bc1 vs rs st.
    (bs.code = bc0 ++ code ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (bs.stack = vs ++ (MAP RefPtr rs) ++ st) ∧
    (∀r. MEM r rs ⇒ r ∈ FDOM bs.refs) ∧ ALL_DISTINCT rs ∧
    (LENGTH rs = nk) ∧ (LENGTH vs = nk) ∧
    (k + nz = nk)
    ⇒
    bc_next^* bs
    (bs with <| refs := bs.refs |++ ZIP (DROP k rs,DROP k vs)
              ; pc := next_addr bs.inst_length (bc0 ++ code)|>)``,
  Induct >- (
    rw[Once num_fold_def,Once SWAP_REVERSE,LENGTH_NIL,FUPDATE_LIST_THM] >>
    rw[] >> fsrw_tac[ARITH_ss][FUPDATE_LIST_THM] >>
    metis_tac[DROP_LENGTH_NIL,ZIP,FUPDATE_LIST_THM,with_same_pc,with_same_refs,RTC_CASES1,MAP2]) >>
  rw[Once num_fold_def,update_refptr_def] >>
  first_x_assum(qspecl_then[`nk`,`s'''`,`k+1`]mp_tac) >>
  simp[] >> unabbrev_all_tac >> simp[] >>
  disch_then strip_assume_tac >>
  simp[Once SWAP_REVERSE] >>
  ntac 3 strip_tac >>
  map_every qx_gen_tac[`vvs`,`rrs`] >> rpt strip_tac >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ ls ++ code ++ bc1` >>
  qpat_assum`X = (s'''',k')`kall_tac >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  qmatch_assum_abbrev_tac`Abbrev (ls = [x1;x2;x3])` >>
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
  simp[EL_MAP] >>
  conj_asm1_tac >- (
    first_x_assum match_mp_tac >>
    simp[MEM_EL] >>
    qexists_tac`k` >>
    simp[] ) >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  first_x_assum(qspecl_then[`bs1`,`bc0 ++ ls`,`bc1`,`vvs`,`rrs`,`st`]mp_tac) >>
  simp[Abbr`bs1`,Abbr`ls`,FILTER_APPEND,SUM_APPEND,ADD1] >>
  qmatch_abbrev_tac`bc_next^* bs3 bs4 ⇒ bc_next^* bs3 bs2` >>
  qsuff_tac `bs4 = bs2` >- rw[] >>
  unabbrev_all_tac >>
  simp[bc_state_component_equality,FILTER_APPEND,SUM_APPEND] >>
  `DROP k rrs = EL k rrs :: DROP (k + 1) rrs` by (
     simp[GSYM ADD1,DROP_CONS_EL] ) >>
  `DROP k vvs = EL k vvs :: DROP (k + 1) vvs` by (
     simp[GSYM ADD1,DROP_CONS_EL] ) >>
  simp[FUPDATE_LIST_THM])

val num_fold_store_thm = store_thm("num_fold_store_thm",
  ``∀nz k s. let s' = num_fold (λs. s with out := Stack (Store k)::s.out) s nz in
    ∃code.
      (s'.out = REVERSE code ++ s.out) ∧
      (s'.next_label = s.next_label) ∧
      EVERY ($~ o is_Label) code ∧
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
  ``∀d env sz s defs.
    let s' = compile_closures d env sz s defs in
    ∃code.
      (s'.out = REVERSE code ++ s.out) ∧
      EVERY ($~ o is_Label) code ∧ (s'.next_label = s.next_label) ∧
      ∀bs bc0 bc1 cls.
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        EVERY ISR defs ∧
        EVERY (IS_SOME o bc_find_loc bs o Lab o OUTR) defs ∧
        EVERY ((λ(recs,envs).
          EVERY (λn. n < LENGTH env) envs ∧
          EVERY (λn. IS_SOME (lookup_ct cls sz bs.stack bs.refs (EL n env))) envs ∧
          EVERY (λn. n < LENGTH defs) recs)
               o closure_data_ceenv o FAPPLY d o OUTR) defs
        ⇒
        ∃bvs rs.
        let bvs = MAP
        ((λl. Block closure_tag
          [CodePtr (THE (bc_find_loc bs (Lab l)))
          ; let (recs,envs) = (d ' l).ceenv in
            Block 0 (MAP (λn. RefPtr (EL n rs)) recs ++
                     MAP (λn. THE (lookup_ct cls sz bs.stack bs.refs (EL n env))) envs)])
        o OUTR) defs in
        (LENGTH rs = LENGTH defs) ∧ ALL_DISTINCT rs ∧ (∀r. MEM r rs ⇒ r ∉ FDOM bs.refs) ∧
        bc_next^* bs
        (bs with <| stack := bvs++bs.stack
                  ; pc := next_addr bs.inst_length (bc0 ++ code)
                  ; refs := bs.refs |++ ZIP(rs,bvs)
                  |>)``,
  rw[compile_closures_def] >>
  qspecl_then[`i0`,`nk`,`s`]mp_tac num_fold_make_ref_thm >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`bmr`strip_assume_tac) >>
  qpat_assum`Abbrev (s' = X)`kall_tac >>
  qspecl_then[`REVERSE defs`,`d`,`s'`,`[]`,`s''`,`ecs`]mp_tac FOLDL_push_lab_thm >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`bpl`strip_assume_tac) >>
  qpat_assum`FOLDL (push_lab d) X Y = Z`kall_tac >>
  qspecl_then[`ecs`,`env`,`sz`,`nk`,`s''`,`0`]mp_tac FOLDL_cons_closure_thm >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`bcc`strip_assume_tac) >>
  qpat_assum`FOLDL X Y ecs = Z`kall_tac >>
  qspecl_then[`nk`,`nk`,`s'''`,`0`]mp_tac num_fold_update_refptr_thm >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`bur`strip_assume_tac) >>
  qspecl_then[`nk`,`k''`,`s''''`]mp_tac num_fold_store_thm >>
  simp[] >> disch_then(Q.X_CHOOSE_THEN`bsr`strip_assume_tac) >>
  simp[Once SWAP_REVERSE] >>
  rpt strip_tac >>
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
    qsuff_tac`lc = lookup_ct cls sz bs.stack bs.refs (EL n env)`>-rw[] >>
    simp[Abbr`lc`] >>
    Q.PAT_ABBREV_TAC`ls:bc_value list = DROP (2 * nk) st` >>
    `ls = bs.stack` by (
      lrw[Abbr`ls`,LIST_EQ_REWRITE,EL_DROP,EL_APPEND2] ) >>
    simp[] >>
    match_mp_tac lookup_ct_change_refs >>
    rw[] >>
    simp[FLOOKUP_DEF,FDOM_FUPDATE_LIST,MEM_MAP,EXISTS_PROD] >>
    `¬MEM p rs` by (
      `IS_SOME (lookup_ct cls sz bs.stack bs.refs (EL n env))` by (
        first_x_assum match_mp_tac >> rw[] ) >>
      pop_assum mp_tac >>
      qpat_assum`EL n env = X`SUBST1_TAC >>
      simp[el_check_def,FLOOKUP_DEF] >> rw[] >>
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
    simp[Abbr`vs`,Abbr`nk`,LENGTH_MAP2] ) >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs3 bs4` >>
  last_x_assum(qspecl_then[`bs4`,`bc0++bmr++bpl++bcc++bur`,`bc1`,`vs`,`MAP RefPtr rs`,`bs.stack`]mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`bs4`,Abbr`bs3`,Abbr`bs2`,Abbr`bs1`,Abbr`k''`,GSYM MAP_REVERSE,Abbr`nk`] >>
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
    simp[] >> rw[] >> fs[FLOOKUP_DEF] >>
    simp[FDOM_FUPDATE_LIST,MEM_MAP,EXISTS_PROD] >>
    `¬MEM p rs` by (
      fs[EVERY_MEM,UNCURRY] >>
      spose_not_then strip_assume_tac >>
      res_tac >> rfs[el_check_def,FLOOKUP_DEF] ) >>
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
  ``∀d env sz cs defs. (compile_closures d env sz cs defs).next_label = cs.next_label``,
  rpt gen_tac >>
  qspecl_then[`d`,`env`,`sz`,`cs`,`defs`]strip_assume_tac compile_closures_thm >>
  fs[LET_THM])
val _ = export_rewrites["compile_closures_next_label_inc"]

val compile_decl_append_out = store_thm("compile_decl_append_out",
  ``∀env a vs. ∃bc. ((FST (compile_decl env a vs)).out = bc ++ (FST a).out) ∧ (EVERY ($~ o is_Label) bc)``,
  rw[compile_decl_def] >>
  qho_match_abbrev_tac `∃bc. ((FST (FOLDL f a vs)).out = bc ++ (FST a).out) ∧ P bc` >>
  qsuff_tac `(λx. ∃bc. ((FST x).out = bc ++ (FST a).out) ∧ P bc) (FOLDL f a vs)` >- rw[] >>
  match_mp_tac FOLDL_invariant >> rw[Abbr`P`] >>
  PairCases_on `x` >> fs[] >>
  simp[Abbr`f`,UNCURRY] >>
  qspecl_then[`x1`,`x0`,`EL (FST y) env`]mp_tac compile_varref_append_out >>
  rw[] >> fs[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[])

val _ = Parse.overload_on("retbc",``λj k. [Stack (Pops (k + 1)); Stack (Load 1); Stack (Store (j + 2)); Stack (Pops (j + 1)); Return]``)
val _ = Parse.overload_on("jmpbc",``λn j k. [Stack (Load (n + k + 2)); Stack (Load (n + 1)); Stack (El 1); Stack (Load (n + 2)); Stack (El 0);
                                             Stack (Shift (n + 4) (k + j + 3)); JumpPtr]``)
val _ = Parse.overload_on("callbc",``λn. [Stack (Load n); Stack (El 1); Stack (Load (n + 1)); Stack (El 0); CallPtr]``)

val pushret_append_out = store_thm("pushret_append_out",
  ``∀t s. ∃bc. ((pushret t s).out = bc ++ s.out) ∧ EVERY ($~ o is_Label) bc ∧
   (∀j k. (t = TCTail j k) ⇒ ∃bc0. bc = REVERSE (retbc j k) ++ bc0)``,
  Cases >> rw[pushret_def])

val pushret_next_label = store_thm("pushret_next_label",
  ``∀t s. (pushret t s).next_label = s.next_label``,
  Cases >> rw[pushret_def])
val _ = export_rewrites["pushret_next_label"]

val zero_exists_lemma = store_thm("zero_exists_lemma", ``(∃m. n = m + n) ∧ (∃m. n = n + m)``, rw[]>>qexists_tac`0`>>rw[])

val compile_append_out = store_thm("compile_append_out",
  ``(∀d env t sz cs exp.
      ∃bc. ((compile d env t sz cs exp).out = bc ++ cs.out) ∧
           (∀j k. (t = TCTail j k) ⇒ ((∃m bc0. bc = REVERSE (retbc j (k+m)) ++ bc0) ∨
                                      (∃n m bc0. bc = REVERSE (jmpbc n j (k+m)) ++ bc0))) ∧
           cs.next_label ≤ (compile d env t sz cs exp).next_label ∧
           ALL_DISTINCT (FILTER is_Label bc) ∧
           EVERY (between cs.next_label (compile d env t sz cs exp).next_label) (MAP dest_Label (FILTER is_Label bc))) ∧
    (∀d env t sz exp n cs xs.
      ∃bc. ((compile_bindings d env t sz exp n cs xs).out = bc ++ cs.out) ∧
           (∀j k. (t = TCTail j k) ⇒ ((∃m bc0. bc = REVERSE (retbc j (k+m)) ++ bc0) ∨
                                      (∃n m bc0. bc = REVERSE (jmpbc n j (k+m)) ++ bc0))) ∧
           cs.next_label ≤ (compile_bindings d env t sz exp n cs xs).next_label ∧
           ALL_DISTINCT (FILTER is_Label bc) ∧
           EVERY (between cs.next_label (compile_bindings d env t sz exp n cs xs).next_label) (MAP dest_Label (FILTER is_Label bc))) ∧
    (∀d env sz cs exps.
      ∃bc. ((compile_nts d env sz cs exps).out = bc ++ cs.out) ∧
           cs.next_label ≤ (compile_nts d env sz cs exps).next_label ∧
           ALL_DISTINCT (FILTER is_Label bc) ∧
           EVERY (between cs.next_label (compile_nts d env sz cs exps).next_label) (MAP dest_Label (FILTER is_Label bc)))``,
  ho_match_mp_tac compile_ind >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >> simp[pushret_def,zero_exists_lemma] >>
    Q.PAT_ABBREV_TAC`p = compile_decl env X vs` >>
    PairCases_on `p` >> rw[] >>
    qmatch_assum_abbrev_tac`Abbrev(X = compile_decl env a vs)` >>
    Q.ISPECL_THEN[`env`,`a`,`vs`]mp_tac compile_decl_append_out >>
    Q.ISPECL_THEN[`env`,`a`,`vs`]mp_tac compile_decl_next_label_inc >>
    asm_simp_tac std_ss [FST,Abbr`X`,Abbr`a`] >>
    rw[] >> fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF]) >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[] >> rw[zero_exists_lemma]) >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[] >> rw[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[] >> rw[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[] >> rw[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def] >>
    qspecl_then[`sz`,`cs`,`EL vn env`]mp_tac compile_varref_append_out >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    rw[] >> fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    fs[FILTER_APPEND] >> rw[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def,LET_THM,UNCURRY] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[zero_exists_lemma] ) >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    fsrw_tac[ARITH_ss,ETA_ss,DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,EVERY_MEM,MEM_MAP,is_Label_rwt,between_def] >>
    rw[] >> fs[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
  strip_tac >- (
    simp[compile_def,LET_THM] >>
    rpt strip_tac >> fs[] >>
    Q.ISPECL_THEN[`d`,`env`,`sz`,`cs`,`defs`]mp_tac compile_closures_thm >>
    simp[] >> strip_tac >> fs[] >>
    pop_assum kall_tac >>
    simp[FILTER_APPEND,ALL_DISTINCT_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF,ALL_DISTINCT_REVERSE,FILTER_REVERSE,MAP_REVERSE,EVERY_REVERSE] >>
    fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[]) >>
  strip_tac >- (
    rw[compile_def] >>
    Q.ISPECL_THEN[`d`,`env`,`sz`,`cs`,`[cb]`]mp_tac compile_closures_thm >>
    simp[] >> strip_tac >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[LET_THM,GSYM FILTER_EQ_NIL,combinTheory.o_DEF,FILTER_APPEND,ALL_DISTINCT_REVERSE,FILTER_REVERSE] >> rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def,LET_THM,UNCURRY] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    srw_tac[ARITH_ss][] >>
    qexists_tac`0`>>rw[]) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >> fs[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >> rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >> fs[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
    rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >> fs[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
    rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    ntac 2 gen_tac >> Cases >> simp[compile_def] >> rw[] >> fs[] >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,MEM_MAP,between_def] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    fs[] >> rw[] >> fs[] >> qexists_tac`n+m`>>simp[]) >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  rw[compile_def] >> fs[] >>
  fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC)

val Cenv_bs_imp_incsz = store_thm("Cenv_bs_imp_incsz",
  ``∀c rd s env renv rsz bs bs'.
    Cenv_bs c rd s env renv rsz bs ∧
    (∃v p e. (bs' = bs with <| stack := v::bs.stack; pc := p; handler := e |>))
    ⇒
    Cenv_bs c rd s env renv (rsz+1) bs'``,
  rw[Cenv_bs_def,s_refs_def,good_rd_def] >> rw[] >> fs[] >>
  match_mp_tac(GEN_ALL(MP_CANON EVERY2_mono)) >>
  HINT_EXISTS_TAC >> simp[] >>
  rpt gen_tac >>
  BasicProvers.CASE_TAC >>
  imp_res_tac lookup_ct_imp_incsz >>
  simp[])

val Cenv_bs_imp_decsz = store_thm("Cenv_bs_imp_decsz",
  ``∀c rd s env renv rsz bs bs'.
    Cenv_bs c rd s env renv (rsz+1) bs ∧
      (CTLet (rsz+1) ∉ set renv) ∧
      (∃v p e. bs = bs' with <| stack := v::bs'.stack; pc := p; handler := e |>) ⇒
    Cenv_bs c rd s env renv rsz bs'``,
  rw[Cenv_bs_def,fmap_rel_def,s_refs_def,FDOM_DRESTRICT,good_rd_def] >> fs[] >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  rpt strip_tac >> res_tac >> pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  pop_assum mp_tac >>
  rw[lookup_ct_incsz] >>
  rfs[MEM_ZIP,MEM_EL] >>
  metis_tac[])

val Cenv_bs_CTLet_bound = store_thm("Cenv_bs_CTLet_bound",
  ``Cenv_bs c rd s env renv rsz bs ∧ MEM (CTLet n) renv ⇒ n ≤ rsz``,
  rw[Cenv_bs_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  rfs[MEM_ZIP,MEM_EL] >> fsrw_tac[DNF_ss][] >>
  qmatch_assum_rename_tac `z < LENGTH renv`[]>>
  first_x_assum (qspec_then `z` mp_tac) >>
  qpat_assum`CTLet n = X`(assume_tac o SYM) >>
  simp[el_check_def] >>
  srw_tac[ARITH_ss][])

val Cenv_bs_pops = store_thm("Cenv_bs_pops",
  ``∀vs c rd s env renv rsz bs bs'. Cenv_bs c rd s env renv (rsz + LENGTH vs) bs ∧
    (∀n. MEM (CTLet n) renv ⇒ n ≤ rsz) ∧
    (∃p e. bs = bs' with <| stack := vs ++ bs'.stack; pc := p; handler := e|>)
    ⇒ Cenv_bs c rd s env renv rsz bs'``,
  Induct >> rw[] >- ( fs[Cenv_bs_def,s_refs_def,good_rd_def] >> fs[]) >>
  first_x_assum match_mp_tac >>
  simp[bc_state_component_equality] >>
  qexists_tac`bs' with stack := vs ++ bs'.stack` >> rw[] >>
  match_mp_tac Cenv_bs_imp_decsz >>
  qmatch_assum_abbrev_tac`Cenv_bs c rd s env renv x y` >>
  qexists_tac`y` >>
  unabbrev_all_tac >>
  fsrw_tac[ARITH_ss][ADD1,bc_state_component_equality] >>
  spose_not_then strip_assume_tac >>
  res_tac >> fsrw_tac[ARITH_ss][] )

val Cenv_bs_with_pc = store_thm("Cenv_bs_with_pc",
  ``Cenv_bs c rd s env env0 sz0 (bs with pc := p) = Cenv_bs c rd s env env0 sz0 bs``,
  rw[Cenv_bs_def,s_refs_with_pc])

val Cv_bv_l2a_mono = store_thm("Cv_bv_l2a_mono",
  ``∀pp.
    (∀Cv bv. Cv_bv pp Cv bv ⇒ ∀pp' l2a.
     (∀x y. (SND (SND pp) x = SOME y) ⇒ (l2a x = SOME y))
     ∧ (pp' = (FST pp, FST(SND pp), l2a))
     ⇒ Cv_bv pp' Cv bv) ∧
    (∀benv fs env defs.
     benv_bvs pp benv fs env defs ⇒ ∀pp' l2a.
     (∀x y. (SND (SND pp) x = SOME y) ⇒ (l2a x = SOME y))
     ∧ (pp' = (FST pp, FST(SND pp), l2a))
     ⇒ benv_bvs pp' benv fs env defs)``,
  gen_tac >>
  PairCases_on `pp` >> simp[] >>
  ho_match_mp_tac Cv_bv_ind >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
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

val Cv_bv_l2a_mono_mp = MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_l2a_mono)))

val s_refs_append_code = store_thm("s_refs_append_code",
  ``∀c rd s bs bs' ls.
     s_refs c rd s bs ∧ (bs' = (bs with code := bs.code ++ ls))
    ⇒ s_refs c rd s bs'``,
  rw[s_refs_def,fmap_rel_def,good_rd_def,FEVERY_DEF,UNCURRY] >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >> rpt strip_tac >>
  res_tac >>
  match_mp_tac Cv_bv_l2a_mono_mp >>
  qexists_tac `mk_pp rd c bs` >>
  rw[] >> metis_tac[bc_find_loc_aux_append_code])

val Cenv_bs_append_code = store_thm("Cenv_bs_append_code",
  ``∀c rd s env env0 sz0 bs bs' ls.
    Cenv_bs c rd s env env0 sz0 bs ∧ (bs' = (bs with code := bs.code ++ ls)) ⇒
    Cenv_bs c rd s env env0 sz0 bs'``,
  reverse(rw[Cenv_bs_def]) >- PROVE_TAC[s_refs_append_code] >>
  fs[Cenv_bs_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,s_refs_def] >> rw[] >>
  res_tac >>
  BasicProvers.CASE_TAC >> fs[] >>
  match_mp_tac Cv_bv_l2a_mono_mp >>
  qexists_tac `mk_pp rd c bs` >>
  rw[] >> metis_tac[bc_find_loc_aux_append_code])

val Cenv_bs_FUPDATE = store_thm("Cenv_bs_FUPDATE",
  ``∀c rd s env env0 sz0 bs v bv bs'.
    Cenv_bs c rd s env env0 sz0 bs ∧
    Cv_bv (mk_pp rd c bs') v bv ∧
    (bs' = bs with stack := bv::bs.stack)
    ⇒
    Cenv_bs c rd s (v::env) ((CTLet (sz0 + 1))::env0) (sz0 + 1) bs'``,
  rw[Cenv_bs_def,s_refs_def] >> fs[el_check_def] >- (
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    rpt strip_tac >> res_tac >>
    pop_assum mp_tac >> BasicProvers.CASE_TAC >>
    imp_res_tac lookup_ct_imp_incsz >>
    simp[] ) >>
  fs[good_rd_def])

val Cenv_bs_FUPDATE_LIST = store_thm("Cenv_bs_FUPDATE_LIST",
  ``∀vs c rd s env cenv sz bs bs bvs bs' env' cenv' sz'.
  Cenv_bs c rd s env cenv sz bs ∧
  (bs' = bs with stack := bvs ++ bs.stack) ∧
  EVERY2 (Cv_bv (mk_pp rd c bs')) vs bvs ∧
  (env' = vs++env) ∧
  (cenv' = (REVERSE(GENLIST(λm. CTLet(sz+m+1))(LENGTH vs)))++cenv) ∧
  (sz' = sz + LENGTH vs)
  ⇒
  Cenv_bs c rd s env' cenv' sz' bs'``,
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

val Cenv_bs_DOMSUB = store_thm("Cenv_bs_DOMSUB",
  ``∀c rd s env renv rsz bs.
    Cenv_bs c rd s env renv rsz bs ∧ (env ≠ []) ∧ (renv ≠ []) ⇒
    Cenv_bs c rd s (TL env) (TL renv) rsz bs``,
  ntac 3 gen_tac >> Cases >> simp[] >> Cases >> simp[] >>
  rw[Cenv_bs_def,EVERY2_EVERY])

val Cenv_bs_change_store = store_thm("Cenv_bs_change_store",
  ``∀c rd s env renv rsz bs rd' s' bs' rfs'.
    Cenv_bs c rd s env renv rsz bs ∧
    s_refs c rd' s' bs' ∧
    (bs' = bs with refs := rfs') ∧
    DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rfs' (COMPL (set rd'.sm)) ∧
    rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls
    ⇒
    Cenv_bs c rd' s' env renv rsz bs'``,
  rw[Cenv_bs_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  res_tac >> pop_assum mp_tac >> BasicProvers.CASE_TAC >> strip_tac >>
  qho_match_abbrev_tac`case X of NONE => F | SOME Y => Z Y` >>
  qmatch_assum_abbrev_tac`X' = SOME x` >>
  `X = X'` by (
    unabbrev_all_tac >>
    match_mp_tac lookup_ct_change_refs >>
    rpt gen_tac >> strip_tac >>
    fs[s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY,el_check_def] >>
    fs[SUBMAP_DEF,FDOM_DRESTRICT,FLOOKUP_DEF,DRESTRICT_DEF] >>
    metis_tac[] ) >>
  simp[Abbr`Z`] >>
  match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
  HINT_EXISTS_TAC >>
  simp[] >>
  fs[s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY] >>
  fs[SUBMAP_DEF,SUBSET_DEF,DRESTRICT_DEF,IN_FRANGE] )

(*
val good_ecs_def = Define`
  good_ecs d ecs = FEVERY (λ(k,v).
  let (fvs,xs,ns,j) = FAPPLY d k in
  v = SND(ITSET(bind_fv ns xs (LENGTH xs) j) fvs (FEMPTY,0,[]))) ecs`
*)

val code_env_code_def = Define`
  code_env_code c code =
  ALL_DISTINCT (FILTER is_Label code) ∧
  FEVERY (λ(l,cd).
    ∃cs bc0 cc bc1.
      Cexp_pred cd.body ∧
      ((compile c (MAP CTEnv cd.ccenv) (TCTail cd.az 0) 0 cs cd.body).out = cc ++ cs.out) ∧
      EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc0) ∧ l < cs.next_label ∧
      (code = bc0 ++ Label l :: (REVERSE cc) ++ bc1)) c`

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

val code = ``jmpbc (LENGTH (args1 :bc_value list)) (LENGTH (args : bc_value list)) (LENGTH (vs : bc_value list))``
val jmpbc_thm = store_thm("jmpbc_thm",
  ``∀bs bc0 bc1 bv vs benv ret args cl ct x y args1 st bs'.
    (bs.stack = args1 ++ (Block ct [CodePtr x;y])::vs++benv::ret::args++cl::st) ∧
    (bs.code = bc0 ++ jmpbc (LENGTH args1) (LENGTH args) (LENGTH vs) ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (bs' = bs with <| stack := y::ret::args1++(Block ct [CodePtr x;y])::st; pc := x |>)
    ⇒ bc_next^* bs bs'``,
  rw[] >>
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
  qspecl_then[`bc0++(TAKE 5 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND,ADD1] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  simp[bc_eval_stack_def] >>
  lrw[TAKE_APPEND2,DROP_APPEND2,TAKE_APPEND1] >>
  rw[bump_pc_def] >>
  ntac 5 (pop_assum kall_tac) >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 6 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND,ADD1] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def,Abbr`bs2`] >>
  REWRITE_TAC[GSYM CONS_APPEND,GSYM APPEND_ASSOC] >>
  rw[])

(* TODO: move? *)
val option_case_NONE_F = store_thm("option_case_NONE_F",
  ``(case X of NONE => F | SOME x => P x) = (∃x. (X = SOME x) ∧ P x)``,
  Cases_on`X`>>rw[])

val code_for_push_def = Define`
  code_for_push rd bs bce bc0 code s s' c env vs renv rsz =
    ∃bvs rf rd'.
    let bs' = bs with <| stack := (REVERSE bvs)++bs.stack; pc := next_addr bs.inst_length (bc0 ++ code); refs := rf |> in
    bc_next^* bs bs' ∧
    EVERY2 (Cv_bv (mk_pp rd' c (bs' with code := bce))) vs bvs ∧
    Cenv_bs c rd' s' env renv (rsz+(LENGTH vs)) (bs' with code := bce) ∧
    DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf (COMPL (set rd'.sm)) ∧
    rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls`

val code_for_return_def = Define`
  code_for_return rd bs bce st ret v s s' c =
    ∃bv rf rd'.
    let bs' = bs with <| stack := bv::st; pc := ret; refs := rf |> in
    bc_next^* bs bs' ∧
    Cv_bv (mk_pp rd' c (bs' with code := bce)) v bv ∧
    s_refs c rd' s' (bs' with code := bce) ∧
    DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf (COMPL (set rd'.sm)) ∧
    rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls`

val code_for_push_return = store_thm("code_for_push_return",
  ``∀rd bs bce bc0 code s s' c env v renv rsz bc1 args args1 bs' blvs benv st cl cl1 ret.
    code_for_push rd bs bce bc0 code s s' c env [v] renv rsz ∧
    (bs.code = bc0 ++ code ++ retbc (LENGTH args) (LENGTH blvs) ++ bc1) ∧
    (bs.stack = blvs++benv::CodePtr ret::args++cl::st)
    ⇒
    code_for_return rd bs bce st ret v s s' c``,
    rw[code_for_push_def,code_for_return_def,LET_THM] >>
    qmatch_assum_rename_tac `Cv_bv pp v bv`["pp"] >>
    map_every qexists_tac [`bv`,`rf`,`rd'`] >>
    fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    qspecl_then[`bs0`,`bs1`,`retbc (LENGTH args) (LENGTH blvs) ++ bc1`]mp_tac (SIMP_RULE(srw_ss())[]RTC_bc_next_append_code) >>
    rw[] >>
    match_mp_tac (SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
    first_assum (exists_tac o rand o concl) >> fs[Abbr`bs0`] >>
    qpat_assum`bs.code = X`(assume_tac o SYM)>>fs[]>>
    match_mp_tac retbc_thm >>
    pop_assum(assume_tac o SYM) >>
    qexists_tac`bc0 ++ code` >> fs[Abbr`bs1`] >>
    qexists_tac`blvs`>>fs[]>>
    qexists_tac`args`>>fs[])

val compile_labels_lemma = store_thm("compile_labels_lemma",
  ``∀d env t sz cs exp bc0 cs1 cls1 code.
    (cs1 = compile d env t sz cs exp) ∧
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
  qspecl_then[`d`,`env`,`t`,`sz`,`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
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

(*
val bind_fv_thm = store_thm("bind_fv_thm",
  ``∀ns xs az i fvs acc env ecl ec. FINITE fvs ∧ (acc = (env,ecl,ec)) ∧ (ns ≠ [] ⇒ i < LENGTH ns) ∧ ALL_DISTINCT ns ⇒
    (ITSET (bind_fv ns xs az i) fvs acc =
     let fvl = SET_TO_LIST fvs in
     let envs = FILTER (λx. ¬MEM x xs ∧ ∀j. (find_index x ns 0 = SOME j) ⇒ j ≠ i) fvl in
     let ecs = MAP (λx. (x, case find_index x ns 0 of NONE => CEEnv x | SOME j => CERef (j + 1))) envs in
     let args = FILTER (λx. MEM x xs) fvl in
     let ls1 = ZIP (args, MAP (λfv. CTArg (2 + az - (THE (find_index fv xs 1)))) args) in
     let ls2 = GENLIST (λn. (FST(EL n ecs), (case SND(EL n ecs) of CEEnv _ => CTEnv | CERef _ => CTRef) (ecl + n))) (LENGTH ecs) in
     let env0 = env |++ ls1 |++ ls2 in
     (if ns ≠ [] ∧ EL i ns ∈ fvs ∧ EL i ns ∉ set xs then env0 |+ (EL i ns, CTArg (2 + az)) else env0
     ,ecl + LENGTH ecs
     ,(REVERSE (MAP SND ecs))++ec
     ))``,
  ntac 4 gen_tac >>
  Q.ISPEC_THEN`bind_fv ns xs az i`ho_match_mp_tac(Q.GEN`f`ITSET_IND) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> fs[] >>
  asm_simp_tac std_ss [Once ITSET_def] >>
  Cases_on`fvs = {}` >- rw[LET_THM,FUPDATE_LIST_THM] >>
  fs[bind_fv_def] >>
  Cases_on`find_index (CHOICE fvs) xs 1` >> fs[] >- (
    Cases_on`find_index (CHOICE fvs) ns 0` >> fs[] >- (
      asm_simp_tac std_ss [Once SET_TO_LIST_THM,SimpRHS] >>
      rw[] >>
      Q.ISPECL_THEN[`xs`,`CHOICE fvs`,`1`](strip_assume_tac o SYM) find_index_MEM >>
      Q.ISPECL_THEN[`xs`,`CHOICE fvs`,`0`](strip_assume_tac o SYM) find_index_MEM >>
      Q.ISPECL_THEN[`ns`,`CHOICE fvs`,`0`](strip_assume_tac o SYM) find_index_MEM >>
      reverse conj_asm2_tac >- (
        conj_tac >- (
          simp[Abbr`ecs`,Abbr`ecs'`,Abbr`envs`,Abbr`envs'`,Abbr`fvl`,Abbr`fvl'`] >>
          srw_tac[ARITH_ss][ADD1] >>
          rw[] >> fs[] >> rfs[] ) >>
        REWRITE_TAC[Once(GSYM REVERSE_DEF)] >>
        REWRITE_TAC[REVERSE_INV] >>
        simp[Abbr`ecs'`,Abbr`ecs`,Abbr`envs'`,Abbr`envs`,Abbr`fvl`,Abbr`fvl'`] >>
        rfs[] ) >>
      rfs[] >>
      `ns ≠ [] ⇒ (EL i ns ∈ REST fvs = EL i ns ∈ fvs)` by (
        rw[REST_DEF,EQ_IMP_THM] >>
        spose_not_then strip_assume_tac >> fs[] >>
        metis_tac[MEM_EL] ) >>
      fs[] >>
      qsuff_tac `env0 = env0'` >- (rw[] >> fs[]) >>
      `ecs = (CHOICE fvs, CEEnv (CHOICE fvs))::ecs'` by (
        match_mp_tac LIST_EQ_MAP_PAIR >>
        conj_tac >- (
          simp[Abbr`ecs`,Abbr`ecs'`,MAP_MAP_o,combinTheory.o_DEF,Abbr`envs`,Abbr`envs'`,Abbr`fvl`,Abbr`fvl'`] ) >>
        match_mp_tac (fst(EQ_IMP_RULE(SPEC_ALL REVERSE_INV))) >>
        asm_simp_tac std_ss [MAP,REVERSE_DEF] ) >>
      simp[Abbr`env0`,Abbr`env0'`,Abbr`ls1`,Abbr`ls1'`,Abbr`ls2`,Abbr`ls2'`] >>
      simp[GENLIST_CONS,combinTheory.o_DEF,ADD1,FUPDATE_LIST_THM] >>
      AP_THM_TAC >> AP_TERM_TAC >>
      simp[Abbr`args'`,Abbr`args`,Abbr`fvl`,Abbr`fvl'`] >>
      qmatch_abbrev_tac`(env |++ ls) |+ p = env |+ p |++ ls` >>
      Q.ISPECL_THEN[`p::ls`,`ls++[p]`,`env`]mp_tac FUPDATE_LIST_ALL_DISTINCT_PERM >>
      `ALL_DISTINCT (MAP FST (p::ls))` by (
        qsuff_tac `∃P. MAP FST (p::ls) = FILTER P (SET_TO_LIST fvs)`
          >- metis_tac[FILTER_ALL_DISTINCT,ALL_DISTINCT_SET_TO_LIST] >>
        simp[Once SET_TO_LIST_THM] >>
        rw[Abbr`p`,Abbr`ls`,MAP_ZIP] >>
        qexists_tac`λx. MEM x xs ∨ (x = CHOICE fvs)` >> rw[] >>
        simp[FILTER_EQ] >>
        simp[REST_DEF] ) >>
      simp[sortingTheory.PERM_CONS_EQ_APPEND,FUPDATE_LIST_THM,FUPDATE_LIST_APPEND] >>
      disch_then (match_mp_tac o GSYM) >>
      map_every qexists_tac [`ls`,`[]`] >>
      rw[] ) >>
    Cases_on `x = i` >> fs[] >- (
      asm_simp_tac std_ss [Once SET_TO_LIST_THM,SimpRHS] >>
      rw[] >>
      Q.ISPECL_THEN[`xs`,`CHOICE fvs`,`1`](strip_assume_tac o SYM) find_index_MEM >>
      Q.ISPECL_THEN[`xs`,`CHOICE fvs`,`0`](strip_assume_tac o SYM) find_index_MEM >>
      `ns ≠ []` by (Cases_on`ns`>>fs[find_index_def]) >> fs[] >>
      `EL i ns = CHOICE fvs` by (
        Q.ISPECL_THEN[`ns`,`CHOICE fvs`,`0`]mp_tac find_index_LEAST_EL >>
        simp[MEM_EL] >>
        rw[] >>
        numLib.LEAST_ELIM_TAC >>
        rw[] >> metis_tac[] ) >>
      fs[REST_DEF,CHOICE_DEF] >>
      reverse conj_asm2_tac >- (
        simp[Abbr`ecs`,Abbr`ecs'`,Abbr`envs`,Abbr`envs'`,Abbr`fvl`,Abbr`fvl'`] ) >>
      `ecs' = ecs` by (
        match_mp_tac LIST_EQ_MAP_PAIR >>
        conj_tac >- (
          simp[Abbr`ecs`,Abbr`ecs'`,MAP_MAP_o,combinTheory.o_DEF,Abbr`envs`,Abbr`envs'`,Abbr`fvl`,Abbr`fvl'`] ) >>
        rw[]) >>
      simp[Abbr`env0`,Abbr`env0'`,Abbr`ls1`,Abbr`ls2`,Abbr`ls1'`,Abbr`ls2'`,Abbr`args`,Abbr`args'`,Abbr`fvl`,Abbr`fvl'`] >>
      REWRITE_TAC[GSYM FUPDATE_LIST_APPEND] >>
      qmatch_abbrev_tac`env |+ p |++ ls = (env |++ ls) |+ p` >>
      Q.ISPECL_THEN[`p::ls`,`ls++[p]`,`env`]mp_tac FUPDATE_LIST_ALL_DISTINCT_PERM >>
      `ALL_DISTINCT (MAP FST (p::ls))` by (
        fs[GSYM REST_DEF] >> rfs[Abbr`p`] >>
        `MAP FST ls = FILTER (λx. MEM x xs) (SET_TO_LIST (REST fvs)) ++ FILTER (λx. ¬MEM x xs ∧ find_index x ns 0 ≠ SOME i) (SET_TO_LIST (REST fvs))` by (
          rw[Abbr`ls`,MAP_ZIP,MAP_GENLIST,combinTheory.o_DEF,Abbr`envs`,Abbr`envs'`] >>
          rw[LIST_EQ_REWRITE,Abbr`ecs`,EL_MAP] ) >>
        fs[Abbr`envs`,Abbr`envs'`,MEM_FILTER] >>
        simp[ALL_DISTINCT_APPEND,MEM_FILTER] >>
        metis_tac[FILTER_ALL_DISTINCT,ALL_DISTINCT_SET_TO_LIST,FINITE_REST] ) >>
      simp[sortingTheory.PERM_CONS_EQ_APPEND,FUPDATE_LIST_THM,FUPDATE_LIST_APPEND] >>
      disch_then match_mp_tac >>
      map_every qexists_tac [`ls`,`[]`] >>
      rw[] ) >>
    asm_simp_tac std_ss [Once SET_TO_LIST_THM,SimpRHS] >>
    rw[] >>
    Q.ISPECL_THEN[`xs`,`CHOICE fvs`,`1`](strip_assume_tac o SYM) find_index_MEM >>
    Q.ISPECL_THEN[`xs`,`CHOICE fvs`,`0`](strip_assume_tac o SYM) find_index_MEM >>
    `ns ≠ []` by (Cases_on`ns`>>fs[find_index_def]) >> fs[] >>
    `EL i ns ≠ CHOICE fvs` by (
      `x < LENGTH ns ∧ (EL x ns = CHOICE fvs)` by (
        Q.ISPECL_THEN[`ns`,`CHOICE fvs`,`0`]mp_tac find_index_LEAST_EL >>
        rw[MEM_EL] >- (
          numLib.LEAST_ELIM_TAC >>
          conj_tac >- metis_tac[] >>
          rw[] >>
          qmatch_rename_tac`m < LENGTH ns`[] >>
          Cases_on`n < m`>>res_tac>>fs[]>>
          DECIDE_TAC ) >>
        numLib.LEAST_ELIM_TAC >>
        metis_tac[] ) >>
      fs[EL_ALL_DISTINCT_EL_EQ] >>
      metis_tac[] ) >>
    `EL i ns ∈ REST fvs = EL i ns ∈ fvs` by (
      fs[REST_DEF] ) >>
    reverse conj_asm2_tac >- (
      conj_tac >- (
        simp[Abbr`ecs`,Abbr`ecs'`,Abbr`envs`,Abbr`envs'`,Abbr`fvl`,Abbr`fvl'`] >>
        srw_tac[ARITH_ss][ADD1] >>
        rw[] >> fs[] >> rfs[] ) >>
      REWRITE_TAC[Once(GSYM REVERSE_DEF)] >>
      REWRITE_TAC[REVERSE_INV] >>
      simp[Abbr`ecs'`,Abbr`ecs`,Abbr`envs'`,Abbr`envs`,Abbr`fvl`,Abbr`fvl'`] >>
      rfs[] ) >>
    rfs[] >>
    `ecs = (CHOICE fvs, CERef (x+1))::ecs'` by (
      match_mp_tac LIST_EQ_MAP_PAIR >>
      conj_tac >- (
        simp[Abbr`ecs`,Abbr`ecs'`,MAP_MAP_o,combinTheory.o_DEF,Abbr`envs`,Abbr`envs'`,Abbr`fvl`,Abbr`fvl'`] ) >>
      match_mp_tac (fst(EQ_IMP_RULE(SPEC_ALL REVERSE_INV))) >>
      asm_simp_tac std_ss [MAP,REVERSE_DEF] ) >>
    qsuff_tac `env0 = env0'` >- rw[] >>
    simp[Abbr`env0`,Abbr`env0'`,Abbr`ls1`,Abbr`ls1'`,Abbr`ls2`,Abbr`ls2'`] >>
    simp[GENLIST_CONS,combinTheory.o_DEF,ADD1,FUPDATE_LIST_THM] >>
    AP_THM_TAC >> AP_TERM_TAC >>
    simp[Abbr`args'`,Abbr`args`,Abbr`fvl`,Abbr`fvl'`] >>
    qmatch_abbrev_tac`(env |++ ls) |+ p = env |+ p |++ ls2` >>
    Q.ISPECL_THEN[`p::ls`,`ls++[p]`,`env`]mp_tac FUPDATE_LIST_ALL_DISTINCT_PERM >>
    `ALL_DISTINCT (MAP FST (p::ls))` by (
      qsuff_tac `∃P. MAP FST (p::ls) = FILTER P (SET_TO_LIST fvs)`
        >- metis_tac[FILTER_ALL_DISTINCT,ALL_DISTINCT_SET_TO_LIST] >>
      simp[Once SET_TO_LIST_THM] >>
      rw[Abbr`p`,Abbr`ls`,MAP_ZIP,Abbr`ls2`] >>
      qexists_tac`λx. MEM x xs ∨ (x = CHOICE fvs)` >> rw[] >>
      simp[FILTER_EQ] >>
      simp[REST_DEF] ) >>
    simp[sortingTheory.PERM_CONS_EQ_APPEND,FUPDATE_LIST_THM,FUPDATE_LIST_APPEND] >>
    disch_then (match_mp_tac o GSYM) >>
    map_every qexists_tac [`ls`,`[]`] >>
    rw[] ) >>
  asm_simp_tac std_ss [Once SET_TO_LIST_THM,SimpRHS] >>
  rw[] >>
  Q.ISPECL_THEN[`xs`,`CHOICE fvs`,`1`](strip_assume_tac o SYM) find_index_MEM >>
  Q.ISPECL_THEN[`xs`,`CHOICE fvs`,`0`](strip_assume_tac o SYM) find_index_MEM >>
  rfs[] >>
  reverse conj_asm2_tac >- (
    simp[Abbr`ecs'`,Abbr`ecs`,Abbr`envs'`,Abbr`envs`,Abbr`fvl`,Abbr`fvl'`]) >>
  `ns ≠ [] ⇒ (EL i ns ∉ set xs ⇒ (EL i ns ≠ CHOICE fvs))` by (
    strip_tac >>
    spose_not_then strip_assume_tac >> fs[] ) >>
  qsuff_tac `env0 = env0'` >- (
    rw[] >> fs[REST_DEF] ) >>
  `ecs = ecs'` by (
    match_mp_tac LIST_EQ_MAP_PAIR >>
    conj_tac >- (
      simp[Abbr`ecs`,Abbr`ecs'`,MAP_MAP_o,combinTheory.o_DEF,Abbr`envs`,Abbr`envs'`,Abbr`fvl`,Abbr`fvl'`] ) >>
    rw[] ) >>
  simp_tac std_ss [Abbr`env0`,Abbr`env0'`,Abbr`ls1`,Abbr`ls1'`,Abbr`ls2`,Abbr`ls2'`] >>
  pop_assum SUBST1_TAC >>
  simp[] >>
  simp[GENLIST_CONS,combinTheory.o_DEF,ADD1,FUPDATE_LIST_THM] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  simp[Abbr`args'`,Abbr`args`,Abbr`fvl`,Abbr`fvl'`] >>
  simp[FUPDATE_LIST_THM] )

val FDOM_bind_fv = store_thm("FDOM_bind_fv",
  ``∀ns xs az i fvs env ecl ec.
      FINITE fvs ∧ (ns ≠ [] ⇒ i < LENGTH ns) ∧ ALL_DISTINCT ns ⇒
      (FDOM (FST(ITSET (bind_fv ns xs az i) fvs (env,ecl,ec))) = FDOM env ∪ fvs)``,
  rpt gen_tac >> strip_tac >>
  qspecl_then[`ns`,`xs`,`az`,`i`,`fvs`,`(env,ecl,ec)`]mp_tac bind_fv_thm >>
  rw[] >>
  rw[Abbr`env0`,FDOM_FUPDATE_LIST,Abbr`ls1`,MAP_ZIP,Abbr`ls2`] >>
  rw[MAP_GENLIST,combinTheory.o_DEF,LIST_TO_SET_GENLIST,IMAGE_EL_count_LENGTH] >>
  rw[EXTENSION,Abbr`args`,MEM_FILTER,Abbr`fvl`,Abbr`ecs`,EXISTS_PROD,MEM_MAP,Abbr`envs`] >>
  rw[EQ_IMP_THM] >> fs[] >>
  Cases_on`MEM x xs`>>fs[] >>
  fs[find_index_ALL_DISTINCT_EL_eq] >>
  metis_tac[])
*)

(*
val Cenv_bs_bind_fv = store_thm("Cenv_bs_bind_fv",
  ``∀c rd s env ns xs az i fvs bs
     cenv defs e l vs a benv bve ret bvs st pp.
    (env = DRESTRICT (extend_rec_env cenv cenv ns defs xs vs) fvs) ∧
    (bs.stack = benv::CodePtr ret::(REVERSE bvs)++(Block closure_tag [CodePtr a;benv])::st) ∧
    (pp = mk_pp rd c bs) ∧
    (benv = Block 0 bve) ∧
    (fvs = free_vars c e) ∧
    benv_bvs pp bve fvs xs cenv defs ns i ∧
    s_refs c rd s bs ∧
    ALL_DISTINCT ns ∧
    ALL_DISTINCT xs ∧
    (ns ≠ [] ⇒ i < LENGTH ns ∧ (LENGTH ns = LENGTH defs) ∧ (EL i defs = (xs,INR l))) ∧
    ((ns = []) ⇒ (defs = [(xs,INR l)])) ∧
    (FLOOKUP c l = SOME e) ∧
    (bc_find_loc_aux bs.code bs.inst_length l 0 = SOME a) ∧
    (LENGTH xs = LENGTH vs) ∧
    EVERY2 (Cv_bv pp) vs bvs ∧
    fvs ⊆ FDOM cenv ∪ set ns ∪ set xs ∧
    (az = LENGTH vs)
    ⇒ Cenv_bs c rd s env (FST (ITSET (bind_fv ns xs az i) fvs (FEMPTY,0,[]))) 0 bs``,
  rw[Cenv_bs_def] >>
  simp[fmap_rel_def] >>
  conj_asm1_tac >- (
    rw[FDOM_bind_fv,FDOM_extend_rec_env,FDOM_DRESTRICT] >>
    rw[INTER_COMM] >>
    rw[GSYM SUBSET_INTER_ABSORPTION] ) >>
  rfs[FDOM_bind_fv] >> pop_assum (assume_tac o SYM) >>
  qabbrev_tac `fvs = free_vars c e` >>
  `FINITE fvs` by rw[Abbr`fvs`] >>
  qspecl_then[`ns`,`xs`,`LENGTH vs`,`i`,`fvs`,`(FEMPTY,0,[])`]mp_tac bind_fv_thm >>
  rw[] >> simp[] >>
  Cases_on `MEM x args` >- (
    `MEM x xs` by (
      fs[Abbr`args`,Abbr`fvl`,MEM_FILTER] ) >>
    `∃n. (find_index x xs 1 = SOME (n + 1)) ∧ (EL n xs = x)` by (
      simp[find_index_LEAST_EL] >>
      numLib.LEAST_ELIM_TAC >>
      fs[MEM_EL] >> PROVE_TAC[]) >>
    Q.PAT_ABBREV_TAC`env1 = if X then Y else env0` >>
    qho_match_abbrev_tac`P (env1 ' x)` >>
    qsuff_tac`P (env0 ' x)` >- (
      rw[Abbr`env1`,Abbr`P`,FAPPLY_FUPDATE_THM] >>
      rw[] >> fs[] ) >>
    `env0 ' x = (FEMPTY |++ ls1) ' x` by (
      simp[Abbr`env0`] >>
      match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
      simp_tac std_ss [Abbr`ls2`,MAP_GENLIST,LIST_TO_SET_GENLIST,combinTheory.o_DEF,IMAGE_EL_count_LENGTH]>>
      simp[Abbr`ecs`,FORALL_PROD,Abbr`envs`,Abbr`fvl`,MEM_MAP,MEM_FILTER] ) >>
    pop_assum SUBST1_TAC >>
    match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_tac >- rw[Abbr`ls1`,FILTER_ALL_DISTINCT,ALL_DISTINCT_SET_TO_LIST,Abbr`fvl`,MAP_ZIP,Abbr`args`] >>
    simp[Abbr`ls1`,MAP_ZIP,Abbr`args`] >>
    Q.PAT_ABBREV_TAC`ls = FILTER X fvl` >>
    `ALL_DISTINCT ls` by rw[Abbr`ls`,FILTER_ALL_DISTINCT,Abbr`fvl`,ALL_DISTINCT_SET_TO_LIST] >>
    simp[ALL_DISTINCT_MEM_ZIP_MAP,Abbr`P`] >>
    fsrw_tac[ARITH_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    rfs[MEM_ZIP] >> fsrw_tac[DNF_ss][] >>
    simp[DRESTRICT_DEF] >>
    simp[extend_rec_env_def,FOLDL2_FUPDATE_LIST,MAP2_MAP,FST_pair,MAP_ZIP,SND_pair] >>
    Q.PAT_ABBREV_TAC`env2 = FOLDL X cenv ns` >>
    qho_match_abbrev_tac`P ((env2 |++ ZIP (xs,vs)) ' x)` >>
    match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
    simp[MAP_ZIP] >>
    simp[MEM_ZIP] >>
    fsrw_tac[DNF_ss][Abbr`P`] >>
    qexists_tac`n`>>simp[]>>
    imp_res_tac find_index_LESS_LENGTH >> rfs[] >>
    Q.PAT_ABBREV_TAC`bv = EL X (Block 0 bve::Y)` >>
    qsuff_tac`bv = EL n bvs` >- rw[] >>
    rw[Abbr`bv`] >>
    pop_assum mp_tac >>
    rpt (pop_assum kall_tac) >>
    simp[EL_CONS] >>
    srw_tac[ARITH_ss][PRE_SUB1] >>
    `(LENGTH bvs - n) = SUC (LENGTH bvs - n - 1)` by DECIDE_TAC >>
    pop_assum SUBST1_TAC >> simp[] >>
    simp[EL_APPEND1] >>
    simp[EL_REVERSE,GSYM ADD1] ) >>
  `¬MEM x xs` by (
    rfs[Abbr`args`,MEM_FILTER,Abbr`fvl`,MEM_SET_TO_LIST] ) >>
  Cases_on `find_index x ns 0 = SOME i` >- (
    `x = EL i ns` by (
      imp_res_tac find_index_ALL_DISTINCT_EL_eq >> fs[] ) >>
    `ns ≠ []` by (Cases_on `ns` >> fs[find_index_def]) >>
    `LENGTH bvs = LENGTH vs` by fs[EVERY2_EVERY] >>
    fsrw_tac[ARITH_ss][ADD1] >>
    `MEM (EL i ns) ns` by (rw[MEM_EL] >> PROVE_TAC[]) >>
    simp[DRESTRICT_DEF] >>
    simp[extend_rec_env_def,FOLDL_FUPDATE_LIST,FOLDL2_FUPDATE_LIST,MAP2_MAP,FST_pair,SND_pair,MAP_ZIP] >>
    Q.PAT_ABBREV_TAC`env1 = cenv |++ X` >>
    `(env1 |++ ZIP (xs,vs)) ' (EL i ns) = CRecClos cenv ns defs (EL i ns)` by (
      match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
      simp[MAP_ZIP,Abbr`env1`] >>
      ho_match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
      simp[MAP_MAP_o,combinTheory.o_DEF,MEM_MAP] ) >>
    pop_assum SUBST1_TAC >>
    `LENGTH vs + 2 = SUC(SUC(LENGTH(REVERSE bvs)))` by srw_tac[ARITH_ss][ADD1] >>
    pop_assum SUBST1_TAC >>
    REWRITE_TAC[EL,TL] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    simp_tac std_ss [EL_LENGTH_APPEND,NULL,GSYM CONS_APPEND,HD] >>
    simp[Once Cv_bv_cases] ) >>
  Cases_on `MEM x ns` >- (
    `ns ≠ []` by (Cases_on `ns` >> fs[]) >> fs[] >>
    Cases_on `x = EL i ns` >- (
      fs[] >>
      `i < LENGTH ns` by rw[] >>
      imp_res_tac find_index_ALL_DISTINCT_EL >>
      fs[] ) >>
    Q.PAT_ABBREV_TAC`env1 = if X then Y else env0` >>
    qho_match_abbrev_tac`P (env1 ' x)` >>
    qsuff_tac`P (env0 ' x)` >- (
      rw[Abbr`env1`,Abbr`P`,FAPPLY_FUPDATE_THM] ) >>
    simp[Abbr`env1`,Abbr`P`] >>
    `∃jx. find_index x ns 0 = SOME jx` by (
      metis_tac[find_index_MEM,optionTheory.NOT_SOME_NONE,optionTheory.option_CASES] ) >>
    `MEM (x, CERef (jx + 1)) ecs` by (
      simp[Abbr`ecs`,MEM_MAP,Abbr`envs`,MEM_FILTER,Abbr`fvl`] ) >>
    `∃n. (env0 ' x = CTRef n) ∧ n < LENGTH ecs ∧ (EL n ecs = (x, CERef (jx + 1))) ∧ (find_index (EL n envs) ns 0 = SOME jx)` by (
      fs[MEM_EL] >>
      qmatch_assum_rename_tac`m < LENGTH ecs`[] >>
      qexists_tac`m`>>simp[] >>
      simp[Abbr`env0`] >>
      reverse conj_tac >- (
        fs[Abbr`ecs`] >> rfs[EL_MAP] >>
        Cases_on`find_index (EL m envs) ns 0` >> fs[] ) >>
      qabbrev_tac`fm = FEMPTY |++ ls1` >>
      qho_match_abbrev_tac`P ((fm |++ ls2) ' (EL n ns))` >>
      match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
      simp_tac std_ss [Abbr`ls2`,GENLIST_EL_MAP,MAP_GENLIST,combinTheory.o_DEF,LIST_TO_SET_GENLIST,IMAGE_EL_count_LENGTH,Abbr`P`] >>
      conj_tac >- rw[FILTER_ALL_DISTINCT,Abbr`fvl`,ALL_DISTINCT_SET_TO_LIST,Abbr`ecs`,MAP_MAP_o,combinTheory.o_DEF,Abbr`envs`] >>
      simp[] >>
      qexists_tac`m` >>
      qpat_assum`X = EL m ecs`(assume_tac o SYM) >>
      simp[] ) >>
    qpat_assum`benv_bvs pp bvs fvs xs cenv defs ns i`mp_tac >>
    `envs ≠ []` by (
      simp[Abbr`envs`,FILTER_EQ_NIL,combinTheory.o_DEF,EXISTS_MEM,Abbr`fvl`] >>
      PROVE_TAC[] ) >>
    simp[CONJUNCT2(SPEC_ALL Cv_bv_cases)] >>
    disch_then strip_assume_tac >>
    simp[] >>
    `LENGTH ecs = LENGTH envs` by rw[Abbr`ecs`] >> fs[] >>
    first_x_assum(qspec_then`n`mp_tac) >>
    simp[] >>
    disch_then(qx_choosel_then[`p`,`jenv`]strip_assume_tac) >>
    fs[s_refs_def] >>
    qpat_assum`good_rd c rd bs`(mp_tac o SIMP_RULE(srw_ss())[good_rd_def,FEVERY_DEF]) >>
    strip_tac >>
    first_x_assum(qspec_then`p`mp_tac) >>
    fs[FLOOKUP_DEF] >>
    simp[DRESTRICT_DEF,extend_rec_env_def,FOLDL_FUPDATE_LIST,FOLDL2_FUPDATE_LIST,MAP2_MAP,MAP_ZIP,FST_pair,SND_pair] >>
    strip_tac >>
    Q.PAT_ABBREV_TAC`env1 = cenv |++ X` >>
    `(env1 |++ ZIP (xs,vs)) ' x = CRecClos cenv ns defs (EL jx ns)` by (
      match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
      simp[MAP_ZIP,Abbr`env1`] >>
      ho_match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
      simp[MAP_MAP_o,combinTheory.o_DEF,MEM_MAP] >>
      imp_res_tac find_index_ALL_DISTINCT_EL_eq >>
      simp[]) >>
    simp[] >>
    match_mp_tac (MP_CANON syneq_Cv_bv) >> simp[] >>
    qexists_tac`CRecClos jenv ns defs (EL jx ns)` >> simp[] >>
    simp[syneq_cases] >>
    fs[fmap_rel_OPTREL_FLOOKUP,EVERY_MEM,FORALL_PROD] >>
    rpt gen_tac >> strip_tac >>
    qx_gen_tac`v` >> strip_tac >>
    first_x_assum(qspec_then`v`mp_tac) >>
    rw[FLOOKUP_DRESTRICT] >>
    fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD] >>
    metis_tac[IN_DIFF] ) >>
  `x ∈ set envs` by (
    rw[MEM_FILTER,Abbr`envs`,Abbr`fvl`] ) >>
  `ns ≠ [] ⇒ (MEM (EL i ns) ns)` by (
    strip_tac >> fs[] >> rw[MEM_EL] >> PROVE_TAC[] ) >>
  Q.PAT_ABBREV_TAC`env1 = if X then Y else env0` >>
  qho_match_abbrev_tac`P (env1 ' x)` >>
  qsuff_tac`P (env0 ' x)` >- (
    rw[Abbr`env1`,Abbr`P`,FAPPLY_FUPDATE_THM] >>
    rw[] >> fs[]) >>
  simp[Abbr`env1`,Abbr`P`] >>
  `find_index x ns 0 = NONE` by (
    Q.ISPECL_THEN[`ns`,`x`,`0`]mp_tac find_index_MEM >> rw[] ) >>
  `MEM (x, CEEnv x) ecs` by (
    simp[Abbr`ecs`,MEM_MAP] ) >>
  `∃n. (env0 ' x = CTEnv n) ∧ n < LENGTH ecs ∧ (EL n ecs = (x, CEEnv x)) ∧ (find_index (EL n envs) ns 0 = NONE) ∧ (x = EL n envs)` by (
    fs[MEM_EL] >>
    qmatch_assum_rename_tac`(x,CEEnv x) = EL m ecs`[] >>
    `m = n` by (
      fs[Abbr`ecs`] >> rfs[EL_MAP] >>
      qsuff_tac `ALL_DISTINCT envs` >-
        (fs[EL_ALL_DISTINCT_EL_EQ] >> PROVE_TAC[])>>
      simp[Abbr`envs`,FILTER_ALL_DISTINCT,Abbr`fvl`,ALL_DISTINCT_SET_TO_LIST] ) >>
    qexists_tac`n`>>simp[]>>
    rfs[Abbr`env0`] >>
    qabbrev_tac`fm = FEMPTY |++ ls1` >>
    qho_match_abbrev_tac`P ((fm |++ ls2) ' (EL n envs))` >>
    match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
    simp_tac std_ss [Abbr`ls2`,GENLIST_EL_MAP,MAP_GENLIST,combinTheory.o_DEF,LIST_TO_SET_GENLIST,IMAGE_EL_count_LENGTH,Abbr`P`] >>
    conj_tac >- rw[FILTER_ALL_DISTINCT,Abbr`fvl`,ALL_DISTINCT_SET_TO_LIST,Abbr`ecs`,MAP_MAP_o,combinTheory.o_DEF,Abbr`envs`] >>
    simp[] >>
    qpat_assum`X = EL m ecs`(assume_tac o SYM) >>
    qexists_tac`m`>>simp[]) >>
  simp[] >>
  qpat_assum`benv_bvs pp benv fvs xs cenv defs ns i`mp_tac >>
  `envs ≠ []` by (
    simp[Abbr`envs`,FILTER_EQ_NIL,combinTheory.o_DEF,EXISTS_MEM,Abbr`fvl`] >>
    PROVE_TAC[] ) >>
  simp[CONJUNCT2(SPEC_ALL Cv_bv_cases)] >>
  disch_then(strip_assume_tac) >>
  simp[] >>
  `LENGTH ecs = LENGTH envs` by rw[Abbr`ecs`] >> fs[] >>
  first_x_assum(qspec_then`n`mp_tac) >> simp[] >> rw[] >>
  simp[DRESTRICT_DEF,extend_rec_env_def,FOLDL_FUPDATE_LIST,FOLDL2_FUPDATE_LIST,MAP2_MAP,MAP_ZIP,FST_pair,SND_pair] >>
  `EL n envs ∈ FDOM cenv` by (
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[] ) >>
  rw[] >>
  Q.PAT_ABBREV_TAC`env1 = cenv |++ X` >>
  `(env1 |++ ZIP (xs,vs)) ' (EL n envs) = cenv ' (EL n envs)` by (
    match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
    simp[MAP_ZIP,Abbr`env1`] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
    simp[MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,FORALL_PROD] ) >>
  rw[])
*)

(*
val benv_bvs_free_vars_SUBSET = store_thm("benv_bvs_free_vars_SUBSET",
  ``FINITE fvs ∧ benv_bvs pp benv fvs xs env defs ns i ⇒
    fvs ⊆ FDOM env ∪ set ns ∪ set xs``,
  rw[Once Cv_bv_cases,SUBSET_DEF] >>
  Cases_on`MEM x ns`>>fs[] >>
  Cases_on`MEM x xs`>>fs[] >>
  `find_index x ns 0 = NONE` by rw[GSYM find_index_MEM] >>
  qmatch_assum_abbrev_tac`LENGTH bvs = LENGTH (FILTER P fvl)` >>
  `MEM x (FILTER P fvl)`  by (
    rw[MEM_FILTER,Abbr`P`,Abbr`fvl`] ) >>
  pop_assum(strip_assume_tac o SIMP_RULE(srw_ss())[MEM_EL]) >>
  first_x_assum(qspec_then`n`mp_tac) >> rw[])
*)

fun filter_asms P = POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC o List.rev o List.filter P)

val Cv_bv_not_env = store_thm("Cv_bv_not_env",
  ``∀pp Cv bv. Cv_bv pp Cv bv ⇒ ∀vs. (bv = Block 0 vs) ⇒ (vs = [])``,
  gen_tac >> ho_match_mp_tac Cv_bv_only_ind >> simp[])

(* TODO: move *)
val bump_pc_inst_length = store_thm("bump_pc_inst_length",
  ``(bump_pc s).inst_length = s.inst_length``,
  rw[bump_pc_def] >> BasicProvers.CASE_TAC >> rw[])
val _ = export_rewrites["bump_pc_inst_length"]

val compile_bindings_thm = store_thm("compile_bindings_thm",
  ``∀d env t sz e n s m bc cc.
    ((compile_bindings d env t sz e n s m).out = bc ++ s.out) ∧
    ((compile d
       ((REVERSE(GENLIST(λi. CTLet (sz+n+1+i))m))++env)
       (case t of TCTail j k => TCTail j (k+(m+n)) | _ => t)
       (sz+(m+n))
       s e).out = cc++s.out) ⇒
    (bc = (case t of TCNonTail F => [Stack(Pops (m + n))] | _ => [])++cc)``,
  Induct_on`m`>- (
    rw[compile_def,FUPDATE_LIST_THM]>>
    Cases_on`t`>>fs[]>>
    rw[]>>fs[]) >>
  rw[compile_def,GENLIST_CONS,combinTheory.o_DEF] >>
  qmatch_assum_abbrev_tac`(compile_bindings d env0 t sz e n0 s m).out = bc ++ s.out` >>
  first_x_assum(qspecl_then[`d`,`env0`,`t`,`sz`,`e`,`n0`,`s`,`bc`,`cc`]mp_tac) >>
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

val closure_data_component_equality = DB.fetch"Compile""closure_data_component_equality"

val compile_val = store_thm("compile_val",
  ``(∀c s env exp res. Cevaluate c s env exp res ⇒
      ∀rd s' v cs cenv sz bs bce bcr bc0.
        Cexp_pred exp ∧
        BIGUNION (IMAGE all_Clocs (set env)) ⊆ count (LENGTH s) ∧
        BIGUNION (IMAGE all_Clocs (set s)) ⊆ count (LENGTH s) ∧
        (body_count exp = 0) ∧
        (res = (s', Rval v)) ∧
        (bce ++ bcr = bs.code) ∧ good_code_env c bce ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        (free_vars exp ⊆ count (LENGTH cenv)) ∧
        Cenv_bs c rd s env cenv sz (bs with code := bce) ∧
        ALL_DISTINCT (FILTER is_Label bc0) ∧
        EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc0)
        ⇒
      (∀code bc1.
        ((compile c cenv (TCNonTail F) sz cs exp).out = REVERSE code ++ cs.out) ∧
        (bs.code = bc0 ++ code ++ bc1)
       ⇒
       code_for_push rd bs bce bc0 code s s' c env [v] cenv sz) ∧
      (∀code bc1 az lz.
        ((compile c cenv (TCTail az lz) sz cs exp).out = REVERSE code ++ cs.out) ∧
        (bs.code = bc0 ++ code ++ bc1)
        ⇒
        ∀env0 defs vs klvs blvs benv ret args cl st.
        (az = LENGTH args) ∧ (lz = LENGTH klvs) ∧
        (env = klvs ++ extend_rec_env env0 defs vs) ∧
        EVERY2 (Cv_bv (mk_pp rd c (bs with code := bce))) vs args ∧
        EVERY2 (Cv_bv (mk_pp rd c (bs with code := bce))) klvs blvs ∧
        (bs.stack = blvs++benv::CodePtr ret::(REVERSE args)++cl::st)
        ⇒
        code_for_return rd bs bce st ret v s s' c)) ∧
    (∀c s env exps ress. Cevaluate_list c s env exps ress ⇒
      ∀rd s' vs cs cenv sz bs bce bcr bc0 code bc1.
        EVERY Cexp_pred exps ∧
        BIGUNION (IMAGE all_Clocs (set env)) ⊆ count (LENGTH s) ∧
        BIGUNION (IMAGE all_Clocs (set s)) ⊆ count (LENGTH s) ∧
        (body_count_list exps = 0) ∧
        (ress = (s', Rval vs)) ∧
        (bce ++ bcr = bs.code) ∧ good_code_env c bce ∧
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        (BIGUNION (IMAGE free_vars (set exps)) ⊆ count (LENGTH cenv)) ∧
        Cenv_bs c rd s env cenv sz (bs with code := bce) ∧
        ALL_DISTINCT (FILTER is_Label bc0) ∧
        EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc0)
        ⇒
      (((compile_nts c cenv sz cs exps).out = REVERSE code ++ cs.out) ⇒
        code_for_push rd bs bce bc0 code s s' c env vs cenv sz))``,
  ho_match_mp_tac Cevaluate_strongind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    ntac 3 gen_tac >> qx_gen_tac`n` >> strip_tac >> simp[] >>
    rpt gen_tac >> strip_tac >> simp[compile_def,pushret_def] >>
    conj_asm1_tac >- (
      ntac 2 gen_tac >>
      fs[code_for_push_def,Cenv_bs_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
      fs[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >> rfs[] >>
      last_assum (qspec_then `n` mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
      REWRITE_TAC[Once option_case_NONE_F] >> simp[EL_ZIP] >>
      disch_then(Q.X_CHOOSE_THEN`x`strip_assume_tac) >>
      strip_tac >>
      imp_res_tac Cv_bv_not_env >>
      map_every qexists_tac [`[x]`,`bs.refs`,`rd`] >> rw[s_refs_with_stack] >- (
        match_mp_tac compile_varref_thm >> fs[] >>
        simp[bc_state_component_equality] >>
        metis_tac[])
      >- (
        qmatch_assum_rename_tac `z < LENGTH cenv`[] >>
        qmatch_abbrev_tac`X` >>
        last_x_assum (qspec_then `z` mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
        simp[option_case_NONE_F,EL_ZIP] >> rw[] >>
        qunabbrev_tac`X` >>
        imp_res_tac lookup_ct_imp_incsz >>
        rfs[EL_ZIP]) >>
      fs[s_refs_def,good_rd_def]) >>
    rw[] >> fs[] >>
    match_mp_tac code_for_push_return >>
    qspecl_then[`sz`,`cs`,`EL n cenv`]strip_assume_tac compile_varref_append_out >> fs[] >>
    first_x_assum(qspec_then`REVERSE bc`mp_tac) >> simp[] >>
    fs[Once SWAP_REVERSE] >> strip_tac >>
    qmatch_assum_abbrev_tac `code_for_push rd bs bce bc0 ccode s s c renv v cenv rsz` >>
    map_every qexists_tac [`bc0`,`ccode`,`renv`,`cenv`,`rsz`] >>
    simp[] >>
    qexists_tac `REVERSE args` >> fsrw_tac[ARITH_ss][EVERY2_EVERY]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    conj_asm1_tac >- (
      ntac 2 gen_tac >>
      Cases_on`l`>>rw[compile_def,LET_THM,code_for_push_def,pushret_def]>>
      qpat_assum`X = REVERSE code`(assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
      qmatch_assum_abbrev_tac `code = [x]` >>
      `bc_fetch bs = SOME x` by (
        match_mp_tac bc_fetch_next_addr >>
        qexists_tac `bc0` >>
        rw[Abbr`x`]) >> (
      rw[Once Cv_bv_cases] >>
      map_every qexists_tac [`bs.refs`,`rd`] >> reverse (rw[]) >- (
        match_mp_tac Cenv_bs_imp_incsz >>
        qexists_tac`bs with code := bce` >>
        rw[bc_state_component_equality]  ) >>
      rw[RTC_eq_NRC] >>
      qexists_tac `SUC 0` >>
      rw[NRC] >>
      rw[bc_eval1_thm] >>
      rw[bc_eval1_def,Abbr`x`] >>
      rw[bc_eval_stack_def] >>
      srw_tac[ARITH_ss][bump_pc_def,FILTER_APPEND,SUM_APPEND,ADD1])) >>
    ntac 4 gen_tac >> strip_tac >>
    qspecl_then[`c`,`cenv`,`TCNonTail F`,`sz`,`cs`,`(CLit l)`]strip_assume_tac(CONJUNCT1 compile_append_out) >> fs[] >>
    fs[Once SWAP_REVERSE] >>
    `∃bc2. code ++ bc1 = REVERSE bc ++ (retbc az lz) ++ bc2` by (
      Cases_on`l`>>fs[compile_def,pushret_def] >> rw[] >> fs[Once SWAP_REVERSE]) >>
    fs[] >> rpt gen_tac >> strip_tac >>
    match_mp_tac code_for_push_return >> simp[] >>
    qmatch_assum_abbrev_tac`code_for_push rd bs bce bc0 ccode s s c renv v cenv rsz` >>
    map_every qexists_tac [`bc0`,`ccode`,`renv`,`cenv`,`rsz`] >> rw[] >>
    qexists_tac`REVERSE args`>>fsrw_tac[ARITH_ss][EVERY2_EVERY]) >>
  strip_tac >- (
    fsrw_tac[ETA_ss][FOLDL_UNION_BIGUNION] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def,LET_THM,pushret_def] >>
    fsrw_tac[ETA_ss][] >>
    conj_asm1_tac >- (
      ntac 2 gen_tac >>
      qspecl_then[`c`,`cenv`,`sz`,`cs`,`exps`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT2 (CONJUNCT2 compile_append_out)) >>
      fs[] >>
      disch_then(assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
      qmatch_assum_abbrev_tac `code = ls0 ++ [x]` >>
      first_x_assum (qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`ls0`]mp_tac) >>
      simp[Abbr`ls0`] >>
      simp[code_for_push_def] >>
      disch_then(qx_choosel_then[`bvs`,`rf`,`rd'`]strip_assume_tac) >>
      srw_tac[DNF_ss][Once Cv_bv_cases] >>
      map_every qexists_tac[`rf`,`rd'`,`bvs`] >>
      simp[] >>
      conj_tac >- (
        qmatch_assum_abbrev_tac `bc_next^* bs0 bs05` >>
        rw[Once RTC_CASES2] >> disj2_tac >>
        qexists_tac `bs05` >>
        fs[Abbr`bs0`,Abbr`bs05`] >>
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
      qmatch_assum_abbrev_tac`Cenv_bs c rd' s' denv cenv sz1 bs1` >>
      `Cenv_bs c rd' s' denv cenv sz (bs1 with stack := bs.stack)` by (
        match_mp_tac Cenv_bs_pops >>
        map_every qexists_tac[`REVERSE bvs`,`bs1`] >>
        imp_res_tac Cevaluate_list_LENGTH >>
        fs[] >>
        simp[bc_state_component_equality,Abbr`bs1`] >>
        `LENGTH exps = LENGTH bvs` by fs[EVERY2_EVERY] >> fs[] >>
        PROVE_TAC[Cenv_bs_CTLet_bound,ADD_SYM] ) >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac `bs1 with stack := bs.stack` >>
      rw[bc_state_component_equality,Abbr`bs1`] ) >>
    ntac 4 gen_tac >> strip_tac >> fs[] >> rw[] >>
    match_mp_tac code_for_push_return >>
    first_x_assum(qspecl_then[`rd`]kall_tac) >>
    qspecl_then[`c`,`cenv`,`sz`,`cs`,`exps`]strip_assume_tac(CONJUNCT2(CONJUNCT2 compile_append_out)) >>
    fs[Once SWAP_REVERSE] >>
    qmatch_assum_abbrev_tac`code_for_push rd bs bce bc0 ccode s s' c renv v cenv rsz` >>
    map_every qexists_tac[`bc0`,`ccode`,`renv`,`cenv`,`rsz`] >>
    simp[Abbr`ccode`] >>
    qexists_tac`REVERSE args`>>fsrw_tac[ARITH_ss][EVERY2_EVERY]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    fs[] >> rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    conj_asm1_tac >- (
      rw[compile_def,LET_THM,pushret_def] >> fs[REVERSE_APPEND] >>
      qspecl_then[`c`,`cenv`,`TCNonTail F`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
      fs[Once SWAP_REVERSE] >>
      qmatch_assum_abbrev_tac `code = ls0 ++ [x]` >>
      first_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
      simp[code_for_push_def,Abbr`ls0`,Once SWAP_REVERSE] >>
      disch_then(qx_choosel_then[`bv`,`rfs`,`rd'`] mp_tac o CONJUNCT1) >>
      srw_tac[DNF_ss][Once Cv_bv_cases] >>
      srw_tac[DNF_ss][Once Cv_bv_cases] >>
      map_every qexists_tac[`rfs`,`rd'`] >>
      conj_tac >- (
        qmatch_assum_abbrev_tac `bc_next^* bs bs05` >>
        rw[Once RTC_CASES2] >> disj2_tac >>
        qexists_tac `bs05` >> rw[] >>
        `bc_fetch bs05 = SOME x` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs05`,Abbr`x`] >>
          map_every qexists_tac [`bc0 ++ REVERSE cx`,`bc1`] >> rw[] ) >>
        rw[bc_eval1_thm] >>
        rw[bc_eval1_def,Abbr`x`] >>
        rw[bump_pc_def] >>
        rw[bc_eval_stack_def,Abbr`bs05`] >>
        unabbrev_all_tac >>
        srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] >>
        rw[bc_state_component_equality] >>
        AP_TERM_TAC >> rw[EQ_IMP_THM] ) >>
      reverse conj_tac >- fs[] >>
      qmatch_assum_abbrev_tac`Cenv_bs c rd' s' ccenv csenv sz1 bs1` >>
      `Cenv_bs c rd' s' ccenv csenv sz (bs1 with stack := bs.stack)` by (
        match_mp_tac Cenv_bs_imp_decsz >>
        qexists_tac `bs1` >>
        rw[bc_state_component_equality,Abbr`bs1`,Abbr`sz1`] >>
        spose_not_then strip_assume_tac >>
        imp_res_tac Cenv_bs_CTLet_bound >>
        DECIDE_TAC ) >>
      qunabbrev_tac`sz1` >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac`bs1 with stack := bs.stack` >>
      rw[bc_state_component_equality,Abbr`bs1`] ) >>
    first_x_assum(qspec_then`rd` kall_tac) >>
    fs[compile_def,LET_THM,pushret_def] >>
    rw[]>>fs[] >>
    match_mp_tac code_for_push_return >>
    qspecl_then[`c`,`cenv`,`TCNonTail F`,`sz`,`cs`,`exp`]strip_assume_tac(CONJUNCT1 compile_append_out) >>
    fs[Once SWAP_REVERSE] >>
    qmatch_assum_abbrev_tac`code_for_push rd bs bce bc0 ccode s s' c renv v cenv csz` >>
    map_every qexists_tac[`bc0`,`ccode`,`renv`,`cenv`,`csz`] >>
    rw[Abbr`ccode`] >>
    qexists_tac`REVERSE args`>>fs[EVERY2_EVERY]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    fs[] >> rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    conj_asm1_tac >- (
      rw[compile_def,LET_THM,pushret_def] >> fs[REVERSE_APPEND] >>
      qspecl_then[`c`,`cenv`,`TCNonTail F`,`sz`,`cs`,`exp`]strip_assume_tac(CONJUNCT1 compile_append_out) >>
      fs[Once SWAP_REVERSE] >>
      qmatch_assum_abbrev_tac `code = ls0 ++ [x]` >>
      first_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
      simp[code_for_push_def,Abbr`ls0`,Once SWAP_REVERSE] >>
      disch_then(qx_choosel_then[`bv`,`rfs`,`rd'`] mp_tac o CONJUNCT1) >>
      fs[(Q.SPECL[`CConv m vs`](CONJUNCT1 (SPEC_ALL Cv_bv_cases)))] >>
      srw_tac[DNF_ss][] >>
      fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
      map_every qexists_tac[`rfs`,`rd'`,`EL n bvs`] >>
      rev_full_simp_tac(srw_ss()++DNF_ss)[MEM_ZIP] >>
      conj_tac >- (
        qmatch_assum_abbrev_tac `bc_next^* bs bs05` >>
        rw[Once RTC_CASES2] >> disj2_tac >>
        qexists_tac `bs05` >> rw[] >>
        `bc_fetch bs05 = SOME x` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs05`,Abbr`x`] >>
          map_every qexists_tac [`bc0 ++ REVERSE bc`,`bc1`] >> rw[] ) >>
        rw[bc_eval1_thm] >>
        rw[bc_eval1_def,Abbr`x`] >>
        rw[bump_pc_def] >>
        rw[bc_eval_stack_def,Abbr`bs05`] >>
        unabbrev_all_tac >>
        srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] ) >>
      qmatch_assum_abbrev_tac`Cenv_bs c rd' s' ccenv csenv sz1 bs1` >>
      `Cenv_bs c rd' s' ccenv csenv sz (bs1 with stack := bs.stack)` by (
        match_mp_tac Cenv_bs_imp_decsz >>
        qexists_tac `bs1` >>
        rw[bc_state_component_equality,Abbr`bs1`,Abbr`sz1`] >>
        spose_not_then strip_assume_tac >>
        imp_res_tac Cenv_bs_CTLet_bound >>
        DECIDE_TAC ) >>
      qunabbrev_tac`sz1` >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac`bs1 with stack := bs.stack` >>
      simp[bc_state_component_equality,Abbr`bs1`]) >>
    first_x_assum(qspec_then`rd` kall_tac) >>
    fs[compile_def,LET_THM,pushret_def] >>
    rw[]>>fs[] >>
    match_mp_tac code_for_push_return >>
    qspecl_then[`c`,`cenv`,`TCNonTail F`,`sz`,`cs`,`exp`]strip_assume_tac(CONJUNCT1 compile_append_out) >>
    fs[Once SWAP_REVERSE] >>
    qmatch_assum_abbrev_tac`code_for_push rd bs bce bc0 ccode s s' c ccenv v csenv csz` >>
    map_every qexists_tac[`bc0`,`ccode`,`ccenv`,`csenv`,`csz`] >>
    rw[Abbr`ccode`] >>
    qexists_tac`REVERSE args` >> fs[EVERY2_EVERY]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def] >>
    REWRITE_TAC[ONE] >> REWRITE_TAC[compile_def] >> simp[compile_def] >>
    qspecl_then[`c`,`cenv`,`TCNonTail F`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
    simp[GSYM FORALL_AND_THM] >> ntac 2 gen_tac >>
    reverse(Cases_on`∃bc10. code = REVERSE cx ++ bc10`) >- (
      fsrw_tac[DNF_ss][] >>
      conj_tac >> rpt gen_tac >>
      Q.PAT_ABBREV_TAC`tt = X:call_context` >>
      Q.PAT_ABBREV_TAC`ee = Y::cenv`>>
      Q.PAT_ABBREV_TAC`cs0 = compile c cenv X Y Z A` >>
      qspecl_then[`c`,`ee`,`tt`,`sz + 1`,`cs0`,`exp'`](strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
      fs[Once SWAP_REVERSE] >> strip_tac >> fs[]) >> fs[] >>
    POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC) >>
    first_x_assum(qspecl_then[`rd`,`cs`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
    `LENGTH s ≤ LENGTH s' ∧
     LENGTH s' ≤ LENGTH s''` by PROVE_TAC[LESS_EQ_TRANS,Cevaluate_store_SUBSET,FST] >>
    fs[ALL_DISTINCT_APPEND] >> rfs[] >>
    fs[Once SWAP_REVERSE] >>
    disch_then (mp_tac o SIMP_RULE (srw_ss()++DNF_ss) [code_for_push_def,LET_THM] o CONJUNCT1) >>
    reverse(Cases_on`∃bc11. bs.code = bc0 ++ REVERSE cx ++ bc11`) >- (
      rw[] >> fs[] ) >> fs[] >>
    disch_then (qx_choosel_then[`rf`,`rd'`,`bv`]strip_assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    conj_tac >- (
      Q.PAT_ABBREV_TAC`tt = X:call_context` >>
      Q.PAT_ABBREV_TAC`ee = Y::cenv`>>
      Q.PAT_ABBREV_TAC`cs0 = compile c cenv X Y Z A` >>
      qspecl_then[`c`,`ee`,`tt`,`sz + 1`,`cs0`,`exp'`](strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
      fs[Abbr`tt`,Once SWAP_REVERSE] >>
      first_x_assum(qspecl_then[`rd'`,`cs0`,`ee`,`sz+1`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE cx`]mp_tac) >>
      simp[Abbr`ee`] >>
      discharge_hyps >- (
        conj_tac >- (
          imp_res_tac Cevaluate_Clocs >> fs[] >>
          fsrw_tac[DNF_ss][SUBSET_DEF] >>
          metis_tac[LESS_LESS_EQ_TRANS]) >>
        conj_tac >- (
          imp_res_tac Cevaluate_Clocs >> fs[] ) >>
        simp[Abbr`cs0`,Abbr`bs1`] >>
        conj_tac >- (
          fsrw_tac[DNF_ss][SUBSET_DEF] >>
          Cases>>fsrw_tac[ARITH_ss][]>>
          strip_tac>>res_tac>>fsrw_tac[ARITH_ss][]) >>
        conj_tac >- (
          match_mp_tac Cenv_bs_FUPDATE >>
          qexists_tac `bs with <|code := bce; pc := next_addr bs.inst_length (bc0 ++ REVERSE cx); refs := rf|>` >>
          simp[bc_state_component_equality] >>
          match_mp_tac Cenv_bs_imp_decsz >> rfs[] >>
          qmatch_assum_abbrev_tac`Cenv_bs c rd' s' envv cenv szz bss` >>
          qexists_tac `bss` >>
          simp[bc_state_component_equality,Abbr`bss`,Abbr`szz`] >>
          spose_not_then strip_assume_tac >>
          imp_res_tac Cenv_bs_CTLet_bound >>
          DECIDE_TAC) >>
        match_mp_tac compile_labels_lemma >>
        map_every qexists_tac[`c`,`cenv`,`TCNonTail F`,`sz`,`cs`,`exp`] >>
        simp[Once SWAP_REVERSE] ) >>
      disch_then(mp_tac o SIMP_RULE (srw_ss()++DNF_ss) [code_for_push_def,LET_THM,Once SWAP_REVERSE] o CONJUNCT1) >>
      ntac 2 strip_tac >> fs[] >> rfs[] >>
      qpat_assum`∀bc1. X`mp_tac >>
      `bs1.code = bs.code` by rw[Abbr`bs1`] >>
      simp[] >>
      disch_then(qx_choosel_then[`rf'`,`rd''`,`bv'`]strip_assume_tac) >>
      srw_tac[DNF_ss][code_for_push_def,LET_THM] >>
      map_every qexists_tac [`rf'`,`rd''`,`bv'`] >>
      qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
      conj_tac >- (
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        qexists_tac`bs2` >>
        conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
        match_mp_tac RTC_SUBSET >>
        rw[bc_eval1_thm] >>
        `bc_fetch bs2 = SOME (Stack (Pops 1))` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs2`] >>
          qexists_tac`bc0 ++ REVERSE cx ++ REVERSE bc`>>rw[] ) >>
        rw[bc_eval1_def] >>
        rw[bump_pc_def] >>
        srw_tac[ARITH_ss][bc_eval_stack_def,Abbr`bs2`,Abbr`bs1`] >>
        rw[bc_state_component_equality] >>
        srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND] ) >>
      conj_tac >- fs[Abbr`bs1`] >>
      conj_tac >- (
        qmatch_abbrev_tac`Cenv_bs c rd'' s'' env cenv (sz + 1) bs4` >>
        match_mp_tac Cenv_bs_imp_incsz >>
        qmatch_assum_abbrev_tac`Cenv_bs c rd'' s'' env3 renv1 rsz1 bs3` >>
        qexists_tac`bs4 with <| stack := bs.stack; pc := bs3.pc |>` >>
        reverse(rw[]) >- rw[bc_state_component_equality,Abbr`bs4`] >>
        qspecl_then[`c`,`rd''`,`s''`,`env3`,`renv1`,`rsz1`,`bs3`]mp_tac Cenv_bs_DOMSUB >>
        simp[Abbr`renv1`,Abbr`rsz1`,Abbr`env3`] >> strip_tac >>
        match_mp_tac Cenv_bs_imp_decsz >>
        qexists_tac`bs4 with stack := bv::bs.stack` >>
        reverse(rw[]) >-(rw[bc_state_component_equality,Abbr`bs4`])
        >- (
          imp_res_tac Cenv_bs_CTLet_bound >>
          pop_assum (qspec_then`sz +1`mp_tac) >>
          srw_tac[ARITH_ss][] ) >>
        match_mp_tac Cenv_bs_imp_decsz >>
        qexists_tac`bs4 with stack := bs3.stack` >>
        reverse(rw[]) >-(rw[bc_state_component_equality,Abbr`bs4`,Abbr`bs3`,Abbr`bs1`])
        >- (
          imp_res_tac Cenv_bs_CTLet_bound >>
          pop_assum (qspec_then`sz +2`mp_tac) >>
          srw_tac[ARITH_ss][] ) >>
        `bs4 with stack := bs3.stack = bs3 with pc := bs4.pc` by (
          rw[Abbr`bs4`,Abbr`bs3`,bc_state_component_equality,Abbr`bs1`] ) >>
        fs[Cenv_bs_with_pc] >> fsrw_tac[ARITH_ss][]) >>
      fs[Abbr`bs1`] >> metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS]) >>
    ntac 2 gen_tac >>
    Q.PAT_ABBREV_TAC`tt = X:call_context` >>
    Q.PAT_ABBREV_TAC`ee = Y::cenv`>>
    Q.PAT_ABBREV_TAC`cs0 = compile c cenv X Y Z A` >>
    qspecl_then[`c`,`ee`,`tt`,`sz + 1`,`cs0`,`exp'`](Q.X_CHOOSE_THEN`cy`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
    qpat_assum`∀j k. X` kall_tac >>
    fs[Abbr`tt`,Once SWAP_REVERSE] >> strip_tac >>
    first_x_assum(qspecl_then[`rd'`,`cs0`,`ee`,`sz + 1`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE cx`]mp_tac) >>
    simp[Abbr`ee`] >>
    discharge_hyps >- (
      conj_tac >- (
        imp_res_tac Cevaluate_Clocs >> fs[] >>
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        metis_tac[LESS_LESS_EQ_TRANS]) >>
      conj_tac >- (
        imp_res_tac Cevaluate_Clocs >> fs[] ) >>
      simp[Abbr`cs0`,Abbr`bs1`] >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        Cases>>fsrw_tac[ARITH_ss][]>>
        strip_tac>>res_tac>>fsrw_tac[ARITH_ss][]) >>
      conj_tac >- (
        match_mp_tac Cenv_bs_FUPDATE >>
        qexists_tac `bs with <|code := bce; pc := next_addr bs.inst_length (bc0 ++ REVERSE cx); refs := rf|>` >>
        simp[bc_state_component_equality] >>
        match_mp_tac Cenv_bs_imp_decsz >> rfs[] >>
        qmatch_assum_abbrev_tac`Cenv_bs c rd' s' envv cenv szz bss` >>
        qexists_tac `bss` >>
        simp[bc_state_component_equality,Abbr`bss`,Abbr`szz`] >>
        spose_not_then strip_assume_tac >>
        imp_res_tac Cenv_bs_CTLet_bound >>
        DECIDE_TAC) >>
      match_mp_tac compile_labels_lemma >>
      map_every qexists_tac[`c`,`cenv`,`TCNonTail F`,`sz`,`cs`,`exp`] >>
      simp[Once SWAP_REVERSE] ) >>
    disch_then(mp_tac o SIMP_RULE (srw_ss()++DNF_ss) [] o CONJUNCT2) >>
    strip_tac >> rpt gen_tac >> strip_tac >>
    rw[] >> fs[] >> rfs[] >>
    qpat_assum`∀code bc1. X`(mp_tac o (CONV_RULE (RESORT_FORALL_CONV (op@ o partition (C mem ["args","klvs'"] o fst o dest_var))))) >>
    disch_then(qspecl_then[`v::klvs`,`args`]mp_tac) >> simp[ADD1] >>
    simp[Once SWAP_REVERSE] >>
    `bs1.code = bs.code` by rw[Abbr`bs1`] >>
    fsrw_tac[ARITH_ss][] >>
    disch_then(qspecl_then[`env0`,`defs`,`vs`]mp_tac) >>
    simp[FUPDATE_LIST_THM] >>
    fsrw_tac[DNF_ss][] >>
    simp[Abbr`bs1`] >>
    disch_then(qspecl_then[`blvs`,`st`]mp_tac o (CONV_RULE (RESORT_FORALL_CONV List.rev))) >>
    simp[] >>
    discharge_hyps >- (
      fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
      rw[] >>
      match_mp_tac(MP_CANON (GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
      simp[] >>
      qexists_tac`rd` >>
      simp[DRESTRICT_SUBSET_SUBMAP] >>
      fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,SUBMAP_DEF,DRESTRICT_DEF,UNCURRY]) >>
    simp[code_for_return_def] >>
    disch_then(qx_choosel_then[`bv2`,`rd2`,`rf2`]strip_assume_tac) >>
    map_every qexists_tac[`bv2`,`rd2`,`rf2`] >>
    simp[] >>
    conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    metis_tac[SUBMAP_TRANS,IS_PREFIX_TRANS] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def,pushret_def] >>
    Q.ISPECL_THEN[`c`,`cenv`,`sz`,`cs`,`defs`]mp_tac compile_closures_thm >>
    simp[] >>
    disch_then(Q.X_CHOOSE_THEN`cc`mp_tac) >>
    strip_tac >>
    reverse(Cases_on`∃bc10. bs.code = bc0 ++ cc ++ bc10`) >- (
      qmatch_assum_abbrev_tac`X.out = REVERSE cc ++ cs.out` >>
      conj_tac >> rpt gen_tac >>
      Q.PAT_ABBREV_TAC`tt = Y:call_context`>>
      strip_tac >>
      qspecl_then[`c`,`cenv`,`tt`,`sz`,`exp`,`0`,`X`,`LENGTH defs`]mp_tac(CONJUNCT1 (CONJUNCT2 compile_append_out)) >>
      rw[Once SWAP_REVERSE_SYM] >> fs[] ) >>
    fs[] >>
    first_x_assum(qspecl_then[`bs`,`bc0`,`bc10`,`FDOM rd.cls`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      qpat_assum`∀rd yy. Z`kall_tac >>
      fs[SUM_eq_0,MEM_MAP,GSYM LEFT_FORALL_IMP_THM,EVERY_MEM] >>
      conj_asm1_tac >- (
        Cases >> simp[] >>
        PairCases_on`x`>>strip_tac>>
        res_tac>>fs[]) >>
      asm_simp_tac(srw_ss()++QUANT_INST_ss[sum_qp])[] >>
      conj_tac >- (
        fsrw_tac[DNF_ss][MEM_EL] >>
        map_every qx_gen_tac[`l`,`i`] >> strip_tac >>
        rator_x_assum`good_code_env`mp_tac >>
        simp[good_code_env_def,FEVERY_DEF] >>
        strip_tac >> first_x_assum(qspec_then`l`mp_tac) >>
        `l ∈ FDOM c` by metis_tac[] >>
        `bs.code = bce ++ bcr` by metis_tac[] >>
        ntac 2 (pop_assum mp_tac) >> rpt (pop_assum kall_tac) >>
        rw[bc_find_loc_def] >>
        qmatch_abbrev_tac`IS_SOME X` >>
        Cases_on`X`>>rw[]>>
        fs[markerTheory.Abbrev_def] >>
        imp_res_tac(GSYM bc_find_loc_aux_NONE)>>
        fs[]) >>
      simp[LENGTH_NIL] >>
      simp[MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
      map_every qx_gen_tac[`l`,`i`] >> strip_tac >>
      simp[UNCURRY] >>
      rator_x_assum`good_code_env`mp_tac >>
      simp[good_code_env_def,FEVERY_DEF] >> strip_tac >>
      first_x_assum(qspec_then`l`mp_tac) >>
      `l ∈ FDOM c` by metis_tac[] >>
      simp[EVERY_MEM,MEM_EL,GSYM LEFT_FORALL_IMP_THM,closure_data_component_equality] >>

      free_vars_mkshift
      label_closures_thm
      bind_fv_def

      `LENGTH cenv = LENGTH env` by metis_tac[Cenv_bs_def,EVERY2_EVERY] >>
      strip_tac >>
      conj_tac >- metis_tac[] >>
      reverse conj_tac >- metis_tac[] >>
      rator_x_assum`Cenv_bs`mp_tac >>
      simp[Cenv_bs_def,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
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
      fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY] >>
      metis_tac[MEM_EL]) >>
    Q.PAT_ABBREV_TAC`ccs = compile_closures c cenv sz cs defs` >>
    first_x_assum(qspecl_then[`rd'`,`ccs`,
      `REVERSE (GENLIST(λm. CTLet (sz+m+1))(LENGTH defs)) ++ cenv`,
      `sz+(LENGTH defs)`,
      `bs1`,`bce`,`bcr`,`bc0++cc`]mp_tac) >>
    discharge_hyps >- (
      simp[] >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF,MEM_GENLIST] >>
        PROVE_TAC[] ) >>
      conj_tac >- simp[Abbr`bs1`] >>
      conj_tac >- simp[Abbr`bs1`] >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF,FOLDL_UNION_BIGUNION,LET_THM] >>
        metis_tac[LESS_IMP_LESS_ADD,ADD_SYM] ) >>
      conj_tac >- (
        match_mp_tac Cenv_bs_FUPDATE_LIST >>
        Q.PAT_ABBREV_TAC`vs = GENLIST (CRecClos env defs) Y` >>
        map_every qexists_tac[`vs`,`env`,`cenv`,`sz`] >>
        `LENGTH vs = LENGTH defs` by simp[Abbr`vs`] >>
        simp[] >>
        qexists_tac`bs1 with <| stack := bs.stack; code := bce |>` >>
        simp[bc_state_component_equality,Abbr`bs1`] >>
        reverse conj_asm2_tac >- (
          simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
          qx_gen_tac`n`>>strip_tac >>
          simp[EL_MAP,Abbr`vs`] >>
          simp[Once Cv_bv_cases] >>
          rator_x_assum`RTC`kall_tac >>
          `∃l. EL n defs = INR l` by (
            Cases_on`EL n defs`>>simp[] >>
            fs[SUM_eq_0,MEM_MAP,MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
            Cases_on`x` >>
            metis_tac[body_count_def,ADD1,ADD_SYM,SUC_NOT]) >>
          qpat_assum`bs.code = X`kall_tac >>
          qpat_assum`X = bs.code`(assume_tac o SYM) >>
          simp[FLOOKUP_DEF,el_check_def,bc_find_loc_def] >>
          simp[UNCURRY] >>
          qexists_tac`l` >> simp[] >>
          conj_tac >- metis_tac[] >>
          conj_tac >- metis_tac[] >>
          conj_tac >- metis_tac[] >>
          conj_asm2_tac >- (
            qsuff_tac`MEM (Label l) bce` >- (
              metis_tac[bc_find_loc_aux_append_code,bc_find_loc_aux_NONE,optionTheory.option_CASES,optionTheory.THE_DEF] ) >>
            fs[good_code_env_def,FEVERY_DEF] >>
            first_x_assum(qspec_then`l`mp_tac)>>
            first_x_assum(qspec_then`l`mp_tac)>>
            rw[] >> simp[] ) >>
          conj_asm1_tac >- metis_tac[] >>
          simp[Once Cv_bv_cases] >>
          qabbrev_tac`recs = FST (c ' l).ceenv` >>
          qabbrev_tac`envs = SND (c ' l).ceenv` >>
          map_every qexists_tac[`envs`,`recs`] >>
          simp[] >>
          conj_tac >- metis_tac[FST,SND,pair_CASES] >>
          reverse conj_tac >- (
            gen_tac >> strip_tac >>
            simp[EL_APPEND2,EL_MAP] >>
            Cenv_bs_def
            s_refs_def

          qpat_assum`good_ecs X Y`mp_tac >>
          simp[good_ecs_def,FEVERY_DEF] >>
          first_x_assum(qspecl_then[`xs`,`l`,`n`]mp_tac) >>
          simp[FLOOKUP_DEF] >> strip_tac >>
          disch_then(qspec_then`l`mp_tac) >>
          qpat_assum`bc_next^* bs1 bs2`kall_tac >>
          `l ∈ FDOM cd.ecs` by (
            fsrw_tac[DNF_ss][SUBSET_DEF,MEM_FILTER] >>
            first_x_assum(qspec_then`(xs,INR l)`mp_tac) >>
            simp[MEM_EL] >> metis_tac[] ) >>
          simp[] >>
          qspecl_then[`ns`,`xs`,`LENGTH xs`,`n`,`free_vars c (c ' l)`,`(FEMPTY,0,[])`]mp_tac bind_fv_thm >>
          simp[] >>
          disch_then kall_tac >>
          disch_then kall_tac >>
          Q.PAT_ABBREV_TAC`fvl:string list = SET_TO_LIST X` >>
          Q.PAT_ABBREV_TAC`envs = FILTER X fvl` >>
          qx_gen_tac`i` >> strip_tac >>
          Q.PAT_ABBREV_TAC`fv = EL i envs` >>
          `fv ∈ free_vars c (c ' l) ∧ fv ∉ set xs ∧ find_index fv ns 0 ≠ SOME n` by (
            `MEM fv envs` by (rw[MEM_EL] >> metis_tac[]) >>
            pop_assum mp_tac >>
            simp[Abbr`fv`,Abbr`envs`,Abbr`fvl`,MEM_FILTER] ) >>
          `fv ∈ free_vars (c \\ l) (c ' l)` by metis_tac[free_vars_DOMSUB,SUBSET_DEF,IN_UNION] >>
          Cases_on`find_index fv ns 0` >> simp[] >- (
            simp[EL_REVERSE,EL_MAP,PRE_SUB1] >>
            fsrw_tac[DNF_ss][FOLDL_UNION_BIGUNION_paired,SUBSET_DEF,FORALL_PROD] >>
            `¬MEM fv ns` by metis_tac[find_index_MEM] >>
            first_x_assum(qspecl_then[`fv`,`xs`,`cb`]mp_tac) >>
            simp[FLOOKUP_DEF] >>
            `MEM (xs,INR l) defs` by metis_tac[MEM_EL] >>
            simp[]>>strip_tac >>
            fs[Cenv_bs_def,fmap_rel_def,FDOM_DRESTRICT,EXTENSION] >>
            conj_asm1_tac >- PROVE_TAC[] >>
            first_x_assum(qspec_then`fv`mp_tac) >>
            simp[] >>
            BasicProvers.CASE_TAC >>
            simp[DRESTRICT_DEF] >> strip_tac >>
            match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
            qexists_tac`rd` >>
            simp[Abbr`rd'`] ) >>
          imp_res_tac find_index_LESS_LENGTH >> fs[] >>
          simp[EL_REVERSE,PRE_SUB1,EL_MAP] >>
          simp[Abbr`rd'`,FDOM_FUPDATE_LIST,MAP_GENLIST,combinTheory.o_DEF] >>
          simp[RIGHT_EXISTS_AND_THM] >>
          conj_tac >- (
            simp[MEM_GENLIST] >>
            disj2_tac >>
            Q.PAT_ABBREV_TAC`z = LENGTH defs - y`  >>
            qexists_tac`z` >>
            simp[Abbr`z`] ) >>
          qho_match_abbrev_tac`∃jenv. (((rd.cls |++ ls) ' k) = (jenv,ns,defs,x)) ∧ P jenv` >>
          qho_match_abbrev_tac`Q ((rd.cls |++ ls) ' k)` >>
          match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
          simp[Abbr`ls`,MAP_GENLIST,combinTheory.o_DEF,MEM_GENLIST,Abbr`k`] >>
          srw_tac[DNF_ss][] >>
          simp[RIGHT_EXISTS_AND_THM] >>
          conj_tac >- (
            qmatch_abbrev_tac`ALL_DISTINCT rs'` >>
            qsuff_tac`rs' = rs` >- rw[] >>
            simp[Abbr`rs'`] >>
            match_mp_tac GENLIST_EL >>
            simp[] ) >>
          Q.PAT_ABBREV_TAC`z = LENGTH defs - y`  >>
          qexists_tac`z` >>
          simp[Abbr`z`,Abbr`Q`] >>
          simp[Abbr`P`] ) >>
        match_mp_tac Cenv_bs_change_store >>
        Q.PAT_ABBREV_TAC`pc = next_addr il X` >>
        map_every qexists_tac[`rd`,`s`,`bs with <| pc := pc ; code := bce|>`] >>
        simp[bc_state_component_equality,Abbr`rd'`,Cenv_bs_with_pc] >>
        `LENGTH bvs = LENGTH rs` by rw[Abbr`bvs`] >>
        fs[Cenv_bs_def,s_refs_def] >>
        reverse conj_tac >- (
          simp[SUBMAP_DEF,DRESTRICT_DEF,FDOM_FUPDATE_LIST] >>
          rw[] >>
          match_mp_tac EQ_SYM >>
          match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
          simp[MAP_ZIP] >>
          fs[f_o_f_DEF,EXTENSION] >>
          metis_tac[] ) >>
        fs[Cenv_bs_def,s_refs_def,fmap_rel_def,good_rd_def] >>
        conj_tac >- (
          fs[FEVERY_DEF,UNCURRY,FDOM_FUPDATE_LIST] >>
          simp[MAP_GENLIST,combinTheory.o_DEF,MAP_ZIP,MEM_GENLIST] >>
          qx_gen_tac`x` >>
          Cases_on`MEM x rs` >> simp[] >- (
            disch_then kall_tac >>
            conj_tac >- (
              fs[f_o_f_DEF,EXTENSION,IN_FRANGE] >>
              metis_tac[] ) >>
            Q.PAT_ABBREV_TAC`ls = GENLIST (X:num->(num#(string |-> Cv)#string list#def list#num)) Y` >>
            qho_match_abbrev_tac`P ((rd.cls |++ ls) ' x)` >>
            match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
            `MAP FST ls = rs` by (
              simp[Abbr`ls`,MAP_GENLIST,combinTheory.o_DEF] >>
              lrw[LIST_EQ_REWRITE] ) >>
            simp[] >>
            srw_tac[DNF_ss][Abbr`ls`,MEM_GENLIST] >>
            `∃i. i < LENGTH defs ∧ (x = EL i rs)` by metis_tac[MEM_EL] >>
            qexists_tac`i`>>simp[] >>
            simp[Abbr`P`] >>
            fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
            first_x_assum ho_match_mp_tac >>
            simp[MEM_ZIP] >>
            Q.PAT_ABBREV_TAC`z = LENGTH defs - y` >>
            qexists_tac`z` >>
            simp[Abbr`z`,EL_MAP] >>
            qho_match_abbrev_tac`((bs.refs |++ ls) ' k) = X` >>
            qho_match_abbrev_tac`P ((bs.refs |++ ls) ' k)` >>
            match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
            simp[Abbr`ls`,MAP_ZIP,Abbr`P`,Abbr`X`,MEM_ZIP,Abbr`k`] >>
            qexists_tac`i`>>simp[EL_REVERSE,PRE_SUB1]) >>
          reverse strip_tac >- metis_tac[MEM_EL] >>
          Q.PAT_ABBREV_TAC`bv = (bs.refs |++ ls) ' x` >>
          Q.PAT_ABBREV_TAC`dd = (rd.cls |++ ls) ' x` >>
          qsuff_tac`(bv = bs.refs ' x) ∧ (dd = rd.cls ' x)` >- (
            strip_tac >>
            conj_tac >- metis_tac[] >>
            conj_tac >- metis_tac[] >>
            conj_tac >- metis_tac[] >>
            match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
            qexists_tac`rd` >> simp[] ) >>
          map_every qunabbrev_tac[`bv`,`dd`] >>
          conj_tac >>
          match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM >>
          simp[MAP_ZIP,MAP_GENLIST,combinTheory.o_DEF] >>
          TRY (qmatch_abbrev_tac `x ∉ set rs'` >> `rs = rs'` by lrw[Abbr`rs'`,LIST_EQ_REWRITE]) >>
          metis_tac[] ) >>
        conj_asm1_tac >- (
          fs[f_o_f_DEF,EXTENSION,FDOM_FUPDATE_LIST,MAP_ZIP] >>
          metis_tac[] ) >>
        simp[f_o_f_DEF] >>
        qx_gen_tac `x` >> strip_tac >>
        qsuff_tac`rd.sm ' x ∉ set (MAP FST (ZIP (rs,REVERSE bvs)))` >- (
          strip_tac >>
          simp[FUPDATE_LIST_APPLY_NOT_MEM,f_o_f_DEF] >>
          match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
          qexists_tac`rd` >> simp[] >>
          metis_tac[f_o_f_DEF] ) >>
        simp[MAP_ZIP] >>
        fs[f_o_f_DEF,EXTENSION] >>
        metis_tac[] ) >>
      fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
      simp[ALL_DISTINCT_APPEND,FILTER_APPEND,Abbr`ccs`] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    strip_tac >>
    conj_tac >- (
      pop_assum kall_tac >>
      pop_assum mp_tac >>
      Q.PAT_ABBREV_TAC`cenv1 = cenv |++ ls` >>
      qspecl_then[`cd`,`cenv1`,`TCNonTail F`,`sz + LENGTH ns`,`ccs`,`exp`](Q.X_CHOOSE_THEN`ce`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      disch_then(qspec_then`REVERSE ce`mp_tac) >>
      qspecl_then[`cd`,`cenv`,`TCNonTail F`,`sz`,`exp`,`0`,`ccs`,`ns`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1(CONJUNCT2 compile_append_out)) >>
      `bs1.code = bs.code` by rw[Abbr`bs1`] >>
      qspecl_then[`cd`,`cenv`,`TCNonTail F`,`sz`,`exp`,`0`,`ccs`,`ns`]mp_tac compile_bindings_thm >>
      simp[Once SWAP_REVERSE] >>
      Q.PAT_ABBREV_TAC`cenv2 = cenv |++ ls` >>
      `(cenv2 = cenv1)` by ( simp[Abbr`cenv1`,Abbr`cenv2`] ) >>
      qpat_assum`X = ce ++ ccs.out`mp_tac >>
      simp[] >> strip_tac >> strip_tac >>
      strip_tac >> gen_tac >> strip_tac >>
      fs[] >>
      qpat_assum`code_for_push rd' bs1 bce X Y Z s' c A B G D`mp_tac >>
      simp[code_for_push_def] >>
      asm_simp_tac(srw_ss()++DNF_ss)[] >>
      map_every qx_gen_tac[`rf1`,`rd1`,`bv1`] >>
      strip_tac >>
      map_every qexists_tac[`rf1`,`rd1`,`bv1`] >>
      conj_tac >- (
        qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
        qmatch_abbrev_tac`bc_next^* bs bs3` >>
        qsuff_tac `bc_next bs2 bs3` >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
        simp[bc_eval1_thm] >>
        `bc_fetch bs2 = SOME (Stack (Pops (LENGTH defs)))` by (
          match_mp_tac bc_fetch_next_addr >>
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
        match_mp_tac Cenv_bs_imp_incsz >>
        qexists_tac`bs with <| code := bce ; refs := rf1 |>` >>
        simp[bc_state_component_equality] >>
        match_mp_tac Cenv_bs_change_store >>
        map_every qexists_tac[`rd`,`s`,`bs with code := bce`] >>
        simp[bc_state_component_equality] >>
        fs[Cenv_bs_def,s_refs_def,good_rd_def,Abbr`bs1`] ) >>
      fs[Abbr`rd'`] >>
      reverse conj_tac >- metis_tac[SUBMAP_TRANS] >>
      match_mp_tac SUBMAP_TRANS >>
      qexists_tac`DRESTRICT bs1.refs (COMPL (FRANGE rd.sm))` >>
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
    pop_assum mp_tac >>
    pop_assum kall_tac >>
    Q.PAT_ABBREV_TAC`cenv1 = cenv |++ ls` >>
    strip_tac >>
    rpt gen_tac >>
    pop_assum(mp_tac o Q.SPECL[`lz + LENGTH (ns:string list)`,`az`] o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
    qspecl_then[`cd`,`cenv1`,`TCTail az (lz + LENGTH ns)`,`sz + LENGTH ns`,`ccs`,`exp`](Q.X_CHOOSE_THEN`ce`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    disch_then(qspec_then`REVERSE ce`mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
    qspecl_then[`cd`,`cenv`,`TCTail az lz`,`sz`,`exp`,`0`,`ccs`,`ns`](Q.X_CHOOSE_THEN`cb`strip_assume_tac)(CONJUNCT1(CONJUNCT2 compile_append_out)) >>
    `bs1.code = bs.code` by rw[Abbr`bs1`] >>
    qspecl_then[`cd`,`cenv`,`TCTail az lz`,`sz`,`exp`,`0`,`ccs`,`ns`]mp_tac compile_bindings_thm >>
    simp[Once SWAP_REVERSE] >>
    Q.PAT_ABBREV_TAC`cenv2 = cenv |++ ls` >>
    `(cenv2 = cenv1)` by ( simp[Abbr`cenv1`,Abbr`cenv2`] ) >>
    qpat_assum`X = ce ++ ccs.out`mp_tac >>
    simp[] >> strip_tac >> strip_tac >>
    strip_tac >> strip_tac >>
    rpt (qpat_assum`∀j k. (TCTail az lz = X) ⇒ Y`kall_tac) >>
    rfs[] >> fs[] >> rw[] >>
    fs[FOLDL_FUPDATE_LIST] >>
    first_x_assum(qspecl_then[`env0`,`ns'`,`defs'`,`xs`,`vs`]mp_tac) >>
    Q.PAT_ABBREV_TAC`klvs2 = MAP (X:string->string#Cv) ns` >>
    qpat_assum`Abbrev(bs1 = X)`mp_tac >>
    Q.PAT_ABBREV_TAC`bvs:bc_value list = REVERSE (MAP X defs)` >>
    strip_tac >>
    disch_then(qspecl_then[`(REVERSE klvs2)++klvs`,`bvs++blvs`]mp_tac) >>
    simp[Abbr`bs1`] >>
    disch_then(qspec_then`args`mp_tac) >>
    simp[] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >- simp[Abbr`klvs2`] >>
      conj_tac >- (
        fs[DISJOINT_SYM,MAP_REVERSE] >>
        simp[Abbr`klvs2`,MAP_MAP_o,combinTheory.o_DEF] >>
        qpat_assum`DISJOINT (FDOM cenv1) X`mp_tac >>
        simp[Abbr`cenv1`,FDOM_FUPDATE_LIST,MAP_ZIP,DISJOINT_SYM] ) >>
      conj_asm1_tac >- (
        simp[Abbr`klvs2`,MAP_MAP_o,combinTheory.o_DEF,ALL_DISTINCT_APPEND,MAP_REVERSE,ALL_DISTINCT_REVERSE] >>
        fs[DISJOINT_DEF,EXTENSION] >>
        metis_tac[] ) >>
      conj_tac >- (
        simp[FUPDATE_LIST_APPEND] >>
        qmatch_abbrev_tac`fm |++ l1 |++ l2 = X` >>
        match_mp_tac EQ_TRANS >>
        qexists_tac `fm |++ l2 |++ l1` >>
        conj_tac >- (
          match_mp_tac FUPDATE_LIST_APPEND_COMMUTES >>
          fs[ALL_DISTINCT_APPEND,DISJOINT_DEF,EXTENSION,Abbr`l1`,Abbr`l2`,MAP_REVERSE] >>
          metis_tac[] ) >>
        AP_THM_TAC >> AP_TERM_TAC >>
        match_mp_tac FUPDATE_LIST_ALL_DISTINCT_PERM >>
        simp[Abbr`l2`,Abbr`klvs2`,MAP_MAP_o,combinTheory.o_DEF] ) >>
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
        simp[EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
        srw_tac[DNF_ss][EL_MAP,Abbr`klvs2`,EL_REVERSE,PRE_SUB1] >>
        fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,Abbr`rd'`] >>
        first_x_assum(qspec_then`EL n rs`mp_tac) >>
        simp[FDOM_FUPDATE_LIST,MAP_GENLIST,combinTheory.o_DEF,MEM_GENLIST,MAP_ZIP] >>
        `MEM (EL n rs) rs` by metis_tac[MEM_EL] >>
        simp[] >>
        simp[TAKE_LENGTH_ID_rwt] >>
        qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
        `P` by (
          qunabbrev_tac`P` >>
          metis_tac[] ) >>
        simp[Abbr`Q`,Abbr`R`] >>
        qho_match_abbrev_tac`Q ((rd.cls |++ ls) ' (EL n rs)) ⇒ R` >>
        qho_match_abbrev_tac`Z ((rd.cls |++ ls) ' (EL n rs))` >>
        match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
        `MAP FST ls = rs` by (
          lrw[Abbr`ls`,LIST_EQ_REWRITE,MAP_GENLIST] ) >>
        simp[Abbr`ls`,MEM_GENLIST] >>
        srw_tac[DNF_ss][Abbr`Z`] >>
        qexists_tac`n`>>simp[Abbr`Q`] >>
        qho_match_abbrev_tac`Q ((bs.refs |++ (ZIP(rs,bvs))) ' (EL n rs))` >>
        match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
        simp[MAP_ZIP] >>
        simp[MEM_ZIP] >>
        srw_tac[DNF_ss][Abbr`Q`] >>
        qexists_tac`n`>>simp[Abbr`R`] >>
        simp[EL_MAP] ) >>
      fs[EVERY_MEM,FORALL_PROD] >> rw[] >>
      match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
      qexists_tac`rd` >> simp[] >>
      simp[Abbr`rd'`] ) >>
    simp[Abbr`Q`,Abbr`R`,code_for_return_def] >>
    asm_simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac[`bv1`,`rf1`,`rd1`] >>
    strip_tac >>
    map_every qexists_tac[`bv1`,`rf1`,`rd1`] >>
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
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    Cases_on`cb`>>fs[] >>
    strip_tac >>
    simp[compile_def,pushret_def] >>
    qmatch_assum_rename_tac`l ∈ FDOM c`[] >>
    conj_asm1_tac >- (
      simp[code_for_push_def] >>
      Q.ISPECL_THEN[`cd`,`cenv`,`sz`,`0`,`cs`,`[(xs,INR l)]:def list`]mp_tac compile_closures_thm >>
      simp[] >> disch_then(Q.X_CHOOSE_THEN`cx`strip_assume_tac) >>
      simp[] >>
      fsrw_tac[DNF_ss][] >> rw[] >>
      first_x_assum(qspecl_then[`bs`,`bc0`,`bc1`,`FDOM rd.cls`]mp_tac) >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac[`P`,`Q`,`R`] >>
        simp[] >>
        conj_tac >- (
          fs[good_code_env_def,FEVERY_DEF] >>
          first_x_assum(qspec_then`l`mp_tac) >>
          rw[] >>
          simp[bc_find_loc_def] >>
          qmatch_abbrev_tac`IS_SOME X` >>
          Cases_on`X`>>rw[] >>
          fs[markerTheory.Abbrev_def] >>
          pop_assum (assume_tac o SYM) >>
          imp_res_tac bc_find_loc_aux_NONE >>
          pop_assum mp_tac >>
          qpat_assum`X ++ Y = bc0 ++ cx ++ bc1`(SUBST1_TAC o SYM) >>
          simp[] ) >>
        fs[good_ecs_def,FEVERY_DEF,FLOOKUP_DEF] >> rfs[] >>
        first_x_assum(qspec_then`l`mp_tac) >>
        simp[] >> strip_tac >>
        qspecl_then[`[]`,`xs`,`LENGTH xs`,`0`,`free_vars (c \\ l) (c ' l)`,`(FEMPTY,0,[])`]mp_tac bind_fv_thm >>
        simp[] >> strip_tac >>
        simp[MEM_MAP,FORALL_PROD,EXISTS_PROD,MEM_FILTER] >>
        ntac 2 (pop_assum kall_tac) >>
        conj_tac >- (
          simp[GSYM FORALL_AND_THM] >>
          simp[GSYM IMP_CONJ_THM] >>
          rpt gen_tac >> strip_tac >>
          fsrw_tac[DNF_ss][SUBSET_DEF] >>
          qpat_assum`CEEnv fv = X`mp_tac >>
          BasicProvers.CASE_TAC >> fs[] >>
          rw[] >>
          fs[Cenv_bs_def,fmap_rel_def] >>
          first_x_assum(qspec_then`fv`mp_tac) >>
          fs[FDOM_DRESTRICT] >>
          `fv ∈ FDOM env` by (
            fsrw_tac[DNF_ss][EXTENSION] >>
            metis_tac[] ) >>
          simp[] >>
          Q.PAT_ABBREV_TAC`P = lookup_ct x y z a b` >>
          Cases_on`P`>>rw[] ) >>
        rw[] >>
        simp[find_index_def] ) >>
      simp[] >>
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      disch_then(Q.X_CHOOSE_THEN`rs`strip_assume_tac) >>
      rfs[LENGTH_NIL,FUPDATE_LIST_THM] >> rw[] >>
      pop_assum mp_tac >>
      Q.PAT_ABBREV_TAC`bv = Block 3 X` >>
      strip_tac >>
      map_every qexists_tac[`bs.refs`,`rd`,`bv`] >>
      simp[] >>
      conj_tac >- (
        simp[Once Cv_bv_cases] >>
        `MEM (Label l) bce` by (
          fs[good_code_env_def,FEVERY_DEF] >>
          first_x_assum(qspec_then`l`mp_tac) >>
          simp[] >> rw[] >> simp[] ) >>
        simp[Abbr`bv`] >>
        qpat_assum`bs.code = bc0 ++ Y`kall_tac >>
        qpat_assum`bc_next^* X Y`kall_tac >>
        fs[UNCURRY,FLOOKUP_DEF,bc_find_loc_def] >>
        conj_tac >- (
          `∃x. bc_find_loc_aux bce bs.inst_length l 0 = SOME x` by (
            Cases_on`bc_find_loc_aux bce bs.inst_length l 0`>>fs[] >>
            imp_res_tac bc_find_loc_aux_NONE >>
            fs[good_code_env_def,FEVERY_DEF] >>
            pop_assum mp_tac >>
            first_x_assum(qspec_then`l`mp_tac) >>
            rw[] >> rw[] ) >>
          imp_res_tac bc_find_loc_aux_append_code >>
          qpat_assum`X = bs.code`(assume_tac o SYM) >>
          fs[] ) >>
        qpat_assum`good_ecs x y`mp_tac >>
        simp[good_ecs_def,FEVERY_DEF] >>
        disch_then(qspec_then`l`mp_tac) >>
        simp[] >>
        qspecl_then[`[]`,`xs`,`LENGTH xs`,`0`,`free_vars (c \\ l) (c ' l)`,`(FEMPTY,0,[])`]mp_tac bind_fv_thm >>
        rw[] >>
        qpat_assum`ITSET x y z = w`kall_tac >>
        simp[Once Cv_bv_cases] >>
        `free_vars c (c ' l) = free_vars (c \\ l) (c ' l)` by (
          REWRITE_TAC[SET_EQ_SUBSET] >>
          conj_tac >- PROVE_TAC[CONJUNCT1 free_vars_DOMSUB,IN_UNION,SUBSET_DEF] >>
          PROVE_TAC[free_vars_DOMSUB_SUBSET] ) >>
        conj_tac >- simp[Abbr`ecs`,Abbr`envs`,Abbr`fvl`] >>
        qx_gen_tac`i` >>
        simp[] >> strip_tac >>
        qpat_assum`cd.ecs ' l = X`mp_tac >>
        simp[] >> strip_tac >> fs[] >> rfs[] >>
        simp[MAP_REVERSE] >>
        qabbrev_tac`fv = EL i envs` >>
        simp[find_index_def] >>
        `MEM fv envs` by (rw[MEM_EL,Abbr`fv`] >> PROVE_TAC[]) >>
        fs[Abbr`envs`,MEM_FILTER,Abbr`fvl`] >>
        `fv ∈ FDOM cenv` by fs[SUBSET_DEF] >>
        fs[Cenv_bs_def,fmap_rel_def,FDOM_DRESTRICT] >>
        `fv ∈ FDOM env` by (fs[EXTENSION] >> PROVE_TAC[] ) >>
        simp[MAP_MAP_o,EL_MAP,Abbr`ecs`] >>
        simp[find_index_def] >>
        rpt(first_x_assum(qspec_then`fv`mp_tac)) >>
        simp[] >>
        Q.PAT_ABBREV_TAC`P = lookup_ct a b X Y e` >>
        Cases_on`P`>>simp[DRESTRICT_DEF]) >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac`bs with code := bce` >>
      simp[bc_state_component_equality]) >>
    Q.ISPECL_THEN[`cd`,`cenv`,`sz`,`0`,`cs`,`[(xs,INR l)]:def list`]mp_tac compile_closures_thm >>
    simp[] >> disch_then strip_assume_tac >>
    pop_assum kall_tac >>
    fs[Once SWAP_REVERSE] >>
    rpt gen_tac >> strip_tac >> fs[] >> rw[] >>
    match_mp_tac code_for_push_return >>
    qmatch_assum_abbrev_tac`code_for_push rd bs bce bc0 code s s c ee vv cenv sz` >>
    map_every qexists_tac [`bc0`,`code`,`ee`,`cenv`,`sz`] >>
    simp[] >>
    qexists_tac`REVERSE args`>>fs[EVERY2_EVERY]) >>
  strip_tac >- (
    simp[] >> rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    simp[compile_def,FOLDL_UNION_BIGUNION] >>
    simp_tac(srw_ss()++ETA_ss)[] >>
    strip_tac >> rfs[] >> fs[] >>
    BasicProvers.VAR_EQ_TAC >>
    qspecl_then[`cd`,`cenv`,`TCNonTail F`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
    simp[GSYM FORALL_AND_THM] >> ntac 2 gen_tac >>
    Q.PAT_ABBREV_TAC`cs0 = compile cd cenv X sz cs exp` >>
    qspecl_then[`cd`,`cenv`,`sz+1`,`cs0`,`exps`](Q.X_CHOOSE_THEN`cxs`strip_assume_tac)(CONJUNCT2 (CONJUNCT2 compile_append_out)) >> fs[] >>
    reverse(Cases_on`∃bc10. code = REVERSE cx ++ REVERSE cxs ++ bc10`) >- (
      fsrw_tac[DNF_ss][] >>
      conj_tac >> rpt gen_tac >>
      rw[Once SWAP_REVERSE]) >> fs[] >>
    reverse(Cases_on`bs.code = bc0 ++ REVERSE cx ++ REVERSE cxs ++ bc10 ++ bc1`) >- fs[] >>
    fs[Once SWAP_REVERSE] >>
    POP_ASSUM_LIST(map_every assume_tac) >>
    first_x_assum(qspecl_then[`rd`,`cs`,`cd`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
    `FDOM s ⊆ FDOM s' ∧ FDOM s' ⊆ FDOM s'' ∧ FDOM s'' ⊆ FDOM s'''` by PROVE_TAC[Cevaluate_store_SUBSET,FST] >>
    fs[ALL_DISTINCT_APPEND] >>
    fs[Once SWAP_REVERSE] >>
    disch_then(mp_tac o SIMP_RULE(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] o CONJUNCT1) >>
    disch_then(qx_choosel_then[`rf`,`rd'`,`bf`]strip_assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    first_x_assum(qspecl_then[`rd'`,`cs0`,`cd`,`cenv`,`sz+1`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE cx`,`REVERSE cxs`]mp_tac) >>
    simp[Abbr`bs1`] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      simp[Abbr`cs0`] >>
      conj_tac >- PROVE_TAC[SUBSET_TRANS] >>
      conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
      match_mp_tac compile_labels_lemma >>
      map_every qexists_tac [`cd`,`cenv`,`TCNonTail F`,`sz`,`cs`,`exp`,`bc0`,`REVERSE cx`] >>
      rw[] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    disch_then(mp_tac o SIMP_RULE(srw_ss()++DNF_ss)[code_for_push_def,LET_THM]) >>
    disch_then(qx_choosel_then[`bvs`,`rfs`,`rd''`]strip_assume_tac) >>
    conj_tac >- (
      srw_tac[DNF_ss][code_for_push_def,LET_THM] >>
      qmatch_assum_abbrev_tac`Cv_bv (ps',c,l2a) cl bf` >>
      `Cv_bv (rd'', c, l2a) cl bf` by (
        match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
        qexists_tac`rd'` >>
        rw[] >>
        fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY,SUBMAP_DEF,SUBSET_DEF]) >>
      pop_assum mp_tac >>
      simp[Abbr`cl`,Once Cv_bv_cases] >>
      disch_then(qx_choosel_then[`a`,`bve`,`b`,`i'`,`l`,`xs'`]strip_assume_tac) >>
      `(i' = i) ∧ (xs' = xs)` by ( Cases_on`ns = []` >> fs[] >> rfs[]) >> rw[] >>
      fs[] >> rfs[] >> rw[] >> fs[] >> rw[] >>
      qho_match_abbrev_tac`∃rf sm bv. bc_next^* bs (bs2 rf bv) ∧ P rf sm bv` >>
      qmatch_assum_abbrev_tac`bc_next^* bs0 bs3` >>
      qmatch_assum_abbrev_tac`bc_next^* bs0 bs3` >>
      qsuff_tac `∃rf sm bv. bc_next^* bs3 (bs2 rf bv) ∧ P rf sm bv` >-
        metis_tac[RTC_TRANSITIVE,transitive_def] >>
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
      qho_match_abbrev_tac`∃rf sm bv. bc_next^* bs1 (bs2 rf bv) ∧ P rf sm bv` >>
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
      qho_match_abbrev_tac`∃rf sm bv. bc_next^* bs1 (bs2 rf bv) ∧ P rf sm bv` >>
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
      qho_match_abbrev_tac`∃rf sm bv. bc_next^* bs1 (bs2 rf bv) ∧ P rf sm bv` >>
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
      qho_match_abbrev_tac`∃rf sm bv. bc_next^* bs1 (bs2 rf bv) ∧ P rf sm bv` >>
      `bc_fetch bs1 = SOME CallPtr` by (
        match_mp_tac bc_fetch_next_addr >>
        rw[Abbr`bs1`] >>
        Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
        Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
        qexists_tac`ls ++ TAKE 4 l2` >>
        srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
      simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
      rw[bc_eval1_thm,bc_eval1_def] >>
      simp[Abbr`bs1`] >>
      fs[bc_fetch_with_stack,bump_pc_with_stack] >>
      fsrw_tac[ARITH_ss][] >>
      rw[bump_pc_def] >>
      qpat_assum`bc_fetch X = Y` kall_tac >>
      qpat_assum`bc_fetch X = Y` kall_tac >>
      Q.PAT_ABBREV_TAC`ret = x + 1` >>
      qho_match_abbrev_tac`∃rf sm bv. bc_next^* bs1 (bs2 rf bv) ∧ P rf sm bv` >>
      qpat_assum`good_code_env c d bce`(fn th => mp_tac((uncurry CONJ)((I##Q.SPEC`l`)(CONJ_PAIR(SIMP_RULE(srw_ss())[good_code_env_def,FEVERY_DEF]th)))) >> assume_tac th) >>
      fs[FLOOKUP_DEF] >>
      `cb = INR l` by ( Cases_on`ns=[]`>>fs[]>>rfs[] ) >> fs[] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      qpat_assum`X = d ' l`(assume_tac o SYM) >>
      simp[] >>
      map_every qx_gen_tac [`cdc`,`csc`,`cb0`,`cc`,`cb1`] >>
      strip_tac >>
      pop_assum (assume_tac o SYM) >>
      qmatch_assum_abbrev_tac`cdc.env_azs ' l = (enc,LENGTH vs)` >>
      first_x_assum (qspecl_then[`rd''`,`csc`,`cdc`,`enc`,`0`,`bs1`,`bce`,`bcr`,`cb0 ++ [Label l]`]mp_tac) >>
      simp[] >>
      qmatch_abbrev_tac`(X ⇒ Q) ⇒ R` >>
      `X` by (
        map_every qunabbrev_tac[`X`,`P`,`Q`,`R`] >>
        `(ns ≠ [] ⇒ i < LENGTH ns) ∧ ALL_DISTINCT ns` by (
          Cases_on`ns=[]`>>fs[] >>
          imp_res_tac find_index_LESS_LENGTH >> fs[] ) >>
        simp[FDOM_bind_fv,Abbr`enc`] >>
        conj_tac >- (
          unabbrev_all_tac >>
          fs[FLOOKUP_DEF] >> rfs[] >>
          fs[DISJOINT_DEF,EXTENSION] >> rw[] >>
          ntac 9 (pop_assum kall_tac) >>
          ntac 3 (pop_assum (qspec_then`x`mp_tac)) >>
          Cases_on `x ∈ free_vars c (c ' l)` >> fs[] >>
          Cases_on `x ∈ set (binders (c ' l))` >> fs[] >>
          qspecl_then[`c`,`c ' l`,`l`]mp_tac(CONJUNCT1 free_vars_DOMSUB) >>
          simp[SUBSET_DEF] >>
          disch_then(qspec_then`x`strip_assume_tac) >> rfs[] >>
          Cases_on`MEM x ns`>>fs[]>>
          Cases_on`MEM x ns'`>>fs[]>>
          qpat_assum`benv_bvs X Y Z ns env' defs ns' i`mp_tac >>
          simp[Once Cv_bv_cases] >> rw[] >> pop_assum mp_tac >>
          Q.PAT_ABBREV_TAC`fvs = SET_TO_LIST (free_vars X Y)` >>
          Q.PAT_ABBREV_TAC`evs = FILTER X fvs` >>
          `MEM x evs` by (
            Q.ISPECL_THEN[`ns'`,`x`,`0`]mp_tac find_index_MEM >>
            simp[Abbr`evs`,MEM_FILTER] >>
            simp[Abbr`fvs`] ) >>
          pop_assum(mp_tac o SIMP_RULE std_ss [MEM_EL]) >>
          disch_then(Q.X_CHOOSE_THEN`z` strip_assume_tac) >>
          disch_then(qspec_then`z`mp_tac) >> simp[] >>
          Q.ISPECL_THEN[`ns'`,`x`,`0`]mp_tac find_index_MEM >>
          simp[] ) >>
        conj_tac >- (
          qspecl_then[`c`,`d`,`s`,`env`,`exp`,`(s',Rval (CRecClos env' ns defs n))`]mp_tac (CONJUNCT1 Cevaluate_Clocs) >>
          qspecl_then[`c`,`d`,`s'`,`env`,`exps`,`(s'',Rval vs)`]mp_tac (CONJUNCT2 Cevaluate_Clocs) >>
          simp[] >>
          qpat_assum `LENGTH xs = LENGTH vs` mp_tac >>
          qpat_assum `FDOM s' ⊆ FDOM s''` mp_tac >>
          rpt (pop_assum kall_tac) >>
          fsrw_tac[DNF_ss][extend_rec_env_def,SUBSET_DEF,FOLDL2_FUPDATE_LIST,FOLDL_FUPDATE_LIST,MAP2_MAP,FST_pair,SND_pair,MAP_ZIP] >>
          qx_gen_tac `x` >>
          simp[FORALL_AND_THM,RIGHT_FORALL_IMP_THM] >>
          ntac 4 strip_tac >>
          simp[Once CONJ_COMM] >> simp[GSYM AND_IMP_INTRO] >>
          ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
          reverse conj_tac >-
            (srw_tac[DNF_ss][MAP_ZIP] >> PROVE_TAC[]) >>
          ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
          srw_tac[DNF_ss][MAP_MAP_o,combinTheory.o_DEF,MEM_MAP] >>
          PROVE_TAC[] ) >>
        conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
        conj_tac >- simp[Abbr`bs1`] >>
        conj_tac >- (
          fs[Abbr`bs1`,Abbr`l2a`] >>
          qspecl_then[`bce`,`bs.inst_length`,`l`,`0`]mp_tac bc_find_loc_aux_ALL_DISTINCT >>
          simp[] >>
          disch_then(qspec_then`LENGTH cb0`mp_tac) >>
          srw_tac[ARITH_ss][] >>
          pop_assum mp_tac >>
          REWRITE_TAC[GSYM APPEND_ASSOC] >>
          rw[EL_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
          simp[FILTER_APPEND] ) >>
        conj_tac >- (
          match_mp_tac Cenv_bs_bind_fv >>
          map_every qexists_tac[`env'`,`defs`,`b`,`l`,`vs`] >>
          simp[Abbr`bs1`] >>
          map_every qexists_tac[`a`,`bvs`,`bs.stack`] >>
          simp[] >>
          conj_tac >- ( fs[s_refs_def,Cenv_bs_def,good_rd_def] ) >>
          conj_tac >- (rw[] >> fs[]) >>
          conj_tac >- (rw[] >> fs[]) >>
          fs[FLOOKUP_DEF] >> rfs[] >>
          fs[Abbr`l2a`] >>
          match_mp_tac (GEN_ALL benv_bvs_free_vars_SUBSET) >>
          simp[] >> metis_tac[] ) >>
        qpat_assum`X = bce`(assume_tac o SYM) >>
        fs[ALL_DISTINCT_APPEND,FILTER_APPEND] ) >>
      simp[] >>
      map_every qunabbrev_tac[`X`,`Q`] >>
      disch_then(qspecl_then[`0`,`LENGTH vs`]mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev) o CONJUNCT2) >>
      simp[] >> simp[Once SWAP_REVERSE] >>
      simp_tac (srw_ss()++DNF_ss) [] >>
      disch_then(mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
      simp[LENGTH_NIL_SYM,FUPDATE_LIST_THM] >>
      simp_tac(srw_ss())[Abbr`bs1`]>>
      disch_then(qspecl_then[`bs.stack`,`Block 3 [CodePtr a; Block 0 bve]`,`bvs`,`vs`,`xs`,`defs`,`ns`,`env'`]mp_tac) >>
      pop_assum kall_tac >>
      `LENGTH bvs = LENGTH vs` by fs[EVERY2_EVERY] >>
      `∃bc10. bs.code = cb0 ++ [Label l] ++ REVERSE cc ++ bc10` by (
        qpat_assum`bce ++ bcr = X`(assume_tac o SYM) >>
        qpat_assum`X = bce`(assume_tac o SYM) >>
        rw[] ) >> pop_assum SUBST1_TAC >> fs[] >>
      simp[code_for_return_def,Abbr`R`] >>
      disch_then(qx_choosel_then[`bvr`,`rfr`,`smr`]strip_assume_tac) >>
      map_every qexists_tac [`rfr`,`smr`,`bvr`] >>
      simp[Abbr`bs2`] >>
      Q.PAT_ABBREV_TAC`ret' = next_addr X Y` >>
      `ret' = ret` by (
        map_every qunabbrev_tac[`ret`,`ret'`] >>
        srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND,ADD1] ) >>
      rw[] >>
      simp[Abbr`P`] >>
      reverse conj_tac >- PROVE_TAC[SUBMAP_TRANS] >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qunabbrev_tac`bs0` >>
      qmatch_assum_abbrev_tac`Cenv_bs c rd s renv cenv sz bs0` >>
      qexists_tac`bs0 with refs := rfr` >>
      simp[Abbr`bs0`,bc_state_component_equality] >>
      match_mp_tac Cenv_bs_change_store >>
      qmatch_assum_abbrev_tac`Cenv_bs c rd s renv cenv sz bs0` >>
      map_every qexists_tac[`rd`,`s`,`bs0`] >>
      simp[] >>
      fs[s_refs_def,Abbr`l2a`,good_rd_def] >>
      simp[Abbr`bs0`,bc_state_component_equality] >>
      conj_tac >- metis_tac[SUBMAP_TRANS] >>
      conj_tac >- metis_tac[SUBMAP_TRANS] >>
      fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
      metis_tac[SUBMAP_TRANS]) >>
    asm_simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac[`env0`,`ns0`,`defs0`,`xs0`,`vs0`,`klvs`,`blvs`,`benv`,`ret`,`args0`,`cl0`,`st`] >>
    simp[Once SWAP_REVERSE] >> strip_tac >>
    qmatch_assum_abbrev_tac`Cv_bv (ps',c,l2a) cl bf` >>
    `Cv_bv (rd'', c, l2a) cl bf` by (
      match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
      qexists_tac`rd'` >>
      rw[Abbr`ps'`] >>
      fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY,SUBMAP_DEF,SUBSET_DEF]) >>
    pop_assum mp_tac >>
    simp[Abbr`cl`,Once Cv_bv_cases] >>
    disch_then(qx_choosel_then[`a`,`bve`,`b`,`i'`,`l`,`xs'`]strip_assume_tac) >>
    `(i' = i) ∧ (xs' = xs) ∧ (cb = INR l)` by ( Cases_on`ns = []` >> fs[] >> rfs[]) >> rw[] >>
    fs[] >> rfs[] >> rw[] >> fs[] >> rw[] >>
    qpat_assum`good_code_env c d bce`(fn th => mp_tac((uncurry CONJ)((I##Q.SPEC`l`)(CONJ_PAIR(SIMP_RULE(srw_ss())[good_code_env_def,FEVERY_DEF]th)))) >> assume_tac th) >>
    fs[FLOOKUP_DEF] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    qpat_assum`X = d ' l`(assume_tac o SYM) >>
    simp[] >>
    map_every qx_gen_tac [`cdc`,`csc`,`cb0`,`cc`,`cb1`] >>
    strip_tac >>
    pop_assum (assume_tac o SYM) >>
    simp[code_for_return_def] >>
    qho_match_abbrev_tac`∃bv rf sm. bc_next^* bs (bs2 rf bv) ∧ P rf bv sm` >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs05` >>
    qmatch_assum_abbrev_tac`bc_next^* bs05 bs3` >>
    qsuff_tac `∃rf bv sm. bc_next^* bs3 (bs2 rf bv) ∧ P rf bv sm` >-
      metis_tac[RTC_TRANSITIVE,transitive_def] >>
    qspec_then`bs3`mp_tac jmpbc_thm >>
    simp[Abbr`bs3`] >>
    disch_then(qspecl_then[`st`,`REVERSE bvs`]mp_tac o (CONV_RULE(RESORT_FORALL_CONV List.rev))) >> simp[] >>
    disch_then(qspec_then`REVERSE args0`mp_tac) >> simp[] >>
    disch_then(qspec_then`bc1`mp_tac) >> simp[] >>
    `(LENGTH exps = LENGTH bvs) ∧ (LENGTH klvs = LENGTH blvs)` by (
      fs[EVERY2_EVERY] >> imp_res_tac Cevaluate_list_LENGTH >> fs[] ) >>
    simp[] >>
    qmatch_abbrev_tac`bc_next^* bs1 bs3 ⇒ X` >> strip_tac >>
    qsuff_tac `∃rf bv sm. bc_next^* bs3 (bs2 rf bv) ∧ P rf bv sm` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    map_every qunabbrev_tac[`X`,`bs3`,`bs1`] >>
    pop_assum kall_tac >>
    qho_match_abbrev_tac `∃rf bv sm. bc_next^* bs1 (bs2 rf bv) ∧ P rf bv sm` >>
    qmatch_assum_abbrev_tac`cdc.env_azs ' l = (enc,LENGTH vs)` >>
    first_x_assum (qspecl_then[`rd''`,`csc`,`cdc`,`enc`,`0`,`bs1`,`bce`,`bcr`,`cb0 ++ [Label l]`]mp_tac) >>
    qmatch_abbrev_tac`(X ⇒ Q) ⇒ R` >>
    `X` by (
      map_every qunabbrev_tac[`X`,`P`,`Q`,`R`] >>
      `(ns ≠ [] ⇒ i < LENGTH ns) ∧ ALL_DISTINCT ns` by (
        Cases_on`ns=[]`>>fs[] >>
        imp_res_tac find_index_LESS_LENGTH >> fs[] ) >>
      simp[FDOM_bind_fv,Abbr`enc`] >>
      conj_tac >- (
        unabbrev_all_tac >>
        fs[FLOOKUP_DEF] >> rfs[] >>
        fs[DISJOINT_DEF,EXTENSION] >> rw[] >>
        ntac 11 (pop_assum kall_tac) >>
        ntac 3 (pop_assum (qspec_then`x`mp_tac)) >>
        Cases_on `x ∈ free_vars c (c ' l)` >> fs[] >>
        Cases_on `x ∈ set (binders (c ' l))` >> fs[] >>
        qspecl_then[`c`,`c ' l`,`l`]mp_tac(CONJUNCT1 free_vars_DOMSUB) >>
        simp[SUBSET_DEF] >>
        disch_then(qspec_then`x`strip_assume_tac) >> rfs[] >>
        Cases_on`MEM x ns`>>fs[]>>
        Cases_on`MEM x ns'`>>fs[]>>
        qpat_assum`benv_bvs X Y Z ns env' defs ns' i`mp_tac >>
        simp[Once Cv_bv_cases] >> rw[] >> pop_assum mp_tac >>
        Q.PAT_ABBREV_TAC`fvs = SET_TO_LIST (free_vars X Y)` >>
        Q.PAT_ABBREV_TAC`evs = FILTER X fvs` >>
        `MEM x evs` by (
          Q.ISPECL_THEN[`ns'`,`x`,`0`]mp_tac find_index_MEM >>
          simp[Abbr`evs`,MEM_FILTER] >>
          simp[Abbr`fvs`] ) >>
        pop_assum(mp_tac o SIMP_RULE std_ss [MEM_EL]) >>
        disch_then(Q.X_CHOOSE_THEN`z` strip_assume_tac) >>
        disch_then(qspec_then`z`mp_tac) >> simp[] >>
        Q.ISPECL_THEN[`ns'`,`x`,`0`]mp_tac find_index_MEM >>
        simp[] ) >>
      conj_tac >- (
        qmatch_assum_abbrev_tac`Cevaluate c d s env exp (s',Rval (CRecClos env' ns defs n))` >>
        qspecl_then[`c`,`d`,`s`,`env`,`exp`,`(s',Rval (CRecClos env' ns defs n))`]mp_tac (CONJUNCT1 Cevaluate_Clocs) >>
        qspecl_then[`c`,`d`,`s'`,`env`,`exps`,`(s'',Rval vs)`]mp_tac (CONJUNCT2 Cevaluate_Clocs) >>
        simp[] >>
        qpat_assum `LENGTH xs = LENGTH vs` mp_tac >>
        qpat_assum `FDOM s' ⊆ FDOM s''` mp_tac >>
        rpt (pop_assum kall_tac) >>
        fsrw_tac[DNF_ss][extend_rec_env_def,SUBSET_DEF,FOLDL2_FUPDATE_LIST,FOLDL_FUPDATE_LIST,MAP2_MAP,FST_pair,SND_pair,MAP_ZIP] >>
        qx_gen_tac `x` >>
        simp[FORALL_AND_THM,RIGHT_FORALL_IMP_THM] >>
        ntac 4 strip_tac >>
        simp[Once CONJ_COMM] >> simp[GSYM AND_IMP_INTRO] >>
        ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
        reverse conj_tac >-
          (srw_tac[DNF_ss][MAP_ZIP] >> PROVE_TAC[]) >>
        ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
        srw_tac[DNF_ss][MAP_MAP_o,combinTheory.o_DEF,MEM_MAP] >>
        PROVE_TAC[] ) >>
      conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
      conj_tac >- simp[Abbr`bs1`] >>
      conj_tac >- (
        fs[Abbr`bs1`,Abbr`l2a`] >>
        qspecl_then[`bce`,`bs.inst_length`,`l`,`0`]mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        simp[] >>
        disch_then(qspec_then`LENGTH cb0`mp_tac) >>
        `EL (LENGTH cb0) bce = Label l` by (
          rw[] >> lrw[EL_APPEND2,EL_APPEND1] ) >>
        lrw[TAKE_APPEND1] >>
        simp[FILTER_APPEND] ) >>
      conj_tac >- (
        match_mp_tac Cenv_bs_bind_fv >>
        map_every qexists_tac[`env'`,`defs`,`c ' l`,`l`,`vs`] >>
        simp[Abbr`bs1`] >>
        map_every qexists_tac[`a`,`bvs`,`st`] >>
        simp[] >>
        conj_tac >- ( fs[s_refs_def,Cenv_bs_def,good_rd_def] ) >>
        conj_tac >- (rw[] >> fs[]) >>
        conj_tac >- (rw[] >> fs[]) >>
        fs[FLOOKUP_DEF] >> rfs[] >>
        fs[Abbr`l2a`] >>
        match_mp_tac (GEN_ALL benv_bvs_free_vars_SUBSET) >>
        simp[] >> metis_tac[] ) >>
      rw[] >> fs[ALL_DISTINCT_APPEND,FILTER_APPEND]) >>
    simp[] >>
    map_every qunabbrev_tac[`X`,`Q`] >>
    disch_then(qspecl_then[`0`,`LENGTH vs`]mp_tac o (CONV_RULE(RESORT_FORALL_CONV List.rev)) o CONJUNCT2) >>
    simp[Once SWAP_REVERSE] >>
    simp_tac (srw_ss()++DNF_ss) [] >>
    simp[Abbr`bs1`] >>
    disch_then(mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
    simp[LENGTH_NIL_SYM,FUPDATE_LIST_THM] >>
    disch_then(qspecl_then[`st`,`Block 3 [CodePtr a; Block 0 bve]`,`bvs`,`vs`,`xs`,`defs`,`ns`,`env'`,`cb1 ++ bcr`]mp_tac) >>
    simp[] >> pop_assum kall_tac >>
    `LENGTH bvs = LENGTH vs` by fs[EVERY2_EVERY] >>
    simp[code_for_return_def,Abbr`R`] >>
    disch_then(qx_choosel_then[`bvr`,`rfr`,`smr`]strip_assume_tac) >>
    map_every qexists_tac [`rfr`,`bvr`,`smr`] >>
    simp[Abbr`bs2`,Abbr`P`] >>
    metis_tac[SUBMAP_TRANS]) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[compile_def,pushret_def] >>
    rpt gen_tac >> strip_tac >>
    qspecl_then[`cd`,`cenv`,`TCNonTail F`,`sz`,`cs`,`exp`]strip_assume_tac (CONJUNCT1 compile_append_out) >>
    simp[Once SWAP_REVERSE] >>
    simp[Once SWAP_REVERSE] >>
    reverse(Cases_on`∃bc10. bs.code = bc0 ++ REVERSE bc ++ (prim1_to_bc uop)::bc10`) >- (
      rw[] >> fs[] ) >>
    fs[] >>
    first_x_assum(qspecl_then[`rd`,`cs`,`cd`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
    simp[Once SWAP_REVERSE] >>
    disch_then(assume_tac o CONJUNCT1) >>
    conj_asm1_tac >- (
      pop_assum mp_tac >>
      simp[code_for_push_def] >>
      fsrw_tac[DNF_ss][] >>
      map_every qx_gen_tac[`rf`,`rd'`,`bv`] >>
      strip_tac >>
      qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
      qspecl_then[`c`,`rd'`,`uop`,`s'`,`v`,`s''`,`v'`,`bs1`,`bc0 ++ REVERSE bc`,`bc10`,`bce`,`bs.stack`,`bv`]
        mp_tac prim1_to_bc_thm >>
      simp[Abbr`bs1`] >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by fs[Cenv_bs_def] >>
      simp[Abbr`Q`,Abbr`R`] >>
      disch_then(qx_choosel_then[`bvr`,`rfr`,`smr`]strip_assume_tac) >>
      map_every qexists_tac[`rfr`,`rd' with sm := smr`,`bvr`] >>
      simp[] >>
      qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
      qmatch_assum_abbrev_tac`bc_next bs1 bs2` >>
      conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
      reverse conj_tac >- metis_tac[SUBMAP_TRANS] >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac`bs with <| code := bce; refs := rfr|>`>>
      simp[bc_state_component_equality] >>
      match_mp_tac Cenv_bs_change_store >>
      map_every qexists_tac[`rd`,`s`,`bs with <| code := bce|>`]>>
      simp[bc_state_component_equality] >>
      fs[Cenv_bs_def,s_refs_def,good_rd_def,UNCURRY,FEVERY_DEF,SUBSET_DEF] >>
      metis_tac[SUBMAP_TRANS] ) >>
    srw_tac[DNF_ss][] >>
    match_mp_tac code_for_push_return >>
    qmatch_assum_abbrev_tac`code_for_push rd bs bce bc0 code s s'' c env vv renv rsz` >>
    map_every qexists_tac [`bc0`,`code`,`env`,`renv`,`rsz`] >>
    simp[Abbr`code`] >>
    qexists_tac `REVERSE args` >>
    fs[EVERY2_EVERY] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    conj_asm1_tac >- (
      rw[compile_def,LET_THM,pushret_def] >>
      qspecl_then[`cd`,`cenv`,`TCNonTail F`,`sz`,`cs`,`e1`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      qmatch_assum_abbrev_tac`cs0.out = cx ++ cs.out` >>
      qspecl_then[`cd`,`cenv`,`TCNonTail F`,`sz+1`,`cs0`,`e2`](Q.X_CHOOSE_THEN`cy`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      fs[Once SWAP_REVERSE] >>
      first_x_assum (qspecl_then[`rd`,`cs`,`cd`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
      simp[Abbr`cs0`,compile_def,Once SWAP_REVERSE] >>
      simp[code_for_push_def] >>
      disch_then (qx_choosel_then [`bvs`,`rfs`,`sms`] strip_assume_tac) >>
      fs[EVERY2_EVERY] >>
      `∃bv0 bv1. bvs = [bv0;bv1]` by (
        Cases_on `bvs` >> fs[] >>
        Cases_on `t` >> fs[LENGTH_NIL] ) >> fs[] >> rw[] >>
      fsrw_tac[DNF_ss][] >>
      qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
      qmatch_assum_abbrev_tac `Cv_bv pp v1 bv0` >>
      qspecl_then[`p2`,`v1`,`v2`,`v`,`bs0`,`bc0 ++ REVERSE cx ++ REVERSE cy`,`bc1`,`bs.stack`,`bv0`,`bv1`,`pp`]mp_tac prim2_to_bc_thm >>
      fs[Abbr`bs0`] >>
      `FST pp = sms` by rw[Abbr`pp`] >> fs[] >>
      imp_res_tac (CONJUNCT2 Cevaluate_store_SUBSET) >>
      imp_res_tac (CONJUNCT2 Cevaluate_Clocs) >> fs[] >>
      `(FDOM sms.sm = FDOM s') ∧ good_sm sms.sm` by
        fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
      simp[] >>
      disch_then (Q.X_CHOOSE_THEN`bv`strip_assume_tac) >>
      map_every qexists_tac [`rfs`,`sms`,`bv`] >> fs[] >>
      conj_tac >- (
        rw[Once RTC_CASES2] >> disj2_tac >>
        qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
        qexists_tac `bs0` >> rw[] >>
        qmatch_assum_abbrev_tac`bc_next bs0 bs11` >>
        qmatch_abbrev_tac `bc_next bs0 bs12` >>
        qsuff_tac `bs11 = bs12` >- metis_tac[bc_eval1_thm,optionTheory.SOME_11] >>
        rw[Abbr`bs11`,Abbr`bs12`] >>
        Q.PAT_ABBREV_TAC`x = Stack Y` >>
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
      match_mp_tac Cenv_bs_imp_incsz >>
      qmatch_assum_abbrev_tac `Cenv_bs c sms s' renv cenv (sz + 2) bs0` >>
      qexists_tac`bs0 with <| stack := bs.stack |>` >>
      reverse(rw[])>-(rw[bc_state_component_equality,Abbr`bs0`])>>
      match_mp_tac Cenv_bs_pops >>
      map_every qexists_tac[`[bv1;bv0]`,`bs0`] >>
      simp[Abbr`bs0`,bc_state_component_equality] >>
      metis_tac[Cenv_bs_CTLet_bound] ) >>
    fs[Once compile_def,LET_THM,pushret_def] >>
    qspecl_then[`cd`,`cenv`,`sz`,`cs`,`[e1;e2]`]strip_assume_tac(CONJUNCT2(CONJUNCT2 compile_append_out)) >>
    simp[Once SWAP_REVERSE] >> rw[] >>
    fs[Once SWAP_REVERSE] >>
    match_mp_tac code_for_push_return >>
    qmatch_assum_abbrev_tac`code_for_push sm bs bce bc0 ccode s s' c ccenv rvs renv rsz` >>
    map_every qexists_tac[`bc0`,`ccode`,`ccenv`,`renv`,`rsz`] >>
    simp[Abbr`ccode`] >>
    qexists_tac`REVERSE args`>>fs[EVERY2_EVERY]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    conj_asm1_tac >- (
      rw[compile_def,LET_THM,pushret_def] >>
      qspecl_then[`cd`,`cenv`,`TCNonTail F`,`sz`,`cs`,`e1`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      qmatch_assum_abbrev_tac`cs0.out = cx ++ cs.out` >>
      qspecl_then[`cd`,`cenv`,`TCNonTail F`,`sz+1`,`cs0`,`e2`](Q.X_CHOOSE_THEN`cy`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
      fs[Once SWAP_REVERSE] >>
      first_x_assum (qspecl_then[`rd`,`cs`,`cd`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
      simp[Abbr`cs0`,compile_def,Once SWAP_REVERSE] >>
      simp[code_for_push_def] >>
      disch_then (qx_choosel_then [`bvs`,`rfs`,`sms`] strip_assume_tac) >>
      fs[EVERY2_EVERY] >>
      `∃bv0 bv1. bvs = [bv0;bv1]` by (
        Cases_on `bvs` >> fs[] >>
        Cases_on `t` >> fs[LENGTH_NIL] ) >> fs[] >> rw[] >>
      fsrw_tac[DNF_ss][] >>
      qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
      Cases_on`v1`>>fs[]>>
      map_every qexists_tac[`rfs |+ (sms.sm ' n, bv1)`,`sms`,`Block unit_tag []`] >>
      Cases_on`n ∈ FDOM s'`>> fs[] >>
      conj_tac >- (
        match_mp_tac (SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        qexists_tac`bs0` >>
        rw[RTC_eq_NRC] >>
        qexists_tac`SUC(SUC 0)` >>
        rw[NRC] >>
        `bc_fetch bs0 = SOME Update` by (
          match_mp_tac bc_fetch_next_addr >>
          qexists_tac`bc0 ++ REVERSE cx ++ REVERSE cy` >>
          simp[Abbr`bs0`] ) >>
        simp[Once bc_eval1_thm] >>
        simp[bc_eval1_def,Abbr`bs0`] >>
        qpat_assum`Cv_bv X Y bv0`mp_tac >>
        simp[Once Cv_bv_cases] >>
        disch_then strip_assume_tac >>
        simp[] >>
        conj_tac >- (
          fs[Cenv_bs_def,s_refs_def,fmap_rel_def,f_o_f_DEF,FLOOKUP_DEF] >>
          fs[EXTENSION] >> metis_tac[] ) >>
        fs[bump_pc_def] >>
        qpat_assum`X = SOME Update`kall_tac >>
        qmatch_abbrev_tac`bc_next bs0 bs1` >>
        `bc_fetch bs0 = SOME (Stack (Cons unit_tag 0))` by (
          match_mp_tac bc_fetch_next_addr >>
          qexists_tac`bc0 ++ REVERSE cx ++ REVERSE cy ++ [Update]` >>
          simp[Abbr`bs0`,SUM_APPEND,FILTER_APPEND] ) >>
        simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def] >>
        simp[bump_pc_def,Abbr`bs0`,Abbr`bs1`,bc_state_component_equality] >>
        simp[SUM_APPEND,FILTER_APPEND] >>
        fs[FLOOKUP_DEF] ) >>
      qpat_assum`X = v`(assume_tac o SYM) >>
      qpat_assum`X = s'`(assume_tac o SYM) >>
      simp[Once Cv_bv_cases] >>
      conj_tac >- (
        match_mp_tac Cenv_bs_imp_incsz >>
        Q.PAT_ABBREV_TAC`rfs2 = rfs |+ X` >>
        qexists_tac`bs with <| code := bce; refs := rfs2|>` >>
        simp[bc_state_component_equality] >>
        match_mp_tac Cenv_bs_change_store >>
        map_every qexists_tac[`rd`,`s`,`bs with code := bce`] >>
        `FDOM (s' |+ (n,v2)) = FDOM s'` by (
          simp[EXTENSION] >> PROVE_TAC[]) >>
        simp[bc_state_component_equality] >>
        fs[Cenv_bs_def,s_refs_def,good_rd_def,FEVERY_DEF,UNCURRY] >>
        simp[Abbr`rfs2`] >>
        reverse conj_tac >- (
          simp[IN_FRANGE] >> rw[] >> PROVE_TAC[] ) >>
        simp[fmap_rel_def,f_o_f_DEF] >>
        conj_tac >- (
          fs[FAPPLY_FUPDATE_THM] >> rw[] >>
          metis_tac[IN_FRANGE] ) >>
        conj_asm1_tac >- (
          simp[EXTENSION] >>
          fs[FEVERY_DEF,UNCURRY,IN_FRANGE,Cenv_bs_def,s_refs_def,fmap_rel_def] >>
          fs[EXTENSION,f_o_f_DEF] >>
          metis_tac[] ) >>
        simp[f_o_f_DEF] >>
        simp[FAPPLY_FUPDATE_THM] >>
        gen_tac >> strip_tac >>
        Cases_on`x=n` >> simp[] >>
        `sms.sm ' x ≠ sms.sm ' n` by (
          fs[INJ_DEF] >> PROVE_TAC[] ) >>
        simp[] >>
        fs[fmap_rel_def] >>
        first_x_assum(qspec_then`x`mp_tac) >>
        simp[f_o_f_DEF] ) >>
      fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
      `sms.sm ' n ∈ FRANGE sms.sm` by (simp[IN_FRANGE] >> PROVE_TAC[]) >>
      simp[]) >>
    fs[Once compile_def,LET_THM,pushret_def] >>
    qspecl_then[`cd`,`cenv`,`sz`,`cs`,`[e1;e2]`]strip_assume_tac(CONJUNCT2(CONJUNCT2 compile_append_out)) >>
    simp[Once SWAP_REVERSE] >> rw[] >>
    fs[Once SWAP_REVERSE] >>
    match_mp_tac code_for_push_return >>
    qmatch_assum_abbrev_tac`code_for_push sm bs bce bc0 ccode s s'' c ccenv rvs renv rsz` >>
    map_every qexists_tac[`bc0`,`ccode`,`ccenv`,`renv`,`rsz`] >>
    simp[Abbr`ccode`] >>
    qexists_tac`REVERSE args`>>fs[EVERY2_EVERY]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    fs[compile_def,LET_THM] >>
    Q.PAT_ABBREV_TAC`cs0 = compile cd cenv t sz cs exp` >>
    qabbrev_tac`nl = cs0.next_label` >>
    full_simp_tac std_ss [prove(``w::x::y::cs0.out=[w;x;y]++cs0.out``,rw[])] >>
    full_simp_tac std_ss [prove(``x::y::(cs0).out=[x;y]++(cs0).out``,rw[])] >>
    Q.PAT_ABBREV_TAC`lc3 = [Label x;y]` >>
    Q.PAT_ABBREV_TAC`lc2 = [Label x;y;z]` >>
    qunabbrev_tac`cs0` >>
    qspecl_then[`cd`,`cenv`,`TCNonTail F`,`sz`,`cs`,`exp`](Q.X_CHOOSE_THEN`be1`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    qmatch_assum_abbrev_tac`cs0.out = be1 ++ cs.out` >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    simp[RIGHT_AND_FORALL_THM] >>
    CONV_TAC (RESORT_FORALL_CONV (op@ o partition (C mem ["args","klvs"] o fst o dest_var))) >>
    ntac 2 gen_tac >>
    Q.PAT_ABBREV_TAC`cs2 = compiler_result_out_fupd (K (lc2 ++ Y ++ X)) Z` >>
    Q.PAT_ABBREV_TAC`cs3 = compiler_result_out_fupd (K (lc3 ++ Y)) Z` >>
    Q.PAT_ABBREV_TAC`cs2k = compiler_result_out_fupd (K (lc2 ++ Y ++ X)) Z` >>
    Q.PAT_ABBREV_TAC`cs3k = compiler_result_out_fupd (K (X::Y)) Z` >>
    qspecl_then[`cd`,`cenv`,`TCNonTail F`,`sz`,`cs2`,`e2`](Q.X_CHOOSE_THEN`be2`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    qspecl_then[`cd`,`cenv`,`TCNonTail F`,`sz`,`cs3`,`e3`](Q.X_CHOOSE_THEN`be3`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    Q.PAT_ABBREV_TAC`tt = TCTail X Y` >>
    qspecl_then[`cd`,`cenv`,`tt`,`sz`,`cs2k`,`e2`](Q.X_CHOOSE_THEN`be2k`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    qspecl_then[`cd`,`cenv`,`tt`,`sz`,`cs3k`,`e3`](Q.X_CHOOSE_THEN`be3k`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    qabbrev_tac`tf = TCNonTail F` >>
    `(compile cd cenv tf sz cs3 e3).out = be3 ++ lc3 ++ be2 ++ lc2 ++ be1 ++ cs.out` by (
      simp[Abbr`cs3`,Abbr`cs2`]) >>
    `(compile cd cenv tt sz cs3k e3).out = be3k ++ [Label (nl + 1)] ++ be2k ++ lc2 ++ be1 ++ cs.out` by (
      simp[Abbr`cs3k`,Abbr`cs2k`]) >>
    simp[] >>
    qabbrev_tac`nl1 = nl + 1` >>
    qabbrev_tac`nl2 = nl + 2` >>
    qabbrev_tac `il = bs.inst_length` >>
    `FDOM s ⊆ FDOM s' ∧ FDOM s' ⊆ FDOM s''` by metis_tac[SUBSET_TRANS,Cevaluate_store_SUBSET,FST] >>
    rpt gen_tac >>
    simp_tac (srw_ss()) [Once SWAP_REVERSE] >>
    simp_tac (srw_ss()) [Once SWAP_REVERSE] >>
    reverse(Cases_on`∃bc10. bs.code = bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ bc10`) >- (
      rw[] >> fs[]) >>
    rpt (qpat_assum `∀j k. X ⇒ Y` kall_tac) >> fs[] >>
    POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC) >>
    first_x_assum(qspecl_then[`rd`,`cs`,`cd`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
    fs[ALL_DISTINCT_APPEND,Once SWAP_REVERSE] >>
    disch_then(CHOOSE_THEN strip_assume_tac o SIMP_RULE (srw_ss()) [code_for_push_def,LET_THM,Once Cv_bv_cases] o CONJUNCT1) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    conj_tac >- (
      rw[] >>
      Cases_on `b1` >> fs[] >- (
        first_x_assum(qspecl_then[`rd'`,`cs2`,`cd`,`cenv`,`sz`,`bs1 with <| stack := bs.stack; pc := next_addr il (bc0 ++ REVERSE be1 ++ REVERSE lc2) |>`
                                 ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2`]mp_tac) >>
        simp[Abbr`bs1`,Once SWAP_REVERSE] >>
        qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
        `P` by (
          map_every qunabbrev_tac [`P`,`Q`,`R`] >>
          conj_tac >- metis_tac[SUBSET_TRANS] >>
          conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
          conj_tac >- (
            fs[Abbr`cs2`,Abbr`cs0`] >>
            match_mp_tac Cenv_bs_imp_decsz >>
            qmatch_assum_abbrev_tac `Cenv_bs c rd' s' renv cenv (sz + 1) bs1` >>
            qexists_tac`bs1` >>
            reverse(rw[])>-(rw[bc_state_component_equality,Abbr`bs1`])>>
            imp_res_tac Cenv_bs_CTLet_bound >>
            pop_assum(qspec_then`sz+1`mp_tac) >>
            srw_tac[ARITH_ss][] ) >>
          fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2`
                          ,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP,Abbr`cs0`] >>
          rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
        simp[] >>
        map_every qunabbrev_tac [`P`,`Q`,`R`] >>
        disch_then(mp_tac o CONJUNCT1) >>
        simp_tac(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] >>
        map_every qx_gen_tac[`rfs2`,`sm2`,`b2`] >> strip_tac >>
        map_every qexists_tac[`rfs2`,`sm2`,`b2`] >>
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
          rw[Abbr`bs05`,bc_state_component_equality] >>
          rw[bc_find_loc_def] >>
          qmatch_abbrev_tac`bc_find_loc_aux ls il nl 0 = SOME (next_addr il ls0)` >>
          `∃ls1. ls = ls0 ++ ls1` by rw[Abbr`ls`,Abbr`ls0`] >>
          pop_assum SUBST1_TAC >> qunabbrev_tac`ls` >>
          match_mp_tac bc_find_loc_aux_append_code >>
          match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
          `ALL_DISTINCT (FILTER is_Label ls0)` by (
            fs[ALL_DISTINCT_APPEND,FILTER_APPEND] ) >>
          qexists_tac`LENGTH bc0 + LENGTH be1 + 2` >>
          fsrw_tac[ARITH_ss][Abbr`ls0`,Abbr`lc2`] >>
          conj_tac >- lrw[EL_DROP,EL_CONS,EL_APPEND2] >>
          lrw[TAKE_APPEND2,FILTER_APPEND] ) >>
        conj_tac >- (
          qmatch_abbrev_tac`bc_next^* bs bs13` >>
          `bc_fetch bs11 = SOME (Jump (Lab nl2))` by (
            match_mp_tac bc_fetch_next_addr >>
            simp[Abbr`bs11`,Abbr`lc3`] >>
            Q.PAT_ABBREV_TAC`ls = X ++ REVERSE be2` >>
            qexists_tac`ls` >>
            rw[] ) >>
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
                ,Abbr`nl2`,Abbr`lc2`,Abbr`lc3`,Abbr`nl1`,Abbr`cs2`,MEM_MAP,between_def,Abbr`cs0`,Abbr`cs3`] >>
              rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
            lrw[TAKE_APPEND2,EL_APPEND2,FILTER_APPEND] ) >>
          metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
        simp[Abbr`il`] >>
        conj_tac >- fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
        metis_tac[SUBMAP_TRANS] ) >>
      first_x_assum(qspecl_then[`rd'`,`cs3`,`cd`,`cenv`,`sz`,`bs1 with <| stack := bs.stack;
                                pc := next_addr il (bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2 ++ REVERSE lc3) |>`
                               ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2 ++ REVERSE lc3`]mp_tac) >>
      simp[Abbr`bs1`,Once SWAP_REVERSE] >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac[`P`,`Q`,`R`] >>
        conj_tac >- metis_tac[SUBSET_TRANS] >>
        conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
        conj_tac >- (
          match_mp_tac Cenv_bs_imp_decsz >>
          qmatch_assum_abbrev_tac `Cenv_bs c rd' s' renv cenv (sz + 1) bs1` >>
          qexists_tac`bs1` >>
          reverse(rw[])>-(rw[bc_state_component_equality,Abbr`bs1`])>>
          imp_res_tac Cenv_bs_CTLet_bound >>
          pop_assum(qspec_then`sz+1`mp_tac) >>
          srw_tac[ARITH_ss][]) >>
        simp[Abbr`cs3`] >>
        fsrw_tac[DNF_ss,ARITH_ss]
          [FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2`,Abbr`lc3`
          ,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP,Abbr`cs0`,Abbr`nl1`,Abbr`nl2`] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
      simp[] >>
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      disch_then(mp_tac o CONJUNCT1) >>
      Q.PAT_ABBREV_TAC`ls = X++cs.out` >>
      `ls = be3 ++ cs3.out` by (
        rw[Abbr`ls`,Abbr`cs3`] >>
        qunabbrev_tac`cs2` >> simp[] ) >>
      simp[Once SWAP_REVERSE] >>
      simp_tac(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] >>
      map_every qx_gen_tac[`rfs3`,`sm3`,`b3`] >> strip_tac >>
      map_every qexists_tac[`rfs3`,`sm3`,`b3`] >>
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
          fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,between_def,is_Label_rwt,MEM_FILTER,Abbr`lc2`,Abbr`nl2`]) >>
        qmatch_abbrev_tac`bc_eval1 (bump_pc bs03) = SOME bs06` >>
        `bc_fetch bs03 = SOME (JumpIf (Lab nl))` by (
          fs[bc_fetch_def,Abbr`bs03`] >> rfs[REVERSE_APPEND] ) >>
        rw[bump_pc_def] >>
        rw[Abbr`bs03`] >>
        qmatch_abbrev_tac`bc_eval1 bs03 = SOME bs06` >>
        `bc_fetch bs03 = SOME (Jump (Lab nl1))` by (
          match_mp_tac bc_fetch_next_addr >>
          rw[Abbr`bs03`,Abbr`lc2`] >>
          qexists_tac`bc0 ++ REVERSE be1 ++ [JumpIf (Lab nl)]` >>
          rw[REVERSE_APPEND,FILTER_APPEND,SUM_APPEND] >>
          srw_tac[ARITH_ss][] ) >>
        rw[bc_eval1_def] >>
        rw[Abbr`bs03`,Abbr`bs06`,Abbr`bs05`] >>
        rw[bc_state_component_equality] >>
        rw[bc_find_loc_def] >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        simp[Abbr`lc3`] >>
        Q.PAT_ABBREV_TAC`ls = X ++ REVERSE be2` >>
        qexists_tac`LENGTH ls + 1` >>
        lrw[Abbr`ls`,EL_APPEND2] >>
        lrw[TAKE_APPEND2,FILTER_APPEND] ) >>
      conj_tac >- (
        qmatch_abbrev_tac`bc_next^* bs bs08` >>
        `bs08 = bs07` by (
          rw[Abbr`bs08`,Abbr`bs07`] >>
          rw[bc_state_component_equality] >>
          rw[FILTER_APPEND] ) >>
        metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
      simp[Abbr`il`] >>
      conj_tac >- fs[Cenv_bs_def,s_refs_def,good_rd_def] >>
      metis_tac[SUBMAP_TRANS] ) >>
    rpt strip_tac >>
    Cases_on `b1` >> fs[] >- (
      first_x_assum(qspecl_then[`rd'`,`cs2k`,`cd`,`cenv`,`sz`,`bs1 with <| stack := bs.stack; pc := next_addr il (bc0 ++ REVERSE be1 ++ REVERSE lc2) |>`
                               ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2`]mp_tac) >>
      simp[Abbr`bs1`] >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac [`P`,`Q`,`R`] >>
        conj_tac >- metis_tac[SUBSET_TRANS] >>
        conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
        conj_tac >- (
          fs[Abbr`cs2k`,Abbr`cs0`] >>
          match_mp_tac Cenv_bs_imp_decsz >>
          qmatch_assum_abbrev_tac `Cenv_bs c rd' s' renv cenv (sz + 1) bs1` >>
          qexists_tac`bs1` >>
          reverse(rw[])>-(rw[bc_state_component_equality,Abbr`bs1`])>>
          imp_res_tac Cenv_bs_CTLet_bound >>
          pop_assum(qspec_then`sz+1`mp_tac) >>
          srw_tac[ARITH_ss][] ) >>
        fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2k`,Abbr`nl2`
                        ,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP,Abbr`cs0`] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
      simp[] >>
      map_every qunabbrev_tac [`P`,`Q`,`R`] >>
      disch_then(mp_tac o CONJUNCT2) >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      disch_then(mp_tac o CONV_RULE (RESORT_FORALL_CONV (op@ o partition (C mem ["args'","klvs'"] o fst o dest_var)))) >>
      disch_then(qspecl_then[`klvs`,`args`]mp_tac) >>
      fs[Abbr`tf`,Once SWAP_REVERSE] >>
      `bc10 = REVERSE be2k ++ Label nl1::(REVERSE be3k ++ bc1)` by (
        rw[] >> fs[] ) >>
      simp[] >>
      disch_then(qspecl_then[`env0`,`ns`,`defs`,`xs`,`vs`,`blvs`,`benv`,`ret`,`cl`,`st`]mp_tac) >>
      simp[] >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac [`P`,`Q`,`R`] >>
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
      simp[] >>
      map_every qunabbrev_tac [`P`,`Q`,`R`] >>
      simp[code_for_return_def] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      map_every qx_gen_tac[`bv2`,`rf2`,`sm2`] >>
      strip_tac >>
      map_every qexists_tac[`bv2`,`rf2`,`sm2`] >>
      simp[] >>
      reverse conj_tac >- metis_tac[SUBMAP_TRANS] >>
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
        fs[ALL_DISTINCT_APPEND,FILTER_APPEND] ) >>
      qexists_tac`LENGTH bc0 + LENGTH be1 + 2` >>
      fsrw_tac[ARITH_ss][Abbr`ls0`,Abbr`lc2`] >>
      conj_tac >- lrw[EL_DROP,EL_CONS,EL_APPEND2] >>
      lrw[TAKE_APPEND2,FILTER_APPEND] ) >>
    first_x_assum(qspecl_then[`rd'`,`cs3k`,`cd`,`cenv`,`sz`,`bs1 with <| stack := bs.stack;
                              pc := next_addr il (bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2k ++ [Label nl1]) |>`
                             ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2k ++ [Label nl1]`]mp_tac) >>
    simp[Abbr`bs1`,Once SWAP_REVERSE] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >- metis_tac[SUBSET_TRANS] >>
      conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
      conj_tac >- (
        match_mp_tac Cenv_bs_imp_decsz >>
        qmatch_assum_abbrev_tac `Cenv_bs c rd' s' renv cenv (sz + 1) bs1` >>
        qexists_tac`bs1` >>
        reverse(rw[])>-(rw[bc_state_component_equality,Abbr`bs1`])>>
        imp_res_tac Cenv_bs_CTLet_bound >>
        pop_assum(qspec_then`sz+1`mp_tac) >>
        srw_tac[ARITH_ss][]) >>
      simp[Abbr`cs3k`] >>
      fsrw_tac[DNF_ss,ARITH_ss]
        [FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2k`,Abbr`lc3`,Abbr`tt`,Abbr`tf`
        ,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP,Abbr`cs0`,Abbr`nl1`,Abbr`nl2`] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    disch_then(mp_tac o CONJUNCT2) >>
    simp_tac(srw_ss()++DNF_ss)[Abbr`tt`] >>
    disch_then(mp_tac o CONV_RULE (RESORT_FORALL_CONV (op@ o partition (C mem ["args'","klvs'"] o fst o dest_var)))) >>
    disch_then(qspecl_then[`klvs`,`args`]mp_tac) >>
    simp[] >>
    `bc10 = REVERSE be2k ++ Label nl1::(REVERSE be3k ++ bc1)` by (
      rw[] >> fs[] ) >>
    simp[Abbr`cs3k`] >>
    disch_then(qspec_then`REVERSE be3k`mp_tac) >>
    simp[Abbr`cs2k`] >>
    disch_then(qspecl_then[`env0`,`ns`,`defs`,`xs`,`vs`,`blvs`,`benv`,`ret`,`cl`,`st`]mp_tac) >>
    simp[] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac [`P`,`Q`,`R`] >>
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
    simp[] >>
    map_every qunabbrev_tac [`P`,`Q`,`R`] >>
    simp[code_for_return_def] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac[`bv2`,`rf2`,`sm2`] >>
    strip_tac >>
    map_every qexists_tac[`bv2`,`rf2`,`sm2`] >>
    simp[] >>
    reverse conj_tac >- metis_tac[SUBMAP_TRANS] >>
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
    `bc_fetch bs1 = SOME (Jump (Lab nl1))` by (
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
      fs[ALL_DISTINCT_APPEND,FILTER_APPEND] ) >>
    qunabbrev_tac`ls2` >>
    Q.PAT_ABBREV_TAC`ls2 = X ++ REVERSE be2k` >>
    qexists_tac`LENGTH ls2` >>
    lrw[EL_APPEND2,TAKE_APPEND2,FILTER_APPEND] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[] >>
    simp[code_for_push_def,compile_def] >>
    rw[Once SWAP_REVERSE] >>
    map_every qexists_tac[`bs.refs`,`rd`] >>
    rw[RTC_eq_NRC] >>
    TRY (qexists_tac`0` >>rw[]) >>
    TRY (qmatch_abbrev_tac `Cenv_bs c rd A B C D E` >>
         qmatch_assum_abbrev_tac `Cenv_bs c rd A B C D E'` >>
         qsuff_tac`E = E'`>-rw[] >>
         unabbrev_all_tac) >>
    rw[bc_state_component_equality]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def] >> strip_tac >>
    qspecl_then[`cd`,`cenv`,`TCNonTail F`,`sz`,`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`cs0.out = be ++ cs.out` >>
    qspecl_then[`cd`,`cenv`,`sz+1`,`cs0`,`exps`]mp_tac(CONJUNCT2(CONJUNCT2 compile_append_out)) >>
    disch_then(Q.X_CHOOSE_THEN`bes`strip_assume_tac) >>
    POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC) >>
    first_x_assum(qspecl_then[`rd`,`s'`,`v`,`cs`,`cd`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`]mp_tac) >>
    `FDOM s ⊆ FDOM s' ∧
     FDOM s' ⊆ FDOM s''` by PROVE_TAC[SUBSET_TRANS,Cevaluate_store_SUBSET,FST] >>
    simp[] >>
    fs[ALL_DISTINCT_APPEND] >>
    fs[Once SWAP_REVERSE] >>
    rfs[Abbr`cs0`] >>
    fs[REVERSE_APPEND] >>
    disch_then(mp_tac o CONJUNCT1) >>
    `code = REVERSE be ++ REVERSE bes` by (
      PROVE_TAC[SWAP_REVERSE,REVERSE_APPEND] ) >>
    fs[] >>
    simp[code_for_push_def] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`rfs`,`rd'`,`bv`] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    qmatch_assum_abbrev_tac`cs0.out = be ++ cs.out` >>
    first_x_assum(qspecl_then[`rd'`,`cs0`,`cd`,`cenv`,`sz+1`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE be`,`REVERSE bes`]mp_tac) >>
    simp[Abbr`bs1`] >>
    qmatch_abbrev_tac `(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >- PROVE_TAC[SUBSET_TRANS] >>
      conj_tac >- PROVE_TAC[Cevaluate_Clocs,FST] >>
      match_mp_tac compile_labels_lemma >> fs[Abbr`cs0`] >>
      map_every qexists_tac[`cd`,`cenv`,`TCNonTail F`,`sz`,`cs`,`exp`,`bc0`] >>
      simp[]) >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >> fs[] >>
    simp[code_for_push_def] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`bvs`,`rf`,`rd''`] >>
    strip_tac >>
    map_every qexists_tac[`bv::bvs`,`rf`,`rd''`] >>
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
      qmatch_abbrev_tac `Cenv_bs c rd'' s2 renv env0 sz0 bsx` >>
      qmatch_assum_abbrev_tac `Cenv_bs c rd'' s2 renv env0 sz0 bsy` >>
      `bsx = bsy` by (
        rw[Abbr`bsx`,Abbr`bsy`,bc_state_component_equality,REVERSE_APPEND] ) >>
      rw[] ) >>
    metis_tac[SUBMAP_TRANS]) >>
  strip_tac >- rw[] >>
  rw[] )

val _ = export_theory ()
