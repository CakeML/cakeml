open HolKernel boolLib bossLib lcsymtacs
open miscLib bvlTheory bvlbTheory sptreeTheory alistTheory pairTheory listTheory arithmeticTheory rich_listTheory pred_setTheory
val _ = new_theory"bvl_to_bvlb"
val _ = ParseExtras.temp_tight_equality()

val bbComp_def = tDefine"bbComp"`
  bbComp ((Var n):bvl_exp) = ((Var n):bvl_exp) ∧
  bbComp (If e1 e2 e3) = If (bbComp e1) (bbComp e2) (bbComp e3) ∧
  bbComp (Let es e) = Let (MAP bbComp es) (bbComp e) ∧
  bbComp (Raise e) = Raise (bbComp e) ∧
  bbComp (Handle e1 e2) = Handle (bbComp e1) (bbComp e2) ∧
  bbComp (Tick e) = Tick (bbComp e) ∧
  bbComp (Call n loc es) = Call n loc (MAP bbComp es) ∧
  bbComp (Op op es) = Let (MAP bbComp es) (Op op (REVERSE (GENLIST Var (LENGTH es))))`
(WF_REL_TAC`measure bvl_exp_size` >> simp[bvl_exp_size_def] >>
 rpt conj_tac >> rpt gen_tac >>
 Induct_on`es`>> simp[bvl_exp_size_def] >> rw[] >> res_tac >>
 simp[bvl_exp_size_def])

val bbComp_code_def = Define`
  bbComp_code = fromAList o MAP (λ(p,(n,e)). (p,(n,bbComp e))) o toAList`

val dec_clock_with_code = prove(
  ``dec_clock n (s with code := y) =
    (dec_clock n s) with code := y``,
  rw[dec_clock_def])

val dec_clock_code = prove(
  ``(dec_clock n s).code = s.code``,
  rw[dec_clock_def])

val lookup_bbComp_code = prove(
  ``lookup loc (bbComp_code c) =
    OPTION_MAP (λ(a,b). (a, bbComp b)) (lookup loc c)``,
  rw[bbComp_code_def,lookup_fromAList] >>
  simp[SIMP_RULE std_ss [UNCURRY,LAMBDA_PROD](Q.ISPEC`λ(n,e). (n,bbComp e)`ALOOKUP_MAP)] >>
  simp[ALOOKUP_toAList])

val find_code_bbComp_code = prove(
  ``find_code x y (bbComp_code c) =
    OPTION_MAP (λ(a,b). (a, bbComp b)) (find_code x y c)``,
  Cases_on`x` >> rw[find_code_def,lookup_bbComp_code] >>
  BasicProvers.CASE_TAC >> simp[] >>
  BasicProvers.CASE_TAC >> fs[] >> rw[] >>
  BasicProvers.CASE_TAC >> fs[] >> rw[] >>
  BasicProvers.CASE_TAC >> fs[] >> rw[])

val _ = augment_srw_ss[rewrites[dec_clock_with_code,dec_clock_code,find_code_bbComp_code]]

val bbEval_REVERSE_GENLIST_Var = prove(
  ``∀n a env.
    n = LENGTH a ⇒
    bbEval (REVERSE (GENLIST Var n),a++env,s) =
      (Result (REVERSE a),s)``,
  Induct>>simp[LENGTH_NIL_SYM,bbEval_def]>>
  Cases>>rw[GENLIST,REVERSE_SNOC]>>
  rw[Once bbEval_CONS,bbEval_def] >>
  fsrw_tac[ARITH_ss][] >>
  first_x_assum(qspecl_then[`TAKE(LENGTH t)(h::t)`,`DROP(LENGTH t)(h::t)++env`]mp_tac) >>
  simp[] >> rw[LENGTH_NIL] >>
  `LENGTH t ≠ 0` by simp[LENGTH_NIL] >>
  simp[LIST_EQ_REWRITE,ADD1] >>
  Cases >> simp[EL_REVERSE,EL_TAKE,PRE_SUB1,ADD1,EL_CONS,EL_APPEND1])

val bEvalOp_with_code = store_thm("bEvalOp_with_code",
  ``domain ls = domain s.code ⇒
    (bEvalOp op vs (s with code := ls) =
     OPTION_MAP (λ(x,y). (x,y with code := ls)) (bEvalOp op vs s))``,
  strip_tac >>
  rw[bEvalOp_def] >>
  Cases_on`op`>>simp[] >> fs[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[])

val domain_bbComp_code = prove(
  ``domain (bbComp_code s) = domain s``,
  rw[bbComp_code_def,domain_fromAList,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
  simp[EXTENSION,domain_lookup,MEM_MAP,EXISTS_PROD,MEM_toAList])

val bbComp_correct = store_thm("bbComp_correct",
  ``∀xs env s res s'.
      bEval (xs,env,s) = (res,s') ⇒
      bbEval (MAP bbComp xs,env,s with code := bbComp_code s.code) = (res,s' with code := bbComp_code s'.code)``,
  recInduct bEval_ind >>
  simp[bEval_def,bbComp_def,bbEval_def,ETA_AX] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  TRY (
    imp_res_tac bEval_IMP_LENGTH >>
    CHANGED_TAC(simp[bbEval_REVERSE_GENLIST_Var]) >>
    simp[bEvalOp_with_code,domain_bbComp_code] >>
    BasicProvers.CASE_TAC >> fs[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    imp_res_tac bEvalOp_const >>
    rw[]) >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.CASE_TAC >> fs[])

val _ = export_theory()
