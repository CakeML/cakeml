open preamble
open ml_translatorLib ml_hol_kernelTheory holKernelProofTheory
open bigStepTheory
open terminationTheory

val _ = new_theory"ml_hol_init"

val _ = Globals.max_print_depth := 20

val obviously_pure_dec_def = Define`
  obviously_pure_dec (Dlet _ (Fun _ _)) = T ∧
  obviously_pure_dec (Dlet _ _) = F ∧
  obviously_pure_dec _ = T`

val with_same_defined_types = Q.prove(
  `x with defined_types := x.defined_types = x`,
  rw[semanticPrimitivesTheory.state_component_equality])
val _ = augment_srw_ss[rewrites[with_same_defined_types]]

val evaluate_pure_decs = store_thm("evaluate_pure_decs",
  ``∀decs ck mn env st x y z.
    EVERY obviously_pure_dec decs ∧
    evaluate_decs ck mn env st decs (x,y,Rval z) ⇒
      x = (st with defined_types := x.defined_types)``,
  Induct >>
  simp[Once evaluate_decs_cases] >>
  Cases >> simp[obviously_pure_dec_def] >- (
    Cases_on`e`>>simp[obviously_pure_dec_def] >>
    simp[Once evaluate_dec_cases] >>
    simp[Once evaluate_cases] >>
    simp[PULL_EXISTS] >>
    Cases_on`p` >> simp[pmatch_def] >> rw[] >>
    Cases_on`r`>>fs[semanticPrimitivesTheory.combine_dec_result_def] >>
    res_tac >> fs[] ) >>
  simp[PULL_EXISTS,Once evaluate_dec_cases] >> rw[] >>
  Cases_on`r`>>fs[semanticPrimitivesTheory.combine_dec_result_def] >>
  res_tac >> fs[] )

val drop_10_pure = prove(
  ``EVERY obviously_pure_dec (DROP 10 ml_hol_kernel_decls)``,
  ONCE_REWRITE_TAC[ml_hol_kernel_decls] >>
  EVAL_TAC)

val ml_hol_kernel_decls_split =
  Q.ISPECL[`10:num`,`ml_hol_kernel_decls`]TAKE_DROP |> SYM
  |> CONV_RULE(RAND_CONV(LAND_CONV(RAND_CONV(REWR_CONV ml_hol_kernel_decls) THENC EVAL)))

val kernel_init_thm = store_thm("kernel_init_thm",
  ``∃refs.
      HOL_STORE (Tmod_state "Kernel" ml_hol_kernel_decls).refs refs ∧
      STATE init_ctxt refs``,
  mp_tac (CONJUNCT1 kernel_thm) >>
  simp[Once evaluate_top_cases] >> strip_tac >>
  pop_assum mp_tac >>
  qpat_abbrev_tac`env:v environment = X` >>
  qpat_abbrev_tac`st:unit state = X` >>
  qpat_abbrev_tac`tys = Tmod_tys X Y` >>
  qpat_abbrev_tac`res = Tmod_env X Y` >>
  last_assum SUBST1_TAC >>
  ONCE_REWRITE_TAC[ml_hol_kernel_decls_split] >>
  ONCE_REWRITE_TAC[evaluate_decs_cases] >> rw[] >>
  rator_x_assum`evaluate_dec`mp_tac >>
  ONCE_REWRITE_TAC[evaluate_dec_cases] >>
  CONV_TAC(LAND_CONV EVAL) >> rw[] >>
  `env.c = (SND (THE (prim_sem_env empty_state.ffi))).c` by METIS_TAC[markerTheory.Abbrev_def] >>
  pop_assum mp_tac >>
  simp_tac (srw_ss()) [initSemEnvTheory.prim_sem_env_eq,initialProgramTheory.prim_sem_env_def] >>
  strip_tac >>
  ntac 9 (
    qpat_assum`Rval X = Y`mp_tac >>
    Cases_on`r`>> CONV_TAC(LAND_CONV EVAL) >> strip_tac >>
    rator_x_assum`evaluate_decs`mp_tac >>
    CONV_TAC(LAND_CONV EVAL) >>
    ONCE_REWRITE_TAC[evaluate_decs_cases] >>
    ONCE_REWRITE_TAC[evaluate_dec_cases] >>
    CONV_TAC(LAND_CONV EVAL) >> rw[] ) >>
  qpat_assum`Rval X = Y`mp_tac >>
  Cases_on`r`>> CONV_TAC(LAND_CONV EVAL) >> strip_tac >>
  imp_res_tac evaluate_pure_decs >>
  pop_assum(mp_tac o C MATCH_MP drop_10_pure) >>
  rw[] >>
  rpt (
    (rator_x_assum`evaluate_list`mp_tac ORELSE
     rator_x_assum`evaluate`mp_tac) >>
    ONCE_REWRITE_TAC[evaluate_cases] >>
    CONV_TAC(LAND_CONV EVAL) >> rw[] ) >>
  ntac 9 ( pop_assum mp_tac >> CONV_TAC(LAND_CONV EVAL) >> rw[] ) >>
  `st.refs = []` by (
    simp[Abbr`st`] >>
    simp[initSemEnvTheory.prim_sem_env_eq,initialProgramTheory.prim_sem_env_def] ) >>
  rw[ml_monadTheory.HOL_STORE_def] >>
  rw[ml_monadTheory.isRefv_def] >>
  qexists_tac`<|
    the_type_constants := [(strlit"bool",0);(strlit"fun",2:num)];
    the_term_constants := [(strlit"=",Fun(Tyvar(strlit"A"))(Fun(Tyvar(strlit"A"))Bool))];
    the_axioms := [];
    the_context := init_ctxt |>` >>
  qpat_assum`s2 = _` SUBST1_TAC >>
  EVAL_TAC >> rw[PULL_EXISTS])

val _ = export_theory()
