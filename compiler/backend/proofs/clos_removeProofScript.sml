open preamble closPropsTheory clos_relationTheory clos_removeTheory;

val _ = new_theory"clos_removeProof";

val _ = Parse.bring_to_front_overload"Let"{Name="Let",Thy="closLang"};

val remove_correct = Q.store_thm("remove_correct",
  `∀es es' s.
    every_Fn_vs_NONE es ⇒
    remove es = (es',s) ⇒
    exp_rel (:'ffi) es es'`,
  ho_match_mp_tac remove_ind >>
  rw[remove_def] >> fs[LET_THM] >>
  rpt(first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >>
  imp_res_tac remove_SING >>
  rpt var_eq_tac >> fs[] >>
  TRY ( qcase_tac`Let` >> cheat (*
    reverse every_case_tac >> fs[] >> rw[] >>
    rpt(first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >> rw[]
    >- metis_tac[compat_let] >>
    simp[exp_rel_def, exec_rel_rw, evaluate_ev_def] >>
    qx_genl_tac [`i`, `env1`, `env2`, `s1`, `s2`] >>
    strip_tac >> simp[closSemTheory.evaluate_def] >>
    cheat *)) >>
  TRY ( qcase_tac`Letrec` >> cheat ) >>
  metis_tac[compat]);

val k_intro = Q.prove(`(λn. x) = K x`, simp[FUN_EQ_THM])

val code_locs_const_0 = Q.store_thm("code_locs_const_0[simp]",
  `code_locs [const_0] = []`,
  EVAL_TAC)

val code_locs_REPLICATE_const_0 = Q.store_thm("code_locs_REPLICATE_const_0[simp]",
  `code_locs (REPLICATE n const_0) = []`,
  Induct_on`n`>>rw[REPLICATE,code_locs_def]>>
  rw[code_locs_cons])

val remove_distinct_locs = Q.store_thm("remove_distinct_locs",
  `∀es.
    set (code_locs (FST (remove es))) ⊆ set (code_locs es) ∧
    (ALL_DISTINCT (code_locs es) ⇒ ALL_DISTINCT (code_locs (FST (remove es))))`,
  ho_match_mp_tac remove_ind >>
  rw[remove_def,code_locs_def] >>
  fs[code_locs_def,LET_THM] >>
  imp_res_tac remove_SING >> fs[] >>
  fs[ALL_DISTINCT_APPEND,SUBSET_DEF] >> rfs[] >>
  TRY (
    fs[Once code_locs_cons,code_locs_def] >>
    simp[ALL_DISTINCT_APPEND] >>
    metis_tac[] ) >>
  rw[]>>
  fs[code_locs_def,LET_THM] >>
  simp[ALL_DISTINCT_APPEND] >>
  TRY(metis_tac[]) >>
  unabbrev_all_tac >>
  fs[MEM_GENLIST,PULL_EXISTS,MAP_MAP_o,o_DEF,UNCURRY] >>
  fs[MEM_MAP,PULL_EXISTS,code_locs_map,MEM_FLAT,EXISTS_PROD] >- (
    metis_tac[FST,SND,remove_SING,SING_HD,PAIR,LENGTH,ONE] ) >>
  conj_tac >- (
    rpt(pop_assum mp_tac) >>
    qspec_tac(`LENGTH fns`,`z`) >>
    gen_tac >> ntac 10 strip_tac >>
    Induct_on`fns` >> fs[ALL_DISTINCT_APPEND] >>
    Cases >> fs[] >> rw[] >>
    fs[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
    TRY (
      fsrw_tac[DNF_ss][] >>
      qcase_tac`ALL_DISTINCT (FLAT _)` >>
      first_x_assum (match_mp_tac o MP_CANON) >>
      fs[ALL_DISTINCT_GENLIST] >>
      ONCE_REWRITE_TAC[CONJ_ASSOC] >>
      conj_tac >- metis_tac[DECIDE``x < y ⇒ x < SUC y``] >>
      metis_tac[DECIDE``x < y ⇒ x < SUC y``]) >>
    metis_tac[FST,SND,remove_SING,SING_HD,PAIR,LENGTH,ONE]) >>
  metis_tac[FST,SND,remove_SING,SING_HD,PAIR,LENGTH,ONE]);

val every_Fn_vs_NONE_const_0 = Q.store_thm("every_Fn_vs_NONE_const_0[simp]",
  `every_Fn_vs_NONE [const_0]`,
  EVAL_TAC)

val every_Fn_vs_NONE_remove = Q.store_thm("every_Fn_vs_NONE_remove",
  `∀es es' s.
   every_Fn_vs_NONE es ⇒
   remove es = (es',s) ⇒
   every_Fn_vs_NONE es'`,
  ho_match_mp_tac remove_ind >>
  rw[remove_def] >> fs[LET_THM] >>
  rpt(first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >>
  imp_res_tac remove_SING >>
  rpt var_eq_tac >> fs[] >>
  every_case_tac >> fs[] >> rw[] >>
  rpt(first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >> rw[] >>
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] >>
  simp[EVERY_REPLICATE,EVERY_MAP,UNCURRY] >>
  simp[GSYM every_Fn_vs_NONE_EVERY] >>
  simp[EVERY_MEM,FORALL_PROD] >> rw[] >>
  fsrw_tac[QUANT_INST_ss[pair_default_qp]][] >>
  res_tac >>
  fs[Once every_Fn_vs_NONE_EVERY,EVERY_MAP,EVERY_MEM] >>
  metis_tac[remove_SING,HD,SND,PAIR]);

val every_Fn_SOME_const_0 = Q.store_thm("every_Fn_SOME_const_0[simp]",
  `every_Fn_SOME [const_0]`,
  EVAL_TAC)

val every_Fn_SOME_remove = Q.store_thm("every_Fn_SOME_remove",
  `∀es es' s.
   every_Fn_SOME es ⇒
   remove es = (es',s) ⇒
   every_Fn_SOME es'`,
  ho_match_mp_tac remove_ind >>
  rw[remove_def] >> fs[LET_THM] >>
  rpt(first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >>
  imp_res_tac remove_SING >>
  rpt var_eq_tac >> fs[] >>
  every_case_tac >> fs[] >> rw[] >>
  rpt(first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >> rw[] >>
  ONCE_REWRITE_TAC[every_Fn_SOME_EVERY] >>
  simp[EVERY_REPLICATE,EVERY_MAP,UNCURRY] >>
  simp[GSYM every_Fn_SOME_EVERY] >>
  simp[EVERY_MEM,FORALL_PROD] >> rw[] >>
  fsrw_tac[QUANT_INST_ss[pair_default_qp]][] >>
  res_tac >>
  fs[Once every_Fn_SOME_EVERY,EVERY_MAP,EVERY_MEM] >>
  metis_tac[remove_SING,HD,SND,PAIR]);

val _ = export_theory();
