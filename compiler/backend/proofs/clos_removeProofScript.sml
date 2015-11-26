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
  TRY ( qcase_tac`Let` >>
    reverse every_case_tac >> fs[] >> rw[] >>
    rpt(first_assum(split_applied_pair_tac o lhs o concl) >> fs[]) >> rw[]
    >- metis_tac[compat_let] >>
    cheat ) >>
  TRY ( qcase_tac`Fn` >> cheat ) >>
  TRY ( qcase_tac`Letrec` >> cheat ) >>
  metis_tac[compat]);

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
