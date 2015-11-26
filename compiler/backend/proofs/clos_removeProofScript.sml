open preamble clos_relationTheory clos_removeTheory;

val _ = new_theory"clos_removeProof";

val _ = Parse.bring_to_front_overload"Let"{Name="Let",Thy="closLang"};

val remove_correct = Q.store_thm("remove_correct",
  `∀es es' s.
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
  metis_tac[compat])

val _ = export_theory();
