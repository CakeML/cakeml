open preamble;
open clos_relationTheory clos_relationPropsTheory closPropsTheory clos_mtiTheory;
open closSemTheory

val _ = new_theory "clos_mtiProof";

val collect_args_correct = Q.prove (
`!num_args e num_args' e' e''.
  collect_args num_args e = (num_args', e') ∧
  exp_rel (:'ffi) [e'] [e'']
  ⇒
  exp_rel (:'ffi) [Fn NONE NONE num_args e] [Fn NONE NONE num_args' e'']`,
 ho_match_mp_tac collect_args_ind >>
 srw_tac[][collect_args_def]
 >- metis_tac [fn_add_arg, exp_rel_trans, exp_rel_refl] >>
 metis_tac [compat]);

val collect_apps_correct = Q.prove (
`!args e args' e' e''.
  collect_apps args e = (args', e') ∧
  exp_rel (:'ffi) [e'] [e''] ∧
  exp_rel (:'ffi) args' args''
  ⇒
  exp_rel (:'ffi) [App NONE e args] [App NONE e'' args'']`,
 ho_match_mp_tac collect_apps_ind >>
 srw_tac[][collect_apps_def]
 >- (
   `exp_rel (:'ffi) [App NONE (App NONE e es) args] [App NONE e (args++es)]`
   by (
     match_mp_tac app_combine >>
     simp [exp_rel_refl]) >>
   metis_tac [exp_rel_trans]) >>
 metis_tac [compat]);

val collect_args_max_app = Q.store_thm(
  "collect_args_max_app",
  `∀e e' n n'. n ≤ max_app ∧ collect_args n e = (n', e') ⇒ n' ≤ max_app`,
  Induct >> simp[collect_args_def] >> rpt gen_tac >>
  rename1 `Fn opt1 opt2 nn body` >>
  Cases_on `opt1` >> Cases_on `opt2` >>
  simp[collect_args_def] >> rw[] >> metis_tac[]);

val collect_args_never_decreases = Q.store_thm(
  "collect_args_never_decreases",
  `∀e e' n n'. collect_args n e = (n', e') ⇒ n ≤ n'`,
  Induct >> simp[collect_args_def] >> rpt gen_tac >>
  rename1 `Fn opt1 opt2 nn body` >>
  Cases_on `opt1` >> Cases_on `opt2` >>
  simp[collect_args_def] >> rw[] >> res_tac >> simp[]);

val check_loc_NONE_increases = Q.store_thm(
  "check_loc_NONE_increases",
  `check_loc locopt NONE n m p ∧ n ≤ n' ⇒ check_loc locopt NONE n' m p`,
  Cases_on `locopt` >> simp[closSemTheory.check_loc_def]);

val check_loc_second_NONE = Q.store_thm(
  "check_loc_second_NONE",
  `check_loc locopt NONE nps nargs sofar ⇔ locopt = NONE ∧ nargs ≤ max_app`,
  Cases_on `locopt` >> simp[closSemTheory.check_loc_def]);

val option_CASE_NONE_T = Q.store_thm(
  "option_CASE_NONE_T",
  `option_CASE x T f ⇔ x = NONE ∨ ∃y. x = SOME y ∧ f y`,
  Cases_on `x` >> simp[]);

val dest_closure_Recclosure_EQ_NONE = Q.store_thm(
  "dest_closure_Recclosure_EQ_NONE",
  `dest_closure locopt (Recclosure loc argE cloE fns i) args = NONE ⇔
     LENGTH fns ≤ i ∨ FST (EL i fns) ≤ LENGTH argE ∨
     ¬check_loc locopt (lift ($+ (2*i)) loc) (FST (EL i fns))
         (LENGTH args) (LENGTH argE)`,
  simp[dest_closure_def, UNCURRY] >> rw[] >>
  Cases_on `LENGTH fns ≤ i` >> simp[] >>
  Cases_on `FST (EL i fns) ≤ LENGTH argE` >> simp[]);


(*

(* play with a concrete intro_multi example and their respective evaluations *)
val e1 = ``Letrec NONE NONE [(1, Fn NONE NONE 1 (Op (Const 3) []))] (Var 0)``
val intro_multi_e2 = EVAL ``intro_multi [^e1]``

val exp_rel = ASSUME ``exp_rel (:'ffi) [^e1] ^(rhs (concl intro_multi_e2))``

val result =
    exp_rel |> SIMP_RULE (srw_ss()) [exp_rel_def]
            |> Q.SPEC `i`
            |> Q.SPECL [`env`, `env`, `s`, `s`]
            |> SIMP_RULE (srw_ss()) [val_rel_refl, state_rel_refl]
            |> SIMP_RULE (srw_ss()) [exec_rel_rw, evaluate_ev_def]
            |> Q.SPEC `i`
            |> SIMP_RULE (srw_ss() ++ ARITH_ss)
                  [evaluate_def, LET_THM, closLangTheory.max_app_def]
            |> SIMP_RULE (srw_ss())
                 [res_rel_rw, state_rel_refl, val_rel_rw, is_closure_def,
                  check_closures_def, clo_can_apply_def,
                  clo_to_num_params_def, clo_to_partial_args_def,
                  rec_clo_ok_def, clo_to_loc_def, option_CASE_NONE_T]
            |> Q.SPECL [`j`, `[v1;v2]`, `[v1;v2]`, `s2`, `s2`]
            |> SIMP_RULE (srw_ss())
                 [val_rel_refl, state_rel_refl,
                  option_case_NONE_F, dest_closure_Recclosure_EQ_NONE,
                  check_loc_second_NONE, closLangTheory.max_app_def]
            |> SIMP_RULE (srw_ss()) [dest_closure_def, LET_THM,
                                     check_loc_second_NONE,
                                     closLangTheory.max_app_def,
                                     exec_rel_rw, evaluate_ev_def]
            |> UNDISCH_ALL
            |> Q.SPEC `0`
            |> SIMP_RULE (srw_ss()) [evaluate_def, closLangTheory.max_app_def,
                                     dest_closure_def, check_loc_second_NONE]
*)


(* IH is unhelpful here because of the way application to multiple arguments
   gets split across two evaluations in the evaluate_ev-Exp1 case:
     1. the body gets evaluated in an environment including the other
        recursive functions
     2. if the function now has more arguments, then these are available when
        the body is evaluated, and less are available when the evaluate_app
        gets called.
     3. The IH saying that the recclosure bodies are exp-related is not
        pertinent because the respective bodies are evaluated in environments
        of different lengths
*)
val dest_addarg_Fn_def = Define`
  (dest_addarg_Fn n (Fn NONE NONE m body) =
     if n + m ≤ max_app (* ∧ 0 < m *) then SOME (m, body) else NONE) ∧
  (dest_addarg_Fn _ _ = NONE)
`;
val _ = augment_srw_ss [rewrites [dest_addarg_Fn_def]]

val dest_addarg_Fn_EQ_SOME = Q.store_thm(
  "dest_addarg_Fn_EQ_SOME",
  `dest_addarg_Fn n e = SOME (m, body) ⇔
    e = Fn NONE NONE m body ∧ n + m ≤ max_app (* ∧ 0 < m *)`,
  Cases_on `e` >> simp[] >> rename1 `Fn opt1 opt2` >>
  Cases_on `opt1` >> Cases_on `opt2` >> simp[] >> metis_tac[ADD_COMM]);

val TAKE_EQ_NIL = Q.store_thm(
  "TAKE_EQ_NIL",
  `∀l n. TAKE n l = [] ⇔ n = 0 ∨ l = []`,
  Induct >> simp[] >> rw[]);

val DISJ_CONG = Q.prove(
  `(~q ⇒ (p = p')) ⇒ (~p' ⇒ (q = q')) ⇒ (p ∨ q ⇔ p' ∨ q')`,
  DECIDE_TAC);

val nonnil_length = Q.prove(
  `v ≠ [] ⇒ LENGTH v ≠ 0`,
  Cases_on `v` >> simp[]);

val DROP_TAKE_APPEND_DROP = Q.store_thm(
  "DROP_TAKE_APPEND_DROP",
  `∀l n m. n ≤ m ⇒ DROP n (TAKE m l) ++ DROP m l = DROP n l`,
  Induct >> simp[] >> rw[]);

val app_rw_closure = save_thm(
  "app_rw_closure",
  prove(
    mk_imp(``0n < numargs ∧ LENGTH (cargs:closSem$v list) < numargs``,
           concl evaluate_app_rw
                 |> strip_forall |> #2 |> rand
                 |> Term.subst [``f:closSem$v`` |->
                                  ``Closure NONE cargs clo numargs b``,
                                ``loc_opt : num option`` |->
                                   ``NONE : num option``]),
    Cases_on `args`
    >- simp[evaluate_def, dest_closure_def, check_loc_second_NONE,
            dec_clock_def] >>
    simp[evaluate_app_rw]))

val exp_rel_exec_rel_Exp1 = Q.store_thm(
  "exp_rel_exec_rel_Exp1",
  `state_rel i s1 s2 ∧ LIST_REL (val_rel (:'a) i) E1 E2 ∧
   LIST_REL (val_rel (:'a) i) A1 A2 ∧
   exp_rel (:'a) [e1] [e2] ⇒
   exec_rel i (Exp1 NONE e1 E1 A1 n, (s1:'a closSem$state))
              (Exp1 NONE e2 E2 A2 n, s2)`,
  strip_tac >>
  simp[exec_rel_rw, evaluate_ev_def] >> qx_gen_tac `k` >> strip_tac >>
  reverse (rw[])
  >- (simp[res_rel_rw] >> metis_tac[DECIDE ``0n≤x``, val_rel_mono]) >>
  qpat_assum `exp_rel (:'a) _ _` mp_tac >> simp[exp_rel_thm] >>
  disch_then
    (qspecl_then [`i`, `E1`, `E2`, `s1`, `s2`, `k - (n - 1)`] mp_tac) >>
  simp[]>>
  simp[SimpL ``$==>``, res_rel_cases] >> strip_tac >> simp[]
  >- (imp_res_tac evaluate_SING >> fs[] >>
      Cases_on `A1 = []`
      >- fs[evaluate_def, res_rel_rw] >>
      irule res_rel_evaluate_app >> simp[] >> imp_res_tac evaluate_clock >>
      fs[] >> irule val_rel_mono_list >> qexists_tac `i` >> simp[])
  >- simp[res_rel_rw])

val recClosure_add_arg0 = Q.prove(
  `LIST_REL (λ(n,e) (n',e').
               case dest_addarg_Fn n e of
                   SOME(m,e0) => exp_rel (:'ffi) [e0] [e'] ∧ n' = n + m
                 | NONE => n = n' ∧ exp_rel (:'ffi) [e] [e'])
            fns1 fns2 ⇒
   ∀j i CE1 CE2 AE1 AE2.
     j ≤ i ∧
     LIST_REL (val_rel (:'ffi) i) CE1 CE2 ∧
     LIST_REL (val_rel (:'ffi) i) AE1 AE2
    ⇒
     LIST_REL (val_rel (:'ffi) j)
        (GENLIST (Recclosure NONE AE1 CE1 fns1) (LENGTH fns1))
        (GENLIST (Recclosure NONE AE2 CE2 fns2) (LENGTH fns1)) ∧
     (∀pfx1 sfx1 vs2 fidx m fina1 fib01 fina2 fib2.
        fidx < LENGTH fns1 ∧ EL fidx fns1 = (fina1, Fn NONE NONE m fib01) ∧
        fina1 + m ≤ max_app ∧ LENGTH pfx1 < m ∧
        EL fidx fns2 = (fina2, fib2) ∧
        LENGTH sfx1 + LENGTH AE1 = fina1 ∧
        LIST_REL (val_rel (:'ffi) i) (pfx1 ++ sfx1) vs2 ⇒
        val_rel (:'ffi) j
          (Closure NONE pfx1
                   (sfx1 ++ AE1 ++
                    GENLIST (Recclosure NONE [] CE1 fns1) (LENGTH fns1) ++
                    CE1)
                   m
                   fib01)
          (Recclosure NONE (vs2 ++ AE2) CE2 fns2 fidx))`,
  strip_tac >> completeInduct_on `j` >> rpt strip_tac
  >- (simp[LIST_REL_EL_EQN] >> qx_gen_tac `fidx` >> strip_tac >>
      `∃fina1 fib1 fina2 fib2.
          EL fidx fns1 = (fina1,fib1) ∧ EL fidx fns2 = (fina2,fib2)`
        by metis_tac[pair_CASES] >>
      `LENGTH fns2 = LENGTH fns1 ∧ LENGTH AE2 = LENGTH AE1 ∧
       LENGTH CE2 = LENGTH CE1` by fs[LIST_REL_EL_EQN] >>
      `fina1 ≤ fina2`
        by (qpat_assum `LIST_REL _ fns1 fns2` mp_tac >> simp[LIST_REL_EL_EQN] >>
            disch_then (qspec_then `fidx` mp_tac) >> simp[] >>
            `dest_addarg_Fn fina1 fib1 = NONE ∨
                ∃m b. dest_addarg_Fn fina1 fib1 = SOME(m,b)`
              by metis_tac[option_CASES, pair_CASES] >> simp[]) >>
      simp[val_rel_rw] >> conj_tac
      >- simp[check_closures_def, clo_can_apply_def] >>
      simp[dest_closure_def, revdroprev, revtakerev, check_loc_second_NONE] >>
      qx_genl_tac [`k`, `vs1`, `vs2`, `s1`, `s2`, `locopt`] >>
      Cases_on `locopt` >> simp[] >> strip_tac >>
      `LENGTH vs2 = LENGTH vs1` by fs[LIST_REL_EL_EQN] >>
      Cases_on `LENGTH vs1 ≤ max_app` >> simp[] >>
      Cases_on `LENGTH AE1 < fina1` >> simp[] >>
      Cases_on `LENGTH AE1 + LENGTH vs1 < fina1` >> simp[]
      >- (simp[exec_rel_rw, evaluate_ev_def] >> qx_gen_tac `kk` >> strip_tac >>
          reverse (rw[]) >> simp[res_rel_rw]
          >- metis_tac[val_rel_mono, DECIDE ``0n ≤ x``] >>
          reverse conj_tac
          >- (irule (last (CONJUNCTS val_rel_mono)) >> qexists_tac `k` >>
              simp[]) >>
          first_x_assum (qspec_then `kk - (LENGTH vs1 - 1)` mp_tac) >> simp[] >>
          disch_then
            (qspecl_then [`k`, `CE1`, `CE2`, `vs1 ++ AE1`, `vs2 ++ AE2`]
                         mp_tac) >>
          simp[] >> impl_tac
          >- (conj_tac
              >- (irule val_rel_mono_list >> qexists_tac `i` >> simp[]) >>
              irule EVERY2_APPEND_suff >> simp[] >> irule val_rel_mono_list >>
              qexists_tac `i` >> simp[]) >>
          simp[LIST_REL_EL_EQN]) >>
      Cases_on `LENGTH AE1 + LENGTH vs1 < fina2` >> simp[]
      >- ((* recursive closure 2 is still partially applied *)
          simp[exec_rel_rw, evaluate_ev_def] >> qx_gen_tac `kk` >> strip_tac >>
          reverse (Cases_on `fina1 ≤ kk + (LENGTH AE1 + 1)`) >> simp[]
          >- (simp[res_rel_rw] >> metis_tac[val_rel_mono, DECIDE ``0n≤x``]) >>
          `fina1 < fina2` by simp[] >>
          qmatch_assum_abbrev_tac `LIST_REL (UNCURRY Rf) fns1 fns2` >>
          `UNCURRY Rf (fina1,fib1) (fina2,fib2)`
            by metis_tac[LIST_REL_EL_EQN] >>
          pop_assum mp_tac >> simp[Abbr`Rf`, option_case_NONE_F] >>
          simp[dest_addarg_Fn_EQ_SOME, FORALL_PROD, PULL_EXISTS] >>
          rpt strip_tac >> rename1 `fina2 = fina1 + m` >>
          rename1 `exp_rel (:'ffi) [fib01] [fib2]` >>
          simp[evaluate_def] >> reverse (Cases_on `LENGTH vs1 ≤ kk + 1`) >>
          simp[]
          >- (simp[evaluate_app_rw, TAKE_EQ_NIL, dest_closure_def,
                   check_loc_second_NONE] >>
              simp[res_rel_rw] >> metis_tac[val_rel_mono, DECIDE ``0n≤x``]) >>
          simp[app_rw_closure, dest_closure_def, check_loc_second_NONE,
               dec_clock_def] >>
          simp[res_rel_rw] >> reverse conj_tac
          >- (irule (last (CONJUNCTS val_rel_mono)) >> qexists_tac `k` >>
              simp[]) >>
          `0 < LENGTH vs1` by (Cases_on `vs1` >> fs[]) >>
          first_x_assum (qspec_then `kk + 1 - LENGTH vs1` mp_tac) >> simp[] >>
          disch_then (qspecl_then [`k`, `CE1`, `CE2`, `AE1`, `AE2`] mp_tac) >>
          simp[] >> impl_tac
          >- (`k ≤ i` by decide_tac >> metis_tac [val_rel_mono_list]) >>
          disch_then (irule o CONJUNCT2) >> simp[TAKE_DROP]) >>
      simp[exec_rel_rw, evaluate_ev_def] >> qx_gen_tac `kk` >> strip_tac >>
      reverse (Cases_on `fina1 ≤ kk + (LENGTH AE1 + 1)`) >> simp[]
      >- (simp[res_rel_rw] >> metis_tac[DECIDE``0n≤x``,val_rel_mono]) >>
      Cases_on `fina2 = fina1`
      >- (rveq >> simp[] >>
          qmatch_assum_abbrev_tac `LIST_REL (UNCURRY Rf) fns1 fns2` >>
          `UNCURRY Rf (fina1,fib1) (fina1,fib2)`
            by metis_tac[LIST_REL_EL_EQN] >>
          pop_assum mp_tac >> simp[Abbr`Rf`] >>
          `dest_addarg_Fn fina1 fib1 = NONE ∨
             ∃m fib0. dest_addarg_Fn fina1 fib1 = SOME(m,fib0)`
            by metis_tac[pair_CASES,option_CASES]
          >- (simp[] >> simp[exp_rel_def, exec_rel_rw, evaluate_ev_def] >>
              disch_then
               (qspecl_then [`k`,
                             `DROP (LENGTH AE1 + LENGTH vs1 - fina1) vs1 ++
                              AE1 ++
                              GENLIST (Recclosure NONE [] CE1 fns1)
                                      (LENGTH fns1) ++
                              CE1`,
                             `DROP (LENGTH AE1 + LENGTH vs1 - fina1) vs2 ++
                              AE2 ++
                              GENLIST (Recclosure NONE [] CE2 fns2)
                                      (LENGTH fns1) ++
                              CE2`, `s1`, `s2`] mp_tac) >>
              simp[] >> impl_tac
              >- (rpt (irule EVERY2_APPEND_suff)
                  >- (irule EVERY2_DROP >> simp[])
                  >- (`k ≤ i` by simp[] >> metis_tac[val_rel_mono_list])
                  >- (fs[PULL_FORALL, IMP_CONJ_THM] >> fs[FORALL_AND_THM] >>
                      first_x_assum irule >> simp[] >> qexists_tac `i` >>
                      simp[])
                  >- (`k ≤ i` by simp[] >> metis_tac[val_rel_mono_list])) >>
              disch_then (qspec_then `kk + (LENGTH AE1 + 1) - fina1` mp_tac) >>
              simp[] >> simp[SimpL ``$==>``, res_rel_cases] >> strip_tac >>
              simp[]
              >- (imp_res_tac evaluate_SING >> fs[] >>
                  qmatch_abbrev_tac `res_rel (evaluate_app _ _ args1 _) _` >>
                  Cases_on `args1 = []`
                  >- (fs[Abbr`args1`, TAKE_EQ_NIL]
                      >- (`fina1 = LENGTH AE1 + LENGTH vs1` by simp[] >> fs[] >>
                          simp[res_rel_rw]) >>
                      fs[]) >>
                  fs[Abbr`args1`, TAKE_EQ_NIL] >> rw[] >>
                  irule res_rel_evaluate_app >> simp[TAKE_EQ_NIL] >>
                  irule EVERY2_TAKE >> irule val_rel_mono_list >>
                  qexists_tac `k` >> simp[] >> imp_res_tac evaluate_clock >>
                  fs[])
              >- simp[res_rel_rw]) >>
          simp[] >> fs[dest_addarg_Fn_EQ_SOME] >>
          strip_tac >> `m = 0` by simp[] >> rveq >> fs[] >>
          simp[evaluate_def]) >>
      `fina1 < fina2` by simp[] >>
      qmatch_assum_abbrev_tac `LIST_REL (UNCURRY Rf) fns1 fns2` >>
      `UNCURRY Rf (fina1,fib1) (fina2,fib2)`
        by metis_tac[LIST_REL_EL_EQN] >>
      pop_assum mp_tac >> simp[Abbr`Rf`, option_case_NONE_F] >>
      simp[dest_addarg_Fn_EQ_SOME, FORALL_PROD, PULL_EXISTS] >>
      rpt strip_tac >> rename1 `fina2 = fina1 + m` >>
      rename1 `fib1 = Fn NONE NONE m fib01` >>
      simp[evaluate_def, evaluate_app_rw, TAKE_EQ_NIL, dest_closure_def,
           check_loc_second_NONE, revtakerev, revdroprev] >>
      Cases_on `kk + (LENGTH AE1 + 1) < fina1 + m` >> simp[]
      >- (simp[res_rel_rw] >> metis_tac[DECIDE ``0n≤x``,val_rel_mono]) >>
      simp[TAKE_TAKE, DROP_TAKE_APPEND_DROP] >>
      qpat_assum `exp_rel (:'ffi) _ _` mp_tac >>
      simp[exp_rel_thm, dec_clock_def] >>
      qabbrev_tac `N = LENGTH AE1 + LENGTH vs1 - (fina1 + m)` >>
      qabbrev_tac `
        Recs = λce fns. GENLIST (Recclosure NONE [] ce fns) (LENGTH fns1)` >>
      simp[] >>
      disch_then (qspecl_then [`k`, `DROP N vs1 ++ AE1 ++ Recs CE1 fns1 ++ CE1`,
                               `DROP N vs2 ++ AE2 ++ Recs CE2 fns2 ++ CE2`,
                               `s1`, `s2`,
                               `kk + (LENGTH AE1 + 1) - (fina1 + m)`]
                              mp_tac) >> simp[] >>
      impl_tac
      >- (rpt (irule EVERY2_APPEND_suff) >> simp[EVERY2_DROP]
          >- (irule val_rel_mono_list >> qexists_tac `i` >> simp[])
          >- (simp[Abbr`Recs`] >> first_x_assum (qspec_then `k` mp_tac) >>
              simp[] >> disch_then (qspec_then `i` mp_tac) >> simp[])
          >- (irule val_rel_mono_list >> qexists_tac `i` >> simp[])) >>
      simp[SimpL ``$==>``, res_rel_cases] >> strip_tac >> simp[]
      >- (imp_res_tac evaluate_SING >> fs[] >>
          Cases_on `TAKE N vs1 = []` >> fs[TAKE_EQ_NIL]
          >- simp[res_rel_rw]
          >- fs[]
          >- (irule res_rel_evaluate_app >> simp[TAKE_EQ_NIL] >>
              irule EVERY2_TAKE >> irule val_rel_mono_list >>
              qexists_tac `k` >> simp[] >> imp_res_tac evaluate_clock >> fs[]))
      >- simp[res_rel_rw]) >>
  `LENGTH fns2 = LENGTH fns1 ∧ LENGTH CE2 = LENGTH CE1 ∧
   LENGTH AE2 = LENGTH AE1` by fs[LIST_REL_EL_EQN] >>
  simp[val_rel_rw, check_closures_def, clo_can_apply_def] >>
  `LENGTH vs2 = LENGTH pfx1 + LENGTH sfx1` by fs[LIST_REL_EL_EQN] >> simp[] >>
  `fina2 = fina1 + m ∧ exp_rel (:'ffi) [fib01] [fib2]`
     by (qpat_assum `LIST_REL _ fns1 fns2` mp_tac >>
         simp[LIST_REL_EL_EQN] >>
         disch_then (qspec_then `fidx` mp_tac) >> simp[]) >> simp[] >>
  qx_genl_tac [`k`, `vv1`, `vv2`, `s1`, `s2`, `locopt`] >>
  Cases_on `locopt` >>
  simp[dest_closure_def, check_loc_second_NONE] >> strip_tac >>
  `LENGTH vv2 = LENGTH vv1` by fs[LIST_REL_EL_EQN] >>
  Cases_on `LENGTH vv1 ≤ max_app` >>
  simp[revtakerev, revdroprev] >>
  Cases_on `LENGTH pfx1 + LENGTH vv1 < m` >> simp[]
  >- (simp[exec_rel_rw, evaluate_ev_def] >> qx_gen_tac `kk` >> strip_tac >>
      reverse (rw[res_rel_rw])
      >- metis_tac[val_rel_mono, DECIDE``0n≤x``]
      >- (irule (last (CONJUNCTS val_rel_mono)) >> qexists_tac `k` >> simp[]) >>
      simp[] >> first_x_assum (qspec_then `kk - (LENGTH vv1 - 1)` mp_tac) >>
      simp[] >>
      disch_then (qspecl_then [`k`, `CE1`, `CE2`, `AE1`, `AE2`] mp_tac) >>
      simp[] >> impl_tac
      >- (`k ≤ i` by simp[] >> metis_tac[val_rel_mono_list]) >>
      disch_then (irule o CONJUNCT2) >> simp[] >>
      REWRITE_TAC [GSYM APPEND_ASSOC] >> irule EVERY2_APPEND_suff >> simp[] >>
      `k ≤ i` by simp[] >> metis_tac[val_rel_mono_list]) >>
  simp[exec_rel_rw, evaluate_ev_def] >> qx_gen_tac `kk` >> strip_tac >>
  rveq >> simp[] >> reverse (Cases_on `m ≤ kk + (LENGTH pfx1 + 1)`) >>
  simp[res_rel_rw] >- metis_tac[DECIDE ``0n≤x``, val_rel_mono] >>
  qpat_assum `exp_rel (:'ffi) _ _` mp_tac >>
  simp[exp_rel_thm, dec_clock_def] >>
  qabbrev_tac `N = LENGTH pfx1 + LENGTH vv1 - m` >>
  qabbrev_tac `
    Recs = λce fns. GENLIST (Recclosure NONE [] ce fns) (LENGTH fns1)` >>
  simp[] >>
  disch_then
    (qspecl_then [`k`,
                  `DROP N vv1 ++ pfx1 ++ sfx1 ++ AE1 ++ Recs CE1 fns1 ++ CE1`,
                  `DROP N vv2 ++ vs2 ++ AE2 ++ Recs CE2 fns2 ++ CE2`,
                  `s1`, `s2`,
                   `kk + (LENGTH pfx1 + 1) - m`]
                 mp_tac) >> simp[] >>
  impl_tac
  >- (`k ≤ i` by simp[] >> reverse (irule EVERY2_APPEND_suff)
      >- metis_tac[val_rel_mono_list] >>
      reverse (irule EVERY2_APPEND_suff)
      >- (simp[Abbr`Recs`] >> first_x_assum (qspec_then `k` mp_tac) >>
          simp[] >> disch_then (qspec_then `i` mp_tac) >> simp[]) >>
      reverse (irule EVERY2_APPEND_suff)
      >- metis_tac[val_rel_mono_list] >>
      REWRITE_TAC [GSYM APPEND_ASSOC] >> irule EVERY2_APPEND_suff >>
      simp[EVERY2_DROP] >> metis_tac[val_rel_mono_list]) >>
  simp[SimpL ``$==>``, res_rel_cases] >> strip_tac >> simp[]
  >- (imp_res_tac evaluate_SING >> fs[] >>
      Cases_on `TAKE N vv1 = []` >> fs[TAKE_EQ_NIL]
      >- simp[res_rel_rw]
      >- fs[]
      >- (irule res_rel_evaluate_app >> simp[TAKE_EQ_NIL] >>
          irule EVERY2_TAKE >> irule val_rel_mono_list >>
          qexists_tac `k` >> simp[] >> imp_res_tac evaluate_clock >> fs[]))
  >- simp[res_rel_rw])

val recClosure_add_arg_lem = save_thm(
  "recClosure_add_arg_lem",
  recClosure_add_arg0 |> UNDISCH
                      |> SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]
                      |> CONJUNCT1 |> DISCH_ALL
                      |> SIMP_RULE bool_ss [PULL_FORALL, AND_IMP_INTRO])

val recClosure_add_arg = Q.store_thm(
  "recClosure_add_arg",
  `LIST_REL
       (λ(n,e) (n',e').
          case dest_addarg_Fn n e of
            NONE => n = n' ∧ exp_rel (:'ffi) [e] [e']
          | SOME (m,e0) => exp_rel (:'ffi) [e0] [e'] ∧ n' = n + m) fns1
       fns2 ∧
   exp_rel (:'ffi) [body1] [body2] ⇒
   exp_rel (:'ffi) [Letrec NONE NONE fns1 body1] [Letrec NONE NONE fns2 body2]`,
  strip_tac >> simp[exp_rel_thm, evaluate_def] >> rpt strip_tac >>
  reverse (Cases_on `EVERY (λ(n,e). n ≤ max_app ∧ n ≠ 0) fns1`) >> simp[] >>
  `EVERY (λ(n,e). n ≤ max_app ∧ n ≠ 0) fns2`
    by (fs[EVERY_MEM, MEM_EL, LIST_REL_EL_EQN, FORALL_PROD, PULL_EXISTS] >>
        rfs[] >> rpt gen_tac >> strip_tac >>
        rename1 `(n2,b2) = EL fidx fns2` >>
        qpat_assum `(n2,b2) = _` (assume_tac o SYM) >>
        `∃n1 b1. EL fidx fns1 = (n1,b1)` by metis_tac[pair_CASES] >>
        `n1 ≠ 0 ∧ n1 ≤ max_app` by metis_tac[] >>
        last_x_assum (qspec_then `fidx` mp_tac) >> simp[] >>
        `dest_addarg_Fn n1 b1 = NONE ∨
            ∃m1 b01. dest_addarg_Fn n1 b1 = SOME(m1,b01)`
          by metis_tac[pair_CASES, option_CASES] >> simp[] >>
        fs[dest_addarg_Fn_EQ_SOME]) >>
  simp[] >> qpat_assum `exp_rel (:'ffi) _ _` mp_tac >>
  simp[exp_rel_thm] >> disch_then irule >> qexists_tac `i` >> simp[] >>
  irule EVERY2_APPEND_suff >> simp[] >>
  `LENGTH fns2 = LENGTH fns1` by (imp_res_tac LIST_REL_LENGTH >> simp[]) >>
  simp[] >> irule recClosure_add_arg_lem >> simp[] >> qexists_tac `i` >> simp[])

val mti_letrec1_def = Define`
  (mti_letrec1 (m, Fn NONE NONE n b) =
     if m + n ≤ max_app then (m + n, b)
     else (m, Fn NONE NONE n b)) ∧
  (mti_letrec1 me = me)
`;
val _ = export_rewrites ["mti_letrec1_def"]

val mti_letrec1_size_decrease = Q.store_thm(
  "mti_letrec1_size_decrease",
  `mti_letrec1 (m, b) = (n,b') ∧ (m ≠ n ∨ b' ≠ b) ⇒ exp_size b' < exp_size b`,
  Cases_on `b` >> simp[Cong DISJ_CONG] >>
  rename1 `Fn opt1 opt2` >> Cases_on `opt1` >> Cases_on `opt2` >>
  simp[Cong DISJ_CONG] >> rw[] >>
  simp[Cong DISJ_CONG, closLangTheory.exp_size_def]);

val mti_letrec1_size_LEQ = Q.store_thm(
  "mti_letrec1_size_LEQ",
  `exp_size (SND (mti_letrec1 (n,b))) ≤ exp_size b`,
  Cases_on `b` >> simp[] >> rename1 `Fn opt1 opt2` >>
  Cases_on `opt1` >> Cases_on `opt2` >> simp[] >> rw[] >>
  simp[closLangTheory.exp_size_def]);

val mti_letrec1_unchangedE_unchangedN = Q.store_thm(
  "mti_letrec1_unchangedE_unchangedN",
  `mti_letrec1 (n,b) = (m,b) ⇒ n = m`,
  Cases_on `b` >> simp[] >> rename1 `Fn opt1 opt2` >>
  map_every Cases_on [`opt1`, `opt2`] >> simp[] >> rw[] >>
  pop_assum (mp_tac o AP_TERM ``closLang$exp_size``) >>
  simp[closLangTheory.exp_size_def]);

val mti_letrec_def = tDefine "mti_letrec" `
  mti_letrec m b =
   let (n',b') = mti_letrec1 (m, b)
   in
     if b = b' then (m,b) else mti_letrec n' b'`
  (WF_REL_TAC `measure (exp_size o SND)` >>
   metis_tac[SND, mti_letrec1_size_decrease])

val collect_args_mti_letrec = Q.store_thm(
  "collect_args_mti_letrec",
  `∀n e. collect_args n e = mti_letrec n e`,
  ho_match_mp_tac collect_args_ind >> simp[collect_args_def] >> rpt conj_tac >>
  simp[Once mti_letrec_def] >> rpt strip_tac >> rw[] >> fs[]
  >- (simp[Once mti_letrec_def, SimpRHS] >> rw[] >>
      pop_assum (mp_tac o AP_TERM ``closLang$exp_size``) >>
      simp[closLangTheory.exp_size_def]) >>
  simp[Once mti_letrec_def]);

val mti_letrec1_correct = Q.store_thm(
  "mti_letrec1_correct",
  `exp_rel (:'ffi) [Letrec NONE NONE fns b]
                   [Letrec NONE NONE (MAP mti_letrec1 fns) b]`,
  irule recClosure_add_arg >> simp[exp_rel_refl] >>
  simp[LIST_REL_EL_EQN, EL_MAP] >> qx_gen_tac `n` >> strip_tac >>
  Cases_on `EL n fns` >> simp[] >> rename1 `mti_letrec1 (m, e)` >>
  Cases_on `e` >> simp[exp_rel_refl] >> rename1 `Fn opt1 opt2` >>
  Cases_on `opt1` >> Cases_on `opt2` >> rw[exp_rel_refl])

val exp_size_MAP_mti_letrec1 = Q.store_thm(
  "exp_size_MAP_mti_letrec1",
  `exp3_size (MAP SND (MAP mti_letrec1 fns)) ≤ exp3_size (MAP SND fns)`,
  Induct_on `fns` >> simp[FORALL_PROD, closLangTheory.exp_size_def] >>
  qx_genl_tac [`n`, `b`] >> assume_tac mti_letrec1_size_LEQ >> simp[]);

val mti_letrec_row_def = tDefine "mti_letrec_row" `
  mti_letrec_row fns =
    let fns' = MAP mti_letrec1 fns
    in
      if fns' = fns then fns
      else mti_letrec_row fns'`
  (WF_REL_TAC `measure (closLang$exp3_size o MAP SND)` >>
   simp[LIST_EQ_REWRITE, PULL_EXISTS] >> csimp[EL_MAP] >> Induct >>
   simp[closLangTheory.exp_size_def] >> rpt gen_tac >> rename1 `i < SUC _` >>
   Cases_on `i` >> simp[] >> strip_tac
   >- (rename1 `mti_letrec1 me = me` >> Cases_on `me` >> simp[] >>
       rename1 `mti_letrec1 (n,e)` >>
       `∃n' e'. mti_letrec1 (n,e) = (n',e')` by metis_tac[pair_CASES] >>
       `exp_size e' < exp_size e`
         by (fs[] >> metis_tac[mti_letrec1_size_decrease]) >> fs[] >>
       `exp3_size (MAP SND (MAP mti_letrec1 fns)) ≤ exp3_size (MAP SND fns)`
         by metis_tac[exp_size_MAP_mti_letrec1] >>
       simp[]) >>
   rename1 `mti_letrec1 me` >> Cases_on `me` >>
   rename1 `mti_letrec1 (m,e)` >> simp[] >> res_tac >>
   `exp_size (SND (mti_letrec1(m,e))) ≤ exp_size e`
     by metis_tac[mti_letrec1_size_LEQ] >> simp[])

val mti_letrec_expanded = Q.store_thm(
  "mti_letrec_expanded",
  `UNCURRY mti_letrec x = UNCURRY mti_letrec (mti_letrec1 x)`,
  Cases_on `x` >> simp[] >> simp[SimpLHS, Once mti_letrec_def] >>
  rename1 `mti_letrec1 (n,b)` >> Cases_on `mti_letrec1 (n,b)` >> simp[] >>
  rw[] >> imp_res_tac mti_letrec1_unchangedE_unchangedN >> rw[] >>
  simp[Once mti_letrec_def]);

val mti_letrec_mti_letrec_row = Q.store_thm(
  "mti_letrec_mti_letrec_row",
  `∀fns. MAP (UNCURRY mti_letrec) fns = mti_letrec_row fns`,
  ho_match_mp_tac (theorem "mti_letrec_row_ind") >> simp[] >> rpt strip_tac >>
  simp[Once mti_letrec_row_def] >> rw[] >> fs[]
  >- (fs[LIST_EQ_REWRITE, EL_MAP] >> qx_gen_tac `i` >> strip_tac >>
      Cases_on `EL i fns` >> simp[Once mti_letrec_def] >>
      rename1 `mti_letrec1 (m,b)` >>
      `mti_letrec1 (m,b) = (m,b)` by metis_tac[] >> simp[]) >>
  first_x_assum (SUBST_ALL_TAC o SYM) >>
  simp[MAP_MAP_o] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM] >> simp[Once mti_letrec_expanded, SimpLHS])

val mti_letrec_row_correct = Q.store_thm(
  "mti_letrec_row_correct",
  `∀funs. exp_rel (:'ffi) [Letrec NONE NONE funs e]
                          [Letrec NONE NONE (mti_letrec_row funs) e]`,
  ho_match_mp_tac (theorem "mti_letrec_row_ind") >> simp[] >> rpt strip_tac >>
  simp[Once mti_letrec_row_def] >> rw[exp_rel_refl] >> fs[] >>
  metis_tac[mti_letrec1_correct, exp_rel_trans]);

val intro_multi_alternative_rhs = Q.store_thm(
  "intro_multi_alternative_rhs",
  `MAP (λ(n,e). let (n',e') = collect_args n e
                in
                  (n', f e')) fns =
   MAP (I ## f) (mti_letrec_row fns)`,
  simp[GSYM mti_letrec_mti_letrec_row, MAP_MAP_o, UNCURRY, o_DEF,
       PAIR_MAP] >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM, FORALL_PROD, collect_args_mti_letrec]);

val UNCURRY_mti_letrec_UNCURRY_collect_args = Q.store_thm(
  "UNCURRY_mti_letrec_UNCURRY_collect_args",
  `UNCURRY mti_letrec = UNCURRY collect_args`,
  simp[FUN_EQ_THM, FORALL_PROD, collect_args_mti_letrec]);

val intro_multi_correct = Q.store_thm ("intro_multi_correct",
`!es. exp_rel (:'ffi) es (intro_multi es)`,
 ho_match_mp_tac intro_multi_ind >>
 srw_tac[][intro_multi_def, compat_nil, compat_var]
 >- metis_tac [compat_cons, intro_multi_sing, HD]
 >- metis_tac [compat_if, intro_multi_sing, HD]
 >- metis_tac [compat_let, intro_multi_sing, HD]
 >- metis_tac [compat_raise, intro_multi_sing, HD]
 >- metis_tac [compat_handle, intro_multi_sing, HD]
 >- metis_tac [compat_tick, intro_multi_sing, HD]
 >- metis_tac [compat_call, intro_multi_sing, HD]
 >- metis_tac [collect_apps_correct, intro_multi_sing, HD]
 >- metis_tac [compat_app, intro_multi_sing, HD]
 >- metis_tac [collect_args_correct, intro_multi_sing, HD]
 >- metis_tac [compat_fn, intro_multi_sing, HD]
 >- metis_tac [compat_fn, intro_multi_sing, HD]
 (* Letrec with loc = NONE *)
 >- (simp[intro_multi_alternative_rhs] >>
     irule exp_rel_trans >>
     qexists_tac `[Letrec NONE NONE (mti_letrec_row funs) e]` >>
     reverse conj_tac
     >- (reverse (irule compat_letrec)
         >- metis_tac[HD, intro_multi_sing] >>
         simp[LIST_REL_EL_EQN, GSYM mti_letrec_mti_letrec_row, EL_MAP] >>
         simp[UNCURRY_mti_letrec_UNCURRY_collect_args] >> qx_gen_tac `i` >>
         strip_tac >>
         `∃n b. EL i funs = (n,b)` by metis_tac[pair_CASES] >> simp[] >>
         `∃n' b'. collect_args n b = (n',b')` by metis_tac[pair_CASES] >>
         simp[] >> metis_tac[HD, intro_multi_sing, MEM_EL]) >>
    simp[mti_letrec_row_correct])
 >- (reverse (irule compat_letrec)
     >- metis_tac[intro_multi_sing, HD] >>
     simp[LIST_REL_EL_EQN] >> qx_gen_tac `n` >>
     rename1 `EL mm fns` >>
     Cases_on `EL mm fns` >> simp[exp_rel_refl])
 >- (reverse (irule compat_letrec)
     >- metis_tac[intro_multi_sing, HD] >>
     simp[LIST_REL_EL_EQN] >> qx_gen_tac `n` >>
     rename1 `EL mm fns` >> Cases_on `EL mm fns` >>
     simp[exp_rel_refl])
 >- metis_tac [compat_op, intro_multi_sing, HD]);

val HD_intro_multi = Q.prove(
  `[HD (intro_multi [e])] = intro_multi [e]`,
  metis_tac[intro_multi_sing,HD])

val contains_App_SOME_collect_args = Q.store_thm("contains_App_SOME_collect_args",
  `∀x y a b. collect_args x y = (a,b) ⇒
    (contains_App_SOME [y] ⇔ contains_App_SOME [b])`,
  ho_match_mp_tac collect_args_ind >>
  srw_tac[][collect_args_def,contains_App_SOME_def] >>
  srw_tac[][contains_App_SOME_def]);

val contains_App_SOME_collect_apps = Q.store_thm("contains_App_SOME_collect_apps",
  `∀x y a b. collect_apps x y = (a,b) ⇒
    (max_app < LENGTH x ∨ contains_App_SOME x ∨ contains_App_SOME [y] ⇔
     max_app < LENGTH a ∨ contains_App_SOME a ∨ contains_App_SOME [b])`,
  ho_match_mp_tac collect_apps_ind >>
  srw_tac[][collect_apps_def,contains_App_SOME_def] >>
  srw_tac[][contains_App_SOME_def] >> full_simp_tac(srw_ss())[] >>
  Cases_on`max_app < LENGTH x`>>full_simp_tac(srw_ss())[] >- DECIDE_TAC >>
  Cases_on`max_app < LENGTH es`>>full_simp_tac(srw_ss())[] >- DECIDE_TAC >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[] >> srw_tac[][] >>
  rpt (pop_assum mp_tac) >>
  ONCE_REWRITE_TAC[contains_App_SOME_EXISTS] >> srw_tac[][] >>
  metis_tac[]);

val contains_App_SOME_intro_multi = Q.store_thm("contains_App_SOME_intro_multi[simp]",
  `∀es. contains_App_SOME (intro_multi es) ⇔ contains_App_SOME es`,
  ho_match_mp_tac intro_multi_ind >>
  srw_tac[][intro_multi_def,contains_App_SOME_def] >>
  ONCE_REWRITE_TAC[CONS_APPEND] >>
  REWRITE_TAC[HD_intro_multi] >>
  full_simp_tac(srw_ss())[HD_intro_multi] >>
  full_simp_tac(srw_ss())[contains_App_SOME_def,HD_intro_multi,intro_multi_length]
  >- ( rpt (pop_assum mp_tac) >> ONCE_REWRITE_TAC[contains_App_SOME_EXISTS] >> srw_tac[][] )
  >- metis_tac[contains_App_SOME_collect_apps]
  >- metis_tac[contains_App_SOME_collect_args]
  >- (
    simp[MAP_MAP_o,UNCURRY,o_DEF] >>
    AP_THM_TAC >> AP_TERM_TAC >>
    pop_assum kall_tac >>
    Induct_on`funs`>>
    srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
    ONCE_REWRITE_TAC[CONS_APPEND] >>
    REWRITE_TAC[HD_intro_multi] >>
    rpt(pop_assum mp_tac) >>
    ONCE_REWRITE_TAC[contains_App_SOME_EXISTS] >>
    srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
    metis_tac[contains_App_SOME_collect_args,SND,PAIR]));

val every_Fn_vs_NONE_collect_apps = Q.prove(
  `∀es e x y. collect_apps es e = (x,y) ⇒
  (every_Fn_vs_NONE x ∧ every_Fn_vs_NONE [y] ⇔
   every_Fn_vs_NONE es ∧ every_Fn_vs_NONE [e])`,
  ho_match_mp_tac collect_apps_ind >>
  srw_tac[][collect_apps_def] >> full_simp_tac(srw_ss())[] >>
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] >>
  srw_tac[][] >> metis_tac[])

val every_Fn_vs_NONE_collect_args = Q.prove(
  `∀es e x y. collect_args es e = (x,y) ⇒
    (every_Fn_vs_NONE [y] ⇔ every_Fn_vs_NONE [e])`,
  ho_match_mp_tac collect_args_ind >>
  srw_tac[][collect_args_def] >> full_simp_tac(srw_ss())[])

val every_Fn_vs_NONE_intro_multi = Q.store_thm("every_Fn_vs_NONE_intro_multi[simp]",
  `∀es. every_Fn_vs_NONE (intro_multi es) = every_Fn_vs_NONE es`,
  ho_match_mp_tac intro_multi_ind >>
  srw_tac[][intro_multi_def] >>
  ONCE_REWRITE_TAC[CONS_APPEND] >>
  REWRITE_TAC[HD_intro_multi] >>
  full_simp_tac(srw_ss())[HD_intro_multi]
  >- ( rpt (pop_assum mp_tac) >> ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] >> srw_tac[][] )
  >- metis_tac[every_Fn_vs_NONE_collect_apps]
  >- metis_tac[every_Fn_vs_NONE_collect_args] >>
  simp[MAP_MAP_o,o_DEF,UNCURRY] >>
  qmatch_abbrev_tac `_ ∧ P ⇔ _ ∧ P` >>
  Cases_on `P` >> simp[] >>
  ntac 2 (pop_assum kall_tac) >>
  Induct_on`funs`>>
  srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
  ONCE_REWRITE_TAC[CONS_APPEND] >>
  REWRITE_TAC[HD_intro_multi] >>
  rpt(pop_assum mp_tac) >>
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] >>
  srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
  metis_tac[every_Fn_vs_NONE_collect_args,SND,PAIR]);

val _ = export_theory();
