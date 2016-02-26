open preamble;
open clos_relationTheory clos_relationPropsTheory closPropsTheory clos_mtiTheory;
open closSemTheory

val _ = new_theory "clos_mtiProof";

val bool_case_eq = Q.prove(
  `COND b t f = v ⇔ b /\ v = t ∨ ¬b ∧ v = f`,
  srw_tac[][] >> metis_tac[]);

val pair_case_eq = Q.prove (
`pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v`,
 Cases_on `x` >>
 srw_tac[][]);

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
  qcase_tac `Fn opt1 opt2 nn body` >>
  Cases_on `opt1` >> Cases_on `opt2` >>
  simp[collect_args_def] >> rw[] >> metis_tac[]);

val collect_args_never_decreases = Q.store_thm(
  "collect_args_never_decreases",
  `∀e e' n n'. collect_args n e = (n', e') ⇒ n ≤ n'`,
  Induct >> simp[collect_args_def] >> rpt gen_tac >>
  qcase_tac `Fn opt1 opt2 nn body` >>
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
     ¬check_loc locopt (lift ($+ i) loc) (FST (EL i fns))
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
     if n + m ≤ max_app then SOME (m, body) else NONE) ∧
  (dest_addarg_Fn _ _ = NONE)
`;
val _ = augment_srw_ss [rewrites [dest_addarg_Fn_def]]

val recClosure_add_arg = Q.store_thm(
  "recClosure_add_arg",
  `LIST_REL (λ(n,e) (n',e').
               n ≠ 0 ∧
               case dest_addarg_Fn n e of
                   SOME(m,e0) => exp_rel (:'ffi) [e0] [e'] ∧ n' = n + m
                 | NONE => n = n' ∧ exp_rel (:'ffi) [e] [e'])
            fns fns'
    ⇒
      exp_rel (:'ffi) [Letrec NONE fvs fns body] [Letrec NONE fvs fns' body]`,
  strip_tac >>
  `LIST_REL (λp1 p2. FST p1 ≤ FST p2) fns fns'`
    by (pop_assum mp_tac >> match_mp_tac LIST_REL_mono >>
        simp[FORALL_PROD] >> rpt gen_tac >> qcase_tac `dest_addarg_Fn _ f` >>
        Cases_on `f` >> simp[dest_addarg_Fn_def] >>
        qcase_tac `Fn opt1 opt2` >> Cases_on `opt1` >> Cases_on `opt2` >>
        simp[] >> rw[]) >>
  simp[exp_rel_def, exec_rel_rw, evaluate_ev_def, evaluate_def] >>
  qabbrev_tac `nargs_ok = λ(n,e:closLang$exp). n ≤ max_app ∧ n ≠ 0` >>
  `EVERY nargs_ok fns' ⇔ EVERY nargs_ok fns`
    by (fs[LIST_REL_EL_EQN, EVERY_MEM, FORALL_PROD, EQ_IMP_THM] >>
        rpt strip_tac
        >- (qcase_tac `nargs_ok (n,b)` >>
            `∃i. i < LENGTH fns ∧ EL i fns = (n,b)` by metis_tac[MEM_EL] >>
            `∃n' b'. EL i fns' = (n',b')` by (Cases_on `EL i fns'` >> simp[]) >>
            `MEM (n',b') fns'` by metis_tac[MEM_EL] >>
            qpat_assum `∀n. n < LENGTH _ ⇒ _ (EL n fns) (EL n fns')`
              (qspec_then `i` mp_tac) >> rfs[] >>
            first_x_assum (qspecl_then [`n'`, `b'`] mp_tac) >>
            simp[Abbr`nargs_ok`] >>
            Cases_on `b` >> simp[] >>
            qcase_tac `Fn opt1 opt2` >> Cases_on `opt1` >> simp[] >>
            Cases_on `opt2` >> simp[] >> rw[])
        >- (qcase_tac `nargs_ok (n',b')` >>
            `∃i. i < LENGTH fns ∧ EL i fns' = (n',b')` by metis_tac[MEM_EL] >>
            `∃n b. EL i fns = (n,b)` by (Cases_on `EL i fns` >> simp[]) >>
            `MEM (n,b) fns` by metis_tac[MEM_EL] >>
            qpat_assum `∀n. n < LENGTH _ ⇒ _ (EL n fns) (EL n fns')`
              (qspec_then `i` mp_tac) >> rfs[] >>
            first_x_assum (qspecl_then [`n`, `b`] mp_tac) >>
            simp[Abbr`nargs_ok`] >>
            Cases_on `b` >> simp[] >>
            qcase_tac `Fn opt1 opt2` >> Cases_on `opt1` >> simp[] >>
            Cases_on `opt2` >> simp[] >> rw[])) >>
  reverse (Cases_on `EVERY nargs_ok fns`) >> simp[]
  >- simp[res_rel_rw] >>
  Cases_on `fvs` >> simp[PULL_FORALL, AND_IMP_INTRO]
  >- (`exp_rel (:'ffi) [body] [body]` by metis_tac[exp_rel_refl] >>
      pop_assum mp_tac >>
      CONV_TAC (LAND_CONV
        (SIMP_CONV (srw_ss()) [
           exp_rel_def, exec_rel_rw, evaluate_ev_def, PULL_FORALL,
           AND_IMP_INTRO])) >>
      rpt strip_tac >> first_x_assum match_mp_tac >> qexists_tac `i` >>
      simp[] >>
      irule EVERY2_APPEND_suff >> simp[] >>
      qpat_assum `LIST_REL _ env env'` mp_tac >>
      rpt (first_x_assum (kall_tac o assert (free_in ``i:num`` o concl))) >>
      `∀E1 E2 V1 V2.
         LIST_REL (val_rel (:'ffi) i) E1 E2 ∧
         LIST_REL (val_rel (:'ffi) i) V1 V2 ⇒
         LIST_REL (val_rel (:'ffi) i)
           (GENLIST (Recclosure NONE V1 E1 fns) (LENGTH fns))
           (GENLIST (Recclosure NONE V2 E2 fns') (LENGTH fns'))`
        suffices_by metis_tac[LIST_REL_NIL] >>
      completeInduct_on `i` >> rpt strip_tac >>
      simp[LIST_REL_EL_EQN] >>
      `LENGTH fns' = LENGTH fns` by fs[LIST_REL_EL_EQN] >> simp[] >>
      qx_gen_tac `fidx` >> strip_tac >>
      simp[val_rel_rw, is_closure_def, check_closures_def, clo_can_apply_def,
           clo_to_partial_args_def, clo_to_num_params_def, clo_to_loc_def,
           rec_clo_ok_def] >>
      `∃fina fib fina' fib'.
         EL fidx fns = (fina,fib) ∧ EL fidx fns' = (fina',fib')`
        by metis_tac[pair_CASES] >> simp[] >>
      `MEM (fina,fib) fns ∧ MEM (fina',fib') fns'` by metis_tac[MEM_EL] >>
      `0 < fina ∧ 0 < fina'`
        by (fs[EVERY_MEM] >> res_tac >> fs[Abbr`nargs_ok`]) >>
      simp[] >>
      simp[option_CASE_NONE_T, option_case_NONE_F,
           dest_closure_Recclosure_EQ_NONE, check_loc_second_NONE] >>
      `fina ≤ fina'` by (fs[LIST_REL_EL_EQN] >> metis_tac[FST]) >>
      `LENGTH V2 = LENGTH V1` by fs[LIST_REL_EL_EQN] >> simp[] >>
      qx_genl_tac [`j`, `vs1`, `vs2`, `s1`, `s2`] >> strip_tac >>
      Cases_on `LENGTH vs1 ≤ max_app` >> simp[] >>
      Cases_on `LENGTH V1 < fina` >> simp[] >>
      simp[dest_closure_def, revtakerev, revdroprev, check_loc_second_NONE] >>
      `LENGTH vs2 = LENGTH vs1` by fs[LIST_REL_EL_EQN] >> simp[] >>
      Cases_on `LENGTH V1 + LENGTH vs1 < fina` >> simp[]
      >- (simp[exec_rel_rw, evaluate_ev_def] >> qx_gen_tac `k` >>
          reverse (rw[])
          >- (simp[res_rel_rw] >> metis_tac[val_rel_mono, DECIDE``0n≤j``]) >>
          simp[res_rel_rw] >> reverse conj_tac
          >- (irule (last (CONJUNCTS val_rel_mono)) >> qexists_tac `j` >>
              simp[]) >>
          first_x_assum (qspec_then `k - (LENGTH vs1 - 1)` mp_tac) >> simp[] >>
          disch_then
            (qspecl_then [`E1`, `E2`, `vs1 ++ V1`, `vs2 ++ V2`] mp_tac) >>
          discharge_hyps
          >- (conj_tac
              >- (irule val_rel_mono_list >> qexists_tac `i` >> simp[]) >>
              irule EVERY2_APPEND_suff >>
              irule val_rel_mono_list
              >- (qexists_tac `j` >> simp[]) >> qexists_tac `i` >> simp[]) >>
          simp[LIST_REL_EL_EQN]) >>
      cheat) >>
  cheat)


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
 >- (qcase_tac `Letrec NONE fvs fns body` >>
     simp[exp_rel_def, exec_rel_rw, evaluate_ev_def,
          closSemTheory.evaluate_def] >>
     qx_genl_tac [`i`, `env1`, `env2`, `s1`, `s2`] >> strip_tac >>
     qx_gen_tac `j` >> strip_tac >>
     reverse (Cases_on `EVERY (λ(nn,e). nn ≤ max_app ∧ nn ≠ 0) fns`) >>
     simp[] >- simp[res_rel_rw] >>
     simp[EVERY_MAP] >> fs[EVERY_MEM, FORALL_PROD] >>
     qmatch_abbrev_tac `res_rel _ (if GUARD then _ else _)` >>
     `GUARD`
       by (simp[Abbr`GUARD`] >> qx_genl_tac [`n`, `e`] >> strip_tac >>
           `∃n' e'. collect_args n e = (n', e')`
             by (Cases_on `collect_args n e` >> simp[]) >> simp[] >>
           res_tac >> conj_tac >- metis_tac[collect_args_max_app] >>
           imp_res_tac collect_args_never_decreases >> strip_tac >> fs[]) >>
     simp[] >> Q.UNABBREV_TAC `GUARD` >>
     Cases_on `fvs` >> simp[]
     >- (qpat_assum `exp_rel _ _ _` mp_tac >>
         simp[exp_rel_def, exec_rel_rw, evaluate_ev_def, PULL_FORALL] >>
         `∃body'. intro_multi [body] = [body']`
           by metis_tac[intro_multi_sing] >> simp[] >>
         disch_then irule >> qexists_tac `i` >> simp[] >>
         simp[LIST_REL_EL_EQN] >>
         `LENGTH env2 = LENGTH env1` by fs[LIST_REL_EL_EQN] >> simp[] >>
         qx_gen_tac `n` >> strip_tac >> reverse (Cases_on `n < LENGTH fns`)
         >- (simp[EL_APPEND2] >> fs[LIST_REL_EL_EQN]) >>
         simp[EL_APPEND1, val_rel_rw, is_closure_def] >>
         conj_tac
         >- (simp[check_closures_def, clo_can_apply_def,
                  clo_to_num_params_def, clo_to_partial_args_def,
                  rec_clo_ok_def, clo_to_loc_def, EL_MAP] >>
             `∃nn ee. EL n fns = (nn,ee)`
               by (Cases_on `EL n fns` >> simp[]) >> simp[] >>
             Cases_on `collect_args nn ee` >> simp[] >>
             imp_res_tac collect_args_never_decreases >> simp[]) >>
         simp[option_case_NONE_F, option_CASE_NONE_T,
              dest_closure_Recclosure_EQ_NONE] >>
         `∃nn ee. EL n fns = (nn,ee)` by (Cases_on `EL n fns` >> simp[]) >>
         simp[] >> `MEM (nn,ee) fns` by metis_tac[MEM_EL] >>
         `nn ≠ 0 ∧ nn ≤ max_app` by metis_tac[] >> simp[] >>
         simp[check_loc_second_NONE] >>
         qx_genl_tac [`k`, `vs1`, `vs2`, `s11`, `s12`] >> strip_tac >>
         Cases_on `LENGTH vs1 ≤ max_app` >> simp[] >>
         `LENGTH vs2 = LENGTH vs1` by fs[LIST_REL_EL_EQN] >>
         simp[dest_closure_def, EL_MAP, revtakerev, revdroprev, bool_case_eq,
              check_loc_second_NONE] >>
         Cases_on `nn ≤ LENGTH vs1` >> simp[]
         >- (`∃nn1 ee1. collect_args nn ee = (nn1,ee1)`
               by (Cases_on `collect_args nn ee` >> simp[]) >> simp[] >>
             `nn ≤ nn1` by metis_tac[collect_args_never_decreases] >> simp[] >>
             Cases_on `nn1 ≤ LENGTH vs1` >> simp[]
             >- (simp[revtakerev, revdroprev] >>
                 simp[exec_rel_rw, evaluate_ev_def] >> cheat) >>
             cheat) >>
         cheat) >>
     cheat)
 >- (reverse (irule compat_letrec)
     >- metis_tac[intro_multi_sing, HD] >>
     simp[LIST_REL_EL_EQN] >> qx_gen_tac `n` >>
     qcase_tac `EL mm fns` >>
     Cases_on `EL mm fns` >> simp[exp_rel_refl])
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
  AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  pop_assum kall_tac >>
  Induct_on`funs`>>
  srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
  ONCE_REWRITE_TAC[CONS_APPEND] >>
  REWRITE_TAC[HD_intro_multi] >>
  rpt(pop_assum mp_tac) >>
  ONCE_REWRITE_TAC[every_Fn_vs_NONE_EVERY] >>
  srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
  metis_tac[every_Fn_vs_NONE_collect_args,SND,PAIR]);

val _ = export_theory();
