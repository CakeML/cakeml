open preamble
open clos_relationTheory closSemTheory

val _ = new_theory "clos_relationProps";

val state_rel_io_mono = store_thm(
  "state_rel_io_mono[simp]",
  ``state_rel k s1 s2 ⇒
    state_rel k (s1 with io := io) (s2 with io := io)``,
  ONCE_REWRITE_TAC [val_rel_def] >> simp[]);

val exp_rel_evaluate_with_io = store_thm(
  "exp_rel_evaluate_with_io",
  ``(∀i v. val_rel i v v) ⇒
    ∀e1 e2.
      exp_rel e1 e2 ==>
      ∀s1 s2 k io r.
         state_rel k s1 s2 ⇒
         res_rel (evaluate_with_io e1 s1 (SOME io) k)
                 (evaluate_with_io e2 s2 (SOME io) k)``,
  simp[exp_rel_def, evaluate_with_io_def, exec_rel_rw, evaluate_ev_def] >>
  strip_tac >> qx_genl_tac [`e1`, `e2`] >> strip_tac >>
  qx_genl_tac [`s1`, `s2`, `k`, `io`] >>
  first_x_assum (qspecl_then [`k`, `[]`, `[]`,
                              `s1 with io := SOME io`,
                              `s2 with io := SOME io`]
                             mp_tac) >> simp[])

val resulteq =
    prove_case_eq_thm { case_def = TypeBase.case_def_of ``:(α,β) result``,
                        nchotomy = TypeBase.nchotomy_of ``:(α,β) result``}

val errorresulteq =
    prove_case_eq_thm { case_def = TypeBase.case_def_of ``:α error_result``,
                        nchotomy = TypeBase.nchotomy_of ``:α error_result``}

val listeq =
    prove_case_eq_thm { case_def = TypeBase.case_def_of ``:α list``,
                        nchotomy = TypeBase.nchotomy_of ``:α list``}

val refeq =
    prove_case_eq_thm { case_def = TypeBase.case_def_of ``:α ref``,
                        nchotomy = TypeBase.nchotomy_of ``:α ref``}

val veq =
    prove_case_eq_thm { case_def = TypeBase.case_def_of ``:closSem$v``,
                        nchotomy = TypeBase.nchotomy_of ``:closSem$v``}

val eqresulteq =
    prove_case_eq_thm { case_def = TypeBase.case_def_of ``:eq_result``,
                        nchotomy = TypeBase.nchotomy_of ``:eq_result``}
val appkindeq =
    prove_case_eq_thm { case_def = TypeBase.case_def_of ``:app_kind``,
                        nchotomy = TypeBase.nchotomy_of ``:app_kind``}

val paireq = prove(
  ``pair_CASE p f = v ⇔ ∃a b. p = (a,b) ∧ v = f a b``,
  Cases_on `p` >> simp[] >> metis_tac[]);

val ioeventeq =
    prove_case_eq_thm { case_def = TypeBase.case_def_of ``:io_event``,
                        nchotomy = TypeBase.nchotomy_of ``:io_event``}

val booleq = prove(
  ``(if p then x else y) = z ⇔ p ∧ x = z ∨ ¬p ∧ y = z``,
  rw[]);



val optioneq = prove(
  ``option_CASE opt n s = x ⇔ opt = NONE ∧ n = x ∨ ∃y. opt = SOME y ∧ x = s y``,
  Cases_on `opt` >> simp[] >> metis_tac[]);

val do_app_preserves_ioNONE = store_thm(
  "do_app_preserves_ioNONE",
  ``do_app op args s = Rval (v, s') ∧ s.io = NONE ⇒ s'.io = NONE``,
  Cases_on `op` >> Cases_on `args` >>
  simp[do_app_def, optioneq, listeq, veq, booleq, refeq, eqresulteq, paireq] >>
  rw[] >> rw[] >> fs[ffiTheory.call_FFI_def]);

val dec_clock_io = store_thm(
  "dec_clock_io[simp]",
  ``(dec_clock n s).io = s.io``,
  simp[dec_clock_def]);

val ioNONE_preserved = store_thm(
  "ioNONE_preserved",
  ``(∀esenvs es env s s' rv.
       evaluate esenvs = (rv, s') ∧ esenvs = (es,env,s) ∧ s.io = NONE ⇒
       s'.io = NONE) ∧
    (∀l f vs s s' rv.
       evaluate_app l f vs s = (rv, s') ∧ s.io = NONE ⇒ s'.io = NONE)``,
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[Once evaluate_def, paireq, resulteq, booleq, errorresulteq,
       optioneq, appkindeq, listeq] >>
  rpt strip_tac >> rw[]
  >- metis_tac[do_app_preserves_ioNONE]
  >- metis_tac[]);

open relationTheory
val exp3_size_EQ0 = store_thm(
  "exp3_size_EQ0[simp]",
  ``closLang$exp3_size l = 0 ⇔ l = []``,
  Cases_on `l` >> simp[closLangTheory.exp_size_def]);

val evaluate_ind' = save_thm(
  "evaluate_ind'",
    WF_INDUCTION_THM
      |> Q.ISPEC `
           inv_image ((<) LEX (<) LEX (<))
              (λx. case x of
                     INL (s:closSem$state,xs) =>
                       (s.clock, closLang$exp3_size xs, 0)
                   | INR (s:closSem$state,args) =>
                       (s.clock, 0, LENGTH (args:closSem$v list)))`
      |> SIMP_RULE (srw_ss()) [WF_inv_image, pairTheory.WF_LEX,
                               pairTheory.LEX_DEF, pairTheory.FORALL_PROD,
                               WF_TC, sumTheory.FORALL_SUM]
      |> Q.SPEC `λx. case x of INL (a1,a2) => P0 a1 a2
                             | INR (b1,b2) => Q0 b1 b2`
      |> SIMP_RULE (srw_ss()) [DISJ_IMP_THM, FORALL_AND_THM]);

val _ = augment_srw_ss [rewrites [closLangTheory.exp_size_def]]
val kill_asm_guard =
    disch_then (fn th => SUBGOAL_THEN (lhand (concl th))
                                      (MP_TAC o MATCH_MP th)) >- simp[]

val merge1 = prove(
  ``(∀s:closSem$state x. s.clock < N ⇒ P s x) ∧
    (∀s x. s.clock = N ∧ Q s x ⇒ P s x) ⇒
    (∀s x. s.clock ≤ N ∧ Q s x ⇒ P s x)``,
  dsimp[DECIDE ``x:num ≤ y ⇔ x < y ∨ x = y``]);

val merge2 = prove(
  ``(∀s:closSem$state x. s.clock < N ⇒ P s x) ∧ (∀s x. s.clock = N ⇒ P s x) ⇒
    ∀s x. s.clock ≤ N ⇒ P s x``,
  dsimp[DECIDE ``x:num ≤ y ⇔ x < y ∨ x = y``]);

val merge_tac =
  first_x_assum (fn c1 => first_x_assum (fn c2 =>
    assume_tac (HO_MATCH_MP merge1 (CONJ c1 c2)))) ORELSE
  first_x_assum (fn c1 => first_x_assum (fn c2 =>
    assume_tac (HO_MATCH_MP merge2 (CONJ c1 c2))))

val killevalapp =
    rpt (first_x_assum (kall_tac o assert (free_in ``evaluate_app`` o concl)))

val (evclock1, evclock2) = CONJ_PAIR evaluate_clock

val acc_ts = map (fn th => th |> concl |> strip_forall |> #2 |> lhs |> rator)
                 (TypeBase.accessors_of ``:closSem$state``)

val upd_ts = map (fn th => th |> concl |> strip_forall |> #2 |> lhs
                              |> rator)
                 (TypeBase.updates_of ``:closSem$state``)

val extendio_def = Define`
  extendio s io =
    case s.io of
        NONE => s
      | SOME io0 => s with io := SOME (LAPPEND io0 io)
`;

val extendio_accessors = save_thm(
  "extendio_accessors[simp]",
  map (fn acc => prove(``^acc (extendio s io) = ^acc s``,
                       simp[extendio_def] >> Cases_on `s.io` >> simp[]))
      (filter (not o aconv ``state_io``) acc_ts) |> LIST_CONJ)

val extendio_updates = save_thm(
  "extendio_updates[simp]",
  map
    (fn upd => prove(``^upd (extendio s io) = extendio (^upd s) io``,
                     simp[extendio_def]>> Cases_on `s.io` >> simp[]))
    (filter (not o aconv ``state_io_fupd`` o rator) upd_ts) |> LIST_CONJ)

val doapp_extendio_type_error = store_thm(
  "doapp_extendio_type_error",
  ``do_app opt args s0 = Rerr (Rabort Rtype_error) ⇒
    do_app opt args (extendio s0 io) = Rerr (Rabort Rtype_error)``,
  Cases_on `opt` >> Cases_on `args` >>
  dsimp[do_app_def, optioneq, listeq, veq, booleq, refeq, eqresulteq, paireq])

val doapp_extendio_nonffi = store_thm(
  "doapp_extendio_nonffi",
  ``do_app opt args s0 = Rval (rv, s) ∧ (∀n. opt ≠ FFI n) ⇒
    do_app opt args (extendio s0 io) = Rval (rv, extendio s io)``,
  Cases_on `opt` >> Cases_on `args` >>
  dsimp[do_app_def, optioneq, listeq, veq, booleq, refeq, eqresulteq, paireq] >>
  metis_tac[])

val doapp_extendio_SOMEioresult = store_thm(
  "doapp_extendio_SOMEioresult",
  ``do_app opt args s0 = Rval (rv, s) ∧ s.io ≠ NONE ⇒
    do_app opt args (extendio s0 io) = Rval (rv, extendio s io)``,
  Cases_on `∀n. opt ≠ FFI n` >> simp[] >- metis_tac[doapp_extendio_nonffi] >>
  fs[] >> Cases_on `args` >>
  dsimp[do_app_def, optioneq, listeq, veq, booleq, refeq, eqresulteq, paireq] >>
  simp[ffiTheory.call_FFI_def] >> Cases_on `s0.io` >>
  simp[extendio_def] >> dsimp[optioneq, paireq, ioeventeq, booleq] >>
  csimp[] >> qcase_tac `LHD l0 = SOME (IO_event _ _)` >>
  Q.ISPEC_THEN `l0` STRUCT_CASES_TAC llistTheory.llist_CASES >> simp[]);

fun first_r_assum ttac = first_x_assum (fn th => ttac th >> assume_tac th)

val exp_rel_sem = store_thm(
  "exp_rel_sem",
  ``(∀i v. val_rel i v v) ⇒
    ∀e1 e2 s1 s2.
      exp_rel e1 e2 ∧ (∀i. state_rel i s1 s2) ∧ ¬sem e1 s1 Fail ==>
      ¬sem e2 s2 Fail ∧
      ∀res. sem e1 s1 res ==> sem e2 s2 res``,
  strip_tac >> qx_genl_tac [`e1`, `e2`, `s1`, `s2`] >> strip_tac >>
  reverse conj_tac
  >- (qx_gen_tac `res` >>
      Cases_on `res` >> simp[sem_def]
      >- ((* diverge case *)
          strip_tac >> conj_tac
          >- (qx_gen_tac `k` >>
              first_x_assum
                (qspec_then `k` (qx_choose_then `s1'` strip_assume_tac)) >>
              qabbrev_tac `ev1 = evaluate_with_io e1 s1 (SOME l) k` >>
              qabbrev_tac `ev2 = evaluate_with_io e2 s2 (SOME l) k` >>
              `res_rel ev1 ev2` by metis_tac[exp_rel_evaluate_with_io] >>
              pop_assum mp_tac >> simp[res_rel_rw] >> dsimp[] >>
              simp[Once state_rel_rw] >> metis_tac[])
          >- (qx_gen_tac `io` >> strip_tac >>
              `∃k. (SND (evaluate_with_io e1 s1 (SOME io) k)).io = NONE`
                by metis_tac[] >>
              qexists_tac `k` >>
              qabbrev_tac `ev1 = evaluate_with_io e1 s1 (SOME io) k` >>
              qabbrev_tac `ev2 = evaluate_with_io e2 s2 (SOME io) k` >>
              `res_rel ev1 ev2` by metis_tac[exp_rel_evaluate_with_io] >>
              pop_assum mp_tac >>
              `∃r' s'. ev1 = (r',s')` by (Cases_on `ev1` >> simp[]) >>
              Cases_on `r'` >>
              simp[res_rel_rw] >> dsimp[]
              >- (var_eq_tac >> fs[] >> simp[Once state_rel_rw])
              >- (qcase_tac `res_rel (Rerr err, _)` >>
                  Cases_on `err`
                  >- (fs[res_rel_rw] >> dsimp[Once state_rel_rw]) >>
                  qcase_tac `res_rel (Rerr (Rabort abt), _)` >>
                  Cases_on `abt`
                  >- ((* type error *)
                      fs[Abbr`ev1`, sem_def] >> metis_tac[pairTheory.FST])
                  >- ((* timeout *)
                      simp[res_rel_rw] >> var_eq_tac >> fs[] >>
                      dsimp[Once state_rel_rw]))))
      >- ((* terminate case *)
          disch_then (qx_choosel_then [`k`, `s1'`, `r`] strip_assume_tac) >>
          qabbrev_tac `ev1 = evaluate_with_io e1 s1 (SOME (fromList l)) k` >>
          qabbrev_tac `ev2 = evaluate_with_io e2 s2 (SOME (fromList l)) k` >>
          qexists_tac `k` >>
          `res_rel ev1 ev2` by metis_tac[exp_rel_evaluate_with_io] >>
          pop_assum mp_tac >> simp[res_rel_rw] >> dsimp[] >>
          simp[Once state_rel_rw]))
  >- (fs[sem_def] >> qx_genl_tac [`k`, `io`] >>
      first_x_assum (qspecl_then [`k`, `io`] strip_assume_tac) >>
      qabbrev_tac `ev1 = evaluate_with_io e1 s1 (SOME io) k` >>
      qabbrev_tac `ev2 = evaluate_with_io e2 s2 (SOME io) k` >>
      `∃r1 s1'. ev1 = (r1,s1')` by (Cases_on `ev1` >> simp[]) >>
      `∃r2 s2'. ev2 = (r2,s2')` by (Cases_on `ev2` >> simp[]) >>
      `res_rel ev1 ev2` by metis_tac[exp_rel_evaluate_with_io] >>
      pop_assum mp_tac >>
      map_every qunabbrev_tac [`ev1`, `ev2`] >> fs[] >>
      Cases_on `r1` >> dsimp[res_rel_rw] >> qcase_tac `res_rel (Rerr e,_)` >>
      Cases_on `e` >> dsimp[res_rel_rw] >> qcase_tac `Rabort a` >>
      Cases_on `a` >> dsimp[res_rel_rw] >> fs[]))

(* ----------------------------------------------------------------------
    Theorems specific to certain transformations

    Could perhaps be in ../proofs/clos_XProofScript.sml for various values
    of X.
   ---------------------------------------------------------------------- *)

val rev_take_rev_all = Q.prove (
`n = LENGTH l ⇒ REVERSE (TAKE n (REVERSE l)) = l`,
 `LAST_N (LENGTH l) l = l` by simp [LAST_N_LENGTH] >>
 rfs [] >>
 simp [GSYM LAST_N_def, LAST_N_LENGTH]);

val rev_drop_rev_all = Q.prove (
`n = LENGTH l ⇒ REVERSE (DROP n (REVERSE l)) = []`,
 fs [DROP_REVERSE, BUTLASTN_LENGTH_NIL]);

val add_opt = Q.store_thm ("add_opt",
`!n1 n2. exp_rel [Op Add [Op (Const n1) []; Op (Const n2) []]] [Op (Const (n2 + n1)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw,
     val_rel_rw, evaluate_ev_def] >>
 metis_tac [val_rel_mono]);

val sub_opt = Q.store_thm ("sub_opt",
`!n1 n2. exp_rel [Op Sub [Op (Const n1) []; Op (Const n2) []]] [Op (Const (n2 - n1)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw,
     val_rel_rw, evaluate_ev_def] >>
 metis_tac [val_rel_mono]);

val mult_opt = Q.store_thm ("mult_opt",
`!n1 n2. exp_rel [Op Mult [Op (Const n1) []; Op (Const n2) []]] [Op (Const (n2 * n1)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, evaluate_ev_def, do_app_def,
     res_rel_rw, val_rel_rw] >>
 metis_tac [val_rel_mono]);

val div_opt = Q.store_thm ("div_opt",
`!n1 n2. exp_rel [Op Div [Op (Const n1) []; Op (Const n2) []]] [Op (Const (n2 / n1)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw,
     val_rel_rw, evaluate_ev_def] >>
 rw [res_rel_rw, val_rel_rw] >>
 metis_tac [val_rel_mono]);

val mod_opt = Q.store_thm ("mod_opt",
`!n1 n2. exp_rel [Op Mod [Op (Const n1) []; Op (Const n2) []]]
                 [Op (Const (n2 % n1)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, evaluate_ev_def, do_app_def,
     res_rel_rw, val_rel_rw] >>
 rw [res_rel_rw, val_rel_rw] >>
 metis_tac [val_rel_mono]);

val less_opt = Q.store_thm ("less_opt",
`!n1 n2.
  exp_rel [Op Less [Op (Const n1) []; Op (Const n2) []]]
          [Op (Cons (if n2 < n1 then true_tag else false_tag)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, do_app_def, res_rel_rw,
     val_rel_rw, Boolv_def, evaluate_ev_def] >>
 metis_tac [val_rel_mono]);

val leq_opt = Q.store_thm ("leq_opt",
`!n1 n2.
  exp_rel [Op LessEq [Op (Const n1) []; Op (Const n2) []]]
          [Op (Cons (if n2 ≤ n1 then true_tag else false_tag)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, evaluate_ev_def, do_app_def,
     res_rel_rw, val_rel_rw, Boolv_def] >>
 metis_tac [val_rel_mono]);

val greater_opt = Q.store_thm ("greater_opt",
`!n1 n2.
  exp_rel [Op Greater [Op (Const n1) []; Op (Const n2) []]]
          [Op (Cons (if n2 > n1 then true_tag else false_tag)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, evaluate_ev_def, do_app_def,
     res_rel_rw, val_rel_rw, Boolv_def] >>
 metis_tac [val_rel_mono]);

val geq_opt = Q.store_thm ("geq_opt",
`!n1 n2.
  exp_rel [Op GreaterEq [Op (Const n1) []; Op (Const n2) []]]
          [Op (Cons (if n2 ≥ n1 then true_tag else false_tag)) []]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, evaluate_ev_def, do_app_def,
     res_rel_rw, val_rel_rw, Boolv_def] >>
 metis_tac [val_rel_mono]);

val fn_add_arg = Q.store_thm ("fn_add_arg",
`!vars vars2 num_args num_args' e.
  num_args ≠ 0 ∧
  num_args' ≠ 0 ∧
  num_args + num_args' ≤ max_app ⇒
  exp_rel [Fn NONE vars num_args (Fn NONE vars2 num_args' e)]
          [Fn NONE vars (num_args + num_args') e]`,
 cheat (* rw [exp_rel_def, exec_rel_rw, evaluate_def, evaluate_ev_def] >>
 rw [res_rel_rw] >>
 Cases_on `clos_env s.restrict_envs vars env` >>
 fs [res_rel_rw] >>
 `s'.restrict_envs = s.restrict_envs` by fs [Once state_rel_rw] >>
 imp_res_tac val_rel_clos_env >>
 imp_res_tac val_rel_mono >>
 rw [val_rel_rw, is_closure_def, check_closures_def, clo_can_apply_def, clo_to_loc_def,
     clo_to_num_params_def, clo_to_partial_args_def, rec_clo_ok_def] >>
 simp [] >>
 imp_res_tac LIST_REL_LENGTH >>
 `args ≠ [] ∧ args' ≠ []` by (Cases_on `args` >> Cases_on `args'` >> fs []) >>
 rw [exec_rel_rw, evaluate_app_rw, dest_closure_def, res_rel_rw] >>
 rw [res_rel_rw] >>
 Cases_on `loc` >>
 fs [check_loc_def] >>
 rw [res_rel_rw] >>
 fs []
 >- metis_tac [val_rel_mono, ZERO_LESS_EQ] >>
 simp [evaluate_def, rev_take_rev_all] >>
 CASE_TAC >>
 rw [res_rel_rw] >>
 simp [rev_drop_rev_all] >>
 simp [evaluate_def , res_rel_rw, dec_clock_def] >>
 `i''' - LENGTH args' ≤ i''` by decide_tac >>
 imp_res_tac val_rel_mono >>
 simp [] >>
 rw [val_rel_rw, is_closure_def, exec_rel_rw, check_closures_def, clo_can_apply_def,
     clo_to_loc_def, clo_to_num_params_def, clo_to_partial_args_def, rec_clo_ok_def] >>
 `args'' ≠ [] ∧ args''' ≠ []` by (Cases_on `args''` >> Cases_on `args'''` >> fs []) >>
 simp [evaluate_app_rw, dest_closure_def] >>
 Cases_on `loc` >>
 fs [check_loc_def] >>
 rw [res_rel_rw] >>
 fs [] >>
 imp_res_tac LIST_REL_LENGTH >>
 Cases_on `i''''' < LENGTH args''` >>
 simp [res_rel_rw]
 >- metis_tac [val_rel_mono, ZERO_LESS_EQ]
 >- (fs [dec_clock_def] >>
     `i'' ≤ i` by decide_tac >>
     `LIST_REL (val_rel i'') (args ++ x) (args' ++ vs2')`
                by metis_tac [EVERY2_APPEND, val_rel_mono_list, LIST_REL_LENGTH] >>
     `?vs2''.
       clos_env s''.restrict_envs vars2 (args' ++ vs2') = SOME vs2'' ∧
       LIST_REL (val_rel i'') x' vs2''`
                  by metis_tac [val_rel_clos_env] >>
     simp [rev_take_rev_all, rev_drop_rev_all, dec_clock_def] >>
     qabbrev_tac `l = LENGTH args'''` >>
     `LENGTH args'' = l` by metis_tac [] >>
     `exp_rel [e] [e]` by metis_tac [exp_rel_refl] >>
     fs [exp_rel_def] >>
     pop_assum (qspecl_then [`i''''' - l`,
                             `args''++x'`,
                             `args''' ++ args' ++ vs2'`,
                             `s''''`,
                             `s'''''`] mp_tac) >>
     `i''''' - l ≤ i''''` by decide_tac >>
     imp_res_tac val_rel_mono >>
     simp [] >>
     rfs [] >>
     `i'''''-l ≤ i'' ∧ i''''' -l ≤ i''''` by decide_tac >>
     `LIST_REL (val_rel (i''''' − l)) (args'' ++ x') (args''' ++ args' ++ vs2')`
             by (`vs2'' = args'++vs2'` by cheat >>
                 metis_tac [APPEND_ASSOC, EVERY2_APPEND, val_rel_mono_list]) >>
     simp [exec_rel_rw] >>
     DISCH_TAC >>
     pop_assum (qspec_then `i'''''-l` mp_tac) >>
     simp [] >>
     reverse (strip_assume_tac (Q.ISPEC `evaluate ([e],args'' ++ x',s'''' with clock := i''''' − l)`
                         result_store_cases)) >>
     simp [res_rel_rw] >>
     DISCH_TAC >>
     fs []
     >- metis_tac [] >>
     imp_res_tac evaluate_SING >>
     fs [] >>
     rw [evaluate_def, res_rel_rw])
 >- metis_tac [val_rel_mono, ZERO_LESS_EQ]
 >- metis_tac [val_rel_mono, ZERO_LESS_EQ]
 >- metis_tac [val_rel_mono, ZERO_LESS_EQ]
 >- metis_tac [val_rel_mono, ZERO_LESS_EQ] *));

val fn_add_loc = Q.store_thm ("fn_add_loc",
`!vars num_args e l. exp_rel [Fn NONE vars num_args e] [Fn (SOME l) vars num_args e]`,
  cheat
 (* rw [exp_rel_def, exec_rel_rw, evaluate_def] >>
 Cases_on `clos_env s.restrict_envs vars env` >>
 rw [res_rel_rw] >>
 `s.restrict_envs = s'.restrict_envs` by fs [Once state_rel_rw] >>
 imp_res_tac val_rel_clos_env >>
 rfs [] >>
 fs [val_rel_rw, is_closure_def, check_closures_def, clo_can_apply_def,
     clo_to_loc_def, clo_to_num_params_def, clo_to_partial_args_def, rec_clo_ok_def] >>
 reverse (rw [])
 >- metis_tac [val_rel_mono] >>
 rw [exec_rel_rw] >>
 `args ≠ [] ∧ args' ≠ []` by (Cases_on `args` >> Cases_on `args'` >> fs []) >>
 simp [evaluate_app_rw, dest_closure_def] >>
 Cases_on `loc ` >>
 fs [check_loc_def, res_rel_rw] >>
 rw [res_rel_rw] >>
 simp [] >>
 imp_res_tac LIST_REL_LENGTH >>
 fs []
 >- metis_tac [val_rel_mono, ZERO_LESS_EQ] >>
 fs [dec_clock_def] >>
 simp [rev_take_rev_all, rev_drop_rev_all] >>
 qabbrev_tac `l = LENGTH args'` >>
 `LENGTH args = l` by metis_tac [] >>
 `exp_rel [e] [e]` by metis_tac [exp_rel_refl] >>
 fs [exp_rel_def] >>
 pop_assum (qspecl_then [`i''' - l`,
              `args++x`,
              `args' ++ vs2'`,
              `s'' with clock := i''' - l`,
              `s''' with clock := i''' - l`] mp_tac) >>
              `i'''- l ≤ i''` by decide_tac >>
 imp_res_tac val_rel_mono >>
 simp [state_rel_clock] >>
 rfs [] >>
 `i'''- l ≤ i'' ∧ i'''- l ≤ i` by decide_tac >>
 `LIST_REL (val_rel (i''' − l)) (args ++ x) (args' ++ vs2')`
           by metis_tac [EVERY2_APPEND, val_rel_mono_list] >>
 simp [exec_rel_rw] >>
 DISCH_TAC >>
 pop_assum (qspec_then `i'''-l` mp_tac) >>
 simp [] >>
 reverse (strip_assume_tac (Q.ISPEC `evaluate ([e],args ++ x,s'' with clock := i''' − l)`
           result_store_cases)) >>
 simp [res_rel_rw] >>
 DISCH_TAC >>
 fs []
 >- metis_tac [] >>
 imp_res_tac evaluate_SING >>
 fs [] >>
 rw [evaluate_def, res_rel_rw] *));



val _ = export_theory();
