open preamble bvlSemTheory clos_to_bvlTheory;

val _ = new_theory"bvlProps";

val bool_to_tag_11 = store_thm("bool_to_tag_11[simp]",
  ``bool_to_tag b1 = bool_to_tag b2 ⇔ (b1 = b2)``,
  rw[bool_to_tag_def] >> EVAL_TAC >> simp[])

val _ = Q.store_thm("Boolv_11[simp]",`bvlSem$Boolv b1 = Boolv b2 ⇔ b1 = b2`,EVAL_TAC>>rw[]);

val evaluate_LENGTH = prove(
  ``!xs s env. (\(xs,s,env).
      (case evaluate (xs,s,env) of (Rval res,s1) => (LENGTH xs = LENGTH res)
            | _ => T))
      (xs,s,env)``,
  HO_MATCH_MP_TAC evaluate_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [evaluate_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ BasicProvers.EVERY_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  |> SIMP_RULE std_ss [];

val _ = save_thm("evaluate_LENGTH", evaluate_LENGTH);

val evaluate_IMP_LENGTH = store_thm("evaluate_IMP_LENGTH",
  ``(evaluate (xs,s,env) = (Rval res,s1)) ==> (LENGTH xs = LENGTH res)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL evaluate_LENGTH) \\ fs []);

val evaluate_CONS = store_thm("evaluate_CONS",
  ``evaluate (x::xs,env,s) =
      case evaluate ([x],env,s) of
      | (Rval v,s2) =>
         (case evaluate (xs,env,s2) of
          | (Rval vs,s1) => (Rval (HD v::vs),s1)
          | t => t)
      | t => t``,
  Cases_on `xs` \\ fs [evaluate_def]
  \\ Cases_on `evaluate ([x],env,s)` \\ fs [evaluate_def]
  \\ Cases_on `q` \\ fs [evaluate_def]
  \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a` \\ fs []
  \\ Cases_on `t` \\ fs []);

val evaluate_SNOC = store_thm("evaluate_SNOC",
  ``!xs env s x.
      evaluate (SNOC x xs,env,s) =
      case evaluate (xs,env,s) of
      | (Rval vs,s2) =>
         (case evaluate ([x],env,s2) of
          | (Rval v,s1) => (Rval (vs ++ v),s1)
          | t => t)
      | t => t``,
  Induct THEN1
   (fs [SNOC_APPEND,evaluate_def] \\ REPEAT STRIP_TAC
    \\ Cases_on `evaluate ([x],env,s)` \\ Cases_on `q` \\ fs [])
  \\ fs [SNOC_APPEND,APPEND]
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `evaluate ([h],env,s)` \\ Cases_on `q` \\ fs []
  \\ Cases_on `evaluate (xs,env,r)` \\ Cases_on `q` \\ fs []
  \\ Cases_on `evaluate ([x],env,r')` \\ Cases_on `q` \\ fs [evaluate_def]
  \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a''` \\ fs [LENGTH]
  \\ REV_FULL_SIMP_TAC std_ss [LENGTH_NIL] \\ fs []);

val evaluate_APPEND = store_thm("evaluate_APPEND",
  ``!xs env s ys.
      evaluate (xs ++ ys,env,s) =
      case evaluate (xs,env,s) of
        (Rval vs,s2) =>
          (case evaluate (ys,env,s2) of
             (Rval ws,s1) => (Rval (vs ++ ws),s1)
           | res => res)
      | res => res``,
  Induct \\ fs [APPEND,evaluate_def] \\ REPEAT STRIP_TAC
  THEN1 REPEAT BasicProvers.CASE_TAC
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ REPEAT BasicProvers.CASE_TAC \\ fs []);

val evaluate_code = store_thm("evaluate_code",
  ``!xs env s1 vs s2.
      (evaluate (xs,env,s1) = (vs,s2)) ==> s2.code = s1.code``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_def]
  \\ FULL_SIMP_TAC std_ss []
  \\ BasicProvers.FULL_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [dec_clock_def]
  \\ Cases_on`q`  \\ FULL_SIMP_TAC (srw_ss())[]
  \\ POP_ASSUM MP_TAC
  \\ BasicProvers.CASE_TAC \\ FULL_SIMP_TAC (srw_ss())[]
  \\ SRW_TAC[][] \\ SRW_TAC[][]
  \\ POP_ASSUM MP_TAC
  \\ BasicProvers.CASE_TAC \\ FULL_SIMP_TAC (srw_ss())[]
  \\ SRW_TAC[][] \\ IMP_RES_TAC do_app_const \\ SRW_TAC[][]
  \\ POP_ASSUM MP_TAC
  \\ BasicProvers.CASE_TAC \\ FULL_SIMP_TAC (srw_ss())[]
  \\ SRW_TAC[][] \\ SRW_TAC[][dec_clock_def]);

val evaluate_mk_tick = Q.store_thm ("evaluate_mk_tick",
  `!exp env s n.
    evaluate ([mk_tick n exp], env, s) =
      if s.clock < n then
        (Rerr(Rabort Rtimeout_error), s with clock := 0)
      else
        evaluate ([exp], env, dec_clock n s)`,
  Induct_on `n` >>
  rw [mk_tick_def, evaluate_def, dec_clock_def, FUNPOW] >>
  fs [mk_tick_def, evaluate_def, dec_clock_def] >>
  rw [] >>
  full_simp_tac (srw_ss()++ARITH_ss) [dec_clock_def, ADD1]
  >- (`s with clock := s.clock = s`
             by rw [state_component_equality] >>
      rw [])
  >- (`s.clock = n` by decide_tac >>
      fs []));

val inc_clock_def = Define `
  inc_clock ck s = s with clock := s.clock + ck`;

val inc_clock_code = Q.store_thm ("inc_clock_code",
  `!n (s:bvlSem$state). (inc_clock n s).code = s.code`,
  rw [inc_clock_def]);

val inc_clock_refs = Q.store_thm ("inc_clock_refs",
  `!n (s:bvlSem$state). (inc_clock n s).refs = s.refs`,
  rw [inc_clock_def]);

val inc_clock0 = Q.store_thm ("inc_clock0",
  `!n (s:bvlSem$state). inc_clock 0 s = s`,
  simp [inc_clock_def, state_component_equality]);

val _ = export_rewrites ["inc_clock_refs", "inc_clock_code", "inc_clock0"];

val dec_clock_code = Q.store_thm ("dec_clock_code",
  `!n (s:bvlSem$state). (dec_clock n s).code = s.code`,
  rw [dec_clock_def]);

val dec_clock_refs = Q.store_thm ("dec_clock_refs",
  `!n (s:bvlSem$state). (dec_clock n s).refs = s.refs`,
  rw [dec_clock_def]);

val dec_clock0 = Q.store_thm ("dec_clock0",
  `!n (s:bvlSem$state). dec_clock 0 s = s`,
  simp [dec_clock_def, state_component_equality]);

val _ = export_rewrites ["dec_clock_refs", "dec_clock_code", "dec_clock0"];

val do_app_change_clock = store_thm("do_app_change_clock",
  ``(do_app op args s1 = SOME (res,s2)) ==>
    (do_app op args (s1 with clock := ck) = SOME (res,s2 with clock := ck))``,
  SIMP_TAC std_ss [do_app_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [] \\
  CCONTR_TAC >> fs [] >>
  rw [] >>
  fs [do_eq_def]);

val evaluate_add_clock = Q.store_thm ("evaluate_add_clock",
  `!exps env s1 res s2.
    evaluate (exps,env,s1) = (res, s2) ∧
    res ≠ Rerr(Rabort Rtimeout_error)
    ⇒
    !ck. evaluate (exps,env,inc_clock ck s1) = (res, inc_clock ck s2)`,
  recInduct evaluate_ind >>
  rw [evaluate_def]
  >- (Cases_on `evaluate ([x], env,s)` >> fs [] >>
      Cases_on `q` >> fs [] >> rw [] >>
      Cases_on `evaluate (y::xs,env,r)` >> fs [] >>
      Cases_on `q` >> fs [] >> rw [] >> fs[])
  >- (Cases_on `evaluate ([x1],env,s)` >> fs [] >>
      Cases_on `q` >> fs [] >> rw[] >> fs[])
  >- (Cases_on `evaluate (xs,env,s)` >>
      fs [] >>
      Cases_on `q` >>
      fs [] >>
      rw [] >> fs[])
  >- (Cases_on `evaluate (xs,env,s)` >> fs [] >>
      Cases_on `q` >> fs [] >> rw[] >> fs[] >>
      BasicProvers.EVERY_CASE_TAC >>
      fs [] >> rw [] >> fs[])
  >- (Cases_on `evaluate ([x1],env,s1)` >> fs [] >>
      Cases_on `q` >> fs [] >> rw [] >> fs[] >>
      Cases_on`e`>>fs[]>>rw[]>>fs[])
  >- (Cases_on `evaluate (xs,env,s)` >> fs [] >>
      Cases_on `q` >> fs [] >> rw[] >> fs[] >>
      rw [inc_clock_def] >>
      BasicProvers.EVERY_CASE_TAC >>
      fs [] >>
      imp_res_tac do_app_const >>
      imp_res_tac do_app_change_clock >>
      fs [] >>
      rw [] >>
      pop_assum (qspec_then `r.clock` mp_tac) >>
      rw [] >>
      `r with clock := r.clock = r` by rw [state_component_equality] >>
      fs [])
  >- (rw [] >>
      fs [inc_clock_def, dec_clock_def] >>
      rw [] >>
      `s.clock + ck - 1 = s.clock - 1 + ck` by (srw_tac [ARITH_ss] [ADD1]) >>
      metis_tac [])
  >- (Cases_on `evaluate (xs,env,s1)` >>
      fs [] >>
      Cases_on `q` >>
      fs [] >>
      rw [] >>
      BasicProvers.EVERY_CASE_TAC >>
      fs [] >>
      rw [] >>
      rfs [inc_clock_def, dec_clock_def] >>
      rw []
      >- decide_tac >>
      `r.clock + ck - (ticks + 1) = r.clock - (ticks + 1) + ck` by srw_tac [ARITH_ss] [ADD1] >>
      metis_tac []));

val take_drop_lem = Q.prove (
  `!skip env.
    skip < LENGTH env ∧
    skip + SUC n ≤ LENGTH env ∧
    DROP skip env ≠ [] ⇒
    EL skip env::TAKE n (DROP (1 + skip) env) = TAKE (n + 1) (DROP skip env)`,
  Induct_on `n` >>
  rw [take1, hd_drop] >>
  `skip + SUC n ≤ LENGTH env` by decide_tac >>
  res_tac >>
  `LENGTH (DROP skip env) = LENGTH env - skip` by rw [LENGTH_DROP] >>
  `SUC n < LENGTH (DROP skip env)` by decide_tac >>
  `LENGTH (DROP (1 + skip) env) = LENGTH env - (1 + skip)` by rw [LENGTH_DROP] >>
  `n < LENGTH (DROP (1 + skip) env)` by decide_tac >>
  rw [TAKE_EL_SNOC, ADD1] >>
  `n + (1 + skip) < LENGTH env` by decide_tac >>
  `(n+1) + skip < LENGTH env` by decide_tac >>
  rw [EL_DROP] >>
  srw_tac [ARITH_ss] []);

val evaluate_genlist_vars = Q.store_thm ("evaluate_genlist_vars",
  `!skip env n st.
    n + skip ≤ LENGTH env ⇒
    evaluate (GENLIST (λarg. Var (arg + skip)) n, env, st)
    =
    (Rval (TAKE n (DROP skip env)), st)`,
  Induct_on `n` >>
  rw [evaluate_def, DROP_LENGTH_NIL, GSYM ADD1] >>
  rw [Once GENLIST_CONS] >>
  rw [Once evaluate_CONS, evaluate_def] >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  first_x_assum (qspecl_then [`skip + 1`, `env`] mp_tac) >>
  rw [] >>
  `n + (skip + 1) ≤ LENGTH env` by decide_tac >>
  fs [] >>
  rw [combinTheory.o_DEF, ADD1, GSYM ADD_ASSOC] >>
  `skip + 1 = 1 + skip ` by decide_tac >>
  fs [] >>
  `LENGTH (DROP skip env) = LENGTH env - skip` by rw [LENGTH_DROP] >>
  `n < LENGTH env - skip` by decide_tac >>
  `DROP skip env ≠ []`
        by (Cases_on `DROP skip env` >>
            fs [] >>
            decide_tac) >>
  metis_tac [take_drop_lem]);

val evaluate_var_reverse = Q.store_thm ("evaluate_var_reverse",
  `!xs env n ys st.
   evaluate (MAP Var xs, env, st) = (Rval ys, st)
   ⇒
   evaluate (REVERSE (MAP Var xs), env, st) = (Rval (REVERSE ys), st)`,
  Induct_on `xs` >>
  rw [evaluate_def] >>
  fs [evaluate_APPEND] >>
  pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_CONS]) >>
  rw [] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [evaluate_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw [] >>
  res_tac >>
  fs []);

val evaluate_genlist_vars_rev = Q.store_thm ("evaluate_genlist_vars_rev",
  `!skip env n st.
    n + skip ≤ LENGTH env ⇒
    evaluate (REVERSE (GENLIST (λarg. Var (arg + skip)) n), env, st) =
    (Rval (REVERSE (TAKE n (DROP skip env))), st)`,
  rw [] >>
  imp_res_tac evaluate_genlist_vars >>
  pop_assum (qspec_then `st` assume_tac) >>
  `GENLIST (λarg. Var (arg + skip):bvl$exp) n = MAP Var (GENLIST (\arg. arg + skip) n)`
           by rw [MAP_GENLIST, combinTheory.o_DEF] >>
  fs [] >>
  metis_tac [evaluate_var_reverse]);

val _ = export_theory();
