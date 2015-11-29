open preamble bvlSemTheory clos_to_bvlTheory bvl_constTheory;

val _ = new_theory"bvlProps";

val bool_to_tag_11 = store_thm("bool_to_tag_11[simp]",
  ``bool_to_tag b1 = bool_to_tag b2 ⇔ (b1 = b2)``,
  rw[bool_to_tag_def] >> EVAL_TAC >> simp[])

val _ = Q.store_thm("Boolv_11[simp]",`bvlSem$Boolv b1 = Boolv b2 ⇔ b1 = b2`,EVAL_TAC>>rw[]);

val find_code_EVERY_IMP = store_thm("find_code_EVERY_IMP",
  ``(find_code dest a (r:'ffi bvlSem$state).code = SOME (q,t)) ==>
    EVERY P a ==> EVERY P q``,
  Cases_on `dest` \\ fs [find_code_def] \\ REPEAT STRIP_TAC
  \\ BasicProvers.EVERY_CASE_TAC \\ SRW_TAC [] [] \\ fs []
  \\ BasicProvers.EVERY_CASE_TAC \\ SRW_TAC [] [] \\ fs []
  \\ `?x1 l1. a = SNOC x1 l1` by METIS_TAC [SNOC_CASES] \\ fs []
  \\ BasicProvers.EVERY_CASE_TAC \\ SRW_TAC [] [] \\ fs []
  \\ BasicProvers.EVERY_CASE_TAC \\ SRW_TAC [] [] \\ fs []
  \\ BasicProvers.EVERY_CASE_TAC \\ SRW_TAC [] [] \\ fs []
  \\ BasicProvers.EVERY_CASE_TAC \\ SRW_TAC [] [] \\ fs []
  \\ FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,FRONT_SNOC]);

val do_app_err = Q.store_thm("do_app_err",
  `do_app op vs s = Rerr e ⇒ (e = Rabort Rtype_error)`,
  rw[do_app_def] >> every_case_tac >> fs[LET_THM] >> rw[]);

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

val evaluate_SING = Q.store_thm("evaluate_SING",
  `(evaluate ([x],env,s) = (Rval a,p1)) ==> ?d1. a = [d1]`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a` \\ fs [LENGTH_NIL]);

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

val evaluate_MAP_Const = store_thm("evaluate_MAP_Const",
  ``!exps.
      evaluate (MAP (K (Op (Const i) [])) (exps:'a list),env,t1) =
        (Rval (MAP (K (Number i)) exps),t1)``,
  Induct \\ fs [evaluate_def,evaluate_CONS,do_app_def]);

val evaluate_Bool = Q.store_thm("evaluate_Bool[simp]",
  `evaluate ([Bool b],env,s) = (Rval [Boolv b],s)`,
  EVAL_TAC)

fun split_tac q = Cases_on q \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) []

val evaluate_expand_env = Q.store_thm("evaluate_expand_env",
  `!xs a s env.
     FST (evaluate (xs,a,s)) <> Rerr(Rabort Rtype_error) ==>
     (evaluate (xs,a ++ env,s) = evaluate (xs,a,s))`,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ ASM_SIMP_TAC std_ss []
  THEN1 (split_tac `evaluate ([x],env,s)` \\ split_tac `evaluate (y::xs,env,r)`)
  THEN1 (Cases_on `n < LENGTH env` \\ FULL_SIMP_TAC (srw_ss()) []
         \\ SRW_TAC [] [rich_listTheory.EL_APPEND1] \\ DECIDE_TAC)
  THEN1 (split_tac `evaluate ([x1],env,s)` \\ SRW_TAC [] [])
  THEN1 (split_tac `evaluate (xs,env,s)`)
  THEN1 (split_tac `evaluate ([x1],env,s)`)
  THEN1 (split_tac `evaluate ([x1],env,s1)` \\ BasicProvers.CASE_TAC >> simp[])
  THEN1 (split_tac `evaluate (xs,env,s)`)
  THEN1 (SRW_TAC [] [])
  THEN1 (split_tac `evaluate (xs,env,s1)`));

val inc_clock_def = Define `
  inc_clock ck s = s with clock := s.clock + ck`;

val inc_clock_code = Q.store_thm ("inc_clock_code",
  `!n (s:'ffi bvlSem$state). (inc_clock n s).code = s.code`,
  rw [inc_clock_def]);

val inc_clock_refs = Q.store_thm ("inc_clock_refs",
  `!n (s:'ffi bvlSem$state). (inc_clock n s).refs = s.refs`,
  rw [inc_clock_def]);

val inc_clock_ffi = Q.store_thm ("inc_clock_ffi[simp]",
  `!n (s:'ffi bvlSem$state). (inc_clock n s).ffi = s.ffi`,
  rw [inc_clock_def]);

val inc_clock_clock = Q.store_thm ("inc_clock_clock[simp]",
  `!n (s:'ffi bvlSem$state). (inc_clock n s).clock = s.clock + n`,
  rw [inc_clock_def]);

val inc_clock0 = Q.store_thm ("inc_clock0",
  `!n (s:'ffi bvlSem$state). inc_clock 0 s = s`,
  simp [inc_clock_def, state_component_equality]);

val _ = export_rewrites ["inc_clock_refs", "inc_clock_code", "inc_clock0"];

val inc_clock_add = Q.store_thm("inc_clock_add",
  `inc_clock k1 (inc_clock k2 s) = inc_clock (k1 + k2) s`,
  simp[inc_clock_def,state_component_equality]);

val dec_clock_code = Q.store_thm ("dec_clock_code",
  `!n (s:'ffi bvlSem$state). (dec_clock n s).code = s.code`,
  rw [dec_clock_def]);

val dec_clock_refs = Q.store_thm ("dec_clock_refs",
  `!n (s:'ffi bvlSem$state). (dec_clock n s).refs = s.refs`,
  rw [dec_clock_def]);

val dec_clock_ffi = Q.store_thm ("dec_clock_ffi[simp]",
  `!n (s:'ffi bvlSem$state). (dec_clock n s).ffi = s.ffi`,
  rw [dec_clock_def]);

val dec_clock0 = Q.store_thm ("dec_clock0",
  `!n (s:'ffi bvlSem$state). dec_clock 0 s = s`,
  simp [dec_clock_def, state_component_equality]);

val _ = export_rewrites ["dec_clock_refs", "dec_clock_code", "dec_clock0"];

val do_app_change_clock = prove(
  ``(do_app op args s1 = Rval (res,s2)) ==>
    (do_app op args (s1 with clock := ck) = Rval (res,s2 with clock := ck))``,
  SIMP_TAC std_ss [do_app_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [] \\
  CCONTR_TAC >> fs [] >>
  rw [] >>
  fs []);

val do_app_change_clock_err = prove(
  ``(do_app op args s1 = Rerr e) ==>
    (do_app op args (s1 with clock := ck) = Rerr e)``,
  SIMP_TAC std_ss [do_app_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs []);

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
      imp_res_tac do_app_change_clock_err >>
      fs [] >>
      rw [])
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

val do_app_io_events_mono = Q.store_thm("do_app_io_events_mono",
  `do_app op vs s1 = Rval (x,s2) ⇒
   s1.ffi.io_events ≼ s2.ffi.io_events ∧
   (IS_SOME s1.ffi.final_event ⇒ s2.ffi = s1.ffi)`,
  rw[do_app_def] >> every_case_tac >> fs[LET_THM] >> rw[] >> fs[] >>
  fs[ffiTheory.call_FFI_def] >> every_case_tac >> fs[] >> rw[]);

val evaluate_io_events_mono = Q.store_thm("evaluate_io_events_mono",
  `!exps env s1 res s2.
    evaluate (exps,env,s1) = (res, s2)
    ⇒
    s1.ffi.io_events ≼ s2.ffi.io_events ∧
    (IS_SOME s1.ffi.final_event ⇒ s2.ffi = s1.ffi)`,
  recInduct evaluate_ind >>
  rw [evaluate_def] >>
  every_case_tac >> fs[] >>
  rw[] >> rfs[] >>
  metis_tac[IS_PREFIX_TRANS,do_app_io_events_mono])

val Boolv_11 = store_thm("Boolv_11[simp]",``bvlSem$Boolv b1 = Boolv b2 ⇔ b1 = b2``,EVAL_TAC>>rw[]);

val do_app_inc_clock = Q.prove(
  `do_app op vs (inc_clock x y) =
   map_result (λ(v,s). (v,s with clock := x + y.clock)) I (do_app op vs y)`,
  Cases_on`do_app op vs y` >>
  imp_res_tac do_app_change_clock_err >>
  TRY(Cases_on`a`>>imp_res_tac do_app_change_clock) >>
  fs[inc_clock_def] >> simp[])

val dec_clock_1_inc_clock = Q.prove(
  `x ≠ 0 ⇒ dec_clock 1 (inc_clock x s) = inc_clock (x-1) s`,
  simp[state_component_equality,inc_clock_def,dec_clock_def])

val dec_clock_1_inc_clock2 = Q.prove(
  `s.clock ≠ 0 ⇒ dec_clock 1 (inc_clock x s) = inc_clock x (dec_clock 1 s)`,
  simp[state_component_equality,inc_clock_def,dec_clock_def])

val dec_clock_inc_clock = Q.prove(
  `¬(s.clock < n) ⇒ dec_clock n (inc_clock x s) = inc_clock x (dec_clock n s)`,
  simp[state_component_equality,inc_clock_def,dec_clock_def])

val evaluate_add_to_clock_io_events_mono = Q.store_thm("evaluate_add_to_clock_io_events_mono",
  `∀exps env s extra.
    (SND(evaluate(exps,env,s))).ffi.io_events ≼
    (SND(evaluate(exps,env,inc_clock extra s))).ffi.io_events ∧
    (IS_SOME((SND(evaluate(exps,env,s))).ffi.final_event) ⇒
     (SND(evaluate(exps,env,inc_clock extra s))).ffi =
     (SND(evaluate(exps,env,s))).ffi)`,
  recInduct evaluate_ind >>
  rw[evaluate_def] >>
  TRY (
    qcase_tac`Boolv T` >>
    qmatch_assum_rename_tac`IS_SOME _.ffi.final_event` >>
    ntac 4 (BasicProvers.CASE_TAC >> fs[] >> rfs[]) >>
    ntac 2 (TRY (BasicProvers.CASE_TAC >> fs[] >> rfs[])) >>
    rw[] >> fs[] >> rfs[]) >>
  every_case_tac >> fs[] >> rfs[] >>
  fs[dec_clock_1_inc_clock,dec_clock_1_inc_clock2] >>
  imp_res_tac evaluate_add_clock >> rfs[] >> fs[] >> rw[] >>
  imp_res_tac evaluate_io_events_mono >> rfs[] >> fs[] >> rw[] >>
  rfs[do_app_inc_clock] >> fs[] >> rw[] >> fs[] >>
  imp_res_tac do_app_io_events_mono >>
  TRY(fsrw_tac[ARITH_ss][] >>NO_TAC) >>
  fs[dec_clock_inc_clock] >>
  metis_tac[evaluate_io_events_mono,SND,IS_PREFIX_TRANS,Boolv_11,PAIR,
            inc_clock_ffi,dec_clock_ffi]);

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
  `!xs env ys (st:'ffi bvlSem$state).
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

val evaluate_isConst = Q.store_thm("evaluate_isConst",
  `!xs. EVERY isConst xs ==>
        (evaluate (xs,env,s) = (Rval (MAP (Number o getConst) xs),s))`,
  Induct \\ fs [evaluate_def]
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ Cases \\ fs [isConst_def]
  \\ Cases_on `o'` \\ fs [isConst_def]
  \\ Cases_on `l` \\ fs [isConst_def,evaluate_def,do_app_def,getConst_def]);

val do_app_refs_SUBSET = store_thm("do_app_refs_SUBSET",
  ``(do_app op a r = Rval (q,t)) ==> FDOM r.refs SUBSET FDOM t.refs``,
  fs [do_app_def]
  \\ NTAC 5 (fs [SUBSET_DEF,IN_INSERT] \\ SRW_TAC [] []
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [LET_DEF,dec_clock_def]));

val evaluate_refs_SUBSET_lemma = prove(
  ``!xs env s. FDOM s.refs SUBSET FDOM (SND (evaluate (xs,env,s))).refs``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ fs [evaluate_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []
  \\ REV_FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC SUBSET_TRANS
  \\ fs [dec_clock_def] \\ fs []
  \\ IMP_RES_TAC do_app_refs_SUBSET \\ fs [SUBSET_DEF]);

val evaluate_refs_SUBSET = store_thm("evaluate_refs_SUBSET",
  ``(evaluate (xs,env,s) = (res,t)) ==> FDOM s.refs SUBSET FDOM t.refs``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL evaluate_refs_SUBSET_lemma) \\ fs []);

val get_vars_def = Define `
  (get_vars [] env = SOME []) /\
  (get_vars (n::ns) env =
     if n < LENGTH env then
       (case get_vars ns env of
        | NONE => NONE
        | SOME vs => SOME (EL n env :: vs))
     else NONE)`

val isVar_def = Define `
  (isVar ((Var n):bvl$exp) = T) /\ (isVar _ = F)`;

val destVar_def = Define `
  (destVar ((Var n):bvl$exp) = n)`;

val evaluate_Var_list = Q.store_thm("evaluate_Var_list",
  `!l. EVERY isVar l ==>
       (evaluate (l,env,s) = (Rerr(Rabort Rtype_error),s)) \/
       ?vs. (evaluate (l,env,s) = (Rval vs,s)) /\
            (get_vars (MAP destVar l) env = SOME vs) /\
            (LENGTH vs = LENGTH l)`,
  Induct \\ fs [evaluate_def,get_vars_def] \\ Cases \\ fs [isVar_def]
  \\ ONCE_REWRITE_TAC [evaluate_CONS] \\ fs [evaluate_def]
  \\ Cases_on `n < LENGTH env` \\ fs []
  \\ REPEAT STRIP_TAC \\ fs [destVar_def]);

val bVarBound_def = tDefine "bVarBound" `
  (bVarBound n [] <=> T) /\
  (bVarBound n ((x:bvl$exp)::y::xs) <=>
     bVarBound n [x] /\ bVarBound n (y::xs)) /\
  (bVarBound n [Var v] <=> v < n) /\
  (bVarBound n [If x1 x2 x3] <=>
     bVarBound n [x1] /\ bVarBound n [x2] /\ bVarBound n [x3]) /\
  (bVarBound n [Let xs x2] <=>
     bVarBound n xs /\ bVarBound (n + LENGTH xs) [x2]) /\
  (bVarBound n [Raise x1] <=> bVarBound n [x1]) /\
  (bVarBound n [Tick x1] <=>  bVarBound n [x1]) /\
  (bVarBound n [Op op xs] <=> bVarBound n xs) /\
  (bVarBound n [Handle x1 x2] <=>
     bVarBound n [x1] /\ bVarBound (n + 1) [x2]) /\
  (bVarBound n [Call ticks dest xs] <=> bVarBound n xs)`
  (WF_REL_TAC `measure (exp1_size o SND)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
   \\ SRW_TAC [] [bvlTheory.exp_size_def] \\ DECIDE_TAC);

val GoodHandleLet_def = Define `
  (GoodHandleLet ((Handle (Let xs b) y):bvl$exp) <=>
     EVERY isVar xs /\ bVarBound (LENGTH xs) [b]) /\
  (GoodHandleLet ((Handle _ y):bvl$exp) <=> F) /\
  (GoodHandleLet _ <=> T)`;

val bEvery_def = tDefine "bEvery" `
  (bEvery P [] <=> T) /\
  (bEvery P ((x:bvl$exp)::y::xs) <=>
     bEvery P [x] /\ bEvery P (y::xs)) /\
  (bEvery P [Var v] <=> P (Var v)) /\
  (bEvery P [If x1 x2 x3] <=> P (If x1 x2 x3) /\
     bEvery P [x1] /\ bEvery P [x2] /\ bEvery P [x3]) /\
  (bEvery P [Let xs x2] <=> P (Let xs x2) /\
     bEvery P xs /\ bEvery P [x2]) /\
  (bEvery P [Raise x1] <=> P (Raise x1) /\ bEvery P [x1]) /\
  (bEvery P [Tick x1] <=> P (Tick x1) /\ bEvery P [x1]) /\
  (bEvery P [Op op xs] <=> P (Op op xs) /\ bEvery P xs) /\
  (bEvery P [Handle x1 x2] <=> P (Handle x1 x2) /\
     bEvery P [x1] /\ bEvery P [x2]) /\
  (bEvery P [Call ticks dest xs] <=> P (Call ticks dest xs) /\ bEvery P xs)`
  (WF_REL_TAC `measure (exp1_size o SND)`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
   \\ SRW_TAC [] [bvlTheory.exp_size_def] \\ DECIDE_TAC);

val _ = export_rewrites["bEvery_def","GoodHandleLet_def","bVarBound_def"];

val bVarBound_EVERY = Q.store_thm("bVarBound_EVERY",
  `∀ls. bVarBound P ls ⇔ EVERY (λe. bVarBound P [e]) ls`,
  Induct >> simp[] >> Cases >> simp[] >>
  Cases_on`ls`>>simp[]);

val bEvery_EVERY = Q.store_thm("bEvery_EVERY",
  `∀ls. bEvery P ls ⇔ EVERY (λe. bEvery P [e]) ls`,
  Induct >> simp[] >> Cases >> simp[] >>
  Cases_on`ls`>>simp[]);

val _ = export_theory();
