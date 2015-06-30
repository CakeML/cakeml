open preamble bviSemTheory;

val _ = new_theory"bviProps";

val bvl_to_bvi_id = store_thm("bvl_to_bvi_id",
  ``bvl_to_bvi (bvi_to_bvl s) s = s``,
  EVAL_TAC \\ fs [bviSemTheory.state_component_equality]);

val bvl_to_bvi_with_refs = Q.store_thm("bvl_to_bvi_with_refs",
  `bvl_to_bvi (x with refs := y) z = bvl_to_bvi x z with <| refs := y |>`,
  EVAL_TAC)

val bvl_to_bvi_with_io = Q.store_thm("bvl_to_bvi_with_io",
  `bvl_to_bvi (x with io := y) z = bvl_to_bvi x z with io := y`,
  EVAL_TAC)

val evaluate_LENGTH = prove(
  ``!xs s env. (\(xs,s,env).
      (case evaluate (xs,s,env) of (Rval res,s1) => (LENGTH xs = LENGTH res)
            | _ => T))
      (xs,s,env)``,
  HO_MATCH_MP_TAC evaluate_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [evaluate_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  |> SIMP_RULE std_ss [];

val _ = save_thm("evaluate_LENGTH", evaluate_LENGTH);

val evaluate_IMP_LENGTH = store_thm("evaluate_IMP_LENGTH",
  ``(evaluate (xs,s,env) = (Rval res,s1)) ==> (LENGTH xs = LENGTH res)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL evaluate_LENGTH) \\ fs []);

val evaluate_SING_IMP = store_thm("evaluate_SING_IMP",
  ``(evaluate ([x],env,s1) = (Rval vs,s2)) ==> ?w. vs = [w]``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `vs` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ FULL_SIMP_TAC (srw_ss()) []);

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

val inc_clock_def = Define `
  inc_clock n (s:bviSem$state) = s with clock := s.clock + n`;

val inc_clock_ZERO = store_thm("inc_clock_ZERO",
  ``!s. inc_clock 0 s = s``,
  fs [inc_clock_def,state_component_equality]);

val inc_clock_ADD = store_thm("inc_clock_ADD",
  ``inc_clock n (inc_clock m s) = inc_clock (n+m) s``,
  fs [inc_clock_def,state_component_equality,AC ADD_ASSOC ADD_COMM]);

val dec_clock_inv_clock = store_thm("dec_clock_inv_clock",
  ``¬(t1.clock < ticks + 1) ==>
    (dec_clock (ticks + 1) (inc_clock c t1) = inc_clock c (dec_clock (ticks + 1) t1))``,
  fs [dec_clock_def,inc_clock_def,state_component_equality] \\ DECIDE_TAC);

val dec_clock_inv_clock1 = store_thm("dec_clock_inv_clock1",
  ``t1.clock <> 0 ==>
    (dec_clock 1 (inc_clock c t1) = inc_clock c (dec_clock 1 t1))``,
  fs [dec_clock_def,inc_clock_def,state_component_equality] \\ DECIDE_TAC);

val do_app_inv_clock = prove(
  ``case do_app op (REVERSE a) s of
    | Rerr e => (do_app op (REVERSE a) (inc_clock n s) = Rerr e)
    | Rval (v,s1) => (do_app op (REVERSE a) (inc_clock n s) = Rval (v,inc_clock n s1))``,
  fs [bviSemTheory.do_app_def] \\ Cases_on `op` \\ fs [do_app_aux_def,bvlSemTheory.do_app_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [bvi_to_bvl_def,closSemTheory.get_global_def,inc_clock_def,bvl_to_bvi_def,LET_DEF]
  \\ SRW_TAC [] [] \\ REV_FULL_SIMP_TAC std_ss []);

val evaluate_inv_clock = store_thm("evaluate_inv_clock",
  ``!xs env t1 res t2 n.
      (evaluate (xs,env,t1) = (res,t2)) /\ res <> Rerr(Rabort Rtimeout_error) ==>
      (evaluate (xs,env,inc_clock n t1) = (res,inc_clock n t2))``,
  SIMP_TAC std_ss [] \\ recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ fs [evaluate_def]
  THEN1 (`?res5 s5. evaluate ([x],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ `?res6 s6. evaluate (y::xs,env,s5) = (res6,s6)` by METIS_TAC [PAIR]
    \\ fs [] \\ REVERSE (Cases_on `res5`) \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on `res6` \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on`e` \\ fs[])
  THEN1 (Cases_on `n < LENGTH env` \\ fs [] \\ SRW_TAC [] [])
  \\ TRY (`?res5 s5. evaluate ([x1],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ fs [] \\ Cases_on `res5` \\ fs [] \\ SRW_TAC [] [] \\ fs [] \\ NO_TAC)
  THEN1 (`?res5 s5. evaluate (xs,env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ fs [] \\ Cases_on `res5` \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on`e` \\ fs[])
  \\ TRY (Cases_on `s.clock = 0` \\ fs []
    \\ `(inc_clock n s).clock <> 0` by (EVAL_TAC \\ DECIDE_TAC)
    \\ fs [dec_clock_inv_clock1] \\ NO_TAC)
  THEN1
   (`?res5 s5. evaluate (xs,env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ fs [] \\ Cases_on `res5` \\ fs [] \\ SRW_TAC [] []
    \\ TRY (Cases_on`e` \\ fs[] \\ NO_TAC)
    \\ MP_TAC (do_app_inv_clock |> Q.INST [`s`|->`s5`])
    \\ Cases_on `do_app op (REVERSE a) s5` \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on `a'` \\ fs [] \\ SRW_TAC [] [])
  THEN1
   (Cases_on `dest = NONE /\ IS_SOME handler` \\ fs []
    \\ Cases_on `evaluate (xs,env,s1)` \\ fs []
    \\ Cases_on `q` \\ fs []
    \\ `(inc_clock n r).code = r.code` by SRW_TAC [] [inc_clock_def] \\ fs []
    \\ Cases_on `find_code dest a r.code` \\ fs [] \\ SRW_TAC [] []
    \\ TRY (Cases_on`e` \\ fs[] \\ NO_TAC)
    \\ Cases_on `x` \\ fs []
    \\ Cases_on `r.clock < ticks + 1` \\ fs [] \\ SRW_TAC [] []
    \\ IMP_RES_TAC dec_clock_inv_clock
    \\ POP_ASSUM (ASSUME_TAC o GSYM)
    \\ Cases_on `evaluate ([r'],q,dec_clock (ticks + 1) r)` \\ fs []
    \\ Cases_on `q'` \\ fs [] \\ SRW_TAC [] []
    \\ TRY(Cases_on`e` \\ fs[] \\ Cases_on`a'` \\ fs[] \\ rw[])
    \\ RES_TAC \\ TRY (fs [inc_clock_def] \\ decide_tac)
    \\ Cases_on `handler` \\ fs [] \\ rw[]));

val evaluate_code_const_lemma = prove(
  ``!xs env s. (SND (evaluate (xs,env,s))).code = s.code``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ fs [evaluate_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ fs [dec_clock_def]
  \\ fs [do_app_def]
  \\ REVERSE (Cases_on `do_app_aux op a r`) \\ fs []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []
  \\ SRW_TAC [] [] \\ fs [bvl_to_bvi_def] \\ fs [do_app_aux_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []);

val evaluate_code_const = store_thm("evaluate_code_const",
  ``!xs env s res t. (evaluate (xs,env,s) = (res,t)) ==> (t.code = s.code)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL evaluate_code_const_lemma) \\ fs []);

val do_app_code = store_thm("do_app_code",
  ``!op s1 s2. (do_app op a s1 = Rval (x0,s2)) ==> (s2.code = s1.code)``,
  SIMP_TAC std_ss [do_app_def] \\ REPEAT STRIP_TAC
  \\ every_case_tac \\ fs []
  \\ Cases_on `do_app_aux op a s1` \\ fs []
  \\ Cases_on `x` \\ fs [] THEN1
   (Cases_on `do_app op a (bvi_to_bvl s1)` \\ fs []
    \\ rw[bvl_to_bvi_def])
  \\ Cases_on `op` \\ fs [do_app_aux_def]
  \\ Cases_on `a` \\ fs []
  \\ rw[]);

val do_app_err = Q.store_thm("do_app_err",
  `do_app op a s = Rerr e ⇒ e = Rabort Rtype_error`,
  rw[bviSemTheory.do_app_def] >>
  every_case_tac >> fs[] >> rw[] >>
  imp_res_tac bvlPropsTheory.do_app_err >> rw[]);

val _ = export_theory();
