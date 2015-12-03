open preamble bviSemTheory;

val _ = new_theory"bviProps";

val initial_state_simp = Q.store_thm("initial_state_simp[simp]",
  `(initial_state f c k).code = c ∧
   (initial_state f c k).ffi = f ∧
   (initial_state f c k).clock = k ∧
   (initial_state f c k).refs = FEMPTY ∧
   (initial_state f c k).global = NONE`,
   rw[initial_state_def]);

val bvl_to_bvi_id = store_thm("bvl_to_bvi_id",
  ``bvl_to_bvi (bvi_to_bvl s) s = s``,
  EVAL_TAC \\ fs [bviSemTheory.state_component_equality]);

val bvl_to_bvi_with_refs = Q.store_thm("bvl_to_bvi_with_refs",
  `bvl_to_bvi (x with refs := y) z = bvl_to_bvi x z with <| refs := y |>`,
  EVAL_TAC)

val bvl_to_bvi_with_clock = Q.store_thm("bvl_to_bvi_with_clock",
  `bvl_to_bvi (x with clock := y) z = bvl_to_bvi x z with <| clock := y |>`,
  EVAL_TAC)

val bvl_to_bvi_with_ffi = Q.store_thm("bvl_to_bvi_with_ffi",
  `bvl_to_bvi (x with ffi := y) z = bvl_to_bvi x z with ffi := y`,
  EVAL_TAC)

val bvl_to_bvi_code = Q.store_thm("bvl_to_bvi_code[simp]",
  `(bvl_to_bvi x y).code = y.code`,
  EVAL_TAC)

val bvl_to_bvi_clock = Q.store_thm("bvl_to_bvi_clock[simp]",
  `(bvl_to_bvi x y).clock = x.clock`,
  EVAL_TAC)

val bvi_to_bvl_refs = Q.store_thm("bvi_to_bvl_refs[simp]",
  `(bvi_to_bvl x).refs = x.refs`, EVAL_TAC)

val bvi_to_bvl_code = Q.store_thm("bvi_to_bvl_code[simp]",
  `(bvi_to_bvl x).code = map (K ARB) x.code`, EVAL_TAC)

val bvi_to_bvl_clock = Q.store_thm("bvi_to_bvl_clock[simp]",
  `(bvi_to_bvl x).clock = x.clock`, EVAL_TAC)

val domain_bvi_to_bvl_code = Q.store_thm("domain_bvi_to_bvl_code[simp]",
  `domain (bvi_to_bvl s).code = domain s.code`,
  rw[bvi_to_bvl_def,domain_map])

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

val inc_clock_def = Define `
  inc_clock n (s:'ffi bviSem$state) = s with clock := s.clock + n`;

val inc_clock_ZERO = store_thm("inc_clock_ZERO",
  ``!s. inc_clock 0 s = s``,
  fs [inc_clock_def,state_component_equality]);

val inc_clock_ADD = store_thm("inc_clock_ADD",
  ``inc_clock n (inc_clock m s) = inc_clock (n+m) s``,
  fs [inc_clock_def,state_component_equality,AC ADD_ASSOC ADD_COMM]);

val inc_clock_refs = Q.store_thm("inc_clock_refs[simp]",
  `(inc_clock n s).refs = s.refs`,EVAL_TAC)

val inc_clock_code = Q.store_thm("inc_clock_code[simp]",
  `(inc_clock n s).code = s.code`,EVAL_TAC)

val inc_clock_global = Q.store_thm("inc_clock_global[simp]",
  `(inc_clock n s).global = s.global`,
  rw[inc_clock_def])

val dec_clock_global = Q.store_thm("dec_clock_global[simp]",
  `(dec_clock n s).global = s.global`,
  rw[dec_clock_def])

val dec_clock_refs = Q.store_thm("dec_clock_refs[simp]",
  `(dec_clock n s).refs = s.refs`,
  rw[dec_clock_def])

val dec_clock_with_code = Q.store_thm("dec_clock_with_code[simp]",
  `bviSem$dec_clock n (s with code := c) = dec_clock n s with code := c`,
  EVAL_TAC );

val dec_clock_code = Q.store_thm("dec_clock_code[simp]",
  `(dec_clock n s).code = s.code`,
  rw[dec_clock_def])

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
    \\ fs [] \\ reverse (Cases_on `res5`) \\ fs [] \\ SRW_TAC [] []
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
  \\ reverse (Cases_on `do_app_aux op a r`) \\ fs []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []
  \\ SRW_TAC [] [] \\ fs [bvl_to_bvi_def] \\ fs [do_app_aux_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rw[]);

val evaluate_code_const = store_thm("evaluate_code_const",
  ``!xs env s res t. (evaluate (xs,env,s) = (res,t)) ==> (t.code = s.code)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL evaluate_code_const_lemma) \\ fs []);

val evaluate_global_mono_lemma = Q.prove(
  `∀xs env s. IS_SOME s.global ⇒ IS_SOME((SND (evaluate (xs,env,s))).global)`,
  recInduct evaluate_ind >> rpt strip_tac >>
  rw[evaluate_def] >> every_case_tac >> fs[] >> rfs[] >>
  fs[do_app_def] >>
  every_case_tac >> fs[] >> rw[] >>
  rw[bvl_to_bvi_def] >>
  fs[do_app_aux_def] >>
  every_case_tac >> fs[] >> rw[]);

val evaluate_global_mono = Q.store_thm("evaluate_global_mono",
  `∀xs env s res t. (evaluate (xs,env,s) = (res,t)) ⇒ IS_SOME s.global ⇒ IS_SOME t.global`,
  METIS_TAC[SND,evaluate_global_mono_lemma]);

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
  \\ rw[]
  \\ every_case_tac >> fs[] >> rw[]);

val do_app_err = Q.store_thm("do_app_err",
  `do_app op a s = Rerr e ⇒ e = Rabort Rtype_error`,
  rw[bviSemTheory.do_app_def] >>
  every_case_tac >> fs[] >> rw[] >>
  imp_res_tac bvlPropsTheory.do_app_err >> rw[]);

val do_app_aux_with_code = Q.store_thm("do_app_aux_with_code",
  `do_app_aux op vs (s with code := c) =
   OPTION_MAP (OPTION_MAP (λ(x,y). (x,y with code := c))) (do_app_aux op vs s)`,
  rw[do_app_aux_def] >>
  every_case_tac >> fs[]);

val do_app_with_code = Q.store_thm("do_app_with_code",
  `bviSem$do_app op vs s = Rval (r,s') ⇒
   domain s.code ⊆ domain c ⇒
   do_app op vs (s with code := c) = Rval (r,s' with code := c)`,
  rw[do_app_def,do_app_aux_with_code] >>
  Cases_on`do_app_aux op vs s`>>fs[]>>
  reverse(Cases_on`x`)>>fs[]>- (
    every_case_tac >> fs[] ) >>
  Cases_on`do_app op vs (bvi_to_bvl s)` >> fs[] >>
  every_case_tac >> fs[] >> rpt var_eq_tac >>
  fs[bvi_to_bvl_def] >>
  imp_res_tac bvlPropsTheory.do_app_with_code >> fs[domain_map] >>
  fs[bvlSemTheory.state_component_equality] >>
  fs[bvl_to_bvi_def,bviSemTheory.state_component_equality] >>
  rpt(first_x_assum(qspec_then`map (K ARB) c`mp_tac)) >>
  simp[domain_map,bvlSemTheory.state_component_equality] );

val do_app_with_code_err = Q.store_thm("do_app_with_code_err",
  `bviSem$do_app op vs s = Rerr e ⇒
   (domain c ⊆ domain s.code ∨ e ≠ Rabort Rtype_error) ⇒
   do_app op vs (s with code := c) = Rerr e`,
  rw[do_app_def,do_app_aux_with_code] >>
  Cases_on`do_app_aux op vs s`>>fs[]>>
  (reverse(Cases_on`x`)>>fs[]>- (
     every_case_tac >> fs[] )) >>
  Cases_on`do_app op vs (bvi_to_bvl s)` >> fs[] >>
  every_case_tac >> fs[] >> rpt var_eq_tac >>
  fs[bvi_to_bvl_def] >>
  imp_res_tac bvlPropsTheory.do_app_with_code >> fs[domain_map] >>
  imp_res_tac bvlPropsTheory.do_app_with_code_err >> fs[domain_map] >>
  fs[bvlSemTheory.state_component_equality] >>
  fs[bvl_to_bvi_def,bviSemTheory.state_component_equality] >>
  TRY(
    rpt(first_x_assum(qspec_then`map (K ARB) s.code`mp_tac)) >>
    simp[domain_map,bvlSemTheory.state_component_equality] >>
    NO_TAC) >>
  rpt(first_x_assum(qspec_then`map (K ARB) c`mp_tac)) >>
  simp[domain_map,bvlSemTheory.state_component_equality]);

val find_code_add_code = Q.store_thm("find_code_add_code",
  `bvlSem$find_code dest a (fromAList code) = SOME x ⇒
   find_code dest a (fromAList (code ++ extra)) = SOME x`,
  Cases_on`dest`>>rw[bvlSemTheory.find_code_def] >>
  every_case_tac >> fs[] >>
  fs[lookup_fromAList,ALOOKUP_APPEND] >> rw[]);

val evaluate_add_code = Q.store_thm("evaluate_add_code",
  `∀xs env s r s'.
    evaluate (xs,env,s) = (r,s') ∧ r ≠ Rerr (Rabort Rtype_error) ∧
    s.code = fromAList code
    ⇒
    evaluate (xs,env,s with code := fromAList (code ++ extra)) =
      (r,s' with code := fromAList (code ++ extra))`,
  recInduct evaluate_ind >>
  rw[evaluate_def] >>
  TRY (
    qcase_tac`Boolv T = HD _` >>
    BasicProvers.CASE_TAC >> fs[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    rpt(IF_CASES_TAC >> fs[]) >>
    TRY(qpat_assum`_ = HD _`(assume_tac o SYM))>>fs[]>>
    every_case_tac >> fs[] >> rw[] >> rfs[] >> rw[] >>
    imp_res_tac evaluate_code_const >> fs[] >> rfs[] >>
    (qpat_assum`_ = HD _`(assume_tac o SYM))>>fs[] ) >>
  TRY (
    qcase_tac`bviSem$do_app` >>
    every_case_tac >> fs[] >> rw[] >>
    imp_res_tac evaluate_code_const >> fs[] >>
    imp_res_tac do_app_code >> fs[] >> rfs[] >>
    rw[] >> fs[] >>
    TRY (
      drule (GEN_ALL do_app_with_code) >>
      disch_then(qspec_then`fromAList (code ++ extra)`mp_tac) >>
      simp[domain_fromAList] >> NO_TAC) >>
    drule (GEN_ALL do_app_with_code_err) >>
    disch_then(qspec_then`fromAList (code++extra)`mp_tac) >>
    simp[] >> NO_TAC) >>
  TRY (
    qcase_tac`bvlSem$find_code` >>
    every_case_tac >> fs[] >>
    rpt var_eq_tac >> fs[] >> rfs[] >>
    rw[] >> fs[] >> rfs[] >>
    imp_res_tac evaluate_code_const >> fs[] >> rfs[] >>
    imp_res_tac find_code_add_code >> fs[] >> rw[] >> fs[] >>
    rw[] >> NO_TAC) >>
  every_case_tac >> fs[] >> rw[] >> rfs[] >> rw[] >>
  imp_res_tac evaluate_code_const >> fs[] >> rfs[]);

val _ = export_theory();
