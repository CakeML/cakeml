open preamble bviSemTheory;
local open bvlPropsTheory in end;

val _ = new_theory"bviProps";

val initial_state_simp = Q.store_thm("initial_state_simp[simp]",
  `(initial_state f c k).code = c ∧
   (initial_state f c k).ffi = f ∧
   (initial_state f c k).clock = k ∧
   (initial_state f c k).refs = FEMPTY ∧
   (initial_state f c k).global = NONE`,
   srw_tac[][initial_state_def]);

val initial_state_with_simp = Q.store_thm("initial_state_with_simp[simp]",
  `initial_state f c k with clock := k1 = initial_state f c k1 ∧
   initial_state f c k with code := c1 = initial_state f c1 k`,
  EVAL_TAC);

val bvl_to_bvi_id = store_thm("bvl_to_bvi_id",
  ``bvl_to_bvi (bvi_to_bvl s) s = s``,
  EVAL_TAC \\ full_simp_tac(srw_ss())[bviSemTheory.state_component_equality]);

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

val bvi_to_bvl_ffi = Q.store_thm("bvi_to_bvl_ffi[simp]",
  `(bvi_to_bvl x).ffi = x.ffi`, EVAL_TAC);

val bvi_to_bvl_to_bvi_with_ffi = Q.store_thm("bvi_to_bvl_to_bvi_with_ffi",
  `bvl_to_bvi (bvi_to_bvl x with ffi := f) x = x with ffi := f`,
  EVAL_TAC \\ rw[state_component_equality]);

val domain_bvi_to_bvl_code = Q.store_thm("domain_bvi_to_bvl_code[simp]",
  `domain (bvi_to_bvl s).code = domain s.code`,
  srw_tac[][bvi_to_bvl_def,domain_map])

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
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL evaluate_LENGTH) \\ full_simp_tac(srw_ss())[]);

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
  Cases_on `xs` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ Cases_on `evaluate ([x],env,s)` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ Cases_on `q` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]);

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
   (full_simp_tac(srw_ss())[SNOC_APPEND,evaluate_def] \\ REPEAT STRIP_TAC
    \\ Cases_on `evaluate ([x],env,s)` \\ Cases_on `q` \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[SNOC_APPEND,APPEND]
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `evaluate ([h],env,s)` \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `evaluate (xs,env,r)` \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `evaluate ([x],env,r')` \\ Cases_on `q` \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a''` \\ full_simp_tac(srw_ss())[LENGTH]
  \\ REV_FULL_SIMP_TAC std_ss [LENGTH_NIL] \\ full_simp_tac(srw_ss())[]);

val evaluate_APPEND = store_thm("evaluate_APPEND",
  ``!xs env s ys.
      evaluate (xs ++ ys,env,s) =
      case evaluate (xs,env,s) of
        (Rval vs,s2) =>
          (case evaluate (ys,env,s2) of
             (Rval ws,s1) => (Rval (vs ++ ws),s1)
           | res => res)
      | res => res``,
  Induct \\ full_simp_tac(srw_ss())[APPEND,evaluate_def] \\ REPEAT STRIP_TAC
  THEN1 REPEAT BasicProvers.CASE_TAC
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ REPEAT BasicProvers.CASE_TAC \\ full_simp_tac(srw_ss())[]);

val inc_clock_def = Define `
  inc_clock n (s:'ffi bviSem$state) = s with clock := s.clock + n`;

val inc_clock_ZERO = store_thm("inc_clock_ZERO",
  ``!s. inc_clock 0 s = s``,
  full_simp_tac(srw_ss())[inc_clock_def,state_component_equality]);

val inc_clock_ADD = store_thm("inc_clock_ADD",
  ``inc_clock n (inc_clock m s) = inc_clock (n+m) s``,
  full_simp_tac(srw_ss())[inc_clock_def,state_component_equality,AC ADD_ASSOC ADD_COMM]);

val inc_clock_refs = Q.store_thm("inc_clock_refs[simp]",
  `(inc_clock n s).refs = s.refs`,EVAL_TAC)

val inc_clock_code = Q.store_thm("inc_clock_code[simp]",
  `(inc_clock n s).code = s.code`,EVAL_TAC)

val inc_clock_global = Q.store_thm("inc_clock_global[simp]",
  `(inc_clock n s).global = s.global`,
  srw_tac[][inc_clock_def])

val inc_clock_ffi = Q.store_thm("inc_clock_ffi[simp]",
  `(inc_clock n s).ffi = s.ffi`,
  srw_tac[][inc_clock_def])

val inc_clock_clock = Q.store_thm("inc_clock_clock[simp]",
  `(inc_clock n s).clock = s.clock + n`,
  srw_tac[][inc_clock_def])

val dec_clock_global = Q.store_thm("dec_clock_global[simp]",
  `(dec_clock n s).global = s.global`,
  srw_tac[][dec_clock_def])

val dec_clock_ffi = Q.store_thm("dec_clock_ffi[simp]",
  `(dec_clock n s).ffi = s.ffi`,
  srw_tac[][dec_clock_def])

val dec_clock_refs = Q.store_thm("dec_clock_refs[simp]",
  `(dec_clock n s).refs = s.refs`,
  srw_tac[][dec_clock_def])

val dec_clock_with_code = Q.store_thm("dec_clock_with_code[simp]",
  `bviSem$dec_clock n (s with code := c) = dec_clock n s with code := c`,
  EVAL_TAC );

val dec_clock_code = Q.store_thm("dec_clock_code[simp]",
  `(dec_clock n s).code = s.code`,
  srw_tac[][dec_clock_def])

val dec_clock_inv_clock = store_thm("dec_clock_inv_clock",
  ``¬(t1.clock < ticks + 1) ==>
    (dec_clock (ticks + 1) (inc_clock c t1) = inc_clock c (dec_clock (ticks + 1) t1))``,
  full_simp_tac(srw_ss())[dec_clock_def,inc_clock_def,state_component_equality] \\ DECIDE_TAC);

val dec_clock_inv_clock1 = store_thm("dec_clock_inv_clock1",
  ``t1.clock <> 0 ==>
    (dec_clock 1 (inc_clock c t1) = inc_clock c (dec_clock 1 t1))``,
  full_simp_tac(srw_ss())[dec_clock_def,inc_clock_def,state_component_equality] \\ DECIDE_TAC);

val dec_clock0 = Q.store_thm ("dec_clock0[simp]",
  `!n (s:'ffi bviSem$state). dec_clock 0 s = s`,
  simp [dec_clock_def, state_component_equality]);

val do_app_inv_clock = prove(
  ``case do_app op (REVERSE a) s of
    | Rerr e => (do_app op (REVERSE a) (inc_clock n s) = Rerr e)
    | Rval (v,s1) => (do_app op (REVERSE a) (inc_clock n s) = Rval (v,inc_clock n s1))``,
  full_simp_tac(srw_ss())[bviSemTheory.do_app_def] \\ Cases_on `op` \\ full_simp_tac(srw_ss())[do_app_aux_def,bvlSemTheory.do_app_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ full_simp_tac(srw_ss())[bvi_to_bvl_def,closSemTheory.get_global_def,inc_clock_def,bvl_to_bvi_def,LET_DEF]
  \\ SRW_TAC [] [] \\ REV_FULL_SIMP_TAC std_ss []);

val evaluate_inv_clock = store_thm("evaluate_inv_clock",
  ``!xs env t1 res t2 n.
      (evaluate (xs,env,t1) = (res,t2)) /\ res <> Rerr(Rabort Rtimeout_error) ==>
      (evaluate (xs,env,inc_clock n t1) = (res,inc_clock n t2))``,
  SIMP_TAC std_ss [] \\ recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[evaluate_def]
  THEN1 (`?res5 s5. evaluate ([x],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ `?res6 s6. evaluate (y::xs,env,s5) = (res6,s6)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ Cases_on `res6` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ Cases_on`e` \\ full_simp_tac(srw_ss())[])
  THEN1 (Cases_on `n < LENGTH env` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [])
  \\ TRY (`?res5 s5. evaluate ([x1],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `res5` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
  THEN1 (`?res5 s5. evaluate (xs,env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `res5` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ Cases_on`e` \\ full_simp_tac(srw_ss())[])
  \\ TRY (Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[]
    \\ `(inc_clock n s).clock <> 0` by (EVAL_TAC \\ DECIDE_TAC)
    \\ full_simp_tac(srw_ss())[dec_clock_inv_clock1] \\ NO_TAC)
  THEN1
   (`?res5 s5. evaluate (xs,env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `res5` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ TRY (Cases_on`e` \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ MP_TAC (do_app_inv_clock |> Q.INST [`s`|->`s5`])
    \\ Cases_on `do_app op (REVERSE a) s5` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ Cases_on `a'` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [])
  THEN1
   (Cases_on `dest = NONE /\ IS_SOME handler` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `evaluate (xs,env,s1)` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
    \\ `(inc_clock n r).code = r.code` by SRW_TAC [] [inc_clock_def] \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `find_code dest a r.code` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ TRY (Cases_on`e` \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `r.clock < ticks + 1` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ IMP_RES_TAC dec_clock_inv_clock
    \\ POP_ASSUM (ASSUME_TAC o GSYM)
    \\ Cases_on `evaluate ([r'],q,dec_clock (ticks + 1) r)` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `q'` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ TRY(Cases_on`e` \\ full_simp_tac(srw_ss())[] \\ Cases_on`a'` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][])
    \\ RES_TAC \\ TRY (full_simp_tac(srw_ss())[inc_clock_def] \\ decide_tac)
    \\ Cases_on `handler` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]));

val evaluate_code_const_lemma = prove(
  ``!xs env s. (SND (evaluate (xs,env,s))).code = s.code``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ REV_FULL_SIMP_TAC std_ss [] \\ full_simp_tac(srw_ss())[dec_clock_def]
  \\ full_simp_tac(srw_ss())[do_app_def]
  \\ reverse (Cases_on `do_app_aux op a r`) \\ full_simp_tac(srw_ss())[]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[bvl_to_bvi_def] \\ full_simp_tac(srw_ss())[do_app_aux_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]);

val evaluate_code_const = store_thm("evaluate_code_const",
  ``!xs env s res t. (evaluate (xs,env,s) = (res,t)) ==> (t.code = s.code)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL evaluate_code_const_lemma) \\ full_simp_tac(srw_ss())[]);

val evaluate_global_mono_lemma = Q.prove(
  `∀xs env s. IS_SOME s.global ⇒ IS_SOME((SND (evaluate (xs,env,s))).global)`,
  recInduct evaluate_ind >> rpt strip_tac >>
  srw_tac[][evaluate_def] >> every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[do_app_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  srw_tac[][bvl_to_bvi_def] >>
  full_simp_tac(srw_ss())[do_app_aux_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

val evaluate_global_mono = Q.store_thm("evaluate_global_mono",
  `∀xs env s res t. (evaluate (xs,env,s) = (res,t)) ⇒ IS_SOME s.global ⇒ IS_SOME t.global`,
  METIS_TAC[SND,evaluate_global_mono_lemma]);

val do_app_code = store_thm("do_app_code",
  ``!op s1 s2. (do_app op a s1 = Rval (x0,s2)) ==> (s2.code = s1.code)``,
  SIMP_TAC std_ss [do_app_def] \\ REPEAT STRIP_TAC
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `do_app_aux op a s1` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `x` \\ full_simp_tac(srw_ss())[] THEN1
   (Cases_on `do_app op a (bvi_to_bvl s1)` \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][bvl_to_bvi_def])
  \\ Cases_on `op` \\ full_simp_tac(srw_ss())[do_app_aux_def]
  \\ Cases_on `a` \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][]
  \\ every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

val do_app_err = Q.store_thm("do_app_err",
  `do_app op a s = Rerr e ⇒ e = Rabort Rtype_error`,
  srw_tac[][bviSemTheory.do_app_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac bvlPropsTheory.do_app_err >> srw_tac[][]);

val do_app_aux_const = Q.store_thm("do_app_aux_const",
  `do_app_aux op vs s = SOME (SOME (y,z)) ⇒
   z.clock = s.clock`,
  Cases_on`op`>>srw_tac[][do_app_aux_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][])

val do_app_aux_with_code = Q.store_thm("do_app_aux_with_code",
  `do_app_aux op vs (s with code := c) =
   OPTION_MAP (OPTION_MAP (λ(x,y). (x,y with code := c))) (do_app_aux op vs s)`,
  srw_tac[][do_app_aux_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[]);

val do_app_with_code = Q.store_thm("do_app_with_code",
  `bviSem$do_app op vs s = Rval (r,s') ⇒
   domain s.code ⊆ domain c ⇒
   do_app op vs (s with code := c) = Rval (r,s' with code := c)`,
  srw_tac[][do_app_def,do_app_aux_with_code] >>
  Cases_on`do_app_aux op vs s`>>full_simp_tac(srw_ss())[]>>
  reverse(Cases_on`x`)>>full_simp_tac(srw_ss())[]>- (
    every_case_tac >> full_simp_tac(srw_ss())[] ) >>
  Cases_on`do_app op vs (bvi_to_bvl s)` >> full_simp_tac(srw_ss())[] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
  full_simp_tac(srw_ss())[bvi_to_bvl_def] >>
  imp_res_tac bvlPropsTheory.do_app_with_code >> full_simp_tac(srw_ss())[domain_map] >>
  full_simp_tac(srw_ss())[bvlSemTheory.state_component_equality] >>
  full_simp_tac(srw_ss())[bvl_to_bvi_def,bviSemTheory.state_component_equality] >>
  rpt(first_x_assum(qspec_then`map (K ARB) c`mp_tac)) >>
  simp[domain_map,bvlSemTheory.state_component_equality] );

val do_app_with_code_err = Q.store_thm("do_app_with_code_err",
  `bviSem$do_app op vs s = Rerr e ⇒
   (domain c ⊆ domain s.code ∨ e ≠ Rabort Rtype_error) ⇒
   do_app op vs (s with code := c) = Rerr e`,
  srw_tac[][do_app_def,do_app_aux_with_code] >>
  Cases_on`do_app_aux op vs s`>>full_simp_tac(srw_ss())[]>>
  (reverse(Cases_on`x`)>>full_simp_tac(srw_ss())[]>- (
     every_case_tac >> full_simp_tac(srw_ss())[] )) >>
  Cases_on`do_app op vs (bvi_to_bvl s)` >> full_simp_tac(srw_ss())[] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
  full_simp_tac(srw_ss())[bvi_to_bvl_def] >>
  imp_res_tac bvlPropsTheory.do_app_with_code >> full_simp_tac(srw_ss())[domain_map] >>
  imp_res_tac bvlPropsTheory.do_app_with_code_err >> full_simp_tac(srw_ss())[domain_map] >>
  full_simp_tac(srw_ss())[bvlSemTheory.state_component_equality] >>
  full_simp_tac(srw_ss())[bvl_to_bvi_def,bviSemTheory.state_component_equality] >>
  TRY(
    rpt(first_x_assum(qspec_then`map (K ARB) s.code`mp_tac)) >>
    simp[domain_map,bvlSemTheory.state_component_equality] >>
    NO_TAC) >>
  rpt(first_x_assum(qspec_then`map (K ARB) c`mp_tac)) >>
  simp[domain_map,bvlSemTheory.state_component_equality]);

val find_code_add_code = Q.store_thm("find_code_add_code",
  `bvlSem$find_code dest a (fromAList code) = SOME x ⇒
   find_code dest a (fromAList (code ++ extra)) = SOME x`,
  Cases_on`dest`>>srw_tac[][bvlSemTheory.find_code_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[lookup_fromAList,ALOOKUP_APPEND] >> srw_tac[][]);

val evaluate_add_code = Q.store_thm("evaluate_add_code",
  `∀xs env s r s'.
    evaluate (xs,env,s) = (r,s') ∧ r ≠ Rerr (Rabort Rtype_error) ∧
    s.code = fromAList code
    ⇒
    evaluate (xs,env,s with code := fromAList (code ++ extra)) =
      (r,s' with code := fromAList (code ++ extra))`,
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def] >>
  TRY (
    qcase_tac`Boolv T = HD _` >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    rpt(IF_CASES_TAC >> full_simp_tac(srw_ss())[]) >>
    TRY(qpat_assum`_ = HD _`(assume_tac o SYM))>>full_simp_tac(srw_ss())[]>>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    imp_res_tac evaluate_code_const >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    (qpat_assum`_ = HD _`(assume_tac o SYM))>>full_simp_tac(srw_ss())[] ) >>
  TRY (
    qcase_tac`bviSem$do_app` >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    imp_res_tac evaluate_code_const >> full_simp_tac(srw_ss())[] >>
    imp_res_tac do_app_code >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    TRY (
      drule (GEN_ALL do_app_with_code) >>
      disch_then(qspec_then`fromAList (code ++ extra)`mp_tac) >>
      simp[domain_fromAList] >> NO_TAC) >>
    drule (GEN_ALL do_app_with_code_err) >>
    disch_then(qspec_then`fromAList (code++extra)`mp_tac) >>
    simp[] >> NO_TAC) >>
  TRY (
    qcase_tac`bvlSem$find_code` >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_code_const >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac find_code_add_code >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    srw_tac[][] >> NO_TAC) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_code_const >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]);

val do_app_aux_with_clock = Q.store_thm("do_app_aux_with_clock",
  `do_app_aux op vs (s with clock := c) =
   OPTION_MAP (OPTION_MAP (λ(x,y). (x,y with clock := c))) (do_app_aux op vs s)`,
  srw_tac[][do_app_aux_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[]);

val do_app_change_clock = Q.store_thm("do_app_change_clock",
  `(do_app op args s1 = Rval (res,s2)) ==>
   (do_app op args (s1 with clock := ck) = Rval (res,s2 with clock := ck))`,
  srw_tac[][do_app_def,do_app_aux_with_clock] >>
  Cases_on`do_app_aux op args s1`>>full_simp_tac(srw_ss())[]>>
  reverse(Cases_on`x`)>>full_simp_tac(srw_ss())[]>- (
    every_case_tac >> full_simp_tac(srw_ss())[] ) >>
  Cases_on`do_app op args (bvi_to_bvl s1)` >> full_simp_tac(srw_ss())[] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
  full_simp_tac(srw_ss())[bvi_to_bvl_def] >>
  imp_res_tac bvlPropsTheory.do_app_change_clock >>
  full_simp_tac(srw_ss())[bvlSemTheory.state_component_equality] >>
  full_simp_tac(srw_ss())[bvl_to_bvi_def,bviSemTheory.state_component_equality]);

val do_app_change_clock_err = Q.store_thm("do_app_change_clock_err",
  `bviSem$do_app op vs s = Rerr e ⇒
   do_app op vs (s with clock := c) = Rerr e`,
  srw_tac[][do_app_def,do_app_aux_with_clock] >>
  Cases_on`do_app_aux op vs s`>>full_simp_tac(srw_ss())[]>>
  (reverse(Cases_on`x`)>>full_simp_tac(srw_ss())[]>- (
     every_case_tac >> full_simp_tac(srw_ss())[] )) >>
  Cases_on`do_app op vs (bvi_to_bvl s)` >> full_simp_tac(srw_ss())[] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
  full_simp_tac(srw_ss())[bvi_to_bvl_def] >>
  imp_res_tac bvlPropsTheory.do_app_change_clock >> full_simp_tac(srw_ss())[] >>
  imp_res_tac bvlPropsTheory.do_app_change_clock_err >> full_simp_tac(srw_ss())[]);

val evaluate_add_clock = Q.store_thm ("evaluate_add_clock",
  `!exps env s1 res s2.
    evaluate (exps,env,s1) = (res, s2) ∧
    res ≠ Rerr(Rabort Rtimeout_error)
    ⇒
    !ck. evaluate (exps,env,inc_clock ck s1) = (res, inc_clock ck s2)`,
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def]
  >- (Cases_on `evaluate ([x], env,s)` >> full_simp_tac(srw_ss())[] >>
      Cases_on `q` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
      Cases_on `evaluate (y::xs,env,r)` >> full_simp_tac(srw_ss())[] >>
      Cases_on `q` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[])
  >- (Cases_on `evaluate ([x1],env,s)` >> full_simp_tac(srw_ss())[] >>
      Cases_on `q` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[])
  >- (Cases_on `evaluate (xs,env,s)` >>
      full_simp_tac(srw_ss())[] >>
      Cases_on `q` >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >> full_simp_tac(srw_ss())[])
  >- (Cases_on `evaluate ([x1],env,s)` >> full_simp_tac(srw_ss())[] >>
      Cases_on `q` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[])
  >- (Cases_on `evaluate (xs,env,s)` >> full_simp_tac(srw_ss())[] >>
      Cases_on `q` >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
      srw_tac[][inc_clock_def] >>
      BasicProvers.EVERY_CASE_TAC >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac do_app_const >>
      imp_res_tac do_app_change_clock >>
      imp_res_tac do_app_change_clock_err >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][])
  >- (srw_tac[][] >>
      full_simp_tac(srw_ss())[inc_clock_def, dec_clock_def] >>
      srw_tac[][] >>
      `s.clock + ck - 1 = s.clock - 1 + ck` by (srw_tac [ARITH_ss] [ADD1]) >>
      metis_tac [])
  >- (Cases_on `evaluate (xs,env,s1)` >>
      full_simp_tac(srw_ss())[] >>
      Cases_on `q` >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      BasicProvers.EVERY_CASE_TAC >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      rev_full_simp_tac(srw_ss())[inc_clock_def, dec_clock_def] >>
      fsrw_tac[ARITH_ss][] >>
      `ck + r.clock - (ticks + 1) = r.clock - (ticks + 1) + ck` by srw_tac [ARITH_ss] [ADD1] >>
      full_simp_tac(srw_ss())[] >>
      rpt(first_x_assum(qspec_then`ck`mp_tac))>> srw_tac[][]));

val do_app_aux_io_events_mono = Q.store_thm("do_app_aux_io_events_mono",
  `do_app_aux op vs s = SOME (SOME (x,y)) ⇒
   s.ffi.io_events ≼ y.ffi.io_events ∧
   (IS_SOME s.ffi.final_event ⇒ y.ffi = s.ffi)`,
  srw_tac[][do_app_aux_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]);

val do_app_io_events_mono = Q.store_thm("do_app_io_events_mono",
  `do_app op vs s1 = Rval (x,s2) ⇒
   s1.ffi.io_events ≼ s2.ffi.io_events ∧
   (IS_SOME s1.ffi.final_event ⇒ s2.ffi = s1.ffi)`,
  srw_tac[][do_app_def] >> every_case_tac >> full_simp_tac(srw_ss())[LET_THM] >> srw_tac[][] >> full_simp_tac(srw_ss())[bvl_to_bvi_def] >>
  imp_res_tac bvlPropsTheory.do_app_io_events_mono >> full_simp_tac(srw_ss())[bvi_to_bvl_def] >>
  imp_res_tac do_app_aux_io_events_mono >> full_simp_tac(srw_ss())[]);

val evaluate_io_events_mono = Q.store_thm("evaluate_io_events_mono",
  `!exps env s1 res s2.
    evaluate (exps,env,s1) = (res, s2)
    ⇒
    s1.ffi.io_events ≼ s2.ffi.io_events ∧
    (IS_SOME s1.ffi.final_event ⇒ s2.ffi = s1.ffi)`,
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS,do_app_io_events_mono])

val do_app_inc_clock = Q.prove(
  `do_app op vs (inc_clock x y) =
   map_result (λ(v,s). (v,s with clock := x + y.clock)) I (do_app op vs y)`,
  Cases_on`do_app op vs y` >>
  imp_res_tac do_app_change_clock_err >>
  TRY(Cases_on`a`>>imp_res_tac do_app_change_clock) >>
  full_simp_tac(srw_ss())[inc_clock_def] >> simp[])

val dec_clock_1_inc_clock = Q.prove(
  `x ≠ 0 ⇒ dec_clock 1 (inc_clock x s) = inc_clock (x-1) s`,
  simp[state_component_equality,inc_clock_def,dec_clock_def])

val dec_clock_1_inc_clock2 = Q.prove(
  `s.clock ≠ 0 ⇒ dec_clock 1 (inc_clock x s) = inc_clock x (dec_clock 1 s)`,
  simp[state_component_equality,inc_clock_def,dec_clock_def])

val dec_clock_inc_clock = Q.prove(
  `¬(s.clock < n) ⇒ dec_clock n (inc_clock x s) = inc_clock x (dec_clock n s)`,
  simp[state_component_equality,inc_clock_def,dec_clock_def])

val inc_clock_eq_0 = Q.store_thm("inc_clock_eq_0[simp]",
  `(inc_clock extra s).clock = 0 ⇔ s.clock = 0 ∧ extra = 0`,
  srw_tac[][inc_clock_def])

val evaluate_add_to_clock_io_events_mono = Q.store_thm("evaluate_add_to_clock_io_events_mono",
  `∀exps env s extra.
    (SND(evaluate(exps,env,s))).ffi.io_events ≼
    (SND(evaluate(exps,env,inc_clock extra s))).ffi.io_events ∧
    (IS_SOME((SND(evaluate(exps,env,s))).ffi.final_event) ⇒
     (SND(evaluate(exps,env,inc_clock extra s))).ffi =
     (SND(evaluate(exps,env,s))).ffi)`,
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def] >>
  TRY (
    qcase_tac`Boolv T` >>
    qmatch_assum_rename_tac`IS_SOME _.ffi.final_event` >>
    ntac 4 (BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]) >>
    ntac 2 (TRY (BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[])) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    TRY(qpat_assum`Boolv _ = _`(assume_tac o SYM) >> full_simp_tac(srw_ss())[])) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[dec_clock_1_inc_clock,dec_clock_1_inc_clock2] >>
  imp_res_tac evaluate_add_clock >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_io_events_mono >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  TRY(qpat_assum`Boolv _ = _`(assume_tac o SYM) >> full_simp_tac(srw_ss())[]) >>
  rev_full_simp_tac(srw_ss())[do_app_inc_clock] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  imp_res_tac do_app_io_events_mono >>
  TRY(fsrw_tac[ARITH_ss][] >>NO_TAC) >>
  REV_FULL_SIMP_TAC(srw_ss()++ARITH_ss)[dec_clock_inc_clock,inc_clock_ZERO] >>
  fsrw_tac[ARITH_ss][dec_clock_inc_clock,inc_clock_ZERO] >>
  full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  metis_tac[evaluate_io_events_mono,SND,IS_PREFIX_TRANS,PAIR,
            inc_clock_ffi,dec_clock_ffi]);

val _ = export_theory();
