open preamble bvpTheory bvpSemTheory;
local open bviPropsTheory in end;

val _ = new_theory"bvpProps";

val with_same_locals = store_thm("with_same_locals",
  ``(s with locals := s.locals) = s``,
  fs [state_component_equality]);

val var_corr_def = Define `
  var_corr env corr t <=>
    EVERY2 (\v x. get_var v t = SOME x) corr env`;

val get_vars_thm = store_thm("get_vars_thm",
  ``!vs a t2. var_corr a vs t2 ==> (get_vars vs t2 = SOME a)``,
  Induct \\ Cases_on `a` \\ FULL_SIMP_TAC std_ss [get_vars_def]
  \\ FULL_SIMP_TAC (srw_ss()) [var_corr_def] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []);

val get_vars_append = store_thm("get_vars_append",
  ``∀l1 l2 s. get_vars (l1 ++ l2) s = OPTION_BIND (get_vars l1 s)(λy1. OPTION_BIND (get_vars l2 s)(λy2. SOME(y1 ++ y2)))``,
  Induct >> simp[get_vars_def,OPTION_BIND_SOME,ETA_AX] >> rw[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[]);

val get_vars_reverse = store_thm("get_vars_reverse",
  ``∀ls s ys. get_vars ls s = SOME ys ⇒ get_vars (REVERSE ls) s = SOME (REVERSE ys)``,
  Induct >> simp[get_vars_def] >> rw[get_vars_append] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  rw[get_vars_def]);

val EVERY_get_vars = store_thm("EVERY_get_vars",
  ``!args s1 s2.
      EVERY (\a. lookup a s1 = lookup a s2) args ==>
      (get_vars args s1 = get_vars args s2)``,
  Induct \\ fs [get_vars_def,get_var_def] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []);

val get_vars_IMP_domain = store_thm("get_vars_IMP_domain",
  ``!args x s vs. MEM x args /\ (get_vars args s = SOME vs) ==>
                  x IN domain s``,
  Induct \\ fs [get_vars_def,get_var_def] \\ REPEAT STRIP_TAC
  \\ every_case_tac \\ fs [] \\ SRW_TAC [] []
  \\ fs [domain_lookup]);

val cut_state_opt_with_stack = Q.prove(
  `cut_state_opt x (y with stack := z) = OPTION_MAP (λs. s with stack := z) (cut_state_opt x y)`,
  EVAL_TAC >> every_case_tac >> simp[]);

val consume_space_add_space = store_thm("consume_space_add_space",
  ``consume_space k (add_space t k with locals := env1) =
    SOME (t with <| locals := env1 ; space := 0  |>)``,
  fs [consume_space_def,add_space_def,state_component_equality] \\ DECIDE_TAC);

val consume_space_with_stack = Q.prove(
  `consume_space x (y with stack := z) = OPTION_MAP (λs. s with stack := z) (consume_space x y)`,
  EVAL_TAC >> rw[])

val consume_space_with_locals = Q.prove(
  `consume_space x (y with locals := z) = OPTION_MAP (λs. s with locals := z) (consume_space x y)`,
  EVAL_TAC >> rw[])

val do_app_with_stack = Q.prove(
  `do_app op vs (s with stack := z) = map_result (λ(x,y). (x,y with stack := z)) I (do_app op vs s)`,
  rw[do_app_def,do_space_def,bvi_to_bvp_def,bvp_to_bvi_def] >>
  every_case_tac >> fs[consume_space_with_stack] >> rw[] >> fs[])

val do_app_with_locals = Q.prove(
  `do_app op vs (s with locals := z) = map_result (λ(x,y). (x,y with locals := z)) I (do_app op vs s)`,
  rw[do_app_def,do_space_def,bvi_to_bvp_def,bvp_to_bvi_def] >>
  every_case_tac >> fs[consume_space_with_locals] >> rw[] >> fs[]);

val do_app_err = Q.store_thm("do_app_err",
  `do_app op vs s = Rerr e ⇒ (e = Rabort Rtype_error)`,
  rw[do_app_def] >>
  every_case_tac >> fs[] >> rw[] >>
  imp_res_tac bviPropsTheory.do_app_err >> fs[]);

val do_app_const = Q.store_thm("do_app_const",
  `do_app op vs x = Rval (y,z) ⇒
    z.stack = x.stack ∧ z.handler = x.handler ∧ z.locals = x.locals ∧ z.clock = x.clock`,
  simp[do_app_def,do_space_def] >>
  every_case_tac >> simp[bvi_to_bvp_def] >> strip_tac >>
  rpt var_eq_tac >> simp[] >>
  fs[bviSemTheory.do_app_def] >>
  every_case_tac >> fs[] >> rpt var_eq_tac >>
  fs[bviSemTheory.bvl_to_bvi_def,bvp_to_bvi_def,bviSemTheory.bvi_to_bvl_def] >>
  imp_res_tac bvlSemTheory.do_app_const >> fs[] >>
  imp_res_tac bviPropsTheory.do_app_aux_const >> fs[] >>
  fs[consume_space_def] >> TRY var_eq_tac >> simp[])

val do_app_locals = store_thm("do_app_locals",
  ``(do_app op x s = Rval (q,r)) ==>
    (do_app op x (s with locals := extra) =
       Rval (q,r with locals := extra))``,
  fs [do_app_def,do_space_def,consume_space_def,bvp_to_bvi_def]
  \\ every_case_tac >> fs[] \\ SRW_TAC [] []
  \\ fs [bvi_to_bvp_def,state_component_equality]);

val do_space_alt = store_thm("do_space_alt",
  ``do_space op s =
      if op_space_reset op then SOME (s with space := 0)
      else consume_space (op_space_req op) s``,
  fs [do_space_def] \\ SRW_TAC [] [consume_space_def]
  \\ fs [state_component_equality] \\ fs [] \\ DECIDE_TAC);

val Seq_Skip = store_thm("Seq_Skip",
  ``evaluate (Seq c Skip,s) = evaluate (c,s)``,
  fs [evaluate_def] \\ Cases_on `evaluate (c,s)` \\ fs [LET_DEF] \\ SRW_TAC [] []);

val evaluate_stack_swap = Q.store_thm("evaluate_stack_swap",
  `!c s.
     case evaluate (c,s) of
     | (SOME (Rerr(Rabort Rtype_error)),s1) => T
     | (SOME (Rerr(Rabort a)),s1) => (s1.stack = []) /\
                   (!xs. (LENGTH s.stack = LENGTH xs) ==>
                           evaluate (c,s with stack := xs) =
                             (SOME (Rerr(Rabort a)),s1))
     | (SOME (Rerr (Rraise t)),s1) =>
           (?s2. (jump_exc s = SOME s2) /\ (s2.locals = s1.locals) /\
                 (s2.stack = s1.stack) /\ (s2.handler = s1.handler) /\
                 (!xs s7. (jump_exc (s with stack := xs) = SOME s7) /\
                          (LENGTH s.stack = LENGTH xs) ==>
                          (evaluate (c,s with stack := xs) =
                             (SOME (Rerr (Rraise t)),
                              s1 with <| stack := s7.stack ;
                                         handler := s7.handler ;
                                         locals := s7.locals |>))))
     | (res,s1) => (s1.stack = s.stack) /\ (s1.handler = s.handler) /\
                   (!xs. (LENGTH s.stack = LENGTH xs) ==>
                           evaluate (c,s with stack := xs) =
                             (res, s1 with stack := xs))`,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  THEN1 fs[evaluate_def]
  THEN1 (
    fs[evaluate_def] >> EVAL_TAC >>
    every_case_tac >> fs[] )
  THEN1 (
    fs[evaluate_def] >>
    every_case_tac >>
    fs[set_var_def,cut_state_opt_with_stack,do_app_with_stack] >>
    imp_res_tac do_app_err >> fs[] >> rpt var_eq_tac >>
    fs[cut_state_opt_def,cut_state_def] >> every_case_tac >> fs[] >>
    rpt var_eq_tac >> fs[do_app_with_locals] >>
    TRY(first_assum(split_applied_pair_tac o rhs o concl) >> fs[]) >>
    imp_res_tac do_app_const >> simp[] >>
    EVAL_TAC >> simp[])
  THEN1 (
    fs[evaluate_def] >>
    EVAL_TAC >>
    every_case_tac >> fs[] )
  THEN1 (
    fs[evaluate_def] >>
    EVAL_TAC >>
    every_case_tac >> fs[] )
  THEN1 (
    fs[evaluate_def] >>
    EVAL_TAC >>
    every_case_tac >> fs[] >>
    rpt gen_tac >>
    every_case_tac >> fs[] >>
    rw[] >> simp[])
  THEN1 (
    fs[evaluate_def] >>
    EVAL_TAC >>
    every_case_tac >> fs[] )
  THEN1 (* Seq *)
   (fs [evaluate_def]
    \\ Cases_on `evaluate (c1,s)` \\ fs [LET_DEF]
    \\ Cases_on `evaluate (c2,r)` \\ fs [LET_DEF]
    \\ Cases_on `q = NONE` \\ fs [] \\ Cases_on `q'` \\ fs []
    \\ TRY (Cases_on `x`) \\ TRY (Cases_on`e`) \\ fs [jump_exc_def]
    \\ every_case_tac \\ fs [] \\ SRW_TAC [] [] \\ fs []
    \\ every_case_tac \\ fs []
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
    \\ Q.PAT_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPEC `xs`) \\ fs [])
  THEN1 (* If *)
   (fs [evaluate_def]
    \\ Cases_on `evaluate (c1,s)` \\ fs [LET_DEF]
    \\ Cases_on `evaluate (c2,s)` \\ fs [LET_DEF]
    \\ Cases_on `get_var n s.locals` \\ fs []
    \\ Cases_on `x = Boolv T` \\ fs [get_var_def]
    \\ Cases_on `x = Boolv F` \\ fs [get_var_def])
  THEN1 (* Call *)
   (fs [evaluate_def]
    \\ Cases_on `get_vars args s.locals` \\ fs []
    \\ Cases_on `find_code dest x s.code` \\ fs []
    \\ TRY (fs [call_env_def] \\ NO_TAC)
    \\ Cases_on `x'` \\ fs []
    \\ Cases_on `ret` \\ fs [] THEN1
     (every_case_tac \\ fs []
      \\ fs [call_env_def,dec_clock_def,jump_exc_def]
      \\ every_case_tac \\ fs []
      \\ SRW_TAC [] [] \\ fs []
      \\ Q.PAT_ASSUM `xxx = SOME s7` MP_TAC
      \\ every_case_tac \\ fs []
      \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
      \\ Q.PAT_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPEC `xs`) \\ fs [])
    \\ fs []
    \\ Cases_on `x'` \\ fs []
    \\ Cases_on `cut_env r' s.locals` \\ fs []
    \\ Cases_on `s.clock = 0` \\ fs [] THEN1 (fs [call_env_def])
    \\ Cases_on `evaluate (r,call_env q (push_env x' (IS_SOME handler) (dec_clock s)))` \\ fs []
    \\ Cases_on `q''` \\ fs []
    \\ Cases_on `x''` \\ fs []
    \\ TRY (Cases_on `handler`
       \\ fs [pop_env_def,call_env_def,push_env_def,set_var_def,dec_clock_def]
       \\ REPEAT STRIP_TAC
       \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `Exc x' s.handler::xs`) \\ fs [] \\ NO_TAC)
    \\ reverse(Cases_on`e`)\\fs[] THEN1 (
         Cases_on`a`>>fs[]>>
         rw[]>>
         qpat_abbrev_tac`ss = call_env X Y` >>
         first_x_assum(qspec_then`ss.stack`mp_tac) >>
         (discharge_hyps >- (
            simp[Abbr`ss`] >>
            EVAL_TAC >>
            Cases_on`handler`>>EVAL_TAC >>
            simp[] )) >>
         qpat_abbrev_tac`st:'ffi bvpSem$state = X Y` >>
         `st = ss` by (
           simp[Abbr`ss`,Abbr`st`,bvpSemTheory.state_component_equality] >>
           EVAL_TAC >>
           Cases_on`handler`>>EVAL_TAC >>
           simp[] ) >>
         fs[])
    \\ Cases_on `handler` \\ fs [] THEN1
     (fs [pop_env_def,call_env_def,push_env_def,set_var_def,dec_clock_def]
      \\ fs [jump_exc_def]
      \\ Cases_on `s.handler = LENGTH s.stack` \\ fs [LAST_N_LEMMA]
      \\ `s.handler < LENGTH s.stack` by DECIDE_TAC \\ fs []
      \\ IMP_RES_TAC LAST_N_TL \\ fs []
      \\ Cases_on `LAST_N (s.handler + 1) s.stack` \\ fs []
      \\ Cases_on `h` \\ fs []
      \\ SRW_TAC [] [] \\ fs []
      \\ Q.PAT_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPECL [`Env x'::xs`,
           `s7 with clock := s7.clock - 1`])
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      \\ fs [] \\ REPEAT STRIP_TAC
      \\ IMP_RES_TAC LAST_N_TL \\ fs []
      \\ every_case_tac \\ fs []
      \\ fs [bvpSemTheory.state_component_equality])
    \\ Cases_on `x''` \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate (r,call_env q (push_env x8 T (dec_clock s))) =
          (SOME (Rerr (Rraise b)),s9)`
    \\ Cases_on `evaluate (r''',set_var q'' b s9)` \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate (r''',set_var q'' b s9) = (res,r5)`
    \\ Cases_on `res` \\ fs []
    THEN1 (* NONE *)
     (STRIP_TAC THEN1 (fs [set_var_def,pop_env_def,jump_exc_def,call_env_def,
          push_env_def,LAST_N_LEMMA,dec_clock_def] \\ SRW_TAC [] [] \\ fs []
          \\ every_case_tac \\ fs [] \\ SRW_TAC [] [] \\ fs [])
      \\ STRIP_TAC THEN1 (fs [set_var_def,pop_env_def,jump_exc_def,call_env_def,
          push_env_def,LAST_N_LEMMA,dec_clock_def] \\ SRW_TAC [] [] \\ fs [])
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock (s with stack := xs)))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock (s with stack := xs)))).stack) =
          (call_env q (push_env x8 T (dec_clock (s with stack := xs))))` by ALL_TAC
      THEN1 fs [call_env_def,push_env_def,dec_clock_def]
      \\ fs [] \\ fs [call_env_def,push_env_def,jump_exc_def,
           LAST_N_LEMMA,dec_clock_def,set_var_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_ASSUM `LENGTH s.stack = LENGTH xs` (ASSUME_TAC o GSYM)
      \\ fs [LAST_N_LEMMA] \\ SRW_TAC [] [] \\ fs []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `xs`)
      \\ SRW_TAC [] [] \\ fs [] \\ REV_FULL_SIMP_TAC std_ss []
      \\ POP_ASSUM (fn th => fs [GSYM th])
      \\ REPEAT AP_TERM_TAC \\ fs [bvpSemTheory.state_component_equality])
    \\ Cases_on `x'` \\ fs []
    THEN1 (* SOME Rval *)
     (STRIP_TAC THEN1 (fs [set_var_def,pop_env_def,jump_exc_def,call_env_def,
          push_env_def,LAST_N_LEMMA,dec_clock_def] \\ SRW_TAC [] [] \\ fs []
          \\ every_case_tac \\ fs [] \\ SRW_TAC [] [] \\ fs [])
      \\ STRIP_TAC THEN1 (fs [set_var_def,pop_env_def,jump_exc_def,call_env_def,
          push_env_def,LAST_N_LEMMA,dec_clock_def] \\ SRW_TAC [] [] \\ fs [])
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock (s with stack := xs)))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock (s with stack := xs)))).stack) =
          (call_env q (push_env x8 T (dec_clock (s with stack := xs))))` by ALL_TAC
      THEN1 fs [call_env_def,push_env_def,dec_clock_def]
      \\ fs [] \\ fs [call_env_def,push_env_def,jump_exc_def,
           LAST_N_LEMMA,dec_clock_def,set_var_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_ASSUM `LENGTH s.stack = LENGTH xs` (ASSUME_TAC o GSYM)
      \\ fs [LAST_N_LEMMA] \\ SRW_TAC [] [] \\ fs []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `xs`)
      \\ SRW_TAC [] [] \\ fs [] \\ REV_FULL_SIMP_TAC std_ss []
      \\ POP_ASSUM (fn th => fs [GSYM th])
      \\ REPEAT AP_TERM_TAC \\ fs [bvpSemTheory.state_component_equality])
    \\ Cases_on`e` \\ fs[]
    THEN1 (* Rraise *)
     (FIRST_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock s))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock s))).stack) =
          (call_env q (push_env x8 T (dec_clock s)))` by ALL_TAC
      THEN1 fs [call_env_def,push_env_def,dec_clock_def]
      \\ POP_ASSUM (fn th => SIMP_TAC std_ss [th])
      \\ SIMP_TAC std_ss [Once dec_clock_def]
      \\ SIMP_TAC std_ss [Once push_env_def]
      \\ SIMP_TAC std_ss [Once call_env_def]
      \\ SIMP_TAC std_ss [Once jump_exc_def]
      \\ SIMP_TAC (srw_ss()) [LAST_N_LEMMA] \\ REPEAT STRIP_TAC
      \\ fs [bvpSemTheory.state_component_equality]
      \\ Q.PAT_ASSUM `jump_exc (set_var q'' b s9) = SOME s2'` MP_TAC
      \\ SIMP_TAC std_ss [Once set_var_def]
      \\ SIMP_TAC (srw_ss()) [Once jump_exc_def]
      \\ Cases_on `LAST_N (s9.handler + 1) s9.stack` \\ fs []
      \\ Cases_on `h` \\ fs [] \\ SIMP_TAC std_ss [Once EQ_SYM_EQ]
      \\ REPEAT STRIP_TAC \\ fs [] \\ POP_ASSUM (K ALL_TAC)
      \\ SIMP_TAC std_ss [Once jump_exc_def] \\ fs []
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock (s with stack := xs)))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock (s with stack := xs)))).stack) =
          (call_env q (push_env x8 T (dec_clock (s with stack := xs))))` by ALL_TAC
      THEN1 fs [call_env_def,push_env_def,dec_clock_def]
      \\ fs [] \\ fs [call_env_def,push_env_def,jump_exc_def,
           LAST_N_LEMMA,dec_clock_def,set_var_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_ASSUM `LENGTH s.stack = LENGTH xs` (ASSUME_TAC o GSYM)
      \\ fs [LAST_N_LEMMA] \\ SRW_TAC [] [] \\ fs []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `xs`)
      \\ SRW_TAC [] [] \\ fs [] \\ REV_FULL_SIMP_TAC std_ss []
      \\ Cases_on `LAST_N (s9.handler + 1) xs` \\ fs []
      \\ Cases_on `h` \\ fs []
      \\ `s9 with <|locals := insert q'' b s9.locals; stack := xs;
             handler := s9.handler|> =
          s9 with <|locals := insert q'' b s9.locals; stack := xs|>` by ALL_TAC
      THEN1 (fs [bvpSemTheory.state_component_equality]) \\ fs []
      \\ fs [bvpSemTheory.state_component_equality])
    \\ Cases_on`a` \\ fs[]
    THEN (* Rtimeout_error *)
     (REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock (s with stack := xs)))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock (s with stack := xs)))).stack) =
          (call_env q (push_env x8 T (dec_clock (s with stack := xs))))` by ALL_TAC
      THEN1 fs [call_env_def,push_env_def,dec_clock_def]
      \\ fs [] \\ fs [call_env_def,push_env_def,jump_exc_def,
           LAST_N_LEMMA,dec_clock_def,set_var_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_ASSUM `LENGTH s.stack = LENGTH xs` (ASSUME_TAC o GSYM)
      \\ fs [LAST_N_LEMMA] \\ SRW_TAC [] [] \\ fs []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `xs`)
      \\ SRW_TAC [] [] \\ fs [] \\ REV_FULL_SIMP_TAC std_ss []
      \\ POP_ASSUM (fn th => fs [GSYM th])
      \\ REPEAT AP_TERM_TAC \\ fs [bvpSemTheory.state_component_equality])))

val evaluate_stack = store_thm("evaluate_stack",
  ``!c s.
      case evaluate (c,s) of
      | (SOME (Rerr(Rabort Rtype_error)),s1) => T
      | (SOME (Rerr(Rabort _)),s1) => (s1.stack = [])
      | (SOME (Rerr _),s1) =>
            (?s2. (jump_exc s = SOME s2) /\ (s2.locals = s1.locals) /\
                  (s2.stack = s1.stack) /\ (s2.handler = s1.handler))
      | (_,s1) => (s1.stack = s.stack) /\ (s1.handler = s.handler)``,
  REPEAT STRIP_TAC \\ ASSUME_TAC (SPEC_ALL evaluate_stack_swap)
  \\ every_case_tac \\ fs []);

val evaluate_NONE_jump_exc = store_thm("evaluate_NONE_jump_exc",
  ``(evaluate (c,s) = (NONE,u1)) /\ (jump_exc u1 = SOME x) ==>
    (jump_exc s = SOME (s with <| stack := x.stack ;
                                  handler := x.handler ;
                                  locals := x.locals |>))``,
  REPEAT STRIP_TAC \\ MP_TAC (Q.SPECL [`c`,`s`] evaluate_stack) \\ fs []
  \\ fs [jump_exc_def] \\ REPEAT STRIP_TAC \\ fs []
  \\ every_case_tac >> fs[]
  \\ SRW_TAC [] []);

val evaluate_NONE_jump_exc_ALT = store_thm("evaluate_NONE_jump_exc_ALT",
  ``(evaluate (c,s) = (NONE,u1)) /\ (jump_exc s = SOME x) ==>
    (jump_exc u1 = SOME (u1 with <| stack := x.stack ;
                                  handler := x.handler ;
                                  locals := x.locals |>))``,
  REPEAT STRIP_TAC \\ MP_TAC (Q.SPECL [`c`,`s`] evaluate_stack) \\ fs []
  \\ fs [jump_exc_def] \\ REPEAT STRIP_TAC \\ fs []
  \\ every_case_tac >> fs[]
  \\ SRW_TAC [] []);

val evaluate_locals_LN_lemma = prove(
  ``!c s.
      FST (evaluate (c,s)) <> NONE /\
      FST (evaluate (c,s)) <> SOME (Rerr(Rabort Rtype_error)) ==>
      ((SND (evaluate (c,s))).locals = LN) \/
      ?t. FST (evaluate (c,s)) = SOME (Rerr(Rraise t))``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ fs [evaluate_def]
  \\ every_case_tac \\ fs [call_env_def,fromList_def]
  \\ imp_res_tac do_app_err >> fs[] >> rfs[]
  \\ SRW_TAC [] [] \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs []
  \\ Cases_on`a`>>fs[]);

val evaluate_locals_LN = store_thm("evaluate_locals_LN",
  ``!c s res t.
      (evaluate (c,s) = (res,t)) /\ res <> NONE /\ res <> SOME (Rerr(Rabort Rtype_error)) ==>
      (t.locals = LN) \/ ?t. res = SOME (Rerr(Rraise t))``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL evaluate_locals_LN_lemma) \\ fs []);

val locals_ok_def = Define `
  locals_ok l1 l2 =
    !v x. (sptree$lookup v l1 = SOME x) ==> (sptree$lookup v l2 = SOME x)`;

val locals_ok_IMP = store_thm("locals_ok_IMP",
  ``locals_ok l1 l2 ==> domain l1 SUBSET domain l2``,
  fs [locals_ok_def,SUBSET_DEF,domain_lookup] \\ METIS_TAC []);

val locals_ok_refl = store_thm("locals_ok_refl",
  ``!l. locals_ok l l``,
  fs [locals_ok_def]);

val locals_ok_cut_env = store_thm("locals_ok_cut_env",
  ``locals_ok l1 l2 /\
    (cut_env names l1 = SOME x) ==>
    (cut_env names l2 = SOME x)``,
  fs [cut_env_def] \\ SRW_TAC [] []
  THEN1 (IMP_RES_TAC locals_ok_IMP \\ IMP_RES_TAC SUBSET_TRANS)
  \\ fs [lookup_inter_alt] \\ SRW_TAC [] []
  \\ fs [locals_ok_def,domain_lookup,SUBSET_DEF,PULL_EXISTS]
  \\ fs [oneTheory.one] \\ RES_TAC \\ RES_TAC \\ fs []);

val locals_ok_get_var = store_thm("locals_ok_get_var",
  ``locals_ok s l /\
    (get_var x s = SOME w) ==>
    (get_var x l = SOME w)``,
  fs [locals_ok_def,get_var_def]);

val locals_ok_get_vars = store_thm("locals_ok_get_vars",
  ``!x w.
      locals_ok s l /\
      (get_vars x s = SOME w) ==>
      (get_vars x l = SOME w)``,
  Induct \\ fs [get_vars_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `get_var h s` \\ fs []
  \\ Cases_on `get_vars x s` \\ fs []
  \\ IMP_RES_TAC locals_ok_get_var \\ fs []);

val bvp_to_bvi_ignore = Q.store_thm("bvp_to_bvi_ignore",
  `(bvp_to_bvi (s with space := t) = bvp_to_bvi s) ∧
   (bvp_to_bvi (s with locals := l) = bvp_to_bvi s) ∧
   (bvp_to_bvi (s with <| locals := l; space := t |>) = bvp_to_bvi s)`,
  EVAL_TAC);

val bvi_to_bvp_space_locals = Q.store_thm("bvi_to_bvp_space_locals",
  `((bvi_to_bvp s t with locals := x) = bvi_to_bvp s (t with locals := x)) /\
   ((bvi_to_bvp s t).locals = t.locals) /\
   ((bvi_to_bvp s t with space := y) = bvi_to_bvp s (t with space := y)) /\
   ((bvi_to_bvp s t).space = t.space)`,
  EVAL_TAC);

val evaluate_locals = store_thm("evaluate_locals",
  ``!c s res s2 vars l.
      res <> SOME (Rerr(Rabort Rtype_error)) /\ (evaluate (c,s) = (res,s2)) /\
      locals_ok s.locals l ==>
      ?w. (evaluate (c, s with locals := l) =
             (res,if res = NONE then s2 with locals := w
                                else s2)) /\
          locals_ok s2.locals w``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ fs [evaluate_def]
  THEN1 (* Skip *) (METIS_TAC [])
  THEN1 (* Move *)
   (Cases_on `get_var src s.locals` \\ fs [] \\ SRW_TAC [] []
    \\ IMP_RES_TAC locals_ok_get_var \\ fs []
    \\ fs [get_var_def,lookup_union,set_var_def,locals_ok_def]
    \\ Q.EXISTS_TAC `insert dest x l` \\ fs [lookup_insert]
    \\ METIS_TAC [])
  THEN1 (* Assign *)
   (Cases_on `names_opt` \\ fs []
    \\ Cases_on `op_space_reset op` \\ fs [cut_state_opt_def] THEN1
     (Cases_on `get_vars args s.locals` \\ fs [cut_state_opt_def]
      \\ IMP_RES_TAC locals_ok_get_vars \\ fs []
      \\ reverse(Cases_on `do_app op x s`) \\ fs [] >- (
           imp_res_tac do_app_err >> fs[] >>
           Cases_on`a`>>fs[] >> rw[] >>
           fs[do_app_def,do_space_def,bvp_to_bvi_ignore,
              bvi_to_bvp_space_locals,
              bvp_spaceTheory.op_space_req_def,
              bvi_to_bvpTheory.op_space_reset_def] >>
           BasicProvers.CASE_TAC >> fs[])
      \\ Cases_on `a` \\ fs [] \\ SRW_TAC [] []
      \\ IMP_RES_TAC do_app_locals \\ fs [set_var_def]
      \\ Q.EXISTS_TAC `insert dest q l`
      \\ fs [set_var_def,locals_ok_def,lookup_insert]
      \\ METIS_TAC [do_app_const])
    \\ fs [cut_state_def]
    \\ Cases_on `cut_env x s.locals` \\ fs []
    \\ IMP_RES_TAC locals_ok_cut_env \\ fs []
    \\ Q.EXISTS_TAC `s2.locals` \\ fs [locals_ok_def]
    \\ SRW_TAC [] [state_component_equality])
  THEN1 (* Tick *)
   (Cases_on `s.clock = 0` \\ fs [] \\ SRW_TAC [] []
    \\ fs [locals_ok_def,call_env_def,EVAL ``fromList []``,lookup_def,
           dec_clock_def] \\ METIS_TAC [])
  THEN1 (* MakeSpace *)
   (Cases_on `cut_env names s.locals` \\ fs []
    \\ IMP_RES_TAC locals_ok_cut_env
    \\ fs [LET_DEF,add_space_def,state_component_equality,locals_ok_def])
  THEN1 (* Raise *)
   (Cases_on `get_var n s.locals` \\ fs [] \\ SRW_TAC [] []
    \\ `jump_exc (s with locals := l) = jump_exc s` by
         fs [jump_exc_def] \\ Cases_on `jump_exc s` \\ fs []
    \\ `get_var n l = SOME x` by
         fs [locals_ok_def,get_var_def] \\ fs []
    \\ srw_tac [] [] \\ Q.EXISTS_TAC `s2.locals`
    \\ fs [locals_ok_def])
  THEN1 (* Return *)
   (Cases_on `get_var n s.locals` \\ fs [] \\ SRW_TAC [] []
    \\ `get_var n l = SOME x` by
         fs [locals_ok_def,get_var_def] \\ fs []
    \\ srw_tac [] [call_env_def]
    \\ simp[locals_ok_def,lookup_fromList])
  THEN1 (* Seq *)
   (Cases_on `evaluate (c1,s)` \\ fs [LET_DEF]
    \\ Cases_on `q = SOME (Rerr(Rabort Rtype_error))` \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `q` \\ fs [] \\ SRW_TAC [] [] \\ METIS_TAC [])
  THEN1 (* If *)
   (Cases_on `get_var n s.locals` \\ fs []
    \\ IMP_RES_TAC locals_ok_get_var \\ fs []
    \\ Cases_on `x = Boolv T` \\ fs []
    \\ Cases_on `x = Boolv F` \\ fs [])
  THEN1 (* Call *)
   (Cases_on `get_vars args s.locals` \\ fs []
    \\ IMP_RES_TAC locals_ok_get_vars \\ fs []
    \\ Cases_on `find_code dest x s.code` \\ fs []
    \\ Cases_on `x'` \\ fs []
    \\ Cases_on `ret` \\ fs [] THEN1
     (Cases_on `handler` \\ fs []
      \\ Cases_on `s.clock = 0` \\ fs [] \\ SRW_TAC [] []
      \\ `call_env q (dec_clock (s with locals := l)) =
          call_env q (dec_clock s)` by
         fs [state_component_equality,dec_clock_def,call_env_def] \\ fs []
      \\ fs [call_env_def,locals_ok_def,lookup_def,fromList_def]
      \\ Q.EXISTS_TAC `s2.locals` \\ fs [locals_ok_refl]
      \\ SRW_TAC [] [state_component_equality])
    \\ Cases_on `x'` \\ fs []
    \\ Cases_on `cut_env r' s.locals` \\ fs []
    \\ IMP_RES_TAC locals_ok_cut_env \\ fs []
    \\ `call_env q (push_env x' (IS_SOME handler)
          (dec_clock (s with locals := l))) =
        call_env q (push_env x' (IS_SOME handler)
          (dec_clock s))` by ALL_TAC THEN1
     (Cases_on `handler`
      \\ fs [state_component_equality,dec_clock_def,call_env_def,push_env_def])
    \\ Cases_on `s.clock = 0` \\ fs [] \\ SRW_TAC [] []
    \\ fs [call_env_def,locals_ok_def,lookup_def,fromList_def]
    \\ fs [] \\ METIS_TAC [locals_ok_refl,with_same_locals]));

val funpow_dec_clock_clock = Q.store_thm ("funpow_dec_clock_clock",
  `!n s. FUNPOW dec_clock n s = (s with clock := s.clock - n)`,
  Induct_on `n` >>
  rw [FUNPOW, state_component_equality, dec_clock_def, ADD1] >>
  decide_tac);

val evaluate_mk_ticks = Q.store_thm ("evaluate_mk_ticks",
  `!p s n.
    evaluate (mk_ticks n p, s)
    =
    if s.clock < n then
      (SOME (Rerr(Rabort Rtimeout_error)), s with <| clock := 0; locals := fromList []; stack := [] |>)
    else
      evaluate (p, FUNPOW dec_clock n s)`,
  Induct_on `n` >>
  rw [evaluate_def, mk_ticks_def, FUNPOW] >>
  fs [mk_ticks_def, evaluate_def] >>
  rw [funpow_dec_clock_clock, dec_clock_def] >>
  simp [call_env_def] >>
  `s.clock - n = 0` by decide_tac >>
  `s.clock - (n+1) = 0` by decide_tac >>
  rw [] >>
  fs [ADD1, LESS_OR_EQ] >>
  full_simp_tac (srw_ss()++ARITH_ss) []);

val FUNPOW_dec_clock_code = store_thm("FUNPOW_dec_clock_code[simp]",
  ``((FUNPOW dec_clock n t).code = t.code) /\
    ((FUNPOW dec_clock n t).stack = t.stack) /\
    ((FUNPOW dec_clock n t).handler = t.handler) /\
    ((FUNPOW dec_clock n t).refs = t.refs) /\
    ((FUNPOW dec_clock n t).ffi = t.ffi) /\
    ((FUNPOW dec_clock n t).global = t.global) /\
    ((FUNPOW dec_clock n t).locals = t.locals) /\
    ((FUNPOW dec_clock n t).clock = t.clock - n)``,
  Induct_on `n` \\ fs [FUNPOW_SUC,dec_clock_def] \\ DECIDE_TAC);

val jump_exc_NONE = store_thm("jump_exc_NONE",
  ``(jump_exc (t with locals := x) = NONE <=> jump_exc t = NONE) /\
    (jump_exc (t with clock := c) = NONE <=> jump_exc t = NONE)``,
  FULL_SIMP_TAC (srw_ss()) [jump_exc_def] \\ REPEAT STRIP_TAC
  \\ every_case_tac \\ FULL_SIMP_TAC std_ss []);

val jump_exc_IMP = store_thm("jump_exc_IMP",
  ``(jump_exc s = SOME t) ==>
    s.handler < LENGTH s.stack /\
    ?n e xs. (LAST_N (s.handler + 1) s.stack = Exc e n::xs) /\
             (t = s with <|handler := n; locals := e; stack := xs|>)``,
  SIMP_TAC std_ss [jump_exc_def]
  \\ Cases_on `LAST_N (s.handler + 1) s.stack` \\ fs []
  \\ Cases_on `h` \\ fs []);

val do_app_Rerr = store_thm("do_app_Rerr",
  ``bvpSem$do_app op x' s1 = Rerr e ==> e = Rabort Rtype_error``,
  fs [bvpSemTheory.do_app_def,bviSemTheory.do_app_def] \\ every_case_tac \\ rw []
  \\ fs [bvlSemTheory.do_app_def] \\ every_case_tac \\ rw []
  \\ fs [LET_DEF]);

val do_app_change_clock = Q.store_thm("do_app_change_clock",
  `(do_app op args s1 = Rval (res,s2)) ==>
   (do_app op args (s1 with clock := ck) = Rval (res,s2 with clock := ck))`,
  rw[do_app_def,do_space_def] >>
  every_case_tac >> fs[] >> rw[] >>
  imp_res_tac bviPropsTheory.do_app_change_clock >>
  fs[bvp_to_bvi_def,bvi_to_bvp_def,state_component_equality] >>
  rpt var_eq_tac >> simp[] >>
  fs[consume_space_def] >>
  rpt var_eq_tac >> fs[] >>
  rpt var_eq_tac >> fs[] );

val cut_state_eq_some = Q.store_thm("cut_state_eq_some",
  `cut_state names s = SOME y ⇔ ∃z. cut_env names s.locals = SOME z ∧ y = s with locals := z`,
  rw[cut_state_def] >> every_case_tac >> fs[EQ_IMP_THM]);

val cut_state_eq_none = Q.store_thm("cut_state_eq_none",
  `cut_state names s = NONE ⇔ cut_env names s.locals = NONE`,
  rw[cut_state_def] >> every_case_tac >> fs[EQ_IMP_THM]);

val evaluate_add_clock = Q.store_thm ("evaluate_add_clock",
  `!exps s1 res s2.
    evaluate (exps,s1) = (res, s2) ∧
    (∀a. res ≠ SOME(Rerr(Rabort a)))
    ⇒
    !ck. evaluate (exps,s1 with clock := s1.clock + ck) = (res, s2 with clock := s2.clock + ck)`,
  recInduct evaluate_ind >> rw [evaluate_def]
  >- (
    every_case_tac >> fs[get_var_def,set_var_def] >> rw[] >> fs[] )
  >- (
    every_case_tac >> fs[] >> rw[] >>
    fs[cut_state_opt_def,cut_state_eq_some,cut_state_eq_none] >>
    every_case_tac >> fs[cut_state_eq_some,cut_state_eq_none] >>
    rw[] >> fs[set_var_def] >> rw[] >>
    imp_res_tac do_app_change_clock >> fs[] >>
    rpt var_eq_tac >> fs[] >>
    rpt var_eq_tac >> fs[state_component_equality] >>
    imp_res_tac do_app_const >> fs[] >>
    imp_res_tac do_app_Rerr >> fs[] )
  >- ( EVAL_TAC >> simp[state_component_equality] )
  >- ( every_case_tac >> fs[] >> rw[] >> EVAL_TAC )
  >- (
    every_case_tac >> fs[] >> rw[] >> fs[jump_exc_NONE] >>
    imp_res_tac jump_exc_IMP >> fs[] )
  >- (
    every_case_tac >> fs[] >> rw[call_env_def] )
  >- (
    fs[LET_THM] >>
    split_pair_tac >> fs[] >>
    every_case_tac >> fs[] >> rw[] >>
    rfs[] >> rw[] )
  >- ( every_case_tac >> fs[] >> rw[] )
  >- (
    every_case_tac >> fs[] >> rw[] >> rfs[] >>
    fsrw_tac[ARITH_ss][call_env_def,dec_clock_def,push_env_def,pop_env_def,set_var_def] >>
    first_x_assum(qspec_then`ck`mp_tac) >> simp[] >>
    every_case_tac >> fs[] >> rw[] >> rfs[] >> fs[] >>
    spose_not_then strip_assume_tac >> fs[]))

val _ = export_theory();
