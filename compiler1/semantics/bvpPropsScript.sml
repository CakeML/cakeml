open preamble bvpSemTheory;

val _ = new_theory"bvpProps";

(* TODO: move *)
val map_error_result_I = Q.store_thm("map_error_result_I[simp]",
  `map_error_result I e = e`,
  Cases_on`e`>>simp[])

val map_result_Rval = Q.store_thm("map_result_Rval[simp]",
  `map_result f1 f2 e = Rval x ⇔ ∃y. e = Rval y ∧ x = f1 y`,
  Cases_on`e`>>simp[EQ_IMP_THM])
(* -- *)

val get_vars_with_stack = prove(
  ``!args s. (s.locals = t.locals) ==>
             (get_vars args s = get_vars args t)``,
  Induct \\ fs [get_vars_def,get_var_def])

val get_vars_with_stack_rwt = prove(
  ``(get_vars args (s with stack := xs) = get_vars args s) /\
    (get_vars args (s with <| locals := l ; stack := xs |>) =
     get_vars args (s with <| locals := l |>))``,
  REPEAT STRIP_TAC
  \\ MATCH_MP_TAC get_vars_with_stack \\ fs [])

val cut_state_opt_with_stack = Q.prove(
  `cut_state_opt x (y with stack := z) = OPTION_MAP (λs. s with stack := z) (cut_state_opt x y)`,
  EVAL_TAC >> every_case_tac >> simp[])

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
  every_case_tac >> fs[consume_space_with_locals] >> rw[] >> fs[])

val do_app_err = Q.store_thm("do_app_err",
  `do_app op vs s = Rerr e ⇒
   ∃a. e = Rabort a ∧ a ≠ Rtimeout_error`,
  rw[do_app_def] >>
  every_case_tac >> fs[] >> rw[] >>
  fs[bviSemTheory.do_app_def] >>
  every_case_tac >> fs[] >> rw[] >>
  imp_res_tac bvlPropsTheory.do_app_err >> rw[])

val do_app_const = Q.store_thm("do_app_const",
  `do_app op vs x = Rval (y,z) ⇒
    z.stack = x.stack ∧ z.handler = x.handler`,
  simp[do_app_def,do_space_def] >>
  every_case_tac >> simp[bvi_to_bvp_def] >> strip_tac >>
  rpt var_eq_tac >> simp[] >>
  fs[bviSemTheory.do_app_def] >>
  every_case_tac >> fs[] >> rpt var_eq_tac >>
  fs[consume_space_def] >> var_eq_tac >> simp[])

(*
val tac =
  fs [evaluate_def]
  \\ ntac 4 (
    BasicProvers.FULL_CASE_TAC
    \\ fs [call_env_def,fromList_def,set_var_def,cut_state_opt_def,
           do_app_def,do_space_def,consume_space_def,add_space_def,
           bvi_to_bvp_def,cut_state_def,cut_env_def,dec_clock_def,
           get_var_def,push_env_def,set_var_def,jump_exc_def,
           get_vars_with_stack_rwt,
           bvi_to_bvpTheory.op_space_reset_def,
           bvp_to_bvi_def,bviSemTheory.do_app_def]
    \\ imp_res_tac bvlPropsTheory.do_app_err
    \\ rw[] \\ fs[])
*)

val evaluate_stack_swap = store_thm("evaluate_stack_swap",
  ``!c s.
      case evaluate (c,s) of
      | (SOME (Rerr(Rabort Rtype_error)),s1) => T
      | (SOME (Rerr(Rabort Rtimeout_error)),s1) => (s1.stack = []) /\
                    (!xs. (LENGTH s.stack = LENGTH xs) ==>
                            evaluate (c,s with stack := xs) =
                              (SOME (Rerr(Rabort Rtimeout_error)),s1))
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
                              (res, s1 with stack := xs))``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  THEN1 fs[evaluate_def]
  THEN1 (
    fs[evaluate_def] >> EVAL_TAC >>
    every_case_tac >> fs[] )
  THEN1 (
    fs[evaluate_def] >>
    every_case_tac >>
    fs[set_var_def,cut_state_opt_with_stack,get_vars_with_stack_rwt,do_app_with_stack] >>
    imp_res_tac do_app_err >> fs[] >> rpt var_eq_tac >>
    fs[cut_state_opt_def,cut_state_def] >> every_case_tac >> fs[] >>
    rpt var_eq_tac >> fs[do_app_with_locals] >>
    TRY(first_assum(split_applied_pair_tac o rhs o concl) >> fs[]) >>
    imp_res_tac do_app_const >> simp[] )
  THEN1 tac THEN1 tac THEN1 (tac \\ tac) THEN1 tac
  THEN1 (* Seq *)
   (fs [evaluate_def]
    \\ Cases_on `evaluate (c1,s)` \\ fs [LET_DEF]
    \\ Cases_on `evaluate (c2,r)` \\ fs [LET_DEF]
    \\ Cases_on `q = NONE` \\ fs [] \\ Cases_on `q'` \\ fs []
    \\ TRY (Cases_on `x`) \\ fs [jump_exc_def]
    \\ REPEAT BasicProvers.CASE_TAC \\ fs [] \\ SRW_TAC [] [] \\ fs []
    \\ POP_ASSUM MP_TAC
    \\ REPEAT BasicProvers.CASE_TAC \\ fs []
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
    \\ Q.PAT_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPEC `xs`) \\ fs []
    \\ REPEAT BasicProvers.CASE_TAC \\ fs [] \\ SRW_TAC [] [])
  THEN1 (* If *)
   (fs [evaluate_def]
    \\ Cases_on `evaluate (g,s)` \\ fs [LET_DEF]
    \\ Cases_on `evaluate (c1,r)` \\ fs [LET_DEF]
    \\ Cases_on `evaluate (c2,r)` \\ fs [LET_DEF]
    \\ REVERSE (Cases_on `q`) \\ fs []
    THEN1 (Cases_on `x` \\ fs [] \\ REPEAT STRIP_TAC
           \\ RES_TAC \\ fs [])
    \\ Cases_on `get_var n r` \\ fs []
    \\ Cases_on `x = bool_to_val T` \\ fs [get_var_def] THEN1
     (Cases_on `q'` \\ fs []
      \\ Cases_on `x'` \\ fs [jump_exc_def]
      \\ REPEAT BasicProvers.CASE_TAC \\ fs [jump_exc_def]
      \\ SRW_TAC [] [bvp_state_explode] \\ fs [set_var_def]
      \\ POP_ASSUM MP_TAC
      \\ REPEAT BasicProvers.CASE_TAC \\ fs []
      \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
      \\ Q.PAT_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPEC `xs`) \\ fs []
      \\ REPEAT BasicProvers.CASE_TAC \\ fs [] \\ SRW_TAC [] [])
    \\ Cases_on `x = bool_to_val F` \\ fs [get_var_def] THEN1
     (Cases_on `q''` \\ fs []
      \\ Cases_on `x'` \\ fs [jump_exc_def]
      \\ REPEAT BasicProvers.CASE_TAC \\ fs [jump_exc_def]
      \\ SRW_TAC [] [bvp_state_explode] \\ fs [set_var_def]
      \\ POP_ASSUM MP_TAC
      \\ REPEAT BasicProvers.CASE_TAC \\ fs []
      \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
      \\ Q.PAT_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPEC `xs`) \\ fs []
      \\ REPEAT BasicProvers.CASE_TAC \\ fs [] \\ SRW_TAC [] []))
  THEN1 (* Call *)
   (fs [evaluate_def]
    \\ Cases_on `s.clock = 0` \\ fs []
    \\ Cases_on `get_vars args s` \\ fs []
    \\ Cases_on `find_code dest x s.code` \\ fs []
    \\ TRY (fs [call_env_def] \\ NO_TAC)
    \\ Cases_on `x'` \\ fs []
    \\ Cases_on `ret` \\ fs [get_vars_with_stack_rwt] THEN1
     (REPEAT BasicProvers.CASE_TAC \\ fs []
      \\ fs [call_env_def,dec_clock_def,jump_exc_def]
      \\ REPEAT BasicProvers.CASE_TAC \\ fs []
      \\ SRW_TAC [] [] \\ fs []
      \\ Q.PAT_ASSUM `xxx = SOME s7` MP_TAC
      \\ REPEAT BasicProvers.CASE_TAC \\ fs []
      \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
      \\ Q.PAT_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPEC `xs`) \\ fs [])
    \\ fs [get_vars_with_stack_rwt]
    \\ Cases_on `x'` \\ fs []
    \\ Cases_on `cut_env r' s.locals` \\ fs []
    \\ Cases_on `evaluate (r,call_env q (push_env x' (IS_SOME handler) (dec_clock s)))` \\ fs []
    \\ Cases_on `q''` \\ fs []
    \\ Cases_on `x''` \\ fs []
    \\ TRY (Cases_on `handler`
       \\ fs [pop_env_def,call_env_def,push_env_def,set_var_def,dec_clock_def]
       \\ REPEAT STRIP_TAC
       \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `Exc x' s.handler::xs`) \\ fs [] \\ NO_TAC)
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
      \\ REPEAT BasicProvers.CASE_TAC \\ fs []
      \\ fs [bvp_state_explode])
    \\ Cases_on `x''` \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate (r,call_env q (push_env x8 T (dec_clock s))) =
          (SOME (Exception b),s9)`
    \\ Cases_on `evaluate (r''',set_var q'' b s9)` \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate (r''',set_var q'' b s9) = (res,r5)`
    \\ Cases_on `res` \\ fs []
    THEN1 (* NONE *)
     (STRIP_TAC THEN1 (fs [set_var_def,pop_env_def,jump_exc_def,call_env_def,
          push_env_def,LAST_N_LEMMA,dec_clock_def] \\ SRW_TAC [] [] \\ fs []
        \\ REPEAT BasicProvers.FULL_CASE_TAC \\ fs [] \\ SRW_TAC [] [] \\ fs [])
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
      \\ REPEAT AP_TERM_TAC \\ fs [bvp_state_explode])
    \\ Cases_on `x'` \\ fs []
    THEN1 (* SOME Result *)
     (STRIP_TAC THEN1 (fs [set_var_def,pop_env_def,jump_exc_def,call_env_def,
          push_env_def,LAST_N_LEMMA,dec_clock_def] \\ SRW_TAC [] [] \\ fs []
        \\ REPEAT BasicProvers.FULL_CASE_TAC \\ fs [] \\ SRW_TAC [] [] \\ fs [])
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
      \\ REPEAT AP_TERM_TAC \\ fs [bvp_state_explode])
    THEN1 (* SOME Exception *)
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
      \\ fs [bvp_state_explode]
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
      THEN1 (fs [bvp_state_explode]) \\ fs []
      \\ fs [bvp_state_explode])
    THEN1 (* SOME TimeOut *)
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
      \\ REPEAT AP_TERM_TAC \\ fs [bvp_state_explode])))

val evaluate_stack = store_thm("evaluate_stack",
  ``!c s.
      case evaluate (c,s) of
      | (SOME (Rerr(Rabort Rtimeout_error)),s1) => (s1.stack = [])
      | (SOME (Rerr(Rabort _)),s1) => T
      | (SOME (Rerr _),s1) =>
            (?s2. (jump_exc s = SOME s2) /\ (s2.locals = s1.locals) /\
                  (s2.stack = s1.stack) /\ (s2.handler = s1.handler))
      | (_,s1) => (s1.stack = s.stack) /\ (s1.handler = s.handler)``,
  REPEAT STRIP_TAC \\ ASSUME_TAC (SPEC_ALL evaluate_stack_swap)
  \\ every_case_tac \\ fs []);

val _ = export_theory();
