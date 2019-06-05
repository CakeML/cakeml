(*
  Properties about dataLang and its semantics
*)
open preamble dataLangTheory dataSemTheory semanticsPropsTheory;

val _ = new_theory"dataProps";

val s = ``s:('c,'ffi) dataSem$state``

Theorem initial_state_simp[simp]:
   (initial_state f c co cc k).clock = k ∧
   (initial_state f c co cc k).locals = LN ∧
   (initial_state f c co cc k).code = c ∧
   (initial_state f c co cc k).ffi = f ∧
   (initial_state f c co cc k).compile_oracle = co ∧
   (initial_state f c co cc k).compile = cc ∧
   (initial_state f c co cc k).stack = []
Proof
  srw_tac[][initial_state_def]
QED

Theorem initial_state_with_simp[simp]:
   (initial_state f c co cc k with clock := k' = initial_state f c co cc k') ∧
   (initial_state f c co cc k with stack := [] = initial_state f c co cc k) ∧
   (initial_state f c co cc k with locals := LN = initial_state f c co cc k)
Proof
  srw_tac[][initial_state_def]
QED

Theorem Boolv_11[simp]:
   dataSem$Boolv b1 = Boolv b2 ⇔ b1 = b2
Proof
  EVAL_TAC>>srw_tac[][]
QED

Theorem with_same_locals:
   (s with locals := s.locals) = s
Proof
  full_simp_tac(srw_ss())[state_component_equality]
QED

val var_corr_def = Define `
  var_corr env corr t <=>
    EVERY2 (\v x. get_var v t = SOME x) corr env`;

Theorem get_vars_thm:
   !vs a t2. var_corr a vs t2 ==> (get_vars vs t2 = SOME a)
Proof
  Induct \\ Cases_on `a` \\ FULL_SIMP_TAC std_ss [get_vars_def]
  \\ FULL_SIMP_TAC (srw_ss()) [var_corr_def] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
QED

Theorem get_vars_append:
   ∀l1 l2 s. get_vars (l1 ++ l2) s = OPTION_BIND (get_vars l1 s)(λy1. OPTION_BIND (get_vars l2 s)(λy2. SOME(y1 ++ y2)))
Proof
  Induct >> simp[get_vars_def,OPTION_BIND_SOME,ETA_AX] >> srw_tac[][] >>
  BasicProvers.EVERY_CASE_TAC >> full_simp_tac(srw_ss())[]
QED

Theorem get_vars_reverse:
   ∀ls s ys. get_vars ls s = SOME ys ⇒ get_vars (REVERSE ls) s = SOME (REVERSE ys)
Proof
  Induct >> simp[get_vars_def] >> srw_tac[][get_vars_append] >>
  BasicProvers.EVERY_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  srw_tac[][get_vars_def]
QED

Theorem EVERY_get_vars:
   !args s1 s2.
      EVERY (\a. lookup a s1 = lookup a s2) args ==>
      (get_vars args s1 = get_vars args s2)
Proof
  Induct \\ full_simp_tac(srw_ss())[get_vars_def,get_var_def] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
QED

Theorem get_vars_IMP_domain:
   !args x s vs. MEM x args /\ (get_vars args s = SOME vs) ==>
                  x IN domain s
Proof
  Induct \\ full_simp_tac(srw_ss())[get_vars_def,get_var_def] \\ REPEAT STRIP_TAC
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
  \\ full_simp_tac(srw_ss())[domain_lookup]
QED

Theorem cut_state_opt_with_const:
   (cut_state_opt x (y with stack := z) = OPTION_MAP (λs. s with stack := z) (cut_state_opt x y)) ∧
   (cut_state_opt x (y with clock := k) = OPTION_MAP (λs. s with clock := k) (cut_state_opt x y))
Proof
  EVAL_TAC >> every_case_tac >> simp[]
QED

Theorem consume_space_add_space:
   consume_space k (add_space t k with locals := env1) =
    SOME (t with <| locals := env1 ; space := 0  |>)
Proof
  full_simp_tac(srw_ss())[consume_space_def,add_space_def,state_component_equality] \\ DECIDE_TAC
QED

val consume_space_with_stack = Q.prove(
  `consume_space x (y with stack := z) = OPTION_MAP (λs. s with stack := z) (consume_space x y)`,
  EVAL_TAC >> srw_tac[][])

val consume_space_with_locals = Q.prove(
  `consume_space x (y with locals := z) = OPTION_MAP (λs. s with locals := z) (consume_space x y)`,
  EVAL_TAC >> srw_tac[][])

val do_app_with_stack = time Q.prove(
  `do_app op vs (s with stack := z) =
   map_result (λ(x,y). (x,y with stack := z)) I (do_app op vs s)`,
  Cases_on `do_app op vs (s with stack := z)`
  \\ Cases_on `op`
  \\ ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_space_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,do_install_def,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def] >>
          TRY (pairarg_tac \\ fs []) >>
          rveq >> fs []));

val do_app_aux_with_space = time Q.store_thm("do_app_aux_with_space",
  `do_app_aux op vs (s with space := z) = map_result (λ(x,y). (x,y with space := z)) I (do_app_aux op vs s)`,
  Cases_on `do_app_aux op vs (s with space := z)`
  \\ Cases_on `op`
  \\ ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_space_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,do_install_def,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def] >>
          TRY (pairarg_tac \\ fs []) >>
          rveq >> fs []));

val do_app_aux_with_locals = time Q.store_thm("do_app_aux_with_locals",
  `do_app_aux op vs (s with locals := z) = map_result (λ(x,y). (x,y with locals := z)) I (do_app_aux op vs s)`,
  Cases_on `do_app_aux op vs (s with locals := z)`
  \\ Cases_on `op`
  \\ ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_space_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,do_install_def,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def] >>
          TRY (pairarg_tac \\ fs []) >>
          rveq >> fs []));

val do_app_with_locals = time Q.prove(
  `do_app op vs (s with locals := z) = map_result (λ(x,y). (x,y with locals := z)) I (do_app op vs s)`,
  Cases_on `do_app op vs (s with locals := z)`
  \\ Cases_on `op`
  \\ ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_space_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,do_install_def,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def] >>
          TRY (pairarg_tac \\ fs []) >>
          rveq >> fs []));

val do_app_aux_err = Q.store_thm("do_app_aux_err",
  `do_app_aux op vs s = Rerr e ⇒ (e = Rabort Rtype_error)
                             \/
                             (?i x. op = FFI i /\ e = Rabort (Rffi_error x)) `,
  rw [ do_app_aux_def,case_eq_thms
     , do_install_def,do_space_def,with_fresh_ts_def
     , PULL_EXISTS, UNCURRY,consume_space_def]
  \\ fs []);

val do_app_aux_const = Q.store_thm("do_app_aux_const",
  `do_app_aux op vs x = Rval (y,z) ⇒
    z.stack = x.stack ∧ z.handler = x.handler ∧ z.locals = x.locals ∧
    z.clock = x.clock ∧ z.compile = x.compile`,
  rw [ do_app_aux_def,case_eq_thms
     , do_install_def,do_space_def,with_fresh_ts_def
     , PULL_EXISTS, UNCURRY,consume_space_def]
  \\ fs []);

Theorem do_app_err:
   do_app op vs s = Rerr e ⇒ (e = Rabort Rtype_error)
                             \/
                             (?i x. op = FFI i /\ e = Rabort (Rffi_error x))
Proof
  rw [ do_app_def,case_eq_thms
     , do_install_def,do_space_def,with_fresh_ts_def
     , PULL_EXISTS, UNCURRY,consume_space_def]
  \\ fs []
  \\ METIS_TAC [do_app_aux_err]
QED

Theorem do_app_const:
   do_app op vs x = Rval (y,z) ⇒
    z.stack = x.stack ∧ z.handler = x.handler ∧ z.locals = x.locals ∧
    z.clock = x.clock ∧ z.compile = x.compile
Proof
  rw [ do_app_def,do_app_aux_def,case_eq_thms
     , do_install_def,do_space_def,with_fresh_ts_def
     , PULL_EXISTS, UNCURRY,consume_space_def]
  \\ fs []
QED

Theorem do_app_locals:
   (do_app op x s = Rval (q,r)) ==>
   (do_app op x (s with locals := extra) =
         Rval (q,r with locals := extra))
Proof
   rw [ do_app_def,do_app_aux_def,case_eq_thms
      , do_install_def,do_space_def,with_fresh_ts_def
      , PULL_EXISTS, UNCURRY,consume_space_def]
   \\ fs []
QED

Theorem do_space_alt:
   do_space op l s =
      if op_space_reset op then SOME (s with space := 0)
      else consume_space (op_space_req op l) s
Proof
  full_simp_tac(srw_ss())[do_space_def] \\ SRW_TAC [] [consume_space_def]
  \\ full_simp_tac(srw_ss())[state_component_equality] \\ fs[] \\ DECIDE_TAC
QED

Theorem Seq_Skip:
   evaluate (Seq c Skip,s) = evaluate (c,s)
Proof
  full_simp_tac(srw_ss())[evaluate_def] \\ Cases_on `evaluate (c,s)` \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
QED

Theorem evaluate_stack_swap:
   !c ^s.
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
                             (res, s1 with stack := xs))
Proof
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  THEN1 full_simp_tac(srw_ss())[evaluate_def]
  THEN1 (
    full_simp_tac(srw_ss())[evaluate_def] >> EVAL_TAC >>
    every_case_tac >> full_simp_tac(srw_ss())[] )
  THEN1 (
    full_simp_tac(srw_ss())[evaluate_def] >>
    every_case_tac >>
    full_simp_tac(srw_ss())[set_var_def,cut_state_opt_with_const,do_app_with_stack] >>
    imp_res_tac do_app_err >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
    full_simp_tac(srw_ss())[cut_state_opt_def,cut_state_def] >> every_case_tac >> full_simp_tac(srw_ss())[] >>
    rpt var_eq_tac >> full_simp_tac(srw_ss())[do_app_with_locals] >>
    TRY(first_assum(split_uncurry_arg_tac o rhs o concl) >> full_simp_tac(srw_ss())[]) >>
    imp_res_tac do_app_const >> simp[] >>
    EVAL_TAC >> simp[])
  THEN1 (
    full_simp_tac(srw_ss())[evaluate_def] >>
    EVAL_TAC >>
    every_case_tac >> full_simp_tac(srw_ss())[] )
  THEN1 (
    full_simp_tac(srw_ss())[evaluate_def] >>
    EVAL_TAC >>
    every_case_tac >> full_simp_tac(srw_ss())[] )
  THEN1 (
    full_simp_tac(srw_ss())[evaluate_def] >>
    EVAL_TAC >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    rpt gen_tac >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    srw_tac[][] >> simp[])
  THEN1 (
    full_simp_tac(srw_ss())[evaluate_def] >>
    EVAL_TAC >>
    every_case_tac >> full_simp_tac(srw_ss())[] )
  THEN1 (* Seq *)
   (full_simp_tac(srw_ss())[evaluate_def]
    \\ Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ Cases_on `evaluate (c2,r)` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ Cases_on `q = NONE` \\ full_simp_tac(srw_ss())[] \\ Cases_on `q'` \\ full_simp_tac(srw_ss())[]
    \\ TRY (Cases_on `x`) \\ TRY (Cases_on`e`) \\ full_simp_tac(srw_ss())[jump_exc_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
    \\ Q.PAT_X_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPEC `xs`) \\ full_simp_tac(srw_ss())[])
  THEN1 (* If *)
   (full_simp_tac(srw_ss())[evaluate_def]
    \\ Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ Cases_on `evaluate (c2,s)` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `isBool T x` \\ full_simp_tac(srw_ss())[get_var_def]
    \\ Cases_on `isBool F x` \\ full_simp_tac(srw_ss())[get_var_def])
  THEN1 (* Call *)
   (full_simp_tac(srw_ss())[evaluate_def]
    \\ Cases_on `get_vars args s.locals` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `find_code dest x s.code` \\ full_simp_tac(srw_ss())[]
    \\ TRY (full_simp_tac(srw_ss())[call_env_def] \\ NO_TAC)
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `ret` \\ full_simp_tac(srw_ss())[] THEN1
     (every_case_tac \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[call_env_def,dec_clock_def,jump_exc_def]
      \\ every_case_tac \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ Q.PAT_X_ASSUM `xxx = SOME s7` MP_TAC
      \\ every_case_tac \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
      \\ Q.PAT_X_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPEC `xs`) \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `cut_env r' s.locals` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] THEN1 (full_simp_tac(srw_ss())[call_env_def])
    \\ Cases_on `evaluate (r,call_env q (push_env x' (IS_SOME handler) (dec_clock ^s)))` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `q''` \\ fs []
    \\ Cases_on `x''` \\ full_simp_tac(srw_ss())[]
    THEN1 (Cases_on `handler`
       \\ full_simp_tac(srw_ss())[pop_env_def,call_env_def,push_env_def,set_var_def,dec_clock_def]
       \\ REPEAT STRIP_TAC
       \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `Exc x' ^s.handler::xs`)
       \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ reverse(Cases_on`e`)\\full_simp_tac(srw_ss())[] THEN1 (
         Cases_on`a`>>full_simp_tac(srw_ss())[]>>
         srw_tac[][]>>
         qpat_abbrev_tac`ss = call_env X Y` >>
         first_x_assum(qspec_then`ss.stack`mp_tac) >>
         (impl_tac >- (
            simp[Abbr`ss`] >>
            EVAL_TAC >>
            Cases_on`handler`>>EVAL_TAC >>
            simp[] )) >>
         qpat_abbrev_tac`st:('c,'ffi) dataSem$state = X Y` >>
         `st = ss` by (
           simp[Abbr`ss`,Abbr`st`,dataSemTheory.state_component_equality] >>
           EVAL_TAC >>
           Cases_on`handler`>>EVAL_TAC >>
           simp[] ) >>
         full_simp_tac(srw_ss())[])
    \\ Cases_on `handler` \\ full_simp_tac(srw_ss())[] THEN1
     (full_simp_tac(srw_ss())[pop_env_def,call_env_def,push_env_def,set_var_def,dec_clock_def]
      \\ full_simp_tac(srw_ss())[jump_exc_def]
      \\ Cases_on `s.handler = LENGTH s.stack` \\ full_simp_tac(srw_ss())[LASTN_LEMMA]
      \\ `s.handler < LENGTH s.stack` by DECIDE_TAC \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC LASTN_TL \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `LASTN (s.handler + 1) s.stack` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ Q.PAT_X_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPECL [`Env x'::xs`,
           `s7 with clock := s7.clock - 1`])
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
      \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      \\ IMP_RES_TAC LASTN_TL \\ full_simp_tac(srw_ss())[]
      \\ every_case_tac \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality])
    \\ Cases_on `x''` \\ full_simp_tac(srw_ss())[]
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate (r,call_env q (push_env x8 T (dec_clock s))) =
          (SOME (Rerr (Rraise b)),s9)`
    \\ Cases_on `evaluate (r''',set_var q'' b s9)` \\ full_simp_tac(srw_ss())[]
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate (r''',set_var q'' b s9) = (res,r5)`
    \\ Cases_on `res` \\ full_simp_tac(srw_ss())[]
    THEN1 (* NONE *)
     (STRIP_TAC THEN1 (full_simp_tac(srw_ss())[set_var_def,pop_env_def,jump_exc_def,call_env_def,
          push_env_def,LASTN_LEMMA,dec_clock_def] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
          \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ STRIP_TAC THEN1 (full_simp_tac(srw_ss())[set_var_def,pop_env_def,jump_exc_def,call_env_def,
          push_env_def,LASTN_LEMMA,dec_clock_def] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock (^s with stack := xs)))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock (s with stack := xs)))).stack) =
          (call_env q (push_env x8 T (dec_clock (s with stack := xs))))` by full_simp_tac(srw_ss())[call_env_def,push_env_def,dec_clock_def]
      \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[call_env_def,push_env_def,jump_exc_def,
           LASTN_LEMMA,dec_clock_def,set_var_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `LENGTH s.stack = LENGTH xs` (ASSUME_TAC o GSYM)
      \\ full_simp_tac(srw_ss())[LASTN_LEMMA] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `xs`)
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[] \\ REV_FULL_SIMP_TAC std_ss []
      \\ POP_ASSUM (fn th => full_simp_tac(srw_ss())[GSYM th])
      \\ REPEAT AP_TERM_TAC \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality])
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
    THEN1 (* SOME Rval *)
     (STRIP_TAC THEN1 (full_simp_tac(srw_ss())[set_var_def,pop_env_def,jump_exc_def,call_env_def,
          push_env_def,LASTN_LEMMA,dec_clock_def] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
          \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ STRIP_TAC THEN1 (full_simp_tac(srw_ss())[set_var_def,pop_env_def,jump_exc_def,call_env_def,
          push_env_def,LASTN_LEMMA,dec_clock_def] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock (^s with stack := xs)))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock (s with stack := xs)))).stack) =
          (call_env q (push_env x8 T (dec_clock (s with stack := xs))))` by full_simp_tac(srw_ss())[call_env_def,push_env_def,dec_clock_def]
      \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[call_env_def,push_env_def,jump_exc_def,
           LASTN_LEMMA,dec_clock_def,set_var_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `LENGTH s.stack = LENGTH xs` (ASSUME_TAC o GSYM)
      \\ full_simp_tac(srw_ss())[LASTN_LEMMA] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `xs`)
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[] \\ REV_FULL_SIMP_TAC std_ss []
      \\ POP_ASSUM (fn th => full_simp_tac(srw_ss())[GSYM th])
      \\ REPEAT AP_TERM_TAC \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality])
    \\ Cases_on`e` \\ full_simp_tac(srw_ss())[]
    THEN1 (* Rraise *)
     (FIRST_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock ^s))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock s))).stack) =
          (call_env q (push_env x8 T (dec_clock s)))` by full_simp_tac(srw_ss())[call_env_def,push_env_def,dec_clock_def]
      \\ POP_ASSUM (fn th => SIMP_TAC std_ss [th])
      \\ SIMP_TAC std_ss [Once dec_clock_def]
      \\ SIMP_TAC std_ss [Once push_env_def]
      \\ SIMP_TAC std_ss [Once call_env_def]
      \\ SIMP_TAC std_ss [Once jump_exc_def]
      \\ SIMP_TAC (srw_ss()) [LASTN_LEMMA] \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality]
      \\ Q.PAT_X_ASSUM `jump_exc (set_var q'' b s9) = SOME s2'` MP_TAC
      \\ SIMP_TAC std_ss [Once set_var_def]
      \\ SIMP_TAC (srw_ss()) [Once jump_exc_def]
      \\ Cases_on `LASTN (s9.handler + 1) s9.stack` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `h` \\ full_simp_tac(srw_ss())[] \\ SIMP_TAC std_ss [Once EQ_SYM_EQ]
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC)
      \\ SIMP_TAC std_ss [Once jump_exc_def] \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock (^s with stack := xs)))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock (s with stack := xs)))).stack) =
          (call_env q (push_env x8 T (dec_clock (s with stack := xs))))` by full_simp_tac(srw_ss())[call_env_def,push_env_def,dec_clock_def]
      \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[call_env_def,push_env_def,jump_exc_def,
           LASTN_LEMMA,dec_clock_def,set_var_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `LENGTH _.stack = LENGTH xs` (ASSUME_TAC o GSYM)
      \\ full_simp_tac(srw_ss())[LASTN_LEMMA] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `xs`)
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[] \\ REV_FULL_SIMP_TAC std_ss []
      \\ Cases_on `LASTN (s9.handler + 1) xs` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
      \\ `s9 with <|locals := insert q'' b s9.locals; stack := xs;
             handler := s9.handler|> =
          s9 with <|locals := insert q'' b s9.locals; stack := xs|>` by (full_simp_tac(srw_ss())[dataSemTheory.state_component_equality]) \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality])
    \\ Cases_on`a` \\ full_simp_tac(srw_ss())[]
    THEN (* Rtimeout_error *)
     (REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock (^s with stack := xs)))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock (s with stack := xs)))).stack) =
          (call_env q (push_env x8 T (dec_clock (s with stack := xs))))` by full_simp_tac(srw_ss())[call_env_def,push_env_def,dec_clock_def]
      \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[call_env_def,push_env_def,jump_exc_def,
           LASTN_LEMMA,dec_clock_def,set_var_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `LENGTH s.stack = LENGTH xs` (ASSUME_TAC o GSYM)
      \\ full_simp_tac(srw_ss())[LASTN_LEMMA] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `xs`)
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[] \\ REV_FULL_SIMP_TAC std_ss []
      \\ POP_ASSUM (fn th => full_simp_tac(srw_ss())[GSYM th])
      \\ REPEAT AP_TERM_TAC \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality]))
QED

Theorem evaluate_stack:
   !c ^s.
      case evaluate (c,s) of
      | (SOME (Rerr(Rabort Rtype_error)),s1) => T
      | (SOME (Rerr(Rabort _)),s1) => (s1.stack = [])
      | (SOME (Rerr _),s1) =>
            (?s2. (jump_exc s = SOME s2) /\ (s2.locals = s1.locals) /\
                  (s2.stack = s1.stack) /\ (s2.handler = s1.handler))
      | (_,s1) => (s1.stack = s.stack) /\ (s1.handler = s.handler)
Proof
  REPEAT STRIP_TAC \\ ASSUME_TAC (SPEC_ALL evaluate_stack_swap)
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
QED

Theorem evaluate_NONE_jump_exc:
   (evaluate (c,^s) = (NONE,u1)) /\ (jump_exc u1 = SOME x) ==>
    (jump_exc s = SOME (s with <| stack := x.stack ;
                                  handler := x.handler ;
                                  locals := x.locals |>))
Proof
  REPEAT STRIP_TAC \\ MP_TAC (Q.SPECL [`c`,`s`] evaluate_stack) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[jump_exc_def] \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ every_case_tac >> full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] []
QED

Theorem evaluate_NONE_jump_exc_ALT:
   (evaluate (c,^s) = (NONE,u1)) /\ (jump_exc s = SOME x) ==>
    (jump_exc u1 = SOME (u1 with <| stack := x.stack ;
                                  handler := x.handler ;
                                  locals := x.locals |>))
Proof
  REPEAT STRIP_TAC \\ MP_TAC (Q.SPECL [`c`,`s`] evaluate_stack) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[jump_exc_def] \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ every_case_tac >> full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] []
QED

val evaluate_locals_LN_lemma = Q.prove(
  `!c ^s.
      FST (evaluate (c,s)) <> NONE /\
      FST (evaluate (c,s)) <> SOME (Rerr(Rabort Rtype_error)) ==>
      ((SND (evaluate (c,s))).locals = LN) \/
      ?t. FST (evaluate (c,s)) = SOME (Rerr(Rraise t))`,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[evaluate_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[call_env_def,fromList_def]
  \\ imp_res_tac do_app_err >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
  \\ Cases_on`a`>>full_simp_tac(srw_ss())[]);

Theorem evaluate_locals_LN:
   !c ^s res t.
      (evaluate (c,s) = (res,t)) /\ res <> NONE /\ res <> SOME (Rerr(Rabort Rtype_error)) ==>
      (t.locals = LN) \/ ?t. res = SOME (Rerr(Rraise t))
Proof
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL evaluate_locals_LN_lemma) \\ full_simp_tac(srw_ss())[]
QED

val locals_ok_def = Define `
  locals_ok l1 l2 =
    !v x. (sptree$lookup v l1 = SOME x) ==> (sptree$lookup v l2 = SOME x)`;

Theorem locals_ok_IMP:
   locals_ok l1 l2 ==> domain l1 SUBSET domain l2
Proof
  full_simp_tac(srw_ss())[locals_ok_def,SUBSET_DEF,domain_lookup] \\ METIS_TAC []
QED

Theorem locals_ok_refl:
   !l. locals_ok l l
Proof
  full_simp_tac(srw_ss())[locals_ok_def]
QED

Theorem locals_ok_cut_env:
   locals_ok l1 l2 /\
    (cut_env names l1 = SOME x) ==>
    (cut_env names l2 = SOME x)
Proof
  full_simp_tac(srw_ss())[cut_env_def] \\ SRW_TAC [] []
  THEN1 (IMP_RES_TAC locals_ok_IMP \\ IMP_RES_TAC SUBSET_TRANS)
  \\ full_simp_tac(srw_ss())[lookup_inter_alt] \\ SRW_TAC [] []
  \\ full_simp_tac(srw_ss())[locals_ok_def,domain_lookup,SUBSET_DEF,PULL_EXISTS]
  \\ full_simp_tac(srw_ss())[oneTheory.one] \\ RES_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[]
QED

Theorem locals_ok_get_var:
   locals_ok s l /\
    (get_var x s = SOME w) ==>
    (get_var x l = SOME w)
Proof
  full_simp_tac(srw_ss())[locals_ok_def,get_var_def]
QED

Theorem locals_ok_get_vars:
   !x w.
      locals_ok s l /\
      (get_vars x s = SOME w) ==>
      (get_vars x l = SOME w)
Proof
  Induct \\ full_simp_tac(srw_ss())[get_vars_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `get_var h s` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `get_vars x s` \\ full_simp_tac(srw_ss())[]
  \\ IMP_RES_TAC locals_ok_get_var \\ full_simp_tac(srw_ss())[]
QED

Theorem evaluate_locals:
   !c s res s2 vars l.
      res <> SOME (Rerr(Rabort Rtype_error)) /\ (evaluate (c,s) = (res,s2)) /\
      locals_ok s.locals l ==>
      ?w. (evaluate (c, s with locals := l) =
             (res,if res = NONE then s2 with locals := w
                                else s2)) /\
          locals_ok s2.locals w
Proof
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[evaluate_def]
  THEN1 (* Skip *) (METIS_TAC [])
  THEN1 (* Move *)
   (Cases_on `get_var src s.locals` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ IMP_RES_TAC locals_ok_get_var \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[get_var_def,lookup_union,set_var_def,locals_ok_def]
    \\ Q.EXISTS_TAC `insert dest x l` \\ full_simp_tac(srw_ss())[lookup_insert]
    \\ METIS_TAC [])
  THEN1 (* Assign *)
   (Cases_on `names_opt` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `op_requires_names op` \\ full_simp_tac(srw_ss())[cut_state_opt_def] THEN1
     (Cases_on `get_vars args s.locals` \\ full_simp_tac(srw_ss())[cut_state_opt_def]
      \\ IMP_RES_TAC locals_ok_get_vars \\ full_simp_tac(srw_ss())[]
      \\ fs [do_app_with_locals]
      \\ fs [case_eq_thms,semanticPrimitivesTheory.result_case_eq]
      \\ fs [call_env_def,set_var_def,state_component_equality]
      \\ fs [locals_ok_def,lookup_insert] \\ rw []
      \\ rpt (qpat_x_assum `insert _ _ _ = _` (assume_tac o GSYM))
      \\ rpt (qpat_x_assum `fromList [] = _` (assume_tac o GSYM))
      \\ fs [lookup_insert] \\ rfs []
      \\ imp_res_tac do_app_const \\ fs [fromList_def,lookup_def])
    \\ full_simp_tac(srw_ss())[cut_state_def]
    \\ Cases_on `cut_env x s.locals` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC locals_ok_cut_env \\ full_simp_tac(srw_ss())[]
    \\ Q.EXISTS_TAC `s2.locals` \\ full_simp_tac(srw_ss())[locals_ok_def]
    \\ SRW_TAC [] [state_component_equality])
  THEN1 (* Tick *)
   (Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[locals_ok_def,call_env_def,EVAL ``fromList []``,lookup_def,
           dec_clock_def] \\ METIS_TAC [])
  THEN1 (* MakeSpace *)
   (Cases_on `cut_env names s.locals` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC locals_ok_cut_env
    \\ full_simp_tac(srw_ss())[LET_DEF,add_space_def,state_component_equality,locals_ok_def])
  THEN1 (* Raise *)
   (Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ `jump_exc (s with locals := l) = jump_exc s` by
         full_simp_tac(srw_ss())[jump_exc_def] \\ Cases_on `jump_exc s` \\ full_simp_tac(srw_ss())[]
    \\ `get_var n l = SOME x` by
         full_simp_tac(srw_ss())[locals_ok_def,get_var_def] \\ full_simp_tac(srw_ss())[]
    \\ srw_tac [] [] \\ Q.EXISTS_TAC `s2.locals`
    \\ full_simp_tac(srw_ss())[locals_ok_def])
  THEN1 (* Return *)
   (Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ `get_var n l = SOME x` by
         full_simp_tac(srw_ss())[locals_ok_def,get_var_def] \\ full_simp_tac(srw_ss())[]
    \\ srw_tac [] [call_env_def]
    \\ simp[locals_ok_def,lookup_fromList])
  THEN1 (* Seq *)
   (Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ Cases_on `q = SOME (Rerr(Rabort Rtype_error))` \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `q` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ METIS_TAC [])
  THEN1 (* If *)
   (Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC locals_ok_get_var \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `isBool T x` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `isBool F x` \\ full_simp_tac(srw_ss())[])
  THEN1 (* Call *)
   (Cases_on `get_vars args s.locals` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC locals_ok_get_vars \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `find_code dest x s.code` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `ret` \\ full_simp_tac(srw_ss())[] THEN1
     (Cases_on `handler` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ `call_env q (dec_clock (s with locals := l)) =
          call_env q (dec_clock s)` by
         full_simp_tac(srw_ss())[state_component_equality,dec_clock_def,call_env_def] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[call_env_def,locals_ok_def,lookup_def,fromList_def]
      \\ Q.EXISTS_TAC `s2.locals` \\ full_simp_tac(srw_ss())[locals_ok_refl]
      \\ SRW_TAC [] [state_component_equality])
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `cut_env r' s.locals` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC locals_ok_cut_env \\ full_simp_tac(srw_ss())[]
    \\ `call_env q (push_env x' (IS_SOME handler)
          (dec_clock (s with locals := l))) =
        call_env q (push_env x' (IS_SOME handler)
          (dec_clock s))` by
     (Cases_on `handler`
      \\ full_simp_tac(srw_ss())[state_component_equality,dec_clock_def,call_env_def,push_env_def])
    \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[call_env_def,locals_ok_def,lookup_def,fromList_def]
    \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [locals_ok_refl,with_same_locals])
QED

Theorem funpow_dec_clock_clock:
   !n s. FUNPOW dec_clock n s = (s with clock := s.clock - n)
Proof
  Induct_on `n` >>
  srw_tac[][FUNPOW, state_component_equality, dec_clock_def, ADD1] >>
  decide_tac
QED

Theorem evaluate_mk_ticks:
   !p s n.
    evaluate (mk_ticks n p, s)
    =
    if s.clock < n then
      (SOME (Rerr(Rabort Rtimeout_error)), s with <| clock := 0; locals := fromList []; stack := [] |>)
    else
      evaluate (p, FUNPOW dec_clock n s)
Proof
  Induct_on `n` >>
  srw_tac[][evaluate_def, mk_ticks_def, FUNPOW] >>
  full_simp_tac(srw_ss())[mk_ticks_def, evaluate_def] >>
  srw_tac[][funpow_dec_clock_clock, dec_clock_def] >>
  simp [call_env_def] >>
  `s.clock - n = 0` by decide_tac >>
  `s.clock - (n+1) = 0` by decide_tac >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[ADD1, LESS_OR_EQ] >>
  full_simp_tac (srw_ss()++ARITH_ss) []
QED

Theorem FUNPOW_dec_clock_code[simp]:
   ((FUNPOW dec_clock n t).code = t.code) /\
    ((FUNPOW dec_clock n t).stack = t.stack) /\
    ((FUNPOW dec_clock n t).handler = t.handler) /\
    ((FUNPOW dec_clock n t).refs = t.refs) /\
    ((FUNPOW dec_clock n t).ffi = t.ffi) /\
    ((FUNPOW dec_clock n t).global = t.global) /\
    ((FUNPOW dec_clock n t).locals = t.locals) /\
    ((FUNPOW dec_clock n t).compile = t.compile) /\
    ((FUNPOW dec_clock n t).compile_oracle = t.compile_oracle) /\
    ((FUNPOW dec_clock n t).clock = t.clock - n)
Proof
  Induct_on `n` \\ full_simp_tac(srw_ss())[FUNPOW_SUC,dec_clock_def] \\ DECIDE_TAC
QED

Theorem jump_exc_NONE:
   (jump_exc (t with locals := x) = NONE <=> jump_exc t = NONE) /\
    (jump_exc (t with clock := c) = NONE <=> jump_exc t = NONE)
Proof
  FULL_SIMP_TAC (srw_ss()) [jump_exc_def] \\ REPEAT STRIP_TAC
  \\ every_case_tac \\ FULL_SIMP_TAC std_ss []
QED

Theorem jump_exc_IMP:
   (jump_exc s = SOME t) ==>
    s.handler < LENGTH s.stack /\
    ?n e xs. (LASTN (s.handler + 1) s.stack = Exc e n::xs) /\
             (t = s with <|handler := n; locals := e; stack := xs|>)
Proof
  SIMP_TAC std_ss [jump_exc_def]
  \\ Cases_on `LASTN (s.handler + 1) s.stack` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
QED

Theorem do_app_Rerr:
   dataSem$do_app op vs s = Rerr e ⇒ (e = Rabort Rtype_error)
                             \/
                             (?i x. op = FFI i /\ e = Rabort (Rffi_error x))
Proof
  strip_tac \\ imp_res_tac do_app_err \\ fs []
QED

Theorem do_app_with_clock:
   do_app op vs (s with clock := z) =
   map_result (λ(x,y). (x,y with clock := z)) I (do_app op vs s)
Proof
  Cases_on `op = Install` THEN1
   (fs [do_app_def,do_install_def]
    \\ every_case_tac \\ fs []
    \\ pairarg_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs []) >>
  Cases_on `do_app op vs s` >>
  fs[do_app_def,do_space_def] >>
  Cases_on `op` >>
  ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def] >>
          rveq >> fs [])
QED

Theorem do_app_change_clock:
   (do_app op args s1 = Rval (res,s2)) ==>
   (do_app op args (s1 with clock := ck) = Rval (res,s2 with clock := ck))
Proof
  Cases_on `op = Install` THEN1
   (fs [do_app_def,do_install_def]
    \\ every_case_tac \\ fs []
    \\ pairarg_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs []) >>
  srw_tac[][do_app_def,do_space_def] >>
  Cases_on `op` >>
  ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def] >>
          rveq >> fs [])
QED

Theorem do_app_change_clock_err:
   (do_app op args s1 = Rerr e) ==>
   (do_app op args (s1 with clock := ck) = Rerr e)
Proof
  Cases_on `op = Install` THEN1
   (fs [do_app_def,do_install_def]
    \\ every_case_tac \\ fs []
    \\ pairarg_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs []) >>
  srw_tac[][do_app_def,do_space_def] >>
  Cases_on `op` >>
  ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def] >>
          rveq >> fs [])
QED

Theorem cut_state_eq_some:
   cut_state names s = SOME y ⇔ ∃z. cut_env names s.locals = SOME z ∧ y = s with locals := z
Proof
  srw_tac[][cut_state_def] >> every_case_tac >> full_simp_tac(srw_ss())[EQ_IMP_THM]
QED

Theorem cut_state_eq_none:
   cut_state names s = NONE ⇔ cut_env names s.locals = NONE
Proof
  srw_tac[][cut_state_def] >> every_case_tac >> full_simp_tac(srw_ss())[EQ_IMP_THM]
QED

Theorem with_same_clock[simp]:
   ^s with clock := s.clock = s
Proof
  srw_tac[][state_component_equality]
QED

Theorem evaluate_add_clock:
   !exps s1 res s2.
    evaluate (exps,s1) = (res, s2) ∧
    res ≠ SOME(Rerr(Rabort Rtimeout_error))
    ⇒
    !ck. evaluate (exps,s1 with clock := s1.clock + ck) = (res, s2 with clock := s2.clock + ck)
Proof
  recInduct evaluate_ind >> srw_tac[][evaluate_def]
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[get_var_def,set_var_def] >> srw_tac[][] >> full_simp_tac(srw_ss())[] )
  >- (
    fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,cut_state_opt_def,cut_state_def,
              bool_case_eq,ffiTheory.call_FFI_def,semanticPrimitivesTheory.result_case_eq,
              with_fresh_ts_def,closSemTheory.ref_case_eq,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def] >>
    rveq \\ fs [call_env_def,do_app_with_clock,do_app_with_locals]
    \\ imp_res_tac do_app_const \\ fs [set_var_def,state_component_equality]
    \\ PairCases_on `y` \\ fs []
    \\ qpat_x_assum `v4 = _` (fn th => once_rewrite_tac [th]) \\ fs []
    \\ imp_res_tac do_app_const \\ fs [set_var_def,state_component_equality])
  >- ( EVAL_TAC >> simp[state_component_equality] )
  >- ( every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> EVAL_TAC )
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[jump_exc_NONE] >>
    imp_res_tac jump_exc_IMP >> full_simp_tac(srw_ss())[] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[jump_exc_def])
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][call_env_def] )
  >- (
    full_simp_tac(srw_ss())[LET_THM] >>
    pairarg_tac >> full_simp_tac(srw_ss())[] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    rev_full_simp_tac(srw_ss())[] >> srw_tac[][] )
  >- ( every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] )
  >- (
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
    fsrw_tac[ARITH_ss][call_env_def,dec_clock_def,push_env_def,pop_env_def,set_var_def] >>
    first_x_assum(qspec_then`ck`mp_tac) >> simp[] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >>
    spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[])
QED

Theorem set_var_const[simp]:
   (set_var x y z).ffi = z.ffi ∧
   (set_var x y z).clock = z.clock
Proof
  EVAL_TAC
QED

Theorem set_var_with_const:
   (set_var x y (z with clock := k)) = set_var x y z with clock := k
Proof
  EVAL_TAC
QED

Theorem cut_state_opt_const:
   cut_state_opt x y = SOME z ⇒
   z.ffi = y.ffi ∧
   z.global = y.global
Proof
   EVAL_TAC >>
   every_case_tac >> EVAL_TAC >>
   srw_tac[][] >> srw_tac[][]
QED

Theorem do_app_io_events_mono:
   do_app x y z = Rval (a,b) ⇒
   z.ffi.io_events ≼ b.ffi.io_events
Proof
  Cases_on `x = Install` THEN1
   (fs [do_app_def,do_install_def]
    \\ every_case_tac \\ fs []
    \\ pairarg_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs []) >>
  srw_tac[][do_app_def,do_space_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  Cases_on `x` >>
  ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def] >>
  rveq >> fs [])
QED

Theorem call_env_const[simp]:
   (call_env x y).ffi = y.ffi ∧
   (call_env x y).clock = y.clock
Proof
  EVAL_TAC
QED

Theorem call_env_with_const:
   (call_env x  (y with clock := z)) = call_env x y with clock := z
Proof
  EVAL_TAC
QED

Theorem dec_clock_const[simp]:
   (dec_clock s).ffi = s.ffi
Proof
  EVAL_TAC
QED

Theorem add_space_const[simp]:
   (add_space s k).ffi = s.ffi
Proof
  EVAL_TAC
QED

Theorem push_env_const[simp]:
   (push_env x y z).ffi = z.ffi ∧
   (push_env x y z).clock = z.clock
Proof
  Cases_on`y`>> EVAL_TAC
QED

Theorem push_env_with_const:
   (push_env x y (z with clock := k)) = (push_env x y z) with clock := k
Proof
  Cases_on`y`>>EVAL_TAC
QED

Theorem pop_env_const:
   pop_env a = SOME b ⇒
   b.ffi = a.ffi
Proof
   EVAL_TAC >>
   every_case_tac >> EVAL_TAC >>
   srw_tac[][] >> srw_tac[][]
QED

Theorem evaluate_io_events_mono:
   !exps s1 res s2.
    evaluate (exps,s1) = (res, s2)
    ⇒
    s1.ffi.io_events ≼ s2.ffi.io_events
Proof
  recInduct evaluate_ind >> srw_tac[][evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[LET_THM] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  TRY (pairarg_tac >> full_simp_tac(srw_ss())[] >> every_case_tac >> full_simp_tac(srw_ss())[])>>
  imp_res_tac cut_state_opt_const >>full_simp_tac(srw_ss())[] >>
  imp_res_tac pop_env_const >>full_simp_tac(srw_ss())[] >>
  imp_res_tac jump_exc_IMP >> full_simp_tac(srw_ss())[] >>
  imp_res_tac do_app_io_events_mono  >>full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
  metis_tac[IS_PREFIX_TRANS]
QED

Theorem with_clock_ffi:
   (^s with clock := y).ffi = s.ffi
Proof
  EVAL_TAC
QED

Theorem evaluate_add_clock_io_events_mono:
   ∀exps s extra.
    (SND(evaluate(exps,s))).ffi.io_events ≼
    (SND(evaluate(exps,s with clock := s.clock + extra))).ffi.io_events
Proof
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def,LET_THM] >>
  TRY (
    rename1`find_code` >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >>
    imp_res_tac pop_env_const >> full_simp_tac(srw_ss())[] >>
    fsrw_tac[ARITH_ss][dec_clock_def,call_env_with_const,push_env_with_const] >>
    imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    fsrw_tac[ARITH_ss][call_env_with_const] >>
    rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[set_var_with_const] >>
    metis_tac[evaluate_io_events_mono,SND,PAIR,IS_PREFIX_TRANS,
              set_var_const,set_var_with_const,with_clock_ffi]) >>
  rpt (pairarg_tac >> full_simp_tac(srw_ss())[]) >>
  every_case_tac >> full_simp_tac(srw_ss())[cut_state_opt_with_const] >> rev_full_simp_tac(srw_ss())[] >>
  rveq >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
  fs [do_app_with_clock] >>
  TRY (PairCases_on `y`) >> fs [] >>
  imp_res_tac jump_exc_IMP >> full_simp_tac(srw_ss())[jump_exc_NONE] >>
  rveq >> full_simp_tac(srw_ss())[state_component_equality] >>
  imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >>
  rveq >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_io_events_mono >> rev_full_simp_tac(srw_ss())[] >>
  fs [] >> imp_res_tac jump_exc_IMP >> rw[jump_exc_NONE] >>
  metis_tac[evaluate_io_events_mono,IS_PREFIX_TRANS,SND,PAIR]
QED

Theorem semantics_Div_IMP_LPREFIX:
   semantics ffi prog co cc start = Diverge l ==> LPREFIX (fromList ffi.io_events) l
Proof
  simp[semantics_def]
  \\ IF_CASES_TAC \\ fs[]
  \\ DEEP_INTRO_TAC some_intro \\ fs[]
  \\ rw[]
  \\ qmatch_abbrev_tac`LPREFIX l1 (build_lprefix_lub l2)`
  \\ `l1 ∈ l2 ∧ lprefix_chain l2` suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_def]
  \\ conj_tac
  >- (
    unabbrev_all_tac >> simp[]
    \\ qexists_tac`0`>>fs[evaluate_def]
    \\ CASE_TAC >> fs[]
    \\ CASE_TAC >> fs[]
    \\ CASE_TAC >> fs[] )
  \\ simp[Abbr`l2`]
  \\ simp[Once(GSYM o_DEF),IMAGE_COMPOSE]
  \\ match_mp_tac prefix_chain_lprefix_chain
  \\ simp[prefix_chain_def,PULL_EXISTS]
  \\ qx_genl_tac[`k1`,`k2`]
  \\ qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES
  \\ simp[LESS_EQ_EXISTS]
  \\ metis_tac[evaluate_add_clock_io_events_mono,
               initial_state_simp,initial_state_with_simp]
QED

Theorem semantics_Term_IMP_PREFIX:
   semantics ffi prog co cc start = Terminate tt l ==> ffi.io_events ≼ l
Proof
  simp[semantics_def] \\ IF_CASES_TAC \\ fs[]
  \\ DEEP_INTRO_TAC some_intro \\ fs[] \\ rw[]
  \\ imp_res_tac evaluate_io_events_mono \\ fs[]
QED

Theorem Resource_limit_hit_implements_semantics:
   implements {Terminate Resource_limit_hit ffi.io_events}
       {semantics ffi (fromAList prog) co cc start}
Proof
  fs [implements_def,extend_with_resource_limit_def]
  \\ Cases_on `semantics ffi (fromAList prog) co cc start` \\ fs []
  \\ imp_res_tac semantics_Div_IMP_LPREFIX \\ fs []
  \\ imp_res_tac semantics_Term_IMP_PREFIX \\ fs []
QED

val get_code_labels_def = Define`
  (get_code_labels (Call r d a h) =
    (case d of SOME x => {x} | _ => {}) ∪
    (case h of SOME (n,p) => get_code_labels p | _ => {})) ∧
  (get_code_labels (Seq p1 p2) = get_code_labels p1 ∪ get_code_labels p2) ∧
  (get_code_labels (If _ p1 p2) = get_code_labels p1 ∪ get_code_labels p2) ∧
  (get_code_labels (Assign _ op _ _) = closLang$assign_get_code_label op) ∧
  (get_code_labels _ = {})`;
val _ = export_rewrites["get_code_labels_def"];

val good_code_labels_def = Define`
  good_code_labels p ⇔
    (BIGUNION (set (MAP (λ(n,m,pp). (get_code_labels pp)) p))) ⊆
    (set (MAP FST p))`

Theorem get_code_labels_mk_ticks:
   ∀n m. get_code_labels (mk_ticks n m) ⊆ get_code_labels m
Proof
   Induct
   \\ rw[dataLangTheory.mk_ticks_def] \\ rw[FUNPOW]
   \\ fs[dataLangTheory.mk_ticks_def]
   \\ first_x_assum (qspec_then`Seq Tick m`mp_tac)
   \\ rw[]
QED

val _ = export_theory();
