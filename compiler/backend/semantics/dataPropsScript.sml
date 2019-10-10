(*
  Properties about dataLang and its semantics
*)
open preamble dataLangTheory dataSemTheory semanticsPropsTheory;

val _ = new_theory"dataProps";

val s = ``s:('c,'ffi) dataSem$state``

Theorem initial_state_simp[simp]:
  (initial_state f c co cc ts hl ls k).clock = k ∧
  (initial_state f c co cc ts hl ls k).locals = LN ∧
  (initial_state f c co cc ts hl ls k).code = c ∧
  (initial_state f c co cc ts hl ls k).ffi = f ∧
  (initial_state f c co cc ts hl ls k).compile_oracle = co ∧
  (initial_state f c co cc ts hl ls k).compile = cc ∧
  (initial_state f c co cc ts hl ls k).stack = [] ∧
  (initial_state f c co cc ts hl ls k).peak_heap_length = 0
Proof
  srw_tac[][initial_state_def]
QED

Theorem initial_state_with_simp[simp]:
   (initial_state f c co cc ts hl ls k with clock := k' = initial_state f c co cc ts hl ls k') ∧
   (initial_state f c co cc ts hl ls k with stack := [] = initial_state f c co cc ts hl ls k) ∧
   (initial_state f c co cc ts hl ls k with locals := LN = initial_state f c co cc ts hl ls k)
Proof
  srw_tac[][initial_state_def]
QED

Theorem lim_safe_eq[simp]:
  lim_safe (s with locals := x0)            op xs = lim_safe s op xs
∧ lim_safe (s with stack := x1)             op xs = lim_safe s op xs
∧ lim_safe (s with global := x2)            op xs = lim_safe s op xs
∧ lim_safe (s with handler := x3)           op xs = lim_safe s op xs
∧ lim_safe (s with refs := x4)              op xs = lim_safe s op xs
∧ lim_safe (s with compile := x5)           op xs = lim_safe s op xs
∧ lim_safe (s with clock := x6)             op xs = lim_safe s op xs
∧ lim_safe (s with code := x7)              op xs = lim_safe s op xs
∧ lim_safe (s with ffi := x8)               op xs = lim_safe s op xs
∧ lim_safe (s with space := x9)             op xs = lim_safe s op xs
∧ lim_safe (s with tstamps := x10)          op xs = lim_safe s op xs
∧ lim_safe (s with safe_for_space := x11)   op xs = lim_safe s op xs
∧ lim_safe (s with peak_heap_length := x12) op xs = lim_safe s op xs
∧ lim_safe (s with compile_oracle := x13)   op xs = lim_safe s op xs
Proof
  MAP_EVERY (fn t => Q.SPEC_TAC (t,t)) [`xs`,`op`,`s`]
  \\ ho_match_mp_tac lim_safe_ind \\ rw []
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

(* INFO: only used in bvi_to_dataProof *)
Theorem consume_space_add_space:
  ∃sf hp. consume_space k (add_space t k with locals := env1) =
          SOME (t with <| locals := env1 ; space := 0
                        ; safe_for_space := sf
                        ; peak_heap_length := hp |>)
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
   map_result (λ(x,y). (x,y with <| stack := z
                                  ; safe_for_space   := do_app_safe op vs (s with stack := z)
                                  ; peak_heap_length := do_app_peak op vs (s with stack := z) |>))
              I (do_app op vs s)`,
  Cases_on `do_app op vs (s with stack := z)`
  \\ Cases_on `op`
  \\ ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_space_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,do_install_def,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def,op_space_reset_def,check_lim_def] >>
          TRY (pairarg_tac \\ fs []) >>
          rveq >> fs []) >> rw [state_component_equality]);

Theorem do_app_aux_with_space:
  do_app_aux op vs (s with space := z) = map_result (λ(x,y). (x,y with space := z)) I (do_app_aux op vs s)
Proof
  Cases_on `do_app_aux op vs (s with space := z)`
  \\ Cases_on `op`
  \\ ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_space_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,do_install_def,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def,check_lim_def] >>
          TRY (pairarg_tac \\ fs []) >>
          rveq >> fs [] \\ rw [])
QED

Theorem do_app_aux_with_locals:
  do_app_aux op vs (s with locals := z) = map_result (λ(x,y). (x,y with locals := z)) I (do_app_aux op vs s)
Proof
  Cases_on `do_app_aux op vs (s with locals := z)`
  \\ Cases_on `op`
  \\ ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_space_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,do_install_def,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def,check_lim_def] >>
          TRY (pairarg_tac \\ fs []) >>
          rveq >> fs [] >> rw [])
QED

val do_app_with_locals = time Q.prove(
  `do_app op vs (s with locals := z) =
   map_result (λ(x,y). (x,y with <| locals := z
                                  ; safe_for_space   := do_app_safe op vs (s with locals := z)
                                  ; peak_heap_length := do_app_peak op vs (s with locals := z)|>))
                       I (do_app op vs s)`,
  Cases_on `do_app op vs (s with locals := z)`
  \\ Cases_on `op`
  \\ ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_space_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,do_install_def,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def,check_lim_def] >>
          TRY (pairarg_tac \\ fs []) >>
          rveq >> fs []) >> rw [state_component_equality]);

Theorem do_app_aux_err:
   do_app_aux op vs s = Rerr e ⇒ (e = Rabort Rtype_error)
                             \/
                             (?i x. op = FFI i /\ e = Rabort (Rffi_error x))
Proof
  rw [ do_app_aux_def,case_eq_thms
     , do_install_def,do_space_def,with_fresh_ts_def
     , PULL_EXISTS, UNCURRY,consume_space_def]
  \\ fs []
QED

Theorem do_app_aux_const:
    do_app_aux op vs x = Rval (y,z) ⇒
    z.stack = x.stack ∧ z.handler = x.handler ∧ z.locals = x.locals ∧
    z.clock = x.clock ∧ z.compile = x.compile
Proof
  rw [ do_app_aux_def,case_eq_thms
     , do_install_def,do_space_def,with_fresh_ts_def
     , PULL_EXISTS, UNCURRY,consume_space_def, check_lim_def]
  \\ fs []
QED

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
     , PULL_EXISTS, UNCURRY,consume_space_def, check_lim_def]
  \\ fs []
QED

Theorem do_app_locals:
   (do_app op x s = Rval (q,r)) ==>
   (do_app op x (s with locals := extra) =
         Rval (q,r with <| locals := extra
                         ; safe_for_space   := do_app_safe op x (s with locals := extra)
                         ; peak_heap_length := do_app_peak op x (s with locals := extra)|>))
Proof
   rw [ do_app_def,do_app_aux_def,case_eq_thms
      , do_install_def,do_space_def,with_fresh_ts_def
      , PULL_EXISTS, UNCURRY,consume_space_def, check_lim_def]
   \\ fs [] >> rw [state_component_equality]
QED

Theorem do_space_alt:
  do_space op l s =
      if op_space_reset op
      then SOME (s with <| space := 0
                         ; safe_for_space   := do_space_safe op l s
                         ; peak_heap_length := do_space_peak op l s |>)
      else consume_space (op_space_req op l) s
Proof
  full_simp_tac(srw_ss())[do_space_def] \\ SRW_TAC [] [consume_space_def]
  \\ full_simp_tac(srw_ss())[state_component_equality] \\ fs[] \\ DECIDE_TAC
QED

Theorem Seq_Skip:
  evaluate (Seq c Skip,s) = evaluate (c,s)
Proof
  full_simp_tac(srw_ss())[evaluate_def]
  \\ Cases_on `evaluate (c,s)` \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] []
QED

Theorem evaluate_safe_alt:
  !c s. evaluate_safe c s = (SND (evaluate(c,s))).safe_for_space
Proof
  rw [evaluate_safe_def,SND]
  \\ Cases_on `evaluate(c,s)`
  \\ rw []
QED

Theorem evaluate_peak_alt:
  !c s. evaluate_peak c s = (SND (evaluate(c,s))).peak_heap_length
Proof
  rw [evaluate_peak_def,SND]
  \\ Cases_on `evaluate(c,s)`
  \\ rw []
QED

Theorem size_of_heap_with_safe:
  ∀s safe. size_of_heap (s with safe_for_space := safe) = size_of_heap s
Proof
  EVAL_TAC \\ rw []
QED

Theorem do_app_safe_peak_swap_aux[local]:
  ∀op vs s q s' safe peak.
   do_app op vs s = Rval (q,s')
     ⇒ let s0 = s with <| safe_for_space := safe; peak_heap_length := peak |>
       in  do_app op vs s0 = Rval (q,s' with <| safe_for_space := do_app_safe op vs s0;
                                                peak_heap_length := do_app_peak op vs s0 |> )
Proof
  Cases \\ rw [do_app_def
              , do_install_def
              , do_app_aux_def
              , with_fresh_ts_def
              , do_space_def
              , op_space_reset_def
              , data_spaceTheory.op_space_req_def
              , consume_space_def
              , size_of_heap_with_safe
              , MAX_DEF
              , check_lim_def]
  \\ TRY (pairarg_tac \\ fs [])
  \\ fs [list_case_eq,option_case_eq,v_case_eq,bool_case_eq,closSemTheory.ref_case_eq
        , ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq, state_component_equality
        , semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,pair_case_eq]
  \\ fs  [data_spaceTheory.op_space_req_def]
  \\ rfs [data_spaceTheory.op_space_req_def]
QED

Theorem do_app_safe_peak_swap = do_app_safe_peak_swap_aux |> SIMP_RULE std_ss [LET_DEF]

Theorem do_app_aux_safe_peak_swap:
  ∀op vs s q s' safe peak. do_app_aux op vs s = Rval (q,s')
    ⇒ ∃safe' peak'.
        do_app_aux op vs (s with <| safe_for_space := safe; peak_heap_length := peak |>) =
        Rval (q,s' with <| safe_for_space := safe'; peak_heap_length := peak' |>)
Proof
  Cases \\ rw [ do_app_aux_def
               , with_fresh_ts_def
               , do_space_def
               , data_spaceTheory.op_space_req_def
               , consume_space_def
               , size_of_heap_with_safe
               , MAX_DEF
               , check_lim_def ]
  \\ TRY (pairarg_tac \\ fs [])
  \\ fs [list_case_eq,option_case_eq,v_case_eq,bool_case_eq,closSemTheory.ref_case_eq
        , ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq, state_component_equality
        , semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,pair_case_eq]
  \\ fs  [data_spaceTheory.op_space_req_def]
  \\ rfs [data_spaceTheory.op_space_req_def]
QED

Theorem do_app_err_safe_peak_swap:
  ∀op vs s e safe peak. do_app op vs s = Rerr e
    ⇒ do_app op vs (s with <| safe_for_space := safe; peak_heap_length := peak |>) =
      Rerr e
Proof
  Cases \\ rw [do_app_def
              , do_install_def
              , do_app_aux_def
              , with_fresh_ts_def
              , do_space_def
              , op_space_reset_def
              , data_spaceTheory.op_space_req_def
              , size_of_heap_with_safe
              , MAX_DEF
              , consume_space_def
              , check_lim_def]
  \\ TRY (pairarg_tac \\ fs [])
  \\ fs [list_case_eq,option_case_eq,v_case_eq,bool_case_eq,closSemTheory.ref_case_eq
        , ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq, state_component_equality
        , semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,pair_case_eq]
  \\ fs  [data_spaceTheory.op_space_req_def]
  \\ rfs [data_spaceTheory.op_space_req_def]
QED

Theorem evaluate_safe_peak_swap_aux[local]:
  ∀c s r s' safe peak.
   evaluate (c,s) = (r,s') ⇒
     let s0 = s with <| safe_for_space := safe; peak_heap_length := peak |>
     in evaluate (c,s0) =
         (r,s' with <| safe_for_space := evaluate_safe c s0;
                       peak_heap_length := evaluate_peak c s0 |>)
Proof
  let val full_fs = fs[ get_var_def, set_var_def
                      , cut_state_opt_def
                      , cut_state_def
                      , get_vars_def
                      , do_install_def
                      , op_space_reset_def
                      , call_env_def
                      , dec_clock_def
                      , add_space_def
                      , jump_exc_def
                      , MAX_DEF
                      , size_of_heap_with_safe
                      , op_requires_names_def];
      val full_cases = fs [ list_case_eq,option_case_eq
                          , v_case_eq
                          , bool_case_eq
                          , closSemTheory.ref_case_eq
                          , ffiTheory.ffi_result_case_eq
                          , ffiTheory.oracle_result_case_eq
                          , semanticPrimitivesTheory.eq_result_case_eq
                          , astTheory.word_size_case_eq
                          , pair_case_eq];
      val basic_tac = fs [evaluate_safe_alt,evaluate_def
                         ,evaluate_peak_alt]
                      \\ rpt (every_case_tac
                      \\ full_fs
                      \\ fs [state_component_equality]);
   in recInduct evaluate_ind \\ REPEAT STRIP_TAC
      >- basic_tac
      >- basic_tac
      >- (fs [evaluate_def]
         \\ full_cases >> full_fs
         \\ fs [evaluate_safe_alt,evaluate_peak_alt,evaluate_def]
         \\ full_cases >> full_fs
         \\ fs [] \\ rfs[]
         \\ rveq \\ fs []
         \\ every_case_tac
         \\ TRY (first_assum (mp_then Any (qspecl_then [`safe`,`peak`] assume_tac) do_app_safe_peak_swap))
         \\ TRY (first_assum (mp_then Any (qspecl_then [`safe`,`peak`] assume_tac) do_app_err_safe_peak_swap))
         \\ rfs [] \\ rveq \\ fs [])
      >- basic_tac
      >- basic_tac
      >- basic_tac
      >- basic_tac
      >- (fs[evaluate_def] (* Seq *)
         \\ Cases_on `evaluate (c1,s)` \\ fs[]
         \\ every_case_tac
         \\ fs [evaluate_safe_alt,evaluate_peak_alt,evaluate_def]
         \\ qpat_x_assum `∀safe peak. evaluate (c1,_) = _` (qspecl_then [`safe`,`peak`] assume_tac)
         \\ ONCE_ASM_REWRITE_TAC [] \\  rw [])
      >- basic_tac
      >- (fs [evaluate_def]
         \\ full_cases >> full_fs
         \\ fs [evaluate_safe_alt,evaluate_peak_alt,evaluate_def]
         \\ full_cases >> full_fs
         \\ fs [] \\ rfs[]
         \\ rveq \\ fs []
         \\ first_x_assum (qspecl_then [`safe`,`peak`] assume_tac)
         \\ ONCE_ASM_REWRITE_TAC []
         \\ rw []
         >- (Q.EXISTS_TAC `NONE`
            \\ qmatch_asmsub_abbrev_tac `evaluate s_foo = (_,s')`
            \\ qmatch_asmsub_abbrev_tac `evaluate (prog,s_bar) = (NONE, s'_bar)`
            \\ Q.EXISTS_TAC `s'_bar`
            \\ qmatch_goalsub_abbrev_tac `evaluate (prog,bar_s)`
            \\ `bar_s = s_bar`
                  by (UNABBREV_ALL_TAC \\ Cases_on `handler` \\ fs[push_env_def])
            \\ rw [Abbr`s'_bar`]
            \\ ONCE_ASM_REWRITE_TAC []
            \\ rw [])
         \\ Q.EXISTS_TAC `SOME v6` \\ fs []
         \\ qpat_x_assum `evaluate _ = (_,s2)` (K ALL_TAC)
         \\ qmatch_asmsub_abbrev_tac `evaluate (prog,s_bar) = (SOME v6, s'_bar)`
         \\ Q.EXISTS_TAC `s'_bar`
         \\ qmatch_goalsub_abbrev_tac `evaluate (prog,bar_s)`
         \\ `bar_s = s_bar`
               by (UNABBREV_ALL_TAC \\ Cases_on `handler` \\ fs[push_env_def])
         \\ rw [Abbr`s'_bar`]
         \\ Cases_on `v6`
         >- (fs [pop_env_def]
            \\ Cases_on `s2.stack` \\ fs []
            \\ ONCE_ASM_REWRITE_TAC [] \\ rw []
            \\ Cases_on `h` \\ fs []
            \\ ONCE_ASM_REWRITE_TAC [] \\ rw [])
         \\ Cases_on `e` \\ fs [] \\ Cases_on `handler` \\ fs []
         \\ ONCE_ASM_REWRITE_TAC [] \\ rw []
         \\ full_cases \\ fs [])
  end
QED

Theorem evaluate_safe_peak_swap =  evaluate_safe_peak_swap_aux |> SIMP_RULE std_ss [LET_DEF]

Theorem evaluate_stack_swap:
  !c ^s.
     let sfs = (λxs. evaluate_safe c (s with stack := xs));
         phl = (λxs. evaluate_peak c (s with stack := xs))
     in case evaluate (c,s) of
          | (SOME (Rerr(Rabort Rtype_error)),s1) => T
          | (SOME (Rerr(Rabort a)),s1) => (s1.stack = [])
              /\ (!xs. (LENGTH s.stack = LENGTH xs) ==>
                       evaluate (c,s with stack := xs) =
                         (SOME (Rerr(Rabort a)),s1 with <| safe_for_space := sfs xs ;
                                                           peak_heap_length := phl xs |>))
          | (SOME (Rerr (Rraise t)),s1) =>
                (?s2. (jump_exc s = SOME s2) /\ (s2.locals = s1.locals) /\
                      (s2.stack = s1.stack) /\ (s2.handler = s1.handler) /\
                      (!xs s7. (jump_exc (s with stack := xs) = SOME s7) /\
                               (LENGTH s.stack = LENGTH xs) ==>
                               (evaluate (c,s with stack := xs) =
                                  (SOME (Rerr (Rraise t)),
                                   s1 with <| stack := s7.stack ;
                                              handler := s7.handler ;
                                              locals := s7.locals ;
                                              safe_for_space := sfs xs ;
                                              peak_heap_length := phl xs |>))))
          | (res,s1) => (s1.stack = s.stack) /\ (s1.handler = s.handler) /\
                        (!xs. (LENGTH s.stack = LENGTH xs) ==>
                                evaluate (c,s with stack := xs) =
                                  (res, s1 with <| stack := xs ;
                                                   safe_for_space := sfs xs ;
                                                   peak_heap_length := phl xs|>))
Proof
  fs [LET_DEF] \\ recInduct evaluate_ind \\ REPEAT STRIP_TAC
  >- fs[evaluate_def,state_component_equality
       ,evaluate_safe_def,evaluate_peak_def]
  >- (fs[evaluate_def] >> EVAL_TAC
      \\ every_case_tac
      \\ fs[state_component_equality,evaluate_safe_def,evaluate_peak_def])
  >- (fs[evaluate_def,evaluate_safe_def,evaluate_peak_def]
     \\ every_case_tac
     \\ fs[set_var_def,cut_state_opt_with_const,do_app_with_stack]
     \\ imp_res_tac do_app_err >> fs[] >> rpt var_eq_tac
     \\ fs[cut_state_opt_def,cut_state_def] >> every_case_tac >> fs[]
     \\ rpt var_eq_tac >> fs[do_app_with_locals]
     \\ TRY(first_assum(split_uncurry_arg_tac o rhs o concl) >> fs[])
     \\ imp_res_tac do_app_const >> simp[]
     \\ EVAL_TAC >> simp[state_component_equality])
  >- (fs[evaluate_def,evaluate_safe_def,evaluate_peak_def]
     \\ EVAL_TAC
     \\ every_case_tac >> fs[state_component_equality])
  >- (fs[evaluate_def,evaluate_safe_def,evaluate_peak_def]
     \\ every_case_tac >> fs[state_component_equality,add_space_def])
  >- (fs[evaluate_def,evaluate_safe_def,evaluate_peak_def]
     \\ EVAL_TAC
     \\ every_case_tac >> fs[]
     \\ rpt gen_tac
     \\ every_case_tac >> fs[]
     \\ srw_tac[][] >> simp[state_component_equality])
  >- (fs[evaluate_def,evaluate_safe_def,evaluate_peak_def]
     \\ EVAL_TAC
     \\ every_case_tac >> fs[state_component_equality])
  >- (fs[evaluate_def,LET_DEF] (* Seq *)
     \\ Cases_on `evaluate (c1,s)` \\ fs[LET_DEF]
     \\ Cases_on `evaluate (c2,r)` \\ fs[LET_DEF]
     \\ Cases_on `q = NONE` \\ fs[] \\ Cases_on `q'` \\ fs[]
     \\ TRY (Cases_on `x`) \\ TRY (Cases_on`e`) \\ fs[jump_exc_def]
     \\ every_case_tac \\ fs[] \\ SRW_TAC [] [] \\ fs[]
     \\ every_case_tac \\ fs[]
     \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
     \\ Q.PAT_X_ASSUM `!xs. bbb` (MP_TAC o Q.SPEC `xs`) \\ fs[]
     \\ TRY (Q.PAT_X_ASSUM `!xs. bbb` (MP_TAC o Q.SPEC `xs`) \\ fs[])
     \\ rw []
     \\ ONCE_ASM_REWRITE_TAC [evaluate_safe_def, evaluate_def,evaluate_peak_def]
     \\ ONCE_ASM_REWRITE_TAC [evaluate_safe_def, evaluate_def,evaluate_peak_def]
     \\ fs [] \\ pairarg_tac
     \\ rw [state_component_equality]
     \\ IMP_RES_TAC evaluate_safe_peak_swap
     \\ fs [state_component_equality])
  >- (fs[evaluate_def,evaluate_safe_def,evaluate_peak_def] (* If *)
     \\ Cases_on `evaluate (c1,s)` \\ fs[LET_DEF]
     \\ Cases_on `evaluate (c2,s)` \\ fs[LET_DEF]
     \\ Cases_on `get_var n s.locals` \\ fs[]
     \\ Cases_on `isBool T x` \\ fs[get_var_def]
     \\ Cases_on `isBool F x` \\ fs[get_var_def])
  >- (fs[evaluate_def,evaluate_safe_alt,evaluate_peak_alt] (* Call *)
     \\ Cases_on `get_vars args s.locals` \\ fs[]
     \\ Cases_on `find_code dest x s.code` \\ fs[]
     \\ TRY (fs[call_env_def] \\ NO_TAC)
     \\ Cases_on `x'` \\ fs[]
     \\ Cases_on `ret` \\ fs[]
     >- (every_case_tac \\ fs[]
        \\ fs[call_env_def,dec_clock_def,jump_exc_def]
        \\ every_case_tac \\ fs[]
        \\ SRW_TAC [] [] \\ fs[]
        \\ Q.PAT_X_ASSUM `xxx = SOME s7` MP_TAC
        \\ every_case_tac \\ fs[]
        \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
        \\ fs [state_component_equality]
        \\ Q.PAT_X_ASSUM `!xs.bbb` (MP_TAC o Q.SPEC `xs`)
        \\ fs [] \\ rw [state_component_equality])
    \\ fs[]
    \\ Cases_on `x'` \\ fs[]
    \\ Cases_on `cut_env r' s.locals` \\ fs[]
    \\ Cases_on `s.clock = 0` \\ fs[]
    >- (fs[call_env_def,state_component_equality])
    \\ Cases_on `evaluate (r,call_env q (push_env x' (IS_SOME handler) (dec_clock ^s)))` \\ fs[]
    \\ Cases_on `q''` \\ fs []
    \\ Cases_on `x''` \\ fs[]
    >- (Cases_on `handler`
       \\ fs[pop_env_def,call_env_def,push_env_def,set_var_def,dec_clock_def]
       \\ REPEAT STRIP_TAC
       >- (FIRST_X_ASSUM (MP_TAC o Q.SPEC `Env x'::xs`)
          \\ fs [] \\ REPEAT STRIP_TAC
          \\ ONCE_ASM_REWRITE_TAC [] \\ rw [])
       >- (FIRST_X_ASSUM (MP_TAC o Q.SPEC `Exc x' ^s.handler::xs`)
          \\ fs [] \\ REPEAT STRIP_TAC
          \\ ONCE_ASM_REWRITE_TAC [] \\ rw []))
    \\ reverse(Cases_on`e`)\\fs[]
    >- (Cases_on`a` >> fs[]
       \\ srw_tac[][]
       \\ qpat_abbrev_tac`ss = call_env X Y`
       \\ first_x_assum(qspec_then`ss.stack`mp_tac)
       \\ (impl_tac
          >- (simp[Abbr`ss`]
             \\ EVAL_TAC
             \\ Cases_on`handler`>>EVAL_TAC
             \\ simp[]))
       \\ qpat_abbrev_tac`st:('c,'ffi) dataSem$state = X Y`
       \\ `st = ss` by (simp[Abbr`ss`,Abbr`st`,dataSemTheory.state_component_equality]
           \\ EVAL_TAC
           \\ Cases_on`handler`>> EVAL_TAC
           \\ simp[])
       \\ rw []
       \\ ONCE_ASM_REWRITE_TAC []
       \\ rw [])
    \\ Cases_on `handler` \\ fs[]
    >- (fs[pop_env_def,call_env_def,push_env_def,set_var_def,dec_clock_def]
       \\ fs[jump_exc_def]
       \\ Cases_on `s.handler = LENGTH s.stack` \\ fs[LASTN_LEMMA]
       \\ `s.handler < LENGTH s.stack` by DECIDE_TAC \\ fs[]
       \\ IMP_RES_TAC LASTN_TL \\ fs[]
       \\ Cases_on `LASTN (s.handler + 1) s.stack` \\ fs[]
       \\ Cases_on `h` \\ fs[]
       \\ SRW_TAC [] [] \\ fs[]
       \\ Q.PAT_X_ASSUM `!xs s7.bbb` (MP_TAC o Q.SPECL [`Env x'::xs`,
           `s7 with clock := s7.clock - 1`])
       \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
       \\ fs[] \\ REPEAT STRIP_TAC
       \\ ONCE_ASM_REWRITE_TAC []
       \\ rw []
       \\ IMP_RES_TAC LASTN_TL \\ fs[]
       \\ every_case_tac \\ fs[]
       \\ fs[dataSemTheory.state_component_equality])
    \\ Cases_on `x''` \\ fs[]
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate (r,call_env q (push_env x8 T (dec_clock s))) =
          (SOME (Rerr (Rraise b)),s9)`
    \\ Cases_on `evaluate (r''',set_var q'' b s9)` \\ fs[]
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate (r''',set_var q'' b s9) = (res,r5)`
    \\ Cases_on `res` \\ fs[]
    >- (STRIP_TAC (* NONE *)
       >- (fs[set_var_def,pop_env_def,jump_exc_def,call_env_def
             , push_env_def,LASTN_LEMMA,dec_clock_def]
          \\ SRW_TAC [] [] \\ fs[]
          \\ every_case_tac \\ fs[]
          \\ SRW_TAC [] [] \\ fs[])
      \\ STRIP_TAC
      >- (fs[set_var_def,pop_env_def,jump_exc_def,call_env_def
            , push_env_def,LASTN_LEMMA,dec_clock_def]
         \\ SRW_TAC [] [] \\ fs [])
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock (^s with stack := xs)))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock (s with stack := xs)))).stack) =
          (call_env q (push_env x8 T (dec_clock (s with stack := xs))))` by fs[call_env_def,push_env_def,dec_clock_def]
      \\ fs[] \\ fs[call_env_def,push_env_def,jump_exc_def,
           LASTN_LEMMA,dec_clock_def,set_var_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `LENGTH s.stack = LENGTH xs` (ASSUME_TAC o GSYM)
      \\ fs[LASTN_LEMMA] \\ SRW_TAC [] [] \\ fs[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `xs`)
      \\ SRW_TAC [] [] \\ fs[] \\ REV_FULL_SIMP_TAC std_ss []
      \\ ONCE_ASM_REWRITE_TAC [] \\ rw []
      \\ qpat_abbrev_tac `ss = (SND (evaluate _)).safe_for_space`
      \\ qpat_abbrev_tac `ph = (SND (evaluate _)).peak_heap_length`
      \\ qhdtm_x_assum `Abbrev` kall_tac
      \\ qhdtm_x_assum `Abbrev` kall_tac
      \\ drule evaluate_safe_peak_swap
      \\ STRIP_TAC
      \\ Q.PAT_X_ASSUM `∀safe peak. bb` (qspecl_then [`ss`,`ph`] assume_tac)
      \\ qmatch_goalsub_abbrev_tac `(r'³',s9_f)`
      \\ qmatch_asmsub_abbrev_tac `(r'³',s9_g)`
      \\ `s9_f = s9_g` by (UNABBREV_ALL_TAC \\ rw [state_component_equality])
      \\ rw [])
    \\ Cases_on `x'` \\ fs[]
    >- (STRIP_TAC (* SOME Rval *)
       >- (fs[set_var_def,pop_env_def,jump_exc_def,call_env_def
             , push_env_def,LASTN_LEMMA,dec_clock_def]
          \\ SRW_TAC [] [] \\ fs[]
          \\ every_case_tac \\ fs[]
          \\ SRW_TAC [] [] \\ fs[])
      \\ STRIP_TAC
      >- (fs[set_var_def,pop_env_def,jump_exc_def,call_env_def
            , push_env_def,LASTN_LEMMA,dec_clock_def]
         \\ SRW_TAC [] [] \\ fs[])
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock (^s with stack := xs)))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock (s with stack := xs)))).stack) =
          (call_env q (push_env x8 T (dec_clock (s with stack := xs))))` by fs[call_env_def,push_env_def,dec_clock_def]
      \\ fs[] \\ fs[call_env_def,push_env_def,jump_exc_def,
           LASTN_LEMMA,dec_clock_def,set_var_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `LENGTH s.stack = LENGTH xs` (ASSUME_TAC o GSYM)
      \\ fs[LASTN_LEMMA] \\ SRW_TAC [] [] \\ fs[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `xs`)
      \\ SRW_TAC [] [] \\ fs[] \\ REV_FULL_SIMP_TAC std_ss []
      \\ ONCE_ASM_REWRITE_TAC [] \\ rw []
      \\ qpat_abbrev_tac `ss = (SND (evaluate _)).safe_for_space`
      \\ qpat_abbrev_tac `ph = (SND (evaluate _)).peak_heap_length`
      \\ qhdtm_x_assum `Abbrev` kall_tac
      \\ qhdtm_x_assum `Abbrev` kall_tac
      \\ drule evaluate_safe_peak_swap
      \\ STRIP_TAC
      \\ Q.PAT_X_ASSUM `∀safe. bb` (qspecl_then [`ss`,`ph`] assume_tac)
      \\ qmatch_goalsub_abbrev_tac `(r'³',s9_f)`
      \\ qmatch_asmsub_abbrev_tac `(r'³',s9_g)`
      \\ `s9_f = s9_g` by (UNABBREV_ALL_TAC \\ rw [state_component_equality])
      \\ rw [])
    \\ Cases_on`e` \\ fs[]  (* Rraise *)
    >- (FIRST_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock ^s))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock s))).stack) =
          (call_env q (push_env x8 T (dec_clock s)))` by fs[call_env_def,push_env_def,dec_clock_def]
      \\ POP_ASSUM (fn th => SIMP_TAC std_ss [th])
      \\ SIMP_TAC std_ss [Once dec_clock_def]
      \\ SIMP_TAC std_ss [Once push_env_def]
      \\ SIMP_TAC std_ss [Once call_env_def]
      \\ SIMP_TAC std_ss [Once jump_exc_def]
      \\ SIMP_TAC (srw_ss()) [LASTN_LEMMA] \\ REPEAT STRIP_TAC
      \\ fs[dataSemTheory.state_component_equality]
      \\ Q.PAT_X_ASSUM `jump_exc (set_var q'' b s9) = SOME s2'` MP_TAC
      \\ SIMP_TAC std_ss [Once set_var_def]
      \\ SIMP_TAC (srw_ss()) [Once jump_exc_def]
      \\ Cases_on `LASTN (s9.handler + 1) s9.stack` \\ fs[]
      \\ Cases_on `h` \\ fs[] \\ SIMP_TAC std_ss [Once EQ_SYM_EQ]
      \\ REPEAT STRIP_TAC \\ fs[] \\ POP_ASSUM (K ALL_TAC)
      \\ rfs[dataSemTheory.state_component_equality]
      \\ SIMP_TAC std_ss [Once jump_exc_def] \\ fs[]
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock (^s with stack := xs)))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock (s with stack := xs)))).stack) =
          (call_env q (push_env x8 T (dec_clock (s with stack := xs))))`
          by fs[call_env_def,push_env_def,dec_clock_def]
      \\ fs[] \\ fs[call_env_def,push_env_def,jump_exc_def,
           LASTN_LEMMA,dec_clock_def,set_var_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `LENGTH _.stack = LENGTH xs` (ASSUME_TAC o GSYM)
      \\ fs[LASTN_LEMMA] \\ SRW_TAC [] [] \\ fs[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `xs`)
      \\ SRW_TAC [] [] \\ fs[] \\ REV_FULL_SIMP_TAC std_ss []
      \\ ONCE_ASM_REWRITE_TAC [] \\ rw []
      \\ Cases_on `LASTN (s9.handler + 1) xs` \\ rfs [] \\ fs[]
      \\ Cases_on `h` \\ rfs [] \\ fs[]
      \\ qpat_abbrev_tac `sf = (SND (evaluate (r,_))).safe_for_space`
      \\ qpat_abbrev_tac `ph = (SND (evaluate (r,_))).peak_heap_length`
      \\ `s9 with <|locals := insert q'' b s9.locals;
                    stack := xs;
                    handler := s.handler;
                    safe_for_space := sf;
                    peak_heap_length := ph|> =
          s9 with <|locals := insert q'' b s9.locals;
                    stack := xs;
                    safe_for_space := sf;
                    peak_heap_length := ph|>`
         by (fs[dataSemTheory.state_component_equality]) \\ fs[]
      \\ drule evaluate_safe_peak_swap
      \\ STRIP_TAC
      \\ Q.PAT_X_ASSUM `∀safe peak. bb` (qspecl_then [`sf`,`ph`] assume_tac)
      \\ qmatch_goalsub_abbrev_tac `(r'³',s9_f)`
      \\ qmatch_asmsub_abbrev_tac `(r'³',s9_g)`
      \\ `s9_f = s9_g` by (UNABBREV_ALL_TAC \\ rw [state_component_equality])
      \\ rw [])
    \\ Cases_on`a` \\ fs[]
    THEN (* Rtimeout_error *)
     (REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `(call_env q (push_env x8 T
           (dec_clock (^s with stack := xs)))).stack`)
      \\ `(call_env q (push_env x8 T (dec_clock s)) with stack :=
            (call_env q (push_env x8 T (dec_clock (s with stack := xs)))).stack) =
          (call_env q (push_env x8 T (dec_clock (s with stack := xs))))` by fs[call_env_def,push_env_def,dec_clock_def]
      \\ fs[] \\ fs[call_env_def,push_env_def,jump_exc_def,
           LASTN_LEMMA,dec_clock_def,set_var_def] \\ REPEAT STRIP_TAC
      \\ Q.PAT_X_ASSUM `LENGTH s.stack = LENGTH xs` (ASSUME_TAC o GSYM)
      \\ fs[LASTN_LEMMA] \\ SRW_TAC [] [] \\ fs[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `xs`)
      \\ SRW_TAC [] [] \\ fs[] \\ REV_FULL_SIMP_TAC std_ss []
      \\ ONCE_ASM_REWRITE_TAC [] \\ rw []
      \\ qpat_abbrev_tac `ss = (SND (evaluate _)).safe_for_space`
      \\ qpat_abbrev_tac `ph = (SND (evaluate _)).peak_heap_length`
      \\ qhdtm_x_assum `Abbrev` kall_tac
      \\ qhdtm_x_assum `Abbrev` kall_tac
      \\ drule evaluate_safe_peak_swap
      \\ STRIP_TAC
      \\ Q.PAT_X_ASSUM `∀safe. bb` (qspecl_then [`ss`,`ph`] assume_tac)
      \\ qmatch_goalsub_abbrev_tac `(r'³',s9_f)`
      \\ qmatch_asmsub_abbrev_tac `(r'³',s9_g)`
      \\ `s9_f = s9_g` by (UNABBREV_ALL_TAC \\ rw [state_component_equality])
      \\ rw []))
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
  \\ every_case_tac \\ fs[LET_DEF]
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

(* INFO: only used in bvi_to_dataProof *)
Theorem evaluate_locals:
  !c s res s2 vars l.
      res <> SOME (Rerr(Rabort Rtype_error)) /\ (evaluate (c,s) = (res,s2)) /\
      locals_ok s.locals l ==>
      ?w safe peak. (evaluate (c, s with locals := l) =
             (res,if res = NONE
                  then (s2 with <| locals := w;
                                   safe_for_space := safe;
                                   peak_heap_length := peak |>)
                  else s2 with <| safe_for_space := safe;
                                  peak_heap_length := peak |>)) /\
          locals_ok s2.locals w
Proof
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[evaluate_def]
  (* Skip *)
  >- (MAP_EVERY Q.EXISTS_TAC [`l`,`s2.safe_for_space`]
     \\ rw [state_component_equality])
  (* Move *)
  >- (Cases_on `get_var src s.locals` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
     \\ IMP_RES_TAC locals_ok_get_var \\ full_simp_tac(srw_ss())[]
     \\ full_simp_tac(srw_ss())[get_var_def,lookup_union,set_var_def,locals_ok_def]
     \\ Q.EXISTS_TAC `insert dest x l`
     \\ Q.EXISTS_TAC `s.safe_for_space`
     \\ fs[lookup_insert,state_component_equality]
     \\ METIS_TAC [])
  (* Assign *)
  >- (Cases_on `names_opt` \\ full_simp_tac(srw_ss())[]
     \\ Cases_on `op_requires_names op` \\ full_simp_tac(srw_ss())[cut_state_opt_def]
     >- (Cases_on `get_vars args s.locals` \\ full_simp_tac(srw_ss())[cut_state_opt_def]
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
     \\ Q.EXISTS_TAC `s2.locals`
     \\ Q.EXISTS_TAC `s2.safe_for_space`
     \\ Q.EXISTS_TAC `s2.peak_heap_length`
     \\ fs[locals_ok_def]
     \\ SRW_TAC [] [state_component_equality])
   (* Tick *)
  >- (Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
     \\ fs[locals_ok_def,call_env_def,EVAL ``fromList []``,lookup_def, dec_clock_def]
     \\ MAP_EVERY (TRY o Q.EXISTS_TAC) [`l`,`s.safe_for_space`,`s.peak_heap_length`]
     \\ rw [state_component_equality])
  (* MakeSpace *)
  >- (Cases_on `cut_env names s.locals` \\ full_simp_tac(srw_ss())[]
     \\ IMP_RES_TAC locals_ok_cut_env
     \\ full_simp_tac(srw_ss())[LET_DEF,add_space_def,state_component_equality,locals_ok_def])
  (* Raise *)
  >- (Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
     \\ `jump_exc (s with locals := l) = jump_exc s`
        by full_simp_tac(srw_ss())[jump_exc_def]
     \\ Cases_on `jump_exc s` \\ full_simp_tac(srw_ss())[]
     \\ `get_var n l = SOME x` by
          full_simp_tac(srw_ss())[locals_ok_def,get_var_def] \\ full_simp_tac(srw_ss())[]
     \\ srw_tac [] [] \\ Q.EXISTS_TAC `s2.locals`
     \\ full_simp_tac(srw_ss())[locals_ok_def,state_component_equality])
  (* Return *)
  >- (Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
     \\ `get_var n l = SOME x` by
          full_simp_tac(srw_ss())[locals_ok_def,get_var_def] \\ full_simp_tac(srw_ss())[]
     \\ srw_tac [] [call_env_def]
     \\ simp[locals_ok_def,lookup_fromList,state_component_equality])
  (* Seq *)
  >- (Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[LET_DEF]
     \\ Cases_on `q = SOME (Rerr(Rabort Rtype_error))` \\ full_simp_tac(srw_ss())[]
     \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ full_simp_tac(srw_ss())[]
     \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
     \\ Cases_on `q` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
     >- (qpat_x_assum `∀l. bb` drule \\ rw []
        \\ drule evaluate_safe_peak_swap \\ rw []
        \\ fs [state_component_equality]
        \\ METIS_TAC [])
     \\ METIS_TAC [])
  (* If *)
  >- (Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[]
     \\ IMP_RES_TAC locals_ok_get_var \\ full_simp_tac(srw_ss())[]
     \\ Cases_on `isBool T x` \\ full_simp_tac(srw_ss())[]
     \\ Cases_on `isBool F x` \\ full_simp_tac(srw_ss())[])
  (* Call *)
  >- (Cases_on `get_vars args s.locals` \\ full_simp_tac(srw_ss())[]
     \\ IMP_RES_TAC locals_ok_get_vars \\ full_simp_tac(srw_ss())[]
     \\ Cases_on `find_code dest x s.code` \\ full_simp_tac(srw_ss())[]
     \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
     \\ Cases_on `ret` \\ full_simp_tac(srw_ss())[]
     >- (Cases_on `handler` \\ full_simp_tac(srw_ss())[]
         \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
         \\ `call_env q (dec_clock (s with locals := l)) =
             call_env q (dec_clock s)`
            by fs[state_component_equality,dec_clock_def,call_env_def]
         \\ fs[]
         \\ fs[call_env_def,locals_ok_def,lookup_def,fromList_def]
         >- fs [state_component_equality]
         \\ Q.EXISTS_TAC `s2.locals`
         \\ Q.EXISTS_TAC `s2.safe_for_space`
         \\ Q.EXISTS_TAC `s2.peak_heap_length`
         \\ full_simp_tac(srw_ss())[locals_ok_refl]
         \\ SRW_TAC [] [state_component_equality])
     \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
     \\ Cases_on `cut_env r' s.locals` \\ full_simp_tac(srw_ss())[]
     \\ IMP_RES_TAC locals_ok_cut_env \\ full_simp_tac(srw_ss())[]
     \\ `call_env q (push_env x' (IS_SOME handler)
           (dec_clock (s with locals := l))) =
         call_env q (push_env x' (IS_SOME handler)
           (dec_clock s))`
        by (Cases_on `handler`
           \\ fs[state_component_equality,dec_clock_def,call_env_def,push_env_def])
     \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
     \\ full_simp_tac(srw_ss())[call_env_def,locals_ok_def,lookup_def,fromList_def]
     \\ full_simp_tac(srw_ss())[]
     >- rw [state_component_equality]
     \\ MAP_EVERY Q.EXISTS_TAC [`s2.locals`,`s2.safe_for_space`,`s2.peak_heap_length`]
     \\ rw [state_component_equality])
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
  srw_tac[][ mk_ticks_def, FUNPOW] >>
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
    ((FUNPOW dec_clock n t).safe_for_space = t.safe_for_space) /\
    ((FUNPOW dec_clock n t).global = t.global) /\
    ((FUNPOW dec_clock n t).locals = t.locals) /\
    ((FUNPOW dec_clock n t).compile = t.compile) /\
    ((FUNPOW dec_clock n t).compile_oracle = t.compile_oracle) /\
    ((FUNPOW dec_clock n t).peak_heap_length = t.peak_heap_length) /\
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

Theorem size_of_heap_with_clock:
  ∀s z. size_of_heap (s with clock := z) = size_of_heap s
Proof
  EVAL_TAC \\ rw []
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
              pair_case_eq,consume_space_def,size_of_heap_with_clock,check_lim_def] >>
          rveq >> fs [] >> rw [])
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
              pair_case_eq,consume_space_def,size_of_heap_with_clock,check_lim_def] >>
          rveq >> fs [] >> rw [])
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
              pair_case_eq,consume_space_def,check_lim_def] >>
          rveq >> fs [] >> rw [])
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
  ∀exps s1 res s2.
    evaluate (exps,s1) = (res, s2) ∧
    res ≠ SOME(Rerr(Rabort Rtimeout_error))
    ⇒
    ∀ck. evaluate (exps,s1 with clock := s1.clock + ck) = (res, s2 with clock := s2.clock + ck)
Proof
  recInduct evaluate_ind >> srw_tac[][evaluate_def]
  >- (every_case_tac
     \\ fs[get_var_def,set_var_def]
     \\ srw_tac[][] >> fs[])
  >- (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,cut_state_opt_def,cut_state_def
         , bool_case_eq,ffiTheory.call_FFI_def,semanticPrimitivesTheory.result_case_eq
         , with_fresh_ts_def,closSemTheory.ref_case_eq
         , ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq
         , semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq
         , pair_case_eq,consume_space_def]
     \\ rveq \\ fs [call_env_def,do_app_with_clock,do_app_with_locals]
     \\ imp_res_tac do_app_const \\ fs [set_var_def,state_component_equality]
     \\ PairCases_on `y` \\ fs []
     \\ qpat_x_assum `v4 = _` (fn th => once_rewrite_tac [th]) \\ fs []
     \\ imp_res_tac do_app_const
     \\ fs [set_var_def,state_component_equality]
     (* FIX: this is obnoxious *)
     \\ qmatch_goalsub_abbrev_tac `size_of_heap f1`
     \\ qpat_abbrev_tac `f2 = (s with locals := _)`
     \\ `size_of_heap f1 = size_of_heap f2` suffices_by rw []
     \\ `f1 = f2 with clock := ck + s.clock` by rw [Abbr `f1`,Abbr `f2`,state_component_equality]
     \\ rw [size_of_heap_with_clock])
  >- (EVAL_TAC >> simp[state_component_equality])
  >- (every_case_tac >> fs[] >> srw_tac[][]
     \\ fs [add_space_def,size_of_heap_def,stack_to_vs_def]
     \\ rw [state_component_equality,size_of_heap_with_clock])
  >- (every_case_tac >> fs[] >> srw_tac[][] >> fs[jump_exc_NONE]
     \\ imp_res_tac jump_exc_IMP >> fs[]
     \\ srw_tac[][] >> fs[jump_exc_def])
  >- (every_case_tac >> fs[] >> srw_tac[][call_env_def])
  >- (fs[LET_THM]
     \\ pairarg_tac >> fs[]
     \\ every_case_tac >> fs[] >> srw_tac[][]
     \\ rfs[] >> srw_tac[][])
  >- (every_case_tac >> fs[] >> srw_tac[][])
  >- (every_case_tac >> fs[] >> srw_tac[][] >> rfs[]
     \\ fsrw_tac[ARITH_ss][call_env_def,dec_clock_def,push_env_def,pop_env_def,set_var_def]
     \\ first_x_assum(qspec_then`ck`mp_tac) >> simp[]
     \\ every_case_tac >> fs[] >> srw_tac[][] >> rfs[] >> fs[]
     \\ spose_not_then strip_assume_tac >> fs[])
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
              pair_case_eq,consume_space_def,check_lim_def] >>
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
  recInduct evaluate_ind
  \\ srw_tac[][evaluate_def,LET_THM]
  \\ TRY (rename1`find_code`
         \\ every_case_tac >> fs[] >> srw_tac[][]
         \\ imp_res_tac evaluate_io_events_mono >> fs[]
         \\ imp_res_tac pop_env_const >> fs[]
         \\ fsrw_tac[ARITH_ss][dec_clock_def,call_env_with_const,push_env_with_const]
         \\ imp_res_tac evaluate_add_clock >> fs[] >> rfs[]
         \\ fsrw_tac[ARITH_ss][call_env_with_const]
         \\ rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[])
         \\ srw_tac[][] >> fs[set_var_with_const]
         \\ metis_tac[evaluate_io_events_mono,SND,PAIR,IS_PREFIX_TRANS
                     ,set_var_const,set_var_with_const,with_clock_ffi])
  \\ rpt (pairarg_tac >> fs[])
  \\ every_case_tac >> fs[cut_state_opt_with_const] >> rfs[]
  \\ rveq >> fs[] >> rveq >> fs[]
  \\ fs [do_app_with_clock]
  \\ TRY (PairCases_on `y`) >> fs []
  \\ imp_res_tac jump_exc_IMP >> fs[jump_exc_NONE]
  \\ rveq >> fs[state_component_equality]
  \\ imp_res_tac evaluate_add_clock >> fs[]
  \\ rveq >> fs[]
  \\ imp_res_tac evaluate_io_events_mono >> rfs[]
  \\ fs [] >> imp_res_tac jump_exc_IMP >> rw[jump_exc_NONE]
  \\ metis_tac[evaluate_io_events_mono,IS_PREFIX_TRANS,SND,PAIR]
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
  good_code_labels p elabs ⇔
    (BIGUNION (set (MAP (λ(n,m,pp). (get_code_labels pp)) p))) ⊆
    (set (MAP FST p)) ∪ elabs`

Theorem get_code_labels_mk_ticks:
   ∀n m. get_code_labels (mk_ticks n m) ⊆ get_code_labels m
Proof
   Induct
   \\ rw[dataLangTheory.mk_ticks_def] \\ rw[FUNPOW]
   \\ fs[dataLangTheory.mk_ticks_def]
   \\ first_x_assum (qspec_then`Seq Tick m`mp_tac)
   \\ rw[]
QED

Theorem v_to_list_SOME_NIL_IFF:
   !v. v_to_list v = SOME [] <=> ?ts. v = Block ts nil_tag []
Proof
  recInduct v_to_list_ind
  \\ rw [] \\ fs [v_to_list_def,list_to_v_def]
  \\ TRY (eq_tac \\ rw [list_to_v_def])
  \\ fs [v_to_list_def,list_to_v_def]
  \\ fs [case_eq_thms] \\ rveq \\ fs []
  \\ rveq \\ fs [list_to_v_def]
  \\ Cases_on `in2` \\ fs [list_to_v_def]
QED

Theorem v_to_list_SOME_CONS_IMP:
   ∀v x xs ts. v_to_list v = SOME (x::xs)
   ==> ?ts' ys. v = Block ts' cons_tag [x;ys] ∧ v_to_list ys = SOME xs
Proof
  recInduct v_to_list_ind
  \\ fs [v_to_list_def] \\ rw []
  \\ every_case_tac \\ fs []
QED

Theorem do_app_safe_for_space_mono:
  (do_app op xs s = Rval (r,s1)) /\ s1.safe_for_space ==> s.safe_for_space
Proof
  Cases_on `op` \\
  fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
      bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_space_def,
      with_fresh_ts_def,closSemTheory.ref_case_eq,do_install_def,
      ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,check_lim_def,
      semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
      pair_case_eq,consume_space_def,op_space_reset_def,data_spaceTheory.op_space_req_def]
  \\ rw [] \\ fs [state_component_equality] \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ EVERY_CASE_TAC \\ fs []
QED

Theorem evaluate_safe_for_space_mono:
  !prog ^s res s1.
    evaluate (prog,s) = (res,s1) /\ s1.safe_for_space ==> s.safe_for_space
Proof
  recInduct evaluate_ind \\ fs [evaluate_def] \\ rw[]
  \\ fs [CaseEq"option",cut_state_opt_def,CaseEq"result",pair_case_eq,
         cut_state_def,jump_exc_def,CaseEq"stack",CaseEq"list"]
  \\ fs [] \\ rveq \\ fs [set_var_def,call_env_def,dec_clock_def,add_space_def]
  \\ imp_res_tac do_app_safe_for_space_mono
  \\ TRY pairarg_tac \\ fs [CaseEq"bool"]
  \\ fs [] \\ rveq \\ fs [set_var_def,call_env_def,dec_clock_def,add_space_def,
       CaseEq"option",pair_case_eq,push_env_def,CaseEq"result"]
  \\ fs [] \\ rveq \\ fs [set_var_def,call_env_def,dec_clock_def,add_space_def,
       CaseEq"option",pair_case_eq,push_env_def,CaseEq"result"]
  \\ TRY (Cases_on `IS_SOME handler`)
  \\ fs [] \\ rveq \\ fs [set_var_def,call_env_def,dec_clock_def,add_space_def,
       CaseEq"option",pair_case_eq,push_env_def]
  \\ fs [pop_env_def,CaseEq"stack",CaseEq"list",CaseEq"error_result",
         option_case_eq,pair_case_eq] \\ rveq \\ fs []
QED

val _ = export_theory();
