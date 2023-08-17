(*
  Properties about dataLang and its semantics
*)
open preamble dataLangTheory dataSemTheory semanticsPropsTheory backendPropsTheory;

val _ = new_theory"dataProps";

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

Definition approx_of_def:
  (approx_of lims [] refs = 0) /\
  (approx_of lims (x::y::ys) refs =
    approx_of lims [x] refs + approx_of lims (y::ys) refs) /\
  (approx_of lims [Word64 _] refs = 3) /\
  (approx_of lims [Number i] refs =
    (if small_num lims.arch_64_bit i then 0 else bignum_size lims.arch_64_bit i)) /\
  (approx_of lims [CodePtr _] refs = 0) /\
  (approx_of lims [RefPtr r] refs =
     case lookup r refs of
     | NONE => 0
     | SOME (ByteArray _ bs) => LENGTH bs DIV (arch_size lims DIV 8) + 2
     | SOME (ValueArray vs) =>
         approx_of lims vs (delete r refs) + LENGTH vs + 1) /\
  (approx_of lims [Block ts tag []] refs = 0) /\
  (approx_of lims [Block ts tag vs] refs =
    approx_of lims vs refs + LENGTH vs + 1)
Termination
  WF_REL_TAC `(inv_image (measure I LEX measure v1_size)
                          (\(lims,vs,refs). (sptree$size refs,vs)))`
  \\ rpt strip_tac \\ fs [sptreeTheory.size_delete]
  \\ imp_res_tac miscTheory.lookup_zero \\ fs []
End

Theorem size_of_approx_of:
  ∀lims xs refs seen n1 refs1 seen1.
    size_of lims xs refs seen = (n1,refs1,seen1) ⇒
    n1 ≤ approx_of lims xs refs
Proof
  qsuff_tac ‘∀lims xs refs seen refsT n1 refs1 seen1.
    size_of lims xs refs seen = (n1,refs1,seen1) ∧ subspt refs refsT ⇒
    n1 ≤ approx_of lims xs refsT ∧ subspt refs1 refs’
  THEN1 (fs [subspt_lookup] \\ metis_tac [])
  \\ ho_match_mp_tac size_of_ind \\ rw []
  \\ fs [size_of_def,approx_of_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ res_tac \\ res_tac \\ fs []
  \\ imp_res_tac subspt_trans \\ res_tac \\ simp []
  \\ ntac 2 (pop_assum kall_tac)
  \\ TRY (
    Cases_on ‘lookup r refs’ \\ fs []
    \\ Cases_on ‘x’ \\ fs []
    \\ rveq \\ fs []
    \\ fs [subspt_lookup] \\ res_tac \\ fs []
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs [lookup_delete]
    \\ first_x_assum (qspec_then ‘delete r refsT’ mp_tac)
    \\ fs [lookup_delete] \\ NO_TAC)
  \\ Cases_on ‘lookup ts seen’ \\ fs []
  \\ rveq \\ fs [] \\ res_tac \\ fs []
QED

val s = ``s:('c,'ffi) dataSem$state``

Theorem OPTION_MAP2_ADD_SOME_0[simp]:
  OPTION_MAP2 $+ x (SOME 0n) = x
Proof
  Cases_on `x` \\ fs []
QED

Theorem OPTION_MAP2_MAX_CANCEL[simp]:
  OPTION_MAP2 MAX (OPTION_MAP2 MAX x y) y = OPTION_MAP2 MAX x y
Proof
  Cases_on `x` \\ Cases_on `y` \\ fs [] \\ rw [MAX_DEF]
QED

Theorem initial_state_simp[simp]:
  (initial_state f c co cc ts l ss k).clock = k ∧
  (initial_state f c co cc ts l ss k).locals = LN ∧
  (initial_state f c co cc ts l ss k).code = c ∧
  (initial_state f c co cc ts l ss k).ffi = f ∧
  (initial_state f c co cc ts l ss k).compile_oracle = co ∧
  (initial_state f c co cc ts l ss k).compile = cc ∧
  (initial_state f c co cc ts l ss k).stack = [] ∧
  (initial_state f c co cc ts l ss k).peak_heap_length = 0
Proof
  srw_tac[][initial_state_def]
QED

Theorem initial_state_with_simp[simp]:
   (initial_state f c co cc ts l ss k with clock := k' = initial_state f c co cc ts l ss k') ∧
   (initial_state f c co cc ts l ss k with stack := [] = initial_state f c co cc ts l ss k) ∧
   (initial_state f c co cc ts l ss k with locals := LN = initial_state f c co cc ts l ss k)
Proof
  srw_tac[][initial_state_def]
QED
(*
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
*)
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
   (cut_state_opt x (y with clock := k) = OPTION_MAP (λs. s with clock := k) (cut_state_opt x y)) ∧
  (cut_state_opt x (y with locals_size := lsz) = OPTION_MAP (λs. s with locals_size := lsz) (cut_state_opt x y))
Proof
  EVAL_TAC >> every_case_tac >> simp[]
QED

(* INFO: only used in bvi_to_dataProof *)
Theorem consume_space_add_space:
  ∃sf hp. consume_space k (add_space (t with locals := env1) k)  =
          SOME (t with <| locals := env1 ; space := 0
                        ; safe_for_space := sf
                        ; peak_heap_length := hp |>)
Proof
  full_simp_tac(srw_ss())[consume_space_def,add_space_def,state_component_equality] \\ DECIDE_TAC
QED

val consume_space_with_stack = Q.prove(
  `consume_space x (y with stack := z) = OPTION_MAP (λs. s with stack := z) (consume_space x y)`,
  EVAL_TAC >> srw_tac[][]);

val consume_space_with_locals = Q.prove(
  `consume_space x (y with locals := z) = OPTION_MAP (λs. s with locals := z) (consume_space x y)`,
  EVAL_TAC >> srw_tac[][]);

val do_app_with_stack = time Q.prove(
  `do_app op vs (s with stack := z) =
   map_result (λ(x,y). (x,y with <| stack := z
                                  ; safe_for_space   := do_app_safe op vs (s with stack := z)
                                  ; stack_max := (do_stack op vs (s with stack := z)).stack_max
                                  ; peak_heap_length := do_app_peak op vs (s with stack := z) |>))
              I (do_app op vs s)`,
  Cases_on `do_app op vs (s with stack := z)`
  \\ Cases_on `op`
  \\ TRY (rename [‘EqualConst cc’] \\ Cases_on ‘cc’)
  \\ ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_stack_def,do_space_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,do_install_def,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def,op_space_reset_def,check_lim_def] >>
          TRY (pairarg_tac \\ fs []) >>
          rveq >> fs []) >>
          fs[allowed_op_def]>>
          rw [state_component_equality] \\ simp [Once CONJ_COMM] \\
          rw[EQ_IMP_THM] >> fs[stack_consumed_def,allowed_op_def,PULL_EXISTS]);

val do_app_with_stack_and_locals = time Q.prove(
  `do_app op vs (s with <|locals_size := lsz; stack := z|>) =
   map_result (λ(x,y). (x,y with <| stack := z
                                  ; locals_size := lsz
                                  ; safe_for_space   := do_app_safe op vs (s with <|locals_size := lsz; stack := z|>)
                                  ; stack_max := (do_stack op vs (s with <|locals_size := lsz; stack := z|>)).stack_max
                                  ; peak_heap_length := do_app_peak op vs (s with <|locals_size := lsz; stack := z|>) |>))
              I (do_app op vs s)`,
  Cases_on `do_app op vs (s with <|locals_size := lsz; stack := z|>)`
  \\ Cases_on `op`
  \\ TRY (rename [‘EqualConst cc’] \\ Cases_on ‘cc’)
  \\ ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_stack_def,do_space_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,do_install_def,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def,op_space_reset_def,check_lim_def] >>
          TRY (pairarg_tac \\ fs []) >>
          rveq >> fs []) >>
          fs[allowed_op_def] >>
          rw [state_component_equality] \\ simp [Once CONJ_COMM] \\
          rw[EQ_IMP_THM] >> fs[stack_consumed_def,allowed_op_def]);

Theorem do_app_aux_with_space:
  do_app_aux op vs (s with space := z) = map_result (λ(x,y). (x,y with space := z)) I (do_app_aux op vs s)
Proof
  Cases_on `do_app_aux op vs (s with space := z)`
  \\ Cases_on `op`
  \\ TRY (rename [‘EqualConst cc’] \\ Cases_on ‘cc’)
  \\ ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_stack_def,do_space_def,
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
  \\ TRY (rename [‘EqualConst cc’] \\ Cases_on ‘cc’)
  \\ ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_stack_def,do_space_def,
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
                                  ; stack_max := (do_stack op vs (s with locals := z)).stack_max
                                  ; peak_heap_length := do_app_peak op vs (s with locals := z)|>))
                       I (do_app op vs s)`,
  Cases_on `do_app op vs (s with locals := z)`
  \\ Cases_on `op`
  \\ TRY (rename [‘EqualConst cc’] \\ Cases_on ‘cc’)
  \\ ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_stack_def,do_space_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,do_install_def,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def,check_lim_def] >>
          TRY (pairarg_tac \\ fs []) >>
          rveq >> fs []) >>
          fs [allowed_op_def]>>
          rw [state_component_equality] \\ simp [Once CONJ_COMM] \\ rw[EQ_IMP_THM] >> fs[stack_consumed_def,allowed_op_def]);

Theorem do_app_aux_err:
   do_app_aux op vs s = Rerr e ⇒ (e = Rabort Rtype_error)
                             \/
                             (?i x. op = FFI i /\ e = Rabort (Rffi_error x))
Proof
  rw [ do_app_aux_def,case_eq_thms, AllCaseEqs()
     , do_install_def,do_space_def,with_fresh_ts_def
     , PULL_EXISTS, UNCURRY,consume_space_def]
  \\ fs []
QED

Theorem do_app_aux_const:
    do_app_aux op vs x = Rval (y,z) ⇒
    z.stack = x.stack ∧ z.handler = x.handler ∧ z.locals = x.locals ∧
    z.clock = x.clock ∧ z.compile = x.compile
Proof
  rw [ do_app_aux_def,case_eq_thms, AllCaseEqs()
     , do_install_def,do_space_def,with_fresh_ts_def
     , PULL_EXISTS, UNCURRY,consume_space_def, check_lim_def]
  \\ fs []
QED

Theorem do_app_err:
   do_app op vs s = Rerr e ⇒ (e = Rabort Rtype_error)
                             \/
                             (?i x. op = FFI i /\ e = Rabort (Rffi_error x))
Proof
  rw [ do_app_def,do_stack_def,case_eq_thms, AllCaseEqs()
     , do_install_def,do_space_def,with_fresh_ts_def
     , PULL_EXISTS, UNCURRY,consume_space_def]
  \\ fs []
  \\ METIS_TAC [do_app_aux_err]
QED

Theorem do_stack_const[simp]:
  (do_stack op vs s).locals             = s.locals
∧ (do_stack op vs s).locals_size        = s.locals_size
∧ (do_stack op vs s).stack              = s.stack
∧ (do_stack op vs s).stack_frame_sizes  = s.stack_frame_sizes
∧ (do_stack op vs s).global             = s.global
∧ (do_stack op vs s).handler            = s.handler
∧ (do_stack op vs s).refs               = s.refs
∧ (do_stack op vs s).compile            = s.compile
∧ (do_stack op vs s).clock              = s.clock
∧ (do_stack op vs s).code               = s.code
∧ (do_stack op vs s).ffi                = s.ffi
∧ (do_stack op vs s).space              = s.space
∧ (do_stack op vs s).tstamps            = s.tstamps
∧ (do_stack op vs s).limits             = s.limits
∧ (do_stack op vs s).peak_heap_length   = s.peak_heap_length
∧ (do_stack op vs s).compile_oracle     = s.compile_oracle
Proof
  EVAL_TAC
QED

Theorem do_app_const:
   do_app op vs x = Rval (y,z) ⇒
    z.stack = x.stack ∧ z.handler = x.handler ∧ z.locals = x.locals ∧
    z.clock = x.clock ∧ z.compile = x.compile
Proof
  rw [ do_app_def,do_stack_def,do_app_aux_def,case_eq_thms
     , do_install_def,do_space_def,with_fresh_ts_def, AllCaseEqs()
     , PULL_EXISTS, UNCURRY,consume_space_def, check_lim_def]
  \\ fs []
QED

Theorem do_app_locals:
   (do_app op x s = Rval (q,r)) ==>
   (do_app op x (s with locals := extra) =
         Rval (q,r with <| locals := extra
                         ; safe_for_space   := do_app_safe op x (s with locals := extra)
                         ; stack_max   := (do_stack op x (s with locals := extra)).stack_max
                         ; peak_heap_length := do_app_peak op x (s with locals := extra)|>))
Proof
   simp[do_app_with_locals,state_component_equality]
QED

Theorem do_space_alt:
  do_space op vs s =
      if op_space_reset op
      then SOME (s with <| space := 0
                         ; safe_for_space   := do_space_safe op vs s
                         ; peak_heap_length := do_space_peak op vs s |>)
      else consume_space (op_space_req op (LENGTH vs)) s
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

val do_app_swap_tac =
   strip_tac
   \\ Cases_on ‘op’
   \\ TRY (rename [‘EqualConst cc’] \\ Cases_on ‘cc’)
   \\ rw [do_app_def,do_stack_def
              , do_install_def
              , do_app_aux_def
              , with_fresh_ts_def
              , do_space_def
              , op_space_reset_def
              , data_spaceTheory.op_space_req_def
              , consume_space_def
              , stack_consumed_def
              , size_of_heap_with_safe
              , MAX_DEF
              , check_lim_def]
  \\ TRY (pairarg_tac \\ fs [])
  \\ TRY (fs [list_case_eq,option_case_eq,v_case_eq,bool_case_eq,closSemTheory.ref_case_eq
        , ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq, state_component_equality
        , semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,pair_case_eq
        , limits_component_equality,stack_consumed_def]
          \\ fs  [data_spaceTheory.op_space_req_def,stack_consumed_def]
          \\ rfs [data_spaceTheory.op_space_req_def]
          \\ simp [Once CONJ_COMM] \\ NO_TAC) \\
  rpt(PURE_TOP_CASE_TAC \\ fs[] \\ rveq) \\ fs[state_component_equality,stack_consumed_def];


Theorem do_app_aux_safe_peak_swap:
  ∀op vs s q s' safe peak. do_app_aux op vs s = Rval (q,s')
    ⇒ ∃safe' peak'.
        do_app_aux op vs (s with <| safe_for_space := safe; peak_heap_length := peak |>) =
        Rval (q,s' with <| safe_for_space := safe'; peak_heap_length := peak' |>)
Proof
   do_app_swap_tac
QED

Theorem do_app_safe_peak_swap:
  ∀op vs s q s' safe peak.
   do_app op vs s = Rval (q,s')
     ⇒ ?new_safe new_peak.
           do_app op vs (s with <| safe_for_space := safe; peak_heap_length := peak|>) =
           Rval (q,s' with <| safe_for_space := new_safe; peak_heap_length := new_peak|>)
Proof
  do_app_swap_tac
QED

Theorem do_app_err_safe_peak_swap:
  ∀op vs s e safe peak. do_app op vs s = Rerr e
    ⇒ do_app op vs (s with <| safe_for_space := safe; peak_heap_length := peak |>) =
      Rerr e
Proof
  do_app_swap_tac
QED

Theorem do_app_lss_sm_safe_peak_swap_aux[local]:
  ∀op vs s q s' lss smx safe peak. do_app op vs s = Rval (q,s')
    ⇒ ∃safe' peak' lss' smx'.
        do_app op vs (s with <|locals_size := lss; stack_max := smx;
           safe_for_space := safe; peak_heap_length := peak |>) =
        Rval (q,s' with <| locals_size := lss'; stack_max := smx';
           safe_for_space := safe'; peak_heap_length := peak' |>)
Proof
  do_app_swap_tac
QED

Theorem do_app_lss_sm_safe_peak_swap =
  do_app_lss_sm_safe_peak_swap_aux |> SIMP_RULE std_ss [LET_DEF];

Theorem do_app_sm_safe_peak_swap_aux[local]:
  ∀op vs s q s' smx safe peak. do_app op vs s = Rval (q,s')
    ⇒ ∃safe' peak' smx'.
        do_app op vs (s with <|stack_max := smx;
           safe_for_space := safe; peak_heap_length := peak |>) =
        Rval (q,s' with <|stack_max := smx';
           safe_for_space := safe'; peak_heap_length := peak' |>)
Proof
  do_app_swap_tac
QED

Theorem do_app_sm_safe_peak_swap =
  do_app_sm_safe_peak_swap_aux |> SIMP_RULE std_ss [LET_DEF];

Theorem do_app_aux_sm_safe_peak_swap:
  ∀op vs s q s' smx safe peak. do_app_aux op vs s = Rval (q,s')
    ⇒ ∃safe' peak' smx'.
        do_app_aux op vs (s with <| stack_max := smx;
           safe_for_space := safe; peak_heap_length := peak |>) =
        Rval (q,s' with <| stack_max := smx';
           safe_for_space := safe'; peak_heap_length := peak' |>)
Proof
  do_app_swap_tac
QED


Theorem do_app_aux_lss_sm_safe_peak_swap:
  ∀op vs s q s'  lss smx safe peak. do_app_aux op vs s = Rval (q,s')
    ⇒ ∃safe' peak' lss' smx'.
        do_app_aux op vs (s with <|locals_size := lss; stack_max := smx;
           safe_for_space := safe; peak_heap_length := peak |>) =
        Rval (q,s' with <| locals_size := lss'; stack_max := smx';
           safe_for_space := safe'; peak_heap_length := peak' |>)
Proof
  do_app_swap_tac
QED

Theorem do_app_err_lss_sm_safe_peak_swap:
  ∀op vs s e lss smx safe peak. do_app op vs s = Rerr e
    ⇒ do_app op vs (s with <| locals_size := lss; stack_max := smx;
       safe_for_space := safe; peak_heap_length := peak |>) =
      Rerr e
Proof
  do_app_swap_tac
QED

Theorem do_app_err_sm_safe_peak_swap:
  ∀op vs s e smx safe peak. do_app op vs s = Rerr e
    ⇒ do_app op vs (s with <|stack_max := smx; safe_for_space := safe; peak_heap_length := peak |>) =
      Rerr e
Proof
  do_app_swap_tac
QED


Theorem do_app_lss_stk_stfrm_swap_aux[local]:
  ∀op vs s q s' lss stk stfrm. do_app op vs s = Rval (q,s')  ⇒
    ?ss pk smx. do_app op vs (s with <|locals_size := lss; stack := stk; stack_frame_sizes := stfrm |>) =
      Rval (q,s' with <|locals_size := lss;
                        stack := stk;
                        stack_frame_sizes := if op = Install then LN else stfrm;
                        stack_max := smx;
                        safe_for_space := ss;
                        peak_heap_length := pk|>)
Proof
  do_app_swap_tac
QED

Theorem do_app_lss_stk_stfrm_swap = do_app_lss_stk_stfrm_swap_aux |> SIMP_RULE std_ss [LET_DEF]

Theorem do_app_err_lss_stk_stfrm_swap:
  ∀op vs s lss stk stfrm. do_app op vs s = Rerr e
    ⇒ do_app op vs (s with <|locals_size := lss; stack := stk; stack_frame_sizes := stfrm |>) =
      Rerr e
Proof
  do_app_swap_tac
QED

Theorem do_app_lim_swap_aux[local]:
  ∀op vs s q s' lim. do_app op vs s = Rval (q,s')
    ⇒ ∃safe peak smx.
        do_app op vs (s with limits := lim) =
        Rval (q,s' with <|limits := lim;
                          stack_max := smx;
                          safe_for_space := safe;
                          peak_heap_length := peak |>)
Proof
  do_app_swap_tac
QED

Theorem do_app_lim_swap = do_app_lim_swap_aux |> SIMP_RULE std_ss [LET_DEF]


Theorem do_app_err_lim_swap:
  ∀op vs s e lim. do_app op vs s = Rerr e
    ⇒ do_app op vs (s with <|limits := lim|>) =
      Rerr e
Proof
  do_app_swap_tac
QED

Theorem size_of_stack_eq:
  (size_of_stack(Env n l::stack) = OPTION_MAP2 $+ n (size_of_stack stack)) /\
  (size_of_stack(Exc n v1 v2::stack) =
     OPTION_MAP2 $+ (OPTION_MAP ($+ 3) n) (size_of_stack stack)) /\
  (size_of_stack [] = SOME 1)
Proof
  rw[size_of_stack_def,size_of_stack_frame_def]
QED

val full_fs = fs[ get_var_def, set_var_def
                      , cut_state_opt_def
                      , cut_state_def
                      , get_vars_def
                      , do_install_def
                      , op_space_reset_def
                      , call_env_def
                      , flush_state_def
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

val basic_tac = fs [evaluate_def]
                      \\ rpt (every_case_tac
                      \\ full_fs
                      \\ fs [state_component_equality]);


Theorem evaluate_fl_smx_safe_peak_swap_aux[local]:
  ∀c s r s' fl smx safe peak.
   evaluate (c,s) = (r,s') ⇒
     if fl
       then (let s0 = s with <|stack_max := smx;
                               safe_for_space := safe; peak_heap_length := peak|>
             in ?smx safe peak. evaluate (c,s0) =
                   (r,s' with <|stack_max := smx;
                                safe_for_space := safe; peak_heap_length := peak|>))
       else
       (let s0 = s with <|stack_max := s.stack_max;
                          safe_for_space := safe; peak_heap_length := peak|>
        in ?smx safe peak. evaluate (c,s0) =
            (r,s' with <|stack_max := s'.stack_max;
                         safe_for_space := safe; peak_heap_length := peak|>))
Proof
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  >- basic_tac
  >- basic_tac
  (* Assign *)
  >- (TOP_CASE_TAC \\ fs [evaluate_def]
     \\ full_cases >> full_fs
     \\ fs [] \\ rfs[]
     \\ rveq \\ fs []
     \\ every_case_tac \\ fs [] \\ rveq \\ fs []
     \\ TRY (metis_tac [] \\ NO_TAC)
     \\ TRY (drule do_app_sm_safe_peak_swap
     \\ disch_then (qspecl_then [`smx`, `safe`, `peak`] assume_tac)
     \\ fs [] \\ metis_tac [] \\ NO_TAC)
     \\ TRY (drule do_app_err_sm_safe_peak_swap
     \\ disch_then (qspecl_then [`smx`, `safe`, `peak`] assume_tac)
     \\ fs [] \\ metis_tac [] \\ NO_TAC)
     \\ TRY (drule do_app_safe_peak_swap
     \\ disch_then (qspecl_then [`safe`, `peak`] assume_tac)
     \\ Cases_on `s` \\ Cases_on `r'` \\ fs [state_fn_updates] \\ NO_TAC)
     \\ TRY (drule do_app_err_safe_peak_swap
     \\ disch_then (qspecl_then [`safe`, `peak`] assume_tac)
     \\ Cases_on `s` \\ fs [state_fn_updates] \\ NO_TAC))
  (*  Tick *)
  >- (fs [evaluate_def]
     \\ full_cases >>  full_fs
     \\ rveq \\ fs []
     \\ every_case_tac
     \\ TRY (metis_tac [] \\ NO_TAC)
     \\ TRY (first_assum (mp_then Any (qspecl_then [`smx`, `safe`,`peak`] assume_tac)
          do_app_sm_safe_peak_swap))
     \\ TRY (first_assum (mp_then Any (qspecl_then [`smx`, `safe`,`peak`] assume_tac)
          do_app_err_sm_safe_peak_swap))
     \\ rfs [] \\ rveq \\ fs [])
  >- basic_tac
  >- basic_tac
  >- basic_tac
  (* Seq *)
  >- (IF_CASES_TAC
     \\ fs[evaluate_def]
     \\ Cases_on `evaluate (c1,s)` \\ fs[]
     \\ every_case_tac \\ rveq \\ fs []
     >- (pairarg_tac \\ fs [] \\ rveq
        \\ IF_CASES_TAC \\ fs [] \\ rveq
        \\ first_x_assum (qspecl_then [`T`, `smx`,`safe`,`peak`] assume_tac) \\ rfs [] \\ metis_tac [])
     >- (first_x_assum (qspecl_then [`T`, `smx`, `safe`,`peak`] assume_tac)
        \\ fs [] \\ every_case_tac \\ fs [] \\ metis_tac [])
     >- (pairarg_tac \\ fs [] \\ rveq
        \\ IF_CASES_TAC \\ fs [] \\ rveq
        \\ first_x_assum (qspecl_then [`F`,`s.stack_max`, `safe`,`peak`] assume_tac)
        \\ rfs [] \\ metis_tac [])
     \\ first_x_assum (qspecl_then [`F`, `s.stack_max`, `safe`,`peak`] assume_tac)
     \\ fs [] \\ every_case_tac \\ fs [] \\ metis_tac [])
  >- (fs [evaluate_def]
      \\ every_case_tac
      \\ full_fs >> metis_tac [])

  (* Call *)
  (* to save the outer if to have minimised duplication
     trade-off then is to use explixit cases insteade ofIF_CASES_TAC *)
  >> fs [evaluate_def]
  >> Cases_on `get_vars args s.locals` >> fs [] >> rveq >> fs []
  >- metis_tac []
  >> Cases_on `find_code dest x s.code s.stack_frame_sizes` >> fs []
  >- metis_tac []
  >> Cases_on `x'` >> fs []
  >> Cases_on `r'` >> fs []
  >> Cases_on `ret` >> fs []
  >- (Cases_on `handler` >> fs []
      >- (Cases_on `s.clock = 0` >> fs []
          >- fs [flush_state_def, state_component_equality]
          >> fs [dec_clock_def]
          >> Cases_on ` evaluate (q',call_env q r'' (s with clock := s.clock − 1))`
          >> fs [call_env_def] >> Cases_on `q''` >> fs [] >> rveq
          >> qpat_abbrev_tac `smnew = OPTION_MAP2 MAX _ _`
          >> qpat_abbrev_tac `ssnew = (_ /\ _)`
          >> IF_CASES_TAC >> fs []
          >> TRY (last_x_assum (qspecl_then [`T`, `smnew`,`ssnew`,`peak`] assume_tac)
          >> fs [] >> metis_tac [] >> NO_TAC)
          >> unabbrev_all_tac
          >> qpat_abbrev_tac `smnew = OPTION_MAP2 MAX _ _`
          >> qpat_abbrev_tac `ssnew = (_ /\ _)`
          >> last_x_assum (qspecl_then [`F`, `smnew`,`ssnew`,`peak`] assume_tac)
          >> fs [] >> metis_tac [])
      >> metis_tac [])
  (* returning call *)
   >> Cases_on `x'` >> fs []
   >> Cases_on `cut_env r' s.locals` >> fs []
   >- metis_tac []
   >> Cases_on `s.clock = 0` >> fs []
   (* calling the environment here, when s = 0 *)
   >- (IF_CASES_TAC >> rveq >> Cases_on `handler` >>
       fs [push_env_def, call_env_def, dec_clock_def]
       >> metis_tac [])
      (* when clock is not zero *)
   >> Cases_on `handler`
   >> fs [push_env_def, call_env_def, dec_clock_def]
   >- (* No handler case *)
       (IF_CASES_TAC >> fs[CaseEq "option", CaseEq "prod", CaseEq"result", CaseEq "error_result",
           PULL_EXISTS] >>
        rveq >>
        qmatch_goalsub_abbrev_tac `stack_max_fupd(K smnew)` >>
        qmatch_goalsub_abbrev_tac `safe_for_space_fupd(K ssnew)` >>
        qmatch_goalsub_abbrev_tac `peak_heap_length_fupd(K phlnew)` >>
        TRY (first_x_assum(drule_then(qspecl_then[`T`, `smnew`,`ssnew`,`phlnew`] strip_assume_tac)) >>
        simp[set_var_def] >> rw[state_component_equality] >>
        fs[pop_env_def,CaseEq"list",CaseEq"stack"] >> rveq >> fs[] >> metis_tac [] >> NO_TAC) >>
        TRY (first_x_assum(drule_then(qspecl_then[`F`, `smnew`,`ssnew`,`phlnew`] strip_assume_tac)) >>
        simp[set_var_def] >> rw[state_component_equality] >>
        fs[pop_env_def,CaseEq"list",CaseEq"stack"] >> rveq >> fs[] >> metis_tac [] >> NO_TAC))
   >- (* Handler case *)
       (IF_CASES_TAC >> fs[CaseEq "option", CaseEq "prod", CaseEq"result", CaseEq "error_result",
           PULL_EXISTS] >>
        rveq >>
        qmatch_goalsub_abbrev_tac `stack_max_fupd(K smnew)` >>
        qmatch_goalsub_abbrev_tac `safe_for_space_fupd(K ssnew)` >>
        qmatch_goalsub_abbrev_tac `peak_heap_length_fupd(K phlnew)` >>
        TRY (first_x_assum(drule_then(qspecl_then[`T`, `smnew`,`ssnew`,`phlnew`] strip_assume_tac)) >>
        simp[set_var_def] >> rw[state_component_equality] >>
        fs[pop_env_def,CaseEq"list",CaseEq"stack"] >> rveq >> fs[] >>
        qmatch_goalsub_abbrev_tac `stack_max_fupd(K smnewer)` >>
        qmatch_goalsub_abbrev_tac `safe_for_space_fupd(K ssnewer)` >>
        qmatch_goalsub_abbrev_tac `peak_heap_length_fupd(K phlnewer)` >>
        first_x_assum(drule_then drule) >>
        disch_then(qspecl_then[`T`,`smnewer`,`ssnewer`,`phlnewer`] strip_assume_tac) >>
        fs[set_var_def] >> rw[state_component_equality] >> NO_TAC) >>
        TRY (first_x_assum(drule_then(qspecl_then[`F`, `smnew`,`ssnew`,`phlnew`] strip_assume_tac)) >>
        simp[set_var_def] >> rw[state_component_equality] >>
        fs[pop_env_def,CaseEq"list",CaseEq"stack"] >> rveq >> fs[] >>
        qmatch_goalsub_abbrev_tac `stack_max_fupd(K smnewer)` >>
        qmatch_goalsub_abbrev_tac `safe_for_space_fupd(K ssnewer)` >>
        qmatch_goalsub_abbrev_tac `peak_heap_length_fupd(K phlnewer)` >>
        first_x_assum(drule_then drule) >>
        disch_then(qspecl_then[`F`,`smnewer`,`ssnewer`,`phlnewer`] strip_assume_tac) >>
        fs[set_var_def] >> rw[state_component_equality] >> metis_tac [] >> NO_TAC))
QED

Theorem evaluate_smx_safe_peak_swap_aux = evaluate_fl_smx_safe_peak_swap_aux |>
              Q.SPECL [`c`,`s`,`r`,`s'`,`T`,`smx`,`safe`,`peak`] |> SIMP_RULE std_ss [] |> GEN_ALL
Theorem evaluate_smx_safe_peak_swap =  evaluate_smx_safe_peak_swap_aux |> SIMP_RULE std_ss [LET_DEF]


Theorem evaluate_safe_peak_swap_aux = evaluate_fl_smx_safe_peak_swap_aux |>
              Q.SPECL [`c`,`s`,`r`,`s'`,`F`,`smx`,`safe`,`peak`] |> SIMP_RULE std_ss [] |> GEN_ALL

Theorem evaluate_safe_peak_swap:
  ∀safe s' s r peak c.
    evaluate (c,s) = (r,s') ⇒
    ∃safe' peak'.
        evaluate
          (c,s with <|safe_for_space := safe;
                      peak_heap_length := peak|>) =
        (r, s' with <|safe_for_space := safe';
                      peak_heap_length := peak'|>)
Proof
  rw []
  \\ drule_then (qspecl_then [`safe`,`peak`] mp_tac)
                evaluate_safe_peak_swap_aux
  \\ rw [LET_DEF]
  \\ MAP_EVERY qexists_tac [`safe'`,`peak'`]
  \\ qmatch_asmsub_abbrev_tac `evaluate (c,s0)`
  \\ qmatch_goalsub_abbrev_tac `evaluate (c,s1)`
  \\ `s0 = s1` by (UNABBREV_ALL_TAC \\ fs [state_component_equality])
  \\ fs [] \\ fs [state_component_equality]
QED

Definition same_stack_size_def:
  same_stack_size x y <=> size_of_stack_frame x = size_of_stack_frame y
End

Theorem same_stack_size_size_of_stack:
  !xs ys.
  LIST_REL same_stack_size xs ys ==>
  size_of_stack xs = size_of_stack ys
Proof
  ho_match_mp_tac LIST_REL_ind >> rw[size_of_stack_def,same_stack_size_def]
QED

Theorem s_peak_heap[simp]:
  s with peak_heap_length := s.peak_heap_length = s /\
  s with safe_for_space := s.safe_for_space = s /\
  s with stack_max := s.stack_max = s /\
  s with locals_size := s.locals_size = s /\
  s with <|stack := s.stack; stack_max := smnew; clock := clock;
           safe_for_space := ssnew|> = s with <|stack_max := smnew; clock := clock;safe_for_space := ssnew|> /\
  s with <|handler:= s.handler; safe_for_space := ssnew; peak_heap_length := plnnew |> = s with <|safe_for_space := ssnew; peak_heap_length := plnnew|>
Proof
  conj_tac >> rw[state_component_equality]
QED

Theorem evaluate_stack_and_locals_swap:
  !c ^s.
     case evaluate (c,s) of
          | (SOME (Rerr(Rabort Rtype_error)),s1) => T
          | (SOME (Rerr(Rabort a)),s1) => (s1.stack = [])
              /\ (!xs lsz. (LENGTH s.stack = LENGTH xs) ==>
                       ?lss sfs smx phl.
                       evaluate (c,s with <|stack := xs; locals_size := lsz |>) =
                         (SOME (Rerr(Rabort a)),s1 with <| locals_size := lss;
                                                           safe_for_space := sfs;
                                                           stack_max := smx;
                                                           peak_heap_length := phl
                                                           |>))
          | (SOME (Rerr (Rraise t)),s1) =>
                (?s2. (jump_exc s = SOME s2) /\ (s2.locals = s1.locals) /\
                      (s2.stack = s1.stack)  /\ (s2.handler = s1.handler) /\
                      (!xs s7 lsz. (jump_exc (s with <|stack := xs; locals_size := lsz |>) = SOME s7) /\
                               (LENGTH s.stack = LENGTH xs) ==>
                               ?lss sfs smx phl.
                               (evaluate (c,s with <|stack := xs; locals_size := lsz |>) =
                                  (SOME (Rerr (Rraise t)),
                                   s1 with <| stack := s7.stack ;
                                              handler := s7.handler ;
                                              locals := s7.locals ;
                                              locals_size := lss;
                                              safe_for_space := sfs ;
                                              stack_max := smx;
                                              peak_heap_length := phl |>))))
          | (res,s1) => (s1.stack = s.stack) /\ (s1.handler = s.handler) /\
                        (!xs lsz. (LENGTH s.stack = LENGTH xs) ==>
                               ?lss sfs smx phl.
                                evaluate (c,s with <|stack := xs; locals_size := lsz |>) =
                                  (res, s1 with <| locals_size := lss;
                                                   stack := xs ;
                                                   safe_for_space := sfs;
                                                   stack_max := smx;
                                                   peak_heap_length := phl|>))
Proof
  ho_match_mp_tac (evaluate_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`)
  \\ REPEAT STRIP_TAC
  (* Skip  *)
  >- fs[LET_DEF, evaluate_def,state_component_equality
       ,evaluate_safe_def,evaluate_peak_def]
  (* Move *)
  >- (fs[LET_DEF, evaluate_def] >> EVAL_TAC
      \\ every_case_tac
      \\ fs[state_component_equality,evaluate_safe_def,evaluate_peak_def])
  (* Assign *)
  >- (fs[evaluate_def]
     \\ every_case_tac
     \\ fs[set_var_def,cut_state_opt_with_const,do_app_with_stack_and_locals]
     \\ imp_res_tac do_app_err >> fs[] >> rpt var_eq_tac
     \\ fs[cut_state_opt_def,cut_state_def] >> every_case_tac >> fs[]
     \\ rpt var_eq_tac >> fs[do_app_with_locals]
     \\ TRY(first_assum(split_uncurry_arg_tac o rhs o concl) >> fs[])
     \\ imp_res_tac do_app_const >> simp[]
     \\ EVAL_TAC >> simp[state_component_equality])
  (* Tick *)
  >- (fs[evaluate_def,evaluate_safe_def,evaluate_peak_def]
     \\ EVAL_TAC
     \\ every_case_tac >> fs[state_component_equality])
  (* MakeSpace *)
  >- (fs[evaluate_def,evaluate_safe_def,evaluate_peak_def]
     \\ every_case_tac >> fs[state_component_equality,add_space_def])
  (* Raise *)
  >- (fs[evaluate_def,evaluate_safe_def,evaluate_peak_def,jump_exc_def,get_var_def]
     \\ TOP_CASE_TAC
     \\ fs[CaseEq "option",CaseEq "bool",CaseEq"list",CaseEq"stack"]
     \\ rveq \\ fs[PULL_EXISTS]
     \\ rw[state_component_equality])
  (* Return *)
  >- (fs[evaluate_def,evaluate_safe_def,evaluate_peak_def]
     \\ EVAL_TAC
     \\ every_case_tac >> fs[state_component_equality])
  (* Seq *)
  >- (fs[evaluate_def,LET_DEF]
      >> pairarg_tac  >>fs []
      >> reverse IF_CASES_TAC \\ fs []
      >- (
       TRY (Cases_on `res`) >> TRY (Cases_on`x`) >> fs[jump_exc_def]
       >- (rfs [] >> rw [] >> last_x_assum (qspecl_then [`xs`,`lsz`] assume_tac) >> rfs [] >> metis_tac []) >>
       Cases_on `e` >> fs[jump_exc_def] >>
       rfs [] >>
       every_case_tac >> fs[] >> SRW_TAC [] [] >> fs[]
       >> every_case_tac >> fs[]
       >> REPEAT STRIP_TAC >> SRW_TAC [] [] >> fs []
       >> TRY(last_x_assum (qspecl_then [`xs`,`lsz`] assume_tac) >> rfs [] >> metis_tac [])
       >> first_x_assum drule >> simp[]
       >> disch_then (qspecl_then [`lsz`] strip_assume_tac) >> rfs [] >> metis_tac []) >>
      rpt(TOP_CASE_TAC >> fs[] >> rveq) >>
      TRY(rw[ELIM_UNCURRY] >>
          res_tac >>
          first_x_assum(qspec_then `lsz` strip_assume_tac) >>
          first_x_assum(qspec_then `lss` strip_assume_tac) >>
          fs[] >>
          qpat_x_assum `evaluate (c',_) = _` assume_tac >>
          drule_then (qspecl_then [`smx`,`sfs`,`phl`] mp_tac) evaluate_smx_safe_peak_swap >>
          simp[] >> rw[] >> goal_assum drule >> NO_TAC) >>
     Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS,CONJ_ASSOC] >>
     conj_tac >-
        (fs[jump_exc_def,CaseEq"list",CaseEq"stack",PULL_EXISTS] >>
         rveq >>
         rfs[]) >>
     rw[ELIM_UNCURRY] >>
     rfs[] >>
     last_x_assum(qspecl_then [`xs`,`lsz`] mp_tac) >> simp[] >>
     strip_tac >> simp[] >>
     first_x_assum(qspec_then `xs` mp_tac) >>
     fs[jump_exc_def,CaseEq"list",CaseEq"stack"] >>
     disch_then(qspec_then `lss` strip_assume_tac) >>
     drule_then (qspecl_then [`smx`,`sfs`,`phl`] mp_tac) evaluate_smx_safe_peak_swap >>
     simp[] >>
     strip_tac >> simp[] >>
     simp[state_component_equality] >>
     rveq >> simp[])
  (* If *)
  >- (fs[evaluate_def,evaluate_safe_def,evaluate_peak_def]
     \\ Cases_on `evaluate (c1,s)` \\ fs[LET_DEF]
     \\ Cases_on `evaluate (c2,s)` \\ fs[LET_DEF]
     \\ Cases_on `get_var n s.locals` \\ fs[]
     \\ Cases_on `isBool T x` \\ fs[get_var_def]
     \\ Cases_on `isBool F x` \\ fs[get_var_def])
  (* Call *)
  >- (fs[evaluate_def]
     \\ Cases_on `get_vars args s.locals` \\ fs[]
     \\ Cases_on `find_code dest x s.code s.stack_frame_sizes` \\ fs[]
     \\ Cases_on `x'` \\ fs[]
     \\ Cases_on `r` \\ fs []
     \\ Cases_on `ret` \\ fs[]
     >- (
        every_case_tac \\ fs[]
        \\ fs[call_env_def,flush_state_def,dec_clock_def,jump_exc_def]
        >- (rw [] >> rw [state_component_equality])
        >- (rw [] >> rw [state_component_equality])
        >- (
          rw [] >>
          first_x_assum drule >> strip_tac >>
          qmatch_goalsub_abbrev_tac `evaluate
              (q', s with <|locals:= _; locals_size := _;  stack := _;
                            stack_max := smnew; clock := _;  safe_for_space := ssnew |>)` >>
          first_x_assum(qspec_then `r'` strip_assume_tac) >>
          drule evaluate_smx_safe_peak_swap_aux >>
          disch_then(qspecl_then [`smnew`,`ssnew`,`s.peak_heap_length`] mp_tac) >>
          simp[] >>
          strip_tac >> fs[] >>
          simp[state_component_equality])
        >- (
          Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS,CONJ_ASSOC] >>
          conj_tac >-
            (drule evaluate_smx_safe_peak_swap_aux >>
             disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV rev)) >>
             disch_then(qspec_then `s.peak_heap_length` mp_tac) >>
             simp[] >>
             disch_then(mp_tac o Ho_Rewrite.REWRITE_RULE [SKOLEM_THM]) >>
             strip_tac >> fs[] >>
             last_x_assum(qspecl_then [`ARB`,`ARB`] strip_assume_tac) >>
             fs[CaseEq"list",CaseEq"stack"] >>
             rpt(PRED_ASSUM is_eq (mp_tac o GSYM)) >>
             rw[]) >>
          rpt strip_tac >>
          qmatch_goalsub_abbrev_tac `evaluate
              (q', s with <|locals:= _; locals_size := _;  stack := _;
                            stack_max := smnew; clock := _;  safe_for_space := ssnew |>)` >>
          first_x_assum(qspec_then `xs` mp_tac) >>
          disch_then drule >>
          fs[CaseEq "list",CaseEq"stack"] >>
          disch_then(qspec_then `r'` strip_assume_tac) >>
          drule evaluate_smx_safe_peak_swap_aux >>
          disch_then(qspecl_then [`smnew`,`ssnew`,`s.peak_heap_length`] mp_tac) >>
          simp[] >>
          strip_tac >> fs[] >>
          simp[state_component_equality] >>
          rpt(PRED_ASSUM is_eq (mp_tac o GSYM)) >>
          rw[]) >>
        (rw [] >>
        qmatch_goalsub_abbrev_tac `evaluate
            (q', s with <|locals:= _; locals_size := _;  stack := _;
                          stack_max := smnew; clock := _;  safe_for_space := ssnew |>)` >>
        first_x_assum (drule_then (qspec_then `r'` strip_assume_tac)) >>
        drule evaluate_smx_safe_peak_swap_aux >>
        disch_then(qspecl_then [`smnew`,`ssnew`,`s.peak_heap_length`] mp_tac) >>
        simp[] >>
        strip_tac >> fs[] >>
        simp[state_component_equality])
        )
     (* returning calls *)
     \\ Cases_on `x'` \\ fs[]
     \\ Cases_on `cut_env r s.locals` \\ fs[]
     \\ IF_CASES_TAC \\ fs[] (* timeout *)
     >- (Cases_on `handler` >>
         rw[call_env_def,push_env_def,dec_clock_def,state_component_equality]
        ) >>
     TOP_CASE_TAC >>
     fs[CaseEq "option",CaseEq"prod",CaseEq"error_result",CaseEq "result"] >> rveq >> fs[] >>
     simp[PULL_EXISTS,set_var_def]
     >- ((* Rval *)
          conj_tac
            >-
             (Cases_on `handler` >>
              fs[call_env_def,push_env_def,dec_clock_def] >>
              qmatch_asmsub_abbrev_tac `stack_max_fupd(K smnew)` >>
              qmatch_asmsub_abbrev_tac `safe_for_space_fupd(K ssnew)` >>
              fs[pop_env_def,CaseEq"list",CaseEq"stack"] >> rveq >> fs[]
             ) >>
          conj_tac
            >-
             (Cases_on `handler` >>
              fs[call_env_def,push_env_def,dec_clock_def] >>
              qmatch_asmsub_abbrev_tac `stack_max_fupd(K smnew)` >>
              qmatch_asmsub_abbrev_tac `safe_for_space_fupd(K ssnew)` >>
              fs[pop_env_def,CaseEq"list",CaseEq"stack"] >> rveq >> fs[]
             ) >>
          rw [] >>
          Cases_on `handler` >>
          fs[call_env_def,push_env_def,dec_clock_def] >>
          qmatch_goalsub_abbrev_tac `stack_max_fupd(K smnew)` >>
          qmatch_goalsub_abbrev_tac `safe_for_space_fupd(K ssnew)` >>
          qmatch_goalsub_abbrev_tac `stack_fupd(K new_stack)` >>
          first_x_assum(qspecl_then [`new_stack`,`r'`] mp_tac) >>
          qunabbrev_tac `new_stack` >>
          simp[] >>
          strip_tac >>
          drule evaluate_smx_safe_peak_swap_aux >>
          disch_then(qspecl_then [`smnew`,`ssnew`,`s.peak_heap_length`] mp_tac) >>
          simp[] >>
          strip_tac >> fs[] >>
          fs[pop_env_def,CaseEq "list", CaseEq "stack"] >> rveq >>
          simp[state_component_equality] >>
          fs[]
        )
     >- ( (*Raise, no handler *)
          fs[push_env_def,call_env_def,dec_clock_def] >>
          Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS,CONJ_ASSOC] >>
          conj_tac >-
            (qmatch_asmsub_abbrev_tac `stack_max_fupd(K smnew)` >>
             qmatch_asmsub_abbrev_tac `safe_for_space_fupd(K ssnew)` >>
             fs[pop_env_def,CaseEq"list",CaseEq"stack"] >> rveq >> fs[] >>
             fs[jump_exc_def,CaseEq"list",CaseEq"stack"] >>
             Cases_on `s.handler = LENGTH s.stack` >> fs[LASTN_LEMMA] >>
             `s.handler < LENGTH s.stack` by DECIDE_TAC >> fs[] >>
             simp[PULL_EXISTS] >>
             fs[LASTN_CONS] >>
             rpt(PRED_ASSUM is_eq (mp_tac o GSYM)) >>
             rw[]
            ) >>
          rpt strip_tac >>
          qmatch_goalsub_abbrev_tac `evaluate
              (q', s with <|locals:= _; locals_size := _;  stack := _;
                            stack_max := smnew; clock := _;  safe_for_space := ssnew |>)` >>
          first_x_assum(qspecl_then [`Env lsz x'::xs`] mp_tac) >>
          fs[jump_exc_def,CaseEq"list",CaseEq"stack"] >>
          fs[LASTN_CONS] >>
          disch_then(qspec_then `r'` strip_assume_tac) >>
          drule evaluate_smx_safe_peak_swap_aux >>
          disch_then(qspecl_then [`smnew`,`ssnew`,`s.peak_heap_length`] mp_tac) >>
          simp[] >>
          strip_tac >> fs[] >>
          rw[state_component_equality])
     >- ( (* Raise, with handler *)
          rpt(TOP_CASE_TAC >> fs[] >> rveq)
          >- ((* Handler yields NONE*)
              conj_tac >-
                (fs[set_var_def,jump_exc_def,call_env_def,push_env_def,dec_clock_def,
                    LASTN_ALT] >> rveq >> fs[]) >>
              conj_tac >-
                (fs[set_var_def,jump_exc_def,call_env_def,push_env_def,dec_clock_def,
                    LASTN_ALT] >> rveq >> fs[]) >>
              rw[] >> fs[set_var_def] >>
              fs[set_var_def,jump_exc_def,call_env_def,push_env_def,dec_clock_def,
                 LASTN_ALT] >>
              rveq >> fs[] >>
              qmatch_goalsub_abbrev_tac `stack_max_fupd(K smnew)` >>
              qmatch_goalsub_abbrev_tac `safe_for_space_fupd(K ssnew)` >>
              last_x_assum(qspec_then `Exc lsz s2.locals s2.handler::xs` mp_tac) >>
              fs[LASTN_ALT] >>
              disch_then(qspec_then `r'` strip_assume_tac) >>
              drule evaluate_smx_safe_peak_swap_aux >>
              disch_then(qspecl_then [`smnew`,`ssnew`,`s.peak_heap_length`] mp_tac) >>
              simp[] >>
              strip_tac >> simp[] >>
              first_x_assum(qspecl_then [`xs`,`lss`] mp_tac) >>
              impl_tac >- metis_tac[] >>
              strip_tac >>
              drule evaluate_smx_safe_peak_swap_aux >>
              disch_then(qspecl_then [`smx'`,`safe`,`peak`] mp_tac) >>
              simp[] >> strip_tac >> simp[] >>
              simp[state_component_equality])
          >- ((* Handler yields Rval *)
              conj_tac >-
                (fs[set_var_def,jump_exc_def,call_env_def,push_env_def,dec_clock_def,
                    LASTN_ALT] >> rveq >> fs[]) >>
              conj_tac >-
                (fs[set_var_def,jump_exc_def,call_env_def,push_env_def,dec_clock_def,
                    LASTN_ALT] >> rveq >> fs[]) >>
              rw[] >> fs[set_var_def] >>
              fs[set_var_def,jump_exc_def,call_env_def,push_env_def,dec_clock_def,
                 LASTN_ALT] >>
              rveq >> fs[] >>
              qmatch_goalsub_abbrev_tac `stack_max_fupd(K smnew)` >>
              qmatch_goalsub_abbrev_tac `safe_for_space_fupd(K ssnew)` >>
              last_x_assum(qspec_then `Exc lsz s2.locals s2.handler::xs` mp_tac) >>
              fs[LASTN_ALT] >>
              disch_then(qspec_then `r'` strip_assume_tac) >>
              drule evaluate_smx_safe_peak_swap_aux >>
              disch_then(qspecl_then [`smnew`,`ssnew`,`s.peak_heap_length`] mp_tac) >>
              simp[] >>
              strip_tac >> simp[] >>
              first_x_assum(qspecl_then [`xs`,`lss`] mp_tac) >>
              impl_tac >- metis_tac[] >>
              strip_tac >>
              drule evaluate_smx_safe_peak_swap_aux >>
              disch_then(qspecl_then [`smx'`,`safe`,`peak`] mp_tac) >>
              simp[] >> strip_tac >> simp[] >>
              simp[state_component_equality])
          >- ((* Handler yields Rraise *)
              Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS,CONJ_ASSOC] >>
              conj_tac >-
                (fs[set_var_def,jump_exc_def,call_env_def,push_env_def,dec_clock_def,
                    CaseEq "list", CaseEq"stack"] >>
                 rveq >> fs[PULL_EXISTS] >> rveq >> fs[LASTN_ALT]) >>
              rw[] >> fs[set_var_def] >>
              fs[set_var_def,jump_exc_def,call_env_def,push_env_def,dec_clock_def,
                 LASTN_ALT] >>
              rveq >> fs[] >>
              qmatch_goalsub_abbrev_tac `stack_max_fupd(K smnew)` >>
              qmatch_goalsub_abbrev_tac `safe_for_space_fupd(K ssnew)` >>
              last_x_assum(qspec_then `Exc lsz s2.locals s2.handler::xs` mp_tac) >>
              fs[LASTN_ALT] >>
              disch_then(qspec_then `r'` strip_assume_tac) >>
              drule evaluate_smx_safe_peak_swap_aux >>
              disch_then(qspecl_then [`smnew`,`ssnew`,`s.peak_heap_length`] mp_tac) >>
              simp[] >>
              strip_tac >> simp[] >>
              first_x_assum(qspecl_then [`xs`] mp_tac) >>
              rfs[CaseEq "list", CaseEq"stack"] >>
              disch_then(qspec_then `lss` strip_assume_tac) >>
              drule evaluate_smx_safe_peak_swap_aux >>
              disch_then(qspecl_then [`smx'`,`safe`,`peak`] mp_tac) >>
              simp[] >> strip_tac >> simp[] >>
              simp[state_component_equality] >>
              rpt(PRED_ASSUM is_eq (mp_tac o GSYM)) >>
              rw[])
          >- ((* Handler yields timeout *)
              rw[] >> fs[set_var_def] >>
              fs[set_var_def,jump_exc_def,call_env_def,push_env_def,dec_clock_def,
                 LASTN_ALT] >>
              rveq >> fs[] >>
              qmatch_goalsub_abbrev_tac `stack_max_fupd(K smnew)` >>
              qmatch_goalsub_abbrev_tac `safe_for_space_fupd(K ssnew)` >>
              last_x_assum(qspec_then `Exc lsz s2.locals s2.handler::xs` mp_tac) >>
              fs[LASTN_ALT] >>
              disch_then(qspec_then `r'` strip_assume_tac) >>
              drule evaluate_smx_safe_peak_swap_aux >>
              disch_then(qspecl_then [`smnew`,`ssnew`,`s.peak_heap_length`] mp_tac) >>
              simp[] >>
              strip_tac >> simp[] >>
              first_x_assum(qspecl_then [`xs`,`lss`] mp_tac) >>
              impl_tac >- metis_tac[] >>
              strip_tac >>
              drule evaluate_smx_safe_peak_swap_aux >>
              disch_then(qspecl_then [`smx'`,`safe`,`peak`] mp_tac) >>
              simp[] >> strip_tac >> simp[] >>
              simp[state_component_equality])
          >- ((* Handler yields FFI error *)
              rw[] >> fs[set_var_def] >>
              fs[set_var_def,jump_exc_def,call_env_def,push_env_def,dec_clock_def,
                 LASTN_ALT] >>
              rveq >> fs[] >>
              qmatch_goalsub_abbrev_tac `stack_max_fupd(K smnew)` >>
              qmatch_goalsub_abbrev_tac `safe_for_space_fupd(K ssnew)` >>
              last_x_assum(qspec_then `Exc lsz s2.locals s2.handler::xs` mp_tac) >>
              fs[LASTN_ALT] >>
              disch_then(qspec_then `r'` strip_assume_tac) >>
              drule evaluate_smx_safe_peak_swap_aux >>
              disch_then(qspecl_then [`smnew`,`ssnew`,`s.peak_heap_length`] mp_tac) >>
              simp[] >>
              strip_tac >> simp[] >>
              first_x_assum(qspecl_then [`xs`,`lss`] mp_tac) >>
              impl_tac >- metis_tac[] >>
              strip_tac >>
              drule evaluate_smx_safe_peak_swap_aux >>
              disch_then(qspecl_then [`smx'`,`safe`,`peak`] mp_tac) >>
              simp[] >> strip_tac >> simp[] >>
              simp[state_component_equality])
          )
     >- ( (* Error *)
         TOP_CASE_TAC >> fs[] >> rveq >>
         rw [] >>
         Cases_on `handler` >>
         fs[call_env_def,push_env_def,dec_clock_def] >>
         qmatch_goalsub_abbrev_tac `stack_max_fupd (K smnew)` >>
         qmatch_goalsub_abbrev_tac `safe_for_space_fupd (K ssnew)` >>
         qmatch_goalsub_abbrev_tac `stack_fupd (K (el1::_))` >>
         last_x_assum(qspec_then `el1::xs` mp_tac) >>
         qunabbrev_tac `el1` >>
         simp[] >> disch_then(qspec_then `r'` strip_assume_tac) >>
         drule evaluate_smx_safe_peak_swap_aux >>
         disch_then(qspecl_then [`smnew`,`ssnew`,`s.peak_heap_length`] mp_tac) >>
         simp[] >>
         strip_tac >> fs[] >>
         simp[state_component_equality]))
QED

Theorem evaluate_stack_swap:
  !c ^s.
     case evaluate (c,s) of
          | (SOME (Rerr(Rabort Rtype_error)),s1) => T
          | (SOME (Rerr(Rabort a)),s1) => (s1.stack = [])
              /\ (!xs. (LENGTH s.stack = LENGTH xs) ==>
                       ?lss sfs smx phl.
                       evaluate (c,s with stack := xs) =
                         (SOME (Rerr(Rabort a)),s1 with <| locals_size := lss;
                                                           safe_for_space := sfs;
                                                           stack_max := smx;
                                                           peak_heap_length := phl
                                                           |>))
          | (SOME (Rerr (Rraise t)),s1) =>
                (?s2. (jump_exc s = SOME s2) /\ (s2.locals = s1.locals) /\
                      (s2.stack = s1.stack)  /\ (s2.handler = s1.handler) /\
                      (!xs s7. (jump_exc (s with stack := xs) = SOME s7) /\
                               (LENGTH s.stack = LENGTH xs) ==>
                               ?lss sfs smx phl.
                               (evaluate (c,s with stack := xs) =
                                  (SOME (Rerr (Rraise t)),
                                   s1 with <| stack := s7.stack ;
                                              handler := s7.handler ;
                                              locals := s7.locals ;
                                              locals_size := lss;
                                              safe_for_space := sfs ;
                                              stack_max := smx;
                                              peak_heap_length := phl |>))))
          | (res,s1) => (s1.stack = s.stack) /\ (s1.handler = s.handler) /\
                        (!xs. (LENGTH s.stack = LENGTH xs) ==>
                               ?lss sfs smx phl.
                                evaluate (c,s with stack := xs) =
                                  (res, s1 with <| locals_size := lss;
                                                   stack := xs ;
                                                   safe_for_space := sfs;
                                                   stack_max := smx;
                                                   peak_heap_length := phl|>))
Proof
  ntac 2 strip_tac >>
  Q.ISPECL_THEN [`c`,`s`] assume_tac evaluate_stack_and_locals_swap >>
  rpt(PURE_TOP_CASE_TAC >> fs[]) >>
  first_x_assum(qspecl_then [`s.locals_size`] assume_tac o CONV_RULE (RESORT_FORALL_CONV rev)) >>
  FULL_SIMP_TAC std_ss [GSYM state_fupdcanon, s_peak_heap]
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
                                  locals := x.locals ;
                                  locals_size := x.locals_size |>))
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
                                    locals := x.locals ;
                                    locals_size := x.locals_size |>))
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
  \\ every_case_tac \\ full_simp_tac(srw_ss())[call_env_def,flush_state_def,fromList_def]
  \\ imp_res_tac do_app_err >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
  \\ rpt(TOP_CASE_TAC >> fs[] >> rveq)
  \\ fs[markerTheory.Abbrev_def]
  \\ rpt(TOP_CASE_TAC >> fs[] >> rveq));

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
      ?w safe peak sm. (evaluate (c, s with locals := l) =
             (res,if res = NONE
                  then (s2 with <| locals := w;
                                   safe_for_space := safe;
                                   stack_max := sm;
                                   peak_heap_length := peak |>)
                  else s2 with <| safe_for_space := safe;
                                  stack_max := sm;
                                  peak_heap_length := peak |>)) /\
          locals_ok s2.locals w
Proof
  recInduct evaluate_ind \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[evaluate_def]
  (* Skip *)
  >- (rw [state_component_equality])
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
     \\ Cases_on `op_requires_names op` \\ fs [cut_state_opt_def]
     >- (Cases_on `get_vars args s.locals` \\ fs []
        \\ fs [cut_state_opt_def]
        \\ IMP_RES_TAC locals_ok_get_vars \\ fs []
        \\ fs [do_app_with_locals]
        \\ fs [case_eq_thms,semanticPrimitivesTheory.result_case_eq,AllCaseEqs()]
        \\ fs [call_env_def,set_var_def,flush_state_def, state_component_equality]
        \\ fs [locals_ok_def,lookup_insert] \\ rw []
        \\ rpt (qpat_x_assum `insert _ _ _ = _` (assume_tac o GSYM))
        \\ rpt (qpat_x_assum `fromList [] = _` (assume_tac o GSYM))
        \\ fs [lookup_insert] \\ rfs []
        \\ imp_res_tac do_app_const \\ fs [fromList_def,lookup_def]
        \\ fs[do_stack_def]
        >> metis_tac [])
     \\ fs [cut_state_def]
     \\ Cases_on `cut_env x s.locals` \\ fs[]
     \\ IMP_RES_TAC locals_ok_cut_env \\ fs[]
     \\ TOP_CASE_TAC >> rw[state_component_equality,locals_ok_def]
     \\ metis_tac[])
   (* Tick *)
  >- (Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
     \\ fs[locals_ok_def,call_env_def,EVAL ``fromList []``,lookup_def, dec_clock_def, flush_state_def]
     \\ MAP_EVERY (TRY o Q.EXISTS_TAC) [`l`,`s.safe_for_space`,`s.peak_heap_length`]
     \\ rw [state_component_equality])
  (* MakeSpace *)
  >- (Cases_on `cut_env names s.locals` \\ full_simp_tac(srw_ss())[]
     \\ IMP_RES_TAC locals_ok_cut_env
     \\ full_simp_tac(srw_ss())[LET_DEF,add_space_def,state_component_equality,locals_ok_def, flush_state_def])
  (* Raise *)
  >- (Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
     \\ `jump_exc (s with locals := l) = jump_exc s`
        by full_simp_tac(srw_ss())[jump_exc_def]
     \\ Cases_on `jump_exc s` \\ full_simp_tac(srw_ss())[]
     \\ `get_var n l = SOME x` by
          full_simp_tac(srw_ss())[locals_ok_def,get_var_def] \\ full_simp_tac(srw_ss())[]
     \\ srw_tac [] [] \\ Q.EXISTS_TAC `s2.locals`
     \\ full_simp_tac(srw_ss())[locals_ok_def,state_component_equality, flush_state_def])
  (* Return *)
  >- (Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
     \\ `get_var n l = SOME x` by
          full_simp_tac(srw_ss())[locals_ok_def,get_var_def] \\ full_simp_tac(srw_ss())[]
     \\ srw_tac [] [call_env_def]
     \\ simp[locals_ok_def,lookup_fromList,state_component_equality, flush_state_def] >> metis_tac [])
  (* Seq *)
  >- (Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[LET_DEF]
     \\ Cases_on `q = SOME (Rerr(Rabort Rtype_error))` \\ full_simp_tac(srw_ss())[]
     \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ full_simp_tac(srw_ss())[]
     \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
     \\ Cases_on `q` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ TRY (metis_tac [] \\ NO_TAC)
     \\ qpat_x_assum `∀l. bb` drule \\ rw []
     \\ drule evaluate_smx_safe_peak_swap
     \\ disch_then (qspecl_then [`sm`,`safe`,`peak`] assume_tac)
     \\ fs []
     \\ IF_CASES_TAC \\ rw[state_component_equality]
     \\ qexists_tac `s2.locals` >> rw[locals_ok_def])
  (* If *)
  >- (Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[]
     \\ IMP_RES_TAC locals_ok_get_var \\ full_simp_tac(srw_ss())[]
     \\ Cases_on `isBool T x` \\ full_simp_tac(srw_ss())[]
     \\ Cases_on `isBool F x` \\ full_simp_tac(srw_ss())[])
  (* Call *)
  >- (Cases_on `get_vars args s.locals` \\ fs []
     \\ IMP_RES_TAC locals_ok_get_vars \\ fs []
     \\ Cases_on `find_code dest x s.code s.stack_frame_sizes` \\ fs []
     \\ Cases_on `x'` \\ fs []
     \\ Cases_on `r` \\ fs []
     \\ Cases_on `ret` \\ fs []
     >- (Cases_on `handler` \\ fs []
         \\ Cases_on `s.clock = 0` \\ fs [] \\ SRW_TAC [] []
         \\ `call_env q r' (dec_clock (s with locals := l)) =
             call_env q r' (dec_clock s)`
            by fs[state_component_equality,dec_clock_def,call_env_def, flush_state_def]
         \\ fs[]
         \\ fs[call_env_def,locals_ok_def,lookup_def,fromList_def, flush_state_def]
         >- fs [state_component_equality]
         \\ Q.EXISTS_TAC `s2.locals`
         \\ Q.EXISTS_TAC `s2.safe_for_space`
         \\ Q.EXISTS_TAC `s2.peak_heap_length`
         \\ Q.EXISTS_TAC `s2.stack_max`
         \\ full_simp_tac(srw_ss())[locals_ok_refl]
         \\ SRW_TAC [] [state_component_equality])
     \\ Cases_on `x'` \\ fs []
     \\ Cases_on `cut_env r s.locals` \\ full_simp_tac(srw_ss())[]
     \\ IMP_RES_TAC locals_ok_cut_env \\ full_simp_tac(srw_ss())[]
     \\ `call_env q r' (push_env x' (IS_SOME handler)
           (dec_clock (s with locals := l))) =
         call_env q r' (push_env x' (IS_SOME handler)
           (dec_clock s))`
        by (Cases_on `handler`
           \\ fs[state_component_equality,dec_clock_def,call_env_def,push_env_def, flush_state_def])
     \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
     \\ full_simp_tac(srw_ss())[call_env_def,locals_ok_def,lookup_def,fromList_def,flush_state_def]
     \\ full_simp_tac(srw_ss())[]
     >- rw [state_component_equality]
     \\ MAP_EVERY Q.EXISTS_TAC [`s2.locals`,`s2.safe_for_space`,`s2.peak_heap_length`,
                                `s2.stack_max`]
     \\ rw [state_component_equality])
QED

Theorem funpow_dec_clock_clock:
   !n s. FUNPOW dataSem$dec_clock n s = (s with clock := s.clock - n)
Proof
  Induct_on `n` >>
  srw_tac[][FUNPOW, state_component_equality, dataSemTheory.dec_clock_def, ADD1] >>
  decide_tac
QED

Theorem evaluate_mk_ticks:
   !p s n.
    evaluate (mk_ticks n p, s)
    =
    if s.clock < n then
      (SOME (Rerr(Rabort Rtimeout_error)),
       s with <| clock := 0; locals := fromList []; stack := [];
                 locals_size := SOME 0|>)
    else
      evaluate (p, FUNPOW dec_clock n s)
Proof
  Induct_on `n` >>
  srw_tac[][ mk_ticks_def, FUNPOW] >>
  full_simp_tac(srw_ss())[mk_ticks_def, evaluate_def] >>
  srw_tac[][funpow_dec_clock_clock, dec_clock_def] >>
  simp [call_env_def,flush_state_def] >>
  `s.clock - n = 0` by decide_tac >>
  `s.clock - (n+1) = 0` by decide_tac >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[ADD1, LESS_OR_EQ] >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  rw[fromList_def]
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
    ((FUNPOW dec_clock n t).stack_frame_sizes = t.stack_frame_sizes) /\
    ((FUNPOW dec_clock n t).locals_size = t.locals_size) /\
    ((FUNPOW dec_clock n t).clock = t.clock - n)
Proof
  Induct_on `n` \\ full_simp_tac(srw_ss())[FUNPOW_SUC,dec_clock_def] \\ DECIDE_TAC
QED

Theorem jump_exc_NONE:
    (jump_exc (t with locals := x) = NONE <=> jump_exc t = NONE) /\
    (jump_exc (t with clock := c) = NONE <=> jump_exc t = NONE) /\
    (jump_exc (t with stack_max := sm) = NONE <=> jump_exc t = NONE) /\
    (jump_exc (t with locals_size := ls) = NONE <=> jump_exc t = NONE) /\
    (jump_exc (t with safe_for_space := safe) = NONE <=> jump_exc t = NONE)
Proof
  FULL_SIMP_TAC (srw_ss()) [jump_exc_def] \\ REPEAT STRIP_TAC
  \\ every_case_tac \\ FULL_SIMP_TAC std_ss []
QED

Theorem jump_exc_IMP:
   (jump_exc s = SOME t) ==>
    s.handler < LENGTH s.stack /\
    ?n e ls xs. (LASTN (s.handler + 1) s.stack = Exc ls e n::xs) /\
                (t = s with <|handler := n; locals_size := ls; locals := e; stack := xs|>)
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

Theorem space_consumed_with_clock:
  !s op vs. space_consumed (s with clock := z) op vs = space_consumed s op vs
Proof
  ho_match_mp_tac space_consumed_ind \\ rpt strip_tac
  \\ simp [space_consumed_def]
QED

Theorem do_app_with_clock:
  do_app op vs (s with clock := z) =
   map_result (λ(x,y). (x,y with clock := z)) I (do_app op vs s)
Proof
  Cases_on `op = Install` THEN1
   (fs [do_app_def,do_stack_def,do_install_def]
    \\ every_case_tac \\ fs []
    \\ pairarg_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs []) >>
  Cases_on `do_app op vs s` >>
  fs[do_app_def,do_stack_def,do_space_def] >>
  Cases_on `op` >> TRY (rename [‘EqualConst cc’] \\ Cases_on ‘cc’) >>
  ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,stack_consumed_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,space_consumed_with_clock,
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
   (fs [do_app_def,do_stack_def,do_install_def]
    \\ every_case_tac \\ fs []
    \\ pairarg_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs []) >>
  srw_tac[][do_app_def,do_stack_def,do_space_def] >>
  Cases_on `op` >> TRY (rename [‘EqualConst cc’] \\ Cases_on ‘cc’) >>
  ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,stack_consumed_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,space_consumed_with_clock,
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
   (fs [do_app_def,do_stack_def,do_install_def]
    \\ every_case_tac \\ fs []
    \\ pairarg_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs []) >>
  srw_tac[][do_app_def,do_stack_def,do_space_def] >>
  Cases_on `op` >> TRY (rename [‘EqualConst cc’] \\ Cases_on ‘cc’) >>
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
     \\ rveq \\ fs [call_env_def,flush_state_def,do_app_with_clock,do_app_with_locals]
     \\ imp_res_tac do_app_const \\ fs [set_var_def,state_component_equality]
     \\ PairCases_on `y` \\ fs []
     \\ qpat_x_assum `v4 = _` (fn th => once_rewrite_tac [th]) \\ fs []
     \\ imp_res_tac do_app_const
     \\ fs[do_stack_def]
     \\ fs [set_var_def,state_component_equality]
     (* FIX: this is obnoxious *)
     \\ qmatch_goalsub_abbrev_tac `size_of_heap f1`
     \\ qpat_abbrev_tac `f2 = (s with locals := _)`
     \\ `size_of_heap f1 = size_of_heap f2`
         by(`f1 = f2 with clock := ck + s.clock`
              by rw [Abbr `f1`,Abbr `f2`,state_component_equality]
            \\ rw [size_of_heap_with_clock])
     \\ `space_consumed f1 = space_consumed f2`
         by(`f1 = f2 with clock := ck + s.clock`
              by rw [Abbr `f1`,Abbr `f2`,state_component_equality]
            \\ rw []
            \\ metis_tac[space_consumed_with_clock])
     \\ rw[])
  >- (EVAL_TAC >> simp[state_component_equality])
  >- (every_case_tac >> fs[] >> srw_tac[][]
     \\ fs [add_space_def,size_of_heap_def,stack_to_vs_def]
     \\ rw [state_component_equality,size_of_heap_with_clock])
  >- (every_case_tac >> fs[] >> srw_tac[][] >> fs[jump_exc_NONE]
     \\ imp_res_tac jump_exc_IMP >> fs[]
     \\ srw_tac[][] >> fs[jump_exc_def])
  >- (every_case_tac >> fs[] >> srw_tac[][call_env_def,flush_state_def] >>
      unabbrev_all_tac >> srw_tac[][])
  >- (fs[LET_THM]
     \\ pairarg_tac >> fs[]
     \\ every_case_tac >> fs[] >> srw_tac[][]
     \\ rfs[] >> srw_tac[][])
  >- (every_case_tac >> fs[] >> srw_tac[][])
  >- (every_case_tac >> fs[] >> srw_tac[][] >> rfs[]
     \\ fsrw_tac[ARITH_ss][call_env_def,flush_state_def,dec_clock_def,push_env_def,pop_env_def,set_var_def,LET_THM]
     \\ TRY(first_x_assum(qspec_then`ck`mp_tac) >> simp[]
                         \\ every_case_tac >> fs[] >> srw_tac[][] >> rfs[] >> fs[]
                         \\ spose_not_then strip_assume_tac >> fs[] \\ NO_TAC)
     \\ every_case_tac >> fs[] >> rfs[] >> rveq >> fs[] >> rfs[]
     \\ TRY(first_x_assum(qspec_then`ck`mp_tac) >> simp[]
                         \\ every_case_tac >> fs[] >> srw_tac[][] >> rfs[] >> fs[]
                         \\ spose_not_then strip_assume_tac >> fs[] \\ NO_TAC))
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
   (fs [do_app_def,do_stack_def,do_install_def]
    \\ every_case_tac \\ fs []
    \\ pairarg_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs []) >>
  srw_tac[][do_app_def,do_stack_def,do_space_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  Cases_on `x` >> TRY (rename [‘EqualConst cc’] >> Cases_on ‘cc’) >>
  ntac 2 (fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
              bool_case_eq,ffiTheory.call_FFI_def,
              with_fresh_ts_def,closSemTheory.ref_case_eq,
              ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
              semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
              pair_case_eq,consume_space_def,check_lim_def] >>
  rveq >> fs [])
QED

Theorem call_env_const[simp]:
   (call_env x s y).ffi = y.ffi ∧
   (call_env x s y).clock = y.clock
Proof
  EVAL_TAC
QED

Theorem call_env_with_const:
   (call_env x s (y with clock := z)) = call_env x s y with clock := z
Proof
  EVAL_TAC
QED

Theorem dec_clock_const[simp]:
   (dec_clock s).ffi = s.ffi ∧
   (dec_clock s).code = s.code ∧
   (dec_clock s).compile_oracle = s.compile_oracle ∧
   (dec_clock s).compile = s.compile ∧
   (dec_clock s).refs = s.refs ∧
   (dec_clock s).global = s.global
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
   (push_env x y z).clock = z.clock ∧
   (push_env x y z).code = z.code ∧
   (push_env x y z).compile_oracle = z.compile_oracle ∧
   (push_env x y z).compile = z.compile ∧
   (push_env x y z).refs = z.refs ∧
   (push_env x y z).global = z.global
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
   b.ffi = a.ffi /\
   b.stack_max = a.stack_max
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
  TRY every_case_tac >> fs[flush_state_def] >> rveq >>
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
         \\ srw_tac[][] >> fs[set_var_with_const,flush_state_def]
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
  \\ fs [] >> imp_res_tac jump_exc_IMP >> rw[jump_exc_NONE,flush_state_def]
  \\ metis_tac[evaluate_io_events_mono,IS_PREFIX_TRANS,SND,PAIR]
QED

Theorem semantics_Div_IMP_LPREFIX:
  semantics ffi prog co cc lim ss start = Diverge l ==> LPREFIX (fromList ffi.io_events) l
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
    \\ CASE_TAC >> fs[]
    \\ CASE_TAC >> fs[flush_state_def] )
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
  semantics ffi prog co cc lim ss start = Terminate tt l ==> ffi.io_events ≼ l
Proof
  simp[semantics_def] \\ IF_CASES_TAC \\ fs[]
  \\ DEEP_INTRO_TAC some_intro \\ fs[] \\ rw[]
  \\ imp_res_tac evaluate_io_events_mono \\ fs[]
QED

Theorem Resource_limit_hit_implements_semantics:
  implements {Terminate Resource_limit_hit ffi.io_events}
       {semantics ffi (fromAList prog) co cc lim ss start}
Proof
  fs [implements_def,extend_with_resource_limit_def]
  \\ Cases_on `semantics ffi (fromAList prog) co cc lim ss start` \\ fs []
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
  \\ fs [case_eq_thms,AllCaseEqs()] \\ rveq \\ fs []
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
  Cases_on `op` \\ TRY (rename [‘EqualConst cc’] \\ Cases_on ‘cc’) \\
  fs [do_app_aux_def,list_case_eq,option_case_eq,v_case_eq,
      bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_stack_def,do_space_def,
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
  \\ fs [] \\ rveq \\ fs [set_var_def,call_env_def,flush_state_def,dec_clock_def,add_space_def]
  \\ imp_res_tac do_app_safe_for_space_mono
  \\ TRY pairarg_tac \\ fs [CaseEq"bool"]
  \\ fs [] \\ rveq \\ fs [set_var_def,call_env_def,flush_state_def,dec_clock_def,add_space_def,
       CaseEq"option",pair_case_eq,push_env_def,CaseEq"result"]
  \\ fs [] \\ rveq \\ fs [set_var_def,call_env_def,flush_state_def,dec_clock_def,add_space_def,
       CaseEq"option",pair_case_eq,push_env_def,CaseEq"result"]
  \\ TRY (Cases_on `IS_SOME handler`)
  \\ fs [] \\ rveq \\ fs [set_var_def,call_env_def,flush_state_def,dec_clock_def,add_space_def,
       CaseEq"option",pair_case_eq,push_env_def]
  \\ fs [pop_env_def,CaseEq"stack",CaseEq"list",CaseEq"error_result",
         option_case_eq,pair_case_eq] \\ rveq \\ fs []
QED

Definition zero_limits_def   :
  zero_limits = <| heap_limit := 0;
                   length_limit := 0;
                   stack_limit := 0 |> :dataSem$limits
End



Theorem evaluate_swap_limits:
  ∀c s r s' limits.
   evaluate (c,s) = (r,s') ⇒
   ?smx safe peak.
     evaluate (c,s with limits := limits) = (r,s' with <|limits := limits;
                                                         stack_max := smx;
                                                         safe_for_space := safe;
                                                         peak_heap_length := peak|>)
Proof
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  >- basic_tac
  >- basic_tac
  (* Assign *)
  >- (
     fs [evaluate_def]
     \\ full_cases >> full_fs
     \\ fs [] \\ rfs[]
     \\ rveq \\ fs []
     \\ every_case_tac \\ fs [] \\ rveq \\ fs []
     \\ TRY (fs [state_component_equality] >> metis_tac [] \\ NO_TAC)
     \\ TRY (drule do_app_lim_swap
     \\ disch_then (qspecl_then [`limits'`] assume_tac)
     \\ fs [] \\ metis_tac [] \\ NO_TAC)
     \\ TRY (drule do_app_err_lim_swap
     \\ disch_then (qspecl_then [`limits'`] assume_tac)
     \\ fs [state_component_equality] \\ metis_tac [] \\ NO_TAC))
  (*  Tick *)
  >- (fs [evaluate_def]
     \\ full_cases >>  full_fs
     \\ rveq \\ fs []
     \\ every_case_tac
     \\ rw[state_component_equality])
  >- basic_tac
  >- basic_tac
  >- basic_tac
  (* Seq *)
  >- (fs[evaluate_def,ELIM_UNCURRY]
     \\ Cases_on `evaluate (c1,s)`
     \\ rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq)
     \\ rpt(first_x_assum(qspec_then `limits'` mp_tac))
     \\ rw[] >> fs[]
     \\ qpat_x_assum `evaluate(c2,_) = _` assume_tac
     \\ drule_then (qspecl_then [`smx'`,`safe'`,`peak'`] strip_assume_tac)
                   evaluate_smx_safe_peak_swap
     \\ fs[]
     \\ rw[state_component_equality])
  >- basic_tac
  (* Call *)
  >> fs [evaluate_def]
  >> Cases_on `get_vars args s.locals` >> fs [] >> rveq >> fs []
  >- rw[state_component_equality]
  >> Cases_on `find_code dest x s.code s.stack_frame_sizes` >> fs []
  >- rw[state_component_equality]
  >> Cases_on `x'` >> fs []
  >> Cases_on `r'` >> fs []
  >> Cases_on `ret` >> fs []
  >- (Cases_on `handler` >> fs []
      >- (Cases_on `s.clock = 0` >> fs []
          >- fs [flush_state_def, state_component_equality]
          >> fs [dec_clock_def]
          >> Cases_on ` evaluate (q',call_env q r'' (s with clock := s.clock − 1))`
          >> fs [call_env_def] >> Cases_on `q''` >> fs [] >> rveq
          >> first_x_assum(qspec_then `limits'` strip_assume_tac)
          >> qpat_abbrev_tac `smnew = OPTION_MAP2 MAX _ _`
          >> qpat_abbrev_tac `ssnew = (_ /\ _)`
          >> drule_then (qspecl_then [`smnew`,`ssnew`,`s.peak_heap_length`] strip_assume_tac)
              evaluate_smx_safe_peak_swap
          >> fs[] >> rw[state_component_equality])
      >> rw[state_component_equality])
  (* returning call *)
   >> Cases_on `x'` >> fs []
   >> Cases_on `cut_env r' s.locals` >> fs []
   >- rw[state_component_equality]
   >> Cases_on `s.clock = 0` >> fs []
   (* calling the environment here, when s = 0 *)
   >- (Cases_on `handler` >>
       fs [push_env_def, call_env_def, dec_clock_def] >>
       rveq >> rw[state_component_equality])
      (* when clock is not zero *)
   >> Cases_on `handler`
   >> fs [push_env_def, call_env_def, dec_clock_def]
   >> fs[CaseEq "option", CaseEq "prod", CaseEq"result", CaseEq "error_result",
         PULL_EXISTS] >>
   rveq >>
   qmatch_goalsub_abbrev_tac `stack_max_fupd(K smnew)` >>
   qmatch_goalsub_abbrev_tac `safe_for_space_fupd(K ssnew)` >>
   res_tac >>
   first_x_assum(qspec_then `limits'` strip_assume_tac) >>
   drule_then(qspecl_then [`smnew`,`ssnew`,`s.peak_heap_length`] strip_assume_tac)
    evaluate_smx_safe_peak_swap >> fs[] >>
   simp[set_var_def] >> rw[state_component_equality] >>
   fs[pop_env_def,CaseEq"list",CaseEq"stack"] >> rveq >> fs[] >>
   res_tac >>
   first_x_assum(qspec_then `limits'` strip_assume_tac) >>
   drule_then(qspecl_then [`smx'`,`safe'`,`peak'`] strip_assume_tac) evaluate_smx_safe_peak_swap >>
   fs[set_var_def] >> rw[state_component_equality]
QED

Theorem evaluate_zero_limits_FST[local]:
  ∀c s r s'.
   FST(evaluate (c,s)) =
   FST(evaluate (c,s with limits := zero_limits))
Proof
  rw[] >>
  Cases_on `evaluate (c,s)` >>
  metis_tac[FST,evaluate_swap_limits]
QED

Theorem evaluate_zero_limits_ffi[local]:
  ∀c s r s'.
   (SND(evaluate (c,s))).ffi =
   (SND(evaluate (c,s with limits := zero_limits))).ffi
Proof
  rw[] >>
  Cases_on `evaluate (c,s)` >>
  drule_then(qspec_then `zero_limits` strip_assume_tac) evaluate_swap_limits >>
  rw[]
QED

(* Stack frames equal up-to size component*)
Definition stack_frame_size_rel_def:
  (stack_frame_size_rel (Exc opt spt num) (Exc opt' spt' num') <=>
    spt = spt' /\ num = num') /\
  (stack_frame_size_rel (Env opt spt) (Env opt' spt') <=>
    spt = spt') /\
  (stack_frame_size_rel _ _ <=> F)
End

Theorem find_code_upto_size:
  (find_code dest x code sizes = foo)
   ==>
   ?other_size.
   find_code dest x code other_sizes = OPTION_MAP (λ(args,exp,size). (args,exp,other_size)) foo
Proof
  Cases_on `dest` >> rw[find_code_def,CaseEq "option",CaseEq "prod",CaseEq "v"] >> rw[]
QED



Theorem do_app_stack_eq:
  ∀op vs s q s'. do_app op vs s = Rval (q,s')  ==>
   s.stack = s'.stack
Proof
 do_app_swap_tac
QED


Theorem do_app_stack_frame_size_rel:
  ∀op vs s q s' stk. do_app op vs s = Rval (q,s')  /\
    LIST_REL stack_frame_size_rel s.stack stk ==>
      LIST_REL stack_frame_size_rel s'.stack stk
Proof
  metis_tac[do_app_stack_eq]
QED

val basics_tac = fs [evaluate_def]
                 \\ every_case_tac
                 \\ full_fs
                 \\ fs [state_component_equality]
                 \\ rfs[];

Theorem evaluate_swap_stack_frame_sizes_aux[local]:
  ∀c s r s' xs lsz sfs.
   evaluate (c,s) = (r,s') /\ LIST_REL stack_frame_size_rel s.stack xs
   ⇒
   let s0 = s with <|locals_size := lsz; stack := xs; stack_frame_sizes := sfs|>
   in
   ?xs lsz smx safe peak sfs'.
     (evaluate (c,s0) = (r,s' with <|locals_size := lsz;
                                     safe_for_space := safe;
                                     stack := xs;
                                     stack_frame_sizes := sfs';
                                     stack_max := smx;
                                     peak_heap_length := peak|>) /\
      LIST_REL stack_frame_size_rel s'.stack xs)
Proof
  PURE_REWRITE_TAC[LET_THM] >>
  CONV_TAC(DEPTH_CONV BETA_CONV) >>
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  >- basics_tac
  >- basics_tac
  (* Assign *)
  >- (fs [evaluate_def]
     \\ full_cases >> full_fs
     \\ fs [] \\ rfs[]
     \\ rveq \\ fs []
     \\ every_case_tac \\ fs [] \\ rveq \\ fs []
     \\ TRY (fs [state_component_equality] \\ metis_tac [] \\ NO_TAC)
     \\ TRY (drule do_app_lss_stk_stfrm_swap
     \\ disch_then (qspecl_then [`lsz`, `xs`, `sfs`] assume_tac)
     \\ fs [state_component_equality]
     \\ match_mp_tac do_app_stack_frame_size_rel \\ asm_exists_tac \\ fs [] \\ NO_TAC)
     \\ TRY (drule do_app_err_lss_stk_stfrm_swap
     \\ disch_then (qspecl_then [`lsz`, `xs`, `sfs`] assume_tac)
     \\ fs [state_component_equality] \\ NO_TAC))
  (*  Tick *)
  >- (fs [evaluate_def]
     \\ full_cases >>  full_fs
     \\ rveq \\ fs []
     \\ every_case_tac
     \\ rw[state_component_equality])
  >- basics_tac
  >- (basics_tac >>
      imp_res_tac LIST_REL_LENGTH >>
      `LIST_REL stack_frame_size_rel (LASTN (s.handler+1) s.stack) (LASTN (s.handler+1) xs)`
        by(match_mp_tac list_rel_lastn \\ rw[]) >>
      fs[CaseEq"list",CaseEq"stack"] >> rfs[stack_frame_size_rel_def] >>
      fs[] >> rveq >> fs[stack_frame_size_rel_def])
  >- basics_tac
  (* Seq *)
  >- (fs[evaluate_def,ELIM_UNCURRY]
     \\ Cases_on `evaluate (c1,s)`
     \\ rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq)
     \\ first_x_assum (drule_then strip_assume_tac)
     \\ first_x_assum(qspecl_then [`lsz`,`sfs`] strip_assume_tac)
     \\ fs[]
     \\ first_x_assum (drule_then strip_assume_tac)
     \\ rename1 `locals_size_fupd (K newlsz)`
     \\ first_x_assum(qspecl_then [`newlsz`,`sfs''`] strip_assume_tac)
     \\ drule_then(qspecl_then [`smx`,`safe`,`peak`] strip_assume_tac) evaluate_smx_safe_peak_swap
     \\ fs[]
     \\ rw[state_component_equality])
  >- basics_tac
  (* Call *)
  >> fs [evaluate_def]
  >> Cases_on `get_vars args s.locals` >> fs [] >> rveq >> fs []
  >- rw[state_component_equality]
  >> Cases_on `find_code dest x s.code s.stack_frame_sizes` >> fs []
  >- (rveq >>
      drule_then (qspec_then `sfs` strip_assume_tac) find_code_upto_size >>
      rw[state_component_equality])
  >> drule_then (qspec_then `sfs` strip_assume_tac) find_code_upto_size
  >> Cases_on `x'` >> fs []
  >> Cases_on `r'` >> fs []
  >> Cases_on `ret` >> fs []
  >- (Cases_on `handler` >> fs []
      >- (Cases_on `s.clock = 0` >> fs []
          >- (fs [flush_state_def, state_component_equality] >>
              match_mp_tac EVERY2_refl >>
              Cases >> rw[stack_frame_size_rel_def])
          >> fs [dec_clock_def]
          >> Cases_on ` evaluate (q',call_env q r'' (s with clock := s.clock − 1))`
          >> fs [call_env_def] >> Cases_on `q''` >> fs [] >> rveq
          >> res_tac
          >> first_x_assum(qspecl_then [`sfs`,`other_size`] strip_assume_tac)
          >> qpat_abbrev_tac `smnew = OPTION_MAP2 MAX _ _`
          >> qpat_abbrev_tac `ssnew = (_ /\ _)`
          >> drule_then (qspecl_then [`smnew`,`ssnew`,`s.peak_heap_length`] strip_assume_tac) evaluate_smx_safe_peak_swap
          >> fs[] >> rw[state_component_equality])
      >> rw[state_component_equality])
  (* returning call *)
   >> Cases_on `x'` >> fs []
   >> Cases_on `cut_env r' s.locals` >> fs []
   >- rw[state_component_equality]
   >> Cases_on `s.clock = 0` >> fs []
   (* calling the environment here, when s = 0 *)
   >- (Cases_on `handler` >>
       fs [push_env_def, call_env_def, dec_clock_def] >>
       rveq >> rw[state_component_equality] >>
       imp_res_tac LIST_REL_LENGTH >> rw[])
      (* when clock is not zero *)
   >> Cases_on `handler`
   >> fs [push_env_def, call_env_def, dec_clock_def]
   >> fs[CaseEq "option", CaseEq "prod", CaseEq"result", CaseEq "error_result",
         PULL_EXISTS] >>
   rveq >>
   qmatch_goalsub_abbrev_tac `stack_max_fupd(K smnew)` >>
   qmatch_goalsub_abbrev_tac `safe_for_space_fupd(K ssnew)` >>
   qmatch_goalsub_abbrev_tac `stack_fupd(K(topstack::_))` >>
   first_x_assum drule >>
   disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV rev)) >>
   disch_then(qspecl_then [`xs`,`topstack`] mp_tac) >>
   simp[Abbr `topstack`,stack_frame_size_rel_def] >>
   disch_then(qspecl_then [`sfs`,`other_size`] strip_assume_tac) >>
   drule_then(qspecl_then [`smnew`,`ssnew`,`s.peak_heap_length`] strip_assume_tac) evaluate_smx_safe_peak_swap >> fs[] >>
   simp[set_var_def] >> rw[state_component_equality] >>
   imp_res_tac LIST_REL_LENGTH >> fs[] >>
   fs[pop_env_def,CaseEq"list",CaseEq"stack"] >> rveq >> fs[] >>
   TRY(rfs[] >> Cases_on `y` >> fs[stack_frame_size_rel_def] >> NO_TAC) >>
   fs[set_var_def] >>
   first_x_assum drule >>
   disch_then(qspecl_then [`lsz'`,`sfs''`] strip_assume_tac) >>
   drule_then(qspecl_then [`smx'`,`safe'`,`peak'`] strip_assume_tac) evaluate_smx_safe_peak_swap >> fs[] >>
   simp[set_var_def] >> rw[state_component_equality]
QED

Theorem evaluate_swap_local_sizes:
  ∀c s r s' lss.
   evaluate (c,s) = (r,s')
   ⇒
   ?xs lsz sfs smx safe peak.
     (evaluate (c,s with locals_size := lss ) =
        (r,s' with <|locals_size := lsz;
                     safe_for_space := safe;
                     stack := xs;
                     stack_frame_sizes := sfs;
                     stack_max := smx;
                     peak_heap_length := peak|>) /\
      LIST_REL stack_frame_size_rel s'.stack xs)
Proof
 rpt strip_tac
 \\ dxrule evaluate_swap_stack_frame_sizes_aux
 \\ disch_then(qspecl_then [`s.stack`,`lss`,`s.stack_frame_sizes`] mp_tac)
 \\ impl_tac >-
   (match_mp_tac EVERY2_refl >> Cases >> rw[stack_frame_size_rel_def])
 \\ rw[]
 \\ `stack_frame_sizes_fupd (K s.stack_frame_sizes) s = s`
    by fs [state_component_equality]
 \\ fs []
 \\ `stack_fupd (K s.stack) s = s`
    by fs [state_component_equality]
 \\ fs [] \\ rw[state_component_equality]
QED

Theorem evaluate_swap_stack_frame_sizes:
  ∀c s r s' sfs.
   evaluate (c,s) = (r,s')
   ⇒
   ?xs lsz smx safe peak sfs'.
     (evaluate (c,s with stack_frame_sizes := sfs) = (r,s' with <|locals_size := lsz;
                                     safe_for_space := safe;
                                     stack := xs;
                                     stack_frame_sizes := sfs';
                                     stack_max := smx;
                                     peak_heap_length := peak|>) /\
      LIST_REL stack_frame_size_rel s'.stack xs)
Proof
 rpt strip_tac >>
 dxrule evaluate_swap_stack_frame_sizes_aux >>
 disch_then(qspecl_then [`s.stack`,`s.locals_size`,`sfs`] mp_tac) >>
 impl_tac >-
   (match_mp_tac EVERY2_refl >> Cases >> rw[stack_frame_size_rel_def]) >>
 rw[] >>
 qsuff_tac `s with <|locals_size := s.locals_size; stack := s.stack;
                     stack_frame_sizes := sfs|> =
            s with stack_frame_sizes := sfs`
 >- metis_tac[] >>
 rw[state_component_equality]
QED

Theorem evaluate_stack_frame_sizes_FST[local]:
  ∀c s r s'.
   FST(evaluate (c,s)) =
   FST(evaluate (c,s with stack_frame_sizes := LN))
Proof
  rw[] >>
  Cases_on `evaluate (c,s)` >>
  metis_tac[FST,evaluate_swap_stack_frame_sizes]
QED

Theorem evaluate_stack_frame_sizes_ffi[local]:
  ∀c s r s'.
   (SND(evaluate (c,s))).ffi =
   (SND(evaluate (c,s with stack_frame_sizes := LN))).ffi
Proof
  rw[] >>
  Cases_on `evaluate (c,s)` >>
  drule_then(qspec_then `LN` strip_assume_tac) evaluate_swap_stack_frame_sizes >>
  rw[]
QED

Theorem semantics_zero_limits:
  dataSem$semantics ffi code co cc lim ss start =
  dataSem$semantics ffi code co cc zero_limits LN start
Proof
  rw[semantics_def,initial_state_def] >>
  fs[Once evaluate_zero_limits_FST, Once evaluate_stack_frame_sizes_FST,
     Once evaluate_zero_limits_ffi, Once evaluate_stack_frame_sizes_ffi] >>
  TRY(every_case_tac >> fs[] >>
      fs[Once evaluate_zero_limits_FST, Once evaluate_stack_frame_sizes_FST,
      Once evaluate_zero_limits_ffi, Once evaluate_stack_frame_sizes_ffi] >>
      first_x_assum(qspec_then `k` assume_tac) >> rfs[] >> NO_TAC) >>
  rw[some_def]
  >- (AP_TERM_TAC >>
      rw[FUN_EQ_THM] >>
      rpt(pop_assum kall_tac) >>
      rw[EQ_IMP_THM]
      >- (dxrule_then(qspec_then `LN` strip_assume_tac) evaluate_swap_stack_frame_sizes >>
          dxrule_then(qspec_then `zero_limits` strip_assume_tac) evaluate_swap_limits >>
          fs[] >>
          goal_assum drule >> rw[])
      >- (dxrule_then(qspec_then `ss` strip_assume_tac) evaluate_swap_stack_frame_sizes >>
          dxrule_then(qspec_then `lim` strip_assume_tac) evaluate_swap_limits >>
          fs[] >>
          goal_assum drule >> rw[]))
  >- (fs[] >>
      rpt(first_x_assum(qspec_then `k` strip_assume_tac)) >>
      dxrule_then(qspec_then `LN` strip_assume_tac) evaluate_swap_stack_frame_sizes >>
      dxrule_then(qspec_then `zero_limits` strip_assume_tac) evaluate_swap_limits >>
      fs[])
  >- (fs[] >>
      rpt(first_x_assum(qspec_then `k` strip_assume_tac)) >>
      dxrule_then(qspec_then `ss` strip_assume_tac) evaluate_swap_stack_frame_sizes >>
      dxrule_then(qspec_then `lim` strip_assume_tac) evaluate_swap_limits >>
      fs[])
QED

Theorem do_app_stack_max:
  do_app op xs s1 = Rval (v,s2) ==>
  option_le s1.stack_max s2.stack_max
Proof
  rw[do_app_def,do_stack_def,do_space_def,do_app_aux_def,do_install_def,with_fresh_ts_def,
     check_lim_def,
     CaseEq "bool",CaseEq"option",CaseEq"list",CaseEq"prod",CaseEq"closLang$op",
     CaseEq "v",CaseEq"ref",CaseEq"ffi_result",CaseEq"eq_result",CaseEq"word_size",
     ELIM_UNCURRY,consume_space_def] >> rw[option_le_max_right,AllCaseEqs()]
  \\ gvs [AllCaseEqs()] \\ rw[option_le_max_right]
QED

Theorem evaluate_option_le_stack_max:
  !c2 s res s1.
  dataSem$evaluate (c2,s) = (res,s1) ==> option_le s.stack_max s1.stack_max
Proof
  recInduct evaluate_ind >> rpt strip_tac
  >- ((* Skip *)
      fs[evaluate_def])
  >- ((* Move *)
      fs[evaluate_def,CaseEq "option",set_var_def] >> rveq >> rw[])
  >- ((* Assign *)
      fs[evaluate_def,CaseEq"bool",CaseEq"option",CaseEq"result",CaseEq"prod",
         cut_state_opt_def,cut_state_def,set_var_def,get_vars_def] >>
      rveq >> fs[flush_state_def] >>
      imp_res_tac do_app_stack_max >> fs[])
  >- ((* Tick *)
      fs[evaluate_def,CaseEq "bool"] >> rveq >> rw[flush_state_def,dec_clock_def])
  >- ((* MakeSpace *)
      fs[evaluate_def,CaseEq "option",set_var_def] >> rveq >> rw[add_space_def])
  >- ((* Raise *)
      fs[evaluate_def,CaseEq "option",set_var_def,jump_exc_def,
         CaseEq "list", CaseEq "stack"] >> rveq >> rw[add_space_def])
  >- ((* Return *)
      fs[evaluate_def,CaseEq "option",set_var_def,jump_exc_def,
         CaseEq "list", CaseEq "stack"] >> rveq >> rw[add_space_def,flush_state_def])
  >- ((* Seq *)
      fs[evaluate_def,ELIM_UNCURRY,CaseEq"bool"] >>
      Cases_on `evaluate (c1,s)` >> res_tac >>
      fs[] >> metis_tac[option_le_trans])
  >- ((* If *)
      fs[evaluate_def,CaseEq"option",CaseEq"bool"]) >>
  (* Call *)
  fs[evaluate_def,CaseEq"option",CaseEq"bool",CaseEq"prod",flush_state_def,
     CaseEq "result", CaseEq "error_result"] >>
  rveq >>
  fs[call_env_def,dec_clock_def,push_env_def,pop_env_def,
     CaseEq "list", CaseEq "stack"]
  (* TODO: department of redundancy department *)
  >- (match_mp_tac option_le_trans >> HINT_EXISTS_TAC >>
      rw[] >>
      Cases_on `s.stack_max` >> rw[OPTION_MAP2_DEF])
  >- (match_mp_tac option_le_trans >> HINT_EXISTS_TAC >>
      rw[] >>
      Cases_on `s.stack_max` >> rw[OPTION_MAP2_DEF])
  >- (Cases_on `handler` >> rw[push_env_def] >>
      Cases_on `s.stack_max` >> rw[OPTION_MAP2_DEF,IS_SOME_EXISTS])
  >- (match_mp_tac option_le_trans >> HINT_EXISTS_TAC >>
      Cases_on `handler` >> rw[push_env_def] >>
      Cases_on `s.stack_max` >> rw[OPTION_MAP2_DEF,IS_SOME_EXISTS])
  >- (match_mp_tac option_le_trans >> HINT_EXISTS_TAC >>
      Cases_on `handler` >> rw[push_env_def] >>
      Cases_on `s.stack_max` >> rw[OPTION_MAP2_DEF,IS_SOME_EXISTS])
  >- (rveq >> fs[set_var_def] >>
      match_mp_tac option_le_trans >> HINT_EXISTS_TAC >>
      Cases_on `handler` >> rw[push_env_def] >>
      Cases_on `s.stack_max` >> rw[OPTION_MAP2_DEF,IS_SOME_EXISTS])
  >- (rveq >> fs[set_var_def] >>
      match_mp_tac option_le_trans >> HINT_EXISTS_TAC >>
      Cases_on `handler` >> rw[push_env_def] >>
      Cases_on `s.stack_max` >> rw[OPTION_MAP2_DEF,IS_SOME_EXISTS])
  >- (match_mp_tac option_le_trans >> HINT_EXISTS_TAC >>
      Cases_on `s.stack_max` >> rw[OPTION_MAP2_DEF,IS_SOME_EXISTS])
  >- (rveq >> fs[set_var_def] >>
      drule_all_then assume_tac option_le_trans >>
      match_mp_tac (PURE_ONCE_REWRITE_RULE [CONJ_SYM] option_le_trans) >>
      goal_assum drule >>
      Cases_on `s.stack_max` >> rw[OPTION_MAP2_DEF,IS_SOME_EXISTS])
  >- (rveq >> fs[set_var_def] >>
      match_mp_tac option_le_trans >> HINT_EXISTS_TAC >>
      Cases_on `handler` >> rw[push_env_def] >>
      Cases_on `s.stack_max` >> rw[OPTION_MAP2_DEF,IS_SOME_EXISTS])
QED

Definition cc_co_only_diff_def:
  cc_co_only_diff (s:('a,'ffi)dataSem$state) (t:('b,'ffi)dataSem$state) <=>
    (* defined this way to allow s and t to have different types *)
    s.locals = t.locals /\
    s.locals_size = t.locals_size /\
    s.stack = t.stack /\
    s.stack_max = t.stack_max /\
    s.stack_frame_sizes = t.stack_frame_sizes /\
    s.global = t.global /\
    s.handler = t.handler /\
    s.refs = t.refs /\
    s.clock = t.clock /\
    s.code = t.code /\
    s.ffi = t.ffi /\
    s.space = t.space /\
    s.tstamps = t.tstamps /\
    s.limits = t.limits /\
    s.safe_for_space = t.safe_for_space /\
    s.peak_heap_length = t.peak_heap_length
End

Theorem do_app_cc_co_only_diff_rval:
    dataSem$do_app op vs s = Rval (v,s1) /\ s1.safe_for_space /\ cc_co_only_diff s t ==>
    ?t1. dataSem$do_app op vs t = Rval (v,t1) /\ cc_co_only_diff s1 t1
Proof
  rpt strip_tac >>
  Cases_on ‘op’ \\ TRY (rename [‘EqualConst cc’] \\ Cases_on ‘cc’) \\ fs [] >>
  ntac 2(
  fs[do_app_aux_def,cc_co_only_diff_def,do_app_def,do_stack_def,list_case_eq,option_case_eq,v_case_eq,
     bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_stack_def,do_space_def,
     with_fresh_ts_def,closSemTheory.ref_case_eq,do_install_def,stack_consumed_def,
     ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,space_consumed_def,
     semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
     pair_case_eq,consume_space_def,op_space_reset_def,check_lim_def,
     CaseEq"closLang$op",ELIM_UNCURRY,size_of_heap_def,stack_to_vs_def] >>
    rveq >> fs[])
  >> gvs []
QED

Theorem do_app_cc_co_only_diff_rerr:
    dataSem$do_app op vs s = Rerr r /\
    op ≠ Install /\ cc_co_only_diff s t ==>
    dataSem$do_app op vs t = Rerr r
Proof
  rpt strip_tac >>
  fs[do_app_def] >>
  rw[] >> fs[] >>
  TOP_CASE_TAC >- fs[cc_co_only_diff_def,do_space_def,CaseEq"bool",consume_space_def] >>
  `space_consumed s op vs = space_consumed t op vs`
    by (qhdtm_x_assum `cc_co_only_diff` mp_tac >>
        MAP_EVERY qid_spec_tac [`t`,`vs`,`op`,`s`] >>
        ho_match_mp_tac space_consumed_ind >> rw[space_consumed_def,cc_co_only_diff_def]) >>
  `?y. do_space op vs s = SOME y /\ cc_co_only_diff y (THE(do_space op vs t))`
    by (fs[do_space_def,CaseEq"bool",consume_space_def] >>
        rveq >> fs[cc_co_only_diff_def] >>
        rw[EQ_IMP_THM,size_of_heap_def,ELIM_UNCURRY,stack_to_vs_def]) >>
  fs[] >>
  qpat_x_assum `cc_co_only_diff s t` kall_tac >>
  rfs[] >>
  `cc_co_only_diff
     (do_stack op vs (y with safe_for_space := (lim_safe y.limits op vs ∧ y.safe_for_space)))
     (do_stack op vs (x with safe_for_space := (lim_safe x.limits op vs ∧ x.safe_for_space)))`
    by(fs[lim_safe_def,do_stack_def,cc_co_only_diff_def,stack_consumed_def]) >>
  rename1 `cc_co_only_diff s1 s2` >>
  qpat_x_assum `cc_co_only_diff y x` kall_tac >>
  rpt(qpat_x_assum `do_space _ _ _ = _` kall_tac) >>
  Cases_on ‘op’ \\ TRY (rename [‘EqualConst cc’] \\ Cases_on ‘cc’) \\ fs [] >>
  fs[do_app_aux_def,cc_co_only_diff_def,do_app_def,list_case_eq,option_case_eq,v_case_eq,
     bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_stack_def,do_space_def,
     with_fresh_ts_def,closSemTheory.ref_case_eq,do_install_def,
     ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
     semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
     pair_case_eq,consume_space_def,op_space_reset_def,check_lim_def,
     CaseEq"closLang$op",ELIM_UNCURRY,size_of_heap_def,stack_to_vs_def] >>
  rveq >> fs[]
QED

Theorem pop_env_safe_for_space:
  pop_env s2 = SOME s1 ==> s1.safe_for_space = s2.safe_for_space
Proof
  rw[pop_env_def,CaseEq"list",CaseEq"stack"] >> rw[]
QED

Theorem pop_env_cc_co_only_diff:
  cc_co_only_diff s2 t2 /\ pop_env s2 = SOME s1 ==>
  ?t1. pop_env t2 = SOME t1 /\ cc_co_only_diff s1 t1
Proof
  rw[pop_env_def,CaseEq"list",CaseEq"stack",cc_co_only_diff_def] >> rw[PULL_EXISTS] >>
  rfs[]
QED

Theorem cc_co_only_diff_call_env:
  cc_co_only_diff s t ==>
  cc_co_only_diff (call_env args1 ss (push_env x'' b (dec_clock s)))
                  (call_env args1 ss (push_env x'' b (dec_clock t)))
Proof
  Cases_on `b` >> rw[cc_co_only_diff_def,call_env_def,push_env_def,dec_clock_def]
QED

Theorem evaluate_cc_co_only_diff:
  ∀prog (s:('a,'ffi)dataSem$state) res s1 (t:('b,'ffi)dataSem$state).
    evaluate (prog, s) = (res,s1) ∧
    s1.safe_for_space ∧
    cc_co_only_diff s t
    ⇒ ∃t1. evaluate (prog, t) = (res,t1) ∧ cc_co_only_diff s1 t1
Proof
  recInduct evaluate_ind >> rpt strip_tac
  >- ((* Skip *)
      fs[evaluate_def] >> rveq >> fs[])
  >- ((* Move *)
      fs[evaluate_def,CaseEq "option",set_var_def] >> rveq >>
      fs[get_var_def,cc_co_only_diff_def])
  >- ((* Assign *)
      fs[evaluate_def] >>
      IF_CASES_TAC >-
        (fs[] >> rveq >> fs[]) >>
      TOP_CASE_TAC >-
        (fs[] >> rveq >>
         fs[cut_state_opt_def,cut_state_def,cut_env_def,
            CaseEq "option",CaseEq "bool"] >>
         rveq >> fs[] >>
         fs[cc_co_only_diff_def] >>rfs[]) >>
      TOP_CASE_TAC >-
        (fs[] >> rveq >>
         fs[cut_state_opt_def,cut_state_def,cut_env_def,
            CaseEq "option",CaseEq "bool"] >>
         rveq >> fs[] >>
         fs[cc_co_only_diff_def] >>rfs[]) >>
      rename1 `cut_state_opt _ _ = SOME t'` >>
      `?s'. cut_state_opt names_opt s = SOME s' /\
           cc_co_only_diff s' t'`
       by(fs[] >> rveq >>
          fs[cut_state_opt_def,cut_state_def,cut_env_def,get_vars_def,
             CaseEq "option",CaseEq "bool"] >>
          rveq >> fs[] >> rveq >> fs[] >>
          fs[cc_co_only_diff_def] >>rfs[]) >>
      qmatch_asmsub_abbrev_tac `~ a1` >>
      fs[] >>
      `s'.locals = t'.locals` by fs[cc_co_only_diff_def] >>
      fs[] >>
      fs[CaseEq "result",CaseEq "prod"] >>
      rveq >> fs[set_var_def] >>
      TRY(drule_all_then strip_assume_tac do_app_cc_co_only_diff_rval >>
          fs[] >>
          fs[cc_co_only_diff_def]
         ) >>
      Cases_on `op = Install` >- fs [flush_state_def] >>
      reverse conj_tac >- fs[cc_co_only_diff_def,flush_state_def] >>
      imp_res_tac do_app_cc_co_only_diff_rerr)
  >- ((* Tick *)
      fs[evaluate_def,CaseEq "bool",flush_state_def,cc_co_only_diff_def,dec_clock_def] >>
      rveq >> fs[])
  >- ((* MakeSpace *)
      fs[evaluate_def,CaseEq "option",set_var_def,add_space_def,
         cc_co_only_diff_def] >> rveq >> rw[add_space_def] >>
      rfs[stack_to_vs_def,size_of_heap_def] >>
      fs[])
  >- ((* Raise *)
      fs[evaluate_def,CaseEq "option",set_var_def,jump_exc_def,
         CaseEq "list", CaseEq "stack",add_space_def,cc_co_only_diff_def] >> rveq >>
      fs[])
  >- ((* Return *)
      fs[evaluate_def,CaseEq "option",set_var_def,jump_exc_def,
         CaseEq "list", CaseEq "stack",cc_co_only_diff_def,add_space_def,flush_state_def] >>
      rveq >> fs[])
  >- ((* Seq *)
      fs[evaluate_def,ELIM_UNCURRY,CaseEq"bool"] >>
      Cases_on `evaluate (c1,s)` >> res_tac >>
      fs[] >>
      imp_res_tac evaluate_safe_for_space_mono >>
      res_tac >>
      fs[])
  >- ((* If *)
      fs[evaluate_def,CaseEq"option",CaseEq"bool"] >>
      imp_res_tac evaluate_safe_for_space_mono >>
      res_tac >>
      fs[] >> rfs[] >>
      fs[cc_co_only_diff_def]) >>
  (* Call *)
  qhdtm_assum `cc_co_only_diff` (strip_assume_tac o REWRITE_RULE[cc_co_only_diff_def]) >>
  fs[evaluate_def] >>
  TOP_CASE_TAC >> fs[] >>
  TOP_CASE_TAC >> fs[CaseEq "prod"] >>
  rveq >> fs[] >>
  TOP_CASE_TAC >-
    ((* Tail call case *)
     fs[CaseEq"bool",CaseEq"prod",CaseEq"option",flush_state_def] >>
     rveq >>
     rfs[] >>
     TRY(fs[cc_co_only_diff_def] >> NO_TAC) >>
     first_x_assum (qspec_then `call_env args1 ss (dec_clock t)` mp_tac) >>
     fs[cc_co_only_diff_def,call_env_def,dec_clock_def] >>
     strip_tac >> fs []) >>
  fs[CaseEq "prod"] >>
  TOP_CASE_TAC >> fs[] >>
  TOP_CASE_TAC >-
    (Cases_on `handler` >>
     rveq >> fs[] >> rveq >>
     fs[cc_co_only_diff_def,call_env_def,push_env_def,dec_clock_def]) >>
  fs[CaseEq"prod"] >> rveq >> fs[] >>
  drule_then(qspecl_then [`x''`,`ss`,`IS_SOME handler`,`args1`] strip_assume_tac) cc_co_only_diff_call_env >>
  Cases_on `handler` >> fs[CaseEq "option",CaseEq "result",CaseEq "error_result"] >>
  rveq >> fs[set_var_def,PULL_EXISTS] >>
  rfs[] >>
  imp_res_tac pop_env_safe_for_space >> fs[] >>
  res_tac >> fs[] >>
  TRY(fs[PULL_EXISTS] >>
      drule_all_then strip_assume_tac pop_env_cc_co_only_diff >>
      goal_assum drule >> fs[cc_co_only_diff_def] >> NO_TAC) >>
  fs[CaseEq "prod"] >> rveq >> fs[] >>
  imp_res_tac evaluate_safe_for_space_mono >> fs[] >> rfs[] >>
  TRY(fs [pop_env_def,cc_co_only_diff_def] >>
      Cases_on `t1.stack` >> fs [] >>
      Cases_on `h` >> fs [] >> NO_TAC) >>
  first_x_assum match_mp_tac >>
  fs[cc_co_only_diff_def]
QED

Theorem evaluate_stack_limit:
  !c2 s res s1.
  dataSem$evaluate (c2,s) = (res,s1) ==> s1.limits.stack_limit = s.limits.stack_limit
Proof
  rpt strip_tac >>
  drule_then(qspec_then `s.limits` strip_assume_tac) evaluate_swap_limits >>
  `s with limits := s.limits = s` by rw[state_component_equality] >>
  fs[] >>
  qpat_x_assum `_ = s1` (SUBST_ALL_TAC o GSYM) >>
  rw[]
QED

(* TODO: move *)
Theorem the_le_IMP_option_le:
  the F (OPTION_MAP ($> n) m)
  ==>
  option_le m (SOME n)
Proof
  Cases_on `m` >> rw[libTheory.the_def]
QED

Theorem do_app_stack_max_le_stack_limit:
  do_app op xs s = Rval(res,s1) /\ s1.safe_for_space /\
  option_le s.stack_max (SOME s.limits.stack_limit) ==>
  option_le s1.stack_max (SOME s1.limits.stack_limit)
Proof
  rpt strip_tac >>
  Cases_on ‘op’ \\ TRY (rename [‘EqualConst cc’] \\ Cases_on ‘cc’) \\ fs [] >>
  fs[do_app_aux_def,cc_co_only_diff_def,do_app_def,do_stack_def,list_case_eq,option_case_eq,v_case_eq,
     bool_case_eq,ffiTheory.call_FFI_def,do_app_def,do_stack_def,do_space_def,
     with_fresh_ts_def,closSemTheory.ref_case_eq,do_install_def,
     ffiTheory.ffi_result_case_eq,ffiTheory.oracle_result_case_eq,
     semanticPrimitivesTheory.eq_result_case_eq,astTheory.word_size_case_eq,
     pair_case_eq,consume_space_def,op_space_reset_def,check_lim_def,
     CaseEq"closLang$op",ELIM_UNCURRY,size_of_heap_def,stack_to_vs_def,
     stack_consumed_def
    ] >>
  rveq >> fs[stack_consumed_def,allowed_op_def] >>
  imp_res_tac the_le_IMP_option_le >>
  fs[option_le_max,option_le_max_right] >>
  rpt (pop_assum mp_tac)>>
  IF_CASES_TAC >> simp [] >>
  fs[option_le_max,option_le_max_right]
QED

Theorem evaluate_stack_max_le_stack_limit:
  ∀prog s res s1.
    dataSem$evaluate (prog,s) = (res,s1) ∧ s1.safe_for_space ∧
    option_le s.stack_max (SOME s.limits.stack_limit) ⇒
    option_le s1.stack_max (SOME s1.limits.stack_limit)
Proof
  recInduct evaluate_ind >> rpt strip_tac
  >- ((* Skip *)
      fs[evaluate_def] >> rveq >> fs[])
  >- ((* Move *)
      fs[evaluate_def,CaseEq "option",set_var_def] >> rveq >> rw[])
  >- ((* Assign *)
      fs[evaluate_def,CaseEq"bool",CaseEq"option",CaseEq"result",CaseEq"prod",
         cut_state_opt_def,cut_state_def,set_var_def,get_vars_def] >>
      rveq >> fs[flush_state_def] >>
      imp_res_tac do_app_stack_max_le_stack_limit >> fs[])
  >- ((* Tick *)
      fs[evaluate_def,CaseEq "bool"] >> rveq >> rw[flush_state_def,dec_clock_def])
  >- ((* MakeSpace *)
      fs[evaluate_def,CaseEq "option",set_var_def] >> rveq >> rw[add_space_def])
  >- ((* Raise *)
      fs[evaluate_def,CaseEq "option",set_var_def,jump_exc_def,
         CaseEq "list", CaseEq "stack"] >> rveq >> rw[add_space_def])
  >- ((* Return *)
      fs[evaluate_def,CaseEq "option",set_var_def,jump_exc_def,
         CaseEq "list", CaseEq "stack"] >> rveq >> rw[add_space_def,flush_state_def])
  >- ((* Seq *)
      fs[evaluate_def,ELIM_UNCURRY,CaseEq"bool"] >>
      Cases_on `evaluate (c1,s)` >> res_tac >>
      fs[] >>
      metis_tac[option_le_trans,evaluate_safe_for_space_mono])
  >- ((* If *)
      fs[evaluate_def,CaseEq"option",CaseEq"bool"] >>
      rveq >> fs[]) >>
  (* Call *)
  ntac 3 (pop_assum mp_tac) >>
  rw[evaluate_def,CaseEq"option",CaseEq"bool",CaseEq"prod",flush_state_def,
     CaseEq "result", CaseEq "error_result",
     pop_env_def,
     CaseEq "list", CaseEq "stack"] >>
  TRY(first_x_assum ACCEPT_TAC)
  >- rw[] >>
  TRY(Cases_on `handler`) >>
  TRY(first_x_assum drule >> rpt(disch_then drule)) >>
  TRY(first_x_assum drule >> rpt(disch_then drule)) >>
  imp_res_tac evaluate_stack_limit >>
  imp_res_tac evaluate_option_le_stack_max >>
  imp_res_tac evaluate_safe_for_space_mono >>
  rpt(PRED_ASSUM is_forall kall_tac) >>
  fs[call_env_def,dec_clock_def,push_env_def,set_var_def] >>
  rfs[] >>
  imp_res_tac the_le_IMP_option_le >>
  fs[option_le_max]
QED

val _ = export_theory();
