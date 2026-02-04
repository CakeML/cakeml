(*
  Proving that Candle prover maintains its invariants (i.e. v_ok)
 *)
Theory candle_prover_evaluate
Ancestors
  candle_kernel_funs ast_extras evaluate namespaceProps perms
  semanticPrimitivesProps misc[qualified] semanticPrimitives
  evaluateProps sptree candle_kernelProg ml_hol_kernel_funsProg
  candle_kernel_vals candle_prover_inv
Libs
  preamble helperLib ml_progLib[qualified]


val _ = temp_send_to_back_overload "If" {Name="If",Thy="compute_syntax"};
val _ = temp_send_to_back_overload "App" {Name="App",Thy="compute_syntax"};
val _ = temp_send_to_back_overload "Var" {Name="Var",Thy="compute_syntax"};
val _ = temp_send_to_back_overload "Let" {Name="Let",Thy="compute_syntax"};

Theorem pmatch_v_ok:
  (∀envC s p v ws env.
    pmatch envC s p v ws = Match env ∧
    v_ok ctxt v ∧
    (∀n len tag m.
      nsLookup envC n = SOME (len,TypeStamp tag m) ∧
      m ∈ kernel_types ⇒
        id_to_n n ∈ kernel_ctors) ∧
    (∀loc r. loc ∉ kernel_locs ∧ LLOOKUP s loc = SOME r ⇒ ref_ok ctxt r) ∧
    EVERY (v_ok ctxt) (MAP SND ws) ⇒
      EVERY (v_ok ctxt) (MAP SND env)) ∧
  (∀envC s ps vs ws env.
    pmatch_list envC s ps vs ws = Match env ∧
    EVERY (v_ok ctxt) vs ∧
    (∀n len tag m.
      nsLookup envC n = SOME (len,TypeStamp tag m) ∧
      m ∈ kernel_types ⇒
        id_to_n n ∈ kernel_ctors) ∧
    (∀loc r. loc ∉ kernel_locs ∧ LLOOKUP s loc = SOME r ⇒ ref_ok ctxt r) ∧
    EVERY (v_ok ctxt) (MAP SND ws) ⇒
      EVERY (v_ok ctxt) (MAP SND env))
Proof
  ho_match_mp_tac pmatch_ind \\ rw [] \\ gvs [pmatch_def, SF SFY_ss]
  >- (
    gs [CaseEq "bool"])
  >- (
    gvs [CaseEqs ["bool", "option", "prod"], SF SFY_ss]
    \\ gvs [same_type_def, same_ctor_def]
    \\ first_x_assum irule
    \\ irule v_ok_Conv_alt
    \\ first_assum (irule_at Any))
  >- (
    gs [CaseEq "bool", v_ok_def, SF SFY_ss])
  >- (
    gvs [CaseEqs ["bool", "option", "store_v"], v_ok_def, SF SFY_ss]
    \\ gs [store_lookup_def, EVERY_EL, EL_MAP, LLOOKUP_THM] \\ rw []
    \\ first_x_assum irule \\ gs []
    \\ first_x_assum drule \\ gs [ref_ok_def])
  >- (
    gvs [CaseEq "match_result", v_ok_def, SF SFY_ss])
QED

local
  val ind_thm =
    full_evaluate_ind
    |> Q.SPECL [
      ‘λs env xs. ∀res s' ctxt.
        evaluate s env xs = (s', res) ∧
        state_ok ctxt s ∧
        env_ok ctxt env ∧
        EVERY safe_exp xs ⇒
          ∃ctxt'.
            (∀v. v_ok ctxt v ⇒ v_ok ctxt' v) ∧
            case res of
              Rval vs =>
                state_ok ctxt' s' ∧
                EVERY (v_ok ctxt') vs
            | Rerr (Rraise v) =>
                state_ok ctxt' s' ∧
                v_ok ctxt' v
            | _ => EVERY ok_event s'.ffi.io_events’,
      ‘λs env v ps errv. ∀res s' ctxt.
        evaluate_match s env v ps errv = (s', res) ∧
        state_ok ctxt s ∧
        env_ok ctxt env ∧
        v_ok ctxt v ∧
        v_ok ctxt errv ∧
        EVERY safe_exp (MAP SND ps) ⇒
          ∃ctxt'.
            (∀v. v_ok ctxt v ⇒ v_ok ctxt' v) ∧
            case res of
              Rval vs =>
                state_ok ctxt' s' ∧
                EVERY (v_ok ctxt') vs
            | Rerr (Rraise v) =>
                state_ok ctxt' s' ∧
                v_ok ctxt' v
            | _ => EVERY ok_event s'.ffi.io_events’,
      ‘λs env ds. ∀res s' ctxt.
        evaluate_decs s env ds = (s', res) ∧
        state_ok ctxt s ∧
        env_ok ctxt env ∧
        EVERY safe_dec ds ⇒
          ∃ctxt'.
            (∀v. v_ok ctxt v ⇒ v_ok ctxt' v) ∧
            case res of
              Rval env1 =>
                state_ok ctxt' s'  ∧
                env_ok ctxt' (extend_dec_env env1 env)
            | Rerr (Rraise v) =>
                state_ok ctxt' s'  ∧
                v_ok ctxt' v
            | _ => EVERY ok_event s'.ffi.io_events’]
    |> CONV_RULE (DEPTH_CONV BETA_CONV);
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> helperLib.list_dest dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
    |> helperLib.list_dest dest_forall
    |> last
  fun evaluate_v_ok () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end

Theorem evaluate_v_ok_Nil:
  ^(get_goal "[]")
Proof
  rw [evaluate_def]
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem evaluate_v_ok_Cons:
  ^(get_goal "_::_::_")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["semanticPrimitives$result", "prod"]]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ first_x_assum (drule_all_then (qx_choose_then ‘ctxt1’ assume_tac)) \\ gs []
  \\ ‘env_ok ctxt1 env’
    by gs [env_ok_def, SF SFY_ss]
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ gs [state_ok_def]
  \\ first_assum (irule_at Any) \\ gs []
  \\ first_assum (irule_at Any) \\ gs [SF SFY_ss]
QED

Theorem evaluate_v_ok_Lit:
  ^(get_goal "Lit l")
Proof
  rw [evaluate_def] \\ gs []
  \\ first_assum (irule_at Any)
  \\ simp [v_ok_Lit]
QED

Theorem evaluate_v_ok_Raise:
  ^(get_goal "Raise e")
Proof
  rw [evaluate_def] \\ gs []
  \\ gvs [AllCaseEqs()]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
QED

Theorem EXISTS_IMP[local,simp]:
  ∃b. ∀x. P a x ⇒ P b x
Proof
  qexists_tac ‘a’ \\ gs []
QED

Theorem evaluate_v_ok_Handle:
  ^(get_goal "Handle e")
Proof
  rw [evaluate_def]
  \\ gvs [AllCaseEqs(), EVERY_MAP]
  \\ first_x_assum (drule_all_then (qx_choose_then ‘ctxt1’ assume_tac)) \\ gs []
  >~ [‘¬can_pmatch_all _ _ _ _’] >- (
    gs [state_ok_def])
  \\ ‘env_ok ctxt1 env’
    by gs [env_ok_def, SF SFY_ss]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem evaluate_v_ok_Con:
  ^(get_goal "Con cn es")
Proof
  rw [evaluate_def]
  \\ gvs [AllCaseEqs(), EVERY_MAP]
  >~ [‘¬do_con_check _ _ _’] >- (
    gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  >- (
    first_x_assum (drule_all_then strip_assume_tac)
    \\ gs [state_ok_def])
  \\ first_x_assum (drule_all_then (qx_choose_then ‘ctxt1’ assume_tac)) \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
  \\ gvs [build_conv_def, CaseEqs ["option", "prod"], do_con_check_def]
  \\ irule v_ok_Conv \\ gs [] \\ rw []
  \\ strip_tac \\ gs [env_ok_def]
QED

Theorem evaluate_v_ok_Var:
  ^(get_goal "ast$Var n")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option"]]
  >- (
    gs [state_ok_def])
  \\ first_assum (irule_at Any)
  \\ gs [env_ok_def, SF SFY_ss]
QED

Theorem evaluate_v_ok_Fun:
  ^(get_goal "ast$Fun n e")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option"]]
  \\ first_assum (irule_at Any) \\ gs []
  \\ irule v_ok_Closure \\ gs []
QED

Theorem evaluate_v_ok_Eval:
  op = Eval ⇒ ^(get_goal "ast$App")
Proof
  rw [evaluate_def]
  \\ gvs [AllCaseEqs(), evaluateTheory.do_eval_res_def]
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ TRY (
    gs [state_ok_def]
    \\ NO_TAC)
  \\ rename [‘state_ok ctxt1 st1’]
  \\ ‘eval_state_ok st1.eval_state’ by fs [state_ok_def]
  \\ gvs [do_eval_def,AllCaseEqs(),eval_state_ok_def,
          declare_env_def,SF SFY_ss,SWAP_REVERSE_SYM]
  \\ last_x_assum (qspec_then ‘ctxt1’ mp_tac)
  \\ (impl_tac >-
   (fs [] \\ qpat_x_assum ‘v_ok ctxt1 (Env env' id)’ mp_tac
    \\ fs [candle_prover_invTheory.v_ok_def,kernel_vals_Env]
    \\ fs [state_ok_def,dec_clock_def,eval_state_ok_def,add_decs_generation_def]
    \\ every_case_tac \\ fs [SF SFY_ss] \\ metis_tac []))
  \\ strip_tac
  \\ fs [state_ok_def,reset_env_generation_def,LEFT_EXISTS_AND_THM]
  \\ fs [candle_prover_invTheory.v_ok_def,kernel_vals_Env,SF SFY_ss]
  \\ fs [PULL_EXISTS]
  \\ first_x_assum $ irule_at Any \\ fs [SF SFY_ss]
  \\ simp [nat_to_v_def,candle_prover_invTheory.v_ok_def]
  \\ every_case_tac \\ fs [eval_state_ok_def, SF SFY_ss]
  \\ gvs [state_ok_def,eval_state_ok_def]
  \\ first_assum (irule_at Any) \\ gs [SF SFY_ss]
QED

Theorem v_ok_v_to_list:
  ∀v vs.
    v_to_list v = SOME vs ∧
    v_ok ctxt v ⇒
      EVERY (v_ok ctxt) vs
Proof
  ho_match_mp_tac v_to_list_ind
  \\ rw [v_to_list_def]
  \\ gvs [AllCaseEqs(), v_ok_def]
  \\ fs [Once v_ok_cases]
  \\ fs [Once inferred_cases]
  \\ gvs [do_partial_app_def,AllCaseEqs()]
  \\ Cases_on ‘ty’ \\ fs [TYPE_TYPE_def]
QED

Theorem do_app_ok:
  do_app (refs,ffi) op vs = SOME ((refs1,ffi1),res) ∧
  op ≠ Opapp ∧
  op ≠ Eval ∧
  EVERY (v_ok ctxt) vs ∧
  (∀loc r. loc ∉ kernel_locs ∧ LLOOKUP refs loc = SOME r ⇒ ref_ok ctxt r) ∧
  EVERY ok_event ffi.io_events ∧
  op ≠ FFI kernel_ffi ∧
  STATE ctxt st ∧
  (∀loc. loc ∈ kernel_locs ⇒ kernel_loc_ok st loc refs) ⇒
    ∃st1.
      STATE ctxt st1 ∧
      (∀loc. loc ∈ kernel_locs ⇒ kernel_loc_ok st1 loc refs1) ∧
      (∀loc r. loc ∉ kernel_locs ∧ LLOOKUP refs1 loc = SOME r ⇒ ref_ok ctxt r) ∧
      EVERY ok_event ffi1.io_events ∧
      case list_result res of
        Rval vs => EVERY (v_ok ctxt) vs
        | Rerr (Rraise v) => v_ok ctxt v
        | _ => T
Proof
  strip_tac
  \\ qpat_x_assum ‘do_app _ _ _ = _’ mp_tac
  \\ Cases_on ‘op = Env_id’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def, nat_to_v_def]
    \\ first_assum (irule_at Any) \\ gs [SF SFY_ss])
  \\ Cases_on ‘∃chn. op = FFI chn’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ gvs [ffiTheory.call_FFI_def, store_lookup_def, store_assign_def,
            CaseEqs ["bool", "list", "option", "oracle_result",
                     "ffi$ffi_result"], EVERY_EL, EL_LUPDATE]
    \\ rw [v_ok_def, EL_APPEND_EQN]
    \\ first_assum (irule_at Any)
    \\ csimp [oEL_LUPDATE]
    \\ rw [] \\ gs [NOT_LESS, LESS_OR_EQ, ok_event_def, ref_ok_def, SF SFY_ss]
    \\ irule kernel_loc_ok_LUPDATE1 \\ gs []
    \\ strip_tac \\ gvs [v_ok_def])
  \\ Cases_on ‘op = ConfigGC’ \\ gs []
  >- (
    rw [do_app_cases, oEL_LUPDATE] \\ gs [SF SFY_ss]
    \\ simp [v_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = ListAppend’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ dxrule_all_then assume_tac v_ok_v_to_list
    \\ dxrule_all_then assume_tac v_ok_v_to_list
    \\ ‘EVERY (v_ok ctxt) (xs ++ ys)’
      by gs []
    \\ pop_assum mp_tac
    \\ rename1 ‘EVERY (v_ok ctxt) zs ⇒ _’
    \\ qid_spec_tac ‘zs’
    \\ Induct \\ simp [list_to_v_def, v_ok_def]
    \\ rw [] \\ first_assum (irule_at Any) \\ gs [SF SFY_ss])
  \\ Cases_on ‘op = Aw8sub_unsafe’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def]
    \\ first_assum (irule_at Any) \\ gs [SF SFY_ss])
  \\ Cases_on ‘op = Aw8update_unsafe’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def]
    \\ gvs [store_lookup_def, store_assign_def, EVERY_EL, EL_LUPDATE]
    \\ first_assum (irule_at Any) \\ gs []
    \\ rw [SF CONJ_ss, oEL_LUPDATE] \\ gs [ref_ok_def, SF SFY_ss]
    \\ irule kernel_loc_ok_LUPDATE1 \\ gs []
    \\ strip_tac \\ gs [])
  \\ Cases_on ‘op = Aupdate_unsafe’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def]
    \\ gvs [store_lookup_def, store_assign_def, EVERY_EL, EL_LUPDATE]
    \\ rw [] \\ gs [EVERY_EL, EL_LUPDATE, ref_ok_def]
    \\ first_assum (irule_at Any)
    \\ rw [] \\ gs []
    >- (
      irule kernel_loc_ok_LUPDATE1 \\ gs []
      \\ strip_tac \\ gvs [v_ok_def])
    \\ gvs [oEL_LUPDATE, CaseEq "bool", SF SFY_ss]
    \\ rw [ref_ok_def, EVERY_EL, EL_LUPDATE] \\ rw []
    \\ first_x_assum drule
    \\ gs [LLOOKUP_EQ_EL, ref_ok_def, EVERY_EL])
  \\ Cases_on ‘op = Asub_unsafe’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ gvs [store_lookup_def, v_ok_def, LLOOKUP_EQ_EL, EVERY_EL]
    \\ first_assum (irule_at Any) \\ gs []
    \\ first_x_assum drule_all
    \\ gs [ref_ok_def, EVERY_EL])
  \\ Cases_on ‘op = Aupdate’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def, SF SFY_ss]
    \\ gvs [store_lookup_def, store_assign_def, EVERY_EL, EL_LUPDATE]
    \\ first_assum (irule_at Any) \\ gs [LLOOKUP_EQ_EL]
    \\ rw [ref_ok_def, EVERY_EL, EL_LUPDATE] \\ rw []
    >- (
      irule kernel_loc_ok_LUPDATE1 \\ gs []
      \\ strip_tac \\ gvs [v_ok_def])
    \\ first_x_assum drule_all
    \\ gs [ref_ok_def, EVERY_EL])
  \\ Cases_on ‘op = Alength’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Asub’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ gvs [store_lookup_def, v_ok_def, EVERY_EL, LLOOKUP_EQ_EL]
    \\ first_assum (irule_at Any) \\ gs []
    \\ first_x_assum drule_all
    \\ gs [ref_ok_def, EVERY_EL])
  \\ Cases_on ‘op = AallocEmpty’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ gvs [v_ok_def, store_alloc_def, EVERY_EL, LLOOKUP_EQ_EL]
    \\ first_assum (irule_at Any) \\ gs []
    \\ rw [EL_APPEND_EQN] \\ gs [NOT_LESS, LESS_OR_EQ, ref_ok_def]
    >- (
      gs [kernel_loc_ok_def, LLOOKUP_EQ_EL, EL_APPEND_EQN]
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ rw [] \\ gs [SF SFY_ss])
    \\ strip_tac
    \\ first_x_assum (drule_then assume_tac)
    \\ drule kernel_loc_ok_LENGTH \\ gs [])
  \\ Cases_on ‘op = Aalloc’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ gvs [v_ok_def, store_alloc_def, EVERY_EL, LLOOKUP_EQ_EL]
    \\ first_assum (irule_at Any) \\ gs []
    \\ rw [EL_APPEND_EQN] \\ gs [NOT_LESS, LESS_OR_EQ, ref_ok_def]
    >- (
      gs [kernel_loc_ok_def, LLOOKUP_EQ_EL, EL_APPEND_EQN]
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ rw [] \\ gs [SF SFY_ss])
    \\ strip_tac
    \\ first_x_assum (drule_then assume_tac)
    \\ drule kernel_loc_ok_LENGTH \\ gs [])
  \\ Cases_on ‘op = AallocFixed’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ gvs [v_ok_def, store_alloc_def, EVERY_EL, LLOOKUP_EQ_EL]
    \\ first_assum (irule_at Any) \\ gs []
    \\ rw [EL_APPEND_EQN] \\ gs [NOT_LESS, LESS_OR_EQ, ref_ok_def]
    \\ TRY (
      gs [kernel_loc_ok_def, LLOOKUP_EQ_EL, EL_APPEND_EQN]
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ rw [] \\ gs [SF SFY_ss])
    \\ gvs [EVERY_EL]
    \\ strip_tac
    \\ first_x_assum (drule_then assume_tac)
    \\ drule kernel_loc_ok_LENGTH \\ gs [])
  \\ Cases_on ‘op = Vlength’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Vsub’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gs [v_ok_def, EVERY_EL])
  \\ Cases_on ‘op = Vsub_unsafe’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gs [v_ok_def, EVERY_EL])
  \\ Cases_on ‘op = VfromList’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ drule_all v_ok_v_to_list
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Strcat’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Strlen’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Strsub’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Explode’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ rename1 ‘MAP _ xs’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ simp [list_to_v_def, v_ok_def])
  \\ Cases_on ‘op = Implode’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = XorAw8Str_unsafe’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def, SF SFY_ss]
    \\ first_assum (irule_at Any) \\ gs [LLOOKUP_EQ_EL]
    \\ gvs [store_assign_def, EL_LUPDATE, EVERY_EL]
    \\ rw [ref_ok_def]
    \\ irule kernel_loc_ok_LUPDATE1
    \\ rpt strip_tac \\ gvs [])
  \\ Cases_on ‘op = CopyAw8Aw8’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def, SF SFY_ss]
    \\ first_assum (irule_at Any) \\ gs [LLOOKUP_EQ_EL]
    \\ gvs [store_assign_def, EL_LUPDATE, EVERY_EL]
    \\ rw [ref_ok_def]
    \\ irule kernel_loc_ok_LUPDATE1
    \\ rpt strip_tac \\ gvs [])
  \\ Cases_on ‘op = CopyAw8Str’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def, SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gvs [store_assign_def, EL_LUPDATE, EVERY_EL, LLOOKUP_EQ_EL]
    \\ rw [ref_ok_def]
    \\ irule kernel_loc_ok_LUPDATE1
    \\ rpt strip_tac \\ gvs [])
  \\ Cases_on ‘op = CopyStrAw8’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def, SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gvs [store_assign_def, EL_LUPDATE, EVERY_EL, LLOOKUP_EQ_EL]
    \\ rw [ref_ok_def]
    \\ irule kernel_loc_ok_LUPDATE1
    \\ rpt strip_tac \\ gvs [])
  \\ Cases_on ‘op = CopyStrStr’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Aw8update’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def, SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gvs [store_assign_def, EL_LUPDATE, EVERY_EL, LLOOKUP_EQ_EL]
    \\ rw [ref_ok_def]
    \\ irule kernel_loc_ok_LUPDATE1
    \\ rpt strip_tac \\ gvs [])
  \\ Cases_on ‘op = Aw8sub’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Aw8length’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Aw8alloc’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ gvs [v_ok_def, store_alloc_def, EVERY_EL, LLOOKUP_EQ_EL]
    \\ first_assum (irule_at Any) \\ gs []
    \\ rw [EL_APPEND_EQN] \\ gs [NOT_LESS, LESS_OR_EQ, ref_ok_def]
    >- (
      gs [kernel_loc_ok_def, LLOOKUP_EQ_EL, EL_APPEND_EQN]
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ rw [] \\ gs [SF SFY_ss])
    \\ strip_tac
    \\ first_x_assum (drule_then assume_tac)
    \\ drule kernel_loc_ok_LENGTH \\ gs [])
  \\ Cases_on ‘∃sz sh n. op = Shift sz sh n’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Equality’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [Boolv_def]
    \\ rw [v_ok_def])
  \\ Cases_on ‘∃test ty. op = Test test ty’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [Boolv_def]
    \\ rw [v_ok_def])
  \\ Cases_on ‘∃ty1 ty2. op = FromTo ty1 ty2’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ gvs [do_conversion_def |> oneline, AllCaseEqs()]
    \\ first_assum (irule_at $ Pos hd)
    \\ simp [Boolv_def]
    \\ rw [v_ok_def]
    \\ last_x_assum drule_all \\ simp [])
  \\ Cases_on ‘∃a ty. op = Arith a ty’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ Cases_on ‘a’ \\ Cases_on ‘ty’ using prim_type_cases
    \\ gvs[do_arith_def,CaseEq"list",CaseEq"bool"]
    \\ simp [Boolv_def]
    \\ rw [v_ok_def]
    \\ first_x_assum irule
    \\ goal_assum drule \\ rw[])
  \\ Cases_on ‘op = Opderef’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gs [v_ok_def, store_lookup_def, EVERY_EL, LLOOKUP_EQ_EL]
    \\ first_x_assum drule \\ gs [ref_ok_def])
  \\ Cases_on ‘op = Opassign’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gvs [v_ok_def, store_assign_def, EVERY_EL, EL_LUPDATE, LLOOKUP_EQ_EL]
    \\ rw [ref_ok_def]
    \\ irule kernel_loc_ok_LUPDATE1
    \\ rpt strip_tac \\ gs [])
  \\ Cases_on ‘op = Opref’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gvs [v_ok_def, store_alloc_def, ref_ok_def, LLOOKUP_EQ_EL]
    \\ rw [DISJ_EQ_IMP] \\ rpt strip_tac
    >- (
      gs [kernel_loc_ok_def, LLOOKUP_EQ_EL, EL_APPEND_EQN]
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ rw [] \\ gs [SF SFY_ss])
    \\ rw [EL_APPEND_EQN] \\ gs [NOT_LESS, LESS_OR_EQ, ref_ok_def]
    \\ first_x_assum (drule_then assume_tac)
    \\ drule kernel_loc_ok_LENGTH \\ gs [])
  \\ Cases_on ‘∃m. op = ThunkOp (AllocThunk m)’ \\ gs[]
  >- (
    rw [do_app_cases] \\ gs [thunk_op_def, AllCaseEqs()]
    \\ pairarg_tac \\ gvs []
    \\ gvs [v_ok_def, store_alloc_def, EVERY_EL, LLOOKUP_EQ_EL]
    \\ first_assum (irule_at Any) \\ gs []
    \\ rw [EL_APPEND_EQN] \\ gs [NOT_LESS, LESS_OR_EQ, ref_ok_def]
    >- (
      gs [kernel_loc_ok_def, LLOOKUP_EQ_EL, EL_APPEND_EQN]
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ rw [] \\ gs [SF SFY_ss])
    \\ strip_tac
    \\ first_x_assum (drule_then assume_tac)
    \\ drule kernel_loc_ok_LENGTH \\ gs [])
  \\ Cases_on ‘∃m. op = ThunkOp (UpdateThunk m)’ \\ gs[]
  >- (
    rw [do_app_cases] \\ gs [thunk_op_def, AllCaseEqs()]
    \\ first_assum (irule_at Any)
    \\ gvs [v_ok_def, store_assign_def, EVERY_EL, EL_LUPDATE, LLOOKUP_EQ_EL]
    \\ rw [ref_ok_def]
    \\ irule kernel_loc_ok_LUPDATE1
    \\ rpt strip_tac \\ gs [])
  \\ Cases_on ‘op = ThunkOp ForceThunk’ \\ gs[]
  >- (rw [do_app_cases] \\ gs [thunk_op_def, AllCaseEqs()])
  \\ Cases_on ‘op’ \\ gs []
  \\ Cases_on ‘t’ \\ gs []
QED

Theorem state_ok_dest_thunk:
  state_ok ctxt s ∧
  EVERY (v_ok ctxt) vs ∧
  dest_thunk (REVERSE vs) s.refs = IsThunk m v ⇒ v_ok ctxt v
Proof
  rw []
  >- (
    gvs [state_ok_def, oneline dest_thunk_def, AllCaseEqs(), v_ok_def,
         store_lookup_def, LLOOKUP_THM]
    \\ first_x_assum drule \\ rw [] \\ gvs [ref_ok_def])
  \\ rw [env_ok_def, sing_env_def]
  \\ Cases_on ‘n'’ \\ gvs []
  \\ gvs [namespaceTheory.nsEmpty_def, namespaceTheory.nsBind_def,
          namespaceTheory.nsLookup_def]
  \\ gvs [oneline dest_thunk_def, AllCaseEqs(), store_lookup_def, state_ok_def,
          LLOOKUP_THM, v_ok_def]
  \\ first_x_assum drule_all \\ rw [] \\ gvs [ref_ok_def]
QED

Theorem state_ok_update_thunk:
  state_ok ctxt s ∧
  EVERY (v_ok ctxt) vs ∧
  EVERY (v_ok ctxt) vs2 ∧
  update_thunk (REVERSE vs) s.refs vs2 = SOME refs ⇒
    state_ok ctxt (s with refs := refs)
Proof
  rw []
  \\ gvs [oneline update_thunk_def, AllCaseEqs(), store_assign_def,
          state_ok_def, LLOOKUP_LUPDATE, v_ok_def]
  \\ goal_assum drule \\ gvs [] \\ rw []
  >- (
    irule kernel_loc_ok_LUPDATE1 \\ gvs []
    \\ metis_tac [EXTENSION])
  >- (first_x_assum drule \\ rw [])
  >- gvs [ref_ok_def]
QED

Theorem evaluate_v_ok_Op:
  op ≠ Opapp ∧ op ≠ Eval ⇒ ^(get_goal "ast$App")
Proof
  rw [evaluate_def] \\ Cases_on ‘getOpClass op’ \\ gs[]
  >~ [‘EvalOp’] >- (Cases_on ‘op’ \\ gs[] \\ Cases_on ‘t’ \\ gs[])
  >~ [‘FunApp’] >- (Cases_on ‘op’ \\ gs[] \\ Cases_on ‘t’ \\ gs[])
  >~ [‘Force’] >- (
    Cases_on ‘op’ \\ gvs [] \\ Cases_on ‘t’ \\ gvs []
    \\ qpat_x_assum ‘_ = (s',res)’ mp_tac
    \\ TOP_CASE_TAC \\ gvs []
    \\ last_x_assum drule_all \\ strip_tac
    \\ reverse TOP_CASE_TAC \\ gvs []
    >- (
      rw [] \\ gvs []
      \\ goal_assum drule \\ gvs [])
    \\ TOP_CASE_TAC \\ gvs []
    >~ [‘BadRef’] >- (
      rw [] \\ gvs []
      \\ goal_assum drule \\ gvs [state_ok_def])
    >~ [‘NotThunk’] >- (
      rw [] \\ gvs []
      \\ goal_assum drule \\ gvs [state_ok_def])
    \\ TOP_CASE_TAC \\ gvs []
    >- (
      rw [] \\ gvs []
      \\ goal_assum drule \\ gvs []
      \\ drule_all_then assume_tac state_ok_dest_thunk \\ gvs [])
    \\ TOP_CASE_TAC \\ gvs []
    >- (
      rw [] \\ gvs []
      \\ goal_assum drule \\ gvs [state_ok_def])
    \\ ntac 2 (TOP_CASE_TAC \\ gvs [])
    >- (
      rw [] \\ gvs []
      \\ goal_assum drule \\ gvs [state_ok_def])
    \\ TOP_CASE_TAC \\ gvs []
    \\ ‘state_ok ctxt' (dec_clock q)’
      by (gvs [dec_clock_def, state_ok_def] \\ metis_tac [])
    \\ Cases_on ‘kernel_vals ctxt' v’
    >- (
      drule (INST_TYPE [“:'a”|->“:'ffi”] kernel_vals_ok)
      \\ ‘v_ok ctxt' (Conv NONE [])’ by gvs [v_ok_def]
      \\ disch_then (drule_all_then (strip_assume_tac)) \\ gs []
      >- (
        rw [] \\ gvs []
        \\ goal_assum drule \\ gvs [state_ok_def])
      \\ rpt (TOP_CASE_TAC \\ gvs [])
      >- (
        rw [] \\ gvs []
        \\ goal_assum drule \\ gvs [state_ok_def])
      >- (
        rw [] \\ gvs []
        \\ qexists ‘ctxt''’ \\ gvs []
        \\ drule_at (Pat ‘update_thunk _ _ _ = _’) state_ok_update_thunk
        \\ disch_then $ qspec_then ‘ctxt''’ mp_tac
        \\ impl_tac \\ gvs []
        \\ gvs [EVERY_EL])
      >- (
        rw [] \\ gvs []
        \\ qexists ‘ctxt''’ \\ gvs [])
      \\ rw [] \\ gvs []
      \\ qexists ‘ctxt''’ \\ gvs [state_ok_def])
    \\ first_x_assum drule
    \\ impl_tac >- (
      gvs [do_opapp_cases]
      >~ [‘Closure env1 n e’] >- (
        drule_all state_ok_dest_thunk \\ strip_tac
        \\ gvs [v_ok_def]
        \\ irule env_ok_with_nsBind \\ gvs [v_ok_def]
        \\ ‘env1 with c := env1.c = env1’ by simp [sem_env_component_equality]
        \\ gvs [])
      \\ drule_all state_ok_dest_thunk \\ strip_tac
      \\ gvs [v_ok_def]
      \\ gs [env_ok_def, evaluateTheory.dec_clock_def, find_recfun_ALOOKUP,
             SF SFY_ss]
      \\ drule_then assume_tac ALOOKUP_MEM
      \\ gs [EVERY_MEM, EVERY_MAP, FORALL_PROD, SF SFY_ss]
      \\ Cases \\ simp [build_rec_env_merge, ml_progTheory.nsLookup_nsBind_compute]
      \\ rw [] \\ gs []
      \\ gs [nsLookup_nsAppend_some, nsLookup_alist_to_ns_some,
             nsLookup_alist_to_ns_none]
      >- simp [v_ok_def]
      >~ [‘ALOOKUP _ _ = SOME _’] >- (
        drule_then assume_tac ALOOKUP_MEM
        \\ gvs [MEM_MAP, EXISTS_PROD, v_ok_def, EVERY_MEM]
        \\ rw [DISJ_EQ_IMP, env_ok_def] \\ gs [SF SFY_ss])
      \\ first_x_assum irule
      \\ gs [SF SFY_ss])
    \\ strip_tac \\ gvs []
    \\ reverse TOP_CASE_TAC \\ gvs []
    >- (
      rw [] \\ gvs []
      \\ goal_assum $ drule_at (Pos $ el 2)
      \\ rw [] \\ gvs [])
    \\ TOP_CASE_TAC \\ gvs []
    >- (
      rw [] \\ gvs []
      \\ goal_assum drule \\ gvs [state_ok_def])
    \\ strip_tac \\ gvs []
    \\ goal_assum $ drule_at (Pos $ el 3) \\ gvs []
    \\ drule_at (Pat ‘update_thunk _ _ _ = _’) state_ok_update_thunk \\ gvs []
    \\ disch_then drule \\ gvs []
    \\ impl_tac \\ gvs []
    \\ gvs [EVERY_EL])
  >~ [‘Simple’] >- (
    gvs [AllCaseEqs()]
    \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs [state_ok_def]
    \\ rename1 ‘EVERY (v_ok ctxt1)’
    \\ qexists_tac ‘ctxt1’ \\ gs []
    \\ drule do_app_ok \\ gs []
    \\ disch_then drule_all \\ simp []
    \\ strip_tac \\ gs []
    \\ rpt CASE_TAC \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
QED

Theorem evaluate_v_ok_Opapp:
  op = Opapp ⇒ ^(get_goal "ast$App")
Proof
  rw [evaluate_def]
  \\ gvs [AllCaseEqs()]
  >~ [‘do_opapp _ = NONE’] >- (
    first_x_assum (drule_all_then strip_assume_tac)
    \\ gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  >~ [‘s.clock = 0’] >- (
    first_x_assum (drule_all_then strip_assume_tac)
    \\ gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ first_x_assum (drule_all_then (qx_choose_then ‘ctxt1’ assume_tac)) \\ gs []
  \\ ‘env_ok ctxt1 env’
    by gs [env_ok_def, SF SFY_ss]
  \\ rename1 ‘state_ok ctxt1 s’
  \\ ‘state_ok ctxt1 (dec_clock s)’
    by (gs [evaluateTheory.dec_clock_def, state_ok_def]
        \\ first_assum (irule_at Any) \\ gs [SF SFY_ss])
  \\ ‘∃f v. vs = [v; f]’
    by (gvs [do_opapp_cases]
        \\ Cases_on ‘vs’ \\ gs [])
  \\ gvs []
  \\ Cases_on ‘kernel_vals ctxt1 f’
  >- (
    drule (INST_TYPE [“:'a”|->“:'ffi”] kernel_vals_ok)
    \\ disch_then (drule_all_then (strip_assume_tac)) \\ gs []
    >- (
      gs [state_ok_def]
      \\ first_assum (irule_at Any) \\ gs [])
    \\ gs [evaluateTheory.dec_clock_def]
    \\ qexists_tac ‘ctxt'’ \\ gs []
    \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs []
    \\ gs [state_ok_def])
  \\ rename1 ‘do_opapp _ = SOME (env1, e)’
  \\ ‘env_ok ctxt1 env1 ∧ safe_exp e’
    suffices_by (
      strip_tac
      \\ last_x_assum (drule_all_then strip_assume_tac)
      \\ qexists_tac ‘ctxt'’
      \\ gs [evaluateTheory.dec_clock_def, state_ok_def, EVERY_MEM,
             AC CONJ_COMM CONJ_ASSOC])
  \\ gvs [v_ok_def, state_ok_def, do_opapp_cases]
  >~ [‘Closure env1 n e’] >- (
    irule env_ok_with_nsBind \\ gs []
    \\ ‘env1 with c := env1.c = env1’
      by rw [sem_env_component_equality]
    \\ gs [])
  \\ gs [env_ok_def, evaluateTheory.dec_clock_def, find_recfun_ALOOKUP,
         SF SFY_ss]
  \\ drule_then assume_tac ALOOKUP_MEM
  \\ gs [EVERY_MEM, EVERY_MAP, FORALL_PROD, SF SFY_ss]
  \\ Cases \\ simp [build_rec_env_merge, ml_progTheory.nsLookup_nsBind_compute]
  \\ rw [] \\ gs []
  \\ gs [nsLookup_nsAppend_some, nsLookup_alist_to_ns_some,
         nsLookup_alist_to_ns_none]
  >~ [‘ALOOKUP _ _ = SOME _’] >- (
    drule_then assume_tac ALOOKUP_MEM
    \\ gvs [MEM_MAP, EXISTS_PROD, v_ok_def, EVERY_MEM]
    \\ rw [DISJ_EQ_IMP, env_ok_def] \\ gs [SF SFY_ss])
  \\ first_x_assum irule
  \\ gs [SF SFY_ss]
QED

Theorem evaluate_v_ok_App:
  ^(get_goal "ast$App")
Proof
  Cases_on ‘op = Opapp’ >- (match_mp_tac evaluate_v_ok_Opapp \\ gs [])
  \\ Cases_on ‘op = Eval’ >- (match_mp_tac evaluate_v_ok_Eval \\ gs [])
  \\ match_mp_tac evaluate_v_ok_Op \\ gs []
QED

Theorem evaluate_v_ok_Log:
  ^(get_goal "Log")
Proof
  rw [evaluate_def]
  \\ gvs [AllCaseEqs(), do_log_def]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  >- (
    first_x_assum (drule_all_then strip_assume_tac)
    \\ gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ rename1 ‘v_ok ctxt1 (Boolv _)’
  \\ ‘env_ok ctxt1 env’
    suffices_by (
      strip_tac
      \\ first_x_assum (drule_all_then strip_assume_tac)
      \\ first_assum (irule_at Any) \\ gs [])
  \\ gs [env_ok_def, SF SFY_ss]
QED

Theorem evaluate_v_ok_If:
  ^(get_goal "ast$If")
Proof
  rw [evaluate_def]
  \\ gvs [AllCaseEqs(), do_if_def]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  >- (
    first_x_assum (drule_all_then strip_assume_tac)
    \\ gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ rename1 ‘v_ok ctxt1 (Boolv _)’
  \\ ‘env_ok ctxt1 env’
    suffices_by (
      strip_tac
      \\ first_x_assum (drule_all_then strip_assume_tac)
      \\ first_assum (irule_at Any) \\ gs [])
  \\ gs [env_ok_def, SF SFY_ss]
QED

Theorem evaluate_v_ok_Mat:
  ^(get_goal "Mat")
Proof
  rw [evaluate_def]
  \\ gvs [AllCaseEqs()]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ first_x_assum (drule_all_then strip_assume_tac)
  >~ [‘¬can_pmatch_all _ _ _ _’] >- (
    gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ rename1 ‘v_ok ctxt1 v’
  \\ ‘env_ok ctxt1 env’
    suffices_by (
      strip_tac
      \\ first_x_assum (drule_all_then strip_assume_tac)
      \\ first_assum (irule_at Any) \\ gs [])
  \\ gs [env_ok_def, SF SFY_ss]
QED

Theorem evaluate_v_ok_Let:
  ^(get_goal "ast$Let")
Proof
  rw [evaluate_def]
  \\ gvs [AllCaseEqs()]
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ rename1 ‘v_ok ctxt1 v’
  \\ ‘env_ok ctxt1 (env with v := nsOptBind xo v env.v)’
    suffices_by (
      strip_tac
      \\ first_x_assum (drule_all_then strip_assume_tac)
      \\ first_assum (irule_at Any)
      \\ gs [])
  \\ gs [env_ok_def, SF SFY_ss]
  \\ Cases_on ‘xo’ \\ gs [namespaceTheory.nsOptBind_def, SF SFY_ss]
  \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem evaluate_v_ok_Letrec:
  ^(get_goal "Letrec")
Proof
  rw [evaluate_def]
  \\ gvs [AllCaseEqs()]
  >~ [‘¬ALL_DISTINCT _’] >- (
    gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ ‘env_ok ctxt (env with v := build_rec_env funs env env.v)’
    suffices_by (
      strip_tac
      \\ first_x_assum (drule_all_then strip_assume_tac)
      \\ first_assum (irule_at Any) \\ gs [])
  \\ gs [env_ok_def, SF SFY_ss]
  \\ simp [build_rec_env_merge, nsLookup_nsAppend_some,
           nsLookup_alist_to_ns_some,
           nsLookup_alist_to_ns_none]
  \\ rw [] \\ gs [SF SFY_ss]
  \\ drule_then assume_tac ALOOKUP_MEM
  \\ gvs [MEM_MAP, EXISTS_PROD, PULL_EXISTS, v_ok_def]
  \\ rw [DISJ_EQ_IMP, env_ok_def] \\ gs [SF SFY_ss]
QED

Theorem evaluate_v_ok_Tannot:
  ^(get_goal "Tannot")
Proof
  rw [evaluate_def]
QED

Theorem evaluate_v_ok_Lannot:
  ^(get_goal "Lannot")
Proof
  rw [evaluate_def]
QED

Theorem evaluate_v_ok_pmatch_Nil:
  ^(get_goal "[]:(pat # exp) list")
Proof
  rw [evaluate_def] \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem evaluate_v_ok_pmatch_Cons:
  ^(get_goal "_::_:(pat # exp) list")
Proof
  rw [evaluate_def] \\ gs []
  \\ gvs [AllCaseEqs()]
  >~ [‘Match env1’] >- (
    ‘env_ok ctxt (env with v := nsAppend (alist_to_ns env1) env.v)’
      suffices_by (
        strip_tac
        \\ first_x_assum (drule_all_then strip_assume_tac)
        \\ first_assum (irule_at Any) \\ gs [])
    \\ gs [env_ok_def, SF SFY_ss]
    \\ simp [nsLookup_nsAppend_some, nsLookup_alist_to_ns_some,
             nsLookup_alist_to_ns_none]
    \\ rw [] \\ gs [SF SFY_ss]
    \\ drule_then assume_tac ALOOKUP_MEM
    \\ drule_then drule (CONJUNCT1 pmatch_v_ok)
    \\ gs [env_ok_def, state_ok_def, SF SFY_ss, EVERY_MAP, LAMBDA_PROD,
           EVERY_MEM, FORALL_PROD])
  \\ gs [state_ok_def]
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem evaluate_v_ok_decs_Nil:
  ^(get_goal "[]:dec list")
Proof
  rw [evaluate_decs_def, extend_dec_env_def]
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem evaluate_v_ok_decs_Cons:
  ^(get_goal "_::_::_:dec list")
Proof
  rw [evaluate_decs_def]
  \\ gvs [AllCaseEqs()]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ rename1 ‘state_ok ctxt1 st1’
  \\ ‘env_ok ctxt1 (extend_dec_env env1 env)’
    by gs [extend_dec_env_def, env_ok_def, SF SFY_ss]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ gs [state_ok_def, combine_dec_result_def]
  \\ CASE_TAC \\ gs [AC CONJ_COMM CONJ_ASSOC]
  >~ [‘Rerr err’] >- (
    CASE_TAC \\ gs []
    \\ first_assum (irule_at Any) \\ gs [SF SFY_ss])
  \\ first_x_assum (irule_at Any) \\ gs []
  \\ gs [env_ok_def, extend_dec_env_def, nsLookup_nsAppend_some]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem evaluate_v_ok_decs_Dlet:
  ^(get_goal "Dlet")
Proof
  reverse $ rw [evaluate_decs_def]
  >- (gs [state_ok_def]
      \\ first_assum (irule_at Any) \\ gs [SF SFY_ss])
  \\ gvs [CaseEqs ["prod", "semanticPrimitives$result"]]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ CASE_TAC \\ gs [state_ok_def]
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [extend_dec_env_def, env_ok_def, nsLookup_nsAppend_some,
         nsLookup_alist_to_ns_some, SF SFY_ss]
  \\ rw [] \\ gs [SF SFY_ss]
  \\ drule_then assume_tac ALOOKUP_MEM
  \\ drule_then drule (CONJUNCT1 pmatch_v_ok)
  \\ gs [env_ok_def, state_ok_def, SF SFY_ss, EVERY_MAP, LAMBDA_PROD,
         EVERY_MEM, FORALL_PROD]
QED

Theorem evaluate_v_ok_decs_Dletrec:
  ^(get_goal "Dletrec")
Proof
  reverse $ rw [evaluate_decs_def]
  >- (gs [state_ok_def]
      \\ first_assum (irule_at Any) \\ gs [SF SFY_ss])
  \\ gvs [CaseEqs ["prod", "semanticPrimitives$result"]]
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [extend_dec_env_def, build_rec_env_merge, env_ok_def,
         nsLookup_nsAppend_some, nsLookup_alist_to_ns_some, SF SFY_ss]
  \\ rw [] \\ gs [SF SFY_ss]
  \\ drule_then assume_tac ALOOKUP_MEM
  \\ gvs [MEM_MAP, EXISTS_PROD]
  \\ simp [v_ok_def, DISJ_EQ_IMP]
  \\ rw [] \\ gs [env_ok_def, SF SFY_ss]
QED

Theorem evaluate_v_ok_decs_Dtype:
  ^(get_goal "Dtype")
Proof
  rw [evaluate_decs_def]
  >~ [‘¬EVERY check_dup_ctors _’] >- (
    gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ gvs [CaseEqs ["prod", "semanticPrimitives$result"], state_ok_def]
  \\ first_assum (irule_at Any) \\ gs []
  \\ conj_tac
  >- (
    rw []
    \\ first_x_assum drule \\ gs [])
  \\ gs [extend_dec_env_def, build_tdefs_def, env_ok_def,
         nsLookup_nsAppend_some, nsLookup_alist_to_ns_some, SF SFY_ss]
  \\ rw [] \\ gs [SF SFY_ss]
  \\ ‘∀m tds n l t k.
        nsLookup (build_tdefs m tds) n = SOME (l, TypeStamp t k) ⇒
          m ≤ k’
    by (ho_match_mp_tac build_tdefs_ind
        \\ simp [build_tdefs_def, nsLookup_nsAppend_some,
                 nsLookup_alist_to_ns_some, SF SFY_ss]
        \\ rw [] \\ gs [SF SFY_ss]
        >- (
          first_x_assum drule
          \\ gs [])
        \\ drule_then assume_tac ALOOKUP_MEM
        \\ gs [build_constrs_def, MEM_MAP, EXISTS_PROD])
  \\ first_x_assum (drule_then assume_tac)
  \\ first_x_assum drule_all \\ gs []
QED

Theorem evaluate_v_ok_decs_Dtabbrev:
  ^(get_goal "Dtabbrev")
Proof
  rw [evaluate_decs_def]
  \\ first_assum (irule_at Any)
  \\ gs [env_ok_def, extend_dec_env_def, SF SFY_ss]
QED

Theorem evaluate_v_ok_decs_Denv:
  ^(get_goal "Denv")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod"]]
  \\ gs [state_ok_def]
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [env_ok_def, extend_dec_env_def, SF SFY_ss]
  \\ gvs [declare_env_def, CaseEqs ["option", "eval_state", "prod"]]
  \\ fs [eval_state_ok_def,SF SFY_ss]
  \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
  \\ rw [] \\ gs [v_ok_def, env_ok_def, nat_to_v_def, SF SFY_ss]
QED

Theorem evaluate_v_ok_decs_Dexn:
  ^(get_goal "Dexn")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod"], state_ok_def]
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [env_ok_def, extend_dec_env_def, SF SFY_ss]
  \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem evaluate_v_ok_decs_Dmod:
  ^(get_goal "Dmod")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod", "semanticPrimitives$result"]]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [env_ok_def, extend_dec_env_def, SF SFY_ss]
  \\ conj_tac
  >- (
    gs [nsLookup_nsAppend_some, nsLookup_nsLift, nsLookupMod_nsLift]
    \\ Cases \\ simp []
    \\ rw [] \\ gs [SF SFY_ss]
    \\ simp [namespaceTheory.id_to_n_def])
  \\ Cases \\ gs [ml_progTheory.nsLookup_nsBind_compute, nsLookup_nsAppend_some,
                  nsLookup_nsLift]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem evaluate_v_ok_decs_Dlocal:
  ^(get_goal "Dlocal")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod", "semanticPrimitives$result"]]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ CASE_TAC \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [env_ok_def, extend_dec_env_def, SF SFY_ss]
  \\ conj_tac
  \\ Cases \\ gs [ml_progTheory.nsLookup_nsBind_compute,
                nsLookup_nsAppend_some]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem evaluate_v_ok:
  ^(evaluate_v_ok ())
Proof
  match_mp_tac (the_ind_thm ())
  \\ rpt conj_tac \\ rpt gen_tac
  \\ rewrite_tac [evaluate_v_ok_Nil, evaluate_v_ok_Cons,
                  evaluate_v_ok_Lit, evaluate_v_ok_Raise,
                  evaluate_v_ok_Handle, evaluate_v_ok_Con,
                  evaluate_v_ok_Var, evaluate_v_ok_Fun,
                  evaluate_v_ok_App, evaluate_v_ok_Log,
                  evaluate_v_ok_If, evaluate_v_ok_Mat,
                  evaluate_v_ok_Let, evaluate_v_ok_Letrec,
                  evaluate_v_ok_Tannot, evaluate_v_ok_Lannot,
                  evaluate_v_ok_pmatch_Nil, evaluate_v_ok_pmatch_Cons,
                  evaluate_v_ok_decs_Nil, evaluate_v_ok_decs_Cons,
                  evaluate_v_ok_decs_Dlet, evaluate_v_ok_decs_Dletrec,
                  evaluate_v_ok_decs_Dtype,
                  evaluate_v_ok_decs_Dtabbrev,
                  evaluate_v_ok_decs_Denv, evaluate_v_ok_decs_Dexn,
                  evaluate_v_ok_decs_Dmod, evaluate_v_ok_decs_Dlocal]
QED
