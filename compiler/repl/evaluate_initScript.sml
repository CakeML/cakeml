(*
  Lemma used in repl_typesTheory: that evaluate_skip's invariant
  holds at initialisation.
*)
Theory evaluate_init
Ancestors
  evaluate semanticPrimitives evaluateProps namespaceProps
  ml_prog evaluate_skip
Libs
  preamble helperLib[qualified]


(* TODO: move *)

Theorem FUN_FMAP_SUBMAP_SUBSET:
  FINITE d1 ∧ FINITE d2 ⇒
  (FUN_FMAP f d1 SUBMAP FUN_FMAP f d2 <=> d1 SUBSET d2)
Proof
  rw[SUBMAP_FLOOKUP_EQN, FLOOKUP_FUN_FMAP, SUBSET_DEF]
QED

Theorem NOT_NIL_CONS:
  xs ≠ [] ⇔ ∃y ys. xs = y::ys
Proof
  Cases_on ‘xs’ \\ gs []
QED

(* -------------------------------------------------------------------------
 *
 * ------------------------------------------------------------------------- *)

Definition state_ok_def:
  state_ok (s: 'ffi semanticPrimitives$state) ⇔
    state_rel (LENGTH s.refs) (FUN_FMAP I (count (LENGTH s.refs)))
                              (FUN_FMAP I (count s.next_type_stamp))
                              (FUN_FMAP I (count s.next_exn_stamp)) s s
End

Definition env_ok_def:
  env_ok (s: 'ffi semanticPrimitives$state) env ⇔
    env_rel (FUN_FMAP I (count (LENGTH s.refs)))
            (FUN_FMAP I (count s.next_type_stamp))
            (FUN_FMAP I (count s.next_exn_stamp))
            env env
End

Definition v_ok_def:
  v_ok (s: 'ffi semanticPrimitives$state) v ⇔
    v_rel (FUN_FMAP I (count (LENGTH s.refs)))
          (FUN_FMAP I (count s.next_type_stamp))
          (FUN_FMAP I (count s.next_exn_stamp))
          v v
End

Definition ref_ok_def:
  ref_ok (s: 'ffi semanticPrimitives$state) v ⇔
    ref_rel (v_rel (FUN_FMAP I (count (LENGTH s.refs)))
                   (FUN_FMAP I (count s.next_type_stamp))
                   (FUN_FMAP I (count s.next_exn_stamp)))
                   v v
End

Theorem ref_ok_thm:
  ref_ok s (Refv v) = v_ok s v ∧
  ref_ok s (Varray vs) = EVERY (v_ok s) vs ∧
  ref_ok s (W8array a) = T ∧
  ref_ok s (Thunk _ v) = v_ok s v
Proof
  rw [ref_ok_def, ref_rel_def, v_ok_def, LIST_REL_EL_EQN, EVERY_EL]
QED

Definition stamp_ok_def:
  stamp_ok (s: 'ffi semanticPrimitives$state) st ⇔
    stamp_rel (FUN_FMAP I (count s.next_type_stamp))
              (FUN_FMAP I (count s.next_exn_stamp)) st st
End

Theorem evaluate_v_ok_mono:
  evaluate s env xs = (t, res) ∧
  v_ok s v ⇒
    v_ok t v
Proof
  rw []
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_type_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_exn_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_refs_length_mono)
  \\ gs [v_ok_def]
  \\ irule v_rel_update
  \\ first_assum (irule_at Any)
  \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO]
QED

Theorem evaluate_env_ok_mono:
  evaluate s env xs = (t, res) ∧
  env_ok s env ⇒
    env_ok t env
Proof
  rw []
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_type_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_exn_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_refs_length_mono)
  \\ gs [env_ok_def]
  \\ irule env_rel_update
  \\ first_assum (irule_at Any)
  \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO]
QED

Theorem v_ok_thm:
  (∀opt vs. v_ok s (Conv opt vs) ⇔
     EVERY (v_ok s) vs ∧
     (∀st. opt = SOME st ⇒ stamp_ok s st)) ∧
  (∀env n x. v_ok s (Closure env n x) ⇔ env_ok s env) ∧
  (∀env f n. v_ok s (Recclosure env f n) ⇔ env_ok s env) ∧
  (∀vs. v_ok s (Vectorv vs) ⇔ EVERY (v_ok s) vs) ∧
  (∀lit. v_ok s (Litv lit)) ∧
  (∀loc b. v_ok s (Loc b loc) ⇔ loc < LENGTH s.refs) ∧
  (∀env ns. v_ok s (Env env ns) ⇔ env_ok s env)
Proof
  rw [v_ok_def, v_rel_def, OPTREL_def, env_ok_def, FLOOKUP_FUN_FMAP,
      LIST_REL_EL_EQN, EVERY_EL, stamp_ok_def]
  \\ rw [EQ_IMP_THM] \\ gs []
  \\ Cases_on ‘opt’ \\ gs []
QED

local
  val ind_thm =
    full_evaluate_ind
    |> Q.SPECL [
      ‘λs env xs. ∀t res.
        evaluate s env xs = (t, res) ∧
        state_ok s ∧
        env_ok s env ∧
        res ≠ Rerr (Rabort Rtype_error) ⇒
          state_ok t ∧
          env_ok t env ∧
          (∀vs. res = Rval vs ⇒ EVERY (v_ok t) vs) ∧
          (∀v. res = Rerr (Rraise v) ⇒ v_ok t v)’,
      ‘λs env v ps errv. ∀t res.
        evaluate_match s env v ps errv = (t, res) ∧
        state_ok s ∧
        env_ok s env ∧
        v_ok s v ∧
        v_ok s errv ∧
        res ≠ Rerr (Rabort Rtype_error) ⇒
          state_ok t ∧
          env_ok t env ∧
          (∀vs. res = Rval vs ⇒ EVERY (v_ok t) vs) ∧
          (∀v. res = Rerr (Rraise v) ⇒ v_ok t v)’,
      ‘λs env ds. ∀t res.
        evaluate_decs s env ds = (t, res) ∧
        state_ok s ∧
        env_ok s env ∧
        res ≠ Rerr (Rabort Rtype_error) ⇒
          state_ok t ∧
          env_ok t env ∧
          (∀env. res = Rval env ⇒ env_ok t env) ∧
          (∀v. res = Rerr (Rraise v) ⇒ v_ok t v)’ ]
    |> CONV_RULE (DEPTH_CONV BETA_CONV);
  val ind_goals =
    ind_thm |> concl |> dest_imp |> fst
            |> helperLib.list_dest dest_conj
in
  fun get_goal s =
    first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
    |> helperLib.list_dest dest_forall
    |> last
  fun evaluate_ok () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end

Theorem evaluate_ok_Nil:
  ^(get_goal "[]")
Proof
  rw [evaluate_def] \\ gs []
QED

Theorem evaluate_ok_Cons:
  ^(get_goal "_::_::_")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["result", "prod"]]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ irule evaluate_v_ok_mono \\ gs [SF SFY_ss]
QED

Theorem evaluate_ok_Lit:
  ^(get_goal "Lit l")
Proof
  rw [evaluate_def] \\ gs []
  \\ simp [v_ok_thm]
QED

Theorem evaluate_ok_Raise:
  ^(get_goal "Raise e")
Proof
  rw [evaluate_def] \\ gs []
  \\ gvs [CaseEqs ["result", "prod"]]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
QED

Theorem evaluate_ok_Handle:
  ^(get_goal "Handle e")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "result", "error_result", "bool"]]
QED

Theorem evaluate_ok_Con:
  ^(get_goal "Con cn es")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "result", "option"]]
  \\ gvs [build_conv_def, CaseEqs ["option", "prod"], v_ok_thm]
  \\ gs [env_ok_def, env_rel_def, stamp_ok_def, ctor_rel_def]
  \\ drule_all_then strip_assume_tac nsAll2_nsLookup1 \\ gs []
  \\ irule stamp_rel_update
  \\ first_assum (irule_at Any)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_type_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_exn_stamp_mono)
  \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO]
QED

Theorem evaluate_ok_Var:
  ^(get_goal "ast$Var n")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option"]]
  \\ gs [env_ok_def, env_rel_def, v_ok_def]
  \\ drule_all_then strip_assume_tac nsAll2_nsLookup1 \\ gs []
QED

Theorem evaluate_ok_Fun:
  ^(get_goal "ast$Fun n e")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option"], v_ok_thm]
QED

Theorem state_ok_eval_state:
  state_ok s ⇒ s.eval_state = NONE
Proof
  rw [state_ok_def, state_rel_def]
QED

Theorem do_eval_state_none:
  s.eval_state = NONE ⇒
    do_eval_res vs s =
      (s, (Rerr (Rabort Rtype_error) : (v sem_env # dec list, v) result))
Proof
  rw [do_eval_res_def, do_eval_def]
QED

Theorem evaluate_ok_Eval:
  op = Eval ⇒ ^(get_goal "App")
Proof
  simp [evaluate_def]
  \\ strip_tac
  \\ strip_tac
  \\ rpt gen_tac
  \\ strip_tac
  \\ qpat_x_assum ‘_ = (t,res)’ mp_tac
  \\ TOP_CASE_TAC \\ rfs []
  \\ reverse TOP_CASE_TAC \\ rfs []
  >- (
    rw [] \\ gs [])
  \\ drule_then assume_tac state_ok_eval_state
  \\ drule_then assume_tac do_eval_state_none
  \\ simp []
QED

Theorem v_ok_v_to_list:
  ∀v vs.
    v_ok s v ∧
    state_ok s ∧
    v_to_list v = SOME vs ⇒
      EVERY (v_ok s) vs
Proof
  ho_match_mp_tac v_to_list_ind \\ gs []
  \\ rw [] \\ gvs [v_ok_thm]
  \\ gvs [v_to_list_def, CaseEq "option"]
QED

Theorem v_ok_list_to_v:
  ∀v vs.
    EVERY (v_ok s) vs ∧
    state_ok s ⇒
      v_ok s (list_to_v vs)
Proof
  Induct_on ‘vs’
  \\ rw [list_to_v_def, v_ok_thm]
  \\ gs [stamp_ok_def, stamp_rel_cases, state_ok_def, state_rel_def]
QED

Theorem do_app_cases[local] = semanticPrimitivesPropsTheory.do_app_cases;

Theorem state_ok_refs_ok[simp]:
  state_ok s ⇒ EVERY (ref_ok s) s.refs
Proof
  rw [state_ok_def, ref_ok_def, state_rel_def, EVERY_EL]
  \\ first_x_assum (qspec_then ‘n’ assume_tac) \\ gs []
QED

Theorem with_same_refs_and_ffi:
  s with <| refs := s.refs; ffi := s.ffi |> = s
Proof
  rw [state_component_equality]
QED

Theorem v_ok_sub_exn[simp]:
  state_ok s ⇒ v_ok s sub_exn_v
Proof
  rw [v_ok_thm, sub_exn_v_def, subscript_stamp_def, stamp_ok_def,
      stamp_rel_cases, state_ok_def, state_rel_def]
QED

Theorem v_ok_chr_exn[simp]:
  state_ok s ⇒ v_ok s chr_exn_v
Proof
  rw [v_ok_thm, chr_exn_v_def, chr_stamp_def, stamp_ok_def,
      stamp_rel_cases, state_ok_def, state_rel_def]
QED

Theorem v_ok_div_exn[simp]:
  state_ok s ⇒ v_ok s div_exn_v
Proof
  rw [v_ok_thm, div_exn_v_def, div_stamp_def, stamp_ok_def,
      stamp_rel_cases, state_ok_def, state_rel_def]
QED

Theorem v_ok_Boolv[simp]:
  state_ok s ⇒ v_ok s (Boolv b)
Proof
  rw [Boolv_def, state_ok_def, v_ok_thm, stamp_ok_def, stamp_rel_cases,
      FLOOKUP_FUN_FMAP, state_rel_def]
QED

Theorem do_app_ok:
  do_app (s.refs,s.ffi) op vs = SOME ((refs,ffi), res) ∧
  state_ok s ∧
  EVERY (v_ok s) vs ∧
  op ≠ Opapp ∧
  op ≠ Eval ⇒
    let t = (s with <| refs := refs; ffi := ffi |>) in
    state_ok t ∧
    EVERY (ref_ok t) refs ∧
    (∀v. res = Rval v ⇒ v_ok t v) ∧
    (∀v. res = Rerr (Rraise v) ⇒ v_ok t v)
Proof
  strip_tac \\ simp [LET_THM]
  \\ simp [Once CONJ_COMM]
  \\ simp [Once (GSYM CONJ_ASSOC)]
  \\ conj_asm2_tac
  >- (
    gs [state_ok_def, state_rel_def, EVERY_EL, ref_ok_def]
    \\ rw [] \\ gs [FLOOKUP_FUN_FMAP])
  \\ simp [Once CONJ_COMM]
  \\ Cases_on ‘op = Env_id’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi])
  \\ Cases_on ‘∃chn. op = FFI chn’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, ffiTheory.call_FFI_def, store_assign_def,
         store_lookup_def,
         CaseEqs ["ffi_result", "option", "bool", "oracle_result"]]
    \\ gvs [with_same_refs_and_ffi]
    \\ gs [state_ok_def, EVERY_EL, state_rel_def] \\ rw []
    \\ first_x_assum (qspec_then ‘n’ assume_tac) \\ gs []
    \\ gs [EL_LUPDATE, ref_ok_def]
    \\ rename1 ‘n = lnum’
    \\ Cases_on ‘n = lnum’ \\ gs [ref_rel_def])
  \\ Cases_on ‘op = ConfigGC’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi])
  \\ Cases_on ‘op = ListAppend’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi]
    \\ irule v_ok_list_to_v
    \\ gs [EVERY_APPEND]
    \\ irule_at (Pos last) v_ok_v_to_list \\ gs []
    \\ first_assum (irule_at Any) \\ gs []
    \\ irule_at Any v_ok_v_to_list \\ gs []
    \\ first_assum (irule_at (Pos hd)) \\ gs [])
  \\ Cases_on ‘op = Aw8sub_unsafe’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi])
  \\ Cases_on ‘op = Aw8update_unsafe’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_assign_def]
    \\ gs [state_ok_def, EVERY_EL, state_rel_def] \\ rw []
    \\ first_x_assum (qspec_then ‘n’ assume_tac) \\ gs []
    \\ gs [EL_LUPDATE, ref_ok_def]
    \\ IF_CASES_TAC \\ gs []
    \\ rw [ref_rel_def])
  \\ Cases_on ‘op = Aupdate_unsafe’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_assign_def, store_lookup_def]
    \\ gs [state_ok_def, EVERY_EL, state_rel_def] \\ rw []
    \\ first_x_assum (qspec_then ‘n’ assume_tac) \\ gs []
    \\ gs [EL_LUPDATE, ref_ok_def]
    \\ IF_CASES_TAC \\ gvs [ref_rel_def, LIST_REL_EL_EQN, v_ok_def]
    \\ rw [EL_LUPDATE, ref_ok_def])
  \\ Cases_on ‘op = Asub_unsafe’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def]
    \\ drule_then assume_tac state_ok_refs_ok
    \\ fs [EVERY_EL]
    \\ first_x_assum drule
    \\ rw [ref_ok_thm, EVERY_EL])
  \\ Cases_on ‘op = Aupdate’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_assign_def, store_lookup_def]
    \\ gs [state_ok_def, EVERY_EL, state_rel_def] \\ rw []
    \\ rw [] \\ gs [v_ok_def]
    \\ rw [EL_LUPDATE, ref_ok_def, ref_rel_def, LIST_REL_EL_EQN]
    \\ rw [] \\ gs [FLOOKUP_FUN_FMAP]
    \\ first_x_assum drule_all
    \\ rw [ref_rel_def, LIST_REL_EL_EQN])
  \\ Cases_on ‘op = Alength’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi])
  \\ Cases_on ‘op = Asub’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def]
    \\ drule_then assume_tac state_ok_refs_ok
    \\ fs [EVERY_EL]
    \\ first_x_assum drule
    \\ rw [ref_ok_thm, EVERY_EL])
  \\ Cases_on ‘op = AallocEmpty’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, store_alloc_def]
    \\ gs [state_ok_def, ref_ok_thm, state_rel_def, EVERY_EL, INJ_IFF,
           FLOOKUP_FUN_FMAP, EL_APPEND_EQN]
    \\ rw [] \\ gs [FUN_FMAP_DEF, ref_rel_def, NOT_LESS, LESS_OR_EQ, ref_ok_def]
    \\ irule ref_rel_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ irule_at Any v_rel_update
    \\ first_assum (irule_at Any)
    \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO])
  \\ Cases_on ‘op = Aalloc’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, store_alloc_def, with_same_refs_and_ffi]
    \\ gs [state_ok_def, ref_ok_thm, state_rel_def, EVERY_EL, INJ_IFF,
           FLOOKUP_FUN_FMAP, EL_APPEND_EQN]
    \\ rw [] \\ gs [FUN_FMAP_DEF, ref_rel_def, NOT_LESS, LESS_OR_EQ, ref_ok_def]
    >- (
      irule ref_rel_mono
      \\ first_assum (irule_at Any) \\ rw []
      \\ irule_at Any v_rel_update
      \\ first_assum (irule_at Any)
      \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO])
    \\ rw [LIST_REL_REPLICATE_same] \\ gs [v_ok_def]
    \\ irule_at Any v_rel_update
    \\ first_assum (irule_at Any)
    \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO])
  \\ Cases_on ‘op = AallocFixed’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, store_alloc_def, with_same_refs_and_ffi]
    \\ gs [state_ok_def, ref_ok_thm, state_rel_def, EVERY_EL, INJ_IFF,
           FLOOKUP_FUN_FMAP, EL_APPEND_EQN]
    \\ rw [] \\ gs [FUN_FMAP_DEF, ref_rel_def, NOT_LESS, LESS_OR_EQ, ref_ok_def]
    >- (
      irule ref_rel_mono
      \\ first_assum (irule_at Any) \\ rw []
      \\ irule_at Any v_rel_update
      \\ first_assum (irule_at Any)
      \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO])
    \\ rw [Once listTheory.LIST_REL_EL_EQN]
    \\ irule_at Any v_rel_update \\ gs[v_ok_def]
    \\ first_x_assum $ irule_at Any \\ rw [v_ok_def]
    \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO])
  \\ Cases_on ‘op = Vlength’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, store_alloc_def, with_same_refs_and_ffi])
  \\ Cases_on ‘op = Vsub’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def]
    \\ drule_then assume_tac state_ok_refs_ok
    \\ fs [EVERY_EL]
    \\ first_x_assum drule
    \\ rw [ref_ok_thm, EVERY_EL])
  \\ Cases_on ‘op = Vsub_unsafe’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def]
    \\ drule_then assume_tac state_ok_refs_ok
    \\ fs [EVERY_EL]
    \\ first_x_assum drule
    \\ rw [ref_ok_thm, EVERY_EL])
  \\ Cases_on ‘op = VfromList’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi]
    \\ irule v_ok_v_to_list
    \\ gs [SF SFY_ss])
  \\ Cases_on ‘op = Strcat’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi])
  \\ Cases_on ‘op = Strlen’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi])
  \\ Cases_on ‘op = Strsub’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi])
  \\ Cases_on ‘op = Explode’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi]
    \\ irule v_ok_list_to_v \\ gs [EVERY_MAP, v_ok_thm])
  \\ Cases_on ‘op = Implode’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi])
  \\ Cases_on ‘op = XorAw8Str_unsafe’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def, copy_array_def, store_assign_def]
    \\ gs [state_ok_def, state_rel_def, EL_LUPDATE, FLOOKUP_FUN_FMAP]
    \\ rw [] \\ gs [ref_rel_def])
  \\ Cases_on ‘op = CopyAw8Aw8’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def, copy_array_def, store_assign_def]
    \\ gs [state_ok_def, state_rel_def, EL_LUPDATE, FLOOKUP_FUN_FMAP]
    \\ rw [] \\ gs [ref_rel_def])
  \\ Cases_on ‘op = CopyAw8Str’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def, copy_array_def, store_assign_def])
  \\ Cases_on ‘op = CopyStrAw8’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def, copy_array_def, store_assign_def]
    \\ gs [state_ok_def, state_rel_def, EL_LUPDATE, FLOOKUP_FUN_FMAP]
    \\ rw [] \\ gs [ref_rel_def])
  \\ Cases_on ‘op = CopyStrStr’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def, copy_array_def, store_assign_def])
  \\ Cases_on ‘op = Aw8update’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def, copy_array_def, store_assign_def]
    \\ gs [state_ok_def, state_rel_def, EL_LUPDATE, FLOOKUP_FUN_FMAP]
    \\ rw [] \\ gs [ref_rel_def])
  \\ Cases_on ‘op = Aw8sub’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def, copy_array_def, store_assign_def])
  \\ Cases_on ‘op = Aw8length’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def, copy_array_def, store_assign_def])
  \\ Cases_on ‘op = Aw8alloc’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def, copy_array_def, store_assign_def, store_alloc_def]
    \\ gs [state_ok_def, state_rel_def, EL_LUPDATE, FLOOKUP_FUN_FMAP]
    \\ gs [INJ_IFF, FUN_FMAP_DEF]
    \\ rw [] \\ gs [ref_rel_def, EL_APPEND_EQN]
    \\ rw [] \\ gs [ref_rel_def, NOT_LESS, LESS_OR_EQ]
    \\ first_x_assum drule \\ rw []
    \\ irule ref_rel_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ irule v_rel_update
    \\ first_assum (irule_at Any)
    \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO])
  \\ Cases_on ‘∃sz sh n. op = Shift sz sh n’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def, copy_array_def, store_assign_def])
  \\ Cases_on ‘op = Equality’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def, copy_array_def, store_assign_def])
  \\ Cases_on ‘∃test ty. op = Test test ty’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def, copy_array_def, store_assign_def])
  \\ Cases_on ‘∃ty1 ty2. op = FromTo ty1 ty2’ \\ gs []
  >- (
    gvs [do_app_def, AllCaseEqs(), oneline do_conversion_def, check_type_def, chr_exn_v_def]
    \\ gvs [v_ok_thm, stamp_ok_def, chr_stamp_def, Once stamp_rel_cases]
    \\ gvs [state_ok_def, state_rel_def])
  \\ Cases_on ‘∃a ty. op = Arith a ty’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def, copy_array_def, store_assign_def,
         CaseEq"sum"]
    \\ Cases_on ‘a’ \\ Cases_on ‘ty’ using semanticPrimitivesPropsTheory.prim_type_cases
    \\ gvs[do_arith_def,CaseEq"list",v_ok_thm] )
  \\ Cases_on ‘op = Opderef’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def, copy_array_def, store_assign_def,
         state_ok_def, v_ok_def, state_rel_def, FLOOKUP_FUN_FMAP]
    \\ first_x_assum drule \\ rw [ref_rel_def])
  \\ Cases_on ‘op = Opassign’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def, copy_array_def, store_assign_def,
         state_ok_def, v_ok_def, state_rel_def, FLOOKUP_FUN_FMAP]
    \\ rw [v_rel_def, EL_LUPDATE]
    \\ first_x_assum drule \\ rw [ref_rel_def])
  \\ Cases_on ‘op = Opref’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, nat_to_v_def, with_same_refs_and_ffi,
         store_lookup_def, copy_array_def, store_assign_def,
         state_ok_def, v_ok_def, state_rel_def, FLOOKUP_FUN_FMAP,
         INJ_IFF, FUN_FMAP_DEF, v_rel_def, store_alloc_def]
    \\ rw [EL_APPEND_EQN] \\ gvs [NOT_LESS, LESS_OR_EQ, ref_rel_def]
    THENL [
      first_x_assum drule \\ rw [ref_rel_def]
      \\ irule_at Any ref_rel_mono
      \\ first_assum (irule_at Any) \\ rw [],
      ALL_TAC ]
    \\ irule v_rel_update
    \\ first_assum (irule_at Any)
    \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO])
  \\ Cases_on ‘∃m. op = ThunkOp (AllocThunk m)’ \\ gs[]
  >- (
    gvs [do_app_cases, v_ok_thm, thunk_op_def, AllCaseEqs()]
    \\ pairarg_tac \\ gvs []
    \\ gvs [store_alloc_def, state_ok_def, v_ok_thm, state_rel_def, EVERY_EL,
            INJ_IFF, FLOOKUP_FUN_FMAP, EL_APPEND_EQN]
    \\ rw [] \\ gvs [FUN_FMAP_DEF, ref_rel_def, NOT_LESS, LESS_OR_EQ,
                     ref_ok_def]
    >- (
      irule ref_rel_mono
      \\ first_assum (irule_at Any) \\ rw []
      \\ irule_at Any v_rel_update
      \\ first_assum (irule_at Any)
      \\ gvs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO])
    \\ gvs [v_ok_def]
    \\ irule_at Any v_rel_update
    \\ first_assum (irule_at Any)
    \\ gvs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO])
  \\ Cases_on ‘∃m. op = ThunkOp (UpdateThunk m)’ \\ gs[]
  >- (
    gvs [do_app_cases, thunk_op_def, AllCaseEqs(), v_ok_thm, store_assign_def,
         state_ok_def, v_ok_def, state_rel_def, FLOOKUP_FUN_FMAP]
    \\ rw [v_rel_def, EL_LUPDATE, ref_rel_def])
  \\ Cases_on ‘op = ThunkOp ForceThunk’ \\ gs[]
  >- gvs [do_app_def, AllCaseEqs(), thunk_op_def]
  \\ Cases_on ‘op’ \\ gs []
  \\ Cases_on ‘t’ \\ gs []
QED

Theorem do_app_ok[allow_rebind] = SIMP_RULE (srw_ss()) [LET_THM] do_app_ok;

Theorem dest_thunk_ok:
  state_ok s ∧
  dest_thunk vs s.refs = IsThunk m v ∧
  do_opapp [v; Conv NONE []] = SOME (env,e) ⇒
    state_ok (dec_clock s) ∧ env_ok (dec_clock s) env
Proof
  rw []
  >- gvs [dec_clock_def, state_ok_def, state_rel_def]
  \\ gvs [do_opapp_def, AllCaseEqs()]
  >- (
    gvs [dec_clock_def, env_ok_def, env_rel_def]
    \\ irule_at Any nsAll2_nsBind \\ gvs []
    \\ conj_tac >- simp [v_rel_def]
    \\ gvs [state_ok_def, state_rel_def, FLOOKUP_FUN_FMAP]
    \\ gvs [oneline dest_thunk_def, AllCaseEqs(), store_lookup_def]
    \\ first_x_assum drule \\ rw [ref_rel_def, v_rel_def, env_rel_def])
  \\ simp [env_ok_def, env_rel_def, dec_clock_def]
  \\ irule_at Any nsAll2_nsBind \\ gvs []
  \\ conj_tac >- simp [v_rel_def]
  \\ simp [semanticPrimitivesPropsTheory.build_rec_env_merge]
  \\ irule_at Any nsAll2_nsAppend \\ gvs []
  \\ irule_at Any nsAll2_alist_to_ns \\ gvs []
  \\ gs [EVERY2_MAP, LAMBDA_PROD, v_rel_def, env_rel_def]
  \\ rw [ELIM_UNCURRY, LIST_REL_EL_EQN]
  \\ gvs [state_ok_def, state_rel_def, FLOOKUP_FUN_FMAP]
  \\ gvs [oneline dest_thunk_def, AllCaseEqs(), store_lookup_def]
  \\ first_x_assum drule \\ rw [ref_rel_def, v_rel_def, env_rel_def]
QED

Theorem evaluate_ok_Op:
  op ≠ Opapp ∧ op ≠ Eval ⇒ ^(get_goal "App")
Proof
  strip_tac
  \\ ‘~ (getOpClass op = EvalOp)’ by (
    Cases_on ‘op’ \\ gs[] \\ Cases_on ‘t’ \\ gs[])
  \\ ‘~ (getOpClass op = FunApp)’ by (
    Cases_on ‘op’ \\ gs[] \\ Cases_on ‘t’ \\ gs[])
  \\ rpt strip_tac
  \\ gs[evaluate_def, Excl "getOpClass_def"]
  \\ Cases_on ‘getOpClass op’ \\ gs[Excl "getOpClass_def"]
  >>~ [‘getOpClass op = Force’]
  >- (
    Cases_on ‘op’ \\ full_simp_tac (srw_ss()) []
    \\ Cases_on ‘t'’ \\ full_simp_tac (srw_ss()) [AllCaseEqs()] \\ gvs []
    >- (
      drule_all dest_thunk_ok \\ rw [] \\ gvs []
      \\ qpat_x_assum ‘state_ok st2’ mp_tac
      \\ rw [state_ok_def, state_rel_def] \\ gvs [FLOOKUP_FUN_FMAP]
      >- simp [INJ_DEF, FUN_FMAP_DEF]
      \\ rw []
      \\ gvs [oneline update_thunk_def, AllCaseEqs(), store_assign_def,
              EL_LUPDATE]
      \\ IF_CASES_TAC \\ gvs [ref_rel_def, v_ok_def])
    >- (drule_all dest_thunk_ok \\ gvs []))
  >- (
    Cases_on ‘op’ \\ full_simp_tac (srw_ss()) []
    \\ Cases_on ‘t'’ \\ full_simp_tac (srw_ss()) [AllCaseEqs()] \\ gvs []
    \\ (
      drule_all dest_thunk_ok \\ rw [] \\ gvs []
      \\ imp_res_tac (CONJUNCT1 evaluate_next_type_stamp_mono)
      \\ imp_res_tac (CONJUNCT1 evaluate_next_exn_stamp_mono)
      \\ imp_res_tac (CONJUNCT1 evaluate_refs_length_mono)
      \\ gvs [dec_clock_def, env_ok_def]
      \\ irule env_rel_update
      \\ first_assum (irule_at Any)
      \\ gvs [oneline update_thunk_def, AllCaseEqs(), store_assign_def,
              FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO]))
  >- (
    Cases_on ‘op’ \\ full_simp_tac (srw_ss()) []
    \\ Cases_on ‘t'’ \\ full_simp_tac (srw_ss()) [AllCaseEqs()] \\ gvs []
    >- (
      gvs [oneline dest_thunk_def, AllCaseEqs(), store_lookup_def]
      \\ qpat_x_assum ‘state_ok st'’ mp_tac
      \\ rw [state_ok_def, state_rel_def] \\ gvs [FLOOKUP_FUN_FMAP]
      \\ first_x_assum drule \\ rw [ref_rel_def, v_ok_def])
    \\ drule_all dest_thunk_ok \\ rw [] \\ gvs []
    \\ gvs [EVERY_EL, v_ok_def, oneline update_thunk_def, AllCaseEqs(),
            store_assign_def])
  >- (
    Cases_on ‘op’ \\ full_simp_tac (srw_ss()) []
    \\ Cases_on ‘t'’ \\ full_simp_tac (srw_ss()) [AllCaseEqs()] \\ gvs []
    \\ drule_all dest_thunk_ok \\ gvs [])
  \\ gvs [CaseEqs ["prod", "result", "option"]]
  \\ dxrule_then assume_tac (iffRL EVERY_REVERSE)
  \\ drule_all_then assume_tac do_app_ok \\ gs []
  \\ gs [env_ok_def]
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_type_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_exn_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_refs_length_mono)
  \\ drule_then assume_tac do_app_refs_length
  \\ TRY (rename1 ‘_ = Icing’ \\ Cases_on ‘isFpBool op’ \\ gs[]
          \\ every_case_tac \\ gs[] \\ rveq \\ gs[])
  \\ irule env_rel_update
  \\ first_assum (irule_at Any)
  \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO]
QED

Theorem do_opapp_cases[local] = semanticPrimitivesPropsTheory.do_opapp_cases;

Theorem do_opapp_update:
  do_opapp vs = SOME (env, x) ∧
  EVERY (v_ok s) vs ∧
  state_ok s ⇒
    env_ok s env
Proof
  rw [do_opapp_cases] \\ gs [v_ok_thm, env_ok_def]
  \\ gs [semanticPrimitivesPropsTheory.find_recfun_ALOOKUP, v_ok_def]
  >- (
    irule_at Any env_rel_nsBind \\ gs [])
  \\ gs [env_rel_def, semanticPrimitivesPropsTheory.build_rec_env_merge]
  \\ irule nsAll2_nsBind \\ gs []
  \\ irule nsAll2_nsAppend \\ gs []
  \\ irule nsAll2_alist_to_ns \\ gs []
  \\ gs [EVERY2_MAP, LAMBDA_PROD, v_rel_def, env_rel_def]
  \\ rw [ELIM_UNCURRY, LIST_REL_EL_EQN]
QED

Theorem evaluate_ok_Opapp:
  op = Opapp ⇒ ^(get_goal "App")
Proof
  simp [evaluate_def]
  \\ strip_tac
  \\ strip_tac
  \\ rpt gen_tac
  \\ strip_tac
  \\ qpat_x_assum ‘_ = (t,res)’ mp_tac
  \\ TOP_CASE_TAC \\ rfs []
  \\ reverse TOP_CASE_TAC \\ rfs []
  >- (
    rw [] \\ gs [])
  \\ TOP_CASE_TAC \\ gs []
  \\ TOP_CASE_TAC \\ gs []
  \\ IF_CASES_TAC \\ gs []
  >- (
    rw [] \\ gs [])
  \\ strip_tac
  \\ rename1 ‘evaluate (dec_clock s1) env1’
  \\ ‘state_ok (dec_clock s1)’
    by (qpat_x_assum ‘state_ok s1’ mp_tac
        \\ rw [state_ok_def, dec_clock_def, state_rel_def]
        \\ gs [])
  \\ dxrule_then assume_tac (iffRL EVERY_REVERSE)
  \\ drule_all_then assume_tac do_opapp_update
  \\ ‘env_ok (dec_clock s1) env1’
    by gs [env_ok_def, dec_clock_def]
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_type_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_exn_stamp_mono)
  \\ dxrule_then assume_tac (CONJUNCT1 evaluate_refs_length_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_type_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_exn_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_refs_length_mono)
  \\ gs [dec_clock_def, env_ok_def]
  \\ irule env_rel_update
  \\ first_assum (irule_at Any)
  \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO]
QED

Theorem evaluate_ok_App:
  ^(get_goal "App")
Proof
  Cases_on ‘op = Opapp’ >- (match_mp_tac evaluate_ok_Opapp \\ gs [])
  \\ Cases_on ‘op = Eval’ >- (match_mp_tac evaluate_ok_Eval \\ gs [])
  \\ match_mp_tac evaluate_ok_Op \\ gs []
QED

Theorem v_ok_do_log:
  state_ok s ∧
  v_ok s v ∧
  do_log lop v x = SOME (Val w) ⇒ v_ok s w
Proof
  rw [] \\ gs []
  \\ gs [do_log_def, CaseEq "bool"]
QED

Theorem evaluate_ok_Log:
  ^(get_goal "Log")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option", "prod", "result", "bool", "exp_or_val"]]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ drule_all_then assume_tac v_ok_do_log \\ gs []
QED

Theorem evaluate_ok_If:
  ^(get_goal "If")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option", "prod", "result", "bool", "exp_or_val"]]
QED

Theorem v_ok_bind_exn[simp]:
  state_ok s ⇒ v_ok s bind_exn_v
Proof
  rw [state_ok_def, state_rel_def, v_ok_thm, stamp_ok_def, stamp_rel_cases,
      bind_exn_v_def, bind_stamp_def]
QED

Theorem evaluate_ok_Mat:
  ^(get_goal "Mat")
Proof
  simp [evaluate_def]
  \\ strip_tac
  \\ rpt gen_tac
  \\ strip_tac
  \\ qpat_x_assum ‘_ = (t,res)’ mp_tac
  \\ TOP_CASE_TAC \\ rfs []
  \\ reverse TOP_CASE_TAC \\ rfs []
  >- (
    rw [] \\ gs [])
  \\ IF_CASES_TAC \\ gs []
  \\ strip_tac
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
QED

Theorem evaluate_ok_Let:
  ^(get_goal "Let")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option", "prod", "result", "bool"]]
  \\ imp_res_tac evaluate_sing \\ gvs []
  \\ drule_all_then assume_tac evaluate_env_ok_mono
  \\ rename1 ‘env_ok st1 (env with v := nsOptBind xo v1 env.v)’
  \\ ‘env_ok st1 (env with v := nsOptBind xo v1 env.v)’
    by (Cases_on ‘xo’ \\ gs [namespaceTheory.nsOptBind_def, env_rel_def,
                           env_ok_def]
        \\ irule nsAll2_nsBind \\ gs [] \\ gs [GSYM v_ok_def])
  \\ drule_all_then assume_tac evaluate_env_ok_mono \\ gs []
  \\ gs [env_ok_def]
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_type_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_exn_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_refs_length_mono)
  \\ irule env_rel_update
  \\ first_assum (irule_at Any)
  \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO]
QED

Theorem evaluate_ok_Letrec:
  ^(get_goal "Letrec")
Proof
  rw [evaluate_def] \\ gs [SF SFY_ss]
  \\ rename1 ‘env_ok st (env with v := build_rec_env funs env env.v)’
  \\ ‘env_ok st (env with v := build_rec_env funs env env.v)’
    by (gs [env_rel_def, semanticPrimitivesPropsTheory.build_rec_env_merge,
            env_ok_def]
        \\ irule nsAll2_nsAppend \\ gs []
        \\ irule nsAll2_alist_to_ns
        \\ rw [EVERY2_MAP, LAMBDA_PROD, LIST_REL_EL_EQN]
        \\ simp [ELIM_UNCURRY, v_rel_def, env_rel_def])
  \\ drule_all_then assume_tac evaluate_env_ok_mono \\ gs []
  \\ gs [env_ok_def]
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_type_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_exn_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_refs_length_mono)
  \\ irule env_rel_update
  \\ first_assum (irule_at Any)
  \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO]
QED

Theorem evaluate_ok_Tannot:
  ^(get_goal "Tannot")
Proof
  rw [evaluate_def]
QED

Theorem evaluate_ok_Lannot:
  ^(get_goal "Lannot")
Proof
  rw [evaluate_def]
QED

Theorem evaluate_ok_pmatch_Nil:
  ^(get_goal "[]:(pat # exp) list")
Proof
  rw [evaluate_def] \\ gs []
QED

Theorem pmatch_ok:
  pmatch env.c s.refs p v ws = Match env1 ∧
  state_ok s ∧
  env_ok s env ∧
  v_ok s v ∧
  EVERY (v_ok s) (MAP SND ws) ⇒
    EVERY (v_ok s) (MAP SND env1)
Proof
  rw [state_ok_def, env_ok_def, v_ok_def, env_rel_def, state_rel_def]
  \\ drule (CONJUNCT1 pmatch_update)
  \\ rpt (disch_then drule) \\ gs []
  \\ rpt (disch_then drule) \\ gs []
  \\ disch_then (qspecl_then [‘s.refs’, ‘ws’] mp_tac) \\ simp []
  \\ gs [EVERY_MAP, EVERY2_MAP, LIST_REL_EL_EQN, EVERY_EL, v_ok_def]
  \\ rw [ELIM_UNCURRY]
QED

Theorem evaluate_ok_pmatch_Cons:
  ^(get_goal "_::_:(pat # exp) list")
Proof
  rw [evaluate_def] \\ gs [CaseEqs ["match_result"]]
  \\ rename1 ‘env_ok st (env with v := nsAppend (alist_to_ns env1) env.v)’
  \\ drule pmatch_ok \\ rw [] \\ gs []
  \\ ‘env_ok st (env with v := nsAppend (alist_to_ns env1) env.v)’
    by (gs [env_ok_def, env_rel_def]
        \\ irule nsAll2_nsAppend \\ gs []
        \\ irule nsAll2_alist_to_ns
        \\ gs [EVERY2_MAP, EVERY_EL]
        \\ rw [LIST_REL_EL_EQN, ELIM_UNCURRY]
        \\ gs [GSYM v_ok_def, EL_MAP])
  \\ drule_all_then assume_tac evaluate_env_ok_mono \\ gs []
  \\ gs [env_ok_def]
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_type_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_exn_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_refs_length_mono)
  \\ irule env_rel_update
  \\ first_assum (irule_at Any)
  \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO]
QED

Theorem evaluate_ok_decs_Nil:
  ^(get_goal "[]:dec list")
Proof
  rw [evaluate_decs_def, extend_dec_env_def]
  \\ gs [env_ok_def, env_rel_def, ctor_rel_def]
QED

Theorem env_ok_extend_dec_env:
  env_ok s env ∧
  state_ok s ∧
  env_ok s env1 ⇒
    env_ok s (extend_dec_env env1 env)
Proof
  rw [env_ok_def]
  \\ irule env_rel_extend_dec_env \\ gs []
QED

Theorem env_ok_nsAppend:
  env_ok s env ∧
  state_ok s ∧
  env_ok s env1 ⇒
    env_ok s <| v := nsAppend env1.v env.v; c := nsAppend env1.c env.c |>
Proof
  rw [env_ok_def]
  \\ irule env_rel_nsAppend \\ gs []
QED

Theorem evaluate_ok_decs_Cons:
  ^(get_goal "_::_::_:dec list")
Proof
  simp [evaluate_decs_def]
  \\ strip_tac \\ rpt gen_tac \\ strip_tac
  \\ qpat_x_assum ‘_ = (t,res)’ mp_tac
  \\ TOP_CASE_TAC \\ fs []
  \\ reverse TOP_CASE_TAC \\ fs []
  >- (
    rw [] \\ gs [])
  \\ simp [CaseEq "prod"]
  \\ strip_tac \\ gvs []
  \\ rename1 ‘combine_dec_result vs res’
  \\ ‘res ≠ Rerr (Rabort Rtype_error)’
    by (strip_tac \\ gs [combine_dec_result_def])
  \\ gs [combine_dec_result_def]
  \\ CASE_TAC \\ gs []
  \\ qpat_x_assum ‘env_ok _ env’ assume_tac
  \\ drule_then (qspec_then ‘vs’ assume_tac) env_ok_extend_dec_env \\ gs []
  \\ rename1 ‘env_ok st2 (extend_dec_env vs env)’
  \\ qspecl_then [‘st’,‘env’,‘[d1]’] mp_tac is_clock_io_mono_evaluate_decs
  \\ qspecl_then [‘st2’,‘extend_dec_env vs env’,‘d2::ds’] mp_tac
                 is_clock_io_mono_evaluate_decs
  \\ rw [is_clock_io_mono_def]
  >~ [‘env_ok t <| v := _; c := _ |>’] >- (
    irule env_ok_nsAppend \\ gs []
    \\ gs [env_ok_def]
    \\ irule env_rel_update
    \\ first_assum (irule_at Any)
    \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO])
  \\ gs [env_ok_def]
  \\ irule env_rel_update
  \\ first_assum (irule_at Any)
  \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO]
QED

Theorem evaluate_ok_decs_Dlet:
  ^(get_goal "Dlet")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["prod", "result", "match_result"]]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ drule pmatch_ok \\ gs [] \\ rw []
  \\ gs [env_ok_def, env_rel_def, ctor_rel_def]
  \\ irule nsAll2_alist_to_ns \\ gs []
  \\ gvs [LIST_REL_EL_EQN, v_ok_def, EVERY_EL, ELIM_UNCURRY, EL_MAP]
QED

Theorem evaluate_ok_decs_Dletrec:
  ^(get_goal "Dletrec")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["prod", "result"]]
  \\ gs [env_rel_def, ctor_rel_def, env_ok_def,
         semanticPrimitivesPropsTheory.build_rec_env_merge]
  \\ irule_at Any nsAll2_alist_to_ns
  \\ gs [EVERY2_MAP, LAMBDA_PROD]
  \\ rw [v_rel_def, LIST_REL_EL_EQN, ELIM_UNCURRY, env_rel_def, ctor_rel_def]
QED

Theorem state_ok_with_next_type_stamp:
  state_ok s ∧
  env_ok s env ⇒
    let s' = s with next_type_stamp := extra + s.next_type_stamp in
    state_ok s' ∧
    env_ok s' env
Proof
  rw [state_ok_def, state_rel_def]
  \\ gs [FLOOKUP_FUN_FMAP, INJ_IFF, FUN_FMAP_DEF]
  >- (
    strip_tac
    \\ first_x_assum (drule_then assume_tac)
    \\ irule ref_rel_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ irule v_rel_update
    \\ first_assum (irule_at Any)
    \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO])
  \\ gs [env_ok_def, env_rel_def]
  \\ irule_at Any ctor_rel_update
  \\ first_assum (irule_at Any)
  \\ irule_at Any nsAll2_mono
  \\ first_assum (irule_at Any)
  \\ simp [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO] \\ rw []
  \\ irule_at Any v_rel_update
  \\ first_assum (irule_at Any)
  \\ simp [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO]
QED

Theorem state_ok_with_next_exn_stamp:
  state_ok s ∧
  env_ok s env ⇒
    let s' = s with next_exn_stamp := extra + s.next_exn_stamp in
    state_ok s' ∧
    env_ok s' env
Proof
  rw [state_ok_def, state_rel_def]
  \\ gs [FLOOKUP_FUN_FMAP, INJ_IFF, FUN_FMAP_DEF]
  >- (
    strip_tac
    \\ first_x_assum (drule_then assume_tac)
    \\ irule ref_rel_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ irule v_rel_update
    \\ first_assum (irule_at Any)
    \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO])
  \\ gs [env_ok_def, env_rel_def]
  \\ irule_at Any ctor_rel_update
  \\ first_assum (irule_at Any)
  \\ irule_at Any nsAll2_mono
  \\ first_assum (irule_at Any)
  \\ simp [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO] \\ rw []
  \\ irule_at Any v_rel_update
  \\ first_assum (irule_at Any)
  \\ simp [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO]
QED

Theorem evaluate_ok_decs_Dtype:
  ^(get_goal "Dtype")
Proof
  simp [evaluate_decs_def]
  \\ strip_tac
  \\ gvs [CaseEq "bool"]
  \\ drule_all_then (qspec_then ‘LENGTH tds’ assume_tac)
                    state_ok_with_next_type_stamp
  \\ gs []
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ rw [state_ok_def, env_ok_def, state_rel_def, env_rel_def]
  \\ simp [ctor_rel_def]
  \\ rename1 ‘_ (_ _ (count (LENGTH tds + n))) (_ _ (count m))’
  \\ qid_spec_tac ‘m’
  \\ qid_spec_tac ‘tds’
  \\ qid_spec_tac ‘n’
  \\ rpt (pop_assum kall_tac)
  \\ ho_match_mp_tac build_tdefs_ind
  \\ simp [build_tdefs_def] \\ rw []
  \\ irule nsAll2_nsAppend \\ gs []
  \\ irule_at Any nsAll2_alist_to_ns \\ gs []
  \\ gs [build_constrs_def, EVERY2_MAP, LAMBDA_PROD, stamp_rel_cases,
         FLOOKUP_FUN_FMAP]
  \\ simp [LIST_REL_EL_EQN, ELIM_UNCURRY, ADD1]
QED

Theorem evaluate_ok_decs_Dtabbrev:
  ^(get_goal "Dtabbrev")
Proof
  rw [evaluate_decs_def]
  \\ gs [env_ok_def, env_rel_def, ctor_rel_def]
QED

Theorem state_ok_declare_env[local]:
  state_ok s ⇒
    ∀env. declare_env s.eval_state env = NONE
Proof
  rw [state_ok_def, state_rel_def, declare_env_def]
QED

Theorem evaluate_ok_decs_Denv:
  ^(get_goal "Denv")
Proof
  rw [evaluate_decs_def]
  \\ gs [state_ok_declare_env]
QED

Theorem evaluate_ok_decs_Dexn:
  ^(get_goal "Dexn")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod"]]
  \\ drule_all_then (qspec_then ‘1’ assume_tac)
                    state_ok_with_next_exn_stamp \\ gs []
  \\ gs [env_ok_def, env_rel_def, ctor_rel_def, stamp_rel_cases,
         FLOOKUP_FUN_FMAP]
QED

Theorem evaluate_ok_decs_Dmod:
  ^(get_goal "Dmod")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod", "result"]]
  \\ gs [env_ok_def, env_rel_def, ctor_rel_def]
QED

Theorem evaluate_ok_decs_Dlocal:
  ^(get_goal "Dlocal")
Proof
  simp [evaluate_decs_def]
  \\ strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ qpat_x_assum ‘_ = (t,res)’ mp_tac
  \\ TOP_CASE_TAC \\ fs []
  \\ reverse TOP_CASE_TAC \\ fs []
  >- (
    rw [] \\ gs [])
  \\ strip_tac \\ gs []
  \\ rename1 ‘env_ok st2 (extend_dec_env env1 env)’
  \\ qpat_x_assum ‘env_ok _ env’ assume_tac
  \\ drule_then (qspec_then ‘env1’ assume_tac) env_ok_extend_dec_env \\ gs []
  \\ qspecl_then [‘st’,‘env’,‘lds’] mp_tac is_clock_io_mono_evaluate_decs
  \\ qspecl_then [‘st2’,‘extend_dec_env env1 env’,‘ds’] mp_tac
                  is_clock_io_mono_evaluate_decs
  \\ rw [is_clock_io_mono_def]
  \\ gs [env_ok_def]
  \\ irule env_rel_update
  \\ first_assum (irule_at Any)
  \\ gs [FUN_FMAP_SUBMAP_SUBSET, COUNT_MONO]
QED

Theorem evaluate_ok:
  ^(evaluate_ok ())
Proof
  match_mp_tac (the_ind_thm ())
  \\ rpt conj_tac \\ rpt gen_tac
  \\ rewrite_tac [evaluate_ok_Nil, evaluate_ok_Cons,
                  evaluate_ok_Lit, evaluate_ok_Raise,
                  evaluate_ok_Handle, evaluate_ok_Con,
                  evaluate_ok_Var, evaluate_ok_Fun,
                  evaluate_ok_App, evaluate_ok_Log,
                  evaluate_ok_If, evaluate_ok_Mat,
                  evaluate_ok_Let, evaluate_ok_Letrec,
                  evaluate_ok_Tannot, evaluate_ok_Lannot,
                  evaluate_ok_pmatch_Nil, evaluate_ok_pmatch_Cons,
                  evaluate_ok_decs_Nil, evaluate_ok_decs_Cons,
                  evaluate_ok_decs_Dlet, evaluate_ok_decs_Dletrec,
                  evaluate_ok_decs_Dtype,
                  evaluate_ok_decs_Dtabbrev,
                  evaluate_ok_decs_Denv, evaluate_ok_decs_Dexn,
                  evaluate_ok_decs_Dmod, evaluate_ok_decs_Dlocal]
QED

(* -------------------------------------------------------------------------
 *  top-level results
 * ------------------------------------------------------------------------- *)

Theorem state_ok_init:
  state_ok (init_state ffi with clock := ck)
Proof
  rw [state_ok_def, state_rel_def, init_state_def, FLOOKUP_FUN_FMAP,
      INJ_IFF, FUN_FMAP_DEF, bool_type_num_def, list_type_num_def]
QED

Theorem env_ok_init:
  env_ok (init_state ffi with clock := ck) init_env
Proof
  rw [env_ok_def, env_rel_def, init_env_def, GSYM namespaceTheory.nsEmpty_def]
  \\ rw [ctor_rel_def, namespaceTheory.nsAll2_def, namespaceTheory.nsSub_def]
  \\ Cases_on ‘id’ \\ fs [namespaceTheory.nsLookup_def]
  \\ gvs [CaseEq "bool", stamp_rel_cases, FLOOKUP_FUN_FMAP, init_state_def]
QED

Theorem evaluate_decs_init:
  evaluate_decs (init_state ffi with clock := ck) init_env decs = (s,Rval env) ⇒
  ∃fr ft fe.
     fr = FUN_FMAP I (count (LENGTH s.refs)) ∧
     ft = FUN_FMAP I (count s.next_type_stamp) ∧
     fe = FUN_FMAP I (count s.next_exn_stamp) ∧
     state_rel (LENGTH s.refs) fr ft fe s s ∧
     env_rel fr ft fe (extend_dec_env env init_env)
                      (extend_dec_env env init_env)
Proof
  rpt strip_tac \\ simp [GSYM state_ok_def, GSYM env_ok_def]
  \\ drule (el 3 (CONJUNCTS evaluate_ok))
  \\ rw [state_ok_init, env_ok_init]
  \\ irule env_ok_extend_dec_env \\ gs []
QED
