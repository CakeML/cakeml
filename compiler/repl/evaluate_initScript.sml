(*
  Lemma used in repl_typesTheory: that evaluate_skip's invariant
  holds at initialisation.
*)

open preamble
open evaluateTheory semanticPrimitivesTheory evaluatePropsTheory
open namespacePropsTheory ml_progTheory
open evaluate_skipTheory
local open helperLib in end

val _ = new_theory "evaluate_init";

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
  ref_ok s (W8array a) = T
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
  (∀loc. v_ok s (Loc loc) ⇔ loc < LENGTH s.refs) ∧
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

Theorem v_rel_list_to_v:
  ∀v vs.
    v_to_list v = SOME vs ∧
    state_ok s ∧
    v_ok s v ⇒
      EVERY (v_ok s) vs
Proof
  ho_match_mp_tac v_to_list_ind
  \\ rw [] \\ gvs [v_ok_thm, v_to_list_def, CaseEq "option"]
QED

Theorem do_app_cases[local] = semanticPrimitivesPropsTheory.do_app_cases;

Theorem state_ok_refs_ok:
  state_ok s ⇒ EVERY (ref_ok s) s.refs
Proof
  rw [state_ok_def, ref_ok_def, state_rel_def, EVERY_EL]
  \\ first_x_assum (qspec_then ‘n’ assume_tac) \\ gs []
QED

Theorem do_app_update:
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
  cheat (*
  strip_tac
  \\ drule_then assume_tac state_ok_refs_ok
  \\ Cases_on ‘op = Env_id’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm]
    \\ first_x_assum (irule_at Any) \\ gs [v_ok_thm, nat_to_v_def])
  \\ Cases_on ‘∃chn. op = FFI chn’ \\ gs []
  >- (
    gvs [do_app_cases, v_ok_thm, ffiTheory.call_FFI_def, store_assign_def,
         store_lookup_def,
         CaseEqs ["ffi_result", "option", "bool", "oracle_result"]]
    \\ cheat)
    >- (
      qmatch_goalsub_abbrev_tac ‘_ :'a ffi_state = ffi2’
      \\ Q.REFINE_EXISTS_TAC ‘s with <| refs := r; ffi := f |>’ \\ simp []
      \\ simp [EVERY_LUPDATE]
    \\ simp
    \\ first_x_assum (irule_at Any)
    \\ gs [st]
    \\ first_x_assum (irule_at Any) \\ gs [v_ok_thm, nat_to_v_def])
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"], PULL_EXISTS]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup
    \\ ‘t.ffi = s.ffi’
      by gs [state_rel_def]
    \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gvs [ref_rel_def]
    >- (
      gvs [CaseEqs ["ffi_result", "option", "bool", "oracle_result"],
              ffiTheory.call_FFI_def, PULL_EXISTS, state_rel_def]
      \\ gs [store_assign_def, store_lookup_def, v_rel_def])
    \\ gvs [CaseEqs ["ffi_result", "option", "bool", "oracle_result"],
            ffiTheory.call_FFI_def, PULL_EXISTS, EXISTS_PROD, v_rel_def,
            store_assign_def, store_lookup_def]
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ qx_gen_tac ‘n1’ \\ rw [] \\ gs [ref_rel_def]
    \\ first_x_assum (qspec_then ‘n1’ assume_tac) \\ gs []
    \\ rw [] \\ gs []
    \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac \\ rw [INJ_DEF]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ gs [])
  \\ Cases_on ‘op = ConfigGC’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = ListAppend’ \\ gs []
  >- (
    ‘FLOOKUP ft list_type_num = SOME list_type_num ∧
     INJ ($' ft) (FDOM ft) (count t.next_type_stamp) ∧
     list_type_num < t.next_type_stamp’
      by (gs [state_rel_def]
          \\ qpat_x_assum ‘INJ ($' ft) _ _’ mp_tac \\ rw [INJ_DEF]
          \\ rpt (first_x_assum (qspec_then ‘list_type_num’ assume_tac))
          \\ gs [flookup_thm])
    \\ Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                              CaseEqs ["list", "v", "option", "prod", "lit"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ dxrule v_rel_v_to_list
    \\ rpt (disch_then drule) \\ gs []
    \\ disch_then drule \\ rw [OPTREL_def]
    \\ gs [option_nchotomy]
    \\ dxrule v_rel_v_to_list
    \\ rpt (disch_then drule) \\ gs []
    \\ disch_then drule \\ rw [OPTREL_def]
    \\ first_assum (irule_at Any)
    \\ first_assum (irule_at Any) \\ gs []
    \\ irule v_rel_list_to_v \\ gs []
    \\ irule_at Any v_to_list_list_to_v
    \\ irule_at Any v_to_list_list_to_v
    \\ gs [LIST_REL_EL_EQN, EL_APPEND_EQN]
    \\ rw [] \\ gs[])
  \\ Cases_on ‘op = Aw8sub_unsafe’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ rw [] \\ gs []
    \\ first_assum (irule_at Any) \\ gs [v_rel_def])
  \\ Cases_on ‘op = Aw8update_unsafe’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ gvs [store_assign_def, store_lookup_def]
    \\ rw [] \\ gs [v_rel_def]
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ qx_gen_tac ‘n1’
    \\ first_x_assum (qspec_then ‘n1’ assume_tac)
    \\ rw [] \\ gs [ref_rel_def]
    \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac \\ rw [INJ_DEF]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ gs [])
  \\ Cases_on ‘op = Aupdate_unsafe’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ gvs [store_assign_def, store_lookup_def, store_v_same_type_def]
    \\ rw [] \\ gs [v_rel_def]
    \\ drule_then assume_tac LIST_REL_LENGTH \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ qx_gen_tac ‘n1’
    \\ first_x_assum (qspec_then ‘n1’ assume_tac)
    \\ rw [] \\ gs [ref_rel_def]
    \\ gvs [LIST_REL_EL_EQN, EL_LUPDATE]
    \\ rw [] \\ gs []
    \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac \\ rw [INJ_DEF]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ gs [])
  \\ Cases_on ‘op = Asub_unsafe’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ rw [] \\ gs []
    \\ gs [LIST_REL_EL_EQN]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = Aupdate’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ gvs [store_assign_def, store_lookup_def, store_v_same_type_def]
    \\ rw [] \\ gs [v_rel_def]
    \\ drule_then assume_tac LIST_REL_LENGTH \\ gvs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE, sub_exn_v_def, v_rel_def, stamp_rel_cases,
           subscript_stamp_def]
    \\ qx_gen_tac ‘n1’
    \\ first_x_assum (qspec_then ‘n1’ assume_tac)
    \\ rw [] \\ gs [ref_rel_def]
    \\ gvs [LIST_REL_EL_EQN, EL_LUPDATE]
    \\ rw [] \\ gs []
    \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac \\ rw [INJ_DEF]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ gs [])
  \\ Cases_on ‘op = Alength’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def, v_rel_def]
    \\ gvs [store_assign_def, store_lookup_def, store_v_same_type_def]
    \\ drule_then assume_tac LIST_REL_LENGTH \\ gvs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def])
  \\ Cases_on ‘op = Asub’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ rw [] \\ gs []
    \\ gvs [LIST_REL_EL_EQN]
    \\ gs [state_rel_def, sub_exn_v_def, v_rel_def, stamp_rel_cases,
           subscript_stamp_def]
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs [])
  \\ Cases_on ‘op = AallocEmpty’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ TRY (rpt (irule_at Any SUBMAP_REFL) \\ gs [] \\ NO_TAC)
    \\ rpt (pairarg_tac \\ gs []) \\ gvs []
    \\ gvs [store_alloc_def, v_rel_def, PULL_EXISTS]
    \\ qexists_tac ‘fr |+ (LENGTH s.refs,LENGTH t.refs)’
    \\ irule_at Any SUBMAP_REFL
    \\ irule_at Any SUBMAP_REFL
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, FLOOKUP_UPDATE]
    \\ conj_tac
    >- (
      qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
      \\ simp [INJ_DEF, FAPPLY_FUPDATE_THM]
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ simp [count_add1]
    \\ strip_tac
    >- (
      qx_gen_tac ‘n’
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ qx_gen_tac ‘n’
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ rw [] \\ gs [EL_LENGTH_APPEND, ref_rel_def]
    \\ gs [EL_APPEND_EQN]
    \\ irule ref_rel_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ irule v_rel_update
    \\ Q.LIST_EXISTS_TAC [‘fe’,‘fr’,‘ft’] \\ gs [])
  \\ Cases_on ‘op = Aalloc’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ TRY (rpt (irule_at Any SUBMAP_REFL) \\ gs [] \\ NO_TAC)
    \\ rpt (pairarg_tac \\ gs []) \\ gvs []
    \\ gvs [store_alloc_def, v_rel_def, PULL_EXISTS, CaseEqs ["bool", "option"],
            v_rel_def, sub_exn_v_def, stamp_rel_cases, subscript_stamp_def]
    >- (
      rpt (irule_at Any SUBMAP_REFL \\ gs [])
      \\ first_assum (irule_at Any)
      \\ gs [state_rel_def])
    \\ qexists_tac ‘fr |+ (LENGTH s.refs,LENGTH t.refs)’
    \\ irule_at Any SUBMAP_REFL
    \\ irule_at Any SUBMAP_REFL
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, FLOOKUP_UPDATE, count_add1]
    \\ conj_tac
    >- (
      qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
      \\ simp [INJ_DEF, FAPPLY_FUPDATE_THM]
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ strip_tac
    >- (
      qx_gen_tac ‘n’
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ qx_gen_tac ‘n’
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ rw [] \\ gs [EL_APPEND_EQN, ref_rel_def, LIST_REL_REPLICATE_same]
    >- (
      rw []
      \\ irule v_rel_update
      \\ first_assum (irule_at (Pat ‘v_rel’)) \\ gs [])
    \\ irule ref_rel_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ irule v_rel_update
    \\ first_assum (irule_at (Pat ‘v_rel’)) \\ gs [])
  \\ Cases_on ‘op = Vlength’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ first_assum (irule_at Any)
    \\ gs [LIST_REL_EL_EQN])
  \\ Cases_on ‘op = Vsub’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ rw [] \\ gvs [CaseEqs ["bool", "option"]]
    \\ gvs [store_alloc_def, v_rel_def, PULL_EXISTS, CaseEqs ["bool", "option"],
            v_rel_def, sub_exn_v_def, stamp_rel_cases, subscript_stamp_def]
    \\ first_assum (irule_at Any)
    \\ gs [state_rel_def, LIST_REL_EL_EQN])
  \\ Cases_on ‘op = VfromList’ \\ gs []
  >- (
    ‘FLOOKUP ft list_type_num = SOME list_type_num ∧
     INJ ($' ft) (FDOM ft) (count t.next_type_stamp) ∧
     list_type_num < t.next_type_stamp’
      by (gs [state_rel_def]
          \\ qpat_x_assum ‘INJ ($' ft) _ _’ mp_tac \\ rw [INJ_DEF]
          \\ rpt (first_x_assum (qspec_then ‘list_type_num’ assume_tac))
          \\ gs [flookup_thm])
    \\ Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                              CaseEqs ["list", "v", "option", "prod", "lit",
                                       "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ rename1 ‘v_rel _ _ _ x1 x2’
    \\ ‘∃res. v_to_list x2 = res’ by gs []
    \\ drule_all v_rel_v_to_list \\ rw [OPTREL_def]
    \\ first_assum (irule_at Any) \\ gs [v_rel_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = Strcat’ \\ gs []
  >- (
    ‘FLOOKUP ft list_type_num = SOME list_type_num ∧
     INJ ($' ft) (FDOM ft) (count t.next_type_stamp) ∧
     list_type_num < t.next_type_stamp’
      by (gs [state_rel_def]
          \\ qpat_x_assum ‘INJ ($' ft) _ _’ mp_tac \\ rw [INJ_DEF]
          \\ rpt (first_x_assum (qspec_then ‘list_type_num’ assume_tac))
          \\ gs [flookup_thm])
    \\ Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                              CaseEqs ["list", "v", "option", "prod", "lit",
                                       "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ rename1 ‘v_rel _ _ _ x1 x2’
    \\ ‘∃res. v_to_list x2 = res’ by gs []
    \\ drule_all v_rel_v_to_list \\ rw [OPTREL_def]
    \\ gs [option_nchotomy]
    \\ rename1 ‘LIST_REL _ y1 y2’
    \\ ‘∃res. vs_to_string y2 = res’ by gs []
    \\ drule_all v_rel_vs_to_string \\ rw []
    \\ gs [v_rel_def]
    \\ first_assum (irule_at Any)
    \\ irule_at Any EQ_REFL \\ gs [])
  \\ Cases_on ‘op = Strlen’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = Strsub’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ rw [] \\ gvs []
    \\ first_assum (irule_at Any) \\ gs []
    \\ gs [v_rel_def, sub_exn_v_def, stamp_rel_cases, subscript_stamp_def,
           state_rel_def])
  \\ Cases_on ‘op = Explode’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ gs [v_rel_def]
    \\ first_assum (irule_at Any) \\ gs []
    \\ irule v_rel_list_to_v
    \\ irule_at Any v_to_list_list_to_v
    \\ irule_at Any v_to_list_list_to_v
    \\ gs [state_rel_def, EVERY2_MAP, LIST_REL_EL_EQN, v_rel_def])
  \\ Cases_on ‘op = Implode’ \\ gs []
  >- (
    ‘FLOOKUP ft list_type_num = SOME list_type_num ∧
     INJ ($' ft) (FDOM ft) (count t.next_type_stamp) ∧
     list_type_num < t.next_type_stamp’
      by (gs [state_rel_def]
          \\ qpat_x_assum ‘INJ ($' ft) _ _’ mp_tac \\ rw [INJ_DEF]
          \\ rpt (first_x_assum (qspec_then ‘list_type_num’ assume_tac))
          \\ gs [flookup_thm])
    \\ Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                              CaseEqs ["list", "v", "option", "prod", "lit",
                                       "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ rename1 ‘v_rel _ _ _ x1 x2’
    \\ ‘∃res. v_to_char_list x2 = res’ by gs []
    \\ drule_all v_rel_v_to_char_list \\ rw []
    \\ first_assum (irule_at Any)
    \\ gs [v_rel_def])
  \\ Cases_on ‘∃opb. op = Chopb opb’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ first_assum (irule_at Any) \\ gs []
    \\ gs [Boolv_def] \\ rw []
    \\ gs [v_rel_def, stamp_rel_cases, state_rel_def])
  \\ Cases_on ‘op = Chr’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ first_assum (irule_at Any) \\ gs []
    \\ rw [] \\ gs [v_rel_def, chr_exn_v_def, stamp_rel_cases, chr_stamp_def,
                    state_rel_def])
  \\ Cases_on ‘op = Ord’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = CopyAw8Aw8’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"], PULL_EXISTS]
    \\ rpt (irule_at Any SUBMAP_REFL \\ gs [])
    \\ imp_res_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rpt (rename [‘ref_rel _ (_ _) y0’] \\ Cases_on ‘y0’ \\ gvs [ref_rel_def])
    \\ gvs [store_assign_def, store_lookup_def, copy_array_def,
            v_rel_def, sub_exn_v_def, subscript_stamp_def, stamp_rel_cases]
    >- (
      first_assum (irule_at Any)
      \\ gs [state_rel_def])
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ qx_gen_tac ‘n1’
    \\ first_x_assum (qspec_then ‘n1’ mp_tac)
    \\ rw [] \\ gs [ref_rel_def]
    \\ rw [] \\ gs [ref_rel_def]
    \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
    \\ rpt (qpat_x_assum ‘FLOOKUP _ _ = _’ mp_tac)
    \\ rw [flookup_thm, INJ_DEF] \\ gs [])
  \\ Cases_on ‘op = CopyAw8Str’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"], PULL_EXISTS]
    \\ rpt (irule_at Any SUBMAP_REFL \\ gs [])
    \\ imp_res_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rpt (rename [‘ref_rel _ (_ _) y0’] \\ Cases_on ‘y0’ \\ gvs [ref_rel_def])
    \\ gvs [store_assign_def, store_lookup_def, copy_array_def,
            v_rel_def, sub_exn_v_def, subscript_stamp_def, stamp_rel_cases]
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ rw [] \\ gs [ref_rel_def, v_rel_def, stamp_rel_cases])
  \\ Cases_on ‘op = CopyStrAw8’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"], PULL_EXISTS]
    \\ rpt (irule_at Any SUBMAP_REFL \\ gs [])
    \\ imp_res_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rpt (rename [‘ref_rel _ (_ _) y0’] \\ Cases_on ‘y0’ \\ gvs [ref_rel_def])
    \\ gvs [store_assign_def, store_lookup_def, copy_array_def,
            v_rel_def, sub_exn_v_def, subscript_stamp_def, stamp_rel_cases]
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ qx_gen_tac ‘n1’
    \\ first_x_assum (qspec_then ‘n1’ mp_tac)
    \\ rw [] \\ gs [ref_rel_def]
    \\ rw [] \\ gs [ref_rel_def]
    \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
    \\ rpt (qpat_x_assum ‘FLOOKUP _ _ = _’ mp_tac)
    \\ rw [flookup_thm, INJ_DEF] \\ gs [])
  \\ Cases_on ‘op = CopyStrStr’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"], PULL_EXISTS]
    \\ rpt (irule_at Any SUBMAP_REFL \\ gs [])
    \\ imp_res_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rpt (rename [‘ref_rel _ (_ _) y0’] \\ Cases_on ‘y0’ \\ gvs [ref_rel_def])
    \\ gvs [store_assign_def, store_lookup_def, copy_array_def,
            v_rel_def, sub_exn_v_def, subscript_stamp_def, stamp_rel_cases]
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ rw [] \\ gs [ref_rel_def, v_rel_def, stamp_rel_cases])
  \\ Cases_on ‘∃n. op = WordToInt n’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v", "word_size"], PULL_EXISTS]
    \\ rpt (irule_at Any SUBMAP_REFL \\ gs [])
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘∃n. op = WordFromInt n’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v", "word_size"], PULL_EXISTS]
    \\ rpt (irule_at Any SUBMAP_REFL \\ gs [])
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = Aw8update’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ gvs [store_assign_def, store_lookup_def]
    \\ rw [] \\ gvs [v_rel_def, sub_exn_v_def, subscript_stamp_def,
                     stamp_rel_cases]
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ qx_gen_tac ‘n1’
    \\ first_x_assum (qspec_then ‘n1’ assume_tac)
    \\ rw [] \\ gs [ref_rel_def]
    \\ rw [] \\ gs [ref_rel_def]
    \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac \\ rw [INJ_DEF]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ gs [])
  \\ Cases_on ‘op = Aw8sub’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ rw [] \\ gvs [LIST_REL_EL_EQN, v_rel_def, sub_exn_v_def,
                     subscript_stamp_def, stamp_rel_cases]
    \\ first_assum (irule_at Any) \\ gs [state_rel_def])
  \\ Cases_on ‘op = Aw8length’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ rw [] \\ gvs [LIST_REL_EL_EQN, v_rel_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = Aw8alloc’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ TRY (rpt (irule_at Any SUBMAP_REFL) \\ gs [] \\ NO_TAC)
    \\ rpt (pairarg_tac \\ gs []) \\ gvs []
    \\ gvs [store_alloc_def, v_rel_def, PULL_EXISTS, CaseEqs ["bool", "option"],
            v_rel_def, sub_exn_v_def, stamp_rel_cases, subscript_stamp_def]
    >- (
      rpt (irule_at Any SUBMAP_REFL \\ gs [])
      \\ first_assum (irule_at Any)
      \\ gs [state_rel_def])
    \\ qexists_tac ‘fr |+ (LENGTH s.refs,LENGTH t.refs)’
    \\ irule_at Any SUBMAP_REFL
    \\ irule_at Any SUBMAP_REFL
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, FLOOKUP_UPDATE, count_add1]
    \\ conj_tac
    >- (
      qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
      \\ simp [INJ_DEF, FAPPLY_FUPDATE_THM]
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ strip_tac
    >- (
      qx_gen_tac ‘n’
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ qx_gen_tac ‘n’
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ rw [] \\ gs [EL_APPEND_EQN, ref_rel_def, LIST_REL_REPLICATE_same]
    \\ irule ref_rel_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ irule v_rel_update
    \\ first_assum (irule_at (Pat ‘v_rel’)) \\ gs [])
  \\ Cases_on ‘∃top. op = FP_top top’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘∃bop. op = FP_bop bop’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘∃uop. op = FP_uop uop’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘∃cmp. op = FP_cmp cmp’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ first_assum (irule_at Any) \\ gs []
    \\ gs [Boolv_def] \\ rw [v_rel_def, stamp_rel_cases]
    \\ gs [state_rel_def])
  \\ Cases_on ‘∃opn. op = Opn opn’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ rw [] \\ gvs []
    \\ first_assum (irule_at Any) \\ gs []
    \\ gs [v_rel_def, div_exn_v_def, div_stamp_def, stamp_rel_cases,
           state_rel_def])
  \\ Cases_on ‘∃opb. op = Opb opb’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ rw [] \\ gvs []
    \\ first_assum (irule_at Any) \\ gs []
    \\ gs [Boolv_def] \\ rw [v_rel_def, stamp_rel_cases]
    \\ gs [state_rel_def])
  \\ Cases_on ‘∃sz opw. op = Opw sz opw’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v", "word_size"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘∃sz sh n. op = Shift sz sh n’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v", "word_size"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = Equality’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v", "word_size"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ gs [CaseEqs ["eq_result"], EXISTS_PROD, PULL_EXISTS]
    \\ gs [state_rel_def]
    \\ rename1 ‘v_rel _ _ _ x1 x2’ \\ rename1 ‘v_rel _ _ _ y1 y2’
    >- (
      qpat_assum ‘do_eq _ _ = _’ (SUBST1_TAC o SYM)
      \\ once_rewrite_tac [EQ_SYM_EQ]
      \\ irule (CONJUNCT1 v_rel_do_eq)
      \\ first_assum (irule_at Any) \\ gs []
      \\ first_assum (irule_at Any) \\ gs []
      \\ first_assum (irule_at Any) \\ gs []
      \\ first_assum (irule_at Any) \\ gs [])
    \\ qexists_tac ‘b’
    \\ qpat_assum ‘do_eq _ _ = _’ (SUBST1_TAC o SYM)
    \\ simp_tac std_ss [Once EQ_SYM_EQ]
    \\ irule_at Any (CONJUNCT1 v_rel_do_eq) \\ gvs []
    \\ first_assum (irule_at (Pat ‘v_rel’)) \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ rw [Boolv_def]
    \\ gs [v_rel_def, stamp_rel_cases, SF SFY_ss])
  \\ Cases_on ‘op = Opderef’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = Opassign’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs [v_rel_def]
    \\ rename1 ‘v_rel fr ft fe v w’
    \\ ‘ref_rel (v_rel fr ft fe) (Refv v) (Refv w)’
      by gs [ref_rel_def]
    \\ drule_all state_rel_store_assign \\ rw [OPTREL_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = Opref’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ TRY (rpt (irule_at Any SUBMAP_REFL) \\ gs [] \\ NO_TAC)
    \\ rpt (pairarg_tac \\ gs []) \\ gvs []
    \\ gvs [store_alloc_def, v_rel_def]
    \\ qexists_tac ‘fr |+ (LENGTH s.refs,LENGTH t.refs)’
    \\ irule_at Any SUBMAP_REFL
    \\ irule_at Any SUBMAP_REFL
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, FLOOKUP_UPDATE, count_add1]
    \\ conj_tac
    >- (
      qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
      \\ rw [INJ_DEF, FAPPLY_FUPDATE_THM]
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ conj_tac
    >- (
      qx_gen_tac ‘n1’
      \\ first_x_assum (qspec_then ‘n1’ assume_tac)
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ qx_gen_tac ‘n1’
    \\ first_x_assum (qspec_then ‘n1’ assume_tac)
    \\ rw [] \\ gs [EL_LENGTH_APPEND, ref_rel_def, EL_APPEND_EQN]
    >- (
      irule v_rel_update
      \\ first_assum (irule_at (Pat ‘v_rel’))
      \\ gs [])
    \\ irule ref_rel_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ irule v_rel_update
    \\ first_assum (irule_at (Pat ‘v_rel’))
    \\ gs [])
  \\ Cases_on ‘op’ \\ gs [] *)
QED

Theorem do_app_update = SIMP_RULE (srw_ss()) [LET_THM] do_app_update;

Theorem evaluate_ok_Op:
  op ≠ Opapp ∧ op ≠ Eval ⇒ ^(get_goal "App")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "result", "option"]]
  \\ dxrule_then assume_tac (iffRL EVERY_REVERSE)
  \\ drule_all_then assume_tac do_app_update \\ gs []
  \\ gs [env_ok_def]
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_type_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_next_exn_stamp_mono)
  \\ drule_then assume_tac (CONJUNCT1 evaluate_refs_length_mono)
  \\ drule_then assume_tac do_app_refs_length
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

Theorem v_ok_Boolv[simp]:
  state_ok s ⇒ v_ok s (Boolv b)
Proof
  rw [Boolv_def, state_ok_def, v_ok_thm, stamp_ok_def, stamp_rel_cases,
      FLOOKUP_FUN_FMAP, state_rel_def]
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
 *
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

val _ = export_theory();

