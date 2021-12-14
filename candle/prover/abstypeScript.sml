(*
  Proving that kernel types are abstract.
 *)

open preamble helperLib;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     terminationTheory namespacePropsTheory evaluatePropsTheory
     sptreeTheory;
open permsTheory kernelTheory ast_extrasTheory;

val _ = new_theory "abstype";

val _ = set_grammar_ancestry [
  "kernel", "ast_extras", "termination", "namespaceProps", "perms",
  "semanticPrimitivesProps", "misc"];

(* -------------------------------------------------------------------------
 *
 * ------------------------------------------------------------------------- *)

Definition safe_exp_def:
  safe_exp (x: exp) = T
End

Inductive v_ok:
[~Inferred:]
  (∀ctxt v.
     inferred ctxt v ⇒
       kernel_vals ctxt v) ∧
[~PartialApp:]
  (∀ctxt f v g.
     kernel_vals ctxt f ∧
     v_ok ctxt v ∧
     do_partial_app f v = SOME g ⇒
       kernel_vals ctxt g) ∧
[~KernelVals:]
  (∀ctxt v.
     kernel_vals ctxt v ⇒
       v_ok ctxt v) ∧
[~Conv:]
  (∀ctxt opt vs.
     EVERY (v_ok ctxt) vs ∧
     (∀tag x. opt = SOME (TypeStamp tag x) ⇒ x ∉ kernel_types) ⇒
       v_ok ctxt (Conv opt vs)) ∧
[~Closure:]
  (∀ctxt env n x.
     env_ok ctxt env ∧
     safe_exp x ⇒
       v_ok ctxt (Closure env n x)) ∧
[~Recclosure:]
  (∀ctxt env f n.
     env_ok ctxt env ∧
     EVERY safe_exp (MAP (SND o SND) f) ⇒
       v_ok ctxt (Recclosure env f n)) ∧
[~Vectorv:]
  (∀ctxt vs.
     EVERY (v_ok ctxt) vs ⇒
       v_ok ctxt (Vectorv vs)) ∧
[~Lit:]
  (∀ctxt lit.
     v_ok ctxt (Litv lit)) ∧
[~Loc:]
  (∀ctxt loc.
     loc ∉ kernel_locs ⇒
       v_ok ctxt (Loc loc)) ∧
[~Env:]
  (∀ctxt env ns.
     env_ok ctxt env ⇒
       v_ok ctxt (Env env ns)) ∧
[env_ok:]
  (∀ctxt env.
     (∀n len tag m. nsLookup env.c n = SOME (len, TypeStamp tag m) ⇒
                  m ∉ kernel_types) ∧
     (∀n v. nsLookup env.v n = SOME v ⇒ v_ok ctxt v) ⇒
       env_ok ctxt env)
End

Definition ref_ok_def:
  ref_ok ctxt (Varray vs) = EVERY (v_ok ctxt) vs ∧
  ref_ok ctxt (Refv v) = v_ok ctxt v ∧
  ref_ok ctxt (W8array vs) = T
End

Definition state_ok_def:
  state_ok ctxt s ⇔
    (∀loc. loc ∈ kernel_locs ⇒ loc < LENGTH s.refs) ∧
    (∀n. n ∈ kernel_types ⇒ n < s.next_type_stamp) ∧
    EVERY (ref_ok ctxt) s.refs ∧
    EVERY (ok_event ctxt) s.ffi.io_events
End

(* -------------------------------------------------------------------------
 * Proving env_ok/v_ok/ref_ok/state_ok for things
 * ------------------------------------------------------------------------- *)

Theorem env_ok_write_cons:
  t ∉ kernel_types ∧
  env_ok ctxt env ⇒
    env_ok ctxt (write_cons nm (n, TypeStamp s t) env)
Proof
  rw [Once v_ok_cases]
  \\ simp [Once v_ok_cases, ml_progTheory.nsLookup_write_cons, SF SFY_ss]
  \\ Cases \\ simp [ml_progTheory.nsLookup_write_cons]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem env_ok_write:
  env_ok ctxt env ∧
  v_ok ctxt v ⇒
    env_ok ctxt (write nm v env)
Proof
  rw [Once v_ok_cases]
  \\ simp [Once v_ok_cases, ml_progTheory.nsLookup_write, SF SFY_ss]
  \\ Cases \\ simp [ml_progTheory.nsLookup_write]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem env_ok_merge_env:
  env_ok ctxt env1 ∧
  env_ok ctxt env2 ⇒
    env_ok ctxt (merge_env env1 env2)
Proof
  simp [GSYM AND_IMP_INTRO]
  \\ simp [Once v_ok_cases] \\ strip_tac
  \\ simp [Once v_ok_cases] \\ strip_tac
  \\ simp [Once v_ok_cases, ml_progTheory.merge_env_def]
  \\ conj_tac
  \\ Cases \\ gs [nsLookup_nsAppend_some, SF SFY_ss]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem env_ok_with:
  env_ok ctxt (env1 with c := env.c) ⇒
    env_ok ctxt (env with v := env1.v)
Proof
  rw [Once v_ok_cases]
  \\ simp [Once v_ok_cases, SF SFY_ss]
QED

Theorem env_ok_with_nsBind:
  v_ok ctxt v ∧
  env_ok ctxt (env2 with c := env.c) ⇒
    env_ok ctxt (env with v := nsBind n v env2.v )
Proof
  simp [GSYM AND_IMP_INTRO]
  \\ strip_tac
  \\ rw [Once v_ok_cases]
  \\ simp [Once v_ok_cases]
  \\ conj_tac
  \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem env_ok_empty_env:
  env_ok ctxt empty_env
Proof
  rw [Once v_ok_cases, ml_progTheory.empty_env_def]
QED

(*
 * env_ok holds for the prim environment.
 *)

Theorem env_ok_init_env:
  env_ok ctxt init_env
Proof
  rw [Once v_ok_cases, ml_progTheory.init_env_def]
  \\ gvs [nsLookup_Bind_v_some, CaseEqs ["bool", "option"], kernel_types_def]
QED

(*
 * env_ok holds for the kernel_env
 *)

Theorem env_ok_kernel_env:
  env_ok ctxt kernel_env
Proof
  rw [kernel_env_def, env_ok_write_cons, kernel_types_def, env_ok_empty_env]
QED

Theorem v_ok_member_v:
  v_ok ctxt member_v
Proof
  rw [member_v_def]
  \\ irule v_ok_Recclosure
  \\ simp [env_ok_merge_env, env_ok_kernel_env, perms_ok_exp_def,
           env_ok_init_env]
  \\ cheat (* FIXME: Define safe_exp *)
QED

(* TODO: Use v_thms *)

Theorem inferred_ok:
  inferred ctxt f ∧
  state_ok ctxt s ∧
  v_ok ctxt v ∧
  do_opapp [f; v] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    ∃ctxt'.
      state_ok ctxt' s' ∧
      (∀v. v_ok ctxt v ⇒ v_ok ctxt' v) ∧
      (∀v. kernel_vals ctxt v ⇒ kernel_vals ctxt' v) ∧
      (∀vs. res = Rval vs ⇒ EVERY (v_ok ctxt') vs) ∧
      (∀v. res = Rerr (Rraise v) ⇒ v_ok ctxt' v)
Proof
  rw [Once inferred_cases]
  >~ [‘f ∈ kernel_funs’] >- (
    gs [kernel_funs_def]
    >~ [‘conj_v’] >- (
      gvs [conj_v_def, do_opapp_def, evaluate_def]
      \\ first_assum (irule_at Any) \\ simp []
      \\ irule v_ok_KernelVals
      \\ irule v_ok_PartialApp
      \\ Q.LIST_EXISTS_TAC [‘conj_v’, ‘v’]
      \\ irule_at Any v_ok_Inferred
      \\ irule_at Any inferred_KernelFuns
      \\ simp [kernel_funs_def]
      \\ simp [Once do_partial_app_def, conj_v_def])
    >~ [‘imp_v’] >- (
      gvs [imp_v_def, do_opapp_def, evaluate_def]
      \\ first_assum (irule_at Any) \\ simp []
      \\ irule v_ok_KernelVals
      \\ irule v_ok_PartialApp
      \\ Q.LIST_EXISTS_TAC [‘imp_v’, ‘v’]
      \\ irule_at Any v_ok_Inferred
      \\ irule_at Any inferred_KernelFuns
      \\ simp [kernel_funs_def]
      \\ simp [Once do_partial_app_def, imp_v_def])
    >~ [‘disj1_v’] >- (
      gvs [disj1_v_def, do_opapp_def, evaluate_def]
      \\ first_assum (irule_at Any) \\ simp []
      \\ irule v_ok_KernelVals
      \\ irule v_ok_PartialApp
      \\ Q.LIST_EXISTS_TAC [‘disj1_v’, ‘v’]
      \\ irule_at Any v_ok_Inferred
      \\ irule_at Any inferred_KernelFuns
      \\ simp [kernel_funs_def]
      \\ simp [Once do_partial_app_def, disj1_v_def])
    >~ [‘not_not_v’] >- (
      cheat))
  >~ [‘TERM ctxt tm’] >- (
    Cases_on ‘tm’ \\ gs [TERM_TYPE_def, do_opapp_cases])
  >~ [‘THM ctxt th’] >- (
    Cases_on ‘th’ \\ gs [THM_TYPE_def, do_opapp_cases])
QED

Theorem v_ok_THM_TYPE_HEAD:
  v_ok ctxt v ∧
  THM_TYPE_HEAD v ⇒
    ∃th. THM_TYPE th v
Proof
  rw [Once v_ok_cases, kernel_types_def, THM_TYPE_HEAD_def]
  \\ gs [Once v_ok_cases, do_partial_app_def, AllCaseEqs ()]
  \\ gs [Once inferred_cases, kernel_funs_def, conj_v_def, disj1_v_def,
         imp_v_def, not_not_v_def, SF SFY_ss]
  \\ Cases_on ‘tm’ \\ gs [TERM_TYPE_def]
QED

Theorem v_ok_TERM_TYPE_HEAD:
  v_ok ctxt v ∧
  TERM_TYPE_HEAD v ⇒
    ∃tm. TERM_TYPE tm v
Proof
  rw [Once v_ok_cases, kernel_types_def, TERM_TYPE_HEAD_def]
  \\ gs [Once v_ok_cases, do_partial_app_def, AllCaseEqs ()]
  \\ gs [Once inferred_cases, kernel_funs_def, conj_v_def, disj1_v_def,
         imp_v_def, not_not_v_def, SF SFY_ss]
  \\ Cases_on ‘th’ \\ gs [THM_TYPE_def]
QED

(*
 * TODO Move elsewhere
 *)

Theorem Arrow2:
  (A --> B --> C) f fv ∧
  do_partial_app fv av = SOME gv ∧
  do_opapp [gv; bv] = SOME (env, exp) ∧
  evaluate (s:'ffi semanticPrimitives$state) env [exp] = (s', res) ∧
  A a av ∧ B b bv ∧
  DoEval ∉ ps ∧
  RefAlloc ∉ ps ∧
  (∀n. RefMention n ∉ ps) ∧
  perms_ok ps av ∧
  perms_ok ps bv ∧
  perms_ok ps fv ⇒
    s.ffi = s'.ffi ∧
    ((res = Rerr (Rabort Rtimeout_error)) ∨
     (res = Rerr (Rabort Rtype_error)) ∨
     s.refs = s'.refs ∧
     s.next_type_stamp = s'.next_type_stamp ∧
     ∃rv. res = Rval [rv] ∧
          C (f a b) rv)
Proof
  strip_tac
  \\ ‘LENGTH s'.refs = LENGTH s.refs’
    by (gvs [do_partial_app_def, CaseEqs ["v", "exp"], do_opapp_cases,
             perms_ok_def]
        \\ drule_at_then (Pos (el 5)) (qspec_then ‘ps’ mp_tac)
                         evaluate_perms_ok_exp
        \\ impl_tac \\ simp []
        \\ gs [perms_ok_state_def, perms_ok_env_def]
        \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
        \\ rw [] \\ gs []
        \\ first_x_assum irule
        \\ first_assum (irule_at (Pos last)) \\ gs [])
  \\ qabbrev_tac ‘env' = write "a" av (write "b" bv (write "f" fv ARB))’
  \\ ‘Eval env' (Var (Short "a")) (A a)’
    by simp [Abbr ‘env'’, ml_translatorTheory.Eval_Var_SIMP]
  \\ ‘Eval env' (Var (Short "b")) (B b)’
    by simp [Abbr ‘env'’, ml_translatorTheory.Eval_Var_SIMP]
  \\ ‘Eval env' (Var (Short "f")) ((A --> B --> C) f)’
    by simp [Abbr ‘env'’, ml_translatorTheory.Eval_Var_SIMP]
  \\ qpat_x_assum ‘(_ --> _) _ _’ kall_tac
  \\ qpat_x_assum ‘A _ _’ kall_tac
  \\ qpat_x_assum ‘B _ _’ kall_tac
  \\ dxrule_all ml_translatorTheory.Eval_Arrow \\ strip_tac
  \\ dxrule_all ml_translatorTheory.Eval_Arrow
  \\ simp [ml_translatorTheory.Eval_def]
  \\ disch_then (qspec_then ‘s.refs’ strip_assume_tac)
  \\ dxrule ml_translatorTheory.evaluate_empty_state_IMP
  \\ simp [ml_progTheory.eval_rel_def, evaluate_def, Abbr ‘env'’,
           ml_progTheory.nsLookup_write]
  \\ qpat_x_assum ‘do_partial_app _ _ = _’ mp_tac
  \\ simp [do_partial_app_def, Once do_opapp_def, AllCaseEqs (), PULL_EXISTS]
  \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘do_opapp _ = SOME (env,exp)’ mp_tac
  \\ simp [do_opapp_cases]
  \\ strip_tac \\ gvs [evaluate_def, do_opapp_cases,
                       evaluateTheory.dec_clock_def]
  \\ dxrule_then (qspec_then ‘s.clock’ mp_tac) evaluate_set_init_clock
  \\ simp [with_same_clock]
  \\ strip_tac \\ gvs []
  \\ mp_tac (CONJUNCT1 is_clock_io_mono_evaluate)
  \\ qmatch_asmsub_abbrev_tac ‘evaluate s env1 [e]’
  \\ disch_then (qspecl_then [`s`,`env1`,`[e]`] mp_tac)
  \\ rw [is_clock_io_mono_def]
  \\ gs [io_events_mono_antisym]
QED

Theorem v_ok_TERM:
  v_ok ctxt v ∧
  TERM_TYPE tm v ⇒
    TERM ctxt tm
Proof
  strip_tac
  \\ Cases_on ‘inferred ctxt v’
  >- (
    irule TERM_from_TERM_TYPE
    \\ gs [SF SFY_ss])
  \\ Cases_on ‘tm’ \\ gvs [TERM_TYPE_def, Once v_ok_cases, kernel_types_def]
  \\ gvs [Once v_ok_cases, do_partial_app_def, CaseEqs ["exp", "v"]]
QED

Theorem v_ok_THM:
  v_ok ctxt v ∧
  THM_TYPE th v ⇒
    THM ctxt th
Proof
  strip_tac
  \\ Cases_on ‘inferred ctxt v’
  >- (
    irule THM_from_THM_TYPE
    \\ gs [SF SFY_ss])
  \\ Cases_on ‘th’ \\ gvs [THM_TYPE_def, Once v_ok_cases, kernel_types_def]
  \\ gvs [Once v_ok_cases, do_partial_app_def, CaseEqs ["exp", "v"]]
QED

Theorem v_ok_bind_exn_v[simp]:
  v_ok ctxt bind_exn_v
Proof
  rw [Once v_ok_cases, bind_exn_v_def]
  \\rw [Once v_ok_cases, bind_stamp_def, kernel_types_def]
QED

Theorem kernel_vals_max_app:
  kernel_vals ctxt f ∧
  do_partial_app f v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ⇒
    f ∈ kernel_funs
Proof
  cheat
QED

Theorem TERM_TYPE_perms_ok:
  ∀tm v. TERM_TYPE tm v ⇒ perms_ok ps v
Proof
  Induct \\ rw [TERM_TYPE_def]
  \\ gs [ml_translatorTheory.NUM_def,
         ml_translatorTheory.INT_def,
         perms_ok_def]
QED

Theorem LIST_TYPE_perms_ok:
  ∀xs xsv.
    (∀x v. A x v ⇒ perms_ok ps v) ∧
    LIST_TYPE A xs xsv ⇒
      perms_ok ps xsv
Proof
  Induct \\ rw []
  \\ gs [ml_translatorTheory.LIST_TYPE_def, perms_ok_def, SF SFY_ss]
QED

Theorem THM_TYPE_perms_ok:
  ∀th v. THM_TYPE th v ⇒ perms_ok ps v
Proof
  Cases \\ rw [THM_TYPE_def]
  \\ gs [perms_ok_def, TERM_TYPE_perms_ok, SF SFY_ss,
         Q.ISPECL [‘(ps:permission set)’, ‘TERM_TYPE’]
                  (GEN_ALL LIST_TYPE_perms_ok)]
QED

Theorem perms_ok_member_v:
  perms_ok ps member_v
Proof
  rw [member_v_def, perms_ok_def, perms_ok_exp_def,
      astTheory.pat_bindings_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = EMPTY’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs [])
  \\ gs [perms_ok_env_def]
QED

Theorem perms_ok_list_union_v:
  perms_ok ps list_union_v
Proof
  rw [list_union_v_def, perms_ok_def, perms_ok_exp_def,
      astTheory.pat_bindings_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = {Short "member"}’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs [])
  \\ gs [perms_ok_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [perms_ok_member_v]
QED

Theorem conj_v_perms_ok:
  perms_ok ps conj_v
Proof
  rw [conj_v_def, perms_ok_def, perms_ok_exp_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = {Short "list_union"}’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs [])
  \\ gs [perms_ok_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [perms_ok_list_union_v]
QED

Theorem disj1_v_perms_ok:
  perms_ok ps disj1_v
Proof
  rw [disj1_v_def, perms_ok_def, perms_ok_exp_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = EMPTY’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs []
        \\ CCONTR_TAC \\ gs [])
  \\ gs [perms_ok_env_def]
QED

Theorem kernel_vals_ok:
  ∀ctxt f.
    kernel_vals ctxt f ⇒
      ∀s v env exp s' res.
        do_opapp [f; v] = SOME (env, exp) ∧
        state_ok ctxt s ∧
        v_ok ctxt v ∧
        evaluate s env [exp] = (s', res) ⇒
          (∃abort. s'.ffi = s.ffi ∧ res = Rerr (Rabort abort)) ∨
          ∃ctxt'.
            state_ok ctxt' s' ∧
            (∀v. v_ok ctxt v ⇒ v_ok ctxt' v) ∧
            (∀v. kernel_vals ctxt v ⇒ kernel_vals ctxt' v) ∧
            (∀vs. res = Rval vs ⇒ EVERY (v_ok ctxt') vs) ∧
            (∀v. res = Rerr (Rraise v) ⇒ v_ok ctxt' v)
Proof
  rw [Once v_ok_cases]
  >~ [‘inferred ctxt f’] >- (
    rw [DISJ_EQ_IMP]
    \\ irule_at Any inferred_ok
    \\ first_assum (irule_at Any)
    \\ first_assum (irule_at Any) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  >~ [‘do_partial_app f v = SOME g’] >- (
    rw [DISJ_EQ_IMP]
    \\ Cases_on ‘f ∈ kernel_funs’ \\ gs [kernel_funs_def]
    >~ [‘conj_v’] >- (
      drule_all_then strip_assume_tac conj_v_alt \\ gvs []
      \\ TRY (first_assum (irule_at Any) \\ gs [] \\ NO_TAC)
      \\ rename1 ‘do_opapp [g; w]’
      \\ ‘∃th1. THM_TYPE th1 v’
        by (irule_at Any v_ok_THM_TYPE_HEAD \\ gs [SF SFY_ss])
      \\ ‘∃th2. THM_TYPE th2 w’
        by (irule_at Any v_ok_THM_TYPE_HEAD \\ gs [SF SFY_ss])
      \\ assume_tac conj_v_thm
      \\ ‘∃ps. DoEval ∉ ps ∧
               RefAlloc ∉ ps ∧
               (∀n. RefMention n ∉ ps) ∧
               perms_ok ps conj_v’
        by (irule_at Any conj_v_perms_ok
            \\ qexists_tac ‘EMPTY’ \\ gs [])
      \\ ‘perms_ok ps v ∧ perms_ok ps w’
        by gs [SF SFY_ss, THM_TYPE_perms_ok]
      \\ drule_all Arrow2
      \\ strip_tac \\ gvs []
      \\ irule_at (Pos last) v_ok_KernelVals
      \\ irule_at Any v_ok_Inferred
      \\ irule_at Any inferred_THM
      \\ first_assum (irule_at (Pos (el 2)))
      \\ irule_at Any conj_thm
      \\ imp_res_tac v_ok_THM
      \\ first_assum (irule_at Any) \\ gs []
      \\ gs [state_ok_def])
    >~ [‘disj1_v’] >- (
      drule_all_then strip_assume_tac disj1_v_alt \\ gvs []
      \\ TRY (first_assum (irule_at Any) \\ gs [] \\ NO_TAC)
      \\ rename1 ‘do_opapp [g; w]’
      \\ ‘∃th. THM_TYPE th v’
        by (irule_at Any v_ok_THM_TYPE_HEAD \\ gs [SF SFY_ss])
      \\ ‘∃tm. TERM_TYPE tm w’
        by (irule_at Any v_ok_TERM_TYPE_HEAD \\ gs [SF SFY_ss])
      \\ assume_tac disj1_v_thm
      \\ ‘∃ps. DoEval ∉ ps ∧
               RefAlloc ∉ ps ∧
               (∀n. RefMention n ∉ ps) ∧
               perms_ok ps disj1_v’
        by (irule_at Any disj1_v_perms_ok
            \\ qexists_tac ‘EMPTY’ \\ gs [])
      \\ ‘perms_ok ps v ∧ perms_ok ps w’
        by gs [SF SFY_ss, THM_TYPE_perms_ok, TERM_TYPE_perms_ok]
      \\ drule_all Arrow2
      \\ strip_tac \\ gvs []
      \\ irule_at (Pos last) v_ok_KernelVals
      \\ irule_at Any v_ok_Inferred
      \\ irule_at Any inferred_THM
      \\ first_assum (irule_at (Pos (el 2)))
      \\ cheat
      (* \\ irule_at Any disj_thm
      \\ imp_res_tac v_ok_THM
      \\ first_assum (irule_at Any) \\ gs []
      \\ gs [state_ok_def] *))
    >~ [‘imp_v’] >- (
      cheat)
    >~ [‘not_not_v’] >- (
      cheat)
    \\ gs [Once v_ok_cases, Once inferred_cases, kernel_funs_def]
    >- (
      Cases_on ‘tm’ \\ gs [TERM_TYPE_def, do_partial_app_def])
    >- (
      Cases_on ‘th’ \\ gs [THM_TYPE_def, do_partial_app_def])
    \\ ‘kernel_vals ctxt f’
      by (irule v_ok_PartialApp
          \\ first_assum (irule_at (Pos hd))
          \\ gs [])
    \\ drule_all kernel_vals_max_app
    \\ rw [kernel_funs_def])
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
            | _ => EVERY (ok_event ctxt') s'.ffi.io_events’,
      ‘λs env v ps errv. ∀res s' ctxt.
        evaluate_match s env v ps errv = (s', res) ∧
        state_ok ctxt s ∧
        env_ok ctxt env ∧
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
            | _ => EVERY (ok_event ctxt') s'.ffi.io_events’,
      ‘λs env ds. ∀res s' ctxt.
        evaluate_decs s env ds = (s', res) ∧
        state_ok ctxt s ∧
        env_ok ctxt env ∧
        EVERY safe_exp (MAP SND ps) ⇒
          ∃ctxt'.
            (∀v. v_ok ctxt v ⇒ v_ok ctxt' v) ∧
            case res of
              Rval env =>
                state_ok ctxt' s'  ∧
                env_ok ctxt env
            | Rerr (Rraise v) =>
                state_ok ctxt' s'  ∧
                v_ok ctxt' v
            | _ => EVERY (ok_event ctxt') s'.ffi.io_events’]
    |> CONV_RULE (DEPTH_CONV BETA_CONV);
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> helperLib.list_dest dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
    |> helperLib.list_dest dest_forall
    |> last
  fun compile_correct_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end

Theorem compile_Nil:
  ^(get_goal "[]")
Proof
  rw [evaluate_def]
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem compile_Cons:
  ^(get_goal "_::_::_")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["result", "prod"]]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ first_x_assum (drule_all_then (qx_choose_then ‘ctxt1’ assume_tac)) \\ gs []
  \\ ‘env_ok ctxt1 env’
    by (qpat_x_assum ‘env_ok _ _’ mp_tac
        \\ rw [Once v_ok_cases]
        \\ rw [Once v_ok_cases]
        \\ gs [SF SFY_ss])
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ rpt CASE_TAC \\ gs []
  \\ gs [state_ok_def]
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem compile_Lit:
  ^(get_goal "Lit l")
Proof
  rw [evaluate_def] \\ gs []
  \\ first_assum (irule_at Any)
  \\ simp [v_ok_Lit]
QED

Theorem compile_Raise:
  ^(get_goal "Raise e")
Proof
  rw [evaluate_def] \\ gs []
  \\ gvs [CaseEqs ["result", "prod"]]
  \\ cheat (* FIXME: Define safe_exp *) (*
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs [] *)
QED

Theorem compile_Handle:
  ^(get_goal "Handle e")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["result", "prod", "error_result", "bool"], EVERY_MAP]
  \\ cheat (* FIXME: Define safe_exp *) (*
  \\ first_x_assum (drule_all_then (qx_choose_then ‘ctxt1’ assume_tac)) \\ gs []
  >~ [‘¬can_pmatch_all _ _ _ _’] >- (
    gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ ‘env_ok ctxt1 env’
    by (qpat_x_assum ‘env_ok _ _’ mp_tac
        \\ rw [Once v_ok_cases]
        \\ rw [Once v_ok_cases]
        \\ gs [SF SFY_ss])
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ first_assum (irule_at Any) \\ gs [] *)
QED

Theorem compile_Con:
  ^(get_goal "Con cn es")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["result", "prod", "error_result", "option"], EVERY_MAP]
  \\ cheat (* FIXME: Define safe_exp *) (*
  >~ [‘¬do_con_check _ _ _’] >- (
    gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  >- (
    first_x_assum (drule_all_then strip_assume_tac)
    \\ gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ first_x_assum (drule_all_then (qx_choose_then ‘ctxt1’ assume_tac)) \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
  \\ gvs [build_conv_def, CaseEqs ["option", "prod"]]
  \\ irule v_ok_Conv \\ gs []
  \\ qpat_x_assum ‘env_ok _ _’ mp_tac
  \\ rw [Once v_ok_cases] \\ gs [SF SFY_ss] *)
QED

Theorem compile_Var:
  ^(get_goal "Var n")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option"]]
  >- (
    gs [state_ok_def]
    \\ metis_tac [])
  \\ first_assum (irule_at Any) \\ gs []
  \\ qpat_x_assum ‘env_ok _ _’ mp_tac
  \\ rw [Once v_ok_cases] \\ gs [SF SFY_ss]
QED

Theorem compile_Fun:
  ^(get_goal "Fun n e")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option"]]
  \\ cheat (* FIXME: Define safe_exp *) (*
  \\ first_assum (irule_at Any) \\ gs []
  \\ irule v_ok_Closure \\ gs []
  \\ first_assum (irule_at Any) *)
QED

Theorem compile_App:
  op = Opapp ⇒ ^(get_goal "App")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "result", "option", "error_result", "bool"]]
  \\ cheat (* FIXME: Define safe_exp *) (*
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
    by (qpat_x_assum ‘env_ok _ _’ mp_tac
        \\ rw [Once v_ok_cases]
        \\ rw [Once v_ok_cases]
        \\ gs [SF SFY_ss])
  \\ rename1 ‘state_ok ctxt1 s’
  \\ ‘state_ok ctxt1 (dec_clock s)’
    by gs [evaluateTheory.dec_clock_def, state_ok_def]
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
  \\ ‘env_ok ctxt1 env1’
    by (gvs [do_opapp_cases]
        >~ [‘Closure env1 n e’] >- (
          irule env_ok_with_nsBind \\ gs []
          \\ ‘env1 with c := env1.c = env1’
            by rw [sem_env_component_equality]
          \\ gs []
          \\ qpat_x_assum ‘v_ok _ (Closure _ _ _)’ mp_tac
          \\ rewrite_tac [Once v_ok_cases] \\ simp []
          \\ rw [] \\ gs [])
        \\ qpat_x_assum ‘v_ok _ (Recclosure _ _ _)’ mp_tac
        \\ rewrite_tac [Once v_ok_cases] \\ simp []
        \\ rw [Once v_ok_cases]
        \\ simp [Once v_ok_cases, SF SFY_ss]
        \\ Cases \\ simp [build_rec_env_merge,
                          ml_progTheory.nsLookup_nsBind_compute]
        \\ rw [] \\ gs []
        \\ gs [nsLookup_nsAppend_some, nsLookup_alist_to_ns_some,
               nsLookup_alist_to_ns_none]
        >~ [‘ALOOKUP _ _ = SOME _’] >- (
          drule_then assume_tac ALOOKUP_MEM
          \\ gvs [MEM_MAP, EXISTS_PROD]
          \\ rewrite_tac [Once v_ok_cases] \\ simp []
          \\ rw [DISJ_EQ_IMP]
          \\ gs [EVERY_MAP, EVERY_MEM, FORALL_PROD, SF SFY_ss]
          \\ simp [Once v_ok_cases, SF SFY_ss]
          \\ first_assum (irule_at Any) \\ gs []
          \\ rw []
          \\ first_x_assum irule
          \\ gs [SF SFY_ss])
        \\ first_x_assum irule
        \\ gs [SF SFY_ss])
  \\ cheat (* there's permissions in v_ok now *) *)
QED

Theorem evaluate_v_ok:
  ^(compile_correct_tm ())
Proof
  match_mp_tac (the_ind_thm ())
  \\ rpt conj_tac
  \\ rewrite_tac [compile_Nil, compile_Cons, compile_Lit, compile_Raise,
                 compile_Handle, compile_Con, compile_Var, compile_Fun,
                 compile_App]
  \\ cheat
QED

val _ = export_theory ();

