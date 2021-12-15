(*
  Proving that kernel types are abstract.
 *)

open preamble helperLib;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     terminationTheory namespacePropsTheory evaluatePropsTheory
     sptreeTheory;
open permsTheory kernelTheory ast_extrasTheory;
local open ml_progLib in end

val _ = new_theory "abstype";

val _ = set_grammar_ancestry [
  "kernel", "ast_extras", "termination", "namespaceProps", "perms",
  "semanticPrimitivesProps", "misc"];

(* -------------------------------------------------------------------------
 * Expressions are safe if they do not construct anything with a name from the
 * kernel type constructors (i.e. one of TYPE, TERM, THM), and if they do not
 * write to the kernel ffi channel.
 *
 * We can't keep track on whether or not the constructors have been brought
 * into scope (i.e., by 'open Kernel;'), so we just forbid their short names
 * everywhere.
 * ------------------------------------------------------------------------- *)

Definition safe_exp_def:
  safe_exp = every_exp $ λx.
               case x of
                  Con opt xs => ∀id. opt = SOME id ⇒ id_to_n id ∉ kernel_ctors
                | App op xs => op ≠ FFI kernel_ffi
                | _ => T
End

Theorem safe_exp_simps[simp] =
   [“safe_exp (Raise e)”,
    “safe_exp (Handle e pes)”,
    “safe_exp (Lit lit)”,
    “safe_exp (Con opt xs)”,
    “safe_exp (Var n)”,
    “safe_exp (Fun n x)”,
    “safe_exp (App op xs)”,
    “safe_exp (Log lop x y)”,
    “safe_exp (If x y z)”,
    “safe_exp (Mat e pes)”,
    “safe_exp (Let opt x y)”,
    “safe_exp (Letrec f x)”,
    “safe_exp (Tannot e t)”,
    “safe_exp (Lannot e l)”]
  |> map (SIMP_CONV (srw_ss()) [safe_exp_def])
  |> map (SIMP_RULE (srw_ss()) [GSYM safe_exp_def, SF ETA_ss])
  |> LIST_CONJ;

Definition safe_dec_def:
  safe_dec = every_dec $ λd.
               case d of
                 Dlet locs pat x => safe_exp x
               | Dletrec locs funs => EVERY safe_exp (MAP (SND o SND) funs)
               | _ => T
End

Theorem safe_dec_simps[simp] =
  [“safe_dec (Dlet l p x)”,
   “safe_dec (Dletrec l f)”,
   “safe_dec (Dtype l tds)”,
   “safe_dec (Dtabbrev l ns n t)”,
   “safe_dec (Dexn l n ts)”,
   “safe_dec (Dmod mn ds)”,
   “safe_dec (Dlocal ds1 ds2)”,
   “safe_dec (Denv n)”]
  |> map (SIMP_CONV (srw_ss()) [safe_dec_def])
  |> map (SIMP_RULE (srw_ss()) [GSYM safe_dec_def, SF ETA_ss])
  |> LIST_CONJ;

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

Theorem v_ok_def =
  [“v_ok ctxt (Conv opt vs)”,
   “v_ok ctxt (Closure env n x)”,
   “v_ok ctxt (Recclosure env f n)”,
   “v_ok ctxt (Vectorv vs)”,
   “v_ok ctxt (Litv lit)”,
   “v_ok ctxt (Loc loc)”,
   “v_ok ctxt (Env env ns)”]
  |> map (SIMP_CONV (srw_ss()) [Once v_ok_cases])
  |> LIST_CONJ;

Theorem env_ok_def = SIMP_CONV (srw_ss()) [Once v_ok_cases] “env_ok ctxt env”;

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

Theorem state_ok_dec_clock:
  state_ok ctxt (dec_clock s) = state_ok ctxt s
Proof
  rw [state_ok_def, evaluateTheory.dec_clock_def]
QED

Theorem state_ok_with_eval_state[simp]:
  state_ok ctxt (s with eval_state := es) = state_ok ctxt s
Proof
  rw [state_ok_def]
QED

(* -------------------------------------------------------------------------
 * Proving env_ok/v_ok/ref_ok/state_ok for things
 * ------------------------------------------------------------------------- *)

Theorem env_ok_write_cons:
  t ∉ kernel_types ∧
  env_ok ctxt env ⇒
    env_ok ctxt (write_cons nm (n, TypeStamp s t) env)
Proof
  simp [env_ok_def]
  \\ strip_tac
  \\ simp [ml_progTheory.nsLookup_write_cons, SF SFY_ss]
  \\ Cases \\ simp [ml_progTheory.nsLookup_write_cons]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem env_ok_write:
  env_ok ctxt env ∧
  v_ok ctxt v ⇒
    env_ok ctxt (write nm v env)
Proof
  simp [env_ok_def]
  \\ strip_tac
  \\ simp [ml_progTheory.nsLookup_write, SF SFY_ss]
  \\ Cases \\ simp [ml_progTheory.nsLookup_write]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem env_ok_merge_env:
  env_ok ctxt env1 ∧
  env_ok ctxt env2 ⇒
    env_ok ctxt (merge_env env1 env2)
Proof
  simp [env_ok_def]
  \\ strip_tac
  \\ simp [ml_progTheory.merge_env_def]
  \\ conj_tac
  \\ Cases \\ gs [nsLookup_nsAppend_some, SF SFY_ss]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem env_ok_with:
  env_ok ctxt (env1 with c := env.c) ⇒
    env_ok ctxt (env with v := env1.v)
Proof
  rw [env_ok_def]
QED

Theorem env_ok_with_nsBind:
  v_ok ctxt v ∧
  env_ok ctxt (env2 with c := env.c) ⇒
    env_ok ctxt (env with v := nsBind n v env2.v )
Proof
  simp [env_ok_def]
  \\ strip_tac
  \\ conj_tac
  \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem env_ok_empty_env:
  env_ok ctxt empty_env
Proof
  rw [env_ok_def, ml_progTheory.empty_env_def]
QED

(*
 * env_ok holds for the prim environment.
 *)

Theorem env_ok_init_env:
  env_ok ctxt init_env
Proof
  rw [env_ok_def, ml_progTheory.init_env_def]
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
  W8Alloc ∉ ps ∧
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
        \\ drule_at_then (Pat ‘evaluate’)
                         (qspec_then ‘ps’ mp_tac)
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
  \\ Cases_on ‘tm’ \\ gvs [TERM_TYPE_def, v_ok_def, kernel_types_def]
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
  \\ Cases_on ‘th’ \\ gvs [THM_TYPE_def, v_ok_def, kernel_types_def]
  \\ gvs [Once v_ok_cases, do_partial_app_def, CaseEqs ["exp", "v"]]
QED

Theorem v_ok_bind_exn_v[simp]:
  v_ok ctxt bind_exn_v
Proof
  rw [v_ok_def, bind_exn_v_def]
  \\rw [Once v_ok_cases, bind_stamp_def, kernel_types_def]
QED

Theorem v_ok_sub_exn_v[simp]:
  v_ok ctxt sub_exn_v
Proof
  rw [v_ok_def, sub_exn_v_def]
  \\ rw [Once v_ok_cases, subscript_stamp_def, kernel_types_def]
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
               W8Alloc ∉ ps ∧
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
               W8Alloc ∉ ps ∧
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

(* TODO Why is everything named compile_xxx? *)

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
            | _ => EVERY (ok_event ctxt') s'.ffi.io_events’,
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
    by gs [env_ok_def, SF SFY_ss]
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
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
QED

Theorem compile_Handle:
  ^(get_goal "Handle e")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["result", "prod", "error_result", "bool"], EVERY_MAP]
  \\ first_x_assum (drule_all_then (qx_choose_then ‘ctxt1’ assume_tac)) \\ gs []
  >~ [‘¬can_pmatch_all _ _ _ _’] >- (
    gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ ‘env_ok ctxt1 env’
    by gs [env_ok_def, SF SFY_ss]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem compile_Con:
  ^(get_goal "Con cn es")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["result", "prod", "error_result", "option"], EVERY_MAP]
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
  \\ irule v_ok_Conv \\ gs [] \\ rw []
  \\ gs [env_ok_def, SF SFY_ss]
QED

Theorem compile_Var:
  ^(get_goal "Var n")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option"]]
  >- (
    gs [state_ok_def]
    \\ metis_tac [])
  \\ first_assum (irule_at Any)
  \\ gs [env_ok_def, SF SFY_ss]
QED

Theorem compile_Fun:
  ^(get_goal "Fun n e")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option"]]
  \\ first_assum (irule_at Any) \\ gs []
  \\ irule v_ok_Closure \\ gs []
QED

Theorem compile_Eval:
  op = Eval ⇒ ^(get_goal "App")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "result", "option", "error_result", "bool"],
          evaluateTheory.do_eval_res_def]
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ TRY (
    gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs []
    \\ NO_TAC)
  \\ cheat
QED

(* TODO move *)
Theorem list_notin_kernel_funs[simp]:
  Conv (SOME (TypeStamp nm list_type_num)) vs ∉ kernel_funs
Proof
  rw [Once v_ok_cases, Once inferred_cases, kernel_funs_def,
      conj_v_def, disj1_v_def, imp_v_def, not_not_v_def]
QED

(* TODO move *)
Theorem list_not_TERM_TYPE[simp]:
  ¬TERM_TYPE tm (Conv (SOME (TypeStamp nm list_type_num)) vs)
Proof
  Cases_on ‘tm’ \\ rw [TERM_TYPE_def] \\ gs [list_type_num_def]
QED

(* TODO move *)
Theorem list_not_THM_TYPE[simp]:
  ¬THM_TYPE th (Conv (SOME (TypeStamp nm list_type_num)) vs)
Proof
  Cases_on ‘th’ \\ rw [THM_TYPE_def] \\ gs [list_type_num_def]
QED

(* TODO move *)
Theorem list_type_NOTIN_kernel_types[simp]:
  list_type_num ∉ kernel_types
Proof
  rw [list_type_num_def, kernel_types_def]
QED

Theorem v_ok_v_to_list:
  ∀v vs.
    v_to_list v = SOME vs ∧
    v_ok ctxt v ⇒
      EVERY (v_ok ctxt) vs
Proof
  ho_match_mp_tac v_to_list_ind
  \\ rw [v_to_list_def]
  \\ gvs [CaseEqs ["option", "list"], v_ok_def]
  \\ gs [Once v_ok_cases, Once inferred_cases, do_partial_app_def,
         CaseEqs ["v", "exp"]]
QED

Theorem do_app_ok:
  do_app (refs,ffi) op vs = SOME ((refs1,ffi1),res) ∧
  op ≠ Opapp ∧
  op ≠ Eval ∧
  EVERY (v_ok ctxt) vs ∧
  EVERY (ref_ok ctxt) refs ∧
  EVERY (ok_event ctxt) ffi.io_events ∧
  op ≠ FFI kernel_ffi ∧
  (∀loc. loc ∈ kernel_locs ⇒ loc < LENGTH refs) ⇒
    (∀loc. loc ∈ kernel_locs ⇒ loc < LENGTH refs1) ∧
    EVERY (ref_ok ctxt) refs1 ∧
    EVERY (ok_event ctxt) ffi1.io_events ∧
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
    \\ simp [v_ok_def, nat_to_v_def])
  \\ Cases_on ‘∃chn. op = FFI chn’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ gvs [ffiTheory.call_FFI_def, store_lookup_def, store_assign_def,
            CaseEqs ["bool", "list", "option", "oracle_result",
                     "ffi$ffi_result"], EVERY_EL, EL_LUPDATE]
    \\ rw [ref_ok_def, v_ok_def, EL_APPEND_EQN]
    \\ gs [NOT_LESS, LESS_OR_EQ, ok_event_def])
  \\ Cases_on ‘op = ConfigGC’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
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
    \\ Induct \\ simp [list_to_v_def, v_ok_def])
  \\ Cases_on ‘op = Aw8sub_unsafe’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Aw8update_unsafe’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def]
    \\ gvs [store_lookup_def, store_assign_def, EVERY_EL, EL_LUPDATE]
    \\ rw [] \\ gs [ref_ok_def])
  \\ Cases_on ‘op = Aupdate_unsafe’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def]
    \\ gvs [store_lookup_def, store_assign_def, EVERY_EL, EL_LUPDATE]
    \\ rw [] \\ gs [EVERY_EL, EL_LUPDATE, ref_ok_def]
    \\ rw [] \\ gs []
    \\ first_x_assum drule_all
    \\ gs [ref_ok_def, EVERY_EL])
  \\ Cases_on ‘op = Asub_unsafe’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ gvs [store_lookup_def, v_ok_def, EVERY_EL]
    \\ first_x_assum drule_all
    \\ gs [ref_ok_def, EVERY_EL])
  \\ Cases_on ‘op = Aupdate’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def]
    \\ gvs [store_lookup_def, store_assign_def, EVERY_EL, EL_LUPDATE]
    \\ rw [ref_ok_def, EVERY_EL, EL_LUPDATE] \\ rw []
    \\ first_x_assum drule_all
    \\ gs [ref_ok_def, EVERY_EL])
  \\ Cases_on ‘op = Alength’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Asub’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ gvs [store_lookup_def, v_ok_def, EVERY_EL]
    \\ first_x_assum drule_all
    \\ gs [ref_ok_def, EVERY_EL])
  \\ cheat (*
  \\ Cases_on ‘op = AallocEmpty’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ gvs [v_ok_def, store_alloc_def, EVERY_EL]
    \\ rw [EL_APPEND_EQN]
    \\ gs [NOT_LESS, LESS_OR_EQ, ref_ok_def])
  \\ Cases_on ‘op = Aalloc’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ gvs [v_ok_def, store_alloc_def, SUBSET_DEF, PULL_EXISTS]
    \\ rw [EL_APPEND_EQN]
    \\ gs [NOT_LESS, LESS_OR_EQ, ref_ok_def])
  \\ Cases_on ‘op = Vlength’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Vsub’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def, EVERY_EL])
  \\ Cases_on ‘op = VfromList’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ drule_all v_ok_v_to_list
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Strcat’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Strlen’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Strsub’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Explode’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ rename1 ‘MAP _ xs’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ simp [list_to_v_def, v_ok_def])
  \\ Cases_on ‘op = Implode’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘∃opb. op = Chopb opb’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [Boolv_def]
    \\ rw [v_ok_def])
  \\ Cases_on ‘op = Chr’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Ord’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = CopyAw8Aw8’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def]
    \\ gvs [store_assign_def, EL_LUPDATE]
    \\ rw [ref_ok_def])
  \\ Cases_on ‘op = CopyAw8Str’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def]
    \\ gvs [store_assign_def, EL_LUPDATE]
    \\ rw [ref_ok_def])
  \\ Cases_on ‘op = CopyStrAw8’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def]
    \\ gvs [store_assign_def, EL_LUPDATE]
    \\ rw [ref_ok_def])
  \\ Cases_on ‘op = CopyStrStr’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘∃n. op = WordToInt n’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘∃n. op = WordFromInt n’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Aw8update’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SUBSET_DEF, PULL_EXISTS, v_ok_def]
    \\ gvs [store_assign_def, EL_LUPDATE]
    \\ rw [ref_ok_def])
  \\ Cases_on ‘op = Aw8sub’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Aw8length’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Aw8alloc’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ gvs [store_alloc_def, v_ok_def, SUBSET_DEF, PULL_EXISTS]
    \\ rw [EL_APPEND_EQN]
    \\ gs [NOT_LESS, LESS_OR_EQ, ref_ok_def])
  \\ Cases_on ‘∃top. op = FP_top top’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘∃bop. op = FP_bop bop’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘∃uop. op = FP_uop uop’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ rw [v_ok_def])
  \\ Cases_on ‘∃cmp. op = FP_cmp cmp’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [Boolv_def]
    \\ rw [v_ok_def])
  \\ Cases_on ‘∃opn. op = Opn opn’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [div_exn_v_def, v_ok_def])
  \\ Cases_on ‘∃opb. op = Opb opb’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [Boolv_def]
    \\ rw [v_ok_def])
  \\ Cases_on ‘∃sz opw. op = Opw sz opw’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘∃sz sh n. op = Shift sz sh n’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Equality’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [Boolv_def]
    \\ rw [v_ok_def])
  \\ Cases_on ‘op = Opderef’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ gs [v_ok_def, store_lookup_def, EVERY_EL]
    \\ first_x_assum drule \\ gs [ref_ok_def])
  \\ Cases_on ‘op = Opassign’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ gvs [v_ok_def, store_assign_def]
    \\ rw [EL_LUPDATE, ref_ok_def])
  \\ Cases_on ‘op = Opref’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ gvs [v_ok_def, store_alloc_def, ref_ok_def, SUBSET_DEF]
    \\ simp [EL_APPEND_EQN]
    \\ rw [] \\ gs []
    \\ gvs [NOT_LESS, LESS_OR_EQ, ref_ok_def])
  \\ Cases_on ‘op’ \\ gs []
  *)
QED

Theorem compile_Op:
  op ≠ Opapp ∧ op ≠ Eval ⇒ ^(get_goal "App")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "result", "option"]]
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs [state_ok_def]
  >~ [‘do_app _ _ _ = NONE’] >- (
    first_assum (irule_at Any)
    \\ gs [])
  \\ rename1 ‘EVERY (v_ok ctxt1)’
  \\ qexists_tac ‘ctxt1’ \\ gs []
  \\ drule do_app_ok \\ gs []
  \\ disch_then drule \\ simp []
QED

Theorem compile_Opapp:
  op = Opapp ⇒ ^(get_goal "App")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "result", "option", "error_result", "bool"]]
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

Theorem compile_App:
  ^(get_goal "App")
Proof
  Cases_on ‘op = Opapp’ >- (match_mp_tac compile_Opapp \\ gs [])
  \\ Cases_on ‘op = Eval’ >- (match_mp_tac compile_Eval \\ gs [])
  \\ match_mp_tac compile_Op \\ gs []
QED

Theorem compile_Log:
  ^(get_goal "Log")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "result", "option", "error_result", "exp_or_val",
                   "bool"], do_log_def]
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

Theorem compile_If:
  ^(get_goal "If")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "result", "option", "error_result", "exp_or_val",
                   "bool"], do_if_def]
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

Theorem compile_Mat:
  ^(get_goal "Mat")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "result", "option", "error_result", "bool"]]
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

Theorem compile_Let:
  ^(get_goal "Let")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "result", "option", "error_result"]]
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

Theorem compile_Letrec:
  ^(get_goal "Letrec")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "result", "option", "error_result"]]
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

Theorem compile_Tannot:
  ^(get_goal "Tannot")
Proof
  rw [evaluate_def]
QED

Theorem compile_Lannot:
  ^(get_goal "Lannot")
Proof
  rw [evaluate_def]
QED

Theorem compile_pmatch_Nil:
  ^(get_goal "[]:(pat # exp) list")
Proof
  rw [evaluate_def] \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem compile_pmatch_Cons:
  ^(get_goal "_::_:(pat # exp) list")
Proof
  rw [evaluate_def] \\ gs []
  \\ gvs [CaseEqs ["bool", "match_result"]]
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
    \\ cheat (* pmatch theorem *))
  \\ gs [state_ok_def]
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem compile_decs_Nil:
  ^(get_goal "[]:dec list")
Proof
  rw [evaluate_decs_def, extend_dec_env_def]
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem compile_decs_Cons:
  ^(get_goal "_::_::_:dec list")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["prod", "result"]]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ rename1 ‘state_ok ctxt1 st1’
  \\ ‘env_ok ctxt1 (extend_dec_env env1 env)’
    by gs [extend_dec_env_def, env_ok_def, SF SFY_ss]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ gs [state_ok_def, combine_dec_result_def]
  \\ CASE_TAC \\ gs [AC CONJ_COMM CONJ_ASSOC]
  >~ [‘Rerr err’] >- (
    CASE_TAC \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  \\ first_x_assum (irule_at Any) \\ gs []
  \\ gs [env_ok_def, extend_dec_env_def, nsLookup_nsAppend_some]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem compile_decs_Dlet:
  ^(get_goal "Dlet")
Proof
  rw [evaluate_decs_def]
  >~ [‘¬ALL_DISTINCT _’] >- (
    gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ gvs [CaseEqs ["prod", "result"]]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ CASE_TAC \\ gs [state_ok_def]
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [extend_dec_env_def, env_ok_def, nsLookup_nsAppend_some,
         nsLookup_alist_to_ns_some, SF SFY_ss]
  \\ rw [] \\ gs [SF SFY_ss]
  \\ drule_then assume_tac ALOOKUP_MEM
  \\ cheat (* pmatch theorem *)
QED

Theorem compile_decs_Dletrec:
  ^(get_goal "Dletrec")
Proof
  rw [evaluate_decs_def]
  >~ [‘¬ALL_DISTINCT _’] >- (
    gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ gvs [CaseEqs ["prod", "result"]]
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [extend_dec_env_def, build_rec_env_merge, env_ok_def,
         nsLookup_nsAppend_some, nsLookup_alist_to_ns_some, SF SFY_ss]
  \\ rw [] \\ gs [SF SFY_ss]
  \\ drule_then assume_tac ALOOKUP_MEM
  \\ gvs [MEM_MAP, EXISTS_PROD]
  \\ simp [v_ok_def, DISJ_EQ_IMP]
  \\ rw [] \\ gs [env_ok_def, SF SFY_ss]
QED

Theorem compile_decs_Dtype:
  ^(get_goal "Dtype")
Proof
  rw [evaluate_decs_def]
  >~ [‘¬EVERY check_dup_ctors _’] >- (
    gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ gvs [CaseEqs ["prod", "result"], state_ok_def]
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
  \\ strip_tac
  \\ first_x_assum drule_all \\ gs []
QED

Theorem compile_decs_Dtabbrev:
  ^(get_goal "Dtabbrev")
Proof
  rw [evaluate_decs_def]
  \\ first_assum (irule_at Any)
  \\ gs [env_ok_def, extend_dec_env_def, SF SFY_ss]
QED

Theorem compile_decs_Denv:
  ^(get_goal "Denv")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod"]]
  \\ gs [state_ok_def]
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [env_ok_def, extend_dec_env_def, SF SFY_ss]
  \\ gvs [declare_env_def, CaseEqs ["option", "eval_state", "prod"]]
  \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
  \\ rw [] \\ gs [v_ok_def, env_ok_def, nat_to_v_def, SF SFY_ss]
QED

Theorem compile_decs_Dexn:
  ^(get_goal "Dexn")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod"], state_ok_def]
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [env_ok_def, extend_dec_env_def, SF SFY_ss]
  \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem compile_decs_Dmod:
  ^(get_goal "Dmod")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod", "result"]]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [env_ok_def, extend_dec_env_def, SF SFY_ss]
  \\ conj_tac
  \\ Cases \\ gs [ml_progTheory.nsLookup_nsBind_compute,
                  nsLookup_nsAppend_some,
                  nsLookup_nsLift]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem compile_decs_Dlocal:
  ^(get_goal "Dlocal")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod", "result"]]
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
  ^(compile_correct_tm ())
Proof
  match_mp_tac (the_ind_thm ())
  \\ rpt conj_tac \\ rpt gen_tac
  \\ rewrite_tac [compile_Nil, compile_Cons, compile_Lit, compile_Raise,
                  compile_Handle, compile_Con, compile_Var, compile_Fun,
                  compile_App, compile_Log, compile_If, compile_Mat,
                  compile_Let, compile_Letrec, compile_Tannot, compile_Lannot,
                  compile_pmatch_Nil, compile_pmatch_Cons, compile_decs_Nil,
                  compile_decs_Cons, compile_decs_Dlet, compile_decs_Dletrec,
                  compile_decs_Dtype, compile_decs_Dtabbrev, compile_decs_Denv,
                  compile_decs_Dexn, compile_decs_Dmod, compile_decs_Dlocal]
QED

val _ = export_theory ();

