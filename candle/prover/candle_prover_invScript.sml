(*
  Definitions of invariants that are to be maintained during
  evaluate of Candle prover
 *)

open preamble helperLib;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     evaluateTheory namespacePropsTheory evaluatePropsTheory
     sptreeTheory candle_kernelProgTheory ml_hol_kernel_funsProgTheory;
open permsTheory candle_kernel_valsTheory ast_extrasTheory;
local open ml_progLib in end

val _ = new_theory "candle_prover_inv";

val _ = set_grammar_ancestry [
  "candle_kernel_vals", "ast_extras", "evaluate", "namespaceProps", "perms",
  "holKernelProof", "semanticPrimitivesProps", "misc"];

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
[~FP_WordTree:]
  (∀ ctxt fp.
     v_ok ctxt (FP_WordTree fp)) ∧
[~FP_BoolTree:]
  (∀ ctxt fp.
     v_ok ctxt (FP_BoolTree fp)) ∧
[~Real:]
  (∀ ctxt r.
     v_ok ctxt (Real r)) ∧
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
     (∀id len tag tn.
        nsLookup env.c id = SOME (len, TypeStamp tag tn) ∧
        tn ∈ kernel_types ⇒
          id_to_n id ∈ kernel_ctors) ∧
     (∀n v. nsLookup env.v n = SOME v ⇒ v_ok ctxt v) ⇒
       env_ok ctxt env)
End

Theorem kernel_vals_Vectorv[simp]:
  ¬kernel_vals ctxt (Vectorv vs)
Proof
  rw [Once v_ok_cases]
  \\ gs [do_partial_app_def, CaseEqs ["exp", "v"]]
QED

Theorem kernel_vals_Env[simp]:
  ¬kernel_vals ctxt1 (Env env id)
Proof
  rw [Once v_ok_cases]
  \\ gs [do_partial_app_def, CaseEqs ["exp", "v"]]
QED

Theorem kernel_vals_Conv:
  kernel_vals ctxt (Conv (SOME stamp) vs) ⇒
    ∃tag m. stamp = TypeStamp tag m ∧ m ∈ kernel_types
Proof
  rw [Once v_ok_cases] \\ gs [do_partial_app_def, CaseEqs ["exp", "v"]]
  \\ irule inferred_Conv \\ gs [SF SFY_ss]
QED

Theorem kernel_vals_Conv_NONE[simp]:
  ¬kernel_vals ctxt (Conv NONE vs)
Proof
  rw [Once v_ok_cases] \\ gs [do_partial_app_def, CaseEqs ["exp", "v"]]
QED

Theorem kernel_vals_Loc[simp]:
  ¬kernel_vals ctxt (Loc loc)
Proof
  rw [Once v_ok_cases] \\ gs [do_partial_app_def, CaseEqs ["exp", "v"]]
QED

Theorem v_ok_def =
  [“v_ok ctxt (Conv opt vs)”,
   “v_ok ctxt (Closure env n x)”,
   “v_ok ctxt (Recclosure env f n)”,
   “v_ok ctxt (Vectorv vs)”,
   “v_ok ctxt (Litv lit)”,
   “v_ok ctxt (FP_WordTree fp)”,
   “v_ok ctxt (FP_BoolTree fp)”,
   “v_ok ctxt (Real r)”,
   “v_ok ctxt (Loc loc)”,
   “v_ok ctxt (Env env ns)”]
  |> map (SIMP_CONV (srw_ss()) [Once v_ok_cases])
  |> LIST_CONJ;

Theorem v_ok_div_exn_v[simp]:
  v_ok ctxt div_exn_v
Proof
  rw [v_ok_def, div_exn_v_def, div_stamp_def]
QED

Theorem v_ok_chr_exn_v[simp]:
  v_ok ctxt chr_exn_v
Proof
  rw [v_ok_def, chr_exn_v_def, chr_stamp_def]
QED

Theorem v_ok_bind_exn_v[simp]:
  v_ok ctxt bind_exn_v
Proof
  rw [v_ok_def, bind_exn_v_def]
  \\ rw [Once v_ok_cases, bind_stamp_def, kernel_types_def]
QED

Theorem v_ok_sub_exn_v[simp]:
  v_ok ctxt sub_exn_v
Proof
  rw [v_ok_def, sub_exn_v_def]
  \\ rw [Once v_ok_cases, subscript_stamp_def, kernel_types_def]
QED

Theorem env_ok_def = SIMP_CONV (srw_ss()) [Once v_ok_cases] “env_ok ctxt env”;

Theorem kernel_vals_ind = v_ok_ind
  |> Q.SPECL [‘P’,‘λ_ _. T’,‘λ_ _. T’]
  |> SIMP_RULE std_ss [] |> GEN_ALL;

Definition ref_ok_def:
  ref_ok ctxt (Varray vs) = EVERY (v_ok ctxt) vs ∧
  ref_ok ctxt (Refv v) = v_ok ctxt v ∧
  ref_ok ctxt (W8array vs) = T
End

Definition kernel_loc_ok_def:
  kernel_loc_ok s loc refs ⇔
    ∃v. LLOOKUP refs loc = SOME (Refv v) ∧
        (the_type_constants = Loc loc ⇒
           LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) s.the_type_constants v) ∧
        (the_term_constants = Loc loc ⇒
           LIST_TYPE (PAIR_TYPE STRING_TYPE TYPE_TYPE) s.the_term_constants v) ∧
        (the_axioms = Loc loc ⇒
           LIST_TYPE THM_TYPE s.the_axioms v) ∧
        (the_context = Loc loc ⇒
           LIST_TYPE UPDATE_TYPE s.the_context v)
End

Theorem kernel_loc_ok_LENGTH:
  kernel_loc_ok st loc refs ⇒
    loc < LENGTH refs
Proof
  rw [kernel_loc_ok_def]
  \\ gs [LLOOKUP_EQ_EL]
QED

Theorem kernel_loc_ok_LUPDATE1:
  kernel_loc_ok st loc refs ∧
  n ≠ loc ⇒
    kernel_loc_ok st loc (LUPDATE v n refs)
Proof
  rw [kernel_loc_ok_def]
  \\ gs [LLOOKUP_EQ_EL, EL_LUPDATE]
  \\ first_assum (irule_at Any) \\ gs []
QED

Definition eval_state_ok_def:
  eval_state_ok NONE = T ∧
  eval_state_ok (SOME (EvalDecs s)) =
    (∀v ds. s.decode_decs v = SOME ds ⇒ EVERY safe_dec ds) ∧
  eval_state_ok _ = F
End

Definition state_ok_def:
  state_ok ctxt s ⇔
    (∀n. n ∈ kernel_types ⇒ n < s.next_type_stamp) ∧
    EVERY ok_event s.ffi.io_events ∧
    eval_state_ok s.eval_state ∧
    ∃state.
      STATE ctxt state ∧
      (∀loc. loc ∈ kernel_locs ⇒ kernel_loc_ok state loc s.refs) ∧
      (∀loc r. loc ∉ kernel_locs ∧ LLOOKUP s.refs loc = SOME r ⇒ ref_ok ctxt r)
End

Theorem state_ok_dec_clock:
  state_ok ctxt (dec_clock s) = state_ok ctxt s
Proof
  rw [state_ok_def, evaluateTheory.dec_clock_def]
QED

(* -------------------------------------------------------------------------
 * Proving env_ok/v_ok/ref_ok/state_ok for things
 * ------------------------------------------------------------------------- *)

Theorem env_ok_extend_dec_env:
  env_ok ctxt env1 ∧
  env_ok ctxt env2 ⇒
    env_ok ctxt (extend_dec_env env1 env2)
Proof
  rw [env_ok_def, extend_dec_env_def, nsLookup_nsAppend_some] \\ gs [SF SFY_ss]
QED

Theorem env_ok_write_cons:
  env_ok ctxt env ∧
  (t ∈ kernel_types ⇒ nm ∈ kernel_ctors) ⇒
    env_ok ctxt (write_cons nm (n, TypeStamp s t) env)
Proof
  simp [env_ok_def, ml_progTheory.write_cons_def, SF SFY_ss]
  \\ strip_tac
  \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
  \\ rw [] \\ gs [SF SFY_ss, namespaceTheory.id_to_n_def]
QED

Theorem env_ok_write_Exn:
  env_ok ctxt env ⇒
  env_ok ctxt (write_cons nm (n,ExnStamp m) env)
Proof
  simp [env_ok_def, ml_progTheory.write_cons_def, SF SFY_ss]
  \\ strip_tac
  \\ Cases \\ rw [ml_progTheory.nsLookup_nsBind_compute] \\ gs [SF SFY_ss]
QED

Theorem env_ok_write_mod:
  env_ok ctxt env1 ∧
  env_ok ctxt env2 ⇒
    env_ok ctxt (write_mod mn env1 env2)
Proof
  rw [env_ok_def, ml_progTheory.write_mod_def, nsLookup_nsAppend_some,
      nsLookup_nsLift, CaseEq "id"]
  \\ gs [namespaceTheory.id_to_n_def, SF SFY_ss]
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
  \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
  \\ rw [] \\ gs [SF SFY_ss]
QED

Theorem env_ok_nsEmpty:
  env_ok ctxt <| v := nsEmpty; c := nsEmpty |>
Proof
  rw [env_ok_def]
QED

Theorem env_ok_empty_env:
  env_ok ctxt empty_env
Proof
  rw [env_ok_def, ml_progTheory.empty_env_def]
QED

Theorem env_ok_init_env:
  env_ok ctxt init_env
Proof
  rw [env_ok_def, ml_progTheory.init_env_def]
  \\ gvs [nsLookup_Bind_v_some, CaseEqs ["bool", "option"], kernel_types_def]
QED

Theorem v_ok_bind_exn_v[simp]:
  v_ok ctxt bind_exn_v
Proof
  fs [bind_exn_v_def]
  \\ fs [Once v_ok_cases,bind_stamp_def]
QED

Theorem v_ok_sub_exn_v[simp]:
  v_ok ctxt sub_exn_v
Proof
  rw [v_ok_def, sub_exn_v_def]
  \\ rw [Once v_ok_cases, subscript_stamp_def, kernel_types_def]
QED

Theorem v_ok_Cons:
  v_ok ctxt (Conv (SOME (TypeStamp "::" 1)) [x; y]) ⇔ v_ok ctxt x ∧ v_ok ctxt y
Proof
  simp [Once v_ok_cases] \\ fs [kernel_types_def]
  \\ eq_tac \\ rw [] \\ rw []
  \\ fs [Once v_ok_cases]
  \\ fs [do_partial_app_def,AllCaseEqs()]
  \\ imp_res_tac inferred_Conv
  \\ gvs [kernel_types_def]
QED

Theorem v_ok_Conv_NONE:
  v_ok ctxt (Conv NONE ls) =
  EVERY (v_ok ctxt) ls
Proof
  rw[v_ok_def]
QED

Theorem NUM_v_ok:
  NUM x v ==> v_ok ctxt v
Proof
  rw[ml_translatorTheory.NUM_def, ml_translatorTheory.INT_def]
  \\ rw[Once v_ok_cases]
QED

Theorem BOOL_v_ok:
  BOOL x v ==> v_ok ctxt v
Proof
  rw[ml_translatorTheory.BOOL_def, semanticPrimitivesTheory.Boolv_def]
  \\ rw[v_ok_Conv]
QED

Theorem STRING_TYPE_v_ok:
  STRING_TYPE x v ==> v_ok ctxt v
Proof
  Cases_on`x` \\ rw[ml_translatorTheory.STRING_TYPE_def]
  \\ rw[Once v_ok_cases]
QED

Theorem PAIR_TYPE_v_ok:
  PAIR_TYPE A B p v /\
  (!v. A (FST p) v ==> v_ok ctxt v) /\
  (!v. B (SND p) v ==> v_ok ctxt v) ==>
  v_ok ctxt v
Proof
  Cases_on`p` \\ rw[ml_translatorTheory.PAIR_TYPE_def]
  \\ irule v_ok_Conv \\ rw[]
QED

Theorem LIST_TYPE_v_ok:
  !A ls v. LIST_TYPE A ls v /\ EVERY (λx. !v. A x v ==> v_ok ctxt v) ls
         ==> v_ok ctxt v
Proof
  gen_tac \\ Induct \\ rw[ml_translatorTheory.LIST_TYPE_def]
  \\ irule v_ok_Conv
  \\ rw[kernel_types_def]
QED


(* -------------------------------------------------------------------------
 * Lemmas about v_ok and {TYPE,TERM,THM}_TYPE{,_HEAD}
 * ------------------------------------------------------------------------- *)

Theorem TYPE_IMP_v_ok:
  TYPE ctxt th ∧ TYPE_TYPE th v ⇒ v_ok ctxt v
Proof
  rw []
  \\ irule v_ok_KernelVals
  \\ irule v_ok_Inferred
  \\ irule inferred_TYPE
  \\ first_x_assum $ irule_at Any
  \\ fs []
QED

Theorem TERM_IMP_v_ok:
  TERM ctxt th ∧ TERM_TYPE th v ⇒ v_ok ctxt v
Proof
  rw []
  \\ irule v_ok_KernelVals
  \\ irule v_ok_Inferred
  \\ irule inferred_TERM
  \\ first_x_assum $ irule_at Any
  \\ fs []
QED

Theorem THM_IMP_v_ok:
  THM ctxt th ∧ THM_TYPE th v ⇒ v_ok ctxt v
Proof
  rw []
  \\ irule v_ok_KernelVals
  \\ irule v_ok_Inferred
  \\ irule inferred_THM
  \\ first_x_assum $ irule_at Any
  \\ fs []
QED

Theorem v_ok_THM_TYPE_HEAD:
  v_ok ctxt v ∧
  THM_TYPE_HEAD v ⇒
    ∃th. THM_TYPE th v
Proof
  rw [Once v_ok_cases, kernel_types_def, THM_TYPE_HEAD_def]
  \\ gs [Once v_ok_cases, do_partial_app_def, AllCaseEqs ()]
  \\ gs [Once inferred_cases, SF SFY_ss, Conv_NOT_IN_kernel_funs]
  \\ TRY (rename [‘TYPE ctxt ty’] \\ Cases_on ‘ty’ \\ gs [TYPE_TYPE_def])
  \\ TRY (rename [‘TERM ctxt tm’] \\ Cases_on ‘tm’ \\ gs [TERM_TYPE_def])
  \\ TRY (rename [‘THM ctxt th’] \\ Cases_on ‘th’ \\ gs [THM_TYPE_def])
QED

Theorem v_ok_TERM_TYPE_HEAD:
  v_ok ctxt v ∧
  TERM_TYPE_HEAD v ⇒
    ∃tm. TERM_TYPE tm v
Proof
  rw [Once v_ok_cases, kernel_types_def, TERM_TYPE_HEAD_def]
  \\ gs [Once v_ok_cases, do_partial_app_def, AllCaseEqs ()]
  \\ gs [Once inferred_cases, SF SFY_ss, Conv_NOT_IN_kernel_funs]
  \\ TRY (rename [‘TYPE ctxt ty’] \\ Cases_on ‘ty’ \\ gs [TYPE_TYPE_def])
  \\ TRY (rename [‘TERM ctxt tm’] \\ Cases_on ‘tm’ \\ gs [TERM_TYPE_def])
  \\ TRY (rename [‘THM ctxt th’] \\ Cases_on ‘th’ \\ gs [THM_TYPE_def])
QED

Theorem v_ok_TYPE_TYPE_HEAD:
  v_ok ctxt v ∧
  TYPE_TYPE_HEAD v ⇒
    ∃ty. TYPE_TYPE ty v
Proof
  rw [Once v_ok_cases, kernel_types_def, TYPE_TYPE_HEAD_def]
  \\ gs [Once v_ok_cases, do_partial_app_def, AllCaseEqs ()]
  \\ gs [Once inferred_cases, SF SFY_ss, Conv_NOT_IN_kernel_funs]
  \\ TRY (rename [‘TYPE ctxt ty’] \\ Cases_on ‘ty’ \\ gs [TYPE_TYPE_def])
  \\ TRY (rename [‘TERM ctxt tm’] \\ Cases_on ‘tm’ \\ gs [TERM_TYPE_def])
  \\ TRY (rename [‘THM ctxt th’] \\ Cases_on ‘th’ \\ gs [THM_TYPE_def])
QED

Theorem v_ok_LIST_TYPE_HEAD:
  v_ok ctxt v ∧
  (!v. v_ok ctxt v ∧ A_HEAD v ==> ?a. A a v) ∧
  LIST_TYPE_HEAD A_HEAD v ⇒
    ∃tms. LIST_TYPE A tms v
Proof
  completeInduct_on ‘v_size v’
  \\ rw [] \\ gvs [PULL_FORALL,AND_IMP_INTRO,LIST_TYPE_HEAD_def,PULL_EXISTS]
  \\ Cases_on ‘l’ \\ fs [ml_translatorTheory.LIST_TYPE_def] \\ gvs []
  THEN1 (qexists_tac ‘[]’ \\ fs [ml_translatorTheory.LIST_TYPE_def])
  \\ rename [‘Conv _ [x;y]’]
  \\ fs [v_ok_Cons]
  \\ last_x_assum (qspecl_then [‘y’,‘t’] mp_tac)
  \\ impl_tac THEN1 fs [v_size_def]
  \\ strip_tac
  \\ first_x_assum(
       drule_then $ drule_then $ qx_choose_then`tm`strip_assume_tac)
  \\ qexists_tac ‘tm::tms’
  \\ fs [ml_translatorTheory.LIST_TYPE_def]
QED

Theorem v_ok_LIST_TERM_TYPE_HEAD:
  v_ok ctxt v ∧
  LIST_TYPE_HEAD TERM_TYPE_HEAD v ⇒
    ∃tms. LIST_TYPE TERM_TYPE tms v
Proof
  strip_tac
  \\ irule v_ok_LIST_TYPE_HEAD
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ metis_tac[v_ok_TERM_TYPE_HEAD]
QED

Theorem v_ok_LIST_THM_TYPE_HEAD:
  v_ok ctxt v ∧
  LIST_TYPE_HEAD THM_TYPE_HEAD v ⇒
    ∃ths. LIST_TYPE THM_TYPE ths v
Proof
  strip_tac
  \\ irule v_ok_LIST_TYPE_HEAD
  \\ first_assum (irule_at Any)
  \\ first_assum (irule_at Any)
  \\ rw [v_ok_THM_TYPE_HEAD, SF SFY_ss]
QED

Theorem v_ok_PAIR_TYPE_HEAD:
  v_ok ctxt v ∧
  (!v. v_ok ctxt v ∧ A_HEAD v ==> ?a. A a v) ∧
  (!v. v_ok ctxt v ∧ B_HEAD v ==> ?b. B b v) ∧
  PAIR_TYPE_HEAD A_HEAD B_HEAD v ⇒
    ∃p. PAIR_TYPE A B p v
Proof
  simp[PAIR_TYPE_HEAD_def]
  \\ rw[Once v_ok_cases, ml_translatorTheory.PAIR_TYPE_def, EXISTS_PROD]
  \\ fs[kernel_vals_Conv_NONE]
  \\ metis_tac[]
QED

Theorem v_ok_LIST_PAIR_TYPE_HEAD:
  v_ok ctxt v ∧
  (!v. v_ok ctxt v ∧ A_HEAD v ==> ?a. A a v) ∧
  (!v. v_ok ctxt v ∧ B_HEAD v ==> ?b. B b v) ∧
  LIST_TYPE_HEAD (PAIR_TYPE_HEAD A_HEAD B_HEAD) v
  ⇒
  ∃ls. LIST_TYPE (PAIR_TYPE A B) ls v
Proof
  rpt strip_tac
  \\ irule v_ok_LIST_TYPE_HEAD
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rpt strip_tac
  \\ irule v_ok_PAIR_TYPE_HEAD
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ metis_tac[]
QED

Theorem v_ok_TYPE:
  v_ok ctxt v ∧
  TYPE_TYPE ty v ⇒
    TYPE ctxt ty
Proof
  strip_tac
  \\ Cases_on ‘inferred ctxt v’
  >- (
    irule TYPE_from_TYPE_TYPE
    \\ gs [SF SFY_ss])
  \\ Cases_on ‘ty’ \\ gvs [TYPE_TYPE_def, v_ok_def, kernel_types_def]
  \\ gvs [Once v_ok_cases, do_partial_app_def, CaseEqs ["exp", "v"]]
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

Theorem v_ok_LIST:
  (!x v. A_TYPE x v ∧ v_ok ctxt v ==> A ctxt x) ==>
  !ls v.
    LIST_TYPE A_TYPE ls v ∧ v_ok ctxt v ⇒ EVERY (A ctxt) ls
Proof
  strip_tac
  \\ Induct
  \\ rw[ml_translatorTheory.LIST_TYPE_def]
  \\ fs[v_ok_Cons]
  \\ metis_tac[]
QED

Theorem v_ok_LIST_TERM:
  ∀tms v ctxt. LIST_TYPE TERM_TYPE tms v ∧ v_ok ctxt v ⇒ EVERY (TERM ctxt) tms
Proof
  rpt strip_tac
  \\ irule v_ok_LIST
  \\ first_assum $ irule_at Any
  \\ first_assum $ irule_at Any
  \\ metis_tac[v_ok_TERM]
QED

Theorem v_ok_LIST_THM:
  ∀ths v ctxt. LIST_TYPE THM_TYPE ths v ∧ v_ok ctxt v ⇒ EVERY (THM ctxt) ths
Proof
  rpt strip_tac
  \\ irule v_ok_LIST
  \\ first_assum (irule_at Any)
  \\ first_assum (irule_at Any)
  \\ rw [v_ok_THM, SF SFY_ss]
QED

Theorem v_ok_LIST_TYPE:
  ∀tms v ctxt. LIST_TYPE TYPE_TYPE tms v ∧ v_ok ctxt v ⇒ EVERY (TYPE ctxt) tms
Proof
  rpt strip_tac
  \\ irule v_ok_LIST
  \\ first_assum $ irule_at Any
  \\ first_assum $ irule_at Any
  \\ metis_tac[v_ok_TYPE]
QED

Theorem v_ok_PAIR:
  (!x v. A_TYPE x v ∧ v_ok ctxt v ⇒ A ctxt x) ∧
  (!x v. B_TYPE x v ∧ v_ok ctxt v ⇒ B ctxt x) ∧
  PAIR_TYPE A_TYPE B_TYPE x v ∧ v_ok ctxt v ⇒
    (λctxt p. A ctxt (FST p) ∧ B ctxt (SND p)) ctxt x
Proof
  Cases_on`x`
  \\ rw[ml_translatorTheory.PAIR_TYPE_def]
  \\ pop_assum mp_tac \\ rw[Once v_ok_cases]
  \\ metis_tac[]
QED

Theorem LIST_TYPE_perms_ok:
  ∀xs xsv.
    (∀x v. A x v ∧ MEM x xs ⇒ perms_ok ps v) ∧
    LIST_TYPE A xs xsv ⇒
      perms_ok ps xsv
Proof
  Induct \\ rw []
  \\ gs [ml_translatorTheory.LIST_TYPE_def, perms_ok_def, SF SFY_ss]
QED

Theorem PAIR_TYPE_perms_ok:
  (∀x v. A x v ⇒ perms_ok ps v) ∧
  (∀x v. B x v ⇒ perms_ok ps v) ∧
  PAIR_TYPE A B x v ⇒
    perms_ok ps v
Proof
  PairCases_on ‘x’ \\ fs [ml_translatorTheory.PAIR_TYPE_def]
  \\ rw [] \\ res_tac \\ fs []
  \\ simp [Once perms_ok_cases]
QED

Theorem UNIT_TYPE_perms_ok:
  !u v. UNIT_TYPE u v ==> perms_ok ps v
Proof
  rw[ml_translatorTheory.UNIT_TYPE_def, perms_ok_def]
QED

Theorem INT_perms_ok:
  ∀s v. INT s v ⇒ perms_ok ps v
Proof
  gvs [ml_translatorTheory.INT_def, perms_ok_def]
QED

Theorem NUM_perms_ok:
  ∀s v. NUM s v ⇒ perms_ok ps v
Proof
  gvs [ml_translatorTheory.NUM_def, ml_translatorTheory.INT_def, perms_ok_def]
QED

Theorem STRING_TYPE_perms_ok:
  ∀s v. STRING_TYPE s v ⇒ perms_ok ps v
Proof
  Cases \\ gvs [ml_translatorTheory.STRING_TYPE_def, perms_ok_def]
QED

Theorem TYPE_TYPE_perms_ok:
  ∀ty v. TYPE_TYPE ty v ⇒ perms_ok ps v
Proof
  recInduct TYPE_TYPE_ind \\ rw [TYPE_TYPE_def]
  \\ imp_res_tac STRING_TYPE_perms_ok
  \\ gvs [ml_translatorTheory.STRING_TYPE_def, perms_ok_def]
  \\ metis_tac [LIST_TYPE_perms_ok]
QED

Theorem TERM_TYPE_perms_ok:
  ∀tm v. TERM_TYPE tm v ⇒ perms_ok ps v
Proof
  Induct \\ rw [TERM_TYPE_def]
  \\ res_tac \\ fs [perms_ok_def]
  \\ imp_res_tac STRING_TYPE_perms_ok
  \\ imp_res_tac TYPE_TYPE_perms_ok \\ fs []
QED

Theorem THM_TYPE_perms_ok:
  ∀th v. THM_TYPE th v ⇒ perms_ok ps v
Proof
  Cases \\ rw [THM_TYPE_def] \\ imp_res_tac TERM_TYPE_perms_ok
  \\ fs [perms_ok_def]
  \\ drule_at (Pos last) LIST_TYPE_perms_ok
  \\ disch_then irule \\ rw []
  \\ imp_res_tac TERM_TYPE_perms_ok \\ fs []
QED

Theorem LIST_TERM_TYPE_perms_ok:
  ∀tm v. LIST_TYPE TERM_TYPE tm v ⇒ perms_ok ps v
Proof
  rw []
  \\ drule_at Any LIST_TYPE_perms_ok
  \\ fs [TERM_TYPE_perms_ok, SF SFY_ss]
QED

Theorem LIST_TYPE_TYPE_perms_ok:
  ∀tm v. LIST_TYPE TYPE_TYPE tm v ⇒ perms_ok ps v
Proof
  rw []
  \\ drule_at Any LIST_TYPE_perms_ok
  \\ fs [TYPE_TYPE_perms_ok, SF SFY_ss]
QED

Theorem LIST_TYPE_THM_perms_ok:
  ∀tm v. LIST_TYPE THM_TYPE th v ⇒ perms_ok ps v
Proof
  rw []
  \\ drule_at Any LIST_TYPE_perms_ok
  \\ fs [THM_TYPE_perms_ok, SF SFY_ss]
QED

Theorem UPDATE_TYPE_perms_ok:
  ∀u v. UPDATE_TYPE u v ⇒ perms_ok ps v
Proof
  Cases \\ rw [UPDATE_TYPE_def]
  \\ imp_res_tac TYPE_TYPE_perms_ok
  \\ imp_res_tac TERM_TYPE_perms_ok
  \\ imp_res_tac STRING_TYPE_perms_ok
  \\ imp_res_tac NUM_perms_ok
  \\ fs [perms_ok_def]
  \\ drule_at (Pos last) LIST_TYPE_perms_ok
  \\ disch_then irule \\ rw []
  \\ drule_at (Pos last) PAIR_TYPE_perms_ok
  \\ disch_then irule \\ rw []
  \\ imp_res_tac STRING_TYPE_perms_ok
  \\ imp_res_tac NUM_perms_ok
  \\ imp_res_tac TERM_TYPE_perms_ok \\ fs []
QED

Inductive sub_conv:
  (MEM v vs ==> sub_conv v (Conv cn vs))
End

Theorem sub_conv_ok:
  !v w. sub_conv v w ==> v_ok ctxt w ==> v_ok ctxt v
Proof
  gen_tac \\ ho_match_mp_tac sub_conv_ind
  \\ rw[]
  \\ pop_assum mp_tac
  \\ rw[Once v_ok_cases]
  \\ fs[EVERY_MEM, SF SFY_ss]
  \\ pop_assum mp_tac
  \\ simp[Once v_ok_cases]
  \\ simp[do_partial_app_def]
  \\ reverse strip_tac
  >- fs[CaseEqs["option","v","exp"]]
  \\ fs[inferred_cases]
  >- (
    Cases_on`ty`
    \\ gvs[SF SFY_ss, STRING_TYPE_v_ok, TYPE_TYPE_def]
    \\ imp_res_tac holKernelProofTheory.TYPE
    \\ drule_then irule LIST_TYPE_v_ok
    \\ fs[EVERY_MEM] \\ rw[]
    \\ res_tac
    \\ simp[SF SFY_ss, TYPE_IMP_v_ok])
  >- (
    Cases_on`tm`
    \\ gvs[SF SFY_ss, STRING_TYPE_v_ok, TERM_TYPE_def]
    \\ imp_res_tac holKernelProofTheory.TERM
    \\ simp[SF SFY_ss, TYPE_IMP_v_ok, TERM_IMP_v_ok]
    \\ Cases_on`t`
    \\ TRY (
      fs[holKernelProofTheory.TERM_def, holSyntaxTheory.term_ok_def]
      \\ NO_TAC)
    \\ imp_res_tac holKernelProofTheory.TERM
    \\ TRY (
      rename1 `TERM_TYPE (Var x ty)`
      \\ `TERM ctxt (Var x ty)` by (
        fs[holKernelProofTheory.TERM_def,
           holKernelProofTheory.TYPE_def]
        \\ fs[holSyntaxTheory.term_ok_def]))
    \\ simp[SF SFY_ss, TERM_IMP_v_ok])
  \\ Cases_on`th`
  \\ imp_res_tac holKernelProofTheory.THM
  \\ fs[THM_TYPE_def] \\ gvs[]
  \\ simp[SF SFY_ss, TERM_IMP_v_ok]
  \\ drule_then irule LIST_TYPE_v_ok
  \\ fs[EVERY_MEM] \\ rw[]
  \\ res_tac
  \\ simp[SF SFY_ss, TERM_IMP_v_ok]
QED

Theorem v_ok_Conv_alt:
  v_ok ctxt (Conv (SOME stamp) vs) ⇒
    EVERY (v_ok ctxt) vs
Proof
  rw[EVERY_MEM]
  \\ drule sub_conv_rules
  \\ disch_then (C (resolve_then Any irule) sub_conv_ok)
  \\ first_assum $ irule_at Any
QED

val _ = export_theory ();
