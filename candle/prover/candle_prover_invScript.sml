(*
  Definitions of invariants that are to be maintained during
  evaluate of Candle prover
 *)

open preamble helperLib;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     terminationTheory namespacePropsTheory evaluatePropsTheory
     sptreeTheory ml_hol_kernelProgTheory;
open permsTheory candle_kernel_valsTheory ast_extrasTheory;
local open ml_progLib in end

val _ = new_theory "candle_prover_inv";

val _ = set_grammar_ancestry [
  "candle_kernel_vals", "ast_extras", "termination", "namespaceProps", "perms",
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

val _ = export_theory ();
