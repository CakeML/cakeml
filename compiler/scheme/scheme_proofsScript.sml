(*
  Proofs for Scheme to CakeML compilation
*)
open preamble;
open scheme_astTheory;
open scheme_semanticsTheory;
open scheme_to_cakeTheory;
open astTheory;

open evaluateTheory;
open semanticPrimitivesTheory;
open namespaceTheory;

val _ = new_theory "scheme_proofs";

Definition subset1_def:
  (subset1 (Apply fn args) ⇔ subset1 fn ∧ EVERY subset1 args) ∧
  (subset1 (Cond c t f) ⇔ subset1 c ∧ subset1 t ∧ subset1 f) ∧
  (subset1 (Exception _) ⇔ T) ∧
  (subset1 (Val v) ⇔ case v of
  | Prim _ => T
  | SNum _ => T
  | SBool _ => T
  | _ => F) ∧
  (subset1 _ ⇔ F)
Termination
  WF_REL_TAC ‘measure exp_size’
End

Theorem val_correct:
  ∀ n . ∃ k . SND (evaluate <| clock := k |> myEnv [scheme_program_to_cake (Val (SNum n))])
    = Rval [Conv (SOME $ TypeStamp "SNum" 0) [Litv $ IntLit &n]]
Proof
  strip_tac
  >> qexists_tac ‘99’
  >> rw[scheme_program_to_cake_def, cps_transform_def, myEnv_def, myC_def,
    to_ml_vals_def,
    evaluate_def, do_opapp_def, dec_clock_def,
    nsLookup_def, nsBind_def, do_con_check_def, build_conv_def]
QED

val _ = export_theory();