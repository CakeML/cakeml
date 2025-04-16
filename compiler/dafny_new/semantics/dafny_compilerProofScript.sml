(*
  Correctness proof for the Dafny to CakeML compiler.
*)

open preamble
open dafny_to_cakemlTheory
open dafny_evaluateTheory
open evaluateTheory
open semanticPrimitivesTheory

val _ = new_theory "dafny_compilerProof";

Type dfy_state[pp] = “:dafny_semanticPrimitives$state”
Type dfy_env[pp] = “:dafny_semanticPrimitives$sem_env”
Type dfy_exp[pp] = “:dafny_ast$exp”
Type dfy_exp_res[pp] = “:'a dafny_semanticPrimitives$exp_result”

Type cml_state[pp] = “:α semanticPrimitives$state”
Type cml_env[pp] = “:v semanticPrimitives$sem_env”
Type cml_exp[pp] = “:ast$exp”
Type cml_res[pp] = “:(v list, v) semanticPrimitives$result”

Definition state_rel_def:
  state_rel s t ⇔
    ∀map l, map ∈ s.locals ∧ l ∈ FDOM map
End

Definition env_rel_def:
  env_rel env_dfy env_cml ⇔
    nsLookup env_cml.c (Short "True") = SOME (0, TypeStamp "True" 0) ∧
    nsLookup env_cml.c (Short "False") = SOME (0, TypeStamp "False" 0)
End

Definition val_rel_def:
  (val_rel (BoolV b) v_cml ⇔ v_cml = Boolv b) ∧
  (val_rel (IntV i₀) (Litv (IntLit i₁)) ⇔ i₀ = i₁) ∧
  (val_rel (StrV ms) (Litv (StrLit s)) ⇔ (explode ms) = s) ∧
  (val_rel _ _ ⇔ F)
End

Definition exp_res_rel_def:
  exp_res_rel (Rval (v_dfy : value)) (Rval [v_cml] : cml_res) ⇔
    val_rel v_dfy v_cml
End

Definition exps_res_rel_def:
  exps_res_rel (Rval vs_dfy) (Rval vs_cml : cml_res) ⇔
    LIST_REL val_rel vs_dfy vs_cml
End

Definition is_exp_fail_def[simp]:
  is_exp_fail (Rerr _) = T ∧
  is_exp_fail _ = F
End

Theorem correct_exp:
  (∀s₁ env_dfy e_dfy s₂ r_dfy t₁ env_cml e_cml.
     evaluate_exp s₁ env_dfy e_dfy = (s₂, r_dfy) ∧ from_exp e_dfy = INR e_cml
     ∧ state_rel s₁ t₁ ∧ env_rel env_dfy env_cml ∧ ¬(is_exp_fail r_dfy)
     ⇒ ∃t₂ r_cml.
         evaluate$evaluate t₁ env_cml [e_cml] = (t₂, r_cml) ∧ state_rel s₂ t₂
         ∧ exp_res_rel r_dfy r_cml) ∧
  (∀s₁ env_dfy es_dfy s₂ rs_dfy t₁ env_cml es_cml.
     evaluate_exps s₁ env_dfy es_dfy = (s₂, rs_dfy)
     ∧ map_from_exp es_dfy = INR es_cml
     ∧ state_rel s₁ t₁ ∧ env_rel env_dfy env_cml ∧ ¬(is_exp_fail rs_dfy)
     ⇒ ∃t₂ rs_cml.
         evaluate$evaluate t₁ env_cml es_cml = (t₂, rs_cml) ∧ state_rel s₂ t₂
         ∧ exps_res_rel rs_dfy rs_cml)
Proof
  ho_match_mp_tac evaluate_exp_ind
  >> rpt strip_tac
  >~ [‘Lit l’] >-
   (gvs [from_exp_def, from_lit_def, evaluate_def, do_con_check_def,
         env_rel_def, build_conv_def, AllCaseEqs ()])

QED
