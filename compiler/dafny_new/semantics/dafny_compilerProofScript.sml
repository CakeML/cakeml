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

Definition env_rel_def:
  env_rel env_dfy env_cml ⇔
    nsLookup env_cml.c (Short "True") = SOME (0, TypeStamp "True" 0) ∧
    nsLookup env_cml.c (Short "False") = SOME (0, TypeStamp "False" 0)
End

(* TODO Define as inductive *)
Definition val_rel_def:
  (val_rel m (BoolV b) v_cml ⇔ v_cml = Boolv b) ∧
  (val_rel m (IntV i₀) (Litv (IntLit i₁)) ⇔ i₀ = i₁) ∧
  (val_rel m (StrV ms) (Litv (StrLit s)) ⇔ (explode ms) = s) ∧
  (val_rel m (ArrV len loc) (Conv NONE [Litv (IntLit (len')); Loc T loc']) ⇔
     len' = &len ∧ FLOOKUP m loc = SOME loc')
  (val_rel _ _ _ ⇔ F)
End

Definition oval_ref_rel_def:
  oval_ref_eq (SOME dval) (Refv cval) = val_rel dval cval ∧
  oval_ref_eq _ _ = F
End

(* TODO Should be more like locals_rel_def *)
Inductive array_rel:
[~nil:]
  array_rel m [] []
[~array:]
  LIST_REL (val_rel m) vs vs' ∧ array_rel m rest rest' ⇒
    array_rel m ((HArr vs)::rest) ((Varray vs')::rest')
[~ref:]
  array_rel m rest rest' ⇒ array_rel m rest ((Refv v)::rest')
End

Definition locals_rel_def:
  local_rel m (l: mlstring |-> num) s_locals t_refs cml_env ⇔
    INJ (λx. l ' x) (FDOM l) 𝕌(:num) ∧
    ∀var val.
      ALOOKUP s_locals var = SOME val ⇒
      ∃loc val'.
        FLOOKUP l var = SOME loc ∧
        store_lookup loc t_refs = SOME val' ∧
        val_rel m val val' ∧
        nsLookup cml_env (Short var) = SOME (Loc T loc)
End

Definition state_rel_def:
  state_rel m l s t cml_env ⇔
    array_rel m s.heap t.refs ∧
    locals_rel m l s.locals t.refs cml_env
    (* TODO How to do state rel between cout? *)
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

(* Theorem correct_exp: *)
(*   (∀s₁ env_dfy e_dfy s₂ r_dfy t₁ env_cml e_cml. *)
(*      evaluate_exp s₁ env_dfy e_dfy = (s₂, r_dfy) ∧ from_exp e_dfy = INR e_cml *)
(*      ∧ state_rel s₁ t₁ ∧ env_rel env_dfy env_cml ∧ ¬(is_exp_fail r_dfy) *)
(*      ⇒ ∃t₂ r_cml. *)
(*          evaluate$evaluate t₁ env_cml [e_cml] = (t₂, r_cml) ∧ state_rel s₂ t₂ *)
(*          ∧ exp_res_rel r_dfy r_cml) ∧ *)
(*   (∀s₁ env_dfy es_dfy s₂ rs_dfy t₁ env_cml es_cml. *)
(*      evaluate_exps s₁ env_dfy es_dfy = (s₂, rs_dfy) *)
(*      ∧ map_from_exp es_dfy = INR es_cml *)
(*      ∧ state_rel s₁ t₁ ∧ env_rel env_dfy env_cml ∧ ¬(is_exp_fail rs_dfy) *)
(*      ⇒ ∃t₂ rs_cml. *)
(*          evaluate$evaluate t₁ env_cml es_cml = (t₂, rs_cml) ∧ state_rel s₂ t₂ *)
(*          ∧ exps_res_rel rs_dfy rs_cml) *)
(* Proof *)
(*   ho_match_mp_tac evaluate_exp_ind *)
(*   >> rpt strip_tac *)
(*   >~ [‘Lit l’] >- *)
(*    (gvs [from_exp_def, from_lit_def, evaluate_def, do_con_check_def, *)
(*          env_rel_def, build_conv_def, AllCaseEqs ()]) *)
(* QED *)

val _ = export_theory ();
