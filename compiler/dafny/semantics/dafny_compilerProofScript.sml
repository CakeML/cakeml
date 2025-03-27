(*
 Correctness proof for the Dafny to CakeML compiler.
*)

open preamble

open dafny_semanticPrimitivesTheory
open dafny_astTheory

open semanticPrimitivesTheory
open simpleIOTheory
open astTheory

open dafny_to_cakemlTheory
open dafny_evaluateTheory
open evaluateTheory
open namespaceTheory
open primTypesTheory
open result_monadTheory

val _ = new_theory "dafny_compilerProof";

Type dafny_program = “:dafny_ast$module list”
Type dafny_state = “:dafny_semanticPrimitives$state”
Type dafny_env = “:dafny_semanticPrimitives$sem_env”
Type dafny_exp = “:dafny_ast$expression”
Type dafny_res = “:'a dafny_evaluate$dafny_result”

Type cakeml_program = “:ast$dec list”
Type cakeml_state = “:simpleIO semanticPrimitives$state”
Type cakeml_env = “:v semanticPrimitives$sem_env”
Type cakeml_exp = “:ast$exp”
Type cakeml_res = “:(v list, v) semanticPrimitives$result”

(* NOTE Can be a lot more declarative; i.e. use ∀ instead of implementing it *)

(* TODO/NOTE env_rel can be defined using (parts of) compile *)
(* TODO Listing env_cml.c like that seems rough; can we generalize this without
   making the proofs more painful? *)
Definition env_rel_def:
  env_rel (env_dfy : dafny_env) (env_cml : cakeml_env) ⇔
    nsLookup env_cml.c (Short "True") = SOME (0, TypeStamp "True" 0) ∧
    nsLookup env_cml.c (Short "False") = SOME (0, TypeStamp "False" 0)
End

Definition dafny_to_cakeml_v_def[simp]:
  dafny_to_cakeml_v UnitV = (Conv NONE []) ∧
  dafny_to_cakeml_v (BoolV b) = (Boolv b) ∧
  dafny_to_cakeml_v (IntV i) = (Litv (IntLit i)) ∧
  dafny_to_cakeml_v (CharV c) = (Litv (Char c)) ∧
  dafny_to_cakeml_v (StrV s) = (Litv (StrLit s))
End

(* TODO *)
Definition state_rel_def:
  state_rel (s : dafny_state) (t : cakeml_state) ⇔ T
End

Definition res_rel_def:
  res_rel (Rval v_dfy) (Rval [v_cml]) = (dafny_to_cakeml_v v_dfy = v_cml) ∧
  res_rel (Rerr Rtype_error) (Rerr (Rabort Rtype_error)) = T ∧
  res_rel (Rerr Rtimeout_error) (Rerr (Rabort Rtimeout_error)) = T ∧
  res_rel (Rerr Runsupported) (_ : cakeml_res) = T ∧
  res_rel (_ : value dafny_res) (_ : cakeml_res) = F
End

(* TODO *)
Definition list_res_rel_def:
  list_res_rel (r_dfy : (value list) dafny_res) (r_cml : cakeml_res) = T
End

Theorem res_rel_rval:
  res_rel (Rval v) x ⇔ ∃w. x = Rval [w] ∧ dafny_to_cakeml_v v = w
Proof
  Cases_on ‘x’ >> gvs [oneline res_rel_def]
  >> Cases_on ‘a’ >> gvs []
  >> Cases_on ‘t’ >> gvs [EQ_SYM_EQ]
QED

Definition is_fail_dfy_def[simp]:
  is_fail_dfy (Rerr _ : 'a dafny_result) = T ∧
  is_fail_dfy _ = F
End

Theorem correct_stmts:
  (∀ (s₁ : dafny_state) (env_dfy : dafny_env) (e : dafny_exp) (s₂ : dafny_state)
     (r_dfy : value dafny_res) (t₁ : cakeml_state) (env_cml : cakeml_env)
     (cml_e : cakeml_exp) (path : ident list).
     evaluate_exp s₁ env_dfy e = (s₂, r_dfy) ∧
     from_expression comp e = INR cml_e ∧ state_rel s₁ t₁ ∧
     env_rel env_dfy env_cml ∧ ¬(is_fail_dfy r_dfy)
     ⇒ ∃ (t₂ : cakeml_state) (r_cml : cakeml_res).
         evaluate$evaluate t₁ env_cml [cml_e] = (t₂, r_cml) ∧
         state_rel s₂ t₂ ∧ res_rel r_dfy r_cml) ∧
  (∀ (s₁ : dafny_state) (env_dfy : dafny_env) (es : dafny_exp list)
     (s₂ : dafny_state) (r_dfy : (value list) dafny_res) (t₁ : cakeml_state)
     (env_cml : cakeml_env) (cml_e : cakeml_exp) (path : ident list).
     evaluate_exps s₁ env_dfy es = (s₂, r_dfy) ∧
     map_from_expression comp es = INR cml_es ∧ state_rel s₁ t₁ ∧
     env_rel env_dfy env_cml ∧ ¬(is_fail_dfy r_dfy)
     ⇒ ∃ (t₂ : cakeml_state) (r_cml : cakeml_res).
         evaluate$evaluate t₁ env_cml cml_es = (t₂, r_cml) ∧
         state_rel s₂ t₂ ∧ list_res_rel r_dfy r_cml) ∧
  (∀ (s₁ : dafny_state) (env_dfy : dafny_env) (stmt : statement)
     (s₂ : dafny_state) (r_dfy : value dafny_res) (t₁ : cakeml_state)
     (env_cml : cakeml_env) (cml_e : cakeml_exp) (path : ident list)
     (lvl : int) (epi : exp).
     evaluate_stmt s₁ env_dfy stmt = (s₂, r_dfy) ∧
     from_stmt comp lvl stmt epi = INR cml_e ∧ state_rel s₁ t₁ ∧
     env_rel env_dfy env_cml ∧ ¬(is_fail_dfy r_dfy)
     ⇒ ∃ (t₂ : cakeml_state) (r_cml : cakeml_res).
         evaluate$evaluate t₁ env_cml [cml_e] = (t₂, r_cml) ∧
         state_rel s₂ t₂ ∧ res_rel r_dfy r_cml) ∧
  (∀ (s₁ : dafny_state) (env_dfy : dafny_env) (stmts : statement list)
     (s₂ : dafny_state) (r_dfy : value dafny_res) (t₁ : cakeml_state)
     (env_cml : cakeml_env) (cml_e : cakeml_exp) (path : ident list)
     (lvl : int) (epi : exp).
     evaluate_stmts s₁ env_dfy stmts = (s₂, r_dfy) ∧
     from_stmts comp lvl stmts epi = INR cml_e ∧ state_rel s₁ t₁ ∧
     env_rel env_dfy env_cml ∧ ¬(is_fail_dfy r_dfy)
     ⇒ ∃ (t₂ : cakeml_state) (r_cml : cakeml_res).
         evaluate$evaluate t₁ env_cml [cml_e] = (t₂, r_cml) ∧
         state_rel s₂ t₂ ∧ res_rel r_dfy r_cml)
Proof
  ho_match_mp_tac evaluate_stmts_ind
  >> rpt strip_tac
  >> cheat
QED

val _ = export_theory ();
