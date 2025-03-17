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
Type dafny_res = “:dafny_evaluate$dafny_result”

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

Definition dafny_to_cakeml_v_def:
  dafny_to_cakeml_v UnitV = (Conv NONE []) ∧
  dafny_to_cakeml_v (BoolV b) = (Boolv b) ∧
  dafny_to_cakeml_v (IntV i) = (Litv (IntLit i)) ∧
  dafny_to_cakeml_v (CharV c) = (Litv (Char c)) ∧
  dafny_to_cakeml_v (StrV s) = (Litv (StrLit s))
End

Definition res_rel_def:
  res_rel (Rval v_dfy) (Rval [v_cml]) = (dafny_to_cakeml_v v_dfy = v_cml) ∧
  res_rel (Rret v_dfy) (Rval [v_cml]) = (dafny_to_cakeml_v v_dfy = v_cml) ∧
  res_rel (Rerr Rtype_error) (Rerr (Rabort Rtype_error)) = T ∧
  res_rel (Rerr Rtimeout_error) (Rerr (Rabort Rtimeout_error)) = T ∧
  res_rel (Rerr Runsupported) (_ : cakeml_res) = T ∧
  res_rel (_ : dafny_res) (_ : cakeml_res) = F
End

Theorem res_rel_rval:
  res_rel (Rval v) x ⇔ ∃w. x = Rval [w] ∧ dafny_to_cakeml_v v = w
Proof
  Cases_on ‘x’ >> gvs [oneline res_rel_def]
  >> Cases_on ‘a’ >> gvs []
  >> Cases_on ‘t’ >> gvs [EQ_SYM_EQ]
QED

Definition is_fail_dfy_def[simp]:
  is_fail_dfy (Rerr _ : dafny_result) = T ∧
  is_fail_dfy _ = F
End

Theorem exp_not_ret:
  ∀s1 env_dfy e st' v. evaluate_exp s1 env_dfy e = (st', Rret v) ⇔ F
Proof
  ho_match_mp_tac evaluate_exp_ind >> rw [evaluate_exp_def]
  >- (Cases_on ‘literal_to_value l’ >> gvs [])
  >- (Cases_on ‘bop’ >> gvs [do_bop_def, AllCaseEqs ()])
QED

Theorem correct_exp:
  ∀ (s₁ : dafny_state) (env_dfy : dafny_env) (e : dafny_exp) (s₂ : dafny_state)
    (r_dfy : dafny_res) (t₁ : cakeml_state) (env_cml : cakeml_env)
    (cml_e : cakeml_exp).
    evaluate_exp s₁ env_dfy e = (s₂, r_dfy) ∧ ¬(is_fail_dfy r_dfy) ∧
    (* state_rel s₁ t₁ ∧ *) env_rel env_dfy env_cml ∧
    (* TODO comp and env for from_expression are sketchy; should they come
       from state? *)
    from_expression (Companion [] []) [] e = INR cml_e ⇒
    ∃ (t₂ : cakeml_state) (r_cml : cakeml_res).
      evaluate$evaluate t₁ env_cml [cml_e] = (t₂, r_cml) ∧
      (* state_rel s₂ t₂ ∧ *) res_rel r_dfy r_cml
Proof
  ho_match_mp_tac evaluate_exp_ind >> rw[]
  >> pop_assum mp_tac >> simp [Once from_expression_def] >> strip_tac
  >~ [‘BinOp’]
  >- (gvs [evaluate_exp_def, CaseEq "prod",
           CaseEq "dafny_semanticPrimitives$result"]
      >~ [‘evaluate_exp _ _ _ = (_, Rret _)’] >- gvs [exp_not_ret]
      >- (Cases_on ‘bop’
          >> gvs [exp_not_ret, is_lop_def, do_bop_def, AllCaseEqs ()]
          >> (pop_assum mp_tac >> simp [Once from_expression_def] >> strip_tac
              >> gvs[AllCaseEqs(), oneline bind_def])
          >~ [‘Lt’]
          >- (last_x_assum $ drule_then $ qspec_then ‘t₁’ strip_assume_tac
              >> first_x_assum $ drule_then $ qspec_then ‘t₂’ strip_assume_tac
              >> gvs [res_rel_rval, dafny_to_cakeml_v_def]
              >> gvs [evaluate_def, do_app_def, opb_lookup_def])
          >~ [‘Plus’]
          >- (last_x_assum $ drule_then $ qspec_then ‘t₁’ strip_assume_tac
              >> first_x_assum $ drule_then $ qspec_then ‘t₂’ strip_assume_tac
              >> Cases_on ‘vl’ >> Cases_on ‘vr’
              >> gvs [do_bop_def, dafny_to_cakeml_v_def, res_rel_rval]
              >> gvs [evaluate_def, do_app_def, opn_lookup_def])
          >~ [‘Minus’]
          >- (last_x_assum $ drule_then $ qspec_then ‘t₁’ strip_assume_tac
              >> first_x_assum $ drule_then $ qspec_then ‘t₂’ strip_assume_tac
              >> Cases_on ‘vl’ >> Cases_on ‘vr’
              >> gvs [do_bop_def, dafny_to_cakeml_v_def, res_rel_rval]
              >> gvs [evaluate_def, do_app_def, opn_lookup_def])
          >~ [‘Times’]
          >- (last_x_assum $ drule_then $ qspec_then ‘t₁’ strip_assume_tac
              >> first_x_assum $ drule_then $ qspec_then ‘t₂’ strip_assume_tac
              >> Cases_on ‘vl’ >> Cases_on ‘vr’
              >> gvs [do_bop_def, dafny_to_cakeml_v_def, res_rel_rval]
              >> gvs [evaluate_def, do_app_def, opn_lookup_def])
          >~ [‘And’]
          >- (Cases_on ‘vl’ >> gvs [do_lop_def]
              >> Cases_on ‘b’ >> gvs []
              (* TODO Figure out why it is swapped here *)
              >> first_x_assum $ drule_then $ qspec_then ‘t₁’ strip_assume_tac
              >> last_x_assum $ drule_then $ qspec_then ‘t₂’ strip_assume_tac
              >> gvs [res_rel_rval, dafny_to_cakeml_v_def]
              >> gvs [evaluate_def, do_log_def])
          >- (Cases_on ‘vl’ >> gvs [do_lop_def]
              >> Cases_on ‘b’ >> gvs []
              >> first_x_assum $ drule_then $ qspec_then ‘t₁’ strip_assume_tac
              >> gvs [res_rel_rval, dafny_to_cakeml_v_def]
              >> gvs [evaluate_def, do_log_def])
          >- (Cases_on ‘vl’ >> gvs [do_lop_def]
              >> Cases_on ‘b’ >> gvs []
              (* TODO Figure out why it is swapped here *)
              >> first_x_assum $ drule_then $ qspec_then ‘t₁’ strip_assume_tac
              >> last_x_assum $ drule_then $ qspec_then ‘t₂’ strip_assume_tac
              >> gvs [res_rel_rval, dafny_to_cakeml_v_def]
              >> gvs [evaluate_def, do_log_def])
          >- (Cases_on ‘vl’ >> gvs [do_lop_def]
              >> Cases_on ‘b’ >> gvs []
              >> first_x_assum $ drule_then $ qspec_then ‘t₁’ strip_assume_tac
              >> gvs [res_rel_rval, dafny_to_cakeml_v_def]
              >> gvs [evaluate_def, do_log_def])))
  >~ [‘Literal’]
  >- (Cases_on ‘l’ >> gvs [from_literal_def]
      >~ [‘BoolLiteral’]
      >- (Cases_on ‘b’ >> gvs [evaluate_exp_def, literal_to_value_def]
          >> gvs [env_rel_def, evaluate_def, do_con_check_def, build_conv_def]
          >> gvs [res_rel_def, dafny_to_cakeml_v_def,
                  Boolv_def, bool_type_num_def])
      >~ [‘IntLiteral’]
      >- (gvs [AllCaseEqs (), oneline bind_def, string_to_int_def]
          >> gvs [evaluate_exp_def, literal_to_value_def]
          >> gvs [evaluate_def, res_rel_def, dafny_to_cakeml_v_def])
      >~ [‘StringLiteral’]
      >- gvs [evaluate_exp_def, literal_to_value_def]
      >~ [‘Char’]
      >- gvs [evaluate_exp_def, literal_to_value_def]
      >~ [‘Null’]
      >- gvs [evaluate_exp_def, literal_to_value_def])
  >> gvs [evaluate_exp_def, literal_to_value_def]
QED

val _ = export_theory ();
