(*
  Defines functional big-step semantics for Dafny.
*)

open preamble
open dafny_semanticPrimitivesTheory

val _ = new_theory "dafny_evaluate";

(* Related papers:
   "Functional Big-step Semantics", https://cakeml.org/esop16.pdf
   "Clocked Definitions in HOL", https://arxiv.org/pdf/1803.03417 *)

(* Helpers for clocked definition of semantics, which were adapted from
   semantics/evaluateScript.sml. *)

Definition fix_clock_def:
  fix_clock s (s', res) =
  (s' with clock := if s'.clock ≤ s.clock then s'.clock else s.clock, res)
End

Triviality fix_clock_IMP:
  fix_clock s x = (s', res) ⇒ s'.clock ≤ s.clock
Proof
  Cases_on ‘x’ >> rw[fix_clock_def] >> gvs[]
QED

Definition dec_clock_def:
  dec_clock s = (s with clock := s.clock − 1)
End

(* Semantics for expressions *)

Definition evaluate_exp_ann_def[nocompute]:
  evaluate_exp st env (FunctionCall name args) =
  (case FLOOKUP env.functions name of
   | NONE => (st, Rerr Rtype_error)
   | SOME (param_names, body) =>
     (case fix_clock st (evaluate_exps st env args) of
      | (st', Rerr err) => (st', Rerr err)
      | (st', Rval vs) =>
        (case set_up_call st' param_names vs of
         | NONE => (st', Rerr Rtype_error)
         | SOME (old_locals, st'') =>
           if st''.clock = 0 then
             (st'', Rerr Rtimeout_error)
           else
             (case evaluate_exp (dec_clock st'') env body of
              | (st₃, Rerr err) => (st₃, Rerr err)
              | (st₃, Rval v) => (restore_locals st₃ old_locals, Rval v))))) ∧
  evaluate_exp st env (IdentifierExp name _) =
  (case read_local st name of
   | NONE => (st, Rerr Rtype_error)
   | SOME v => (st, Rval v)) ∧
  evaluate_exp st env (BinaryExp bop e₀ e₁) =
  (case fix_clock st (evaluate_exp st env e₀) of
   | (st', Rerr err) => (st', Rerr err)
   | (st', Rval v₀) =>
     (case try_sc bop v₀ of
      | SOME v => (st', Rval v)
      | NONE =>
        (case evaluate_exp st' env e₁ of
         | (st'', Rerr err) => (st'', Rerr err)
         | (st'', Rval v₁) =>
           (case do_bop bop v₀ v₁ of
            | SOME res => (st'', Rval res)
            | NONE => (st'', Rerr Rtype_error))))) ∧
  evaluate_exp st env (LiteralExp l) = (st, Rval (lit_to_val l)) ∧
  evaluate_exp st env (ArrayLen e) =
  (case evaluate_exp st env e of
   | (st', Rerr err) => (st', Rerr err)
   | (st', Rval v) =>
     (case get_array_len v of
      | NONE => (st', Rerr Rtype_error)
      | SOME len => (st', Rval (IntV &len)))) ∧
  evaluate_exp st env (ArraySelect arr idx) =
  (case fix_clock st (evaluate_exp st env arr) of
   | (st', Rerr err) => (st', Rerr err)
   | (st', Rval arr) =>
     (case fix_clock st' (evaluate_exp st' env idx) of
      | (st'', Rerr err) => (st'', Rerr err)
      | (st'', Rval idx) =>
        (case index_array st'' arr idx of
         | NONE => (st'', Rerr Rtype_error)
         | SOME v => (st'', Rval v)))) ∧
  evaluate_exp st env (ITE tst thn els) =
  (case fix_clock st (evaluate_exp st env tst) of
   | (st', Rerr err) => (st', Rerr err)
   | (st', Rval v) =>
     (case do_cond v thn els of
      | NONE => (st', Rerr Rtype_error)
      | SOME branch => evaluate_exp st' env branch)) ∧
  (* TODO If ¬env.is_running, try to express ForallExp in logic somehow? *)
  evaluate_exp st env (ForallExp _ _) = (st, Rerr Rtype_error) ∧
  evaluate_exps st env [] = (st, Rval []) ∧
  evaluate_exps st env (e::es) =
  (case fix_clock st (evaluate_exp st env e) of
   | (st', Rerr err) => (st', Rerr err)
   | (st', Rval v) =>
     (case evaluate_exps st' env es of
      | (st'', Rerr err) => (st'', Rerr err)
      | (st'', Rval vs) => (st'', Rval (v::vs))))
Termination
  wf_rel_tac ‘inv_image ($< LEX $<)
              (λx. case x of
                   | INL (s, _, exp) =>
                       (s.clock, expression_size exp)
                   | INR (s, _, exps) =>
                       (s.clock, list_size expression_size exps))’
  >> rpt strip_tac
  >> imp_res_tac fix_clock_IMP
  >> gvs [try_sc_def, dec_clock_def, set_up_call_def,
          oneline do_cond_def, AllCaseEqs ()]
End

Theorem evaluate_exp_clock:
  (∀s₁ env e s₂ r.
     evaluate_exp s₁ env e = (s₂, r) ⇒ s₂.clock ≤ s₁.clock) ∧
  (∀s₁ env es s₂ r.
     evaluate_exps s₁ env es = (s₂, r) ⇒ s₂.clock ≤ s₁.clock)
Proof
  ho_match_mp_tac evaluate_exp_ann_ind
  >> rpt strip_tac
  >> pop_assum mp_tac >> simp [Once evaluate_exp_ann_def] >> strip_tac
  >> gvs [AllCaseEqs (), dec_clock_def, fix_clock_def, restore_locals_def]
  >> EVERY (map imp_res_tac
                [set_up_call_clock, restore_locals_clock, fix_clock_IMP])
  >> gvs[]
QED

Theorem fix_clock_evaluate_exp:
  (fix_clock s₁ (evaluate_exp s₁ env exp) = evaluate_exp s₁ env exp) ∧
  (fix_clock s₁ (evaluate_exps s₁ env exps) = evaluate_exps s₁ env exps)
Proof
  Cases_on ‘evaluate_exp s₁ env exp’ >> Cases_on ‘evaluate_exps s₁ env exps’
  >> imp_res_tac evaluate_exp_clock
  >> gvs [fix_clock_def, state_component_equality]
QED

Theorem evaluate_exp_def[compute] =
  REWRITE_RULE [fix_clock_evaluate_exp] evaluate_exp_ann_def

Theorem evaluate_exp_ind =
  REWRITE_RULE [fix_clock_evaluate_exp] evaluate_exp_ann_ind

(* Semantics for statements *)

(* Also defines the semantics for rhs_exp, due to mutual recursion with
   statements *)
Definition evaluate_stmt_ann_def[nocompute]:
  evaluate_stmt st env Skip = (st, Rcont) ∧
  evaluate_stmt st env (Then stmt₁ stmt₂) =
  (case fix_clock st (evaluate_stmt st env stmt₁) of
   | (st', Rstop stp) => (st', Rstop stp)
   | (st', Rcont) => evaluate_stmt st env stmt₂) ∧
  (* TODO Assign *)
  evaluate_stmt st env (If tst thn els) =
  (case fix_clock st (evaluate_exp st env tst) of
   | (st', Rerr err) => (st', Rstop (Serr err))
   | (st', Rval tst) =>
     (case do_cond tst thn els of
      | NONE => (st', Rstop (Serr Rtype_error))
      | SOME branch => evaluate_stmt st' env branch)) ∧
  (* TODO VarDecl *)
  evaluate_stmt st env (While guard invs decrs mods body) =
  (case fix_clock st (evaluate_exp st env guard) of
   | (st', Rerr err) => (st', Rstop (Serr err))
   | (st', Rval guard_v) =>
     if guard_v = BoolV F then
       (st', Rcont)
     else if guard_v = BoolV T then
       (case fix_clock st' (evaluate_stmt st' env body) of
        | (st'', Rstop stp) => (st'', Rstop stp)
        | (st'', Rcont) =>
          if st''.clock = 0 then
            (st'', Rstop (Serr Rtimeout_error))
          else
            evaluate_stmt (dec_clock st'') env
                          (While guard invs decrs mods body))
     else
       (st', Rstop (Serr Rtype_error))) ∧
  (* TODO Print *)
  evaluate_stmt st env (Return rhss) =
  (case evaluate_rhs_exps st env rhss of
   | (st', Rerr err) => (st', Rstop (Serr err))
   | (st', Rval vs) => (st', Rstop (Sret vs))) ∧
  (* TODO Assert - How should we model ghost code in evaluate? *)
  evaluate_rhs_exp st env (MethodCall name args) =
  (case FLOOKUP env.methods name of
   | NONE => (st, Rerr Rtype_error)
   | SOME (param_names, body) =>
     (case fix_clock st (evaluate_exps st env args) of
      | (st', Rerr err) => (st', Rerr err)
      | (st', Rval vs) =>
        (case set_up_call st' param_names vs of
         | NONE => (st', Rerr Rtype_error)
         | SOME (old_locals, st'') =>
           if st''.clock = 0 then
             (st'', Rerr Rtimeout_error)
           else
             (case evaluate_stmt (dec_clock st'') env body of
              | (st₃, Rcont) => (st₃, Rerr Rtype_error)
              | (st₃, Rstop (Serr err)) => (st₃, Rerr err)
              | (st₃, Rstop (Sret vs)) =>
                  (restore_locals st₃ old_locals, Rval vs))))) ∧
  evaluate_rhs_exps st env [] = (st, Rval []) ∧
  evaluate_rhs_exps st env (e::es) =
  (case fix_clock st (evaluate_rhs_exp st env e) of
   | (st', Rerr err) => (st', Rerr err)
   | (st', Rval vs) =>
     (case evaluate_rhs_exps st' env es of
      | (st'', Rerr err) => (st'', Rerr err)
      | (st'', Rval vs') => (st'', Rval (vs ++ vs'))))
Termination
  cheat
End

val _ = export_theory ();
