(*
  Defines functional big-step semantics for Dafny.
*)

open preamble
open dafny_semanticPrimitivesTheory

val _ = new_theory "dafny_evaluate";

(* The following three definitions/theorems were adapted from
   semantics/evaluateScript.sml *)
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

Definition evaluate_exp_ann_def[nocompute]:
  (* TODO Instead of pushing to the heap, get information from Dafny whether
     a variable is mutable (and then put it on the heap), or not (and then
     put it into the environment? *)
  evaluate_exp st env (FunctionCall name args) =
  (case FLOOKUP env.functions name of
   | NONE => (st, Rerr Rtype_error)
   | SOME (param_names, body) =>
     (case fix_clock st (evaluate_exps st env args) of
      | (st', Rerr err) => (st', Rerr err)
      | (st', Rval vs) =>
        (case push_params st' param_names vs of
         | NONE => (st', Rerr Rtype_error)
         | SOME st'' =>
             if st''.clock = 0 then
               (st'', Rerr Rtimeout_error)
             else
               (case evaluate_exp (dec_clock st'') env body of
                | (st₃, Rerr err) => (st₃, Rerr err)
                | (st₃, Rval v) =>
                  (case pop_params st₃ of
                   | NONE => (st₃, Rerr Rtype_error)
                   | SOME st₄ => (st₄, Rval v)))))) ∧
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
  (* NOTE For now, we assume that forall is only used as ghost code *)
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
  >> gvs [try_sc_def, push_params_def, dec_clock_def,
          oneline do_cond_def, AllCaseEqs ()]
End

val _ = export_theory ();
