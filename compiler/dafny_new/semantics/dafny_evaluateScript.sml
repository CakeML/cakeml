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
  fix_clock s x = (s1, res) ==> s1.clock <= s.clock
Proof
  Cases_on ‘x’ \\ rw[fix_clock_def] \\ gvs[]
QED

Definition dec_clock_def:
  dec_clock s = (s with clock := s.clock − 1)
End

Definition evaluate_ann_def[nocompute]:
  evaluate_exp st env (BinaryExp bop e₀ e₁) =
  (case fix_clock st (evaluate_exp st env e₀) of
   | (st', Rval v₀) =>
     (case try_sc bop v₀ of
      | SOME v => (st', Rval v)
      | NONE =>
        (case evaluate_exp st' env e₁ of
         | (st'', Rval v₁) =>
           (case do_bop bop v₀ v₁ of
            | SOME res => (st'', Rval res)
            | NONE => (st'', Rerr Rtype_error))
         | r => r))
   | r => r) ∧
  evaluate_exp st env (LiteralExp l) = (st, Rval (lit_to_val l))
End

val _ = export_theory ();
