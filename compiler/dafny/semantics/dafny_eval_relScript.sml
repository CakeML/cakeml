(*
  Proves relational big-step-style theorems about Dafny semantics
*)

open preamble
open dafny_astTheory
open dafny_semanticPrimitivesTheory
open dafnyPropsTheory
open dafny_evaluateTheory
open dafny_evaluatePropsTheory

val _ = new_theory "dafny_eval_rel";

Overload True = “Lit (BoolL T)”;
Overload False = “Lit (BoolL F)”;

Overload "imp" = “BinOp Imp”

Definition eval_exp_def:
  eval_exp st env e v ⇔
    ∃ck1 ck2.
      evaluate_exp (st with clock := ck1) env e =
        (st with clock := ck2, Rval v)
End

Definition eval_stmt_def:
  eval_stmt st env body st' ret =
    ∃ck1 ck2.
      evaluate_stmt (st with clock := ck1) env body =
        (st' with clock := ck2, ret)
End

Definition eval_true_def:
  eval_true st env e ⇔ eval_exp st env e (BoolV T)
End

Definition valid_def:
  valid e = ∀st env. eval_true st env e
End

Overload "⊢" = “valid”;

Definition conj_def:
  conj [] = Lit (BoolL T) ∧
  conj [x] = x ∧
  conj (x::xs) = BinOp And (x) (conj xs)
End

(* simp *)

Theorem eval_true_true[simp]:
  eval_true st env True
Proof
  gvs [eval_true_def, eval_exp_def, evaluate_exp_def]
  \\ qexistsl [‘0’, ‘0’] \\ simp []
QED

Theorem conj_empty[simp]:
  conj [] = True
Proof
  rewrite_tac [conj_def]
QED

(* *** *)

Theorem eval_true_mp:
  eval_true st env (imp p q) ∧ eval_true st env p ⇒ eval_true st env q
Proof
  gvs [eval_true_def, eval_exp_def]
  \\ gvs [PULL_EXISTS]
  \\ qx_genl_tac [‘ck₁’, ‘ck₂’, ‘ck₃’, ‘ck₄’]
  \\ rpt strip_tac
  \\ dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₁’ mp_tac
  \\ dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₃’ mp_tac
  \\ rpt strip_tac
  \\ gvs [evaluate_exp_def, do_sc_def, do_bop_def, AllCaseEqs()]
  \\ first_assum $ irule_at $ Pos hd
QED

Theorem eval_true_cons:
  eval_true st env (conj (x::xs)) =
  (eval_true st env x ∧ eval_true st env (conj xs))
Proof
  namedCases_on ‘xs’ ["", "x₁ xs₁"] \\ simp [conj_def]
  \\ gvs [eval_true_def, eval_exp_def]
  \\ gvs [evaluate_exp_def, do_sc_def, PULL_EXISTS, do_bop_def, AllCaseEqs()]
  \\ iff_tac
  >- (rpt strip_tac
      \\ rev_drule (cj 1 evaluate_exp_with_clock)
      \\ rpt strip_tac \\ gvs []
      \\ last_x_assum $ irule_at (Pos hd)
      \\ last_x_assum $ irule_at (Pos hd))
  \\ disch_then $ qx_choosel_then [‘ck₁’, ‘ck₂’, ‘ck₃’, ‘ck₄’] mp_tac
  \\ rpt strip_tac
  \\ dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₂’ mp_tac
  \\ dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₃’ mp_tac
  \\ rpt strip_tac
  \\ first_assum $ irule_at $ Pos hd
  \\ first_assum $ irule_at $ Pos hd
QED

Theorem eval_true_conj_every:
  ∀xs st env. eval_true st env (conj xs) ⇔ EVERY (eval_true st env) xs
Proof
  Induct \\ simp []
  \\ qx_genl_tac [‘x’, ‘st’, ‘env’]
  \\ simp [eval_true_cons]
QED

Theorem eval_exp_evaluate_exps:
  ∀es vs st env.
    LIST_REL (eval_exp st env) es vs ⇒
    ∃ck ck₁.
      evaluate_exps (st with clock := ck) env es =
      (st with clock := ck₁, Rval vs)
Proof
  Induct >-
   (simp [evaluate_exp_def] \\ gen_tac \\ qexistsl [‘0’, ‘0’] \\ simp [])
  \\ qx_genl_tac [‘e’, ‘vs’, ‘st’, ‘env’] \\ disch_tac
  \\ namedCases_on ‘vs’ ["", "v vs₁"] \\ gvs []
  \\ simp [evaluate_exp_def]
  \\ fs [eval_exp_def]
  \\ rename
       [‘evaluate_exp (_ with clock := ck₁) _ _ = (_ with clock := ck₂, _) ’]
  \\ last_x_assum drule
  \\ disch_then $ qx_choosel_then [‘ck₃’, ‘ck₄’] assume_tac
  \\ dxrule (cj 1 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₃’ assume_tac
  \\ dxrule (cj 2 evaluate_exp_add_to_clock) \\ simp []
  \\ disch_then $ qspec_then ‘ck₂’ assume_tac
  \\ qexistsl [‘ck₁ + ck₃’, ‘ck₂ + ck₄’] \\ gvs []
QED

val _ = export_theory ();
