(*
  This compiler phase removes all Tick expressions from flatLang
  programs. Ticks are introduced by source_to_flat when it inlines
  calls to primitive wrappers. They have no observable behaviour.
*)
Theory flat_ticks
Ancestors
  flatLang
Libs
  preamble

Definition remove_ticks_exp_def:
  (remove_ticks_exp (Tick t e) = remove_ticks_exp e) ∧
  (remove_ticks_exp (Raise t e) = Raise t (remove_ticks_exp e)) ∧
  (remove_ticks_exp (Handle t e pes) =
     Handle t (remove_ticks_exp e) (remove_ticks_pes pes)) ∧
  (remove_ticks_exp (Lit t l) = Lit t l) ∧
  (remove_ticks_exp (Con t n es) = Con t n (remove_ticks_exps es)) ∧
  (remove_ticks_exp (Var_local t v) = Var_local t v) ∧
  (remove_ticks_exp (Fun t v e) = Fun t v (remove_ticks_exp e)) ∧
  (remove_ticks_exp (App t op es) = App t op (remove_ticks_exps es)) ∧
  (remove_ticks_exp (If t e1 e2 e3) =
     If t (remove_ticks_exp e1) (remove_ticks_exp e2) (remove_ticks_exp e3)) ∧
  (remove_ticks_exp (Mat t e pes) =
     Mat t (remove_ticks_exp e) (remove_ticks_pes pes)) ∧
  (remove_ticks_exp (Let t n e1 e2) =
     Let t n (remove_ticks_exp e1) (remove_ticks_exp e2)) ∧
  (remove_ticks_exp (Letrec t funs e) =
     Letrec t (remove_ticks_funs funs) (remove_ticks_exp e)) ∧
  (remove_ticks_exps [] = []) ∧
  (remove_ticks_exps (e::es) = remove_ticks_exp e :: remove_ticks_exps es) ∧
  (remove_ticks_pes [] = []) ∧
  (remove_ticks_pes ((p,e)::pes) = (p, remove_ticks_exp e) :: remove_ticks_pes pes) ∧
  (remove_ticks_funs [] = []) ∧
  (remove_ticks_funs ((f,x,e)::funs) =
     (f, x, remove_ticks_exp e) :: remove_ticks_funs funs)
End

Definition remove_ticks_decs_def:
  remove_ticks_decs (ds:flatLang$exp list) = remove_ticks_exps ds
End

Theorem remove_ticks_exps_MAP:
  (∀es. remove_ticks_exps es = MAP remove_ticks_exp es) ∧
  (∀pes. remove_ticks_pes pes = MAP (λ(p,e). (p, remove_ticks_exp e)) pes) ∧
  (∀funs. remove_ticks_funs funs =
          MAP (λ(f,x,e). (f, x, remove_ticks_exp e)) funs)
Proof
  rpt conj_tac \\ Induct \\ TRY PairCases \\ rw [remove_ticks_exp_def]
QED
