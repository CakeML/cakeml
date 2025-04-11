(*
  AST of Scheme
*)
open preamble;
open mlstringTheory;

val _ = new_theory "scheme_ast";

Type senv = “:(mlstring |-> num)”

(* This needs completing: Var, Lit, ... *)
Datatype:
  prim = SAdd | SMul | SMinus | SEqv | CallCC
End

Datatype:
  lit = LitPrim prim | LitNum int | LitBool bool
End

Datatype:
  exp = (*Print mlstring
      |*) Apply exp (exp list)
      | Lit lit
      | Cond exp exp exp
      | Ident mlstring
      | Lambda (mlstring list) (mlstring option) exp
      | Begin (exp list) exp
      | Set mlstring exp
      | Letrec ((mlstring # exp) list) exp
End

Datatype:
  (*Contexts for small-step operational semantics*)
  cont = ApplyK ((val # val list) option) (exp list)
       | CondK exp exp
       | BeginK (exp list) exp
       | SetK mlstring
;
  val = Prim prim | SNum int | Wrong string | SBool bool
      | SList (val list)
      | Proc senv (mlstring list) (mlstring option) exp
      (*requires HOL 94eb753a85c5628f4fd0401deb4b7e2972a8eb25*)
      | Throw ((senv # cont) list)
End

Definition lit_to_val_def:
  lit_to_val (LitPrim p) = Prim p ∧
  lit_to_val (LitNum n) = SNum n ∧
  lit_to_val (LitBool b) = SBool b
End

Inductive static_scope:
[~Lit:]
  static_scope env (Lit lit)
[~Cond:]
  static_scope env c ∧
  static_scope env t ∧
  static_scope env f
  ⇒
  static_scope env (Cond c t f)
[~Apply:]
  static_scope env fn ∧
  EVERY (static_scope env) es
  ⇒
  static_scope env (Apply fn es)
[~Begin:]
  EVERY (static_scope env) es ∧
  static_scope env e
  ⇒
  static_scope env (Begin es e)
[~Lambda_NONE:]
  ALL_DISTINCT xs ∧
  static_scope (env ∪ set xs) e
  ⇒
  static_scope env (Lambda xs NONE e)
[~Lambda_SOME:]
  ALL_DISTINCT (x::xs) ∧
  static_scope (env ∪ set (x::xs)) e
  ⇒
  static_scope env (Lambda xs (SOME x) e)
[~Letrec:]
  ALL_DISTINCT (MAP FST bs) ∧
  EVERY (static_scope (env ∪ set (MAP FST bs))) (MAP SND bs) ∧
  static_scope (env ∪ set (MAP FST bs)) e
  ⇒
  static_scope env (Letrec bs e)
[~Ident:]
  env x
  ⇒
  static_scope env (Ident x)
[~Set:]
  env x ∧
  static_scope env e
  ⇒
  static_scope env (Set x e)
End

Definition exp_rec_def:
  exp_rec (Lit l) = 1 ∧
  exp_rec (Cond c t f) = exp_rec c + exp_rec t + exp_rec f ∧
  exp_rec (Apply fn es) = exp_rec fn + SUM (MAP exp_rec es) ∧
  exp_rec (Begin es e) = exp_rec e + SUM (MAP exp_rec es) ∧
  exp_rec (Lambda xs xp e) = exp_rec e ∧
  exp_rec (Letrec bs e) = exp_rec e + SUM (MAP (exp_rec o SND) bs)∧
  exp_rec (Ident x) = 1 ∧
  exp_rec (Set x e) =  exp_rec e
Termination
  WF_REL_TAC ‘measure exp_size’
End

Theorem static_scope_mono:
  ∀ env e env' .
    env ⊆ env' ∧ static_scope env e ⇒ static_scope env' e
Proof
  simp[Once CONJ_COMM]
  >> simp[GSYM AND_IMP_INTRO]
  >> simp[GSYM PULL_FORALL]
  >> ho_match_mp_tac static_scope_ind
  >> rpt strip_tac
  >~ [‘Letrec bs e’] >- (
    simp[Once static_scope_cases]
    >> ‘env ∪ set (MAP FST bs) ⊆ env' ∪ set (MAP FST bs)’
      by gvs[SUBSET_UNION_ABSORPTION, UNION_ASSOC]
    >> qpat_x_assum ‘∀ _._ ⇒ _’ $ irule_at (Pos last)
    >> simp[]
    >> irule EVERY_MONOTONIC
    >> qpat_x_assum ‘EVERY _ _’ $ irule_at (Pos last)
    >> rpt strip_tac
    >> gvs[]
  )
  >> simp[Once static_scope_cases]
  >> gvs[SUBSET_DEF, SPECIFICATION]
  >> irule EVERY_MONOTONIC
  >> qpat_assum ‘EVERY _ _’ $ irule_at (Pos last)
  >> gvs[]
QED

val _ = export_theory();

(*
  EVAL “static_scoping_check {} (
    Apply (
      Lambda [strlit "f"; strlit "x"] NONE (Begin (
        Apply (Ident $ strlit "f"
        ) [Val $ SNum 1]
      ) [
        Ident $ strlit "x"
      ])
    ) [
      Lambda [strlit "y"] NONE (Begin (
        Set (strlit "x") (Val $ SNum 5)
      ) [
        Apply (Val $ Prim SAdd) [
          Ident $ strlit "y";
          Ident $ strlit "x"
        ]
      ]);
      Val $ SNum 4
    ]
  )”
*)