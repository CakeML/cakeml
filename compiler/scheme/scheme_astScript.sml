(*
  AST of Scheme
*)
open preamble;
open mlstringTheory;

val _ = new_theory "scheme_ast";

Type senv = “:(mlstring |-> num)”
Type loc = “:num”

(* This needs completing: Var, Lit, ... *)
Datatype:
  prim = SAdd | SMul | SMinus | SEqv | CallCC
       | Cons | Car | Cdr
End

Datatype:
  lit = LitPrim prim | LitNum int | LitBool bool | LitNull
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
      | Letrecstar ((mlstring # exp) list) exp
End

Datatype:
  (*Contexts for small-step operational semantics*)
  cont = ApplyK ((val # val list) option) (exp list)
       | CondK exp exp
       | BeginK (exp list) exp
       | SetK mlstring
       | LetinitK ((mlstring # val) list) mlstring ((mlstring # exp) list) exp
;
  val = Prim prim | SNum int | Wrong string | SBool bool
      | Proc senv (mlstring list) (mlstring option) exp
      (*requires HOL 94eb753a85c5628f4fd0401deb4b7e2972a8eb25*)
      | Throw ((senv # cont) list)
      | PairP loc
      | Null
End

Definition lit_to_val_def:
  lit_to_val (LitPrim p) = Prim p ∧
  lit_to_val (LitNum n) = SNum n ∧
  lit_to_val (LitBool b) = SBool b ∧
  lit_to_val (LitNull) = Null
End

Definition static_scope_def:
  static_scope env (Lit lit) = T ∧

  static_scope env (Cond c t f) = (
  static_scope env c ∧
  static_scope env t ∧
  static_scope env f) ∧

  static_scope env (Apply fn es) = (
  static_scope env fn ∧
  static_scope_list env es) ∧

  static_scope env (Begin es e) = (
  static_scope_list env es ∧
  static_scope env e) ∧

  static_scope env (Lambda xs NONE e) = (
  ALL_DISTINCT xs ∧
  static_scope (env ∪ set xs) e) ∧

  static_scope env (Lambda xs (SOME x) e) = (
  ALL_DISTINCT (x::xs) ∧
  static_scope (env ∪ set (x::xs)) e) ∧

  static_scope env (Letrec bs e) = (
  ALL_DISTINCT (MAP FST bs) ∧
  static_scope_list (env ∪ set (MAP FST bs)) (MAP SND bs) ∧
  static_scope (env ∪ set (MAP FST bs)) e) ∧

  static_scope env (Letrecstar bs e) = (
  ALL_DISTINCT (MAP FST bs) ∧
  static_scope_list (env ∪ set (MAP FST bs)) (MAP SND bs) ∧
  static_scope (env ∪ set (MAP FST bs)) e) ∧

  static_scope env (Ident x) = env x ∧

  static_scope env (Set x e) = (
  env x ∧
  static_scope env e) ∧

  (static_scope_list env [] = T) ∧
  static_scope_list env (e::es) = (static_scope env e ∧ static_scope_list env es)
Termination
  WF_REL_TAC ‘measure (λ x . case x of
    | INL(_,e) => exp_size e
    | INR(_,es) => list_size exp_size es)’
  >> conj_tac
  >> Induct_on ‘bs’
  >> gvs[list_size_def, fetch "-" "exp_size_def"]
  >> PairCases
  >> strip_tac
  >> gvs[list_size_def, fetch "-" "exp_size_def"]
  >> pop_assum $ qspec_then ‘e’ assume_tac
  >> gvs[list_size_def, fetch "-" "exp_size_def"]
End

Theorem static_scope_mono_all:
    (∀ env' e env . env ⊆ env' ∧ static_scope env e ⇒ static_scope env' e) ∧
    (∀ env' es env . env ⊆ env' ∧ static_scope_list env es ⇒ static_scope_list env' es)
Proof
  ho_match_mp_tac static_scope_ind
  >> rpt strip_tac
  >> simp[Once static_scope_def]
  >> gvs[Once static_scope_def]
  >> rpt (last_x_assum $ drule_at_then (Pos last) assume_tac)
  >> simp[]
  >> gvs[SUBSET_DEF, SPECIFICATION]
QED

Theorem static_scope_mono = cj 1 static_scope_mono_all;

Theorem every_static_scope[simp]:
  ∀ env . static_scope_list env = EVERY (static_scope env)
Proof
  gen_tac
  >> irule EQ_EXT
  >> Induct
  >> simp[static_scope_def]
QED

val _ = export_theory();
