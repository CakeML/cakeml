(*
  AST of Scheme
*)
open preamble;
open mlstringTheory;

val _ = new_theory "scheme_ast";

Type senv = “:(mlstring |-> num)”

(* This needs completing: Var, Lit, ... *)
Datatype:
  prim = SAdd | SMul | SMinus | SEqv
End

Datatype:
  val = Prim prim | SNum int | Wrong string | SBool bool
      | SList (val list)
      | Proc senv (mlstring list) (mlstring option) exp
;
  exp = Print mlstring
      | Apply exp (exp list)
      | Val (val)
      | Cond exp exp exp
      | Ident mlstring
      | Lambda (mlstring list) (mlstring option) exp
      | Exception mlstring
      | Begin exp (exp list)
      | Set mlstring exp
      | Letrec ((mlstring # exp) list) exp
End

Definition static_scoping_check_def:
  (static_scoping_check env (Cond c t f) ⇔
    static_scoping_check env c ∧
    static_scoping_check env t ∧
    static_scoping_check env f) ∧
  (static_scoping_check env (Apply e args) ⇔
    static_scoping_check env e ∧
    EVERY (static_scoping_check env) args) ∧
  (static_scoping_check env (Set _ e) ⇔ static_scoping_check env e) ∧
  (static_scoping_check env (Begin e es) ⇔
    static_scoping_check env e ∧
    EVERY (static_scoping_check env) es) ∧
  (static_scoping_check env (Lambda xs xp e) ⇔ let xs' = case xp of
    | NONE => xs
    | SOME x => x::xs
    in ALL_DISTINCT xs' ∧ static_scoping_check (env ∪ set xs') e) ∧
  (static_scoping_check env (Letrec xes e) ⇔ let xs = MAP FST xes
    in ALL_DISTINCT xs ∧ let env' = env ∪ set xs
    in static_scoping_check env' e ∧
       EVERY (static_scoping_check env') (MAP SND xes)) ∧
  (static_scoping_check env (Ident x) ⇔ env x) ∧
  (static_scoping_check _ _ ⇔ T)
Termination
  WF_REL_TAC ‘measure $ exp_size o SND’
  >> Induct_on ‘xes’ >- (rw[])
  >> Cases_on ‘h’
  >> simp[definition "val_size_def", list_size_def, snd (TypeBase.size_of “:'a # 'b”)]
  >> rpt strip_tac >- (rw[])
  >> last_x_assum $ qspecl_then [‘e’, ‘a’] $ imp_res_tac
  >> first_x_assum $ qspec_then ‘e’ $ assume_tac
  >> rw[]
End

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