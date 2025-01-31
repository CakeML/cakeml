(*
  Semantics of Scheme
*)
open preamble;
open mlstringTheory;
open scheme_astTheory;

val _ = new_theory "scheme_semantics";

Datatype:
  cont = ApplyK ((val # val list) option) (exp list)
       | CondK exp exp
       | LetK ((mlstring # val) list) mlstring ((mlstring # exp) list) exp
       | InLetK ((mlstring # val) list)
End

Definition sadd_def:
  sadd [] n = SNum n ∧
  sadd (SNum m :: xs) n = sadd xs (m + n) ∧
  sadd (_ :: xs) _ = Wrong "Arguments to + must be numbers"
End

Definition smul_def:
  smul [] n = SNum n ∧
  smul (SNum m :: xs) n = smul xs (m * n) ∧
  smul (_ :: xs) _ = Wrong "Arguments to * must be numbers"
End

Definition strict_def:
  strict (Prim SAdd) xs = sadd xs 0 ∧
  strict (Prim SMul) xs = smul xs 1
End

Definition semantics_def:
  semantics (Val v) = v ∧
  semantics (Apply fn args) = strict (semantics fn) (MAP semantics args)
Termination
  WF_REL_TAC ‘measure exp_size’
End

Definition parameterize_def:
  parameterize env ks env' [] NONE e [] = (env', InLetK env :: ks, e) ∧
  parameterize env ks env' [] (SOME l) e xs = ((l, SList xs)::env', InLetK env :: ks, e) ∧
  parameterize env ks env' (p::ps) lp e (x::xs) = parameterize env ks ((p, x)::env') ps lp e xs ∧
  parameterize env ks _ _ _ _ _ = (env, ks, Val $ Exception $ strlit "Wrong number of arguments")
End

Definition application_def:
  application env ks (Prim p) xs = (case p of
  | SAdd => (env, ks, Val $ sadd xs 0)
  | SMul => (env, ks, Val $ smul xs 1)) ∧
  application env ks (Proc env' ps lp e) xs =
    parameterize env ks env' ps lp e xs
End

Definition return_def:
  return (env, [], v) = (env, [], Val v) ∧

  return (env, ApplyK NONE eargs :: ks, v) = (case eargs of
  | [] => application env ks v []
  | e::es => (env, ApplyK (SOME (v, [])) es :: ks, e)) ∧
  return (env, ApplyK (SOME (vfn, vargs)) eargs :: ks, v) = (case eargs of
  | [] => application env ks vfn (REVERSE $ v::vargs)
  | e::es => (env, ApplyK (SOME (vfn, v::vargs)) es :: ks, e)) ∧

  return (env, CondK t f :: ks, v) = (if v = (SBool F)
    then (env, ks, f) else (env, ks, t)) ∧

  return (env, LetK env' i is e :: ks, v) = (case is of
  | [] => ((i, v)::env', InLetK env :: ks, e)
  | (i', e')::is' => (env, LetK ((i, v)::env') i' is' e :: ks, e')) ∧

  return (env, InLetK env' :: ks, v) = (env', ks, Val v)
End

Definition step_def:
  step (env, ks, Val v) = return (env, ks, v) ∧
  step (env, ks, Apply fn args) = (env, ApplyK NONE args :: ks, fn) ∧
  step (env, ks, Cond c t f) = (env, CondK t f :: ks, c) ∧
  step (env, ks, Ident s) = (let v' = case FIND ($= s o FST) env of
    | NONE => Wrong "Unrecognised identifier"
    | SOME (_, v) => v
    in (env, ks, Val v')) ∧
  step (env, ks, SLet is e) = (case is of
  | [] => (env, ks, e)
  | (i, e')::is' => (env, LetK env i is' e :: ks, e')) ∧
  step (env, ks, Lambda ps lp e) = (env, ks, Val $ Proc env ps lp e)
End

Definition steps_def:
  steps (n:num) t = if n = 0 then t
    else steps (n - 1) $ step t
End

(*EVAL “semantics (Val (SNum 3))”*)
(*EVAL “semantics (Apply (Val (Prim SMul)) [Val (SNum 2); Val (SNum 4)])”*)
(*EVAL “steps 4 ([], [], Apply (Val (Prim SMul)) [Val (SNum 2); Val (SNum 4)])”*)
(*EVAL “steps 2 ([], [], Cond (Val (SBool F)) (Val (SNum 2)) (Val (SNum 4)))”*)
(*EVAL “steps 4 ([], [], SLet [(strlit "x", Val $ SNum 42)] (Ident $ strlit "x"))”*)
(*EVAL “steps 6 ([], [], Apply (Lambda [] (SOME $ strlit "x") (Ident $ strlit "x")) [Val $ SNum 4])”*)

val _ = export_theory();