(*
  Semantics of Scheme
*)
open preamble;
open mlstringTheory;
open scheme_astTheory;

val _ = new_theory "scheme_semantics";

Datatype:
  (*Contexts for small-step operational semantics*)
  cont = ApplyK (((*'a*) val # (*'a*) val list) option) ('a list)
       | CondK 'a 'a
       | LetK ((mlstring # (*'a*) val) list) mlstring ((mlstring # 'a) list) 'a
       | InLetK ((mlstring # (*'a*) val) list)
       | BeginK ('a list)
End

Definition sadd_def:
  sadd vcons _ [] n = vcons $ SNum n ∧
  sadd vcons excons (SNum m :: xs) n = sadd vcons excons xs (m + n) ∧
  sadd _ excons (_ :: xs) _ = excons $ strlit "Arguments to + must be numbers"
End

Definition smul_def:
  smul vcons _ [] n = vcons $ SNum n ∧
  smul vcons excons (SNum m :: xs) n = smul vcons excons xs (m * n) ∧
  smul _ excons (_ :: xs) _ = excons $ strlit "Arguments to * must be numbers"
End

Definition sminus_def:
  sminus [] = Exception $ strlit "Arity mismatch" ∧
  sminus (SNum n :: xs) = (case sadd Val Exception xs 0 of
  | Val (SNum m) => Val (SNum (n - m))
  | e => e) ∧
  sminus _ = Exception $ strlit "Arguments to - must be numbers"
End

Definition seqv_def:
  seqv [v1; v2] = (if v1 = v2 then Val $ SBool T else Val $ SBool F) ∧
  seqv _ = Exception $ strlit "Arity mismatch"
End

(*
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
*)

Definition parameterize_def:
  parameterize _ env ks env' [] NONE e [] = (env', InLetK env :: ks, e) ∧
  parameterize _ env ks env' [] (SOME l) e xs = ((l, SList xs)::env', InLetK env :: ks, e) ∧
  parameterize excons env ks env' (p::ps) lp e (x::xs) = parameterize excons env ks ((p, x)::env') ps lp e xs ∧
  parameterize excons env ks _ _ _ _ _ = (env, ks, excons $ strlit "Wrong number of arguments")
End

Definition application_def:
  application vcons excons env ks (Prim p) xs = (case p of
  | SAdd => (env, ks, sadd vcons excons xs 0)
  | SMul => (env, ks, smul vcons excons xs 1)
  | SMinus => (env, ks, sminus xs)
  | SEqv => (env, ks, seqv xs)) ∧
  (*application _ excons env ks (Proc env' ps lp e) xs =
    parameterize excons env ks env' ps lp e xs ∧*)
  application _ excons env ks _ _ = (env, ks, excons $ strlit "Not a procedure")
End

Definition return_def:
  return vcons _ (env, [], v) = (env, [], vcons v) ∧

  return vcons excons (env, ApplyK NONE eargs :: ks, v) = (case eargs of
  | [] => application vcons excons env ks v []
  | e::es => (env, ApplyK (SOME (v, [])) es :: ks, e)) ∧
  return vcons excons (env, ApplyK (SOME (vfn, vargs)) eargs :: ks, v) = (case eargs of
  | [] => application vcons excons env ks vfn (REVERSE $ v::vargs)
  | e::es => (env, ApplyK (SOME (vfn, v::vargs)) es :: ks, e)) ∧

  return _ _ (env, CondK t f :: ks, v) = (if v = (SBool F)
    then (env, ks, f) else (env, ks, t)) ∧

  return _ _ (env, LetK env' i is e :: ks, v) = (case is of
  | [] => ((i, v)::env', InLetK env :: ks, e)
  | (i', e')::is' => (env, LetK ((i, v)::env') i' is' e :: ks, e')) ∧

  return vcons _ (env, InLetK env' :: ks, v) = (env', ks, vcons v) ∧
  return vcons _ (env, BeginK es :: ks, v) = case es of
  | [] => (env, ks, vcons v)
  | e::es' => (env, BeginK es' :: ks, e)
End

Definition unwind_def:
  unwind excons env [] ex = (env, [], excons ex) ∧
  unwind excons env (k::ks) ex = unwind excons env ks ex
End

Definition step_def:
  step (env, ks, Val v) = return Val Exception (env, ks, v) ∧
  step (env, ks, Apply fn args) = (env, ApplyK NONE args :: ks, fn) ∧
  step (env, ks, Cond c t f) = (env, CondK t f :: ks, c) ∧
  step (env, ks, Ident s) = (let v' = case FIND ($= s o FST) env of
    | NONE => Wrong "Unrecognised identifier"
    | SOME (_, v) => v
    in (env, ks, Val v')) ∧
  step (env, ks, SLet is e) = (case is of
  | [] => (env, ks, e)
  | (i, e')::is' => (env, LetK env i is' e :: ks, e')) ∧
  (*step (env, ks, Lambda ps lp e) = (env, ks, Val $ Proc env ps lp e) ∧*)
  step (env, ks, Begin e es) = (env, BeginK es :: ks, e) ∧

  step (env, ks, Exception ex) = unwind Exception env ks ex
End

Definition steps_def:
  steps (n:num) t = if n = 0 then t
    else steps (n - 1) $ step t
End

(*
  EVAL “semantics (Val (SNum 3))”
  EVAL “semantics (Apply (Val (Prim SMul)) [Val (SNum 2); Val (SNum 4)])”
  EVAL “steps 4 ([], [], Apply (Val (Prim SMinus)) [Val (SNum 2); Val (SNum 4)])”
  EVAL “steps 4 ([], [], Apply (Val (SNum 7)) [Val (SNum 2); Val (SNum 4)])”
  EVAL “steps 6 ([], [InLetK []], Apply (Val (Prim SMul)) [Val (SNum 2); Val (Prim SAdd)])”
  EVAL “steps 2 ([], [], Cond (Val (SBool F)) (Val (SNum 2)) (Val (SNum 4)))”
  EVAL “steps 4 ([], [], SLet [(strlit "x", Val $ SNum 42)] (Ident $ strlit "x"))”
  EVAL “steps 6 ([], [], Apply (Lambda [] (SOME $ strlit "x") (Ident $ strlit "x")) [Val $ SNum 4])”
  EVAL “steps 3 ([], [], Begin (Val $ SNum 1) [Val $ SNum 2])”
  EVAL “steps 10 ([], [], Apply (Val $ Prim SEqv) [Val $ SNum 3; Val $ SNum 2])”
*)

val _ = export_theory();