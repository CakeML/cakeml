(*
  Semantics of Scheme
*)
open preamble;
open mlstringTheory;
open scheme_astTheory;
open finite_mapTheory;

val _ = new_theory "scheme_semantics";

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

Definition fresh_loc_def:
  fresh_loc store l = (LENGTH store, SNOC l store)
End

Definition parameterize_def:
  parameterize _ store ks env [] NONE e [] = (store, ks, env, e) ∧
  parameterize _ store ks env [] (SOME l) e xs = (let (n, store') = fresh_loc store (SList xs)
    in (store', ks, (env |+ (l, n)), e)) ∧
  parameterize excons store ks env (p::ps) lp e (x::xs) = (let (n, store') = fresh_loc store x
    in parameterize excons store' ks (env |+ (p, n)) ps lp e xs) ∧
  parameterize excons store ks _ _ _ _ _ = (store, ks, FEMPTY, excons $ strlit "Wrong number of arguments")
End

Definition application_def:
  application vcons excons store ks env (Prim p) xs = (case p of
  | SAdd => (store, ks, env, sadd vcons excons xs 0)
  | SMul => (store, ks, env, smul vcons excons xs 1)
  | CallCC => case xs of
    | [v] => (store, (env, ApplyK (SOME (v, [])) []) :: ks, env, vcons $ Throw env ks)
    | _ => (store, ks, env, excons $ strlit "arity mismatch")) ∧
  application _ excons store ks _ (Proc env ps lp e) xs =
    parameterize excons store ks env ps lp e xs ∧
  application vcons excons store ks env (Throw env' ks') xs = (case xs of
    | [v] => (store, ks', env', vcons v)
    | _ => (store, ks, env, excons $ strlit "arity mismatch")) ∧
  application _ excons store ks env _ _ = (store, ks, env, excons $ strlit "Not a procedure")
End

Definition return_def:
  return vcons _ (store, [], env, v) = (store, [], env, vcons v) ∧

  return vcons excons (store, (env, ApplyK NONE eargs) :: ks, _, v) = (case eargs of
  | [] => application vcons excons store ks env v []
  | e::es => (store, (env, ApplyK (SOME (v, [])) es) :: ks, env, e)) ∧
  return vcons excons (store, (env, ApplyK (SOME (vfn, vargs)) eargs) :: ks, _, v) = (case eargs of
  | [] => application vcons excons store ks env vfn (REVERSE $ v::vargs)
  | e::es => (store, (env, ApplyK (SOME (vfn, v::vargs)) es) :: ks, env, e)) ∧

  return _ _ (store, (env, CondK t f) :: ks, _, v) = (if v = (SBool F)
    then (store, ks, env, f) else (store, ks, env, t)) ∧

  (*return _ _ (store, LetK store' i is e :: ks, v) = (case is of
  | [] => ((i, v)::store', InLetK store :: ks, e)
  | (i', e')::is' => (store, LetK ((i, v)::store') i' is' e :: ks, e')) ∧

  return vcons _ (store, InLetK store' :: ks, v) = (store', ks, vcons v) ∧*)
  return vcons _ (store, (env, BeginK es) :: ks, _, v) = case es of
  | [] => (store, ks, env, vcons v)
  | e::es' => (store, (env, BeginK es') :: ks, env, e)
End

Definition unwind_def:
  unwind excons store [] ex = (store, [], FEMPTY, excons ex) ∧
  unwind excons store (k::ks) ex = unwind excons store ks ex
End

Definition step_def:
  step (store, ks, env, Val v) = return Val Exception (store, ks, env, v) ∧
  step (store, ks, env, Apply fn args) = (store, (env, ApplyK NONE args) :: ks, env, fn) ∧
  step (store, ks, env, Cond c t f) = (store, (env, CondK t f) :: ks, env, c) ∧
  step (store, ks, env, Ident s) = (let v = case FLOOKUP env s of
    | NONE => Exception $ strlit "Unrecognised identifier"
    | SOME n => Val $ EL n store
    in (store, ks, env, v)) ∧
  (*step (store, ks, env, SLet is e) = (case is of
  | [] => (store, ks, e)
  | (i, e')::is' => (store, LetK store i is' e :: ks, e')) ∧*)
  step (store, ks, env, Lambda ps lp e) = (store, ks, env, Val $ Proc env ps lp e) ∧
  step (store, ks, env, Begin e es) = (store, (env, BeginK es) :: ks, env, e) ∧

  step (store, ks, env, Exception ex) = unwind Exception store ks ex
End

Definition steps_def:
  steps (n:num) t = if n = 0 then t
    else steps (n - 1) $ step t
End

(*
  EVAL “semantics (Val (SNum 3))”
  EVAL “semantics (Apply (Val (Prim SMul)) [Val (SNum 2); Val (SNum 4)])”
  EVAL “steps 4 ([], [], Apply (Val (Prim SMul)) [Val (SNum 2); Val (SNum 4)])”
  EVAL “steps 4 ([], [], Apply (Val (SNum 7)) [Val (SNum 2); Val (SNum 4)])”
  EVAL “steps 6 ([], [InLetK []], Apply (Val (Prim SMul)) [Val (SNum 2); Val (Prim SAdd)])”
  EVAL “steps 2 ([], [], Cond (Val (SBool F)) (Val (SNum 2)) (Val (SNum 4)))”
  EVAL “steps 4 ([], [], SLet [(strlit "x", Val $ SNum 42)] (Ident $ strlit "x"))”
  EVAL “steps 6 ([], [], Apply (Lambda [] (SOME $ strlit "x") (Ident $ strlit "x")) [Val $ SNum 4])”
  EVAL “steps 3 ([], [], Begin (Val $ SNum 1) [Val $ SNum 2])”

  EVAL “steps 16 ([], [], FEMPTY,
    Apply (
      Lambda [strlit "f"; strlit "x"] NONE (
        Apply (Ident $ strlit "f") [Val $ SNum 1]
      )
    ) [
      Lambda [strlit "y"] NONE (
        Apply (Val $ Prim SAdd) [
          Ident $ strlit "y";
          Ident $ strlit "x"
        ]
      );
      Val $ SNum 4
    ]
  )”

  EVAL “steps 16 ([], [], FEMPTY,
    Apply (
      Lambda [strlit "x"] NONE (
        Apply (
          Lambda [strlit "y"] NONE (
            Apply (Val $ Prim SAdd) [
              Ident $ strlit "y";
              Ident $ strlit "x"
            ]
          )
        ) [Val $ SNum 1]
      )
    ) [Val $ SNum 4]
  )”

  EVAL “steps 16 ([], [], FEMPTY,
    Apply (
      Lambda [strlit "x"] NONE (
        Apply (
          Lambda [strlit "x"] NONE (
            Apply (Val $ Prim SAdd) [
              Ident $ strlit "x"
            ]
          )
        ) [Val $ SNum 1]
      )
    ) [Val $ SNum 4]
  )”

  EVAL “steps 20 ([], [], FEMPTY,
    Apply (Val $ Prim SMul) [
      Val $ SNum 2;
      Apply (Val $ Prim CallCC) [ Lambda [strlit "x"] NONE (
        Apply (Val $ Prim SAdd) [
          Val $ SNum 4;
          Cond (Val $ SBool F) (
            Val $ SNum 3
          ) (
            Apply (Ident $ strlit "x") [Val $ SNum 5]
          )
        ]
      )]
    ]
  )”
*)

val _ = export_theory();