(*
  Semantics of Scheme
*)
open preamble;
open mlstringTheory;
open scheme_astTheory;
open finite_mapTheory;

val _ = new_theory "scheme_semantics";

Datatype:
  (*Contexts for small-step operational semantics*)
  cont = ApplyK (((*'a*) val # (*'a*) val list) option) ('a list)
       | CondK 'a 'a
       | BeginK ('a list)
       | SetK mlstring
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
  fresh_loc store ov = (LENGTH store, SNOC ov store)
End

Definition parameterize_def:
  parameterize _ store ks env [] NONE e [] = (store, ks, env, e) ∧
  parameterize _ store ks env [] (SOME l) e xs = (let (n, store') = fresh_loc store (SOME $ SList xs)
    in (store', ks, (env |+ (l, n)), e)) ∧
  parameterize excons store ks env (p::ps) lp e (x::xs) = (let (n, store') = fresh_loc store (SOME x)
    in parameterize excons store' ks (env |+ (p, n)) ps lp e xs) ∧
  parameterize excons store ks _ _ _ _ _ = (store, ks, FEMPTY, excons $ strlit "Wrong number of arguments")
End

Definition application_def:
  application vcons excons store ks (Prim p) xs = (case p of
  | SAdd => (store, ks, FEMPTY, sadd vcons excons xs 0)
  | SMul => (store, ks, FEMPTY, smul vcons excons xs 1)) ∧
  application _ excons store ks (Proc env ps lp e) xs =
    parameterize excons store ks env ps lp e xs ∧
  application _ excons store ks _ _ = (store, ks, FEMPTY, excons $ strlit "Not a procedure")
End

Definition return_def:
  return vcons _ (store, [], env, v) = (store, [], env, vcons v) ∧

  return vcons excons (store, (env, ApplyK NONE eargs) :: ks, _, v) = (case eargs of
  | [] => application vcons excons store ks v []
  | e::es => (store, (env, ApplyK (SOME (v, [])) es) :: ks, env, e)) ∧
  return vcons excons (store, (env, ApplyK (SOME (vfn, vargs)) eargs) :: ks, _, v) = (case eargs of
  | [] => application vcons excons store ks vfn (REVERSE $ v::vargs)
  | e::es => (store, (env, ApplyK (SOME (vfn, v::vargs)) es) :: ks, env, e)) ∧

  return _ _ (store, (env, CondK t f) :: ks, _, v) = (if v = (SBool F)
    then (store, ks, env, f) else (store, ks, env, t)) ∧

  return vcons _ (store, (env, BeginK es) :: ks, _, v) = (case es of
  | [] => (store, ks, env, vcons v)
  | e::es' => (store, (env, BeginK es') :: ks, env, e)) ∧
  return vcons excons (store, (env, SetK x) :: ks, _, v) = (LUPDATE (SOME v) (env ' x) store, ks, env, vcons $ Wrong "Unspecified")
End

Definition unwind_def:
  unwind excons store [] ex = (store, [], FEMPTY, excons ex) ∧
  unwind excons store (k::ks) ex = unwind excons store ks ex
End

Definition letrec_init_def:
  letrec_init store env [] = (store, env) ∧
  letrec_init store env (x::xs) = (let (n, store') = fresh_loc store NONE
    in letrec_init store' (env |+ (x, n)) xs)
End

Definition step_def:
  step (store, ks, env, Val v) = return Val Exception (store, ks, env, v) ∧
  step (store, ks, env, Apply fn args) = (store, (env, ApplyK NONE args) :: ks, env, fn) ∧
  step (store, ks, env, Cond c t f) = (store, (env, CondK t f) :: ks, env, c) ∧
  (*This is undefined if the program doesn't typecheck*)
  step (store, ks, env, Ident s) = (let e = case EL (env ' s) store of
    | NONE => Exception $ strlit "letrec variable touched"
    | SOME v => Val v
    in (store, ks, env, e)) ∧
  step (store, ks, env, Lambda ps lp e) = (store, ks, env, Val $ Proc env ps lp e) ∧
  step (store, ks, env, Begin e es) = (store, (env, BeginK es) :: ks, env, e) ∧
  step (store, ks, env, Set x e) = (store, (env, SetK x) :: ks, env, e) ∧
  (*There is a missing reinit check, though the spec says it is optional*)
  step (store, ks, env, Letrec bs e) = (case bs of
  | [] => (store, ks, env, e)
  | (x, i)::bs' => let (store', env') = letrec_init store env (MAP FST bs)
      in (store', (env', BeginK (SNOC e (MAP (UNCURRY Set) bs'))) :: ks, env', Set x i)) ∧

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

  EVAL “steps 22 ([], [], FEMPTY,
    Apply (
      Lambda [strlit "x"] NONE (Begin (
        Apply (
          Lambda [strlit "y"] NONE (Begin (
            Set (strlit "x") (Val $ SNum 5)
          ) [
            Apply (Val $ Prim SAdd) [
              Ident $ strlit "y";
              Ident $ strlit "x"
            ]
          ])
        ) [Val $ SNum 1]
      ) [
        Ident $ strlit "x"
      ])
    ) [Val $ SNum 4]
  )”

  EVAL “steps 100 ([], [], FEMPTY,
    Letrec [
      (strlit $ "to", Lambda [strlit "x"] NONE (
        Apply (Ident $ strlit "fro") [
          Apply (Val $ Prim SAdd) [Val $ SNum 1; Ident $ strlit "x"]
        ]
      ));
      (strlit $ "fro", Lambda [strlit "x"] NONE (
        Apply (Ident $ strlit "to") [
          Apply (Val $ Prim SMul) [Val $ SNum 2; Ident $ strlit "x"]
        ]
      ))
    ] (Apply (Ident $ strlit "to") [Val $ SNum 0])
  )”

  EVAL “steps 3 ([], [], FEMPTY,
    Letrec [(strlit $ "fail", Ident $ strlit "fail")] (Val $ SBool F)
  )”
*)

val _ = export_theory();