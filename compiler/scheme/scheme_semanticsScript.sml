(*
  Semantics of Scheme
*)
open preamble;
open mlstringTheory;
open scheme_astTheory;
open finite_mapTheory;

val _ = new_theory "scheme_semantics";

Definition sadd_def:
  sadd [] n = Val $ SNum n ∧
  sadd (SNum m :: xs) n = sadd xs (m + n) ∧
  sadd (_ :: xs) _ = Exception $ strlit "Arguments to + must be numbers"
End

Definition smul_def:
  smul [] n = Val $ SNum n ∧
  smul (SNum m :: xs) n = smul xs (m * n) ∧
  smul (_ :: xs) _ = Exception $ strlit "Arguments to * must be numbers"
End

Definition sminus_def:
  sminus [] = Exception $ strlit "Arity mismatch" ∧
  sminus (SNum n :: xs) = (case sadd xs 0 of
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

Definition fresh_loc_def:
  fresh_loc store ov = (LENGTH store, SNOC ov store)
End

Definition parameterize_def:
  parameterize store ks env [] NONE e [] = (store, ks, env, e) ∧
  parameterize store ks env [] (SOME l) e xs = (let (n, store') = fresh_loc store (SOME $ SList xs)
    in (store', ks, (env |+ (l, n)), e)) ∧
  parameterize store ks env (p::ps) lp e (x::xs) = (let (n, store') = fresh_loc store (SOME x)
    in parameterize store' ks (env |+ (p, n)) ps lp e xs) ∧
  parameterize store ks _ _ _ _ _ = (store, ks, FEMPTY, Exception $ strlit "Wrong number of arguments")
End

Definition application_def:
  application store ks (Prim p) xs = (case p of
  | SAdd => (store, ks, FEMPTY, sadd xs 0)
  | SMul => (store, ks, FEMPTY, smul xs 1)
  | SMinus => (store, ks, FEMPTY, sminus xs)
  | SEqv => (store, ks, FEMPTY, seqv xs)
  | CallCC => case xs of
    | [v] => (store, (FEMPTY, ApplyK (SOME (v, [])) []) :: ks, FEMPTY, Val $ Throw ks)
    | _ => (store, ks, FEMPTY, Exception $ strlit "arity mismatch")) ∧
  application store ks (Proc env ps lp e) xs =
    parameterize store ks env ps lp e xs ∧
  application store ks (Throw ks') xs = (case xs of
    | [v] => (store, ks', FEMPTY, Val v)
    | _ => (store, ks, FEMPTY, Exception $ strlit "arity mismatch")) ∧
  application store ks _ _ = (store, ks, FEMPTY, Exception $ strlit "Not a procedure")
End

Definition return_def:
  return store [] v = (store, [], FEMPTY, Val v) ∧

  return store ((env, ApplyK NONE eargs) :: ks) v = (case eargs of
  | [] => application store ks v []
  | e::es => (store, (env, ApplyK (SOME (v, [])) es) :: ks, env, e)) ∧
  return store ((env, ApplyK (SOME (vfn, vargs)) eargs) :: ks) v = (case eargs of
  | [] => application store ks vfn (REVERSE $ v::vargs)
  | e::es => (store, (env, ApplyK (SOME (vfn, v::vargs)) es) :: ks, env, e)) ∧

  return store ((env, CondK t f) :: ks) v = (if v = (SBool F)
    then (store, ks, env, f) else (store, ks, env, t)) ∧

  return store ((env, BeginK es) :: ks) v = (case es of
  | [] => (store, ks, env, Val v)
  | e::es' => (store, (env, BeginK es') :: ks, env, e)) ∧
  return store ((env, SetK x) :: ks) v = (LUPDATE (SOME v) (env ' x) store, ks, env, Val $ Wrong "Unspecified")
End

Definition letrec_init_def:
  letrec_init store env [] = (store, env) ∧
  letrec_init store env (x::xs) = (let (n, store') = fresh_loc store NONE
    in letrec_init store' (env |+ (x, n)) xs)
End

Definition step_def:
  step (store, ks, env, Val v) = return store ks v ∧
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

  step (store, ks, env, Exception ex) = (store, [], env, Exception ex)
End

Definition steps_def:
  steps (n:num) t = if n = 0 then t
    else steps (n - 1) $ step t
End

(*
  open scheme_semanticsTheory;

  EVAL “steps 4 ([], [], Apply (Val (Prim SMinus)) [Val (SNum 2); Val (SNum 4)])”
  EVAL “steps 4 ([], [], Apply (Val (SNum 7)) [Val (SNum 2); Val (SNum 4)])”
  EVAL “steps 6 ([], [InLetK []], Apply (Val (Prim SMul)) [Val (SNum 2); Val (Prim SAdd)])”
  EVAL “steps 2 ([], [], Cond (Val (SBool F)) (Val (SNum 2)) (Val (SNum 4)))”
  EVAL “steps 4 ([], [], SLet [(strlit "x", Val $ SNum 42)] (Ident $ strlit "x"))”
  EVAL “steps 6 ([], [], Apply (Lambda [] (SOME $ strlit "x") (Ident $ strlit "y")) [Val $ SNum 4])”
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

  EVAL “steps 102 ([], [], FEMPTY,
    Letrec [
      (strlit $ "double", Val $ SNum 0);
      (strlit $ "x", Val $ SNum 1)
    ] (Begin (
      Apply (Val $ Prim CallCC) [ Lambda [strlit "x"] NONE (
        Set (strlit "double") (Ident $ strlit "x")
      )]
    ) [
      Set (strlit "x") (Apply (Val $ Prim SMul) [
        Val $ SNum 2;
        Ident $ strlit "x"
      ]);
      Apply (Ident $ strlit "double") [Val $ SNum 0]
    ])
  )”

  EVAL “steps 10 ([], [], FEMPTY, Apply (Val $ Prim SMinus) [Val $ SNum 3; Val $ SNum 2])”

  EVAL “steps 1000 ([], [], FEMPTY, Letrec [(strlit "fac", Lambda [strlit "x"] NONE (
    Cond (Apply (Val $ Prim SEqv) [Ident $ strlit "x"; Val $ SNum 0]) (
      Val $ SNum 1
    ) (
      Apply (Val $ Prim SMul) [Ident $ strlit "x"; Apply (Ident $ strlit "fac") [
        Apply (Val $ Prim SMinus) [Ident $ strlit "x"; Val $ SNum 1]
      ]]
    )
  ))] (Apply (Ident $ strlit "fac") [Val $ SNum 6]))”
*)

val _ = export_theory();