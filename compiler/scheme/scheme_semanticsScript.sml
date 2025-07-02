(*
  Semantics of Scheme
*)
open preamble;
open mlstringTheory;
open scheme_astTheory;
open finite_mapTheory;

val _ = new_theory "scheme_semantics";

Datatype:
  e_or_v = Exp senv exp | Val val | Exception mlstring
End

Datatype:
  store = <| muts : val option list; pairs : (val # val) list |>
End

Definition sadd_def:
  sadd [] n = Val $ SNum n ∧
  sadd (SNum m :: xs) n = sadd xs (m + n) ∧
  sadd (_ :: xs) _ = Exception $ strlit "Arith-op applied to non-number"
End

Definition smul_def:
  smul [] n = Val $ SNum n ∧
  smul (SNum m :: xs) n = smul xs (m * n) ∧
  smul (_ :: xs) _ = Exception $ strlit "Arith-op applied to non-number"
End

Definition sminus_def:
  sminus [] = Exception $ strlit "Arity mismatch" ∧
  sminus (SNum n :: xs) = (case xs of
  | [] => Val (SNum (-n))
  | _::_ => (case sadd xs 0 of
    | Val (SNum m) => Val (SNum (n - m))
    | e => e)) ∧
  sminus _ = Exception $ strlit "Arith-op applied to non-number"
End

Definition seqv_def:
  seqv [v1; v2] = (Val $ SBool $ case v1 of
  | SNum n => (case v2 of
    | SNum m => n = m
    | _ => F)
  | SBool b => (case v2 of
    | SBool b' => b = b'
    | _ => F)
  | _ => F) ∧
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
  fresh_loc stl ov = (LENGTH stl, SNOC ov stl)
End
 
Definition parameterize_def:
  parameterize st env [] NONE e [] = (st, Exp env e) ∧
  parameterize st env [] (SOME (l:mlstring)) e xs = (let (n, muts') = fresh_loc st.muts (SOME $ SList xs)
    in (st with muts := muts', Exp (env |+ (l, n)) e)) ∧
  parameterize st env (p::ps) lp e (x::xs) = (let (n, muts') = fresh_loc st.muts (SOME x)
    in parameterize (st with muts := muts') (env |+ (p, n)) ps lp e xs) ∧
  parameterize st _ _ _ _ _ = (st, Exception $ strlit "Wrong number of arguments")
End

Definition application_def:
  application st ks (Prim p) xs = (case p of
  | SAdd => (st, ks, sadd xs 0)
  | SMul => (st, ks, smul xs 1)
  | SMinus => (st, ks, sminus xs)
  | SEqv => (st, ks, seqv xs)
  | CallCC => (case xs of
    | [v] => (st, (FEMPTY, ApplyK (SOME (v, [])) []) :: ks, Val $ Throw ks)
    | _ => (st, ks, Exception $ strlit "Arity mismatch"))
  | Cons => (case xs of
    | [v1; v2] => (let (l, pairs') = fresh_loc st.pairs (v1, v2)
      in (st with pairs := pairs', ks, Val $ PairP l))
    | _ => (st, ks, Exception $ strlit "Arity mismatch"))
  | Car => (case xs of
    | [v] => (case v of
      | PairP l => (st, ks, Val $ FST $ EL l st.pairs)
      | _ => (st, ks, Exception $ strlit "Can't take car of non-pair"))
    | _ => (st, ks, Exception $ strlit "Arity mismatch"))
  | Cdr => case xs of
    | [v] => (case v of
      | PairP l => (st, ks, Val $ SND $ EL l st.pairs)
      | _ => (st, ks, Exception $ strlit "Can't take cdr of non-pair"))
    | _ => (st, ks, Exception $ strlit "Arity mismatch")) ∧
  application st ks (Proc env ps lp e) xs = (let (st', e') =
    parameterize st env ps lp e xs in (st', ks, e')) ∧
  application st ks (Throw ks') xs = (case xs of
    | [v] => (st, ks', Val v)
    | _ => (st, ks, Exception $ strlit "Arity mismatch")) ∧
  application st ks _ _ = (st, ks, Exception $ strlit "Not a procedure")
End

Definition letinit_def:
  letinit st (env : mlstring |-> num) [] = st ∧
  letinit st env ((x,v)::xvs) =
    letinit (st with muts := LUPDATE (SOME v) (env ' x) st.muts) env xvs
End

Definition return_def:
  return st [] v = (st, [], Val v) ∧

  return st ((env, ApplyK NONE eargs) :: ks) v = (case eargs of
  | [] => application st ks v []
  | e::es => (st, (env, ApplyK (SOME (v, [])) es) :: ks, Exp env e)) ∧
  return st ((env, ApplyK (SOME (vfn, vargs)) eargs) :: ks) v = (case eargs of
  | [] => application st ks vfn (REVERSE $ v::vargs)
  | e::es => (st, (env, ApplyK (SOME (vfn, v::vargs)) es) :: ks, Exp env e)) ∧

  return st ((env, LetinitK xvs x bs e) :: ks) v = (case bs of
  | [] => (letinit st env ((x,v)::xvs), ks, Exp env e)
  | (x',e')::bs' => (st, (env, LetinitK ((x,v)::xvs) x' bs' e) :: ks, Exp env e')) ∧

  return st ((env, CondK t f) :: ks) v = (if v = (SBool F)
    then (st, ks, Exp env f) else (st, ks, Exp env t)) ∧

  return st ((env, BeginK es e) :: ks) v = (case es of
  | [] => (st, ks, Exp env e)
  | e'::es' => (st, (env, BeginK es' e) :: ks, Exp env e')) ∧
  return st ((env, SetK x) :: ks) v = (st with muts := LUPDATE (SOME v) (env ' x) st.muts, ks, Val $ Wrong "Unspecified")
End

Definition letrec_preinit_def:
  letrec_preinit st env [] = (st, env) ∧
  letrec_preinit st env (x::xs) = (let (n, muts') = fresh_loc st.muts NONE
    in letrec_preinit (st with muts := muts') (env |+ (x, n)) xs)
End

Definition step_def:
  step (st, ks, Val v) = return st ks v ∧
  step (st, ks, Exp env $ Lit lit) = (st, ks, Val $ lit_to_val lit) ∧
  step (st, ks, Exp env $ Apply fn args) = (st, (env, ApplyK NONE args) :: ks, Exp env fn) ∧
  step (st, ks, Exp env $ Cond c t f) = (st, (env, CondK t f) :: ks, Exp env c) ∧
  (*This is undefined if the program doesn't typecheck*)
  step (st, ks, Exp env $ Ident s) = (let ev = case EL (env ' s) st.muts of
    | NONE => Exception $ strlit "Letrec variable touched"
    | SOME v => Val v
    in (st, ks, ev)) ∧
  step (st, ks, Exp env $ Lambda ps lp e) = (st, ks, Val $ Proc env ps lp e) ∧
  step (st, ks, Exp env $ Begin es e) = (case es of
  | [] => (st, ks, Exp env e)
  | e'::es' => (st, (env, BeginK es' e) :: ks, Exp env e')) ∧
  step (st, ks, Exp env $ Set x e) = (st, (env, SetK x) :: ks, Exp env e) ∧
  (*There is a missing reinit check, though the spec says it is optional*)
  step (st, ks, Exp env $ Letrec bs e) = (case bs of
  | [] => (st, ks, Exp env e)
  | (x,e')::bs' => let (st', env') = letrec_preinit st env (MAP FST bs)
      in (st', (env', LetinitK [] x bs' e) :: ks, Exp env' e')) ∧
  step (st, ks, Exp env $ Letrecstar bs e) = (let
    (st', env') = letrec_preinit st env (MAP FST bs)
      in (st', ks, Exp env' $ Begin (MAP (UNCURRY Set) bs) e)) ∧

  step (st, ks, Exception ex) = (st, [], Exception ex)
End

Definition steps_def:
  steps (n:num) t = if n = 0 then t
    else steps (n - 1) $ step t
End

(*
  open scheme_semanticsTheory;

Definition empty_store_def:
 empty_store = <| muts := []; pairs := [] |>
End

  EVAL “steps 100 ([], [], FEMPTY, Exp $ Letrec [(strlit "x",Lit $ LitNum 2);(strlit "y",Ident $ strlit "x")] (Ident $ strlit "y"))”
  EVAL “steps 100 (empty_store, [], Exp FEMPTY $ Apply (Lit $ LitPrim Cdr) [Apply (Lit $ LitPrim Cons) [Lit $ LitNum 1; Lit $ LitNull]])”
  EVAL “steps 10 ([], [], FEMPTY, Exp $ Apply (Lit (LitPrim SMinus)) [Lit (LitNum 4); Lit (LitNum 2)])”
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

  EVAL “steps 99 ([], [], FEMPTY,Exp $
    Apply (
      Lambda [strlit "x"] NONE (
        Apply (
          Lambda [strlit "y"] NONE (
            Apply (Lit $ LitPrim SAdd) [
              Ident $ strlit "y";
              Ident $ strlit "x"
            ]
          )
        ) [Lit $ LitNum 1]
      )
    ) [Lit $ LitNum 4]
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
    Letrecstar [
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
    Letrecstar [(strlit $ "fail", Ident $ strlit "fail")] (Val $ SBool F)
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
    Letrecstar [
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

  EVAL “steps 1000 ([], [], FEMPTY, Letrecstar [(strlit "fac", Lambda [strlit "x"] NONE (
    Cond (Apply (Val $ Prim SEqv) [Ident $ strlit "x"; Val $ SNum 0]) (
      Val $ SNum 1
    ) (
      Apply (Val $ Prim SMul) [Ident $ strlit "x"; Apply (Ident $ strlit "fac") [
        Apply (Val $ Prim SMinus) [Ident $ strlit "x"; Val $ SNum 1]
      ]]
    )
  ))] (Apply (Ident $ strlit "fac") [Val $ SNum 6]))”

  EVAL “steps 500 ([], [], FEMPTY, Exp $ Letrecstar [(strlit "fac", Lambda [strlit "x"] NONE (
    Letrecstar [(strlit "st", Lit $ LitNum 0); (strlit "acc", Lit $ LitNum 1)] (
      Begin [ Apply (Lit $ LitPrim CallCC) [ Lambda [strlit "k"] NONE (
        Set (strlit "st") (Ident $ strlit "k")
      )]] (
        Cond (Apply (Lit $ LitPrim SEqv) [Ident $ strlit "x"; Lit $ LitNum 0])
          (Ident $ strlit "acc")
          (Apply (Ident $ strlit "st") [ Begin [
            Set (strlit "acc") (Apply (Lit $ LitPrim SMul) [
              Ident $ strlit "acc";
              Ident $ strlit "x"
            ])
          ] (
            Set (strlit "x") (Apply (Lit $ LitPrim SMinus) [
              Ident $ strlit "x";
              Lit $ LitNum 1
            ])
          )])
      )
    )
  ))] (Apply (Ident $ strlit "fac") [Lit $ LitNum 6]))”
*)

val _ = export_theory();
