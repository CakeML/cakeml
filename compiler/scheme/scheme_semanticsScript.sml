(*
  Semantics of Scheme
*)
Theory scheme_semantics
Ancestors
  mlstring scheme_ast finite_map
Libs
  preamble

Datatype:
  e_or_v = Exp senv exp | Val val | Exception mlstring
End

Datatype:
  store_entry = Mut (val option) | Pair (val # val)
End

Definition mut_entry_def[simp]:
  mut_entry (Mut v) = v
End

Definition pair_entry_def[simp]:
  pair_entry (Pair v) = v
End

Definition sadd_def:
  sadd [] n = Val $ SNum n ∧
  sadd (SNum m :: xs) n = sadd xs (m + n) ∧
  sadd (_ :: xs) _ = Exception $ «Arith-op applied to non-number»
End

Definition smul_def:
  smul [] n = Val $ SNum n ∧
  smul (SNum m :: xs) n = smul xs (m * n) ∧
  smul (_ :: xs) _ = Exception $ «Arith-op applied to non-number»
End

Definition sminus_def:
  sminus [] = Exception $ «Arity mismatch» ∧
  sminus (SNum n :: xs) = (case xs of
  | [] => Val (SNum (-n))
  | _::_ => (case sadd xs 0 of
    | Val (SNum m) => Val (SNum (n - m))
    | e => e)) ∧
  sminus _ = Exception $ «Arith-op applied to non-number»
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
  seqv _ = Exception $ «Arity mismatch»
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

Definition allocate_list_def:
  allocate_list store [] = (store, Null) /\
  allocate_list store (x::xs) = let
      (store', tail) = allocate_list store xs;
      (l, store'') = fresh_loc store' (Pair (x, tail))
    in (store'', PairP l)
End

Definition parameterize_def:
  parameterize store env [] NONE e [] = (store, Exp env e) ∧
  parameterize store env [] (SOME (l:mlstring)) e xs = (let
      (store', listv) = allocate_list store xs;
      (n, store'') = fresh_loc store' (Mut $ SOME listv)
    in (store'', Exp (env |+ (l, n)) e)) ∧
  parameterize store env (p::ps) lp e (x::xs) = (let
      (n, store') = fresh_loc store (Mut $ SOME x)
    in parameterize store' (env |+ (p, n)) ps lp e xs) ∧
  parameterize store _ _ _ _ _ = (store, Exception $ «Wrong number of arguments»)
End

Definition application_def:
  application store ks (Prim p) xs = (case p of
  | SAdd => (store, ks, sadd xs 0)
  | SMul => (store, ks, smul xs 1)
  | SMinus => (store, ks, sminus xs)
  | SEqv => (store, ks, seqv xs)
  | CallCC => (case xs of
    | [v] => (store, (FEMPTY, ApplyK (SOME (v, [])) []) :: ks, Val $ Throw ks)
    | _ => (store, ks, Exception $ «Arity mismatch»))
  | Cons => (case xs of
    | [v1; v2] => (let (l, store') = fresh_loc store (Pair (v1, v2))
      in (store', ks, Val $ PairP l))
    | _ => (store, ks, Exception $ «Arity mismatch»))
  | Car => (case xs of
    | [v] => (case v of
      | PairP l => (store, ks, Val $ FST $ pair_entry $ EL l store)
      | _ => (store, ks, Exception $ «Can't take car of non-pair»))
    | _ => (store, ks, Exception $ «Arity mismatch»))
  | Cdr => (case xs of
    | [v] => (case v of
      | PairP l => (store, ks, Val $ SND $ pair_entry $ EL l store)
      | _ => (store, ks, Exception $ «Can't take cdr of non-pair»))
    | _ => (store, ks, Exception $ «Arity mismatch»))
  | IsNull => (case xs of
    | [v] => (case v of
      | Null => (store, ks, Val $ SBool T)
      | _ => (store, ks, Val $ SBool F))
    | _ => (store, ks, Exception $ «Arity mismatch»))
  | IsPair => case xs of
    | [v] => (case v of
      | PairP _ => (store, ks, Val $ SBool T)
      | _ => (store, ks, Val $ SBool F))
    | _ => (store, ks, Exception $ «Arity mismatch»)) ∧
  application store ks (Proc env ps lp e) xs = (let (store', e') =
    parameterize store env ps lp e xs in (store', ks, e')) ∧
  application store ks (Throw ks') xs = (case xs of
    | [v] => (store, ks', Val v)
    | _ => (store, ks, Exception $ «Arity mismatch»)) ∧
  application store ks _ _ = (store, ks, Exception $ «Not a procedure»)
End

Definition letinit_def:
  letinit store (env : mlstring |-> num) [] = store ∧
  letinit store env ((x,v)::xvs) =
    letinit (LUPDATE (Mut $ SOME v) (env ' x) store) env xvs
End

Definition return_def:
  return store [] v = (store, [], Val v) ∧

  return store ((env, ApplyK NONE eargs) :: ks) v = (case eargs of
  | [] => application store ks v []
  | e::es => (store, (env, ApplyK (SOME (v, [])) es) :: ks, Exp env e)) ∧
  return store ((env, ApplyK (SOME (vfn, vargs)) eargs) :: ks) v = (case eargs of
  | [] => application store ks vfn (REVERSE $ v::vargs)
  | e::es => (store, (env, ApplyK (SOME (vfn, v::vargs)) es) :: ks, Exp env e)) ∧

  return store ((env, LetinitK xvs x bs e) :: ks) v = (case bs of
  | [] => (letinit store env ((x,v)::xvs), ks, Exp env e)
  | (x',e')::bs' => (store, (env, LetinitK ((x,v)::xvs) x' bs' e) :: ks, Exp env e')) ∧

  return store ((env, CondK t f) :: ks) v = (if v = (SBool F)
    then (store, ks, Exp env f) else (store, ks, Exp env t)) ∧

  return store ((env, BeginK es e) :: ks) v = (case es of
  | [] => (store, ks, Exp env e)
  | e'::es' => (store, (env, BeginK es' e) :: ks, Exp env e')) ∧
  return store ((env, SetK x) :: ks) v = (LUPDATE (Mut $ SOME v) (env ' x) store, ks, Val $ Wrong "Unspecified")
End

Definition letrec_preinit_def:
  letrec_preinit store env [] = (store, env) ∧
  letrec_preinit store env (x::xs) = (let (n, store') = fresh_loc store (Mut NONE)
    in letrec_preinit store' (env |+ (x, n)) xs)
End

Definition step_def:
  step (store, ks, Val v) = return store ks v ∧
  step (store, ks, Exp env $ Lit lit) = (store, ks, Val $ lit_to_val lit) ∧
  step (store, ks, Exp env $ Apply fn args) = (store, (env, ApplyK NONE args) :: ks, Exp env fn) ∧
  step (store, ks, Exp env $ Cond c t f) = (store, (env, CondK t f) :: ks, Exp env c) ∧
  (*This is undefined if the program doesn't typecheck*)
  step (store, ks, Exp env $ Ident s) = (let ev = case mut_entry $ EL (env ' s) store of
    | NONE => Exception $ «Letrec variable touched»
    | SOME v => Val v
    in (store, ks, ev)) ∧
  step (store, ks, Exp env $ Lambda ps lp e) = (store, ks, Val $ Proc env ps lp e) ∧
  step (store, ks, Exp env $ Begin es e) = (case es of
  | [] => (store, ks, Exp env e)
  | e'::es' => (store, (env, BeginK es' e) :: ks, Exp env e')) ∧
  step (store, ks, Exp env $ Set x e) = (store, (env, SetK x) :: ks, Exp env e) ∧
  (*There is a missing reinit check, though the spec says it is optional*)
  step (store, ks, Exp env $ Letrec bs e) = (case bs of
  | [] => (store, ks, Exp env e)
  | (x,e')::bs' => let (store', env') = letrec_preinit store env (MAP FST bs)
      in (store', (env', LetinitK [] x bs' e) :: ks, Exp env' e')) ∧
  step (store, ks, Exp env $ Letrecstar bs e) = (let
    (store', env') = letrec_preinit store env (MAP FST bs)
      in (store', ks, Exp env' $ Begin (MAP (UNCURRY Set) bs) e)) ∧

  step (store, ks, Exception ex) = (store, [], Exception ex)
End

Definition steps_def:
  steps = FUNPOW step
End

Datatype:
  scheme_res = STerminate val | SDiverge | SError mlstring
End

Definition terminating_state_def:
  terminating_state (st, ks, e)
    ⇔ (ks = [] ∧ ∃ v . e = Val v) ∨ (∃ ex . e = Exception ex)
End

Definition scheme_semantics_prog_def:
  (scheme_semantics_prog prog (STerminate v) <=>
    (? n store . steps n ([], [], Exp FEMPTY prog) = (store, [], Val v))) /\
  (scheme_semantics_prog prog SDiverge <=>
    (! n . ¬ terminating_state (steps n ([], [], Exp FEMPTY prog)))) /\
  (scheme_semantics_prog prog (SError s) <=>
    (? n store . steps n ([], [], Exp FEMPTY prog) = (store, [], Exception s)))
End

(*
  open scheme_semanticsTheory;

Definition empty_store_def:
 empty_store = <| muts := []; pairs := [] |>
End

  EVAL “steps 100 ([], [], FEMPTY, Exp $ Letrec [(«x»,Lit $ LitNum 2);(«y»,Ident $ «x»)] (Ident $ «y»))”
  EVAL “steps 100 ([], [], Exp FEMPTY $ Apply (Lit $ LitPrim Cdr) [Apply (Lit $ LitPrim Cons) [Lit $ LitNum 1; Lit $ LitNull]])”
  EVAL “steps 10 ([], [], FEMPTY, Exp $ Apply (Lit (LitPrim SMinus)) [Lit (LitNum 4); Lit (LitNum 2)])”
  EVAL “steps 4 ([], [], Apply (Val (SNum 7)) [Val (SNum 2); Val (SNum 4)])”
  EVAL “steps 6 ([], [InLetK []], Apply (Val (Prim SMul)) [Val (SNum 2); Val (Prim SAdd)])”
  EVAL “steps 2 ([], [], Cond (Val (SBool F)) (Val (SNum 2)) (Val (SNum 4)))”
  EVAL “steps 4 ([], [], SLet [(«x», Val $ SNum 42)] (Ident $ «x»))”
  EVAL “steps 6 ([], [], Apply (Lambda [] (SOME $ «x») (Ident $ «y»)) [Val $ SNum 4])”
  EVAL “steps 3 ([], [], Begin (Val $ SNum 1) [Val $ SNum 2])”

  EVAL “steps 16 ([], [], FEMPTY,
    Apply (
      Lambda [«f»; «x»] NONE (
        Apply (Ident $ «f») [Val $ SNum 1]
      )
    ) [
      Lambda [«y»] NONE (
        Apply (Val $ Prim SAdd) [
          Ident $ «y»;
          Ident $ «x»
        ]
      );
      Val $ SNum 4
    ]
  )”

  EVAL “steps 99 ([], [], FEMPTY,Exp $
    Apply (
      Lambda [«x»] NONE (
        Apply (
          Lambda [«y»] NONE (
            Apply (Lit $ LitPrim SAdd) [
              Ident $ «y»;
              Ident $ «x»
            ]
          )
        ) [Lit $ LitNum 1]
      )
    ) [Lit $ LitNum 4]
  )”

  EVAL “steps 16 ([], [], FEMPTY,
    Apply (
      Lambda [«x»] NONE (
        Apply (
          Lambda [«x»] NONE (
            Apply (Val $ Prim SAdd) [
              Ident $ «x»
            ]
          )
        ) [Val $ SNum 1]
      )
    ) [Val $ SNum 4]
  )”

  EVAL “steps 22 ([], [], FEMPTY,
    Apply (
      Lambda [«x»] NONE (Begin (
        Apply (
          Lambda [«y»] NONE (Begin (
            Set «x» (Val $ SNum 5)
          ) [
            Apply (Val $ Prim SAdd) [
              Ident $ «y»;
              Ident $ «x»
            ]
          ])
        ) [Val $ SNum 1]
      ) [
        Ident $ «x»
      ])
    ) [Val $ SNum 4]
  )”

  EVAL “steps 100 ([], [], FEMPTY,
    Letrecstar [
      (strlit $ "to", Lambda [«x»] NONE (
        Apply (Ident $ «fro») [
          Apply (Val $ Prim SAdd) [Val $ SNum 1; Ident $ «x»]
        ]
      ));
      (strlit $ "fro", Lambda [«x»] NONE (
        Apply (Ident $ «to») [
          Apply (Val $ Prim SMul) [Val $ SNum 2; Ident $ «x»]
        ]
      ))
    ] (Apply (Ident $ «to») [Val $ SNum 0])
  )”

  EVAL “steps 3 ([], [], FEMPTY,
    Letrecstar [(strlit $ "fail", Ident $ «fail»)] (Val $ SBool F)
  )”

  EVAL “steps 20 ([], [], FEMPTY,
    Apply (Val $ Prim SMul) [
      Val $ SNum 2;
      Apply (Val $ Prim CallCC) [ Lambda [«x»] NONE (
        Apply (Val $ Prim SAdd) [
          Val $ SNum 4;
          Cond (Val $ SBool F) (
            Val $ SNum 3
          ) (
            Apply (Ident $ «x») [Val $ SNum 5]
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
      Apply (Val $ Prim CallCC) [ Lambda [«x»] NONE (
        Set «double» (Ident $ «x»)
      )]
    ) [
      Set «x» (Apply (Val $ Prim SMul) [
        Val $ SNum 2;
        Ident $ «x»
      ]);
      Apply (Ident $ «double») [Val $ SNum 0]
    ])
  )”

  EVAL “steps 10 ([], [], FEMPTY, Apply (Val $ Prim SMinus) [Val $ SNum 3; Val $ SNum 2])”

  EVAL “steps 1000 ([], [], FEMPTY, Letrecstar [(«fac», Lambda [«x»] NONE (
    Cond (Apply (Val $ Prim SEqv) [Ident $ «x»; Val $ SNum 0]) (
      Val $ SNum 1
    ) (
      Apply (Val $ Prim SMul) [Ident $ «x»; Apply (Ident $ «fac») [
        Apply (Val $ Prim SMinus) [Ident $ «x»; Val $ SNum 1]
      ]]
    )
  ))] (Apply (Ident $ «fac») [Val $ SNum 6]))”

  EVAL “steps 500 ([], [], FEMPTY, Exp $ Letrecstar [(«fac», Lambda [«x»] NONE (
    Letrecstar [(«st», Lit $ LitNum 0); («acc», Lit $ LitNum 1)] (
      Begin [ Apply (Lit $ LitPrim CallCC) [ Lambda [«k»] NONE (
        Set «st» (Ident $ «k»)
      )]] (
        Cond (Apply (Lit $ LitPrim SEqv) [Ident $ «x»; Lit $ LitNum 0])
          (Ident $ «acc»)
          (Apply (Ident $ «st») [ Begin [
            Set «acc» (Apply (Lit $ LitPrim SMul) [
              Ident $ «acc»;
              Ident $ «x»
            ])
          ] (
            Set «x» (Apply (Lit $ LitPrim SMinus) [
              Ident $ «x»;
              Lit $ LitNum 1
            ])
          )])
      )
    )
  ))] (Apply (Ident $ «fac») [Lit $ LitNum 6]))”
*)

