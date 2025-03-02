(*
  Code generator for Scheme to CakeML compiler
*)
open preamble;
open astTheory;
open scheme_astTheory;

open semanticPrimitivesTheory;
open namespaceTheory;

val _ = new_theory "scheme_to_cake";

Definition to_ml_vals_def:
  to_ml_vals (Prim p) = Con (SOME $ Short "Prim") [case p of
  | SAdd => Con (SOME $ Short "SAdd") []
  | SMul => Con (SOME $ Short "SMul") []
  | SMinus => Con (SOME $ Short "SMinus") []
  | SEqv => Con (SOME $ Short "SEqv") []
  | CallCC => Con (SOME $ Short "CallCC") []] ∧
  to_ml_vals (SNum n) = Con (SOME $ Short "SNum") [Lit $ IntLit n] ∧
  to_ml_vals (SBool b) = Con (SOME $ Short "SBool") [Lit $ IntLit
    if b then 1 else 0]
End

Definition cons_list_def:
  cons_list [] = Con (SOME $ Short "nil") [] ∧
  cons_list (x::xs) = Con (SOME $ Short "cons") [x; cons_list xs]
End

Definition proc_ml_def:
  proc_ml n [] NONE k args ce = (n, Mat (Var (Short args)) [
        (Pcon (SOME $ Short "nil") [],
          App Opapp [ce; Var (Short k)]);
        (Pany,
          Con (SOME $ Short "Ex") [Lit $ StrLit "Wrong number of arguments"])
    ]) ∧
  proc_ml n [] (SOME x) k args ce = (n, Let (SOME $ "s" ++ explode x)
      (App Opref [Con (SOME $ Short "SList") [Var (Short args)]])
      (App Opapp [ce; Var (Short k)])) ∧
  proc_ml n (x::xs) xp k args ce = (let
    arg = "x" ++ toString n;
    args' = "xs" ++ toString (n+1);
    (m, inner) = proc_ml (n+2) xs xp k args' ce
  in
    (m, Mat (Var (Short args)) [
        (Pcon (SOME $ Short "nil") [],
          Con (SOME $ Short "Ex") [Lit $ StrLit "Wrong number of arguments"]);
        (Pcon (SOME $ Short "cons") [Pvar arg; Pvar args'],
          Let (SOME $ "s" ++ explode x)
            (App Opref [Con (SOME $ Short "Some") [Var (Short arg)]])
            inner)
    ]))
End

Definition letinit_ml_def:
  letinit_ml [] inner = inner ∧
  letinit_ml ((x,_)::bs) inner = Let (SOME $ "s" ++ explode x)
      (App Opref [Con (SOME $ Short "None") []]) (letinit_ml bs inner)
End

Definition cps_transform_def:
  cps_transform n (Val v) = (let k = "k" ++ toString n in
    (n+1, Fun k $ App Opapp [Var (Short k); to_ml_vals v])) ∧
  cps_transform n (Exception s) =
    (n, Fun "_" $ Con (SOME $ Short "Ex") [Lit $ StrLit $ explode s]) ∧
  cps_transform n (Cond c t f) = (let
    (m, cc) = cps_transform n c;
    k = "k" ++ toString m;
    (l, ck) = cps_transform_cont (m+1) (CondK t f) k
  in
    (l, Fun k $ App Opapp [cc; ck])) ∧
  cps_transform n (Apply fn args) = (let
    (m, cfn) = cps_transform n fn;
    k = "k" ++ toString m;
    (l, ck) = cps_transform_cont (m+1) (ApplyK NONE args) k
  in
    (l, Fun k $ App Opapp [cfn; ck])) ∧
  cps_transform n (Ident x) = (let k = "k" ++ toString n in
    (n, Fun k $ Mat (App Opderef [Var (Short $ "s" ++ explode x)]) [
      (Pcon (SOME $ Short "None") [],
        Con (SOME $ Short "Ex") [Lit $ StrLit "Letrec variable touched"]);
      (Pcon (SOME $ Short "Some") [Pvar $ "s'" ++ explode x],
        App Opapp [Var (Short k); Var (Short $ "s'" ++ explode x)])])) ∧
  cps_transform n (Lambda xs xp e) = (let
    (m, ce) = cps_transform n e;
    args = "xs" ++ toString m;
    k = "k" ++ toString (m+1);
    (l, inner) = proc_ml (m+2) xs xp k args ce;
    k' = "k" ++ toString l;
  in
    (l+1, Fun k' $ App Opapp [Var (Short k');
      Con (SOME $ Short "Proc") [Fun k $ Fun args inner]])) ∧
  cps_transform n (Begin e es) = (let
    (m, ce) = cps_transform n e;
    k = "k" ++ toString m;
    (l, seqk) = cps_transform_seq (m+1) k es
  in
    (l, Fun k $ App Opapp [ce; seqk])) ∧
  cps_transform n (Set x e) = (let
    (m, ce) = cps_transform n e;
    k = "k" ++ toString m;
    t = "t" ++ toString (m+1);
  in
    (m+2, Fun k $ (App Opapp [ce;
      Fun t $ Let NONE (App Opassign [Var (Short $ "s" ++ explode x);
          Con (SOME $ Short "Some") [Var (Short t)]])
        (App Opapp [Var (Short k); Con (SOME $ Short "Wrong") [Lit $ StrLit "Unspecified"]])]))) ∧
  cps_transform n (Letrec bs e) = (let
    (m, ce) = cps_transform n e;
    k = "k" ++ toString m;
    (l, inner) = cps_transform_letreinit (m+1) k bs ce
  in
    (l, Fun k $ letinit_ml bs inner)) ∧

  cps_transform_cont n (CondK t f) k = (let
    (m, ct) = cps_transform n t;
    (l, cf) = cps_transform m f;
    p = "t" ++ toString l;
  in
    (l+1, Fun p $ Mat (Var (Short p)) [
      (Pcon (SOME $ Short "SBool") [Plit $ IntLit 0], App Opapp [cf; Var (Short k)]);
      (Pany, App Opapp [ct; Var (Short k)])
    ])) ∧
  cps_transform_cont n (ApplyK NONE es) k = (let
    t = "t" ++ toString n;
    (m, ce) = cps_transform_app (n+1) (Var (Short t)) [] es k
  in
    (m, Fun t ce)
  ) ∧
  cps_transform_cont n (ApplyK (SOME (f, vs)) es) k =
    cps_transform_app n (to_ml_vals f) (MAP to_ml_vals vs) es k ∧

  cps_transform_app n tfn ts (e::es) k = (let
    (m, ce) = cps_transform n e;
    t = "t" ++ toString m;
    (l, inner) = cps_transform_app (m+1) tfn (Var (Short t)::ts) es k
  in
    (l, App Opapp [ce; Fun t inner])) ∧
  cps_transform_app n tfn ts [] k = (n,
    App Opapp [
      App Opapp [App Opapp [Var (Short "app"); Var (Short k)]; tfn];
      cons_list (REVERSE ts)]) ∧

  cps_transform_seq n k [] = (n, Var (Short k)) ∧
  cps_transform_seq n k (e::es) = (let
    (m, ce) = cps_transform n e;
    (l, inner) = cps_transform_seq m k es
  in
    (l, Fun "_" $ App Opapp [ce; inner])) ∧

  cps_transform_letreinit n k [] ce = (n,
    App Opapp [ce; Var (Short k)]) ∧
  cps_transform_letreinit n k ((x,e)::bs) ce = (let
    (m, ce') = cps_transform n e;
    (l, inner) = cps_transform_letreinit m k bs ce;
    t = "t" ++ toString l
  in
    (l+1, App Opapp [ce'; Fun t $ Let NONE
      (App Opassign [Var (Short $ "s" ++ explode x);
        Con (SOME $ Short "Some") [Var (Short t)]])
      inner]))
Termination
  WF_REL_TAC ‘measure (λ x . case x of
    | INL(_,e) => exp_size e
    | INR(INL(_,k,_)) => cont_size k
    | INR(INR(INL(_,_,_,es,_))) => list_size exp_size es
    | INR(INR(INR(INL(_,_,es)))) => list_size exp_size es
    | INR(INR(INR(INR(_,_,es,_)))) => list_size (exp_size o SND) es)’
  >> strip_tac >- (Cases >> rw[val_size_def, list_size_def])
  >> strip_tac >- (Cases >> rw[val_size_def, list_size_def])
  >> Induct_on ‘bs’ >- (rw[val_size_def, list_size_def])
  >> Cases
  >> rw[val_size_def, list_size_def]
  >> last_x_assum $ qspecl_then [‘e’,‘n’,‘m’,‘ce’] $ mp_tac
  >> rw[]
End

Definition scheme_program_to_cake_def:
  scheme_program_to_cake p = App Opapp [SND (cps_transform 0 p); Fun "t" $ Var (Short "t")]
End

Definition myC_def:
  (myC :('a, string, num # stamp) namespace) = Bind [
    ("SNum", (1, TypeStamp "SNum" 0));
    ("SBool", (1, TypeStamp "SBool" 0));
    ("SList", (1, TypeStamp "SList" 0));
    ("Proc", (1, TypeStamp "Proc" 0));
    ("Throw", (1, TypeStamp "Throw" 0));
    ("Prim", (1, TypeStamp "Prim" 0));
    ("Wrong", (1, TypeStamp "Wrong" 0));
    ("SAdd", (0, TypeStamp "SAdd" 1));
    ("SMul", (0, TypeStamp "SMul" 1));
    ("SMinus", (0, TypeStamp "SMinus" 1));
    ("SEqv", (0, TypeStamp "SEqv" 1));
    ("CallCC", (0, TypeStamp "CallCC" 1));
    ("cons", (2, TypeStamp "cons" 2));
    ("nil", (0, TypeStamp "nil" 2));
    ("Ex", (1, TypeStamp "Ex" 0));
    ("Some", (1, TypeStamp "Some" 3));
    ("None", (0, TypeStamp "None" 3));
  ] []
End

Definition myEnv_def:
  myEnv = <| v := let first = Bind [
    ("sadd", Recclosure <| v := nsEmpty; c := myC |> [
      ("sadd", "k", Fun "n" $ Fun "xs" $ Mat (Var (Short "xs")) [
        (Pcon (SOME $ Short "nil") [],
          App Opapp [Var (Short "k"); Con (SOME $ Short "SNum") [Var (Short "n")]]);
        (Pcon (SOME $ Short "cons") [Pvar "x"; Pvar "xs'"],
          Mat (Var (Short "x")) [
            (Pcon (SOME $ Short "SNum") [Pvar "xn"],
              App Opapp [
                App Opapp [
                  App Opapp [Var (Short "sadd"); Var (Short "k")];
                  App (Opn Plus) [Var (Short "n"); Var (Short "xn")]
                ];
                Var (Short "xs'")
              ]);
            (Pany,
              Con (SOME $ Short "Ex") [Lit $ StrLit "Not a number"])
          ])
      ])
    ] "sadd");
    ("smul", Recclosure <| v := nsEmpty; c := myC |> [
      ("smul", "k", Fun "n" $ Fun "xs" $ Mat (Var (Short "xs")) [
        (Pcon (SOME $ Short "nil") [],
          App Opapp [Var (Short "k"); Con (SOME $ Short "SNum") [Var (Short "n")]]);
        (Pcon (SOME $ Short "cons") [Pvar "x"; Pvar "xs'"],
          Mat (Var (Short "x")) [
            (Pcon (SOME $ Short "SNum") [Pvar "xn"],
              App Opapp [
                App Opapp [
                  App Opapp [Var (Short "smul"); Var (Short "k")];
                  App (Opn Times) [Var (Short "n"); Var (Short "xn")]
                ];
                Var (Short "xs'")
              ]);
            (Pany,
              Con (SOME $ Short "Ex") [Lit $ StrLit "Not a number"])
          ])
      ])
    ] "smul");
    ("seqv", Closure <| v := nsEmpty; c := myC |> "k" (Fun "xs" $
      Mat (Var (Short "xs")) [
        (Pcon (SOME $ Short "nil") [],
          Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
        (Pcon (SOME $ Short "cons") [Pvar "x1"; Pvar "xs'"],
          Mat (Var (Short "xs'")) [
            (Pcon (SOME $ Short "nil") [],
              Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
            (Pcon (SOME $ Short "cons") [Pvar "x2"; Pvar "xs''"],
              Mat (Var (Short "xs''")) [
                (Pcon (SOME $ Short "nil") [],
                  If (App Equality [Var (Short "x1"); Var (Short "x2")])
                    (App Opapp [Var (Short "k"); Con (SOME $ Short "SBool") [Lit $ IntLit 1]])
                    (App Opapp [Var (Short "k"); Con (SOME $ Short "SBool") [Lit $ IntLit 0]]));
                (Pany,
                  Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
              ])
          ])
      ]
    ));
    ("throw", Closure <| v := nsEmpty; c := myC |> "k" (Fun "xs" $
      Mat (Var (Short "xs")) [
        (Pcon (SOME $ Short "nil") [],
          Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
        (Pcon (SOME $ Short "cons") [Pvar "x"; Pvar "xs'"],
          Mat (Var (Short "xs'")) [
            (Pcon (SOME $ Short "nil") [],
              App Opapp [Var (Short "k"); Var (Short "x")]);
            (Pany,
              Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
          ])
      ]
    ));
  ] [];
  second = nsAppend first $ Bind [
    ("sminus", Closure <| v := first; c := myC |> "k" (Fun "xs" $
      Mat (Var (Short "xs")) [
        (Pcon (SOME $ Short "nil") [],
          Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
        (Pcon (SOME $ Short "cons") [Pvar "x"; Pvar "xs'"],
          Mat (Var (Short "x")) [
            (Pcon (SOME $ Short "SNum") [Pvar "n"],
              App Opapp [App Opapp [App Opapp [Var (Short "sadd");
                Fun "t" $ Mat (Var (Short "t")) [
                  (Pcon (SOME $ Short "SNum") [Pvar "m"],
                    App Opapp [Var (Short "k"); Con (SOME $ Short "SNum") [
                      App (Opn Minus) [Var (Short "n"); Var (Short "m")]]]);
                  (Pany,
                    App Opapp [Var (Short "k"); Var (Short "t")])
                ]];
                Lit $ IntLit 0]; Var (Short "xs'")]);
            (Pany,
              Con (SOME $ Short "Ex") [Lit $ StrLit "Not a number"])
          ])
      ]
    ))
  ] []
  in nsAppend second $ Bind [
    ("app", Recclosure <| v := second; c := myC |> [
      ("callcc", "k", Fun "xs" $ Mat (Var (Short "xs")) [
        (Pcon (SOME $ Short "nil") [],
          Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
        (Pcon (SOME $ Short "cons") [Pvar "x"; Pvar "xs'"],
          Mat (Var (Short "xs'")) [
            (Pcon (SOME $ Short "nil") [],
              App Opapp [
                App Opapp [
                  App Opapp [Var (Short "app");Var (Short "k")];
                  Var (Short "x")];
                Con (SOME $ Short "cons") [Con (SOME $ Short "Throw")
                  [Var (Short "k")];
                  Con (SOME $ Short "nil") []]]);
            (Pany,
              Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"])
          ])
      ]);
      ("app", "k", Fun "fn" $ Mat (Var (Short "fn")) [
        (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "SAdd") []],
          App Opapp [App Opapp [Var (Short "sadd"); Var (Short "k")]; Lit $ IntLit 0]);
        (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "SMul") []],
          App Opapp [App Opapp [Var (Short "smul"); Var (Short "k")]; Lit $ IntLit 1]);
        (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "SMinus") []],
          App Opapp [Var (Short "sminus"); Var (Short "k")]);
        (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "SEqv") []],
          App Opapp [Var (Short "seqv"); Var (Short "k")]);
        (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "CallCC") []],
          App Opapp [Var (Short "callcc"); Var (Short "k")]);
        (Pcon (SOME $ Short "Proc") [Pvar "e"],
          App Opapp [Var (Short "e"); Var (Short "k")]);
        (Pcon (SOME $ Short "Throw") [Pvar "k'"],
          App Opapp [Var (Short "throw"); Var (Short "k'")]);
        (Pany, Fun "_" $ Con (SOME $ Short "Ex") [Lit $ StrLit"Not a procedure"])
    ])
    ] "app");
  ] []
; c := myC
|>
End

Definition cake_print_def:
  cake_print e =
    (* val _ = print e; *)
    [Dlet unknown_loc Pany (App Opapp [Var (Short "print"); e])]
End

Definition codegen_def:
  (codegen (Print s)) : string + dec list =
    INR (cake_print (Lit (StrLit (explode s))))
  (*codegen _ = INR [Dlet unknown_loc Pany $ scheme_program_to_cake (cps_transform (Cond (Val $ SBool F) (Val $ SNum 420) (Val $ SNum 69)))]*)
End

val _ = export_theory();

(*
  open scheme_to_cakeTheory;
  open evaluateTheory;

  EVAL “evaluate <| clock := 999 |> myEnv [scheme_program_to_cake $ Val $ SNum 3]”
  EVAL “evaluate <| clock := 999 |> myEnv [scheme_program_to_cake (Cond (Val $ SBool F) (Val $ SNum 420) (Val $ SNum 69))]”
  EVAL “evaluate <| clock := 999 |> myEnv [scheme_program_to_cake (Apply (Val $ Prim SMinus) [Val $ SNum 2; Val $ SNum 3])]”
  EVAL “evaluate <| clock := 999 |> myEnv [scheme_program_to_cake (Apply (Val $ Prim SEqv) [Val $ SNum 2; Val $ SNum 2])]”
  EVAL “evaluate <| clock := 999; refs := [] |> myEnv [scheme_program_to_cake (Apply (Lambda [strlit "x"] NONE (Begin (Set (strlit "x") (Val $ SNum 7)) [Ident $ strlit "x"])) [Val $ SNum 5])]”
  EVAL “SND $ evaluate <| clock := 999; refs := [] |> myEnv [scheme_program_to_cake (
    Letrec [(strlit "f", Lambda [strlit "b"; strlit "x"] NONE (
      Cond (Ident $ strlit "b")
        (Apply (Val $ Prim SMul) [Val $ SNum 2; Ident $ strlit "x"])
        (Apply (Ident $ strlit "f") [Val $ SBool T; Apply
          (Val $ Prim SAdd) [Val $ SNum 1; Ident $ strlit "x"]])
    ))] (
      Apply (Ident $ strlit "f") [Val $ SBool F; Val $ SNum 7]
    )
  )]”
  EVAL “SND $ evaluate <| clock := 999; refs := [] |> myEnv [scheme_program_to_cake (
    Letrec [(strlit "fac", Lambda [strlit "x"] NONE (
      Cond (Apply (Val $ Prim SEqv) [Ident $ strlit "x"; Val $ SNum 0]) (
        Val $ SNum 1
      ) (
        Apply (Val $ Prim SMul) [Ident $ strlit "x"; Apply (Ident $ strlit "fac") [
          Apply (Val $ Prim SMinus) [Ident $ strlit "x"; Val $ SNum 1]
        ]]
      )
    ))] (Apply (Ident $ strlit "fac") [Val $ SNum 6]))]”
  EVAL “SND $ evaluate <| clock := 999; refs := [] |> myEnv [scheme_program_to_cake (
    Apply (Val $ Prim SMul) [
      Val $ SNum 2;
      Apply (Val $ Prim CallCC) [ Lambda [strlit "x"] NONE (
        Apply (Val $ Prim SAdd) [
          Val $ SNum 4;
          Cond (Val $ SBool T) (
            Val $ SNum 3
          ) (
            Apply (Ident $ strlit "x") [Val $ SNum 5]
          )
        ]
      )]
    ]
  )]”
  EVAL “SND $ evaluate <| clock := 999; refs := [] |> myEnv [scheme_program_to_cake (
    Letrec [(strlit "fac", Lambda [strlit "x"] NONE (
      Letrec [(strlit "st", Val $ SNum 0); (strlit "acc", Val $ SNum 1)] (
        Begin ( Apply (Val $ Prim CallCC) [ Lambda [strlit "k"] NONE (
          Set (strlit "st") (Ident $ strlit "k")
        )]) [
          Cond (Apply (Val $ Prim SEqv) [Ident $ strlit "x"; Val $ SNum 0])
            (Ident $ strlit "acc")
            (Apply (Ident $ strlit "st") [ Begin (
              Set (strlit "acc") (Apply (Val $ Prim SMul) [
                Ident $ strlit "acc";
                Ident $ strlit "x"
              ])
            ) [
              Set (strlit "x") (Apply (Val $ Prim SMinus) [
                Ident $ strlit "x";
                Val $ SNum 1
              ])
            ]])
        ]
      )
    ))] (Apply (Ident $ strlit "fac") [Val $ SNum 6])
  )]”
  EVAL “scheme_program_to_cake (Cond (Val $ SBool F) (Val $ SNum 420) (Val $ SNum 69))”
  EVAL “scheme_program_to_cake (Apply (Val $ Prim SMul) [Val $ SNum 2; Val $ SNum 3])”
  EVAL “scheme_program_to_cake (Apply (Lambda [] (SOME $ strlit "x") (Ident $ strlit "x")) [Val $ SNum 5])”
  EVAL “scheme_program_to_cake (Begin (Val $ SNum 0) [Val $ SNum 1; Val $ SNum 2])”
  EVAL “scheme_program_to_cake (Letrec [(strlit "x", Val $ SNum 1)] (Ident $ strlit "x"))”
  EVAL “SND $ evaluate <| clock := 999; refs := [] |> myEnv [scheme_program_to_cake (Apply (Val $ Prim CallCC) [Lambda [strlit "x"] NONE $ Apply (Ident $ strlit "x") [Val $ SNum 5]])]”
*)