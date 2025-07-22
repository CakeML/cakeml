(*
  Code generator for Scheme to CakeML compiler
*)
open preamble;
open astTheory;
open scheme_astTheory;

open semanticPrimitivesTheory;
open namespaceTheory;

val _ = new_theory "scheme_to_cake";

Definition lit_to_ml_val_def:
  lit_to_ml_val (LitPrim p) = Con (SOME $ Short "Prim") [case p of
  | SAdd => Con (SOME $ Short "SAdd") []
  | SMul => Con (SOME $ Short "SMul") []
  | SMinus => Con (SOME $ Short "SMinus") []
  | SEqv => Con (SOME $ Short "SEqv") []
  | CallCC => Con (SOME $ Short "CallCC") []
  | Cons => Con (SOME $ Short "Cons") []
  | Car => Con (SOME $ Short "Car") []
  | Cdr => Con (SOME $ Short "Cdr") []
  | IsNull => Con (SOME $ Short "IsNull") []
  | IsPair => Con (SOME $ Short "IsPair") []] ∧
  lit_to_ml_val (LitNum n) = Con (SOME $ Short "SNum") [Lit $ IntLit n] ∧
  lit_to_ml_val (LitBool b) = Con (SOME $ Short "SBool") [Con (SOME $ Short
    if b then "True" else "False") []] ∧
  lit_to_ml_val LitNull = Con (SOME $ Short "Null") []
End

Definition cons_list_def:
  cons_list [] = Con (SOME $ Short "[]") [] ∧
  cons_list (x::xs) = Con (SOME $ Short "::") [x; cons_list xs]
End

Definition proc_ml_def:
  proc_ml [] NONE k ce = Mat (Var (Short "ts")) [
        (Pcon (SOME $ Short "[]") [],
          App Opapp [ce; Var (Short k)]);
        (Pany,
          Con (SOME $ Short "Ex") [Lit $ StrLit "Wrong number of arguments"])
    ] ∧
  proc_ml [] (SOME x) k ce = Let (SOME $ "var" ++ explode x)
      (App Opref [Con (SOME $ Short "Some") [
        App Opapp [Var (Short "allocate_list"); Var (Short "ts")]]])
      (App Opapp [ce; Var (Short k)]) ∧
  proc_ml (x::xs) xp k ce = (let
    inner = proc_ml xs xp k ce
  in
    Mat (Var (Short "ts")) [
        (Pcon (SOME $ Short "[]") [],
          Con (SOME $ Short "Ex") [Lit $ StrLit "Wrong number of arguments"]);
        (Pcon (SOME $ Short "::") [Pvar "t"; Pvar "ts"],
          Let (SOME $ "var" ++ explode x)
            (App Opref [Con (SOME $ Short "Some") [Var (Short "t")]])
            inner)
    ])
End

Definition letpreinit_ml_def:
  letpreinit_ml [] inner = inner ∧
  letpreinit_ml (x::xs) inner = Let (SOME $ "var" ++ explode x)
      (App Opref [Con (SOME $ Short "None") []]) (letpreinit_ml xs inner)
End

Definition refunc_set_def:
  refunc_set t k x = Let NONE (App Opassign [Var (Short $ "var" ++ explode x);
              Con (SOME $ Short "Some") [t]]) $
            Let (SOME "t") (Con (SOME $ Short "Wrong") [Lit $ StrLit "Unspecified"])
              (App Opapp [k; Var (Short "t")])
End

Definition letinit_ml_def:
  letinit_ml [] inner = inner ∧
  letinit_ml ((x,t)::xts) inner = Let NONE
    (App Opassign [Var (Short $ "var" ++ explode x);
      Con (SOME $ Short "Some") [t]]) $
    letinit_ml xts inner
End

Definition cps_transform_def:
  cps_transform (Lit v) = (let
    mlv = lit_to_ml_val v
  in
    Fun "k" $ Let (SOME "t") mlv $
      App Opapp [Var (Short "k"); Var (Short "t")]) ∧

  cps_transform (Cond c t f) = (let
    cc = cps_transform c;
    ct = cps_transform t;
    cf = cps_transform f;
  in
    Fun "k" $ Let (SOME "k'") (Fun "t" $ Mat (Var (Short "t")) [
      (Pcon (SOME $ Short "SBool") [Pcon (SOME $ Short "False") []],
        App Opapp [cf; Var (Short "k")]);
      (Pany,
        App Opapp [ct; Var (Short "k")])
    ]) $ App Opapp [cc; Var (Short "k'")]) ∧

  cps_transform (Apply fn args) = (let
    cfn = cps_transform fn;
    capp = cps_transform_app (Var (Short "t")) [] args (Var (Short "k"))
  in
    Fun "k" $ Let (SOME "k'") (Fun "t" capp) $ App Opapp [cfn; Var (Short "k'")]) ∧

  cps_transform (Ident x) = Fun "k" $ Mat (App Opderef [Var (Short $ "var" ++ explode x)]) [
      (Pcon (SOME $ Short "None") [],
        Con (SOME $ Short "Ex") [Lit $ StrLit "Letrec variable touched"]);
      (Pcon (SOME $ Short "Some") [Pvar "t"],
        App Opapp [Var (Short "k"); Var (Short "t")])] ∧

  cps_transform (Lambda xs xp e) = (let
    ce = cps_transform e;
    inner = proc_ml xs xp "k" ce;
  in
    Fun "k" $ Let (SOME "t")
      (Con (SOME $ Short "Proc") [Fun "k" $ Fun "ts" inner]) $
      App Opapp [Var (Short "k"); Var (Short "t")]) ∧

  cps_transform (Begin es e) = (let
      inner = cps_transform_seq (Var (Short "k")) es e
    in
      Fun "k" inner) ∧

  cps_transform (Set x e) = (let
    ce = cps_transform e;
    inner = refunc_set (Var (Short "t")) (Var (Short "k")) x;
  in
    Fun "k" $ Let (SOME "k'") (Fun "t" inner) $ App Opapp [ce; Var (Short "k'")]) ∧

  cps_transform (Letrec bs e) = (let
    inner = cps_transform_letinit [] bs e (Var (Short "k"));
  in
    Fun "k" $ letpreinit_ml (MAP FST bs) $ inner) ∧

  cps_transform (Letrecstar bs e) = (let
    ce = cps_transform (Begin (MAP (UNCURRY Set) bs) e);
  in
    Fun "k" $ letpreinit_ml (MAP FST bs) $ App Opapp [ce; Var (Short "k")]) ∧


  cps_transform_app tfn ts (e::es) k = (let
    ce = cps_transform e;
    t = "t" ++ toString (LENGTH ts);
    inner = cps_transform_app tfn (Var (Short t)::ts) es k
  in
    Let (SOME "k'") (Fun t inner) $ App Opapp [ce; Var (Short "k'")]) ∧

  cps_transform_app tfn ts [] k = App Opapp [
      App Opapp [App Opapp [Var (Short "app"); k]; tfn];
      cons_list (REVERSE ts)] ∧


  cps_transform_letinit xts [] e k = (let
    ce = cps_transform e
  in
    letinit_ml xts $ App Opapp [ce; k]) ∧

  cps_transform_letinit xts ((x, e')::bs) e k = (let
    ce = cps_transform e';
    t = "t" ++ toString (LENGTH xts);
    inner = cps_transform_letinit ((x, Var (Short t))::xts) bs e k
  in
    Let (SOME "k'") (Fun t inner) $ App Opapp [ce; Var (Short "k'")]) ∧


  cps_transform_seq k [] e = (let
    ce = cps_transform e
  in
    App Opapp [ce; k]) ∧

  cps_transform_seq k (e'::es) e = (let
    ce = cps_transform e';
    inner = cps_transform_seq k es e
  in
     Let (SOME "k'") (Fun "_" inner) $ App Opapp [ce; Var (Short "k'")])
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λ x . case x of
    | INL(e) => (exp_size e, case e of Letrecstar _ _ => 1 | _ => 0)
    | INR(INL(_,_,es,_)) => (list_size exp_size es, 2n)
    | INR(INR(INL(_,bs,e,_))) => (exp1_size bs + exp_size e, 2)
    | INR(INR(INR(_,es,e))) => (list_size exp_size es + exp_size e, 2))’
  >> rpt conj_tac
  >> simp[exp_size_def]
  >> rpt (Cases >> simp[] >> NO_TAC)
  >> Induct
  >> simp[exp_size_def]
  >> PairCases
  >> simp[exp_size_def]
End

Definition compile_scheme_prog_def:
  compile_scheme_prog p = let
    cp = cps_transform p
  in
    Let (SOME $ "k") (Fun "t" $ Var (Short "t")) $
      App Opapp [cp; Var (Short "k")]
End

Definition cake_print_def:
  cake_print e =
    (* val _ = print e; *)
    [Dlet unknown_loc Pany (App Opapp [Var (Short "print"); e])]
End

Definition scheme_basis_types_def:
  scheme_basis_types = Dtype unknown_loc [
    ([], "sprim", [
      ("SAdd", []);
      ("SMul", []);
      ("SMinus", []);
      ("SEqv", []);
      ("CallCC", []);
      ("Cons", []);
      ("Car", []);
      ("Cdr", []);
      ("IsNull", []);
      ("IsPair", [])
    ]);
    ([], "sval", [
      ("SNum", [Atapp [] (Short "int")]);
      ("SBool", [Atapp [] (Short "bool")]);
      ("Prim", [Atapp [] (Short "sprim")]);
      ("Null", []);
      ("PairP", [Atapp [] (Short "sval")]);
      ("Wrong", [Atapp [] (Short "string")]);
      ("Ex", [Atapp [] (Short "string")]);
      ("Proc", [Atfun
                 (Atfun
                   (Atapp [] (Short "sval"))
                   (Atapp [] (Short "sval")))
                 (Atfun
                   (Atapp [Atapp [] (Short "sval")] (Short "list"))
                   (Atapp [] (Short "sval")))]);
      ("Throw", [Atfun
                  (Atapp [] (Short "sval"))
                  (Atapp [] (Short "sval"))]);
    ])
  ]
End

Definition scheme_basis_def:
  scheme_basis = [
    Dletrec unknown_loc [
      ("sadd", "k", Fun "n" $ Fun "ts" $ Mat (Var (Short "ts")) [
        (Pcon (SOME $ Short "[]") [],
          Let (SOME "t") (Con (SOME $ Short "SNum") [Var (Short "n")]) $
            App Opapp [Var (Short "k"); Var (Short "t")]);
        (Pcon (SOME $ Short "::") [Pvar "t"; Pvar "ts'"],
          Mat (Var (Short "t")) [
            (Pcon (SOME $ Short "SNum") [Pvar "tn"],
              App Opapp [
                App Opapp [
                  App Opapp [Var (Short "sadd"); Var (Short "k")];
                  App (Opn Plus) [Var (Short "n"); Var (Short "tn")]
                ];
                Var (Short "ts'")
              ]);
            (Pany,
              Con (SOME $ Short "Ex") [Lit $ StrLit "Arith-op applied to non-number"])
          ])
      ])
    ];

    Dletrec unknown_loc [
      ("smul", "k", Fun "n" $ Fun "ts" $ Mat (Var (Short "ts")) [
        (Pcon (SOME $ Short "[]") [],
          Let (SOME "t") (Con (SOME $ Short "SNum") [Var (Short "n")]) $
            App Opapp [Var (Short "k"); Var (Short "t")]);
        (Pcon (SOME $ Short "::") [Pvar "t"; Pvar "ts'"],
          Mat (Var (Short "t")) [
            (Pcon (SOME $ Short "SNum") [Pvar "tn"],
              App Opapp [
                App Opapp [
                  App Opapp [Var (Short "smul"); Var (Short "k")];
                  App (Opn Times) [Var (Short "n"); Var (Short "tn")]
                ];
                Var (Short "ts'")
              ]);
            (Pany,
              Con (SOME $ Short "Ex") [Lit $ StrLit "Arith-op applied to non-number"])
          ])
      ])
    ];

    Dlet unknown_loc (Pvar "sminus") $ Fun "k" $ Fun "ts" $
      Mat (Var (Short "ts")) [
        (Pcon (SOME $ Short "[]") [],
          Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
        (Pcon (SOME $ Short "::") [Pvar "t"; Pvar "ts'"],
          Mat (Var (Short "t")) [
            (Pcon (SOME $ Short "SNum") [Pvar "n"],
              Mat (Var (Short "ts'")) [
                (Pcon (SOME $ Short "[]") [],
                  Let (SOME "t") (Con (SOME $ Short "SNum") [
                      App (Opn Minus) [Lit $ IntLit 0; Var (Short "n")]]) $
                    App Opapp [Var (Short "k"); Var (Short "t")]);
                (Pany, App Opapp [App Opapp [App Opapp [Var (Short "sadd");
                  Fun "t" $ Mat (Var (Short "t")) [
                    (Pcon (SOME $ Short "SNum") [Pvar "m"],
                      Let (SOME "t") (Con (SOME $ Short "SNum") [
                          App (Opn Minus) [Var (Short "n"); Var (Short "m")]]) $
                        App Opapp [Var (Short "k"); Var (Short "t")]);
                    (Pany,
                      App Opapp [Var (Short "k"); Var (Short "t")])
                  ]];
                  Lit $ IntLit 0]; Var (Short "ts'")])
              ]);
            (Pany,
              Con (SOME $ Short "Ex") [Lit $ StrLit "Arith-op applied to non-number"])
          ])
      ];

    Dlet unknown_loc (Pvar "seqv") $ Fun "k" $ Fun "ts" $
      Mat (Var (Short "ts")) [
        (Pcon (SOME $ Short "[]") [],
          Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
        (Pcon (SOME $ Short "::") [Pvar "t1"; Pvar "ts'"],
          Mat (Var (Short "ts'")) [
            (Pcon (SOME $ Short "[]") [],
              Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
            (Pcon (SOME $ Short "::") [Pvar "t2"; Pvar "ts''"],
              Mat (Var (Short "ts''")) [
                (Pcon (SOME $ Short "[]") [],
                  (Let (SOME "t") (Con (SOME $ Short "SBool") [
                    Mat (Var (Short "t1")) [
                      (Pcon (SOME $ Short "SNum") [Pvar "n"],
                        Mat (Var (Short "t2")) [
                          (Pcon (SOME $ Short "SNum") [Pvar "m"],
                            App Equality [Var (Short "n"); Var (Short "m")]);
                          (Pany,
                            Con (SOME $ Short "False") [])
                        ]);
                      (Pcon (SOME $ Short "SBool") [Pvar "b"],
                        Mat (Var (Short "t2")) [
                          (Pcon (SOME $ Short "SBool") [Pvar "b'"],
                            App Equality [Var (Short "b"); Var (Short "b'")]);
                          (Pany,
                            Con (SOME $ Short "False") [])
                        ]);
                      (Pany,
                        Con (SOME $ Short "False") [])
                      ]]) $ App Opapp [Var (Short "k"); Var (Short "t")]));
                (Pany,
                  Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"])
              ])
          ])
      ];

    Dlet unknown_loc (Pvar "cons") $ Fun "k" $ Fun "ts" $
      Mat (Var (Short "ts")) [
        (Pcon (SOME $ Short "[]") [],
          Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
        (Pcon (SOME $ Short "::") [Pvar "t1"; Pvar "ts'"],
          Mat (Var (Short "ts'")) [
            (Pcon (SOME $ Short "[]") [],
              Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
            (Pcon (SOME $ Short "::") [Pvar "t2"; Pvar "ts''"],
              Mat (Var (Short "ts''")) [
                (Pcon (SOME $ Short "[]") [],
                  Let (SOME "t") (Con (SOME $ Short "PairP") [
                                    App AallocFixed [Var (Short "t1"); Var (Short "t2")]
                                  ]) $
                    App Opapp [Var (Short "k"); Var (Short "t")]);
                (Pany,
                  Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"])
              ])
          ])
      ];

    Dlet unknown_loc (Pvar "car") $ Fun "k" $ Fun "ts" $
      Mat (Var (Short "ts")) [
        (Pcon (SOME $ Short "[]") [],
          Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
        (Pcon (SOME $ Short "::") [Pvar "t"; Pvar "ts'"],
          Mat (Var (Short "ts'")) [
            (Pcon (SOME $ Short "[]") [],
              Mat (Var (Short "t")) [
                (Pcon (SOME $ Short "PairP") [Pvar "pp"],
                  Let (SOME "t") (App Asub [Var (Short "pp"); Lit (IntLit 0)]) $
                    App Opapp [Var (Short "k"); Var (Short "t")]);
                (Pany,
                  Con (SOME $ Short "Ex") [Lit $ StrLit "Can't take car of non-pair"])
              ]);
            (Pany,
              Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
          ])
      ];

    Dlet unknown_loc (Pvar "cdr") $ Fun "k" $ Fun "ts" $
      Mat (Var (Short "ts")) [
        (Pcon (SOME $ Short "[]") [],
          Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
        (Pcon (SOME $ Short "::") [Pvar "t"; Pvar "ts'"],
          Mat (Var (Short "ts'")) [
            (Pcon (SOME $ Short "[]") [],
              Mat (Var (Short "t")) [
                (Pcon (SOME $ Short "PairP") [Pvar "pp"],
                  Let (SOME "t") (App Asub [Var (Short "pp"); Lit (IntLit 1)]) $
                    App Opapp [Var (Short "k"); Var (Short "t")]);
                (Pany,
                  Con (SOME $ Short "Ex") [Lit $ StrLit "Can't take cdr of non-pair"])
              ]);
            (Pany,
              Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
          ])
      ];

    Dlet unknown_loc (Pvar "isnull") $ Fun "k" $ Fun "ts" $
      Mat (Var (Short "ts")) [
        (Pcon (SOME $ Short "[]") [],
          Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
        (Pcon (SOME $ Short "::") [Pvar "t"; Pvar "ts'"],
          Mat (Var (Short "ts'")) [
            (Pcon (SOME $ Short "[]") [],
              Let (SOME "t") (Mat (Var (Short "t")) [
                (Pcon (SOME $ Short "Null") [],
                  Con (SOME $ Short "SBool") [Con (SOME $ Short "True") []]);
                (Pany,
                  Con (SOME $ Short "SBool") [Con (SOME $ Short "False") []])
              ]) $ App Opapp [Var (Short "k"); Var (Short "t")]);
            (Pany,
              Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
          ])
      ];

    Dlet unknown_loc (Pvar "ispair") $ Fun "k" $ Fun "ts" $
      Mat (Var (Short "ts")) [
        (Pcon (SOME $ Short "[]") [],
          Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
        (Pcon (SOME $ Short "::") [Pvar "t"; Pvar "ts'"],
          Mat (Var (Short "ts'")) [
            (Pcon (SOME $ Short "[]") [],
              Let (SOME "t") (Mat (Var (Short "t")) [
                (Pcon (SOME $ Short "PairP") [Pany],
                  Con (SOME $ Short "SBool") [Con (SOME $ Short "True") []]);
                (Pany,
                  Con (SOME $ Short "SBool") [Con (SOME $ Short "False") []])
              ]) $ App Opapp [Var (Short "k"); Var (Short "t")]);
            (Pany,
              Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
          ])
      ];

    Dlet unknown_loc (Pvar "throw") $ Fun "k" $ Fun "ts" $
      Mat (Var (Short "ts")) [
        (Pcon (SOME $ Short "[]") [],
          Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
        (Pcon (SOME $ Short "::") [Pvar "t"; Pvar "ts'"],
          Mat (Var (Short "ts'")) [
            (Pcon (SOME $ Short "[]") [],
              App Opapp [Var (Short "k"); Var (Short "t")]);
            (Pany,
              Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
          ])
      ];
  ]
End

Definition scheme_basis_list_def:
  scheme_basis_list = Dletrec unknown_loc [
    ("allocate_list", "ts", Mat (Var (Short "ts")) [
      (Pcon (SOME $ Short "[]") [],
        Con (SOME $ Short "Null") []);
      (Pcon (SOME $ Short "::") [Pvar "t"; Pvar "ts'"],
        Con (SOME $ Short "PairP") [
          App AallocFixed [
            Var (Short "t");
            App Opapp [Var (Short "allocate_list"); Var (Short "ts'")]
          ]
        ])
    ])
  ]
End

Definition scheme_basis_app_def:
  scheme_basis_app = Dletrec unknown_loc [
    ("callcc", "k", Fun "ts" $ Mat (Var (Short "ts")) [
      (Pcon (SOME $ Short "[]") [],
        Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
      (Pcon (SOME $ Short "::") [Pvar "t"; Pvar "ts"],
        Mat (Var (Short "ts")) [
          (Pcon (SOME $ Short "[]") [],
            Let (SOME "k'") (
              Fun "t0" $ App Opapp [
                App Opapp [
                  App Opapp [Var (Short "app");Var (Short "k")];
                  Var (Short "t")];
                cons_list [Var (Short "t0")]]
            ) $ Let (SOME "t") (Con (SOME $ Short "Throw") [Var (Short "k")]) $
              App Opapp [Var (Short "k'"); Var (Short "t")]);
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
      (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "Cons") []],
        App Opapp [Var (Short "cons"); Var (Short "k")]);
      (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "Car") []],
        App Opapp [Var (Short "car"); Var (Short "k")]);
      (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "Cdr") []],
        App Opapp [Var (Short "cdr"); Var (Short "k")]);
      (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "IsNull") []],
        App Opapp [Var (Short "isnull"); Var (Short "k")]);
      (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "IsPair") []],
        App Opapp [Var (Short "ispair"); Var (Short "k")]);
      (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "CallCC") []],
        App Opapp [Var (Short "callcc"); Var (Short "k")]);
      (Pcon (SOME $ Short "Proc") [Pvar "e"],
        App Opapp [Var (Short "e"); Var (Short "k")]);
      (Pcon (SOME $ Short "Throw") [Pvar "k'"],
        App Opapp [Var (Short "throw"); Var (Short "k'")]);
      (Pany, Fun "_" $ Con (SOME $ Short "Ex") [Lit $ StrLit"Not a procedure"])
    ])
  ]
End

Definition codegen_def:
  codegen p = INR $ [scheme_basis_types] ++ scheme_basis ++ [scheme_basis_list; scheme_basis_app] ++ [
    Dlet unknown_loc (Pvar "res") $ compile_scheme_prog p;
    Dlet unknown_loc Pany $ Mat (Var (Short "res")) [
      (Pcon (SOME $ Short "SNum") [Pvar "n"],
        App Opapp [Var (Short "print_int"); Var (Short "n")]);
      (Pcon (SOME $ Short "SBool") [Pcon (SOME $ Short "True") []],
        App Opapp [Var (Short "print"); Lit $ StrLit "#t"]);
      (Pcon (SOME $ Short "SBool") [Pcon (SOME $ Short "False") []],
        App Opapp [Var (Short "print"); Lit $ StrLit "#f"]);
      (Pcon (SOME $ Short "Ex") [Pvar "ex"],
        App Opapp [Var (Short "print"); Var (Short "ex")]);
      (Pcon (SOME $ Short "Wrong") [Pany],
        App Opapp [Var (Short "print"); Lit $ StrLit "unspecified"]);
      (Pany, App Opapp [Var (Short "print"); Lit $ StrLit "proc"])
    ]
  ]
End

(*
open scheme_parsingTheory;
open scheme_to_cakeTheory;
EVAL “cps_transform $ OUTR $ parse_to_ast
"(cons 1 2)"”
*)

val _ = export_theory();
