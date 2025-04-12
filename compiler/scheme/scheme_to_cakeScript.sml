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
  to_ml_vals (SBool b) = Con (SOME $ Short "SBool") [Con (SOME $ Short
    if b then "True" else "False") []] ∧
  (*following temporary, needed for proofs*)
  to_ml_vals _ = Con (SOME $ Short "Ex") [Lit $ StrLit "Not supported"]
End

Definition cons_list_def:
  cons_list [] = Con (SOME $ Short "[]") [] ∧
  cons_list (x::xs) = Con (SOME $ Short "::") [x; cons_list xs]
End

Definition proc_ml_def:
  proc_ml n [] NONE k args ce = (n, Mat (Var (Short args)) [
        (Pcon (SOME $ Short "[]") [],
          App Opapp [ce; Var (Short k)]);
        (Pany,
          Con (SOME $ Short "Ex") [Lit $ StrLit "Wrong number of arguments"])
    ]) ∧
  proc_ml n [] (SOME x) k args ce = (n, Let (SOME $ "var" ++ explode x)
      (App Opref [Con (SOME $ Short "Some") [
        Con (SOME $ Short "SList") [Var (Short args)]]])
      (App Opapp [ce; Var (Short k)])) ∧
  proc_ml n (x::xs) xp k args ce = (let
    arg = "x" ++ toString n;
    args' = "xs" ++ toString (n+1);
    (m, inner) = proc_ml (n+2) xs xp k args' ce
  in
    (m, Mat (Var (Short args)) [
        (Pcon (SOME $ Short "[]") [],
          Con (SOME $ Short "Ex") [Lit $ StrLit "Wrong number of arguments"]);
        (Pcon (SOME $ Short "::") [Pvar arg; Pvar args'],
          Let (SOME $ "var" ++ explode x)
            (App Opref [Con (SOME $ Short "Some") [Var (Short arg)]])
            inner)
    ]))
End

Definition letinit_ml_def:
  letinit_ml [] inner = inner ∧
  letinit_ml ((x,_)::bs) inner = Let (SOME $ "var" ++ explode x)
      (App Opref [Con (SOME $ Short "None") []]) (letinit_ml bs inner)
End

Definition cps_transform_def:
  cps_transform n (Lit v) = (let
    k = "k" ++ toString n;
    mlv = to_ml_vals $ lit_to_val v
  in
    (n+1, Fun k $ Let (SOME "v") mlv $
      App Opapp [Var (Short k); Var (Short "v")])) ∧

  cps_transform n (Cond c t f) = (let
    (m, cc) = cps_transform n c;
    (l, ct) = cps_transform m t;
    (j, cf) = cps_transform l f;
    k = "k" ++ toString j;
    p = "t" ++ toString (j+1);
  in
    (j+2, Fun k $ Let (SOME "k") (Fun p $ Mat (Var (Short p)) [
      (Pcon (SOME $ Short "SBool") [Pcon (SOME $ Short "False") []],
        App Opapp [cf; Var (Short k)]);
      (Pany,
        App Opapp [ct; Var (Short k)])
    ]) $ App Opapp [cc; Var (Short "k")])) ∧

  cps_transform n (Apply fn args) = (let
    (m, cfn) = cps_transform n fn;
    k = "k" ++ toString m;
    t = "t" ++ toString (m+1);
    (l, capp) = cps_transform_app (m+2) (Var (Short t)) [] args (Var (Short k))
  in
    (l, Fun k $ Let (SOME "k") (Fun t capp) $ App Opapp [cfn; Var (Short "k")])) ∧

  cps_transform n (Ident x) = (let k = "k" ++ toString n in
    (n, Fun k $ Mat (App Opderef [Var (Short $ "var" ++ explode x)]) [
      (Pcon (SOME $ Short "None") [],
        Con (SOME $ Short "Ex") [Lit $ StrLit "Letrec variable touched"]);
      (Pcon (SOME $ Short "Some") [Pvar $ "'var" ++ explode x],
        App Opapp [Var (Short k); Var (Short $ "'var" ++ explode x)])])) ∧

  cps_transform n (Lambda xs xp e) = (let
    (m, ce) = cps_transform n e;
    args = "xs" ++ toString m;
    k = "k" ++ toString (m+1);
    (l, inner) = proc_ml (m+2) xs xp k args ce;
    k' = "k" ++ toString l;
  in
    (l+1, Fun k' $ Let (SOME "v")
      (Con (SOME $ Short "Proc") [Fun k $ Fun args inner]) $
      App Opapp [Var (Short k'); Var (Short "v")])) ∧

  cps_transform n (Begin es e) = (let
      k = "k" ++ toString n;
      (m, ce) = cps_transform_seq (n+1) (Var (Short k)) es e
    in
      (m, Fun k ce)) ∧

  cps_transform n (Set x e) = (let
    (m, ce) = cps_transform n e;
    k = "k" ++ toString m;
    t = "t" ++ toString (m+1);
  in
    (m+2, Fun k $ Let (SOME "k")
      (Fun t $ Let NONE (App Opassign [Var (Short $ "var" ++ explode x);
            Con (SOME $ Short "Some") [Var (Short t)]]) $
          Let (SOME "v") (Con (SOME $ Short "Wrong") [Lit $ StrLit "Unspecified"])
            (App Opapp [Var (Short k); Var (Short "v")])) $
        App Opapp [ce; Var (Short "k")])) ∧

  cps_transform n (Letrec bs e) = (let
    (m, ce) = cps_transform n e;
    k = "k" ++ toString m;
    (l, inner) = cps_transform_letreinit (m+1) (Var (Short k)) bs ce
  in
    (l, Fun k $ letinit_ml bs inner)) ∧


  cps_transform_app n tfn ts (e::es) k = (let
    (m, ce) = cps_transform n e;
    t = "t" ++ toString m;
    (l, inner) = cps_transform_app (m+1) tfn (Var (Short t)::ts) es k
  in
    (l, Let (SOME "k") (Fun t inner) $ App Opapp [ce; Var (Short "k")])) ∧

  cps_transform_app n tfn ts [] k = (n,
    App Opapp [
      App Opapp [App Opapp [Var (Short "app"); k]; tfn];
      cons_list (REVERSE ts)]) ∧


  cps_transform_seq n k [] e = (let
    (m, ce) = cps_transform n e
  in
    (n, App Opapp [ce; k])) ∧

  cps_transform_seq n k (e'::es) e = (let
    (m, ce) = cps_transform n e';
    (l, inner) = cps_transform_seq m k es e
  in
    (l, Let (SOME "k") (Fun "_" $ inner) $ App Opapp [ce; Var (Short "k")])) ∧


  cps_transform_letreinit n k [] ce = (n, App Opapp [ce; k]) ∧

  cps_transform_letreinit n k ((x,e)::bs) ce = (let
    (m, ce') = cps_transform n e;
    (l, inner) = cps_transform_letreinit m k bs ce;
    t = "t" ++ toString l
  in
    (l+1, App Opapp [ce'; Fun t $ Let NONE
      (App Opassign [Var (Short $ "var" ++ explode x);
        Con (SOME $ Short "Some") [Var (Short t)]])
      inner]))
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λ x . case x of
    | INL(_,e) => (exp_size e, 0)
    | INR(INL(_,_,_,es,_)) => (list_size exp_size es, 1n)
    | INR(INR(INL(_,_,es,e))) => (list_size exp_size es + exp_size e, 1)
    | INR(INR(INR(_,_,bs,_))) => (exp1_size bs), 1)’
End

Definition compile_scheme_prog_def:
  compile_scheme_prog p = let
    (n, cp) = cps_transform 0 p
  in
    Let (SOME $ "k") (Fun "t" $ Var (Short "t")) $
      App Opapp [cp; Var (Short "k")]
End

Definition cake_print_def:
  cake_print e =
    (* val _ = print e; *)
    [Dlet unknown_loc Pany (App Opapp [Var (Short "print"); e])]
End

Definition scheme_basis1_def:
  scheme_basis1 = Dtype unknown_loc [
    ([], "sprim", [
      ("SAdd", []);
      ("SMul", []);
      ("SMinus", []);
      ("SEqv", []);
      ("CallCC", [])
    ]);
    ([], "sval", [
      ("SNum", [Atapp [] (Short "int")]);
      ("SBool", [Atapp [] (Short "bool")]);
      ("Prim", [Atapp [] (Short "sprim")]);
      ("SList", [Atapp [Atapp [] (Short "sval")] (Short "list")]);
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

Definition scheme_basis2_def:
  scheme_basis2 = Dletrec unknown_loc [
    ("sadd", "k", Fun "n" $ Fun "xs" $ Mat (Var (Short "xs")) [
      (Pcon (SOME $ Short "[]") [],
        Let (SOME "v") (Con (SOME $ Short "SNum") [Var (Short "n")]) $
          App Opapp [Var (Short "k"); Var (Short "v")]);
      (Pcon (SOME $ Short "::") [Pvar "x"; Pvar "xs'"],
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
            Con (SOME $ Short "Ex") [Lit $ StrLit "Arith-op applied to non-number"])
        ])
    ])
  ]
End

Definition scheme_basis3_def:
  scheme_basis3 = Dletrec unknown_loc [
    ("smul", "k", Fun "n" $ Fun "xs" $ Mat (Var (Short "xs")) [
      (Pcon (SOME $ Short "[]") [],
        Let (SOME "v") (Con (SOME $ Short "SNum") [Var (Short "n")]) $
          App Opapp [Var (Short "k"); Var (Short "v")]);
      (Pcon (SOME $ Short "::") [Pvar "x"; Pvar "xs'"],
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
            Con (SOME $ Short "Ex") [Lit $ StrLit "Arith-op applied to non-number"])
        ])
    ])
  ]
End

Definition scheme_basis4_def:
  scheme_basis4 = Dlet unknown_loc (Pvar "sminus") $ Fun "k" $ Fun "xs" $
    Mat (Var (Short "xs")) [
      (Pcon (SOME $ Short "[]") [],
        Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
      (Pcon (SOME $ Short "::") [Pvar "x"; Pvar "xs'"],
        Mat (Var (Short "x")) [
          (Pcon (SOME $ Short "SNum") [Pvar "n"],
            App Opapp [App Opapp [App Opapp [Var (Short "sadd");
              Fun "t" $ Mat (Var (Short "t")) [
                (Pcon (SOME $ Short "SNum") [Pvar "m"],
                  Let (SOME "v") (Con (SOME $ Short "SNum") [
                      App (Opn Minus) [Var (Short "n"); Var (Short "m")]]) $
                    App Opapp [Var (Short "k"); Var (Short "v")]);
                (Pany,
                  App Opapp [Var (Short "k"); Var (Short "t")])
              ]];
              Lit $ IntLit 0]; Var (Short "xs'")]);
          (Pany,
            Con (SOME $ Short "Ex") [Lit $ StrLit "Arith-op applied to non-number"])
        ])
    ]
End

Definition scheme_basis5_def:
  scheme_basis5 = Dlet unknown_loc (Pvar "seqv") $ Fun "k" $ Fun "xs" $
    Mat (Var (Short "xs")) [
      (Pcon (SOME $ Short "[]") [],
        Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
      (Pcon (SOME $ Short "::") [Pvar "x1"; Pvar "xs'"],
        Mat (Var (Short "xs'")) [
          (Pcon (SOME $ Short "[]") [],
            Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
          (Pcon (SOME $ Short "::") [Pvar "x2"; Pvar "xs''"],
            Mat (Var (Short "xs''")) [
              (Pcon (SOME $ Short "[]") [],
                If (App Equality [Var (Short "x1"); Var (Short "x2")])
                  (Let (SOME "v") (Con (SOME $ Short "SBool") [Con (SOME $ Short "True") []]) $
                    App Opapp [Var (Short "k"); Var (Short "v")])
                  (Let (SOME "v") (Con (SOME $ Short "SBool") [Con (SOME $ Short "False") []]) $
                    App Opapp [Var (Short "k"); Var (Short "v")]));
              (Pany,
                Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
            ])
        ])
    ]
End

Definition scheme_basis6_def:
  scheme_basis6 = Dlet unknown_loc (Pvar "throw") $ Fun "k" $ Fun "xs" $
    Mat (Var (Short "xs")) [
      (Pcon (SOME $ Short "[]") [],
        Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
      (Pcon (SOME $ Short "::") [Pvar "x"; Pvar "xs'"],
        Mat (Var (Short "xs'")) [
          (Pcon (SOME $ Short "[]") [],
            App Opapp [Var (Short "k"); Var (Short "x")]);
          (Pany,
            Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
        ])
    ]
End

Definition scheme_basis7_def:
  scheme_basis7 = Dletrec unknown_loc [
    ("callcc", "k", Fun "xs" $ Mat (Var (Short "xs")) [
      (Pcon (SOME $ Short "[]") [],
        Con (SOME $ Short "Ex") [Lit $ StrLit "Arity mismatch"]);
      (Pcon (SOME $ Short "::") [Pvar "x"; Pvar "xs'"],
        Mat (Var (Short "xs'")) [
          (Pcon (SOME $ Short "[]") [],
            App Opapp [
              App Opapp [
                App Opapp [Var (Short "app");Var (Short "k")];
                Var (Short "x")];
              cons_list [Con (SOME $ Short "Throw") [Var (Short "k")]]]);
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
  ]
End

Definition scheme_basis_def:
  scheme_basis = [
    scheme_basis1;
    scheme_basis2;
    scheme_basis3;
    scheme_basis4;
    scheme_basis5;
    scheme_basis6;
    scheme_basis7
  ]
End

Definition codegen_def:
  codegen p = INR $ scheme_basis ++ [
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
EVAL “cps_transform 0 $ OUTR $ parse_to_ast
"(begin 1 2 3)"”
*)

val _ = export_theory();