(*
  Proofs for Scheme to CakeML compilation
*)
open preamble;
open computeLib;
open scheme_astTheory;
open scheme_semanticsTheory;
open scheme_to_cakeTheory;
open astTheory;

open evaluateTheory;
open evaluatePropsTheory;
open semanticPrimitivesTheory;
open namespaceTheory;
open primTypesTheory;
open namespacePropsTheory;

val _ = new_theory "scheme_proofs";

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

Theorem scheme_env1_def[allow_rebind, compute] = EVAL_RULE $ zDefine ‘
  scheme_env1 = case evaluate_decs
      (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
      <|v:=nsEmpty;c:=nsEmpty|>
      (prim_types_program ++ [scheme_basis1]) of
    | (st', Rval env) => env
    | _ => <|v:=nsEmpty;c:=nsEmpty|>
’;

Theorem scheme_env1_rw[simp] = LIST_CONJ $ map EVAL [
  “nsLookup scheme_env1.c (Short "SNum")”,
  “nsLookup scheme_env1.c (Short "SBool")”,
  “nsLookup scheme_env1.c (Short "True")”,
  “nsLookup scheme_env1.c (Short "False")”,
  “nsLookup scheme_env1.c (Short "Prim")”,
  “nsLookup scheme_env1.c (Short "SAdd")”,
  “nsLookup scheme_env1.c (Short "SMul")”,
  “nsLookup scheme_env1.c (Short "SMinus")”,
  “nsLookup scheme_env1.c (Short "SEqv")”,
  “nsLookup scheme_env1.c (Short "CallCC")”,
  “nsLookup scheme_env1.c (Short "[]")”,
  “nsLookup scheme_env1.c (Short "::")”,
  “nsLookup scheme_env1.c (Short "Ex")”,
  “nsLookup scheme_env1.c (Short "Proc")”,
  “nsLookup scheme_env1.c (Short "Throw")”
];

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
            Con (SOME $ Short "Ex") [Lit $ StrLit "Not a number"])
        ])
    ])
  ]
End

Theorem scheme_env2_def[allow_rebind, compute] = SRULE [] $
  RESTR_EVAL_RULE [“scheme_env1”] $ zDefine ‘
    scheme_env2 = case evaluate_decs
        (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
        scheme_env1
        [scheme_basis2] of
      | (st', Rval env) => extend_dec_env env scheme_env1
      | _ => <|v:=nsEmpty;c:=nsEmpty|>
’;

Theorem scheme_env2_rw[simp] = LIST_CONJ $ map
  (SRULE [GSYM scheme_env1_def] o EVAL) [
  “nsLookup scheme_env2.c (Short "SNum")”,
  “nsLookup scheme_env2.c (Short "SBool")”,
  “nsLookup scheme_env2.c (Short "True")”,
  “nsLookup scheme_env2.c (Short "False")”,
  “nsLookup scheme_env2.c (Short "Prim")”,
  “nsLookup scheme_env2.c (Short "SAdd")”,
  “nsLookup scheme_env2.c (Short "SMul")”,
  “nsLookup scheme_env2.c (Short "SMinus")”,
  “nsLookup scheme_env2.c (Short "SEqv")”,
  “nsLookup scheme_env2.c (Short "CallCC")”,
  “nsLookup scheme_env2.c (Short "[]")”,
  “nsLookup scheme_env2.c (Short "::")”,
  “nsLookup scheme_env2.c (Short "Ex")”,
  “nsLookup scheme_env2.c (Short "Proc")”,
  “nsLookup scheme_env2.c (Short "Throw")”,

  “nsLookup scheme_env2.v (Short "sadd")”
];

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
            Con (SOME $ Short "Ex") [Lit $ StrLit "Not a number"])
        ])
    ])
  ]
End

Theorem scheme_env3_def[allow_rebind, compute] = SRULE [] $
  RESTR_EVAL_RULE [“scheme_env2”] $ zDefine ‘
    scheme_env3 = case evaluate_decs
        (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
        scheme_env2
        [scheme_basis3] of
      | (st', Rval env) => extend_dec_env env scheme_env2
      | _ => <|v:=nsEmpty;c:=nsEmpty|>
’;

Theorem scheme_env3_rw[simp] = LIST_CONJ $ map
  (SRULE [
    GSYM $ EVAL “scheme_env1”,
    GSYM $ EVAL “scheme_env2”
  ] o EVAL) [
  “nsLookup scheme_env3.c (Short "SNum")”,
  “nsLookup scheme_env3.c (Short "SBool")”,
  “nsLookup scheme_env3.c (Short "True")”,
  “nsLookup scheme_env3.c (Short "False")”,
  “nsLookup scheme_env3.c (Short "Prim")”,
  “nsLookup scheme_env3.c (Short "SAdd")”,
  “nsLookup scheme_env3.c (Short "SMul")”,
  “nsLookup scheme_env3.c (Short "SMinus")”,
  “nsLookup scheme_env3.c (Short "SEqv")”,
  “nsLookup scheme_env3.c (Short "CallCC")”,
  “nsLookup scheme_env3.c (Short "[]")”,
  “nsLookup scheme_env3.c (Short "::")”,
  “nsLookup scheme_env3.c (Short "Ex")”,
  “nsLookup scheme_env3.c (Short "Proc")”,
  “nsLookup scheme_env3.c (Short "Throw")”,

  “nsLookup scheme_env3.v (Short "sadd")”,
  “nsLookup scheme_env3.v (Short "smul")”
];

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
            Con (SOME $ Short "Ex") [Lit $ StrLit "Not a number"])
        ])
    ]
End

Theorem scheme_env4_def[allow_rebind, compute] = SRULE [] $
  RESTR_EVAL_RULE [“scheme_env3”] $ zDefine ‘
    scheme_env4 = case evaluate_decs
        (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
        scheme_env3
        [scheme_basis4] of
      | (st', Rval env) => extend_dec_env env scheme_env3
      | _ => <|v:=nsEmpty;c:=nsEmpty|>
’;

Theorem scheme_env4_rw[simp] = LIST_CONJ $ map
  (SRULE [
    GSYM $ EVAL “scheme_env1”,
    GSYM $ EVAL “scheme_env2”,
    GSYM $ EVAL “scheme_env3”
  ] o EVAL) [
  “nsLookup scheme_env4.c (Short "SNum")”,
  “nsLookup scheme_env4.c (Short "SBool")”,
  “nsLookup scheme_env4.c (Short "True")”,
  “nsLookup scheme_env4.c (Short "False")”,
  “nsLookup scheme_env4.c (Short "Prim")”,
  “nsLookup scheme_env4.c (Short "SAdd")”,
  “nsLookup scheme_env4.c (Short "SMul")”,
  “nsLookup scheme_env4.c (Short "SMinus")”,
  “nsLookup scheme_env4.c (Short "SEqv")”,
  “nsLookup scheme_env4.c (Short "CallCC")”,
  “nsLookup scheme_env4.c (Short "[]")”,
  “nsLookup scheme_env4.c (Short "::")”,
  “nsLookup scheme_env4.c (Short "Ex")”,
  “nsLookup scheme_env4.c (Short "Proc")”,
  “nsLookup scheme_env4.c (Short "Throw")”,

  “nsLookup scheme_env4.v (Short "sadd")”,
  “nsLookup scheme_env4.v (Short "smul")”,
  “nsLookup scheme_env4.v (Short "sminus")”
];

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

Theorem scheme_env5_def[allow_rebind, compute] = SRULE [] $
  RESTR_EVAL_RULE [“scheme_env4”] $ zDefine ‘
    scheme_env5 = case evaluate_decs
        (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
        scheme_env4
        [scheme_basis5] of
      | (st', Rval env) => extend_dec_env env scheme_env4
      | _ => <|v:=nsEmpty;c:=nsEmpty|>
’;

Theorem scheme_env5_rw[simp] = LIST_CONJ $ map
  (SRULE [
    GSYM $ EVAL “scheme_env1”,
    GSYM $ EVAL “scheme_env2”,
    GSYM $ EVAL “scheme_env3”,
    GSYM $ EVAL “scheme_env4”
  ] o EVAL) [
  “nsLookup scheme_env5.c (Short "SNum")”,
  “nsLookup scheme_env5.c (Short "SBool")”,
  “nsLookup scheme_env5.c (Short "True")”,
  “nsLookup scheme_env5.c (Short "False")”,
  “nsLookup scheme_env5.c (Short "Prim")”,
  “nsLookup scheme_env5.c (Short "SAdd")”,
  “nsLookup scheme_env5.c (Short "SMul")”,
  “nsLookup scheme_env5.c (Short "SMinus")”,
  “nsLookup scheme_env5.c (Short "SEqv")”,
  “nsLookup scheme_env5.c (Short "CallCC")”,
  “nsLookup scheme_env5.c (Short "[]")”,
  “nsLookup scheme_env5.c (Short "::")”,
  “nsLookup scheme_env5.c (Short "Ex")”,
  “nsLookup scheme_env5.c (Short "Proc")”,
  “nsLookup scheme_env5.c (Short "Throw")”,

  “nsLookup scheme_env5.v (Short "sadd")”,
  “nsLookup scheme_env5.v (Short "smul")”,
  “nsLookup scheme_env5.v (Short "sminus")”,
  “nsLookup scheme_env5.v (Short "seqv")”
];

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

Theorem scheme_env6_def[allow_rebind, compute] = SRULE [] $
  RESTR_EVAL_RULE [“scheme_env5”] $ zDefine ‘
    scheme_env6 = case evaluate_decs
        (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
        scheme_env5
        [scheme_basis6] of
      | (st', Rval env) => extend_dec_env env scheme_env5
      | _ => <|v:=nsEmpty;c:=nsEmpty|>
’;

Theorem scheme_env6_rw[simp] = LIST_CONJ $ map
  (SRULE [
    GSYM $ EVAL “scheme_env1”,
    GSYM $ EVAL “scheme_env2”,
    GSYM $ EVAL “scheme_env3”,
    GSYM $ EVAL “scheme_env4”,
    GSYM $ EVAL “scheme_env5”
  ] o EVAL) [
  “nsLookup scheme_env6.c (Short "SNum")”,
  “nsLookup scheme_env6.c (Short "SBool")”,
  “nsLookup scheme_env6.c (Short "True")”,
  “nsLookup scheme_env6.c (Short "False")”,
  “nsLookup scheme_env6.c (Short "Prim")”,
  “nsLookup scheme_env6.c (Short "SAdd")”,
  “nsLookup scheme_env6.c (Short "SMul")”,
  “nsLookup scheme_env6.c (Short "SMinus")”,
  “nsLookup scheme_env6.c (Short "SEqv")”,
  “nsLookup scheme_env6.c (Short "CallCC")”,
  “nsLookup scheme_env6.c (Short "[]")”,
  “nsLookup scheme_env6.c (Short "::")”,
  “nsLookup scheme_env6.c (Short "Ex")”,
  “nsLookup scheme_env6.c (Short "Proc")”,
  “nsLookup scheme_env6.c (Short "Throw")”,

  “nsLookup scheme_env6.v (Short "sadd")”,
  “nsLookup scheme_env6.v (Short "smul")”,
  “nsLookup scheme_env6.v (Short "sminus")”,
  “nsLookup scheme_env6.v (Short "seqv")”,
  “nsLookup scheme_env6.v (Short "throw")”
];

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

Theorem scheme_env7_def[allow_rebind, compute] = SRULE [] $
  RESTR_EVAL_RULE [“scheme_env6”] $ zDefine ‘
    scheme_env7 = case evaluate_decs
        (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
        scheme_env6
        [scheme_basis7] of
      | (st', Rval env) => extend_dec_env env scheme_env6
      | _ => <|v:=nsEmpty;c:=nsEmpty|>
’;

Theorem scheme_env7_rw[simp] = LIST_CONJ $ map
  (SRULE [
    GSYM $ EVAL “scheme_env1”,
    GSYM $ EVAL “scheme_env2”,
    GSYM $ EVAL “scheme_env3”,
    GSYM $ EVAL “scheme_env4”,
    GSYM $ EVAL “scheme_env5”,
    GSYM $ EVAL “scheme_env6”
  ] o EVAL) [
  “nsLookup scheme_env7.c (Short "SNum")”,
  “nsLookup scheme_env7.c (Short "SBool")”,
  “nsLookup scheme_env7.c (Short "True")”,
  “nsLookup scheme_env7.c (Short "False")”,
  “nsLookup scheme_env7.c (Short "Prim")”,
  “nsLookup scheme_env7.c (Short "SAdd")”,
  “nsLookup scheme_env7.c (Short "SMul")”,
  “nsLookup scheme_env7.c (Short "SMinus")”,
  “nsLookup scheme_env7.c (Short "SEqv")”,
  “nsLookup scheme_env7.c (Short "CallCC")”,
  “nsLookup scheme_env7.c (Short "[]")”,
  “nsLookup scheme_env7.c (Short "::")”,
  “nsLookup scheme_env7.c (Short "Ex")”,
  “nsLookup scheme_env7.c (Short "Proc")”,
  “nsLookup scheme_env7.c (Short "Throw")”,

  “nsLookup scheme_env7.v (Short "sadd")”,
  “nsLookup scheme_env7.v (Short "smul")”,
  “nsLookup scheme_env7.v (Short "sminus")”,
  “nsLookup scheme_env7.v (Short "seqv")”,
  “nsLookup scheme_env7.v (Short "throw")”,
  “nsLookup scheme_env7.v (Short "callcc")”,
  “nsLookup scheme_env7.v (Short "app")”
];

(*
Example lambda calculus code of conditional expression,
before and after step in CEK machine

(\k0 -> (\k1 -> k1 $ SBool T)
  (\t0 -> match t0
          | SBool F => (\k2 -> k2 (SNum 1)) k0
          | _ => (\k2 -> k2 (SNum 2)) k0))
(\t -> t)

-->

(\k1 -> k1 $ SBool T)
(\t0 -> match t0
        | SBool F => (\k2 -> k2 (SNum 1)) (\t -> t)
        | _ => (\k2 -> k2 (SNum 2)) (\t -> t)))
*)

Definition ml_v_vals_def[nocompute]:
  ml_v_vals v = case evaluate (<|clock:=0|> :num state)
      scheme_env7 [to_ml_vals v] of
    | (st, Rval [mlv]) => mlv
    | _ => ARB
End

fun mydisch x = DISCH (hd $ hyp x) x;

Theorem ml_v_vals_def[allow_rebind, compute] = SRULE [] $ mydisch $
  LIST_CONJ $ map
    (EVAL_RULE o SIMP_RULE pure_ss [SimpRHS, ml_v_vals_def]) [
    REFL “ml_v_vals (Prim SAdd)”,
    REFL “ml_v_vals (Prim SMul)”,
    REFL “ml_v_vals (Prim SMinus)”,
    REFL “ml_v_vals (Prim SEqv)”,
    REFL “ml_v_vals (Prim CallCC)”,
    ASSUME “∀ n . ml_v_vals (SNum n) = ml_v_vals (SNum n)”,
    REFL “ml_v_vals (SBool T)”,
    REFL “ml_v_vals (SBool F)”
  ];

Inductive e_ce_rel:
[~Val:]
  nsLookup env.v (Short valv) = SOME (ml_v_vals v) ∧
  nsLookup env.v (Short var) = SOME kv ∧
  valv ≠ var
  ⇒
  e_ce_rel (Val v) var env kv $ App Opapp [Var (Short var); Var (Short valv)]
[~Exp:]
  (m, ce) = cps_transform n e ∧
  nsLookup env.v (Short var) = SOME kv
  ⇒
  e_ce_rel (Exp e) var env kv $ App Opapp [ce; Var (Short var)]
[~Exception:]
  e_ce_rel (Exception s) var env kv $
    Con (SOME $ Short "Ex") [Lit $ StrLit $ explode s]
End

Theorem scheme_env'_def[allow_rebind, compute] = EVAL_RULE $ zDefine ‘
  scheme_env' = case evaluate_decs (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state) <|v:=nsEmpty;c:=nsEmpty|> (prim_types_program ++ scheme_basis) of
    | (st', Rval env) => env
    | _ => <|v:=nsEmpty;c:=nsEmpty|>
’;

Definition cconses_def[simp]:
  cconses = ["SNum"; "SBool"; "True"; "False";
    "Prim";"SAdd";"SMul";"SMinus";"SEqv";"CallCC";
    "[]"]
End

Definition vconses_def[simp]:
  vconses = ["sadd"; "smul"; "sminus"; "seqv"; "throw"; "callcc"; "app"]
End

(*Definition scheme_env_def:
  scheme_env env
  ⇔
  (nsLookup env.c (Short "SNum") = SOME (1, TypeStamp "SNum" 3)) ∧
  (nsLookup env.c (Short "SBool") = SOME (1, TypeStamp "SBool" 3)) ∧
  (nsLookup env.c (Short "True") = SOME (0, TypeStamp "True" 0)) ∧
  (nsLookup env.c (Short "False") = SOME (0, TypeStamp "False" 0)) ∧
  (nsLookup env.c (Short "Prim") = SOME (1, TypeStamp "Prim" 3)) ∧
  (nsLookup env.c (Short "SAdd") = SOME (0, TypeStamp "SAdd" 2)) ∧
  (nsLookup env.c (Short "SMul") = SOME (0, TypeStamp "SMul" 2)) ∧
  (nsLookup env.c (Short "SMinus") = SOME (0, TypeStamp "SMinus" 2)) ∧
  (nsLookup env.c (Short "SEqv") = SOME (0, TypeStamp "SEqv" 2)) ∧
  (nsLookup env.c (Short "CallCC") = SOME (0, TypeStamp "CallCC" 2)) ∧

  (nsLookup env.c (Short "[]") = SOME (0, TypeStamp "[]" 1))
  (nsLookup env.c (Short "::") = SOME (0, TypeStamp "::" 1))
End*)

(*Theorem scheme_env_def[compute] = EVAL_RULE $ zDefine ‘
  scheme_env env
  ⇔
  EVERY (λ x . nsLookup env.c x = nsLookup scheme_env'.c x) $
    MAP Short cconses ∧
  EVERY (λ x . nsLookup env.v x = nsLookup scheme_env'.v x) $
    MAP Short vconses
’;*)

Theorem scheme_env_def[allow_rebind, compute] = SRULE [] $ zDefine ‘
  scheme_env env
  ⇔
  EVERY (λ x . nsLookup env.c x = nsLookup scheme_env7.c x) $
    MAP Short ["SNum"; "SBool"; "True"; "False";
    "Prim";"SAdd";"SMul";"SMinus";"SEqv";"CallCC";
    "[]"; "::"; "Ex"; "Throw"] ∧
  EVERY (λ x . nsLookup env.v x = nsLookup scheme_env7.v x) $
    MAP Short ["sadd"; "smul"; "sminus"; "seqv"; "throw"; "callcc"; "app"]
’

Definition cps_app_ts_def:
  cps_app_ts n (e::es) = (let
    (m, ce) = cps_transform n e;
    t = "t" ++ toString m
  in
    t :: cps_app_ts (m+1) es) ∧

  cps_app_ts n [] = []
End

Inductive cont_rel:
[~Id:]
  scheme_env env ∧
  ¬ MEM t vconses
  ⇒
  cont_rel []
    (Closure env t (Var (Short t)))
[~CondK:]
  cont_rel ks kv ∧
  nsLookup env.v (Short var) = SOME kv ∧
  (n', ct) = cps_transform n te ∧
  (m', cf) = cps_transform m fe ∧
  scheme_env env ∧
  var ≠ t
  ⇒
  (*Likely needs condition on se i.e. Scheme env*)
  cont_rel ((se, CondK te fe) :: ks)
    (Closure env t $ Mat (Var (Short t)) [
      (Pcon (SOME $ Short "SBool") [Pcon (SOME $ Short "False") []],
        App Opapp [cf; Var (Short var)]);
      (Pany, App Opapp [ct;  Var (Short var)])
    ])
[~ApplyK_NONE:]
  cont_rel ks kv ∧
  nsLookup env.v (Short var) = SOME kv ∧
  (m, ce) = cps_transform_app n (Var (Short t)) [] es (Var (Short var)) ∧
  scheme_env env ∧
  ¬ MEM var vconses ∧
  ¬ MEM t vconses ∧
  ts = cps_app_ts n es ∧
  ¬ MEM var ts ∧
  ¬ MEM t ts ∧
  var ≠ t
  ⇒
  (*Likely needs condition on se i.e. Scheme env*)
  cont_rel ((se, ApplyK NONE es) :: ks)
    (Closure env t $ ce)
[~ApplyK_SOME:]
  cont_rel ks kv ∧
  nsLookup env.v (Short var) = SOME kv ∧
  (m, ce) = cps_transform_app n (Var (Short fnt))
    (Var (Short t) :: MAP (Var o Short) ts) es (Var (Short var)) ∧
  nsLookup env.v (Short fnt) = SOME (ml_v_vals fn) ∧
  LIST_REL (λ x v . nsLookup env.v (Short x) = SOME (ml_v_vals v)) ts vs ∧
  scheme_env env ∧
  ALL_DISTINCT ts ∧
  ¬ MEM var vconses ∧
  ¬ MEM fnt vconses ∧
  ¬ MEM t vconses ∧
  EVERY (λ x . ¬ MEM x vconses) ts ∧
  ¬ MEM var ts ∧
  ¬ MEM fnt ts ∧
  ¬ MEM t ts ∧
  ts' = cps_app_ts n es ∧
  EVERY (λ x . ¬ MEM x ts') ts ∧
  ¬ MEM var ts' ∧
  ¬ MEM fnt ts' ∧
  ¬ MEM t ts' ∧
  var ≠ fnt ∧
  var ≠ t ∧
  fnt ≠ t
  ⇒
  (*Likely needs condition on se i.e. Scheme env*)
  cont_rel ((se, ApplyK (SOME (fn, vs)) es) :: ks)
    (Closure env t $ ce)
End

Theorem compile_in_rel:
  ∀ p st env .
    scheme_env env
    ⇒
    ∃ st' env' var mle k kv .
      e_ce_rel (Exp p) var env' kv mle ∧
      cont_rel k kv ∧
      evaluate st env [compile_scheme_prog p] = evaluate st' env' [mle]
Proof
  simp[Once e_ce_rel_cases, compile_scheme_prog_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
  >> simp[Ntimes evaluate_def 2, nsOptBind_def]
  >> irule_at (Pos hd) EQ_REFL
  >> irule_at Any EQ_REFL
  >> simp[nsLookup_def, Once cont_rel_cases]
  >> metis_tac[]
QED

(*
EVAL “case (SND $ evaluate_decs <|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|>
<|v:=nsEmpty;c:=nsEmpty|> $ prim_types_program
++ (scheme_basis)) of
  | Rval env => evaluate <|clock:=999|> env $ [exp_with_cont [] (Lit $ LitBool T)]
  | _ => (st, v)”
*)

Theorem basis_scheme_env:
    scheme_env scheme_env'
Proof
  EVAL_TAC
QED

(*
open scheme_proofsTheory;
*)

Theorem str_not_num:
  ∀ (n:num) str . ¬ EVERY isDigit str ⇒ toString n ≠ str
Proof
  simp[EVERY_isDigit_num_to_dec_string]
QED

Theorem k_in_ts:
  ∀ es (n:num) m . ¬ MEM (STRING #"k" (toString n)) (cps_app_ts m es)
Proof
  Induct
  >> simp[cps_app_ts_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
QED

Theorem mono_proc_ml_on_n:
  ∀ xs xp n k args ce m ce' .
    (m, ce') = proc_ml n xs xp k args ce ⇒ m ≥ n
Proof
  Induct >> Cases
  >> simp[proc_ml_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
  >> last_x_assum $ dxrule o GSYM
  >> simp[]
QED

Theorem mono_cps_on_n:
  (∀ n e m ce . (m, ce) = cps_transform n e ⇒ m ≥ n) ∧
  (∀ n k k' m ce . (m, ce) = refunc_cont n k k' ⇒ m ≥ n) ∧
  (∀ n fn ts es k m ce . (m, ce) = cps_transform_app n fn ts es k ⇒ m ≥ n) ∧
  (∀ n k es m ce . (m, ce) = cps_transform_seq n k es ⇒ m ≥ n) ∧
  (∀ n k bs ce' m ce . (m, ce) = cps_transform_letreinit n k bs ce' ⇒ m ≥ n)
Proof
  ho_match_mp_tac $ cps_transform_ind
  >> simp[cps_transform_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[]) >- (
    dxrule $ GSYM mono_proc_ml_on_n
    >> simp[]
  )
  >> pop_assum mp_tac
  >> every_case_tac
  >> strip_tac
  >> gvs[]
QED

Theorem t_in_ts:
  ∀ es n m . m > n ⇒ ¬ MEM (STRING #"t" (toString n)) (cps_app_ts m es)
Proof
  Induct >> rpt strip_tac
  >> gvs[cps_app_ts_def]
  >> rpt (pairarg_tac >> gvs[])
  >> dxrule $ GSYM $ cj 1 mono_cps_on_n
  >> simp[]
  >> last_x_assum $ qspecl_then [‘n’, ‘m'+1’] mp_tac
  >> simp[]
QED

Theorem myproof:
  ∀ store store' env env' e e' k k' (st : 'ffi state) mlenv var kv mle .
  step  (store, k, env, e) = (store', k', env', e') ∧
  st.clock > 0 ∧
  cont_rel k kv ∧
  e_ce_rel e var mlenv kv mle ∧
  scheme_env mlenv
  ⇒
  ∃ st' mlenv' var' kv' mle' .
    evaluate st mlenv [mle]
    =
    evaluate st' mlenv' [mle'] ∧
    cont_rel k' kv' ∧
    e_ce_rel e' var' mlenv' kv' mle'
Proof
  Cases_on ‘e’
  >~ [‘Val v’] >- (
    Cases_on ‘k’
    >- (simp[step_def, return_def] >> metis_tac[])
    >> PairCases_on ‘h’
    >> Cases_on ‘∃ te fe . h1 = CondK te fe’ >- (
      gvs[]
      >> simp[step_def, return_def]
      >> Cases_on ‘v = Prim SAdd ∨ v = Prim SMul ∨ v = Prim SMinus ∨
        v = Prim SEqv ∨ v = Prim CallCC ∨
        (∃n. v = SNum n) ∨ v = SBool T ∨ v = SBool F’
      (*Only covering cases supported by to_ml_vals,
      but in theory should work for any vals*)
      >- (
        simp[Once e_ce_rel_cases, Once cont_rel_cases]
        >> simp[oneline ml_v_vals_def]
        >> every_case_tac
        >> gvs[]
        >> rpt strip_tac
        >> simp[SimpLHS, Ntimes evaluate_def 6, do_con_check_def,
          build_conv_def, scheme_env_def, do_opapp_def,
        can_pmatch_all_def, pmatch_def]
        >> qpat_assum ‘scheme_env env’ $ simp o curry ((::) o swap) [
            same_type_def, same_ctor_def, do_opapp_def,
            evaluate_match_def, pmatch_def, pat_bindings_def]
          o SRULE [scheme_env_def]
        >> irule_at (Pos hd) EQ_REFL
        >> simp[Once e_ce_rel_cases]
        >> irule_at Any EQ_REFL
        >> simp[nsLookup_def]
        >> metis_tac[]
      )
      >> cheat
    )
    >> Cases_on ‘h1 = ApplyK NONE []’ >- (
      gvs[]
      >> simp[step_def, return_def, Once e_ce_rel_cases, Once cont_rel_cases]
      >> Cases_on ‘v = Prim SAdd ∨ v = Prim SMul ∨ v = Prim SMinus ∨
        v = Prim SEqv ∨ v = Prim CallCC ∨
        (∃n. v = SNum n) ∨ v = SBool T ∨ v = SBool F’
      >- (
        simp[oneline ml_v_vals_def]
        >> rpt strip_tac
        >> Cases_on ‘st.clock > 6’ >- (
          every_case_tac
          >> gvs[application_def, sadd_def, smul_def, sminus_def,
            seqv_def, cps_transform_def, cons_list_def]
          >> simp[SimpLHS, evaluate_def, do_con_check_def,
            build_conv_def, do_opapp_def]
          >> qpat_assum ‘scheme_env env’ $ simp o single
            o SRULE [scheme_env_def]
          >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
          >> simp[Ntimes evaluate_def 3, dec_clock_def]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >~ [‘Litv (IntLit i)’] >- (
            simp[Once evaluate_def]
            >> irule_at (Pos hd) EQ_REFL
            >> simp[Once e_ce_rel_cases]
            >> metis_tac[]
          )
          >~ [‘SOME (Conv (SOME (TypeStamp "SBool" _)) [
            Conv (Some (TypeStamp "True" _)) []
          ])’] >- (
            simp[Once evaluate_def]
            >> irule_at (Pos hd) EQ_REFL
            >> simp[Once e_ce_rel_cases]
            >> metis_tac[]
          )
          >~ [‘SOME (Conv (SOME (TypeStamp "SBool" _)) [
            Conv (Some (TypeStamp "False" _)) []
          ])’] >- (
            simp[Once evaluate_def]
            >> irule_at (Pos hd) EQ_REFL
            >> simp[Once e_ce_rel_cases]
            >> metis_tac[]
          )
          >> simp[evaluate_def]
          >> simp[do_opapp_def,
          Once find_recfun_def, Once build_rec_env_def]
          >> simp[Ntimes evaluate_def 4, dec_clock_def]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >~ [‘"SAdd"’] >- (
            simp[Ntimes evaluate_def 3, nsOptBind_def,
              do_con_check_def, build_conv_def]
            >> irule_at (Pos hd) EQ_REFL
            >> simp[Once e_ce_rel_cases]
            >> simp[ml_v_vals_def]
          )
          >~ [‘"SMul"’] >- (
            simp[Ntimes evaluate_def 3, nsOptBind_def,
              do_con_check_def, build_conv_def]
            >> irule_at (Pos hd) EQ_REFL
            >> simp[Once e_ce_rel_cases]
            >> simp[ml_v_vals_def]
          )
          >> irule_at (Pos hd) EQ_REFL
          >> simp[Once e_ce_rel_cases]
          >> metis_tac[]
        )
        (*timeout case, I feel like this can be ignored for now*)
        >> cheat
      )
      >> cheat
    )
    >> Cases_on ‘∃ e es . h1 = ApplyK NONE (e::es)’ >- (
      gvs[]
      >> simp[step_def, return_def, Once e_ce_rel_cases,
        Once cont_rel_cases, cps_transform_def, cps_app_ts_def]
      >> rpt strip_tac
      >> rpt (pairarg_tac >> gvs[])
      >> simp[Ntimes evaluate_def 6, do_opapp_def, nsOptBind_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases]
      >> irule_at Any EQ_REFL
      >> qpat_assum ‘cps_transform _ _ = (_,_)’ $
        irule_at (Pos $ el 2) o GSYM
      >> simp[Once cont_rel_cases]
      >> pop_assum $ irule_at (Pos $ el 3) o GSYM
      >> qpat_assum ‘scheme_env env’ $ simp
        o curry ((::) o swap) [scheme_env_def] o SRULE [scheme_env_def]
      >> irule_at Any str_not_num
      >> simp[isDigit_def, t_in_ts]
    )
    >> Cases_on ‘∃ e es . h1 = ApplyK (SOME (fn, vs)) (e::es)’ >- (
      gvs[]
      >> simp[step_def, return_def, Once e_ce_rel_cases,
        Once cont_rel_cases, cps_transform_def, cps_app_ts_def]
      >> rpt strip_tac
      >> rpt (pairarg_tac >> gvs[])
      >> simp[Ntimes evaluate_def 6, do_opapp_def, nsOptBind_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases]
      >> irule_at Any EQ_REFL
      >> qpat_assum ‘cps_transform _ _ = (_,_)’ $ irule_at
        (Pos $ hd o tl) o GSYM
      >> simp[Once cont_rel_cases]
      >> SIMP_TAC std_ss [MAP_o]
      >> pop_assum $ irule_at (Pos $ el 3) o GSYM
        o SIMP_RULE std_ss [Ntimes (GSYM MAP) 2, MAP_o]
      >> irule_at Any EQ_REFL
      >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
      >> qpat_assum ‘scheme_env env’ $ simp
        o curry ((::) o swap) [scheme_env_def] o SRULE [scheme_env_def]
      >> irule_at Any str_not_num
      >> simp[isDigit_def, t_in_ts]
      >> gvs[EVERY_CONJ]
      >> qpat_assum ‘EVERY (λ x . x ≠ _) _’ $ simp o single
        o SRULE [EVERY_MEM]
      >> irule EVERY2_MEM_MONO
      >> qpat_assum ‘LIST_REL _ _ _’ $ irule_at (Pos last)
      >> qpat_assum ‘LIST_REL _ _ _’ $ assume_tac o cj 1
        o SRULE [EVERY2_EVERY]
      >> PairCases >> simp[]
      >> strip_tac
      >> drule $ SRULE [Once CONJ_COMM] MEM_ZIP_MEM_MAP
      >> simp[]
      >> strip_tac
      >> qsuff_tac ‘x0 ≠ t'’
      >> strip_tac
      >> gvs[]
    )
    >> cheat
  )
  >~ [‘Exp e’] >- (
    Cases_on ‘e’
    >> simp[step_def, Once e_ce_rel_cases]
    >~ [‘Lit l’] >- (
      simp[cps_transform_def]
      >> rpt strip_tac
      >> Cases_on ‘l’
      >> simp[lit_to_val_def, to_ml_vals_def]
      >> TRY CASE_TAC (*for Prim cases*)
      >> gvs[lit_to_val_def, to_ml_vals_def]
      >> simp[SimpLHS, Ntimes evaluate_def 7, do_opapp_def,
        do_con_check_def, build_conv_def, nsOptBind_def]
      >> qpat_assum ‘scheme_env mlenv’ $ simp o single
        o SRULE [scheme_env_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases, ml_v_vals_def]
    )
    >~ [‘Cond c te fe’] >- (
      simp[cps_transform_def]
      >> rpt strip_tac
      >> rpt (pairarg_tac >> gvs[])
      >> simp[SimpLHS, Ntimes evaluate_def 6, do_opapp_def, nsOptBind_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases, Once cont_rel_cases]
      >> rpt $ irule_at Any EQ_REFL
      >> gvs[scheme_env_def]
      >> metis_tac[]
    )
    >~ [‘Apply fn es’] >- (
      simp[cps_transform_def]
      >> rpt strip_tac
      >> rpt (pairarg_tac >> gvs[])
      >> simp[SimpLHS, Ntimes evaluate_def 6, do_opapp_def, nsOptBind_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases, Once cont_rel_cases]
      >> rpt $ irule_at Any EQ_REFL
      >> pop_assum $ irule_at Any o GSYM
      >> qpat_assum ‘scheme_env mlenv’ $ simp
        o curry ((::) o swap) [scheme_env_def] o SRULE [scheme_env_def]
      >> irule_at (Pos hd) str_not_num
      >> simp[isDigit_def, k_in_ts, t_in_ts]
      >> metis_tac[]
    )
    >> cheat
  )
  >> cheat
QED

(*Theorem val_correct:
  ∀ n . ∃ k . SND (evaluate <| clock := k |> myEnv [scheme_program_to_cake (Val (SNum n))])
    = Rval [Conv (SOME $ TypeStamp "SNum" 0) [Litv $ IntLit n]]
Proof
  strip_tac
  >> qexists_tac ‘99’
  >> rw[scheme_program_to_cake_def, cps_transform_def, myEnv_def, myC_def,
    to_ml_vals_def,
    Once evaluate_def, do_opapp_def, dec_clock_def,
    nsLookup_def, nsBind_def, do_con_check_def, build_conv_def]
QED*)

val _ = export_theory();