(*
  Code generator for Scheme to CakeML compiler
*)
open preamble;
open astTheory;
open scheme_astTheory

open semanticPrimitivesTheory;
open namespaceTheory;

val _ = new_theory "scheme_to_cake";

Definition to_ml_vals_def:
  to_ml_vals (Prim p) = Con (SOME $ Short "Prim") [case p of
  | SAdd => Con (SOME $ Short "SAdd") []
  | SMul => Con (SOME $ Short "SMul") []
  | SMinus => Con (SOME $ Short "SMinus") []
  | SEqv => Con (SOME $ Short "SEqv") []] ∧
  to_ml_vals (SNum n) = Con (SOME $ Short "SNum") [Lit $ IntLit n] ∧
  to_ml_vals (SBool b) = Con (SOME $ Short "SBool") [Lit $ IntLit
    if b then 1 else 0]
End

Definition cons_list_def:
  cons_list [] = Con (SOME $ Short "nil") [] ∧
  cons_list (x::xs) = Con (SOME $ Short "cons") [Var (Short x); cons_list xs]
End

Definition app_ml_def:
  app_ml n k = let
    t = "t" ++ toString n;
    cex = Fun "_" $ Con (SOME $ Short "Ex") [Lit $ StrLit"Not a procedure"]
  in
    (n+1, Fun t $ Mat (Var (Short t)) [
      (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "SAdd") []],
        App Opapp [App Opapp [Var (Short "sadd"); Var (Short k)]; Lit $ IntLit 0]);
      (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "SMul") []],
        App Opapp [App Opapp [Var (Short "smul"); Var (Short k)]; Lit $ IntLit 1]);
      (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "SMinus") []],
        App Opapp [Var (Short "sminus"); Var (Short k)]);
      (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "SEqv") []],
        App Opapp [Var (Short "seqv"); Var (Short k)]);
      (Pany, cex)
    ])
End

Definition cps_transform_def:
  cps_transform n (Val v) = (let k = "k" ++ toString n in
    (n+1, Fun k $ App Opapp [Var (Short k); to_ml_vals v])) ∧
  cps_transform n (Exception s) =
    (n, Fun "_" $ App Opapp [Var (Short "print"); Lit $ StrLit $ explode s]) ∧
  cps_transform n (Cond c t f) = (let
    (m, cc) = cps_transform n c;
    (l, ct) = cps_transform m t;
    (j, cf) = cps_transform l f;
    p = "t" ++ toString j;
    k = "k" ++ toString (j+1)
  in
    (j+2, Fun k $ App Opapp [cc;  Fun p $ Mat (Var (Short p)) [
      (Pcon (SOME $ Short "SBool") [Plit $ IntLit 0], App Opapp [cf; Var (Short k)]);
      (Pany, App Opapp [ct; Var (Short k)])
    ]])) ∧
  cps_transform n (Apply fn args) = (let
    (m, cfn) = cps_transform n fn;
    k = "k" ++ toString m;
    t = "t" ++ toString (m+1);
    (l, ce) = cps_transform_app (m+2) t [] args k
  in
    (l+1, Fun k $ App Opapp [cfn; Fun t ce])) ∧

  cps_transform_app n tfn ts (e::es) k = (let
    (m, ce) = cps_transform n e;
    t = "t" ++ toString m;
    (l, inner) = cps_transform_app (m+1) tfn (t::ts) es k
  in
    (l, App Opapp [ce; Fun t inner])) ∧
  cps_transform_app n tfn ts [] k = (let
    (m, capp) = app_ml n k;
  in
    (m, App Opapp [App Opapp [capp;Var (Short tfn)];cons_list (REVERSE ts)]))
End

Definition scheme_program_to_cake_def:
  scheme_program_to_cake p = App Opapp [SND (cps_transform 0 p); Fun "t" $ Var (Short "t")]
End

Definition myC_def:
  (myC :('a, string, num # stamp) namespace) = Bind [
    ("SNum", (1, TypeStamp "SNum" 0));
    ("SBool", (1, TypeStamp "SBool" 0));
    ("Prim", (1, TypeStamp "Prim" 0));
    ("SAdd", (0, TypeStamp "SAdd" 1));
    ("SMul", (0, TypeStamp "SMul" 1));
    ("SMinus", (0, TypeStamp "SMinus" 1));
    ("SEqv", (0, TypeStamp "SEqv" 1));
    ("cons", (2, TypeStamp "cons" 2));
    ("nil", (0, TypeStamp "nil" 2));
    ("Ex", (1, TypeStamp "Ex" 0));
  ] []
End

Definition myEnv_def:
  myEnv = <| v := let first = Bind [
    ("sadd", Recclosure <| v := nsEmpty; c := myC |> [
      ("sadd", "k",
        Fun "n" $ Fun "xs" $ Mat (Var (Short "xs")) [
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
      ("smul", "k",
        Fun "n" $ Fun "xs" $ Mat (Var (Short "xs")) [
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
    ))
  ] []
  in nsAppend first $ Bind [
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
  EVAL “scheme_program_to_cake (Cond (Val $ SBool F) (Val $ SNum 420) (Val $ SNum 69))”
  EVAL “scheme_program_to_cake (Apply (Val $ Prim SMinus) [Val $ SNum 2; Val $ SNum 3])”
*)