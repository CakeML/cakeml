(*
  Translation from CPScheme to CakeML
*)
open preamble;
open astTheory;
open mlstringTheory;
open scheme_astTheory;
open cpscheme_astTheory;
open semanticPrimitivesTheory;
open namespaceTheory;

val _ = new_theory "cpscheme_to_cake";

Definition to_ml_vals_def:
  to_ml_vals (Prim p) = Con (SOME $ Short "Prim") [case p of
  | SAdd => Con (SOME $ Short "SAdd") []
  | SMul => Con (SOME $ Short "SMul") []] ∧
  to_ml_vals (SNum n) = Con (SOME $ Short "SNum") [Lit $ IntLit &n] ∧
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
    rfex = Fun "_" $ Con (SOME $ Short "Ex") [Lit $ StrLit"Not a procedure"]
  in
    (n+1, Fun t $ Mat (Var (Short t)) [
      (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "SAdd") []],
        App Opapp [App Opapp [Var (Short "sadd"); Var (Short k)]; Lit $ IntLit 0]);
      (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "SMul") []],
        App Opapp [App Opapp [Var (Short "smul"); Var (Short k)]; Lit $ IntLit 1]);
      (Pany, rfex)
    ])
End

Definition refunc_def:
  refunc n (CVal v) = (let k = "k" ++ toString n in
    (n+1, Fun k $ App Opapp [Var (Short k); to_ml_vals v])) ∧
  refunc n (CException s) =
    (n, Fun "_" $ App Opapp [Var (Short "print"); Lit $ StrLit $ explode s]) ∧
  refunc n (Call c k) = (let
    (m, rfc) = refunc n c;
    k' = "k" ++ toString m;
    (l, rfk) = refunc_cont (m+1) k k';
    t = "t" ++ toString (l)
  in
    (l+1, Fun k' $ App Opapp [rfc; rfk])) ∧

  refunc_cont n (CondK t f) k = (let
    (m, rft) = refunc n t;
    (l, rff) = refunc m f;
    p = "t" ++ toString l
  in
    (l+1, Fun p $ Mat (Var (Short p)) [
      (Pcon (SOME $ Short "SBool") [Plit $ IntLit 0], App Opapp [rff; Var (Short k)]);
      (Pany, App Opapp [rft; Var (Short k)])
    ])) ∧
  refunc_cont n (ApplyK NONE cs) k = (let t = "t" ++ toString n in
    case cs of
    | [] => (n+1, Fun t (Var (Short t)))
    | c::cs' => let
      t = "t" ++ toString n;
      (m, rfc) = refunc_app (n+1) t [] cs k
    in
      (m+1, Fun t rfc)
    ) ∧

  refunc_app n tfn ts (c::cs) k = (let
    (m, rfc) = refunc n c;
    t = "t" ++ toString m;
    (l, inner) = refunc_app (m+1) tfn (t::ts) cs k
  in
    (l, App Opapp [rfc; Fun t inner])) ∧
  refunc_app n tfn ts [] k = (let
    (m, rfapp) = app_ml n k;
  in
    (m, App Opapp [App Opapp [rfapp;Var (Short tfn)];cons_list (REVERSE ts)]))
Termination
  WF_REL_TAC ‘measure $ λ x . case x of
    | INL(_,c) => cexp_size c
    | INR(INL(_,k,_)) => cont_size cexp_size k
    | INR(INR(_,_,_,cs,_)) => list_size cexp_size cs’
End

Definition scheme_program_to_cake_def:
  scheme_program_to_cake p = App Opapp [SND (refunc 0 p); Fun "t" $ Var (Short "t")]
End

Definition myC_def:
  (myC :('a, string, num # stamp) namespace) = Bind [
    ("SNum", (1, TypeStamp "SNum" 0));
    ("SBool", (1, TypeStamp "SBool" 0));
    ("Prim", (1, TypeStamp "Prim" 0));
    ("SAdd", (0, TypeStamp "SAdd" 1));
    ("SMul", (0, TypeStamp "SMul" 1));
    ("cons", (2, TypeStamp "cons" 2));
    ("nil", (0, TypeStamp "nil" 2));
    ("Ex", (1, TypeStamp "Ex" 0));
  ] []
End

Definition myEnv_def:
  myEnv = <| v := Bind [
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
    ] "smul")
  ] []
; c := myC
|>
End

(*
  open cpscheme_to_cakeTheory;
  open scheme_to_cpschemeTheory;
  open evaluateTheory;

  EVAL “evaluate <| clock := 999 |> myEnv [scheme_program_to_cake $ cps_transform $ Val $ SNum 3]”
  EVAL “evaluate <| clock := 999 |> myEnv [scheme_program_to_cake (cps_transform (Cond (Val $ SBool F) (Val $ SNum 420) (Val $ SNum 69)))]”
  EVAL “evaluate <| clock := 999 |> myEnv [scheme_program_to_cake $ cps_transform (Apply (Val $ Prim SMul) [Val $ SNum 2; Val $ SNum 3])]”
  EVAL “scheme_program_to_cake (cps_transform (Cond (Val $ SBool F) (Val $ SNum 420) (Val $ SNum 69)))”
  EVAL “scheme_program_to_cake $ cps_transform (Apply (Val $ Prim SMul) [Val $ SNum 2; Val $ SNum 3])”
*)

val _ = export_theory();