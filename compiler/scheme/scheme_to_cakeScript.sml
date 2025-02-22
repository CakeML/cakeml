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
  app_ml n k t = let
    cex = Fun "_" $ Con (SOME $ Short "Ex") [Lit $ StrLit"Not a procedure"]
  in
    (n, Mat (Var (Short t)) [
      (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "SAdd") []],
        App Opapp [App Opapp [Var (Short "sadd"); Var (Short k)]; Lit $ IntLit 0]);
      (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "SMul") []],
        App Opapp [App Opapp [Var (Short "smul"); Var (Short k)]; Lit $ IntLit 1]);
      (Pcon (SOME $ Short "Proc") [Pvar "e"],
        App Opapp [Var (Short "e"); Var (Short k)]);
      (Pany, cex)
    ])
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
            (App Opref [Var (Short arg)])
            inner)
    ]))
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
    (l, Fun k $ App Opapp [cfn; Fun t ce])) ∧
  cps_transform n (Ident x) = (let k = "k" ++ toString n in
    (n, Fun k $ App Opapp [
      Var (Short k); App Opderef [Var (Short $ "s" ++ explode x)]])) ∧
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

  cps_transform_app n tfn ts (e::es) k = (let
    (m, ce) = cps_transform n e;
    t = "t" ++ toString m;
    (l, inner) = cps_transform_app (m+1) tfn (t::ts) es k
  in
    (l, App Opapp [ce; Fun t inner])) ∧
  cps_transform_app n tfn ts [] k = (let
    (m, capp) = app_ml n k tfn;
  in
    (m, App Opapp [capp;cons_list (REVERSE ts)])) ∧

  cps_transform_seq n k [] = (n, Var (Short k)) ∧
  cps_transform_seq n k (e::es) = (let
    (m, ce) = cps_transform n e;
    (l, inner) = cps_transform_seq m k es
  in
    (l, Fun "_" $ App Opapp [ce; inner]))
Termination
  WF_REL_TAC ‘measure (λ x . case x of
    | INL(_,e) => exp_size e
    | INR(INL(_,_,_,es,_)) => list_size exp_size es
    | INR(INR(_,_,es)) => list_size exp_size es)’
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
  EVAL “evaluate <| clock := 999 |> myEnv [scheme_program_to_cake (Apply (Val $ Prim SMul) [Val $ SNum 2; Val $ SNum 3])]”
  EVAL “evaluate <| clock := 999; refs := [] |> myEnv [scheme_program_to_cake (Apply (Lambda [strlit "x"; strlit "y"] NONE (Ident $ strlit "x")) [Val $ SNum 5; Val $ SNum 4])]”
  EVAL “scheme_program_to_cake (Cond (Val $ SBool F) (Val $ SNum 420) (Val $ SNum 69))”
  EVAL “scheme_program_to_cake (Apply (Val $ Prim SMul) [Val $ SNum 2; Val $ SNum 3])”
  EVAL “scheme_program_to_cake (Apply (Lambda [] (SOME $ strlit "x") (Ident $ strlit "x")) [Val $ SNum 5])”
  EVAL “scheme_program_to_cake (Begin (Val $ SNum 0) [Val $ SNum 1; Val $ SNum 2])”
*)