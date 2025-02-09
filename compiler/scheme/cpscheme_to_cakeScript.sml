(*
  Translation from CPScheme to CakeML
*)
open preamble;
open astTheory;
open mlstringTheory;
open scheme_astTheory;
open cpscheme_astTheory;

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
  app_ml n = let
    t = "t" ++ toString n;
    rfex = Fun "_" $ App Opapp [Var (Short "print"); Lit $ StrLit"Not a procedure"]
  in
    (n+1, Fun t $ Mat (Var (Short t)) [
      (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "SAdd") []], Var (Short "sadd"));
      (Pcon (SOME $ Short "Prim") [Pcon (SOME $ Short "SMul") []], Var (Short "smul"));
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
    (l, rfk) = refunc_cont m k;
    k' = "k" ++ toString l;
    t = "t" ++ toString (l+1)
  in
    (*(l+2, Fun k' $ App Opapp [rfc;
      Fun t $ App Opapp [Var (Short k'); App Opapp [rfk; Var (Short t)]]])) ∧*)

    (*not tail-call?*)
    (*(l+2, Fun k' $ App Opapp [App Opapp [rfc; rfk]; Var (Short k')])) ∧*)
    (l+2, Fun k' $ App Opapp [rfc;
      Fun t $ App Opapp [App Opapp [rfk; Var (Short t)]; Var (Short k')]])) ∧

  refunc_cont n (CondK t f) = (let
    (m, rft) = refunc n t;
    (l, rff) = refunc m f;
    p = "t" ++ toString l
  in
    (l+1, Fun p $ Mat (Var (Short p)) [
      (Pcon (SOME $ Short "SBool") [Plit $ IntLit 0], rff);
      (Pany, rft)
    ])) ∧
  refunc_cont n (ApplyK NONE cs) = (let t = "t" ++ toString n in
    case cs of
    | [] => (n+1, Fun t (Var (Short t)))
    | c::cs' => let
      t = "t" ++ toString n;
      (m, rfc) = refunc_app (n+1) t [] cs
    in
      (m+1, Fun t rfc)
    ) ∧

  refunc_app n tfn ts (c::cs) = (let
    (m, rfc) = refunc n c;
    t = "t" ++ toString m;
    (l, inner) = refunc_app (m+1) tfn (t::ts) cs
  in
    (l, Fun t $ App Opapp [rfc; inner])) ∧
  refunc_app n tfn ts [] = (let
    (m, rfapp) = app_ml n;
  in
    (m, App Opapp [rfapp;Var (Short tfn);cons_list (REVERSE ts)]))
Termination
  WF_REL_TAC ‘measure $ λ x . case x of
    | INL(_,c) => cexp_size c
    | INR(INL(_,k)) => cont_size cexp_size k
    | INR(INR(_,_,_,cs)) => list_size cexp_size cs’
End

Definition scheme_program_to_cake_def:
  scheme_program_to_cake p = App Opapp [SND (refunc 0 p); Fun "t" $ Var (Short "t")]
End

(*
  open cpscheme_to_cakeTheory;
  open scheme_to_cpschemeTheory;
  open evaluateTheory;

  EVAL “evaluate st env [scheme_program_to_cake (cps_transform (Cond (Val $ SBool F) (Val $ SNum 420) (Val $ SNum 69)))]”
  EVAL “refunc 0 (cps_transform (Apply (Val $ Prim SAdd) [Val $ SNum 2]))”
*)

val _ = export_theory();