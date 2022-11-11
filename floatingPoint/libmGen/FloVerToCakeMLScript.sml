(*
  Translation from CakeML floating-point kernels to FloVer input
*)

(* HOL *)
open binary_ieeeTheory machine_ieeeTheory lift_ieeeTheory;
(* CakeML *)
open astTheory;
(* FloVer *)
open ExpressionsTheory IEEE_connectionTheory;
(* Dandelion *)
open checkerDefsTheory;
open preamble;

val _ = new_theory "FloVerToCakeML";

(** Translation from FloVer AST to CakeML AST **)
Definition bopTofpBop_def:
  bopTofpBop Expressions$Plus = FP_Add ∧
  bopTofpBop Sub = FP_Sub ∧
  bopTofpBop Mult = FP_Mul ∧
  bopTofpBop Div = FP_Div
End

Definition toFloVerFloatExp_def:
  toFloVerFloatExp (Expressions$Var i) = Expressions$Var i ∧
  toFloVerFloatExp (Const m c) = Const M64 c ∧
  toFloVerFloatExp (Unop Neg e) = Unop Neg (toFloVerFloatExp e) ∧
  toFloVerFloatExp (Binop b e1 e2) =
    Binop b (toFloVerFloatExp e1) (toFloVerFloatExp e2) ∧
  toFloVerFloatExp (Fma e1 e2 e3) =
    Fma (toFloVerFloatExp e1) (toFloVerFloatExp e2) (toFloVerFloatExp e3) ∧
  toFloVerFloatExp (Downcast m e) =
    Downcast M64 (toFloVerFloatExp e)
End

Definition toCmlFloatExp_def:
  toCmlFloatExp (Expressions$Var i):ast$exp option =
    SOME $ ast$Var (Short ("x" ++ (toString i))) ∧
  toCmlFloatExp (Const M64 c) =
    SOME $ App FpFromWord [Lit (Word64 (float_to_fp64 ((real_to_float dmode c):(52, 11) float)))] ∧
  toCmlFloatExp (Unop Neg e) =
    (case toCmlFloatExp e of
    | NONE => NONE
    | SOME e1 => SOME $ App (FP_uop FP_Neg) [e1]) ∧
  toCmlFloatExp (Binop op e1 e2) =
    (case toCmlFloatExp e1 of
    | NONE => NONE
    | SOME e1F =>
      case toCmlFloatExp e2 of
      | NONE => NONE
      | SOME e2F =>
        SOME $ App (FP_bop (bopTofpBop op)) [e1F; e2F]) ∧
  toCmlFloatExp (Fma e1 e2 e3) =
    (case toCmlFloatExp e1 of
    | NONE => NONE
    | SOME e1F =>
      case toCmlFloatExp e2 of
      | NONE => NONE
      | SOME e2F =>
        case toCmlFloatExp e3 of
        | NONE => NONE
        | SOME e3F =>
          SOME $ App (FP_top FP_Fma) [e3F; e1F; e2F]) ∧
  toCmlFloatExp _ = NONE
End

Definition toCmlFloatProg_def:
  toCmlFloatProg e =
  case toCmlFloatExp e of
  | NONE => NONE
  | SOME p => SOME $ FpOptimise NoOpt p
End

Definition bopToRealBop_def:
  bopToRealBop Expressions$Plus = Real_Add ∧
  bopToRealBop Sub = Real_Sub ∧
  bopToRealBop Mult = Real_Mul ∧
  bopToRealBop Div = Real_Div
End

Definition toCmlRealExp_def:
  toCmlRealExp (Expressions$Var i):ast$exp option =
    SOME $ ast$Var (Short ("x" ++ (toString i))) ∧
  (** FIXME **)
  toCmlRealExp (Const M64 (c,d)) =
    SOME $ App (RealFromIntProd) [Lit (IntLit c); Lit (IntLit d)] ∧
  toCmlRealExp (Unop Neg e) =
    (case toCmlRealExp e of
    | NONE => NONE
    | SOME e1 => SOME $ App (Real_uop Real_Neg) [e1]) ∧
  toCmlRealExp (Binop op e1 e2) =
    (case toCmlRealExp e1 of
    | NONE => NONE
    | SOME e1R =>
      case toCmlRealExp e2 of
      | NONE => NONE
      | SOME e2R =>
        SOME $ App (Real_bop (bopToRealBop op)) [e1R; e2R]) ∧
  toCmlRealExp (Fma e1 e2 e3) =
    (case toCmlRealExp e1 of
    | NONE => NONE
    | SOME e1R =>
      case toCmlRealExp e2 of
      | NONE => NONE
      | SOME e2R =>
        case toCmlRealExp e3 of
        | NONE => NONE
        | SOME e3R =>
          SOME $ App (Real_bop Real_Add) [App (Real_bop Real_Mul) [e1R; e2R]; e3R]) ∧
  toCmlRealExp _ = NONE
End

Definition getPrecondFromCert_def:
  getPrecondFromCert cert = λ (x:num). if x = 0 then SND (HD cert.iv) else (0,0:real)
End

val _ = export_theory ();
