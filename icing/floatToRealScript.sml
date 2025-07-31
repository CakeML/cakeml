(*
  Translation from CakeML floating-point computations to
  CakeML real-number computations.
*)
Theory floatToReal
Ancestors
  semanticPrimitives evaluate fpOpt fpValTree
Libs
  preamble

(**
  Translation from floats to reals, needed for correctness proofs, thus we
  define it here
**)
Definition getRealCmp_def:
  getRealCmp (FP_Less) = Real_Less ∧
  getRealCmp (FP_LessEqual) = Real_LessEqual ∧
  getRealCmp (FP_Greater) = Real_Greater ∧
  getRealCmp (FP_GreaterEqual) = Real_GreaterEqual ∧
  getRealCmp (FP_Equal) = Real_Equal
End

Definition getRealUop_def:
  getRealUop (FP_Abs) = Real_Abs ∧
  getRealUop (FP_Neg) = Real_Neg ∧
  getRealUop (FP_Sqrt) = Real_Sqrt
End

Definition getRealBop_def:
  getRealBop (FP_Add) = Real_Add ∧
  getRealBop (FP_Sub) = Real_Sub ∧
  getRealBop (FP_Mul) = Real_Mul ∧
  getRealBop (FP_Div) = Real_Div
End

Definition realify_def:
  realify (Lit (Word64 w)) = Lit (Word64 w) (* RealFromFP added in App case *)∧
  realify (Lit l) = Lit l ∧
  realify (Var x) = Var x ∧
  realify (Raise e) = Raise (realify e) ∧
  realify (Handle e pes) =
    Handle (realify e) (MAP (\ (p,e). (p, realify e)) pes) ∧
  realify (Con mod exps) = Con mod (MAP realify exps) ∧
  realify (Fun s e) = Fun s (realify e) ∧
  realify (App op exps) =
    (let exps_real = MAP realify exps in
     case op of
     | FpFromWord => App  RealFromFP exps_real
     | FP_cmp cmp => App (Real_cmp (getRealCmp cmp)) exps_real
     | FP_uop uop => App (Real_uop (getRealUop uop)) exps_real
     | FP_bop bop => App (Real_bop (getRealBop bop)) exps_real
     | FP_top _ =>
     (case exps of
      | [e1; e2; e3] => App (Real_bop (Real_Add)) [
                          App (Real_bop (Real_Mul)) [realify e2; realify e3]; realify e1]
      | _ => App op []) (* malformed expression, return garbled output *)
     | _ => App op exps_real) ∧
  realify (Log lop e2 e3) =
    Log lop (realify e2) (realify e3) ∧
  realify (If e1 e2 e3) =
    If (realify e1) (realify e2) (realify e3) ∧
  realify (Mat e pes) =
    Mat (realify e) (MAP (λ(p,e). (p, realify e)) pes) ∧
  realify (Let so e1 e2) =
    Let so (realify e1) (realify e2) ∧
  realify (Letrec ses e) =
    Letrec (MAP (λ (s1,s2,e). (s1, s2, realify e)) ses) (realify e) ∧
  realify (Tannot e t) = Tannot (realify e) t ∧
  realify (Lannot e l) = Lannot (realify e) l ∧
  realify (FpOptimise fpopt e) = FpOptimise fpopt (realify e)
Termination
  wf_rel_tac ‘measure exp_size’
End

