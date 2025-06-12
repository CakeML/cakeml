(*
  Definitions of the floating point operations used in CakeML.
*)
open HolKernel Parse boolLib bossLib;
open astTheory machine_ieeeTheory;

val _ = new_theory "fpSem";

Definition fp_cmp_comp_def:
  fp_cmp_comp fop =
  case fop of
    FP_Less => fp64_lessThan
  | FP_LessEqual => fp64_lessEqual
  | FP_Greater => fp64_greaterThan
  | FP_GreaterEqual => fp64_greaterEqual
  | FP_Equal => fp64_equal
End

Definition fp_uop_comp_def:
  fp_uop_comp fop =
  case fop of
    FP_Abs => fp64_abs
  | FP_Neg => fp64_negate
  | FP_Sqrt => fp64_sqrt roundTiesToEven
End

Definition fp_bop_comp_def:
  fp_bop_comp fop =
  case fop of
  | FP_Add => fp64_add roundTiesToEven
  | FP_Sub => fp64_sub roundTiesToEven
  | FP_Mul => fp64_mul roundTiesToEven
  | FP_Div => fp64_div roundTiesToEven
End

Definition fpfma_def:
  fpfma v1 v2 v3 = fp64_mul_add roundTiesToEven v2 v3 v1
End

Definition fp_top_comp_def:
  fp_top_comp fop = fpfma
End

val _ = export_theory();
