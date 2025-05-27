(*
  Values used to model floating-points, in the style of Icing
*)
open HolKernel Parse boolLib bossLib;
open miscTheory;

val _ = numLib.temp_prefer_num();

val _ = new_theory "fpValTree";

Datatype:
  fp_cmp = FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | FP_Equal
End

Datatype:
  fp_uop = FP_Abs | FP_Neg | FP_Sqrt
End

Datatype:
  fp_bop = FP_Add | FP_Sub | FP_Mul | FP_Div
End

Datatype:
  fp_top = FP_Fma
End

val _ = export_theory()
