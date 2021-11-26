(*
  Definitions of the floating point operations used in CakeML.
*)
open HolKernel Parse boolLib bossLib;
open libTheory machine_ieeeTheory;

val _ = numLib.prefer_num();

val _ = new_theory "fpSem"

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


val _ = Define `
 ((fp_cmp:fp_cmp -> word64 -> word64 -> bool) fop=  ((case fop of
    FP_Less => fp64_lessThan
  | FP_LessEqual => fp64_lessEqual
  | FP_Greater => fp64_greaterThan
  | FP_GreaterEqual => fp64_greaterEqual
  | FP_Equal => fp64_equal
)))`;

val _ = Define `
 ((fp_uop:fp_uop -> word64 -> word64) fop=  ((case fop of
    FP_Abs => fp64_abs
  | FP_Neg => fp64_negate
  | FP_Sqrt => fp64_sqrt roundTiesToEven
)))`;

val _ = Define `
 ((fp_bop:fp_bop -> word64 -> word64 -> word64) fop=  ((case fop of
    FP_Add => fp64_add roundTiesToEven
  | FP_Sub => fp64_sub roundTiesToEven
  | FP_Mul => fp64_mul roundTiesToEven
  | FP_Div => fp64_div roundTiesToEven
)))`;

val _ = Define `
 ((fpfma:word64 -> word64 -> word64 -> word64) v1 v2 v3=  (fp64_mul_add roundTiesToEven v2 v3 v1))`;

val _ = Define `
 ((fp_top:fp_top -> word64 -> word64 -> word64 -> word64) fop=  ((case fop of
    FP_Fma => fpfma
)))`;

val _ = export_theory()
