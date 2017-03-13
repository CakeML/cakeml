open preamble machine_ieeeTheory;

val _ = new_theory "fpSem";

val _ = Datatype `
  fp_cmp =
    FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | FP_Equal `

val _ = Datatype `
  fp_uop =
    FP_Abs | FP_Neg | FP_Sqrt `

val _ = Datatype `
  fp_bop =
    FP_Add | FP_Sub | FP_Mul | FP_Div `

val fp_cmp_def = Define `
  fp_cmp FP_Less w1 w2 = fp64_lessThan w1 w2 /\
  fp_cmp FP_LessEqual w1 w2 = fp64_lessEqual w1 w2 /\
  fp_cmp FP_Greater w1 w2 = fp64_greaterThan w1 w2 /\
  fp_cmp FP_GreaterEqual w1 w2 = fp64_greaterEqual w1 w2 /\
  fp_cmp FP_Equal w1 w2 = fp64_equal w1 w2`

val fp_uop_def = Define `
  fp_uop FP_Abs w = fp64_abs w /\
  fp_uop FP_Neg w = fp64_negate w /\
  fp_uop FP_Sqrt w = fp64_sqrt roundTiesToEven w`

val fp_bop_def = Define `
  fp_bop FP_Add w1 w2 = fp64_add roundTiesToEven w1 w2 /\
  fp_bop FP_Sub w1 w2 = fp64_sub roundTiesToEven w1 w2 /\
  fp_bop FP_Mul w1 w2 = fp64_mul roundTiesToEven w1 w2 /\
  fp_bop FP_Div w1 w2 = fp64_div roundTiesToEven w1 w2`

val _ = export_theory();
