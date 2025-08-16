(*
  Definitions of the floating point operations used in CakeML.
*)
Theory fpSem
Ancestors
  fpValTree fpOpt machine_ieee

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
  | fpValTree$FP_Add => (fp64_add roundTiesToEven)
  | fpValTree$FP_Sub => (fp64_sub roundTiesToEven)
  | fpValTree$FP_Mul => (fp64_mul roundTiesToEven)
  | fpValTree$FP_Div => (fp64_div roundTiesToEven)
End

Definition fpfma_def:
  fpfma v1 v2 v3 = fp64_mul_add roundTiesToEven v2 v3 v1
End

Definition fp_top_comp_def:
  fp_top_comp fop = fpfma
End

Definition fp_opt_comp_def:
  fp_opt_comp fpopt v = (case fpopt of Opt => v | NoOpt => v)
End

(* Compression function for value trees,
   evaluating lazy trees into word64 or bool *)
Definition compress_word_def:
 compress_word (Fp_const w1) =  w1 ∧
 compress_word (Fp_uop u1 v1) = (fp_uop_comp u1 (compress_word v1)) ∧
 compress_word (Fp_bop b v1 v2) = (fp_bop_comp b (compress_word v1) (compress_word v2)) ∧
 compress_word (Fp_top t v1 v2 v3) =
   (fp_top_comp t (compress_word v1) (compress_word v2) (compress_word v3)) ∧
 compress_word (Fp_wopt fpopt v) =  (compress_word v)
End

Definition compress_bool_def:
  compress_bool (Fp_cmp cmp v1 v2) =
    (fp_cmp_comp cmp (compress_word v1) (compress_word v2)) ∧
  compress_bool (Fp_bopt fpopt v)=  (compress_bool v)
End

