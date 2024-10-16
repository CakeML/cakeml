(*
  Values used to model floating-points, in the style of Icing
*)
open HolKernel Parse boolLib bossLib;
open miscTheory;

val _ = numLib.temp_prefer_num();

val _ = new_theory "fpValTree";

(*
  Definition of floating point value trees for CakeML
*)
(*open import Pervasives*)
(*open import Lib*)

Datatype:
  fp_opt =   Opt | NoOpt
End

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

Datatype:
 fp_word_val =
       Fp_const word64
     | Fp_uop fp_uop fp_word_val
     | Fp_bop fp_bop fp_word_val fp_word_val
     | Fp_top fp_top fp_word_val fp_word_val fp_word_val
     | Fp_wopt fp_opt fp_word_val
End

Datatype:
 fp_bool_val =
       Fp_cmp fp_cmp fp_word_val fp_word_val
     | Fp_bopt fp_opt fp_bool_val
End

Definition fp_cmp_def:
  fp_cmp fop f1 f2 = Fp_cmp fop f1 f2
End

Definition fp_uop_def:
  fp_uop fop f1 = Fp_uop fop f1
End

Definition fp_bop_def:
  fp_bop fop f1 f2 = Fp_bop fop f1 f2
End

Definition fp_top_def:
 fp_top fop f1 f2 f3 = Fp_top fop f1 f2 f3
End

val _ = export_theory()
