(*
  Real-valued operations for source semantics
*)
open HolKernel Parse boolLib bossLib;
open miscTheory machine_ieeeTheory realTheory;

val _ = new_theory "realOps";

(*
  Definition of real-valued operations
*)

Datatype:
  real_cmp =
    Real_Less | Real_LessEqual | Real_Greater | Real_GreaterEqual | Real_Equal
End

Datatype:
 real_uop = Real_Abs | Real_Neg | Real_Sqrt
End

Datatype:
  real_bop = Real_Add | Real_Sub | Real_Mul | Real_Div
End

Definition real_cmp_def:
  real_cmp fop =
  (case fop of
     Real_Less => (<)
   | Real_LessEqual => (<=)
   | Real_Greater => (>)
   | Real_GreaterEqual => (>=)
   | Real_Equal => (=))
End

Definition real_uop_def:
  real_uop fop =
  (case fop of
    Real_Abs => (\ n. (if n >(real_of_num 0) then n else(real_of_num 0) - n))
  | Real_Neg => ((\ n. (real_of_num 0) - n))
  | Real_Sqrt => sqrt)
End

Definition real_bop_def:
  real_bop fop =
  (case fop of
     Real_Add => (+)
   | Real_Sub => (-)
   | Real_Mul => ( * )
   | Real_Div => (/))
End

val _ = export_theory();
