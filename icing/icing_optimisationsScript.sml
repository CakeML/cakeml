(*
  Icing optimisations supported by CakeML
  This file defines all the optimisations that can be used by the Icing
  optimizer, defined in source_to_sourceScript.
  Correctness proofs for each optimisation are in the file
  icing_optimisationProofsScript.
*)
open bossLib;
open fpValTreeTheory fpOptTheory;

open preamble;

val _ = new_theory "icing_optimisations";

(*
  Generator for commutativity rewrites
*)
Definition fp_comm_gen_def:
  fp_comm_gen op = (Binop op (Var 0) (Var 1), Binop op (Var 1) (Var 0))
End

(* Commutativity of + *)
val fp_add_comm_def =
  curry save_thm "fp_add_comm_def" (Q.SPEC `FP_Add` fp_comm_gen_def);

(* Commutativity of * *)
val fp_mul_comm_def =
  curry save_thm "fp_mul_comm_def" (Q.SPEC `FP_Mul` fp_comm_gen_def);

(*
  Generator for associativity rewrites
*)
Definition fp_assoc_gen_def:
  fp_assoc_gen op = (Binop op (Binop op (Var 0) (Var 1)) (Var 2),
                     Binop op (Var 0) (Binop op (Var 1) (Var 2)))
End

(* Associativity of + *)
val fp_add_assoc_def =
  curry save_thm "fp_add_assoc_def"
    (Q.SPEC `FP_Add` fp_assoc_gen_def);

(* Associativity of * *)
val fp_mul_assoc_def =
  curry save_thm "fp_mul_assoc_def"
    (Q.SPEC `FP_Mul` fp_assoc_gen_def);

(*
  FMA introudction
*)
Definition fp_fma_intro_def:
  fp_fma_intro = (Binop FP_Add (Binop FP_Mul (Var 0) (Var 1)) (Var 2),
                  Terop FP_Fma (Var 2) (Var 0) (Var 1))
End

(* Subtraction -> Addtion of inverse *)
Definition fp_sub_add_def:
  fp_sub_add = (Binop FP_Sub (Var 0) (Var 1),
                Binop FP_Add (Var 0) (Unop FP_Neg (Var 1)))
End

(* Unary - can be pushed into multiplications; this matches a addition above,
as the bottom-up traversal will not apply the rewrite otherwise *)
Definition fp_neg_push_mul_r_def:
  fp_neg_push_mul_r =
  (Binop FP_Add (Unop FP_Neg (Binop FP_Mul (Var 0) (Var 1))) (Var 2),
   Binop FP_Add (Binop FP_Mul (Var 0) (Unop FP_Neg (Var 1))) (Var 2))
End

val _ = export_theory ();
