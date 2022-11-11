(*
  Peephole optimisations used by PrincessCake
  This file defines all the optimisations that are can be used by the
  PrincessCake optimiser, defined in source_to_source2Script.sml .
  The local correctness proofs for each optimisation are in the file
  icing_optimisationProofsScript.
*)
open bossLib;
open fpOptTheory;

open preamble;

val _ = new_theory "icing_optimisations";

Definition reverse_tuple_def:
  reverse_tuple (a, b) = (b, a)
End

(*
  Generator for commutativity rewrites
*)
Definition fp_comm_gen_def:
  fp_comm_gen op = (Binop op (PatVar 0) (PatVar 1), Binop op (PatVar 1) (PatVar 0))
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
  fp_assoc_gen op = (Binop op (Binop op (PatVar 0) (PatVar 1)) (PatVar 2),
                     Binop op (PatVar 0) (Binop op (PatVar 1) (PatVar 2)))
End

(* Associativity of + *)
val fp_add_assoc_def =
  curry save_thm "fp_add_assoc_def"
    (Q.SPEC `FP_Add` fp_assoc_gen_def);

(* Associativity of * *)
val fp_mul_assoc_def =
  curry save_thm "fp_mul_assoc_def"
    (Q.SPEC `FP_Mul` fp_assoc_gen_def);

Definition fp_assoc2_gen_def:
  fp_assoc2_gen op = reverse_tuple (fp_assoc_gen op)
End

(* Associativity of + *)
val fp_add_assoc2_def =
  curry save_thm "fp_add_assoc2_def"
    (Q.SPEC `FP_Add` fp_assoc2_gen_def);

(* Associativity of * *)
val fp_mul_assoc2_def =
  curry save_thm "fp_mul_assoc2_def"
    (Q.SPEC `FP_Mul` fp_assoc2_gen_def);

(*
  FMA introudction
*)
Definition fp_fma_intro_def:
  fp_fma_intro = (Binop FP_Add (Binop FP_Mul (PatVar 0) (PatVar 1)) (PatVar 2),
                  Terop FP_Fma (PatVar 2) (PatVar 0) (PatVar 1))
End

(* Subtraction -> Addition of inverse *)
Definition fp_sub_add_def:
  fp_sub_add = (Binop FP_Sub (PatVar 0) (PatVar 1),
                Binop FP_Add (PatVar 0) (Unop FP_Neg (PatVar 1)))
End

Definition fp_add_sub_def:
  fp_add_sub = reverse_tuple fp_sub_add
End

Definition fp_times_minus_one_neg_def:
  (* 13830554455654793216 is -1.0 in binary representation *)
  fp_times_minus_one_neg = (Binop FP_Mul (PatVar 0) (Word (13830554455654793216w: word64)), Unop FP_Neg (PatVar 0))
End

Definition fp_neg_times_minus_one_def:
  fp_neg_times_minus_one = reverse_tuple fp_times_minus_one_neg
End

(* Unary - can be pushed into multiplications; this matches a addition above,
as the bottom-up traversal will not apply the rewrite otherwise *)
Definition fp_neg_push_mul_r_def:
  fp_neg_push_mul_r =
  (Binop FP_Add (Unop FP_Neg (Binop FP_Mul (PatVar 0) (PatVar 1))) (PatVar 2),
   Binop FP_Add (Binop FP_Mul (PatVar 0) (Unop FP_Neg (PatVar 1))) (PatVar 2))
End

Definition fp_times_two_to_add_def:
  (* 2.0 is 4611686018427387904 in binary representation *)
  fp_times_two_to_add = (Binop FP_Mul (PatVar 0) (Word (4611686018427387904w: word64)),
                         Binop FP_Add (PatVar 0) (PatVar 0))
End

Definition fp_times_three_to_add_def:
  (* 3.0 is 4613937818241073152 in binary representation *)
  fp_times_three_to_add = (Binop FP_Mul (PatVar 0) (Word (4613937818241073152w: word64)),
                           Binop FP_Add (Binop FP_Add (PatVar 0) (PatVar 0)) (PatVar 0))
End

Definition fp_times_zero_def:
  fp_times_zero = (Binop FP_Mul (PatVar 0) (Word (0w: word64)), Word (0w: word64))
End

Definition fp_plus_zero_def:
  fp_plus_zero = (Binop FP_Add (PatVar 0) (Word (0w: word64)), (PatVar 0))
End

Definition fp_times_one_def:
  (* 4607182418800017408 is 1.0 in binary representation *)
  fp_times_one = (Binop FP_Mul (PatVar 0) (Word (4607182418800017408w: word64)), (PatVar 0))
End

Definition fp_times_into_div_def:
  fp_times_into_div = (Binop FP_Mul (Binop FP_Div (PatVar 0) (PatVar 1)) (PatVar 2), Binop FP_Div (Binop FP_Mul (PatVar 0) (PatVar 2)) (PatVar 1))
End

Definition fp_same_sub_def:
  fp_same_sub = (Binop FP_Sub (PatVar 0) (PatVar 0), (Word (0w: word64)))
End

Definition fp_same_div_def:
  (* 4607182418800017408 is 1.0 in binary representation *)
  fp_same_div = (Binop FP_Div (PatVar 0) (PatVar 0), (Word (4607182418800017408w: word64)))
End

Definition fp_distribute_gen_def:
  fp_distribute_gen opInner opOuter = (Binop opOuter (Binop opInner (PatVar 0) (PatVar 2)) (Binop opInner (PatVar 1) (PatVar 2)),
                                       Binop opInner (Binop opOuter (PatVar 0) (PatVar 1)) (PatVar 2))
End

(* Distributivity of * and + *)
val fp_mul_add_distribute_def =
  curry save_thm "fp_mul_add_distribute_def"
    (Q.SPECL [‘FP_Mul’, ‘FP_Add’] fp_distribute_gen_def);

(* Distributivity of * and - *)
val fp_mul_sub_distribute_def =
  curry save_thm "fp_mul_sub_distribute_def"
    (Q.SPECL [‘FP_Mul’, ‘FP_Sub’] fp_distribute_gen_def);

(* Distributivity of / and + *)
val fp_div_add_distribute_def =
  curry save_thm "fp_div_add_distribute_def"
    (Q.SPECL [‘FP_Div’, ‘FP_Add’] fp_distribute_gen_def);

(* Distributivity of / and - *)
val fp_div_sub_distribute_def =
  curry save_thm "fp_div_sub_distribute_def"
    (Q.SPECL [‘FP_Div’, ‘FP_Sub’] fp_distribute_gen_def);

Definition fp_undistribute_gen_def:
  fp_undistribute_gen opInner opOuter = reverse_tuple (fp_distribute_gen opInner opOuter)
End

(* Reverse Distributivity of * and + *)
val fp_mul_add_undistribute_def =
  curry save_thm "fp_mul_add_undistribute_def"
    (Q.SPECL [‘FP_Mul’, ‘FP_Add’] fp_undistribute_gen_def);

(* Reverse Distributivity of * and - *)
val fp_mul_sub_undistribute_def =
  curry save_thm "fp_mul_sub_undistribute_def"
    (Q.SPECL [‘FP_Mul’, ‘FP_Sub’] fp_undistribute_gen_def);

(* Reverse Distributivity of / and + *)
val fp_div_add_undistribute_def =
  curry save_thm "fp_div_add_undistribute_def"
    (Q.SPECL [‘FP_Div’, ‘FP_Add’] fp_undistribute_gen_def);

(* Reverse Distributivity of / and - *)
val fp_div_sub_undistribute_def =
  curry save_thm "fp_div_sub_undistribute_def"
    (Q.SPECL [‘FP_Div’, ‘FP_Sub’] fp_undistribute_gen_def);

val _ = export_theory ();
