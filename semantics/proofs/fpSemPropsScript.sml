(*
  Properties of floating-point value tree semantics
*)

open preamble fpSemTheory fpValTreeTheory;
open terminationTheory;

val _ = new_theory "fpSemProps";

Theorem compress_word_valid:
  ! v.
    isFpWordOp v ==>
    ? w. compress v =  SOME (Fp_word w)
Proof
  Induct_on `v` \\ fs[isFpWordOp_def, compress_def] \\ rpt strip_tac
  \\ res_tac \\ fs[]
QED

Theorem compress_bool_valid:
  ! v.
    isFpBoolOp v ==>
    ? b. compress v = SOME (Fp_bool b)
Proof
  Induct_on `v` \\ fs[isFpBoolOp_def, compress_def] \\ rpt strip_tac
  \\ imp_res_tac compress_word_valid \\ fs[]
QED

val _ = export_theory();
