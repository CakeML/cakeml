(*
  Implement and prove correct monadic version of encoder
*)
open preamble
open asmTheory lab_to_targetTheory

val _ = new_theory "monadic_enc"
(*
  This hash function is roughly a rolling hash
  The modulus m is a hash size parameter
*)
val hash_reg_imm_def = Define`
  (hash_reg_imm m (Reg reg) = reg) ∧
  (hash_reg_imm m (Imm imm) = 67n + (w2n imm MOD m))`

val hash_binop_def = Define`
  (hash_binop Add = 0n) ∧
  (hash_binop Sub = 1n) ∧
  (hash_binop And = 2n) ∧
  (hash_binop Or  = 3n) ∧
  (hash_binop Xor = 4n)`

val hash_cmp_def = Define`
  (hash_cmp Equal = 5n) ∧
  (hash_cmp Lower = 6n) ∧
  (hash_cmp Less  = 7n) ∧
  (hash_cmp Test  = 8n) ∧
  (hash_cmp NotEqual = 9n) ∧
  (hash_cmp NotLower = 10n) ∧
  (hash_cmp NotLess  = 11n) ∧
  (hash_cmp NotTest  = 12n)`

val hash_shift_def = Define`
  (hash_shift Lsl = 13n) ∧
  (hash_shift Lsr = 14n) ∧
  (hash_shift Asr = 15n) ∧
  (hash_shift Ror = 16n)`

val hash_memop_def = Define`
  (hash_memop Load   = 17n) ∧
  (hash_memop Load8  = 18n) ∧
  (hash_memop Store  = 19n) ∧
  (hash_memop Store8 = 20n)`

val roll_hash_def = Define`
  (roll_hash [] acc = acc) ∧
  (roll_hash (x::xs) acc = roll_hash xs (31n * acc + x))`

(*
Roughly, roll_hash [b;c;d;e] a
gives
roll_hash [b; c; d; e] a = 31 * (31 * (31 * (31 * a + b) + c) + d) + e

Try to put largest terms at the end of the list!
*)

val hash_arith_def = Define`
  (hash_arith m (Binop bop r1 r2 ri) =
    roll_hash [hash_binop bop; r1; r2; hash_reg_imm m ri] 21n) ∧
  (hash_arith m (Shift sh r1 r2 n) =
    roll_hash [hash_shift sh; r1; r2; n] 22n) ∧
  (hash_arith m (Div r1 r2 r3) =
    roll_hash [r1;r2;r3] 23n) ∧
  (hash_arith m (LongMul r1 r2 r3 r4) =
    roll_hash [r1;r2;r3;r4] 24n) ∧
  (hash_arith m (LongDiv r1 r2 r3 r4 r5) =
    roll_hash [r1;r2;r3;r4;r5] 25n) ∧
  (hash_arith m (AddCarry r1 r2 r3 r4) =
    roll_hash [r1;r2;r3;r4] 26n) ∧
  (hash_arith m (AddOverflow r1 r2 r3 r4) =
    roll_hash [r1;r2;r3;r4] 27n) ∧
  (hash_arith m (SubOverflow r1 r2 r3 r4) =
    roll_hash [r1;r2;r3;r4] 28n)`

val hash_fp_def = Define`
  (hash_fp (FPLess r f1 f2) =
    roll_hash [r;f1;f2] 29n) ∧
  (hash_fp (FPLessEqual r f1 f2) =
    roll_hash [r;f1;f2] 30n) ∧
  (hash_fp (FPEqual r f1 f2) =
    roll_hash [r;f1;f2] 31n) ∧

  (hash_fp (FPAbs f1 f2) =
    roll_hash [f1;f2] 32n) ∧
  (hash_fp (FPNeg f1 f2) =
    roll_hash [f1;f2] 33n) ∧
  (hash_fp (FPSqrt f1 f2) =
    roll_hash [f1;f2] 34n) ∧

  (hash_fp (FPAdd f1 f2 f3) =
    roll_hash [f1;f2;f3] 35n) ∧
  (hash_fp (FPSub f1 f2 f3) =
    roll_hash [f1;f2;f3] 36n) ∧
  (hash_fp (FPMul f1 f2 f3) =
    roll_hash [f1;f2;f3] 37n) ∧
  (hash_fp (FPDiv f1 f2 f3) =
    roll_hash [f1;f2;f3] 38n) ∧

  (hash_fp (FPFma f1 f2 f3) =
    roll_hash [f1;f2;f3] 39n) /\

  (hash_fp (FPMov f1 f2) =
    roll_hash [f1;f2] 40n) ∧
  (hash_fp (FPMovToReg r1 r2 f) =
    roll_hash [r1;r2;f] 41n) ∧
  (hash_fp (FPMovFromReg f r1 r2) =
    roll_hash [f;r1;r2] 42n) ∧
  (hash_fp (FPToInt f1 f2) =
    roll_hash [f1;f2] 43n) ∧
  (hash_fp (FPFromInt f1 f2) =
    roll_hash [f1;f2] 44n)`

val hash_inst_def = Define`
  (hash_inst m Skip = 45n) ∧
  (hash_inst m (Const r w) =
    roll_hash [r;w2n w MOD m] 46n) ∧
  (hash_inst m (Arith a) =
    roll_hash [hash_arith m a] 47n) ∧
  (hash_inst m (Mem mop r (Addr rr w)) =
    roll_hash [hash_memop mop; r; rr; w2n w MOD m] 48n) ∧
  (hash_inst m (FP fp) =
    roll_hash [hash_fp fp] 49n)`

val hash_asm_def = Define`
  (hash_asm m (Inst i) =
    roll_hash [hash_inst m i] 50n) ∧
  (hash_asm m (Jump w) =
    roll_hash [w2n w MOD m] 51n) ∧
  (hash_asm m (JumpCmp c r ri w) =
    roll_hash [hash_cmp c; r; hash_reg_imm m ri; w2n w MOD m] 52n) ∧
  (hash_asm m (Call w) =
    roll_hash [w2n w MOD m] 53n) ∧
  (hash_asm m (JumpReg r) =
    roll_hash [r] 54n) ∧
  (hash_asm m (Loc r w) =
    roll_hash [r; w2n w MOD m] 55n)`

val _ = export_theory();
