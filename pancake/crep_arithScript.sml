(*
  Simplification of arithmetic in crepLang.
*)
open preamble crepLangTheory

val _ = new_theory "crep_arith"

val _ = set_grammar_ancestry
        ["crepLang"];


Definition dest_const_def:
  dest_const (Const w) = SOME w /\
  dest_const _ = NONE
End

Definition dest_2exp_def:
  dest_2exp n w = if w = 0w then NONE
    else if w = 1w then SOME n
    else if (w && 1w) <> 0w then NONE
    else dest_2exp (n + 1n) (word_lsr w 1n)
End

Triviality dest_2exp_lemma:
  ! i w n. dest_2exp i w = SOME n ==>
  i <= n /\ w = word_lsl 1w (n - i)
Proof
  ho_match_mp_tac dest_2exp_ind
  \\ rpt gen_tac
  \\ rpt disch_tac
  \\ rw [Once dest_2exp_def]
  \\ fs []
  \\ qsuff_tac `alignment$aligned 1n w`
  >- (
    rw []
    \\ fs [aligned_def]
    \\ pop_assum (ONCE_REWRITE_TAC o single o GSYM)
    \\ simp [align_shift]
  )
  >- (
    simp [aligned_bitwise_and]
  )
QED

Theorem dest_2exp_thm:
  dest_2exp 0n w = SOME n2 ==>
  w = word_lsl 1w n2
Proof
  rw [] \\ imp_res_tac dest_2exp_lemma \\ fs []
QED

Definition mul_const_def:
  mul_const exp c = if c = 0w then Const 0w
    else if c = 1w then exp
    else (case dest_2exp 0n c of
      | NONE => Crepop Mul [exp; Const c]
      | SOME i => Shift Lsl exp i
    )
End

Definition simp_exp_def:
  (simp_exp (Crepop op exps) =
    let exps = MAP simp_exp exps in
    case (op, exps) of
    | (Mul, [exp1; exp2]) => (
        case (dest_const exp1, dest_const exp2) of
        | (SOME c, SOME c2) => Const (c * c2)
        | (SOME c, _) => mul_const exp2 c
        | (_, SOME c) => mul_const exp1 c
        | _ => Crepop op exps
    )
    | _ => Crepop op exps
  ) /\
  simp_exp (Load32 exp) = Load32 (simp_exp exp) /\
  simp_exp (LoadByte exp) = LoadByte (simp_exp exp) /\
  simp_exp (Load exp) = Load (simp_exp exp) /\
  simp_exp (Op bop exps) = Op bop (MAP simp_exp exps) /\
  simp_exp (Cmp cmp exp1 exp2) = Cmp cmp (simp_exp exp1) (simp_exp exp2) /\
  simp_exp (Shift s exp n) = Shift s (simp_exp exp) n /\
  simp_exp exp = exp
Termination
  WF_REL_TAC `measure (exp_size (K 0))`
End

Definition simp_prog_def:
  simp_prog (Dec v exp p) = Dec v (simp_exp exp) (simp_prog p) /\
  simp_prog (Assign v exp) = Assign v (simp_exp exp) /\
  simp_prog (Store exp1 exp2) = Store (simp_exp exp1) (simp_exp exp2) /\
  simp_prog (Store32 exp1 exp2) = Store32 (simp_exp exp1) (simp_exp exp2) /\
  simp_prog (StoreByte exp1 exp2) = StoreByte (simp_exp exp1) (simp_exp exp2) /\
  simp_prog (StoreGlob g exp) = StoreGlob g (simp_exp exp) /\
  simp_prog (Seq p1 p2) = Seq (simp_prog p1) (simp_prog p2) /\
  simp_prog (If exp p1 p2) = If (simp_exp exp) (simp_prog p1) (simp_prog p2) /\
  simp_prog (While exp p) = While (simp_exp exp) (simp_prog p) /\
  simp_prog (Call call_type e exps) = (
    let call_type2 = case call_type of
      | NONE => NONE
      | SOME (rv, rp, opt_handler) => SOME (rv, simp_prog rp, case opt_handler of
          | NONE => NONE
          | SOME (ix, ep) => SOME (ix, simp_prog ep)
      ) in
    Call call_type2 e (MAP simp_exp exps)
  ) /\
  simp_prog (Return exp) = Return (simp_exp exp) /\
  simp_prog (ShMem op vn exp) = ShMem op vn (simp_exp exp) /\
  simp_prog p = p
End

val _ = export_theory();
