(*
  Simplification of arithmetic in crepLang.
*)
Theory crep_arith
Ancestors
  crepLang
Libs
  preamble

Definition dest_const_def:
  dest_const (Const w) = SOME w /\
  dest_const _ = NONE
End

Definition mul_const_def:
  mul_const aw exp c =
    let u = Num (c % &(2 ** arch_width_bits aw)) in
    if u = 0 then Const 0
    else if u = 1 then exp
    else if u = 2 ** LOG2 u then Shift Lsl exp (Const (&(LOG2 u)))
    else Crepop Mul [exp; Const c]
End

Definition simp_exp_def:
  (simp_exp aw (Crepop op exps) =
    let exps = MAP (simp_exp aw) exps in
    case (op, exps) of
    | (Mul, [exp1; exp2]) => (
        case (dest_const exp1, dest_const exp2) of
        | (SOME c, SOME c2) => Const (c * c2)
        | (SOME c, _) => mul_const aw exp2 c
        | (_, SOME c) => mul_const aw exp1 c
        | _ => Crepop op exps
    )
    | _ => Crepop op exps
  ) /\
  simp_exp aw (Load32 exp) = Load32 (simp_exp aw exp) /\
  simp_exp aw (LoadByte exp) = LoadByte (simp_exp aw exp) /\
  simp_exp aw (Load exp) = Load (simp_exp aw exp) /\
  simp_exp aw (Op bop exps) = Op bop (MAP (simp_exp aw) exps) /\
  simp_exp aw (Cmp cmp exp1 exp2) = Cmp cmp (simp_exp aw exp1) (simp_exp aw exp2) /\
  simp_exp aw (Shift s exp1 exp2) = Shift s (simp_exp aw exp1) (simp_exp aw exp2) /\
  simp_exp aw exp = exp
Termination
  WF_REL_TAC `measure (exp_size o SND)`
End

Definition simp_prog_def:
  simp_prog aw (Dec v exp p) = Dec v (simp_exp aw exp) (simp_prog aw p) /\
  simp_prog aw (Assign v exp) = Assign v (simp_exp aw exp) /\
  simp_prog aw (Store exp1 exp2) = Store (simp_exp aw exp1) (simp_exp aw exp2) /\
  simp_prog aw (Store32 exp1 exp2) = Store32 (simp_exp aw exp1) (simp_exp aw exp2) /\
  simp_prog aw (StoreByte exp1 exp2) = StoreByte (simp_exp aw exp1) (simp_exp aw exp2) /\
  simp_prog aw (StoreGlob g exp) = StoreGlob g (simp_exp aw exp) /\
  simp_prog aw (Seq p1 p2) = Seq (simp_prog aw p1) (simp_prog aw p2) /\
  simp_prog aw (If exp p1 p2) = If (simp_exp aw exp) (simp_prog aw p1) (simp_prog aw p2) /\
  simp_prog aw (While exp p) = While (simp_exp aw exp) (simp_prog aw p) /\
  simp_prog aw (Call call_type e exps) = (
    let call_type2 = case call_type of
      | NONE => NONE
      | SOME (rv, opt_handler) => SOME (rv, case opt_handler of
          | NONE => NONE
          | SOME (ix, ep) => SOME (ix, simp_prog aw ep)
      ) in
    Call call_type2 e (MAP (simp_exp aw) exps)
  ) /\
  simp_prog aw (Return exp) = Return (MAP (simp_exp aw) exp) /\
  simp_prog aw (ShMem op vn exp) = ShMem op vn (simp_exp aw exp) /\
  simp_prog aw p = p
End
