open preamble bvlTheory clos_to_bvlTheory;

val _ = new_theory "bvl_const";

val isConst_def = Define `
  (isConst (Op (Const _) []) = T) /\
  (isConst _ = F)`;
val _ = export_rewrites["isConst_def"];

val getConst_def = Define `
  (getConst (Op (Const i) []) = i) /\
  (getConst _ = 0)`;
val _ = export_rewrites["getConst_def"];

val compile_op_def = Define `
  compile_op op xs =
    if EVERY isConst xs then
      let ys = MAP getConst xs in
        (case op of
         | Add => Op (Const (EL 1 ys + EL 0 ys)) []
         | Sub => Op (Const (EL 1 ys - EL 0 ys)) []
         | Mult => Op (Const (EL 1 ys * EL 0 ys)) []
         | Div => Op (Const (EL 1 ys / EL 0 ys)) []
         | Mod => Op (Const (EL 1 ys % EL 0 ys)) []
         | Less => Op (Cons (bool_to_tag (EL 1 ys < EL 0 ys))) []
         | _ => Op op xs)
    else Op op xs`

val compile_exps_def = tDefine "compile_exps" `
  (compile_exps [] = []) /\
  (compile_exps (x::xs) = compile_exp x :: compile_exps xs) /\
  (compile_exp (Var n) = (Var n)) /\
  (compile_exp (If x1 x2 x3) =
     let y1 = compile_exp x1 in
       if y1 = (Bool T) then compile_exp x2 else
       if y1 = (Bool F) then compile_exp x3 else
         If y1 (compile_exp x2) (compile_exp x3)) /\
  (compile_exp (Let xs x2) = Let (compile_exps xs) (compile_exp x2)) /\
  (compile_exp (Raise x1) = Raise (compile_exp x1)) /\
  (compile_exp (Handle x1 x2) = Handle (compile_exp x1) (compile_exp x2)) /\
  (compile_exp (Op op xs) = compile_op op (compile_exps xs)) /\
  (compile_exp (Tick x) = Tick (compile_exp x)) /\
  (compile_exp (Call ticks dest xs) = Call ticks dest (compile_exps xs))`
 (WF_REL_TAC `measure (\y. case y of INL xs => exp1_size xs
                                   | INR x => exp_size x)`)

val compile_exp_SING = store_thm("compile_exp_SING",
  ``!x. [compile_exp x] = compile_exps [x]``,
  Cases \\ SIMP_TAC std_ss [compile_exps_def])

val compile_exps_length = Q.store_thm("compile_exps_length[simp]",
  `∀es. LENGTH (compile_exps es) = LENGTH es`,
  Induct >> rw[compile_exps_def]);

val _ = export_theory();
