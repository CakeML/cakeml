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
  (compile_exps (x::xs) = compile x :: compile_exps xs) /\
  (compile (Var n) = (Var n)) /\
  (compile (If x1 x2 x3) =
     let y1 = compile x1 in
       if y1 = (Bool T) then compile x2 else
       if y1 = (Bool F) then compile x3 else
         If y1 (compile x2) (compile x3)) /\
  (compile (Let xs x2) = Let (compile_exps xs) (compile x2)) /\
  (compile (Raise x1) = Raise (compile x1)) /\
  (compile (Handle x1 x2) = Handle (compile x1) (compile x2)) /\
  (compile (Op op xs) = compile_op op (compile_exps xs)) /\
  (compile (Tick x) = Tick (compile x)) /\
  (compile (Call ticks dest xs) = Call ticks dest (compile_exps xs))`
 (WF_REL_TAC `measure (\y. case y of INL xs => exp1_size xs
                                   | INR x => exp_size x)`)

val compile_SING = store_thm("compile_SING",
  ``!x. [compile x] = compile_exps [x]``,
  Cases \\ SIMP_TAC std_ss [compile_exps_def])

val _ = export_theory();
