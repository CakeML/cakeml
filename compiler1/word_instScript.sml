open preamble wordLangTheory

val _ = ParseExtras.temp_tight_equality ();
val _ = new_theory "word_inst";

(*Copied from wordSem?*)
val num_exp_def = Define `
  (num_exp (Nat n) = n) /\
  (num_exp (Add x y) = num_exp x + num_exp y) /\
  (num_exp (Sub x y) = num_exp x - num_exp y) /\
  (num_exp (Div2 x) = num_exp x DIV 2) /\
  (num_exp (Exp2 x) = 2 ** (num_exp x)) /\
  (num_exp (WordWidth (w:'a word)) = dimindex (:'a))`

(*Flatten list expressions to trees -- of the form:
   +
  /\
  a +
    /\
    b +
      /\
      c d
  Resulting expressions are all binary branching
  TODO: Should add a phase before this to pull constants up
  e.g.
     +
    /\
    5 ..
*)

val flatten_exp_def = tDefine "flatten_exp" ` 
  (flatten_exp (Op Sub exps) = Op Sub (MAP flatten_exp exps)) ∧ 
  (flatten_exp (Op And []) = Const (~0w)) ∧ (*I guess this should never occur..*) 
  (flatten_exp (Op op []) = Const (0w)) ∧ (*I guess this should never occur..*) 
  (flatten_exp (Op op [x]) = flatten_exp x) ∧
  (flatten_exp (Op op (x::xs)) = Op op [flatten_exp x;flatten_exp (Op op xs)]) ∧
  (flatten_exp (Load exp) = Load (flatten_exp exp)) ∧ 
  (flatten_exp (Shift shift exp nexp) = Shift shift (flatten_exp exp) nexp) ∧ 
  (flatten_exp exp = exp)`
  (WF_REL_TAC `measure (exp_size ARB)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
   \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   \\ fs[exp_size_def]
   \\ TRY (DECIDE_TAC))

(*val test = EVAL ``flatten_exp (Op Add [Const 1w;Const 2w; Const 3w; Op Add [Const 4w; Const 5w; Op Add[Const 6w; Const 7w]] ; Const 8w])``*)

(* Next, perform instruction selection assuming input is binary branching
  Each step takes tar and temp where we are allowed to store temporaries 
  in temp and the value of the whole expression must be saved in tar
*)
val inst_select_exp_def = tDefine "inst_select_exp" `
  (*TODO: Add special cases so we never need to reach this case*)
  (inst_select_exp (tar:num) (temp:num) (Const w) = (Inst (Const tar w))) ∧
  (inst_select_exp (tar:num) (temp:num) (Var v) =
    Move 0 [tar,v]) ∧
  (inst_select_exp tar temp (Lookup store_name) = 
    Get tar store_name) ∧ 
  (*For Load, flatten the expression into a temp
    Can be improved (by matching an offset in the nested exp)
  *)
  (inst_select_exp tar temp (Load exp) = 
    let prog = inst_select_exp temp temp exp in
    Seq prog (Inst (Mem Load tar (Addr temp (0w))))) ∧ 
  (*All ops are binary branching*)
  (inst_select_exp tar temp (Op op [e1;e2]) =
    let p1 = inst_select_exp temp temp e1 in
    let p2 = inst_select_exp (temp+1) (temp+1) e2 in
    Seq p1 (Seq p2 ((Inst (Arith (Binop op tar temp (Reg (temp+1)))))))) ∧ 
  (inst_select_exp tar temp (Shift sh exp nexp) =
    let prog = inst_select_exp temp temp exp in
    (*nexp should be evaluated at compile time*) 
    let n = num_exp nexp in 
    Seq prog (Inst (Arith (Shift sh tar temp n)))) ∧ 
  (*Make it total*)
  (inst_select_exp _ _ _ = Skip)`
  (WF_REL_TAC `measure (exp_size ARB o SND o SND)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
   \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   \\ fs[exp_size_def]
   \\ TRY (DECIDE_TAC)) ;
(*
EVAL ``inst_select_exp 0 1 (Op And [Op Add [Var 2;Var 3; Var 4]; Const 0w; Const 0w])``
*)


(*
  Convert all 3 register instructions to 2 register instructions
*)
val three_to_two_reg_def = Define`
  (three_to_two_reg (Inst (Arith (Binop bop r1 r2 ri))) =
    Seq (Move 0 [r1,r2]) (Inst (Arith (Binop bop r1 r1 ri)))) ∧
  (three_to_two_reg (Inst (Arith (Shift l r1 r2 n))) =
    Seq (Move 0 [r1,r2]) (Inst (Arith (Shift l r1 r1 n)))) ∧ 
  (three_to_two_reg (Seq p1 p2) =
    Seq (three_to_two_reg p1) (three_to_two_reg p2)) ∧ 
  (three_to_two_reg (If cmp r1 ri c1 c2) =
    If cmp r1 ri (three_to_two_reg c1) (three_to_two_reg c2)) ∧ 
  (three_to_two_reg (Call ret dest args handler) =
    let retsel =
      case ret of 
        NONE => NONE
      | SOME (n,names,ret_handler,l1,l2) =>
        SOME (n,names,three_to_two_reg ret_handler,l1,l2) in
    let handlersel = 
      case handler of
        NONE => NONE
      | SOME (n,h,l1,l2) => SOME (n,three_to_two_reg h,l1,l2) in
    Call retsel dest args handlersel) ∧ 
  (three_to_two_reg prog = prog)`

(*Flattens all expressions in program, temporary must a fresh var*)
val inst_select_def = Define`
  (inst_select temp (Assign v exp) = 
    inst_select_exp v temp exp) ∧ 
  (inst_select temp (Set store exp) =
    let prog = inst_select_exp temp (temp+1) exp in
    Seq prog (Set store (Var temp))) ∧ 
  (inst_select temp (Store exp var) =
    let prog = inst_select_exp temp (temp+1) exp in
    Seq prog (Inst (Mem Store var (Addr temp 0w)))) ∧ 
  (inst_select temp (Seq p1 p2) =
    Seq (inst_select temp p1) (inst_select temp p2)) ∧ 
  (inst_select temp (If cmp r1 ri c1 c2) =
    If cmp r1 ri (inst_select temp c1) (inst_select temp c2)) ∧ 
  (inst_select temp (Call ret dest args handler) =
    let retsel =
      case ret of 
        NONE => NONE
      | SOME (n,names,ret_handler,l1,l2) =>
        SOME (n,names,inst_select temp ret_handler,l1,l2) in
    let handlersel = 
      case handler of
        NONE => NONE
      | SOME (n,h,l1,l2) => SOME (n,inst_select temp h,l1,l2) in
    Call retsel dest args handlersel) ∧ 
  (inst_select temp prog = prog)`
  

val _ = export_theory();


