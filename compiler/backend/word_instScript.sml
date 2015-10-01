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

(*TODO: Optimize constants in expressions, leaving constants on the right*)

(*Flatten list expressions to trees -- of the form:
      +
     /\
    + a
   /\
  + b
 /\
c d
*)
val flatten_exp_def = tDefine "flatten_exp" `
  (flatten_exp (Op Sub exps) = Op Sub (MAP flatten_exp exps)) ∧
  (flatten_exp (Op And []) = Const (~0w)) ∧ (*I guess this should never occur..*)
  (flatten_exp (Op op []) = Const (0w)) ∧ (*I guess this should never occur..*)
  (flatten_exp (Op op [x]) = flatten_exp x) ∧
  (flatten_exp (Op op (x::xs)) = Op op [flatten_exp (Op op xs);flatten_exp x]) ∧
  (flatten_exp (Load exp) = Load (flatten_exp exp)) ∧
  (flatten_exp (Shift shift exp nexp) = Shift shift (flatten_exp exp) nexp) ∧
  (flatten_exp exp = exp)`
  (WF_REL_TAC `measure (exp_size ARB)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
   \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   \\ fs[exp_size_def]
   \\ TRY (DECIDE_TAC))

(*val test = EVAL ``flatten_exp (Op Add [Const 1w;Const 2w; Const 3w; Op Add [Const 4w; Const 5w; Op Add[Const 6w; Const 7w]] ; Const 8w])``*)

(*
  Maximal Munch instruction selection on (binary) expressions
  c is an asm_config to check validity of imms (TODO: assume 0w is accepted?)
  Optimized munches (assumes Consts are on the RIGHT):
  --Load [Op Add [exp;Const w]]
  Op op [exp;Const w]
  --Store exp var

  Next, perform instruction selection assuming input is binary branching
  Each step takes tar and temp where we are allowed to store temporaries
  in temp and the value of the whole expression must be saved in tar
*)
val inst_select_exp_def = tDefine "inst_select_exp" `
  (inst_select_exp (c:'a asm_config) (tar:num) (temp:num) (Load exp) =
    case exp of
    | Op Add [exp';Const w] =>
      if addr_offset_ok w c then
        let prog = inst_select_exp c temp temp exp' in
          Seq prog (Inst (Mem Load tar (Addr temp w)))
      else
        let prog = inst_select_exp c temp temp exp in
          Seq prog (Inst (Mem Load tar (Addr temp (0w))))
    | _ =>
      let prog = inst_select_exp c temp temp exp in
      Seq prog (Inst (Mem Load tar (Addr temp (0w))))) ∧
  (inst_select_exp c (tar:num) (temp:num) (Const w) = (Inst (Const tar w))) ∧
  (inst_select_exp c (tar:num) (temp:num) (Var v) =
    Move 0 [tar,v]) ∧
  (inst_select_exp c tar temp (Lookup store_name) =
    Get tar store_name) ∧
  (*All ops are binary branching*)
  (inst_select_exp c tar temp (Op op [e1;e2]) =
    let p1 = inst_select_exp c temp temp e1 in
    case e2 of
    | Const w =>
      if c.valid_imm (INL op) w then
        Seq p1 (Inst (Arith (Binop op tar temp (Imm w))))
      else
        let p2 = Inst (Const (temp+1) w) in
        Seq p1 (Seq p2 (Inst (Arith (Binop op tar temp (Reg (temp+1))))))
    | _ =>
      let p2 = inst_select_exp c (temp+1) (temp+1) e2 in
      Seq p1 (Seq p2 (Inst (Arith (Binop op tar temp (Reg (temp+1))))))) ∧
  (inst_select_exp c tar temp (Shift sh exp nexp) =
    let n = num_exp nexp in
    if (n < dimindex(:'a)) then
      let prog = inst_select_exp c temp temp exp in
      if n = 0 then
        Seq prog (Move 0 [tar,temp])
      else
        Seq prog (Inst (Arith (Shift sh tar temp n)))
    else
      Inst (Const tar 0w)) ∧
  (*Make it total*)
  (inst_select_exp _ _ _ _ = Skip)`
  (WF_REL_TAC `measure (exp_size ARB o SND o SND o SND)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
   \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   \\ fs[exp_size_def]
   \\ TRY (DECIDE_TAC)) ;
(*

First munch
EVAL ``inst_select_exp x64_config 5 5 (Load (Op Add [Const 400w; Var 6]))``
EVAL ``inst_select_exp x64_config 5 5 (Load (Op Add [Const 99999999999w; Var 6]))``

Second munch
EVAL ``inst_select_exp x64_config 0 99 (Op And [Const 99w;Op Add [Var 2;Var 3]])``

*)

(*Flattens all expressions in program, temp must a fresh var*)
val inst_select_def = Define`
  (inst_select c temp (Assign v exp) =
    (inst_select_exp c v temp o flatten_exp) exp) ∧
  (inst_select c temp (Set store exp) =
    let prog = (inst_select_exp c temp temp o flatten_exp) exp in
    Seq prog (Set store (Var temp))) ∧
  (inst_select c temp (Store exp var) =
    let exp = flatten_exp exp in
    case exp of
    | Op Add [exp';Const w] =>
      if addr_offset_ok w c then
        let prog = inst_select_exp c temp temp exp' in
          Seq prog (Inst (Mem Store var (Addr temp w)))
      else
        let prog = inst_select_exp c temp temp exp in
          Seq prog (Inst (Mem Store var (Addr temp (0w))))
    | _ =>
      let prog = inst_select_exp c temp temp exp in
      Seq prog (Inst (Mem Store var (Addr temp (0w))))) ∧
  (inst_select c temp (Seq p1 p2) =
    Seq (inst_select c temp p1) (inst_select c temp p2)) ∧
  (inst_select c temp (If cmp r1 ri c1 c2) =
    If cmp r1 ri (inst_select c temp c1) (inst_select c temp c2)) ∧
  (inst_select c temp (Call ret dest args handler) =
    let retsel =
      case ret of
        NONE => NONE
      | SOME (n,names,ret_handler,l1,l2) =>
        SOME (n,names,inst_select c temp ret_handler,l1,l2) in
    let handlersel =
      case handler of
        NONE => NONE
      | SOME (n,h,l1,l2) => SOME (n,inst_select c temp h,l1,l2) in
    Call retsel dest args handlersel) ∧
  (inst_select c temp prog = prog)`

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

val _ = export_theory();


