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

(*
Core of the expression flattening step
- Takes a target variable, next temporary and expression
- Returns a flattened program such that the value of that expr 
  is stored in the target
*)
val inst_select_exp_def = tDefine "inst_select_exp" `
  (inst_select_exp (tar:num) (temp:num) (Const w) = (Inst (Const tar w))) ∧
  (*TODO: Add special cases so we never need to reach this case*)
  (inst_select_exp (tar:num) (temp:num) (Var v) =
    Move 0 [tar,v]) ∧
  (*Not sure about Lookup and Load -- there's no equivalent instruction*) 
  (inst_select_exp tar temp (Lookup store_name) = 
    Get tar store_name) ∧ 
  (*For Load, flatten the expression into a temp*)
  (inst_select_exp tar temp (Load exp) = 
    let prog = inst_select_exp temp (temp+1) exp in
    Seq prog (Inst (Mem Load tar (Addr temp (0w)))))
    (*Seq prog (Assign tar (Load (Var temp))))*) ∧ 
  (*Minus needs special case*)
  (inst_select_exp tar temp (Op Sub [e1;e2]) =
    let p1 = inst_select_exp tar temp e1 in
    let p2 = inst_select_exp temp (temp+1) e2 in
    Seq p1 (Seq p2 ((Inst (Arith (Binop Sub tar tar (Reg temp))))))) ∧ 
  (*Everything else use a full match*)
  (inst_select_exp tar temp (Op op exprs) = 
    (*Put ~0w into target*)
    let init = 
      case op of 
      And => Inst (Const tar ((~0w):'a word))
    | _ => Inst (Const tar ((0w):'a word)) in 
    (*& (e1,e2,e3) becomes
      tar = ~0;
      t1 = ...;
      tar = tar & t1; (*can just be the first line*)
      t2 = ...;
      tar = tar & t2;
      ...
      TODO: Special case Var --> no need to copy to temporary
    *)
    FOLDL (λprog expr. 
        Seq prog 
        (Seq (inst_select_exp temp (temp+1) expr) 
        (Inst (Arith (Binop op tar tar (Reg temp))))))
        init exprs) ∧ 
  (inst_select_exp tar temp (Shift sh exp nexp) =
    let prog = inst_select_exp temp (temp+1) exp in
    (*nexp should be evaluated at compile time*) 
    let n = num_exp nexp in 
    Seq prog (Inst (Arith (Shift sh tar temp n))))`
  (WF_REL_TAC `measure (exp_size ARB o SND o SND)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
   \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   \\ fs[exp_size_def]
   \\ TRY (DECIDE_TAC)) ;
(*
EVAL ``inst_select_exp 0 1 (Op And [Op Add [Var 2;Var 3; Var 4]; Const 0w; Const 0w])``
*)

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


