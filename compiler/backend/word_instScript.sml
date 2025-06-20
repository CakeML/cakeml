(*
  This compiler phase implements instruction selection. It uses the
  Maximal Munch strategy.
*)
open preamble wordLangTheory stackLangTheory sortingTheory;

val _ = new_theory "word_inst";

val _ = Parse.bring_to_front_overload"Shift"{Thy="wordLang",Name="Shift"};
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(*Scheme:
1) Pull all nested ops and consts as far up as possible and convert
  Sub [ x ; Const w ] to Add [x ; Const -w]
2) Flatten to binary branching expressions
3) inst select, assuming binary branches
4) 3->2 regs if necessary
*)

(*Pull all nested arguments with the same op up*)
Definition pull_ops_def:
  (pull_ops op [] acc = acc) ∧
  (pull_ops op (x::xs) acc =
    dtcase x of
    |  (Op op' ls) => if op = op' then pull_ops op xs (ls ++ acc) else pull_ops op xs (x::acc)
    |  _  => pull_ops op xs (x::acc))
End

Definition is_const_def:
  (is_const (Const w) = T) ∧
  (is_const _ = F)
End

Definition rm_const_def:
  (rm_const (Const w) = w) ∧
  (*Make it total*)
  (rm_const _ = 0w)
End

Definition convert_sub_def:
  (convert_sub [Const w1;Const w2] = Const (w1 -w2)) ∧
  (convert_sub [x;Const w] = Op Add [Const (-w); x]) ∧
  (convert_sub ls = Op Sub ls)
End

Theorem convert_sub_pmatch:
  !l.
  convert_sub l =
  case l of
    [Const w1;Const w2] => Const (w1 -w2)
  | [x;Const w] => Op Add [Const (-w);x]
  | ls => Op Sub ls
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac
  >> fs[convert_sub_def]
QED

Definition op_consts_def:
  (op_consts And = Const (~0w)) ∧
  (op_consts _ = Const 0w)
End

Theorem op_consts_pmatch:
  !op.
  op_consts op =
  case op of
    And => Const (~0w)
  | _ => Const 0w
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac
  >> fs[op_consts_def]
QED

(* Returns a definite value *)
Definition reduce_const_def:
  reduce_const op w rest =
  if w = 0w then
    if op = Add ∨ op = Or ∨ op = Xor then
      dtcase rest of
        []  => Const w
      | [x] => x
      | _ => Op op rest
    else if op = And then
      Const 0w
    else Op op (Const w::rest)
  else Op op (Const w::rest)
End

Definition optimize_consts_def:
  optimize_consts op ls =
  let (const_ls,nconst_ls) = PARTITION is_const ls in
    dtcase const_ls of
      [] => Op op nconst_ls
    | _ =>
      let w = THE (word_op op (MAP rm_const const_ls)) in
      reduce_const op w nconst_ls
End

(* If this expression contains a constant it should
    be head of the output operation list *)
Definition pull_exp_def:
  (pull_exp (Op Sub ls) =
    let new_ls = MAP pull_exp ls in
    convert_sub new_ls) ∧
  (pull_exp (Op op []) = op_consts op) ∧
  (pull_exp (Op op [x]) = pull_exp x) ∧
  (pull_exp (Op op ls) =
    (*First, pull all the inner expressions*)
    let new_ls = MAP pull_exp ls in
    (*Then pull at the topmost*)
    let pull_ls = pull_ops op new_ls [] in
      optimize_consts op pull_ls) ∧
  (pull_exp (Load exp) = Load (pull_exp exp)) ∧
  (pull_exp (Shift shift exp nexp) = Shift shift (pull_exp exp) nexp) ∧
  (pull_exp exp = exp)
Termination
  WF_REL_TAC `measure (exp_size ARB)`
  \\ rw[]
  \\ gvs[]
  \\ drule MEM_list_size
  \\ disch_then(qspec_then `exp_size ARB` mp_tac)
  \\ rw[]
End

Theorem pull_exp_pmatch:
  !(exp:'a exp).
  pull_exp exp =
  case exp of
   Op Sub ls => (
    let new_ls = MAP pull_exp ls in
    convert_sub new_ls)
  | Op op [] => op_consts op
  | Op op [x] => pull_exp x
  | Op op ls => (
    let new_ls = MAP pull_exp ls in
    let pull_ls = pull_ops op new_ls [] in
      optimize_consts op pull_ls)
  | Load exp => Load (pull_exp exp)
  | Shift sh exp nexp => Shift sh (pull_exp exp) nexp
  | exp => exp
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac
  >> fs[pull_exp_def,ETA_THM]
QED

(*Flatten list expressions to trees -- of the form:
      +
     /\
    + a
   /\
  + b
 /\
c d
*)
Definition flatten_exp_def:
  (flatten_exp (Op Sub exps) = Op Sub (MAP flatten_exp exps)) ∧
  (flatten_exp (Op op []) = op_consts op) ∧
  (flatten_exp (Op op [x]) = flatten_exp x) ∧
  (flatten_exp (Op op (x::xs)) = Op op [flatten_exp (Op op xs);flatten_exp x]) ∧
  (flatten_exp (Load exp) = Load (flatten_exp exp)) ∧
  (flatten_exp (Shift shift exp nexp) = Shift shift (flatten_exp exp) nexp) ∧
  (flatten_exp exp = exp)
Termination
  WF_REL_TAC `measure (exp_size ARB)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
   \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   \\ fs[exp_size_def]
   \\ TRY (DECIDE_TAC)
End


  (*
Theorem flatten_exp_pmatch:
  !exp.
  flatten_exp exp =
  case exp of
    (Op Sub exps) => Op Sub (MAP flatten_exp exps)
  | (Op op []) => op_consts op
  | (Op op [x]) => flatten_exp x
  | (Op op (x::xs)) => Op op [flatten_exp (Op op xs);flatten_exp x]
  | (Load exp) => Load (flatten_exp exp)
  | (Shift shift exp nexp) => Shift shift (flatten_exp exp) nexp
  | exp => exp
Proof
  rpt strip_tac
  >> CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  >> every_case_tac
  >> fs[flatten_exp_def, ETA_THM]
QED*)
(*
val test = EVAL ``flatten_exp (pull_exp (Op Add [Const 1w;Const 2w; Const 3w; Op Add [Const 4w; Const 5w; Op Add[Const 6w; Const 7w];Op Xor[Const 1w;Var y;Var x]] ; Const (8w:8 word)]))``

val test = EVAL ``flatten_exp (pull_exp (Op Sub [Const 1w; Op Sub[Const 2w;Const (3w:64 word)]]))``

 Op Add [Const 4w; Const 5w; Op Add[Const 6w; Const 7w];Op Xor[Const 1w;Var y;Var x]] ; Const (8w:8 word)]))``
*)

Definition is_Lookup_CurrHeap_def:
  is_Lookup_CurrHeap (Lookup CurrHeap) = T ∧
  is_Lookup_CurrHeap _ = F
End

Theorem is_Lookup_CurrHeap_pmatch:
  is_Lookup_CurrHeap e =
    (case e of Lookup CurrHeap => T | _ => F)
Proof
  rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac >>
         PURE_ONCE_REWRITE_TAC[LET_DEF] >> BETA_TAC) >>
  fs [is_Lookup_CurrHeap_def]
QED

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

Definition inst_select_exp_def:
  (inst_select_exp (c:'a asm_config) (tar:num) (temp:num) (Load exp) =
    dtcase exp of
    | Op Add [exp';Const w] =>
      if addr_offset_ok c w then
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
    if is_Lookup_CurrHeap e2 then
      (let p1 = inst_select_exp c temp temp e1 in
        Seq p1 (OpCurrHeap op tar temp))
    else if is_Lookup_CurrHeap e1 ∧ op ≠ Sub then
      (let p2 = inst_select_exp c temp temp e2 in
        Seq p2 (OpCurrHeap op tar temp))
    else
    let p1 = inst_select_exp c temp temp e1 in
    dtcase e2 of
    | Const w =>
      (*t = r op const*)
      if c.valid_imm (INL op) w then
        Seq p1 (Inst (Arith (Binop op tar temp (Imm w))))
      (*t = r + const --> t = r - const*)
      else if op = Add ∧ c.valid_imm (INL Sub) (-w) then
        Seq p1 (Inst (Arith (Binop Sub tar temp (Imm (-w)))))
      else
      (*no immediates*)
        let p2 = Inst (Const (temp+1) w) in
        Seq p1 (Seq p2 (Inst (Arith (Binop op tar temp (Reg (temp+1))))))
    | _ =>
      let p2 = inst_select_exp c (temp+1) (temp+1) e2 in
      Seq p1 (Seq p2 (Inst (Arith (Binop op tar temp (Reg (temp+1))))))) ∧
  (inst_select_exp c tar temp (Shift sh exp n) =
    if (n < dimindex(:'a)) then
      let prog = inst_select_exp c temp temp exp in
      if n = 0 then
        Seq prog (Move 0 [tar,temp])
      else
        Seq prog (Inst (Arith (Shift sh tar temp n)))
    else
      Inst (Const tar 0w)) ∧
  (*Make it total*)
  (inst_select_exp _ _ _ _ = Skip)
Termination
  WF_REL_TAC `measure (exp_size ARB o SND o SND o SND)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
   \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   \\ fs[exp_size_def]
   \\ TRY (DECIDE_TAC)
End ;

Theorem inst_select_exp_pmatch:
  !c tar temp exp.
  inst_select_exp (c:'a asm_config) tar temp exp =
  case exp of
    Load(Op Add [exp';Const w]) =>
      if addr_offset_ok c w then
        let prog = inst_select_exp c temp temp exp' in
          Seq prog (Inst (Mem Load tar (Addr temp w)))
      else
        (let prog = inst_select_exp c temp temp (Op Add [exp'; Const w]) in
          Seq prog (Inst (Mem Load tar (Addr temp (0w)))))
  | Load exp =>
      (let prog = inst_select_exp c temp temp exp in
      Seq prog (Inst (Mem Load tar (Addr temp (0w)))))
  | Const w => Inst (Const tar w)
  | Var v =>
    Move 0 [tar,v]
  | Lookup store_name =>
    Get tar store_name
  (*All ops are binary branching*)
  | Op op [e1;e2] =>
    (if is_Lookup_CurrHeap e2 then
      (let p1 = inst_select_exp c temp temp e1 in
        Seq p1 (OpCurrHeap op tar temp))
    else if is_Lookup_CurrHeap e1 ∧ op ≠ Sub then
      (let p2 = inst_select_exp c temp temp e2 in
        Seq p2 (OpCurrHeap op tar temp))
    else
     case e2 of
      Const w =>
      (*t = r op const*)
      if c.valid_imm (INL op) w then
        Seq (inst_select_exp c temp temp e1) (Inst (Arith (Binop op tar temp (Imm w))))
      (*t = r + const --> t = r - const*)
      else if op = Add ∧ c.valid_imm (INL Sub) (-w) then
        Seq (inst_select_exp c temp temp e1) (Inst (Arith (Binop Sub tar temp (Imm (-w)))))
      else
      (*no immediates*)
        let p2 = Inst (Const (temp+1) w) in
        Seq (inst_select_exp c temp temp e1) (Seq p2 (Inst (Arith (Binop op tar temp (Reg (temp+1))))))
    | _ =>
      let p2 = inst_select_exp c (temp+1) (temp+1) e2 in
      Seq (inst_select_exp c temp temp e1) (Seq p2 (Inst (Arith (Binop op tar temp (Reg (temp+1)))))))
  | Shift sh exp n =>
    (if (n < dimindex(:'a)) then
      let prog = inst_select_exp c temp temp exp in
      if n = 0 then
        Seq prog (Move 0 [tar,temp])
      else
        Seq prog (Inst (Arith (Shift sh tar temp n)))
    else
      Inst (Const tar 0w))
  (*Make it total*)
  | _ => Skip
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac >>
         PURE_ONCE_REWRITE_TAC[LET_DEF] >> BETA_TAC)
  >> fs[inst_select_exp_def] >> metis_tac[DIMINDEX_GT_0, NOT_ZERO_LT_ZERO]
QED

(*

First munch
EVAL ``inst_select_exp``
 x64_config 5 5 (Load (Op Add [Const 400w; Var 6]))``
EVAL ``inst_select_exp x64_config 5 5 (Load (Op Add [Const 99999999999w; Var 6]))``

Second munch
EVAL ``inst_select_exp x64_config 0 99
EVAL ``(pull_exp (Op And [Const (99w:64 word); Op Add [Op Add [];Op Or []]]))``
*)

(*Flattens all expressions in program, temp must a fresh var*)
Definition inst_select_def:
  (inst_select c temp (Assign v exp) =
    (inst_select_exp c v temp o flatten_exp o pull_exp) exp) ∧
  (inst_select c temp (Set store exp) =
    let prog = (inst_select_exp c temp temp o flatten_exp o pull_exp) exp in
    Seq prog (Set store (Var temp))) ∧
  (inst_select c temp (Store exp var) =
    let exp = (flatten_exp o pull_exp) exp in
    dtcase exp of
    | Op Add [exp';Const w] =>
      if addr_offset_ok c w then
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
  (inst_select c temp (MustTerminate p1) =
    MustTerminate (inst_select c temp p1)) ∧
  (inst_select c temp (ShareInst op v exp) =
    let exp = (flatten_exp o pull_exp) exp in
    dtcase exp of
    | Op Add [exp';Const w] =>
      if ((op = Load ∨ op = Store) /\ addr_offset_ok c w) ∨
          ((op = Load32 ∨ op  = Store32) /\ addr_offset_ok c w) ∨
          ((op = Load8 ∨ op  = Store8) /\ byte_offset_ok c w) then
        let prog = inst_select_exp c temp temp exp' in
          Seq prog (ShareInst op v (Op Add [Var temp; Const w]))
      else
        let prog = inst_select_exp c temp temp exp in
          Seq prog (ShareInst op v (Var temp))
    | _ =>
      let prog = inst_select_exp c temp temp exp in
      Seq prog (ShareInst op v (Var temp))) ∧
  (inst_select c temp (If cmp r1 ri c1 c2) =
    If cmp r1 ri (inst_select c temp c1) (inst_select c temp c2)) ∧
  (inst_select c temp (Call ret dest args handler) =
    let retsel =
      dtcase ret of
        NONE => NONE
      | SOME (n,names,ret_handler,l1,l2) =>
        SOME (n,names,inst_select c temp ret_handler,l1,l2) in
    let handlersel =
      dtcase handler of
        NONE => NONE
      | SOME (n,h,l1,l2) => SOME (n,inst_select c temp h,l1,l2) in
    Call retsel dest args handlersel) ∧
  (inst_select c temp prog = prog)
End

Theorem inst_select_pmatch:
  !c temp prog.
  inst_select c temp prog =
  case prog of
  | Assign v exp =>
    (inst_select_exp c v temp o flatten_exp o pull_exp) exp
  | Set store exp =>
    (let prog = (inst_select_exp c temp temp o flatten_exp o pull_exp) exp in
    Seq prog (Set store (Var temp)))
  | Store exp var =>
    (let exp = (flatten_exp o pull_exp) exp in
    case exp of
    | Op Add [exp';Const w] =>
      if addr_offset_ok c w then
        let prog = inst_select_exp c temp temp exp' in
          Seq prog (Inst (Mem Store var (Addr temp w)))
      else
        let prog = inst_select_exp c temp temp exp in
          Seq prog (Inst (Mem Store var (Addr temp (0w))))
    | _ =>
      let prog = inst_select_exp c temp temp exp in
      Seq prog (Inst (Mem Store var (Addr temp (0w)))))
  | Seq p1 p2 =>
    Seq (inst_select c temp p1) (inst_select c temp p2)
  | MustTerminate p1 =>
    MustTerminate (inst_select c temp p1)
  | (If cmp r1 ri c1 c2) =>
      If cmp r1 ri (inst_select c temp c1) (inst_select c temp c2)
  | ShareInst op var exp =>
    (let exp = (flatten_exp o pull_exp) exp in
    case exp of
    | Op Add [exp';Const w] =>
      if ((op = Load ∨ op = Store) /\ addr_offset_ok c w) \/
          ((op = Load32 ∨ op  = Store32) /\ addr_offset_ok c w) \/
          ((op = Load8 ∨ op  = Store8) /\ byte_offset_ok c w) then
        let prog = inst_select_exp c temp temp exp' in
          Seq prog (ShareInst op var (Op Add [Var temp; Const w]))
      else
        let prog = inst_select_exp c temp temp exp in
          Seq prog (ShareInst op var (Var temp))
    | _ =>
      let prog = inst_select_exp c temp temp exp in
      Seq prog (ShareInst op var (Var temp)))
  | (Call ret dest args handler) =>
    (let retsel =
      case ret of
        NONE => NONE
      | SOME (n,names,ret_handler,l1,l2) =>
        SOME (n,names,inst_select c temp ret_handler,l1,l2) in
    let handlersel =
      case handler of
        NONE => NONE
      | SOME (n,h,l1,l2) => SOME (n,inst_select c temp h,l1,l2) in
    Call retsel dest args handlersel)
  | prog => prog
Proof
  rpt(
    rpt strip_tac
    >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac >>
         PURE_ONCE_REWRITE_TAC[LET_DEF] >> BETA_TAC)
    >> fs[inst_select_def] )
QED

(*
  Convert all 3 register instructions to 2 register instructions
*)
Definition three_to_two_reg_def:
  (three_to_two_reg (Inst (Arith (Binop bop r1 r2 ri))) =
    Seq (Move 0 [r1,r2]) (Inst (Arith (Binop bop r1 r1 ri)))) ∧
  (three_to_two_reg (Inst (Arith (Shift l r1 r2 n))) =
    Seq (Move 0 [r1,r2]) (Inst (Arith (Shift l r1 r1 n)))) ∧
  (three_to_two_reg (Inst (Arith (AddCarry r1 r2 r3 r4))) =
    Seq (Move 0 [r1,r2]) (Inst (Arith (AddCarry r1 r1 r3 r4)))) ∧
  (three_to_two_reg (Inst (Arith (AddOverflow r1 r2 r3 r4))) =
    Seq (Move 0 [r1,r2]) (Inst (Arith (AddOverflow r1 r1 r3 r4)))) ∧
  (three_to_two_reg (Inst (Arith (SubOverflow r1 r2 r3 r4))) =
    Seq (Move 0 [r1,r2]) (Inst (Arith (SubOverflow r1 r1 r3 r4)))) ∧
  (three_to_two_reg (OpCurrHeap bop r1 r2) =
    Seq (Move 0 [r1,r2]) (OpCurrHeap bop r1 r1)) ∧
  (three_to_two_reg (Seq p1 p2) =
    Seq (three_to_two_reg p1) (three_to_two_reg p2)) ∧
  (three_to_two_reg (MustTerminate p1) =
    MustTerminate (three_to_two_reg p1)) ∧
  (three_to_two_reg (If cmp r1 ri c1 c2) =
    If cmp r1 ri (three_to_two_reg c1) (three_to_two_reg c2)) ∧
  (three_to_two_reg (Call ret dest args handler) =
    let retsel =
      dtcase ret of
        NONE => NONE
      | SOME (n,names,ret_handler,l1,l2) =>
        SOME (n,names,three_to_two_reg ret_handler,l1,l2) in
    let handlersel =
      dtcase handler of
        NONE => NONE
      | SOME (n,h,l1,l2) => SOME (n,three_to_two_reg h,l1,l2) in
    Call retsel dest args handlersel) ∧
  (three_to_two_reg prog = prog)
End

Theorem three_to_two_reg_pmatch:
  !prog.
  three_to_two_reg prog =
  case prog of
  | (Inst (Arith (Binop bop r1 r2 ri))) =>
    Seq (Move 0 [r1,r2]) (Inst (Arith (Binop bop r1 r1 ri)))
  | (Inst (Arith (Shift l r1 r2 n))) =>
    Seq (Move 0 [r1,r2]) (Inst (Arith (Shift l r1 r1 n)))
  | (Inst (Arith (AddCarry r1 r2 r3 r4))) =>
    Seq (Move 0 [r1,r2]) (Inst (Arith (AddCarry r1 r1 r3 r4)))
  | (Inst (Arith (AddOverflow r1 r2 r3 r4))) =>
    Seq (Move 0 [r1,r2]) (Inst (Arith (AddOverflow r1 r1 r3 r4)))
  | (Inst (Arith (SubOverflow r1 r2 r3 r4))) =>
    Seq (Move 0 [r1,r2]) (Inst (Arith (SubOverflow r1 r1 r3 r4)))
  | (OpCurrHeap bop r1 r2) =>
    Seq (Move 0 [r1,r2]) (OpCurrHeap bop r1 r1)
  | (Seq p1 p2) =>
    Seq (three_to_two_reg p1) (three_to_two_reg p2)
  | (MustTerminate p1) =>
    MustTerminate (three_to_two_reg p1)
  | (If cmp r1 ri c1 c2) =>
    If cmp r1 ri (three_to_two_reg c1) (three_to_two_reg c2)
  | (Call ret dest args handler) =>
    (let retsel =
      case ret of
        NONE => NONE
      | SOME (n,names,ret_handler,l1,l2) =>
        SOME (n,names,three_to_two_reg ret_handler,l1,l2) in
    let handlersel =
      case handler of
        NONE => NONE
      | SOME (n,h,l1,l2) => SOME (n,three_to_two_reg h,l1,l2) in
    Call retsel dest args handlersel)
  | prog => prog
Proof
  rpt(
    rpt strip_tac
    >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac >>
         PURE_ONCE_REWRITE_TAC[LET_DEF] >> BETA_TAC)
    >> fs[three_to_two_reg_def])
QED

Definition three_to_two_reg_prog_def:
  three_to_two_reg_prog b prog =
    if b then three_to_two_reg prog else prog
End

val _ = export_theory();
