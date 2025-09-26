(*
  The wordLang intermediate language consists of structured programs
  that overate over machine words, a list-like stack and a flat memory.
  This is the language where register allocation is performed.
*)
Theory wordLang
Ancestors
  stackLang
Libs
  preamble

Type shift = ``:ast$shift``

Datatype:
  exp = Const ('a word)
      | Var num
      | Lookup store_name
      | Load exp
      | Op binop (exp list)
      | Shift shift exp num
End

Theorem MEM_IMP_exp_size:
   !xs a. MEM a xs ==> (exp_size l a < exp1_size l xs)
Proof
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [definition"exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC
QED

Type cutsets = “:num_set # num_set” (* non-GCed cutset, GCed cutset *)

Datatype:
  prog = Skip
       | Move num ((num # num) list)
       | Inst ('a inst)
       | Assign num ('a exp)
       | Get num store_name
       | Set store_name ('a exp)
       | Store ('a exp) num
       | MustTerminate wordLang$prog
       | Call ((num list # cutsets # wordLang$prog # num # num) option)
              (* return vars, cut-set, return-handler code, labels l1,l2*)
              (num option) (* target of call *)
              (num list) (* arguments *)
              ((num # wordLang$prog # num # num) option)
              (* handler: varname, exception-handler code, labels l1,l2*)
       | Seq wordLang$prog wordLang$prog
       | If cmp num ('a reg_imm) wordLang$prog wordLang$prog
       | Alloc num cutsets
       | StoreConsts num num num num ((bool # 'a word) list)
       | Raise num
       | Return num (num list) (* return lab, return values *)
       | Tick
       | OpCurrHeap binop num num (* special case compiled well in stackLang *)
       | LocValue num num        (* assign v1 := Loc v2 0 *)
       | Install num num num num cutsets (* code buffer start, length of new code,
                                      data buffer start, length of new data, cut-set *)
       | CodeBufferWrite num num (* code buffer address, byte to write *)
       | DataBufferWrite num num (* data buffer address, word to write *)
       | FFI string num num num num cutsets (* FFI name, conf_ptr, conf_len, array_ptr, array_len, cut-set *)
       | ShareInst memop num ('a exp) (* memory operation, varname, expression for memory address *)
End

Definition raise_stub_location_def:
  raise_stub_location = word_num_stubs - 2
End
Definition store_consts_stub_location_def:
  store_consts_stub_location = word_num_stubs - 1
End

Theorem raise_stub_location_eq = EVAL``raise_stub_location``;
Theorem store_consts_stub_location_eq = EVAL``store_consts_stub_location``;

(* wordLang uses syntactic invariants compared to stackLang that uses semantic flags
   Some of these are also used to EVAL (e.g. for the oracle)
*)

(* Recursors for variables *)
Definition every_var_exp_def:
  (every_var_exp P (Var num) = P num) ∧
  (every_var_exp P (Load exp) = every_var_exp P exp) ∧
  (every_var_exp P (Op wop ls) = EVERY (every_var_exp P) ls) ∧
  (every_var_exp P (Shift sh exp n) = every_var_exp P exp) ∧
  (every_var_exp P expr = T)
End

Definition every_var_imm_def:
  (every_var_imm P (Reg r) = P r) ∧
  (every_var_imm P _ = T)
End

Definition every_var_inst_def:
  (every_var_inst P (Const reg w) = P reg) ∧
  (every_var_inst P (Arith (Binop bop r1 r2 ri)) =
    (P r1 ∧ P r2 ∧ every_var_imm P ri)) ∧
  (every_var_inst P (Arith (Shift shift r1 r2 n)) = (P r1 ∧ P r2)) ∧
  (every_var_inst P (Arith (Div r1 r2 r3)) = (P r1 ∧ P r2 ∧ P r3)) ∧
  (every_var_inst P (Arith (AddCarry r1 r2 r3 r4)) = (P r1 ∧ P r2 ∧ P r3 ∧ P r4)) ∧
  (every_var_inst P (Arith (AddOverflow r1 r2 r3 r4)) = (P r1 ∧ P r2 ∧ P r3 ∧ P r4)) ∧
  (every_var_inst P (Arith (SubOverflow r1 r2 r3 r4)) = (P r1 ∧ P r2 ∧ P r3 ∧ P r4)) ∧
  (every_var_inst P (Arith (LongMul r1 r2 r3 r4)) = (P r1 ∧ P r2 ∧ P r3 ∧ P r4)) ∧
  (every_var_inst P (Arith (LongDiv r1 r2 r3 r4 r5)) = (P r1 ∧ P r2 ∧ P r3 ∧ P r4 ∧ P r5)) ∧
  (every_var_inst P (Mem Load r (Addr a w)) = (P r ∧ P a)) ∧
  (every_var_inst P (Mem Store r (Addr a w)) = (P r ∧ P a)) ∧
  (every_var_inst P (Mem Load32 r (Addr a w)) = (P r ∧ P a)) ∧
  (every_var_inst P (Mem Store32 r (Addr a w)) = (P r ∧ P a)) ∧
  (every_var_inst P (Mem Load8 r (Addr a w)) = (P r ∧ P a)) ∧
  (every_var_inst P (Mem Store8 r (Addr a w)) = (P r ∧ P a)) ∧
  (every_var_inst P (FP (FPLess r d1 d2)) = P r) ∧
  (every_var_inst P (FP (FPLessEqual r d1 d2)) = P r) ∧
  (every_var_inst P (FP (FPEqual r d1 d2)) = P r) ∧
  (every_var_inst P (FP (FPMovToReg r1 r2 d):'a inst) =
    if dimindex(:'a) = 64 then P r1
    else (P r1 ∧ P r2)) ∧
  (every_var_inst P (FP (FPMovFromReg d r1 r2)) =
    if dimindex(:'a) = 64 then P r1
    else (P r1 ∧ P r2)) ∧
  (every_var_inst P inst = T)
End (*catchall*)

Definition every_name_def:
  every_name P (t:cutsets) ⇔
  EVERY P (MAP FST (toAList (FST t))) ∧
  EVERY P (MAP FST (toAList (SND t)))
End

Definition every_var_def:
  (every_var P (Skip:'a prog) ⇔ T) ∧
  (every_var P (Move pri ls) = (EVERY P (MAP FST ls) ∧ EVERY P (MAP SND ls))) ∧
  (every_var P (Inst i) = every_var_inst P i) ∧
  (every_var P (Assign num exp) = (P num ∧ every_var_exp P exp)) ∧
  (every_var P (Get num store) = P num) ∧
  (every_var P (Store exp num) = (P num ∧ every_var_exp P exp)) ∧
  (every_var P (LocValue r _) = P r) ∧
  (every_var P (Install r1 r2 r3 r4 names) = (P r1 ∧ P r2 ∧ P r3 ∧ P r4 ∧ every_name P names)) ∧
  (every_var P (CodeBufferWrite r1 r2) = (P r1 ∧ P r2)) ∧
  (every_var P (DataBufferWrite r1 r2) = (P r1 ∧ P r2)) ∧
  (every_var P (FFI ffi_index cptr clen ptr len names) =
    (P cptr ∧ P clen ∧ P ptr ∧ P len ∧ every_name P names)) ∧
  (every_var P (MustTerminate s1) = every_var P s1) ∧
  (every_var P (Call ret dest args h) =
    ((EVERY P args) ∧
    (case ret of
      NONE => T
    | SOME (v,cutset,ret_handler,l1,l2) =>
      (EVERY P v ∧ every_name P cutset ∧
      every_var P ret_handler ∧
      (case h of
        NONE => T
      | SOME (v,prog,l1,l2) =>
        (P v ∧
        every_var P prog)))))) ∧
  (every_var P (Seq s1 s2) = (every_var P s1 ∧ every_var P s2)) ∧
  (every_var P (If cmp r1 ri e2 e3) =
    (P r1 ∧ every_var_imm P ri ∧ every_var P e2 ∧ every_var P e3)) ∧
  (every_var P (Alloc num numset) =
    (P num ∧ every_name P numset)) ∧
  (every_var P (StoreConsts a b c d ws) =
    (P a ∧ P b ∧ P c ∧ P d)) ∧
  (every_var P (Raise num) = P num) ∧
  (every_var P (Return num1 ns) = (P num1 ∧ EVERY P ns)) ∧
  (every_var P (OpCurrHeap _ num1 num2) = (P num1 ∧ P num2)) ∧
  (every_var P Tick = T) ∧
  (every_var P (Set n exp) = every_var_exp P exp) ∧
  (every_var P (ShareInst op num exp) = (P num /\ every_var_exp P exp)) /\
  (every_var P p = T)
End

(*Recursor for stack variables*)
Definition every_stack_var_def:
  (every_stack_var P (FFI ffi_index cptr clen ptr len names) =
    every_name P names) ∧
  (every_stack_var P (Install _ _ _ _ names) =
    every_name P names) ∧
  (every_stack_var P (Call ret dest args h) =
    (case ret of
      NONE => T
    | SOME (v,cutset,ret_handler,l1,l2) =>
      every_name P cutset ∧
      every_stack_var P ret_handler ∧
    (case h of  (*Does not check the case where Calls are ill-formed*)
      NONE => T
    | SOME (v,prog,l1,l2) =>
      every_stack_var P prog))) ∧
  (every_stack_var P (Alloc num numset) =
    every_name P numset) ∧
  (every_stack_var P (MustTerminate s1) =
    every_stack_var P s1) ∧
  (every_stack_var P (Seq s1 s2) =
    (every_stack_var P s1 ∧ every_stack_var P s2)) ∧
  (every_stack_var P (If cmp r1 ri e2 e3) =
    (every_stack_var P e2 ∧ every_stack_var P e3)) ∧
  (every_stack_var P p = T)
End

(*Find the maximum variable*)
Definition max_var_exp_def:
  (max_var_exp (Var num) = num) ∧
  (max_var_exp (Load exp) = max_var_exp exp) ∧
  (max_var_exp (Op wop ls) = MAX_LIST (MAP (max_var_exp) ls))∧
  (max_var_exp (Shift sh exp n) = max_var_exp exp) ∧
  (max_var_exp exp = 0:num)
End

Definition max_var_inst_def:
  (max_var_inst Skip = 0) ∧
  (max_var_inst (Const reg w) = reg) ∧
  (max_var_inst (Arith (Binop bop r1 r2 ri)) =
    case ri of Reg r => max3 r1 r2 r | _ => MAX r1 r2) ∧
  (max_var_inst (Arith (Shift shift r1 r2 n)) = MAX r1 r2) ∧
  (max_var_inst (Arith (Div r1 r2 r3)) = max3 r1 r2 r3) ∧
  (max_var_inst (Arith (AddCarry r1 r2 r3 r4)) = MAX (MAX r1 r2) (MAX r3 r4)) ∧
  (max_var_inst (Arith (AddOverflow r1 r2 r3 r4)) = MAX (MAX r1 r2) (MAX r3 r4)) ∧
  (max_var_inst (Arith (SubOverflow r1 r2 r3 r4)) = MAX (MAX r1 r2) (MAX r3 r4)) ∧
  (max_var_inst (Arith (LongMul r1 r2 r3 r4)) = MAX (MAX r1 r2) (MAX r3 r4)) ∧
  (max_var_inst (Arith (LongDiv r1 r2 r3 r4 r5)) = MAX (MAX (MAX r1 r2) (MAX r3 r4)) r5) ∧
  (max_var_inst (Mem Load r (Addr a w)) = MAX a r) ∧
  (max_var_inst (Mem Store r (Addr a w)) = MAX a r) ∧
  (max_var_inst (Mem Load32 r (Addr a w)) = MAX a r) ∧
  (max_var_inst (Mem Store32 r (Addr a w)) = MAX a r) ∧
  (max_var_inst (Mem Load8 r (Addr a w)) = MAX a r) ∧
  (max_var_inst (Mem Store8 r (Addr a w)) = MAX a r) ∧
  (max_var_inst (FP (FPLess r f1 f2)) = r) ∧
  (max_var_inst (FP (FPLessEqual r f1 f2)) = r) ∧
  (max_var_inst (FP (FPEqual r f1 f2)) = r) ∧
  (max_var_inst (FP (FPMovToReg r1 r2 d):'a inst) =
    if dimindex(:'a) = 64 then r1
    else MAX r1 r2) ∧
  (max_var_inst (FP (FPMovFromReg d r1 r2)) =
    if dimindex(:'a) = 64 then r1
    else MAX r1 r2) ∧
  (max_var_inst _ = 0)
End

Definition cutsets_max_def[simp]:
  cutsets_max (c:cutsets) =
    MAX (MAX_LIST (MAP FST (toAList (FST c)))) (MAX_LIST (MAP FST (toAList (SND c))))
End

Definition max_var_def:
  (max_var Skip = 0) ∧
  (max_var (Move pri ls) =
    MAX_LIST (MAP FST ls ++ MAP SND ls)) ∧
  (max_var (Inst i) = max_var_inst i) ∧
  (max_var (Assign num exp) = MAX num (max_var_exp exp)) ∧
  (max_var (Get num store) = num) ∧
  (max_var (Store exp num) = MAX num (max_var_exp exp)) ∧
  (max_var (Call ret dest args h) =
    let n = MAX_LIST args in
    case ret of
      NONE => n
    | SOME (v,cutset,ret_handler,l1,l2) =>
      let cutset_max = MAX n (cutsets_max cutset) in
      let ret_max = max3 (MAX_LIST v) cutset_max (max_var ret_handler) in
      (case h of
        NONE => ret_max
      | SOME (v,prog,l1,l2) =>
        max3 v ret_max (max_var prog))) ∧
  (max_var (Seq s1 s2) = MAX (max_var s1) (max_var s2)) ∧
  (max_var (MustTerminate s1) = max_var s1) ∧
  (max_var (If cmp r1 ri e2 e3) =
    let r = case ri of Reg r => MAX r r1 | _ => r1 in
      max3 r (max_var e2) (max_var e3)) ∧
  (max_var (Alloc num numset) =
    MAX num (cutsets_max numset)) ∧
  (max_var (StoreConsts a b c d ws) =
    MAX_LIST [a;b;c;d]) ∧
  (max_var (Install r1 r2 r3 r4 numset) =
    (MAX_LIST [r1;r2;r3;r4;cutsets_max numset])) ∧
  (max_var (CodeBufferWrite r1 r2) =
    MAX r1 r2) ∧
  (max_var (DataBufferWrite r1 r2) =
    MAX r1 r2) ∧
  (max_var (FFI ffi_index ptr1 len1 ptr2 len2 numset) =
    MAX_LIST [ptr1;len1;ptr2;len2;cutsets_max numset]) ∧
  (max_var (Raise num) = num) ∧
  (max_var (OpCurrHeap _ num1 num2) = MAX num1 num2) ∧
  (max_var (Return num1 ns) = MAX_LIST (num1::ns)) ∧
  (max_var Tick = 0) ∧
  (max_var (LocValue r l1) = r) ∧
  (max_var (Set n exp) = max_var_exp exp) ∧
  (max_var (ShareInst op num exp) = MAX num (max_var_exp exp)) /\
  (max_var p = 0)
End

Definition word_op_def:
  word_op op (ws:('a word) list) =
    case (op,ws) of
    | (And,ws) => SOME (FOLDR word_and (¬0w) ws)
    | (Add,ws) => SOME (FOLDR word_add 0w ws)
    | (Or,ws) => SOME (FOLDR word_or 0w ws)
    | (Xor,ws) => SOME (FOLDR word_xor 0w ws)
    | (Sub,[w1;w2]) => SOME (w1 - w2)
    | _ => NONE
End

Definition word_sh_def:
  word_sh sh (w:'a word) n =
    if n <> 0 /\ n ≥ dimindex (:'a) then NONE else
      case sh of
      | Lsl => SOME (w << n)
      | Lsr => SOME (w >>> n)
      | Asr => SOME (w >> n)
      | Ror => SOME (word_ror w n)
End

Definition exp_to_addr_def:
  (exp_to_addr (Var ad) = SOME $ Addr ad 0w) /\
  (exp_to_addr (Op Add [Var ad;Const offset]) = SOME $ Addr ad offset) /\
  (exp_to_addr _ = NONE)
End

Overload shift = “backend_common$word_shift”

Datatype:
  word_loc = Word ('a word) | Loc num num
End

