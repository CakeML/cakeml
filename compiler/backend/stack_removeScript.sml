open preamble stackLangTheory;

val _ = new_theory "stack_remove";

(* TODO: arrange for a few very frequently used store vars to be in
         registers instead of memory. *)

val word_offset_def = Define `
  word_offset n = n2w (dimindex (:'a) DIV 8 * n):'a word`;

val store_list_def = Define `
  store_list = [NextFree; EndOfHeap; HeapLength; OtherHeap;
                AllocSize; Handler; Globals; ProgStart]`

val store_pos_def = Define `
  store_pos name =
    case INDEX_FIND 0 (\n. n = name) store_list of
    | NONE => 0n
    | SOME (i,_) => i+1`

val store_length_def = Define `
  store_length =
    if EVEN (LENGTH store_list) then LENGTH store_list
    else LENGTH store_list + 1`

val store_offset_def = Define `
  store_offset name = 0w - word_offset (store_pos name)`;

val stack_err_lab_def = Define `
  stack_err_lab = 5n`;

val stack_err_stub_def = Define `
  stack_err_stub = [Inst (Const 1 2w); Halt 1]`

(*
    k is stack pointer register
    k+1 is base of store array (and last stack address)
    k+2 is CurrHeap (which is kept in a register for improved speed)
*)

val move_def = Define `
  move dest src = Inst (Arith (Binop Or dest src (Reg src)))`

val max_stack_alloc_def = Define `
  max_stack_alloc = 256n`;

val single_stack_alloc_def = Define `
  single_stack_alloc k n =
    Seq (Inst (Arith (Binop Sub k k (Imm (word_offset n)))))
        (JumpLess k (k+1) stack_err_lab)`

val stack_alloc_def = tDefine "stack_alloc" `
  stack_alloc k n =
    if n = 0 then Skip else
    if n <= max_stack_alloc then single_stack_alloc k n else
      Seq (single_stack_alloc k max_stack_alloc)
          (stack_alloc k (n - max_stack_alloc))`
 (WF_REL_TAC `measure SND`
  \\ fs [max_stack_alloc_def] \\ decide_tac)

val comp_def = Define `
  comp k p =
    case p of
    (* remove store accesses *)
    | Get r name =>
        if name = CurrHeap then move r (k+2)
        else Inst (Mem Load r (Addr (k+1) (store_offset name)))
    | Set name r =>
        if name = CurrHeap then move (k+2) r
        else Inst (Mem Store r (Addr (k+1) (store_offset name)))
    (* remove stack operations *)
    | StackFree n => Inst (Arith (Binop Add k k (Imm (word_offset n))))
    | StackAlloc n => stack_alloc k n
    | StackStore r n => Inst (Mem Store r (Addr k (word_offset n)))
    | StackLoad r n => Inst (Mem Load r (Addr k (word_offset n)))
    | StackLoadAny r i => Seq (Inst (Arith (Binop Add r i (Reg k))))
                              (Inst (Mem Load r (Addr r 0w)))
    | StackStoreAny r i => Seq (Inst (Arith (Binop Add k k (Reg i))))
                          (Seq (Inst (Mem Store r (Addr k 0w)))
                               (Inst (Arith (Binop Sub k k (Reg i)))))
    | StackGetSize r => Inst (Arith (Binop Sub r k (Reg (k+1))))
    | StackSetSize r => Inst (Arith (Binop Add k (k+1) (Reg r)))
    (* for the rest, just leave it unchanged *)
    | Seq p1 p2 => Seq (comp k p1) (comp k p2)
    | If c r ri p1 p2 => If c r ri (comp k p1) (comp k p2)
    | Call ret dest exc =>
        Call (case ret of
              | NONE => NONE
              | SOME (p1,lr,l1,l2) => SOME (comp k p1,lr,l1,l2))
          dest (case exc of
                | NONE => NONE
                | SOME (p2,l1,l2) => SOME (comp k p2,l1,l2))
    | p => p`

val prog_comp_def = Define `
  prog_comp k (n,p) = (n,comp k p)`

val compile_def = Define `
  compile k prog = MAP (prog_comp k) prog`;

val _ = export_theory();
