open preamble stackLangTheory;

val _ = new_theory "stack_remove";

val max_stack_alloc_def = Define `
  max_stack_alloc = 256n`;

val word_offset_def = Define `
  word_offset n = n2w (dimindex (:'a) DIV 8 * n):'a word`;

val store_list_def = Define `
  store_list = [NextFree; EndOfHeap; HeapLength; OtherHeap;
                AllocSize; Handler; Globals; ProgStart; BitmapBase]`

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
  stack_err_lab = 2n`;

(*
    k is stack pointer register
    k+1 is base of store array (and last stack address)
    k+2 is CurrHeap (which is kept in a register for improved speed)
*)

val single_stack_alloc_def = Define `
  single_stack_alloc k n =
    Seq (Inst (Arith (Binop Sub k k (Imm (word_offset n)))))
        (JumpLower k (k+1) stack_err_lab)`

val stack_alloc_def = tDefine "stack_alloc" `
  stack_alloc k n =
    if n = 0 then Skip else
    if n <= max_stack_alloc then single_stack_alloc k n else
      Seq (single_stack_alloc k max_stack_alloc)
          (stack_alloc k (n - max_stack_alloc))`
 (WF_REL_TAC `measure SND` \\ fs [max_stack_alloc_def] \\ decide_tac)

val comp_def = Define `
  comp k (p:'a stackLang$prog) =
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
    | StackGetSize r => Seq (Inst (Arith (Binop Sub r k (Reg (k+1)))))
                            (right_shift_inst r (word_shift (:'a)))
    | StackSetSize r => Seq (left_shift_inst r (word_shift (:'a)))
                            (Inst (Arith (Binop Add k (k+1) (Reg r))))
    | BitmapLoad r v =>
        list_Seq [Inst (Mem Load r (Addr (k+1) (store_offset BitmapBase)));
                  add_inst r v;
                  left_shift_inst r (word_shift (:'a));
                  Inst (Mem Load r (Addr r 0w))]
    (* for the rest, just leave it unchanged *)
    | Seq p1 p2 => Seq (comp k p1) (comp k p2)
    | If c r ri p1 p2 => If c r ri (comp k p1) (comp k p2)
    | While c r ri p1 => While c r ri (comp k p1)
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

val halt_inst_def = Define `
  halt_inst w = Seq (const_inst 1 w) (Halt 1)`

(* init code assumes:
    reg 1: start of program
    reg 2: first address in heap
    reg 3: first address in stack (and one past last address of heap)
    reg 4: one past last address of stack *)

val init_code_def = Define `
  init_code (max_heap_bytes:'a word) (k:num) =
    let prog_start = 1n in
    let heap_start = 2n in
    let heap_end = 3 in
    let stack_end = 4 in
    let temp1 = 6 in
    let temp2 = 7 in
    let temp3 = heap_end in
    let temp4 = stack_end in
    let sp = k in
    let bp = k+1 in
      list_Seq [
        (* adjust heap so that it isn't too big *)
        const_inst temp1 max_heap_bytes;
        move temp2 heap_start;
        sub_inst temp2 heap_end;
        If Lower temp1 (Reg temp2)
          (Seq (move heap_end heap_start)
               (add_inst heap_end temp1)) Skip;
        (* reserve space for the store *)
        const_inst temp1 (word_offset (LENGTH store_list));
        add_inst heap_end temp1;
        (* assert heap_start <+ heap_end <+ stack_end *)
        If Lower heap_start (Reg heap_end) Skip (halt_inst 10w);
        If Lower heap_end (Reg stack_end) Skip (halt_inst 11w);
        (* assert word_offset max_stack_alloc <=+ heap_end *)
        const_inst temp1 (word_offset max_stack_alloc);
        If NotLower temp1 (Reg heap_end) Skip (halt_inst 12w);
        (* assert heap_start, heap_end, stack_end are word aligned *)
        move temp1 heap_start;
        add_inst temp1 heap_end;
        add_inst temp1 stack_end;
        If Test temp1 (Imm (word_offset 1)) Skip (halt_inst 13w);
        (* initialise sp and bp *)
        move sp stack_end;
        move bp heap_end;
        (* temp3 := length of heap half *)
        const_inst temp4 (word_offset (LENGTH store_list));
        sub_inst temp3 temp4;
        div2_inst temp3;
        const_inst temp4 (word_offset 1);
        If Test temp3 (Reg temp4) Skip (sub_inst temp3 temp4);
        (* temp4 := address of second heap half *)
        move temp4 heap_start;
        add_inst temp4 temp3;
        (* initialise stack and store *)
        comp k (list_Seq [
          Set ProgStart prog_start;
          const_inst prog_start 0w;
          Set Globals prog_start;
          Set Handler prog_start;
          Set AllocSize prog_start;
          Set NextFree heap_start;
          Set CurrHeap heap_start;
          Set EndOfHeap temp4;
          Set OtherHeap temp4;
          Set HeapLength temp3;
          const_inst heap_start (word_offset 1);
          sub_inst k heap_start;
          StackStore prog_start 0;
          LocValue 0 1 0])]`

val init_stubs_def = Define `
  init_stubs max_heap_bytes k start =
    [(0n,Seq (init_code max_heap_bytes k) (Call NONE (INL start) NONE));
     (1n,halt_inst 0w);
     (2n,halt_inst 2w)]`

val compile_def = Define `
  compile max_heap_bytes k start prog =
    init_stubs max_heap_bytes k start ++ MAP (prog_comp k) prog`;

val _ = export_theory();
