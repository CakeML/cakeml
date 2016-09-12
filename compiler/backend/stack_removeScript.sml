open preamble stackLangTheory;

val _ = new_theory "stack_remove";

(* -- compiler -- *)

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
    | StackLoadAny r i => Seq (Seq (move r i) (add_inst r k))
                              (Inst (Mem Load r (Addr r 0w)))
    | StackStoreAny r i => Seq (Inst (Arith (Binop Add k k (Reg i))))
                          (Seq (Inst (Mem Store r (Addr k 0w)))
                               (Inst (Arith (Binop Sub k k (Reg i)))))
    | StackGetSize r => Seq (Seq (move r k) (sub_inst r (k+1)))
                            (right_shift_inst r (word_shift (:'a)))
    | StackSetSize r => Seq (left_shift_inst r (word_shift (:'a)))
                            (Seq (move k (k+1)) (add_inst k r))
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

(* -- init code -- *)

val halt_inst_def = Define `
  halt_inst w = Seq (const_inst 1 w) (Halt 1)`

val store_list_code_def = Define `
  (store_list_code a t [] = Skip) /\
  (store_list_code a t (INL w::xs) =
    Seq (list_Seq [const_inst t w; store_inst t a; add_bytes_in_word_inst a])
        (store_list_code a t xs)) /\
  (store_list_code a t (INR i::xs) =
    Seq (list_Seq [store_inst i a; add_bytes_in_word_inst a])
        (store_list_code a t xs))`

(* k+1 is base, k is stack pointer, discards 0 *)
val init_memory_def = Define `
  init_memory k xs =
    list_Seq [const_inst 0 bytes_in_word;
              sub_inst k 0;
              const_inst 0 0w;
              store_inst 0 k;
              store_list_code (k+1) 0 xs]`;

val store_init_def = Define `
  store_init (k:num) =
    (K (INL 0w)) =++
      [(CurrHeap,INR (k+2));
       (NextFree,INR (k+2));
       (EndOfHeap,INR 2);
       (HeapLength,INR 5);
       (OtherHeap,INR 2);
       (BitmapBase,INR 3)]`

(* init code assumes:
    reg 1: start of program
    reg 2: first address in heap
    reg 3: first address in stack (and one past last address of heap)
    reg 4: one past last address of stack *)

val init_code_def = Define `
  init_code max_heap bitmaps k =
    let min_stack = LENGTH bitmaps + LENGTH store_list + 1 in
      if dimword (:'a) <= (dimindex (:'a) DIV 8) * min_stack \/
         dimword (:'a) <= (dimindex (:'a) DIV 8) * max_heap then
        halt_inst (10w:'a word)
      else
        list_Seq [(* check that pointers are in order *)
                If Lower 3 (Reg 2) (halt_inst 7w) Skip;
                If Lower 4 (Reg 3) (halt_inst 8w) Skip;
                (* check that heap size isn't too big *)
                move 0 3;
                sub_inst 0 2;
                const_inst 5 (n2w max_heap * bytes_in_word);
                If Lower 5 (Reg 0) (halt_inst 3w) Skip;
                (* check max_stack_alloc *)
                move 0 3;
                const_inst 5 (n2w (min_stack-1) * bytes_in_word);
                add_inst 0 5;
                const_inst 5 (n2w (max_stack_alloc) * bytes_in_word);
                If Lower 0 (Reg 5) (halt_inst 4w) Skip;
                (* check that stack size is big enough *)
                move 0 4;
                sub_inst 0 3;
                const_inst 5 (n2w min_stack * bytes_in_word);
                If Lower 0 (Reg 5) (halt_inst 5w) Skip;
                (* split heap into two, store heap length in 5 *)
                move 5 3;
                sub_inst 5 2;
                right_shift_inst 5 1;
                (* check that all values are aligned *)
                move 0 2;
                or_inst 0 3;
                or_inst 0 4;
                or_inst 0 5;
                If Test 0 (Imm 7w) Skip (halt_inst 5w);
                (* setup bitmaps, store, stack *)
                move (k+2) 2;
                add_inst 2 5;
                move k 4;
                move (k+1) 3;
                right_shift_inst 3 (word_shift (:'a));
                init_memory k (MAP INL bitmaps ++
                  MAP (store_init k) (REVERSE store_list));
                LocValue 0 1 0]`

val init_stubs_def = Define `
  init_stubs max_heap bitmaps k start =
    [(0n,Seq (init_code max_heap bitmaps k) (Call NONE (INL start) NONE));
     (1n,halt_inst 0w);
     (2n,halt_inst 2w)]`

val check_init_stubs_length = Q.store_thm("check_init_stubs_length",
  `LENGTH (init_stubs max_heap bitmaps k start) + 1 (* gc *) = stack_num_stubs`,
  EVAL_TAC);

(* -- full compiler -- *)

val compile_def = Define `
  compile max_heap bitmaps k start prog =
    init_stubs max_heap bitmaps k start ++ MAP (prog_comp k) prog`;

val _ = export_theory();
