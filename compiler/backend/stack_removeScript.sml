(*
  This compiler phase implements all stack operations as normal memory
  load/store operations.
*)

open preamble stackLangTheory

val _ = new_theory "stack_remove";

val _ = set_grammar_ancestry ["stackLang",
  "misc" (* for bytes_in_word *) ];

(* -- compiler -- *)

val max_stack_alloc_def = Define `
  max_stack_alloc = 255n`;

val word_offset_def = Define `
  word_offset n = n2w (dimindex (:'a) DIV 8 * n):'a word`;

val store_list_def = Define `
  store_list = [NextFree; EndOfHeap; HeapLength; OtherHeap; TriggerGC;
                AllocSize; Handler; Globals; ProgStart; BitmapBase; GenStart;
                CodeBuffer; CodeBufferEnd; BitmapBuffer; BitmapBufferEnd;
                Temp 00w; Temp 01w; Temp 02w; Temp 03w; Temp 04w;
                Temp 05w; Temp 06w; Temp 07w; Temp 08w; Temp 09w;
                Temp 10w; Temp 11w; Temp 12w; Temp 13w; Temp 14w;
                Temp 15w; Temp 16w; Temp 17w; Temp 18w; Temp 19w;
                Temp 20w; Temp 21w; Temp 22w; Temp 23w; Temp 24w;
                Temp 25w; Temp 26w; Temp 27w; Temp 28w; Temp 29w;
                Temp 30w; Temp 31w]`

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

val halt_inst_def = Define `
  halt_inst w = Seq (const_inst 1 w) (Halt 1)`

(*
    k is stack pointer register
    k+1 is base of store array (and last stack address)
    k+2 is CurrHeap (which is kept in a register for improved speed)
*)

val single_stack_alloc_def = Define `
  single_stack_alloc jump k n =
    if jump
    then
      Seq (Inst (Arith (Binop Sub k k (Imm (word_offset n)))))
          (JumpLower k (k+1) stack_err_lab)
    else
       Seq (Inst (Arith (Binop Sub k k (Imm (word_offset n)))))
          (If Lower k (Reg (k+1)) (halt_inst 2w) Skip)`

val stack_alloc_def = tDefine "stack_alloc" `
  stack_alloc jump k n =
    if n = 0 then Skip else
    if n <= max_stack_alloc then single_stack_alloc jump k n else
      Seq (single_stack_alloc jump k max_stack_alloc)
          (stack_alloc jump k (n - max_stack_alloc))`
 (WF_REL_TAC `measure (SND o SND)` \\ fs [max_stack_alloc_def] \\ decide_tac)

val single_stack_free_def = Define `
  single_stack_free k n =
    Inst (Arith (Binop Add k k (Imm (word_offset n))))`

val stack_free_def = tDefine "stack_free" `
  stack_free k n =
    if n = 0 then Skip else
    if n <= max_stack_alloc then single_stack_free k n else
      Seq (single_stack_free k max_stack_alloc)
          (stack_free k (n - max_stack_alloc))`
 (WF_REL_TAC `measure SND` \\ fs [max_stack_alloc_def] \\ decide_tac)

(* upshift the stack pointer *)
val upshift_def = tDefine"upshift"`
  upshift r n =
    if n ≤ max_stack_alloc then
      (Inst (Arith (Binop Add r r (Imm (word_offset n))))):'a stackLang$prog
    else
      Seq (Inst (Arith (Binop Add r r (Imm (word_offset max_stack_alloc)))))
      (upshift r (n-max_stack_alloc))`
  (WF_REL_TAC `measure SND` \\ fs [max_stack_alloc_def] \\ decide_tac)

val downshift_def = tDefine"downshift"`
  downshift r n =
    if n ≤ max_stack_alloc then
      (Inst (Arith (Binop Sub r r (Imm (word_offset n))))) :'a stackLang$prog
    else
      Seq (Inst (Arith (Binop Sub r r (Imm (word_offset max_stack_alloc)))))
      (downshift r (n-max_stack_alloc))`
  (WF_REL_TAC `measure SND` \\ fs [max_stack_alloc_def] \\ decide_tac)

(* Shifts k up and down to store r into n*)
val stack_store_def = Define`
  stack_store k r n =
     Seq (upshift k n)
    (Seq (Inst (Mem Store r (Addr k 0w))) (downshift k n))`

val stack_load_def = Define`
  stack_load r n =
    Seq (upshift r n) (Inst (Mem Load r (Addr r 0w))):'a stackLang$prog`

val comp_def = Define `
  comp jump off k (p:'a stackLang$prog) =
    case p of
    (* remove store accesses *)
    | Get r name =>
        if name = CurrHeap then move r (k+2)
        else Inst (Mem Load r (Addr (k+1) (store_offset name)))
    | Set name r =>
        if name = CurrHeap then move (k+2) r
        else Inst (Mem Store r (Addr (k+1) (store_offset name)))
    (* remove stack operations *)
    | StackFree n => stack_free k n
    | StackAlloc n => stack_alloc jump k n
    | StackStore r n =>
      let w = word_offset n in
      if offset_ok 0 off w then
        Inst (Mem Store r (Addr k w))
      else
        stack_store k r n
    | StackLoad r n =>
      let w = word_offset n in
      if offset_ok 0 off w then
        Inst (Mem Load r (Addr k w))
      else
        Seq (move r k) (stack_load r n)
    | DataBufferWrite r1 r2 => Inst (Mem Store r2 (Addr r1 0w)) (* remove data buffer *)
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
    | Seq p1 p2 => Seq (comp jump off k p1) (comp jump off k p2)
    | If c r ri p1 p2 => If c r ri (comp jump off k p1) (comp jump off k p2)
    | While c r ri p1 => While c r ri (comp jump off k p1)
    | Call ret dest exc =>
        Call (case ret of
              | NONE => NONE
              | SOME (p1,lr,l1,l2) => SOME (comp jump off k p1,lr,l1,l2))
          dest (case exc of
                | NONE => NONE
                | SOME (p2,l1,l2) => SOME (comp jump off k p2,l1,l2))
    | p => p`

val prog_comp_def = Define `
  prog_comp jump off k (n,p) = (n,comp jump off k p)`

(* -- init code -- *)

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
  store_init gen_gc (k:num) =
    (K (INL 0w)) =++
      [(CurrHeap,INR (k+2));
       (NextFree,INR (k+2));
       (TriggerGC,INR (if gen_gc then k+2 else 2));
       (EndOfHeap,INR 2);
       (HeapLength,INR 5);
       (OtherHeap,INR 2);
       (BitmapBase,INR 3);
       (BitmapBuffer,INR 4);
       (BitmapBufferEnd,INR 6);
       (CodeBuffer,INR 7);
       (CodeBufferEnd,INR 1)]`

(* init code assumes:
    reg 1: start of program
    reg 2: first address in heap
    reg 3: first address in stack (and one past last address of heap)
    reg 4: one past last address of stack *)

val init_code_def = Define `
  init_code gen_gc max_heap k =
    let max_heap = (if max_heap * w2n (bytes_in_word:'a word) < dimword (:'a)
                    then n2w max_heap * bytes_in_word
                    else 0w-1w) in
      list_Seq [(* compute the middle address, store in reg0 *)
                move 0 4;
                sub_inst 0 2;
                right_shift_inst 0 (1 + word_shift (:'a));
                left_shift_inst 0 (word_shift (:'a));
                add_inst 0 2;
                (* if reg3 is not between start and end of memory, then put
                   it in the middle (i.e. split heap and stack evenly) *)
                const_inst 5 (n2w max_stack_alloc * bytes_in_word:'a word);
                add_inst 2 5;
                sub_inst 4 5;
                If Lower 3 (Reg 2) (move 3 0)
                  (If Lower 4 (Reg 3) (move 3 0) Skip);
                const_inst 0 (n2w max_stack_alloc * bytes_in_word:'a word);
                sub_inst 2 0;
                add_inst 4 0;
                (* shrink the heap if it is too big *)
                move 0 3;
                sub_inst 0 2;
                const_inst 5 max_heap;
                If Lower 5 (Reg 0) (Seq (move 3 2) (add_inst 3 5)) Skip;
                (* ensure heap is even number of words *)
                sub_inst 3 2;
                right_shift_inst 3 (word_shift (:'a) + 1);
                left_shift_inst 3 (word_shift (:'a) + 1);
                add_inst 3 2;
                (* split heap into two, store heap length in 5 *)
                move 5 3;
                sub_inst 5 2;
                right_shift_inst 5 1;
                (* setup store, stack *)
                move (k+2) 2;
                add_inst 2 5;
                move k 4;
                move (k+1) 3;
                load_inst 3 (k+2);
                right_shift_inst 3 (word_shift (:'a));
                move 0 (k+2);
                add_bytes_in_word_inst 0;
                load_inst 4 0;
                add_bytes_in_word_inst 0;
                load_inst 6 0;
                add_bytes_in_word_inst 0;
                load_inst 7 0;
                add_bytes_in_word_inst 0;
                load_inst 1 0;
                init_memory k (MAP (store_init gen_gc k) (REVERSE store_list));
                LocValue 0 1 0]`

val init_stubs_def = Define `
  init_stubs gen_gc max_heap k start =
    [(0n,Seq (init_code gen_gc max_heap k) (Call NONE (INL start) NONE));
     (1n,halt_inst 0w);
     (2n,halt_inst 2w)]`

Theorem check_init_stubs_length:
   LENGTH (init_stubs gen_gc max_heap k start) + 1 (* gc *) =
   stack_num_stubs
Proof
  EVAL_TAC
QED

(* -- full compiler -- *)

val compile_def = Define `
  compile jump off gen_gc max_heap k start prog =
    init_stubs gen_gc max_heap k start ++
    MAP (prog_comp jump off k) prog`;

val _ = export_theory();
