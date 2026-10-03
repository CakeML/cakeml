(*
  This compiler phase implements all stack operations as normal memory
  load/store operations.
*)
Theory stack_remove
Ancestors
  stackLang
  misc[qualified] (* for bytes_in_word *)
  mlstring
Libs
  preamble


(* -- compiler -- *)

Definition max_stack_alloc_def:
  max_stack_alloc = 255n
End

Definition word_offset_def:
  word_offset aw n = &(arch_bytes aw * n) : int
End

Definition store_list_def:
  store_list = [NextFree; EndOfHeap; HeapLength; OtherHeap; TriggerGC;
                AllocSize; Handler; Globals; GlobReal; ProgStart; BitmapBase;
                GenStart; CodeBuffer; CodeBufferEnd; BitmapBuffer; BitmapBufferEnd;
                Temp 00w; Temp 01w; Temp 02w; Temp 03w; Temp 04w;
                Temp 05w; Temp 06w; Temp 07w; Temp 08w; Temp 09w;
                Temp 10w; Temp 11w; Temp 12w; Temp 13w; Temp 14w;
                Temp 15w; Temp 16w; Temp 17w; Temp 18w; Temp 19w;
                Temp 20w; Temp 21w; Temp 22w; Temp 23w; Temp 24w;
                Temp 25w; Temp 26w; Temp 27w; Temp 28w; Temp 29w;
                Temp 30w; Temp 31w]
End

Definition store_pos_def:
  store_pos name =
    case INDEX_FIND 0 (\n. n = name) store_list of
    | NONE => 0n
    | SOME (i,_) => i+1
End

Definition store_length_def:
  store_length =
    if EVEN (LENGTH store_list) then LENGTH store_list
    else LENGTH store_list + 1
End

Definition store_offset_def:
  store_offset aw name = - word_offset aw (store_pos name)
End

Definition stack_err_lab_def:
  stack_err_lab = 2n
End

Definition halt_inst_def:
  halt_inst w = Seq (const_inst 1 w) (Halt 1)
End

(*
    k is stack pointer register
    k+1 is base of store array (and last stack address)
    k+2 is CurrHeap (which is kept in a register for improved speed)
*)

Definition single_stack_alloc_def:
  single_stack_alloc aw jump k n =
    if jump
    then
      Seq (Inst (Arith (Binop Sub k k (Imm (word_offset aw n)))))
          (JumpLower k (k+1) stack_err_lab)
    else
       Seq (Inst (Arith (Binop Sub k k (Imm (word_offset aw n)))))
          (If Lower k (Reg (k+1)) (halt_inst 2) Skip)
End

Definition stack_alloc_def:
  stack_alloc aw jump k n =
    if n = 0 then Skip else
    if n <= max_stack_alloc then single_stack_alloc aw jump k n else
      Seq (single_stack_alloc aw jump k max_stack_alloc)
          (stack_alloc aw jump k (n - max_stack_alloc))
Termination
  WF_REL_TAC `measure (SND o SND o SND)` \\ fs [max_stack_alloc_def] \\ decide_tac
End

Definition single_stack_free_def:
  single_stack_free aw k n =
    Inst (Arith (Binop Add k k (Imm (word_offset aw n))))
End

Definition stack_free_def:
  stack_free aw k n =
    if n = 0 then Skip else
    if n <= max_stack_alloc then single_stack_free aw k n else
      Seq (single_stack_free aw k max_stack_alloc)
          (stack_free aw k (n - max_stack_alloc))
Termination
  WF_REL_TAC `measure (SND o SND)` \\ fs [max_stack_alloc_def] \\ decide_tac
End

(* upshift the stack pointer *)
Definition upshift_def:
  upshift aw r n =
    if n ≤ max_stack_alloc then
      Inst (Arith (Binop Add r r (Imm (word_offset aw n))))
    else
      Seq (Inst (Arith (Binop Add r r (Imm (word_offset aw max_stack_alloc)))))
      (upshift aw r (n-max_stack_alloc))
Termination
  WF_REL_TAC `measure (SND o SND)` \\ fs [max_stack_alloc_def] \\ decide_tac
End

Definition downshift_def:
  downshift aw r n =
    if n ≤ max_stack_alloc then
      Inst (Arith (Binop Sub r r (Imm (word_offset aw n))))
    else
      Seq (Inst (Arith (Binop Sub r r (Imm (word_offset aw max_stack_alloc)))))
      (downshift aw r (n-max_stack_alloc))
Termination
  WF_REL_TAC `measure (SND o SND)` \\ fs [max_stack_alloc_def] \\ decide_tac
End

(* Shifts k up and down to store r into n*)
Definition stack_store_def:
  stack_store aw k r n =
     Seq (upshift aw k n)
    (Seq (Inst (Mem Store r (Addr k 0))) (downshift aw k n))
End

Definition stack_load_def:
  stack_load aw r n =
    Seq (upshift aw r n) (Inst (Mem Load r (Addr r 0)))
End

Definition copy_each_def:
  copy_each aw t1 t2 =
    While NotEqual 1 (Imm 1)
      (list_Seq [load_inst t1 t2;
                 add_bytes_in_word_inst aw t2;
                 If Test 1 (Imm 1) Skip (add_inst t1 3);
                 right_shift_inst 1 1;
                 store_inst t1 2;
                 add_bytes_in_word_inst aw 2])
End

Definition copy_loop_def:
  copy_loop aw t1 t2 =
    list_Seq [load_inst 1 t2;
              add_bytes_in_word_inst aw t2;
              While Less 1 (Imm 0)
                (list_Seq [copy_each aw t1 t2;
                           load_inst 1 t2;
                           add_bytes_in_word_inst aw t2]);
              copy_each aw t1 t2]
End

Definition comp_def:
  comp aw jump off k p =
    case p of
    (* remove store accesses *)
    | Get r name =>
        if name = CurrHeap then move r (k+2)
        else Inst (Mem Load r (Addr (k+1) (store_offset aw name)))
    | Set name r =>
        if name = CurrHeap then move (k+2) r
        else Inst (Mem Store r (Addr (k+1) (store_offset aw name)))
    | OpCurrHeap op r n =>
        Inst (Arith (Binop op r n (Reg (k+2))))
    (* remove stack operations *)
    | StackFree n => stack_free aw k n
    | StackAlloc n => stack_alloc aw jump k n
    | StackStore r n =>
      let w = word_offset aw n in
      if int_offset_ok off w then
        Inst (Mem Store r (Addr k w))
      else
        stack_store aw k r n
    | StackLoad r n =>
      let w = word_offset aw n in
      if int_offset_ok off w then
        Inst (Mem Load r (Addr k w))
      else
        Seq (move r k) (stack_load aw r n)
    | DataBufferWrite r1 r2 => Inst (Mem Store r2 (Addr r1 0)) (* remove data buffer *)
    | StackLoadAny r i => Seq (Seq (move r i) (add_inst r k))
                              (Inst (Mem Load r (Addr r 0)))
    | StackStoreAny r i => Seq (Inst (Arith (Binop Add k k (Reg i))))
                          (Seq (Inst (Mem Store r (Addr k 0)))
                               (Inst (Arith (Binop Sub k k (Reg i)))))
    | StackGetSize r => Seq (Seq (move r k) (sub_inst r (k+1)))
                            (right_shift_inst r (arch_shift aw))
    | StackSetSize r => Seq (left_shift_inst r (arch_shift aw))
                            (Seq (move k (k+1)) (add_inst k r))
    | BitmapLoad r v =>
        list_Seq [Inst (Mem Load r (Addr (k+1) (store_offset aw BitmapBase)));
                  add_inst r v;
                  left_shift_inst r (arch_shift aw);
                  Inst (Mem Load r (Addr r 0))]
    | StoreConsts t1 t2 _ =>
        list_Seq [Inst (Mem Load t2 (Addr (k+1) (store_offset aw BitmapBase)));
                  add_inst t2 1;
                  left_shift_inst t2 (arch_shift aw);
                  copy_loop aw t1 t2;
                  move t1 1;
                  move t2 1]
    (* for the rest, just leave it unchanged *)
    | Seq p1 p2 => Seq (comp aw jump off k p1) (comp aw jump off k p2)
    | If c r ri p1 p2 => If c r ri (comp aw jump off k p1) (comp aw jump off k p2)
    | Loop p1 => Loop (comp aw jump off k p1)
    | Call ret dest exc =>
        Call (case ret of
              | NONE => NONE
              | SOME (p1,lr,l1,l2) => SOME (comp aw jump off k p1,lr,l1,l2))
          dest (case exc of
                | NONE => NONE
                | SOME (p2,l1,l2) => SOME (comp aw jump off k p2,l1,l2))
    | p => p
End

Definition prog_comp_def:
  prog_comp aw jump off k (n,p) = (n,comp aw jump off k p)
End

(* -- init code -- *)

Definition store_list_code_def:
  (store_list_code aw a t [] = Skip) /\
  (store_list_code aw a t (INL w::xs) =
    Seq (list_Seq [const_inst t w; store_inst t a; add_bytes_in_word_inst aw a])
        (store_list_code aw a t xs)) /\
  (store_list_code aw a t (INR i::xs) =
    Seq (list_Seq [store_inst i a; add_bytes_in_word_inst aw a])
        (store_list_code aw a t xs))
End

(* k+1 is base, k is stack pointer, discards 0 *)
Definition init_memory_def:
  init_memory aw k xs =
    list_Seq [const_inst 0 (&(arch_bytes aw));
              sub_inst k 0;
              const_inst 0 0;
              store_inst 0 k;
              store_list_code aw (k+1) 0 xs]
End

Definition store_init_def:
  store_init gen_gc (k:num) =
    (K (INL 0)) =++
      [(CurrHeap,INR (k+2));
       (GlobReal,INR (k+2));
       (NextFree,INR (k+2));
       (TriggerGC,INR (if gen_gc then k+2 else 2));
       (EndOfHeap,INR 2);
       (HeapLength,INR 5);
       (OtherHeap,INR 2);
       (BitmapBase,INR 3);
       (BitmapBuffer,INR 4);
       (BitmapBufferEnd,INR 6);
       (CodeBuffer,INR 7);
       (CodeBufferEnd,INR 1)]
End

(* init code assumes:
    reg 1: start of program
    reg 2: first address in heap
    reg 3: first address in stack (and one past last address of heap)
    reg 4: one past last address of stack *)

Definition init_code_def:
  init_code aw gen_gc max_heap k =
    let max_heap = (if max_heap * arch_bytes aw < 2 ** arch_width_bits aw
                    then &(max_heap * arch_bytes aw)
                    else -1) in
      list_Seq [(* compute the middle address, store in reg0 *)
                move 0 4;
                sub_inst 0 2;
                right_shift_inst 0 (1 + arch_shift aw);
                left_shift_inst 0 (arch_shift aw);
                add_inst 0 2;
                (* if reg3 is not between start and end of memory, then put
                   it in the middle (i.e. split heap and stack evenly) *)
                const_inst 5 (&(max_stack_alloc * arch_bytes aw));
                add_inst 2 5;
                sub_inst 4 5;
                If Lower 3 (Reg 2) (move 3 0)
                  (If Lower 4 (Reg 3) (move 3 0) Skip);
                const_inst 0 (&(max_stack_alloc * arch_bytes aw));
                sub_inst 2 0;
                add_inst 4 0;
                (* shrink the heap if it is too big *)
                move 0 3;
                sub_inst 0 2;
                const_inst 5 max_heap;
                If Lower 5 (Reg 0) (Seq (move 3 2) (add_inst 3 5)) Skip;
                (* ensure heap is even number of words *)
                sub_inst 3 2;
                right_shift_inst 3 (arch_shift aw + 1);
                left_shift_inst 3 (arch_shift aw + 1);
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
                right_shift_inst 3 (arch_shift aw);
                move 0 (k+2);
                add_bytes_in_word_inst aw 0;
                load_inst 4 0;
                add_bytes_in_word_inst aw 0;
                load_inst 6 0;
                add_bytes_in_word_inst aw 0;
                load_inst 7 0;
                add_bytes_in_word_inst aw 0;
                load_inst 1 0;
                init_memory aw k (MAP (store_init gen_gc k) (REVERSE store_list));
                LocValue 0 1 0]
End

Definition init_stubs_def:
  init_stubs aw gen_gc max_heap k start =
    [(0n,Seq (init_code aw gen_gc max_heap k) (Call NONE (INL start) NONE));
     (1n,halt_inst 0);
     (2n,halt_inst 2)]
End

Definition stub_names_def:
  stub_names () = [
    (0n,implode "_Init");
    (1n,implode "_Halt0");
    (2n,implode "_Halt2")]
End

Theorem check_init_stubs_length:
  LENGTH (init_stubs aw gen_gc max_heap k start) + 2 (* gc + dummy *) =
  stack_num_stubs
Proof
  EVAL_TAC
QED

(* -- full compiler -- *)

Definition compile_def:
  compile aw jump off gen_gc max_heap k start prog =
    init_stubs aw gen_gc max_heap k start ++
    MAP (prog_comp aw jump off k) prog
End
