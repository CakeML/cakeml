open preamble stackLangTheory;

val _ = new_theory "stack_remove";

(* TODO: arrange for a few very frequently used store vars to be in
         registers instead of memory. *)

val word_offset_def = Define `
  word_offset n = n2w (dimindex (:'a) DIV 8 * n):'a word`;

val store_pos_def = Define `
  store_pos name =
    case name of
    | NextFree => 1
    | FreeCount => 2
    | CurrHeap => 3
    | OtherHeap => 4
    | AllocSize => 5
    | Handler => 6:num
    | LastFree => 7
    | ProgStart => 8`

val store_length_def = Define `
  store_length = 8n`; (* must be even and <= store_pos n, for any n *)

val store_offset_def = Define `
  store_offset name = 0w - word_offset (store_pos name)`;

val stack_err_lab_def = Define `
  stack_err_lab = 5:num`;

val comp_def = Define `
  comp sp bp p =
    case p of
    (* remove store accesses *)
    | Get r name => Inst (Mem Load r (Addr bp (store_offset name)))
    | Set name r => Inst (Mem Store r (Addr bp (store_offset name)))
    (* remove stack operations *)
    | StackFree n => Inst (Arith (Binop Add sp sp (Imm (word_offset n))))
    | StackAlloc n => Seq (Inst (Arith (Binop Sub sp sp (Imm (word_offset n)))))
                          (JumpLess sp bp stack_err_lab)
    | StackStore r n => Inst (Mem Store r (Addr sp (word_offset n)))
    | StackLoad r n => Inst (Mem Load r (Addr sp (word_offset n)))
    | StackLoadAny r i => Seq (Inst (Arith (Binop Add r i (Reg sp))))
                              (Inst (Mem Load r (Addr r 0w)))
    | StackStoreAny r i => Seq (Inst (Arith (Binop Add sp sp (Reg i))))
                          (Seq (Inst (Mem Store r (Addr sp 0w)))
                               (Inst (Arith (Binop Sub sp sp (Reg i)))))
    | StackGetSize r => Inst (Arith (Binop Sub r sp (Reg bp)))
    | StackSetSize r => Inst (Arith (Binop Add sp bp (Reg r)))
    (* for the rest, just leave it unchanged *)
    | Seq p1 p2 => Seq (comp sp bp p1) (comp sp bp p2)
    | If c r ri p1 p2 => If c r ri (comp sp bp p1) (comp sp bp p2)
    | Call ret dest exc =>
        Call (case ret of
              | NONE => NONE
              | SOME (p1,lr,l1,l2) => SOME (comp sp bp p1,lr,l1,l2))
          dest (case exc of
                | NONE => NONE
                | SOME (p2,l1,l2) => SOME (comp sp bp p2,l1,l2))
    | p => p`

val prog_comp_def = Define `
  prog_comp sp bp (n,p) = (n,comp sp bp p)`

val compile_def = Define `
  compile (sp,bp) prog = MAP (prog_comp sp bp) prog`;

val _ = export_theory();
