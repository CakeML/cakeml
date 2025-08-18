(*
  The stackLang intermediate language is a structured programming
  language with function calls, while loops, if statements, etc. All
  assignments are assembly instructions and register allocation is
  assumed to have been done. This is the language within which stack
  operations get optimised and turned into normal memory accesses.
*)
Theory stackLang
Ancestors
  asm backend_common
  misc[qualified] (* for bytes_in_word *)
Libs
  preamble


Datatype:
  store_name =
    NextFree | EndOfHeap | TriggerGC | HeapLength | ProgStart | BitmapBase |
    CurrHeap | OtherHeap | AllocSize | Globals | GlobReal | Handler | GenStart |
    CodeBuffer | CodeBufferEnd | BitmapBuffer | BitmapBufferEnd |
    Temp (5 word)
End

Datatype:
  prog = Skip
       | Inst ('a inst)
       | Get num store_name
       | Set store_name num
       | OpCurrHeap binop num num
       | Call ((stackLang$prog # num # num # num) option)
              (* return-handler code, link reg, labels l1,l2*)
              (num + num) (* target of call *)
              ((stackLang$prog # num # num) option)
              (* handler: exception-handler code, labels l1,l2*)
       | Seq stackLang$prog stackLang$prog
       | If cmp num ('a reg_imm) stackLang$prog stackLang$prog
       | While cmp num ('a reg_imm) stackLang$prog
       | JumpLower num num num (* reg, reg, target name *)
       | Alloc num
       | StoreConsts num num (num option) (* reg, reg, stub name to call *)
       | Raise num
       | Return num
       | FFI string num num num num num (* FFI index, conf_ptr, conf_len,
                                           array_ptr, array_len, ret_addr *)
       | Tick
       | LocValue num num num   (* assign v1 := Loc v2 v3 *)
       | Install num num num num num (* code buffer start, length of new code,
                                      data buffer start, length of new data, ret_addr *)
       | ShMemOp memop num ('a addr) (* share memory operation, register, addr to load/store *)
       | CodeBufferWrite num num (* code buffer address, byte to write *)
       | DataBufferWrite num num (* data buffer address, word to write *)
       (* new in stackLang, compared to wordLang, below *)
       | RawCall num            (* tail-call into body of function (past stack alloc) *)
       | StackAlloc num         (* allocate n slots on the stack *)
       | StackFree num          (* free n slots on the stack *)
       | StackStore num num     (* offset, fast *)
       | StackStoreAny num num  (* reg contains offset, slow, used by GC *)
       | StackLoad num num      (* offset, fast *)
       | StackLoadAny num num   (* reg contains offset, slow, used by GC *)
       | StackGetSize num       (* used when installing exc handler *)
       | StackSetSize num       (* used by implementation of raise *)
       | BitmapLoad num num     (* load word from read-only region *)
       | Halt num
End

val _ = map overload_on
  [("move",``\dest src. Inst (Arith (Binop Or dest src (Reg src)))``),
   ("sub_1_inst",``\r1. Inst (Arith (Binop Sub r1 r1 (Imm 1w)))``),
   ("sub_inst",``\r1 r2. Inst (Arith (Binop Sub r1 r1 (Reg r2)))``),
   ("add_inst",``\r1 r2. Inst (Arith (Binop Add r1 r1 (Reg r2)))``),
   ("and_inst",``\r1 r2. Inst (Arith (Binop And r1 r1 (Reg r2)))``),
   ("xor_inst",``\r1 r2. Inst (Arith (Binop Xor r1 r1 (Reg r2)))``),
   ("add_1_inst",``\r1. Inst (Arith (Binop Add r1 r1 (Imm 1w)))``),
   ("or_inst",``\r1 r2. Inst (Arith (Binop Or r1 r1 (Reg r2)))``),
   ("add_bytes_in_word_inst",``\r1. Inst (Arith (Binop Add r1 r1 (Imm (bytes_in_word))))``),
   ("div2_inst",``\r. Inst (Arith (Shift Lsr r r (Imm 1w)))``),
   ("left_shift_inst",``\r v. Inst (Arith (Shift Lsl r r (Imm (n2w v))))``),
   ("right_shift_inst",``\r v. Inst (Arith (Shift Lsr r r (Imm (n2w v))))``),
   ("const_inst",``\r w. Inst (Const r w)``),
   ("load_inst",``\r a. Inst (Mem Load r (Addr a 0w))``),
   ("store_inst",``\r a. Inst (Mem Store r (Addr a 0w))``)]

Definition list_Seq_def:
  (list_Seq [] = Skip) /\
  (list_Seq [x] = x) /\
  (list_Seq (x::y::xs) = Seq x (list_Seq (y::xs)))
End

Definition gc_stub_location_def:
  gc_stub_location = stack_num_stubs-1
End
Definition store_consts_stub_location_def:
  store_consts_stub_location = gc_stub_location-1
End
Theorem gc_stub_location_eq =
  gc_stub_location_def |> CONV_RULE(RAND_CONV EVAL)
Theorem store_consts_stub_location_eq =
  store_consts_stub_location_def |> CONV_RULE(RAND_CONV EVAL)
