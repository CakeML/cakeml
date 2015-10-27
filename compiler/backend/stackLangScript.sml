open preamble wordLangTheory;

val _ = new_theory "stackLang";

val _ = Datatype `
  prog = Skip
       | Inst ('a inst)
       | Get num store_name
       | Set store_name num
       | Call ((stackLang$prog # num # num # num) option)
              (* return-handler code, link reg, labels l1,l2*)
              (num + num) (* target of call *)
              ((stackLang$prog # num # num) option)
              (* handler: exception-handler code, labels l1,l2*)
       | Seq stackLang$prog stackLang$prog
       | If cmp num ('a reg_imm) stackLang$prog stackLang$prog
       | JumpLess num num num (* reg, reg, target name *)
       | Alloc num
       | Raise num
       | Return num num
       | FFI num num num (* FFI index, array_ptr, array_len *)
       | Tick
       (* new in stackLang, compared to wordLang, below *)
       | StackAlloc num
       | StackFree num
       | StackStore num num     (* offset, fast *)
       | StackStoreAny num num  (* reg contains offset, slow, used by GC *)
       | StackLoad num num      (* offset, fast *)
       | StackLoadAny num num   (* reg contains offset, slow, used by GC *)
       | StackGetSize num       (* used when installing exc handler *)
       | StackSetSize num       (* used by implementation of raise *)
       | Halt num`;

val _ = export_theory();
