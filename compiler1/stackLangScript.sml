open preamble wordLangTheory;

val _ = new_theory "stackLang";

val _ = Datatype `
  prog = Skip
       | Inst ('a inst)
       | Get num store_name
       | Set store_name num
       | Call ((stackLang$prog # num # num) option)
              (* return var, return-handler code, labels l1,l2*)
              (num + num) (* target of call *)
              ((stackLang$prog # num # num) option)
              (* handler: exception-handler code, labels l1,l2*)
       | Seq stackLang$prog stackLang$prog
       | If cmp num ('a reg_imm) stackLang$prog stackLang$prog
       | Alloc num
       | Raise num
       | Return num num
       | Tick
       (* new in stackLang, compared to wordLang, below *)
       | StackAlloc num
       | StackStore num num
       | StackLoad num num
       | StackFree num `;

val _ = export_theory();
