open preamble stackLangTheory
     stack_to_labTheory
     stack_removeTheory
     stack_namesTheory;

val _ = new_theory "stack_to_target";

val move_inst_def = Define `
  move_inst dest src =
    if dest = src then Skip else
      Seq (Inst (Const dest 0w))
          (Inst (Arith (Binop Or dest dest (Reg src))))`

val sub_inst_def = Define `
  sub_inst r1 r2 =
    Inst (Arith (Binop Sub r1 r1 (Reg r2)))`

val const_inst_def = Define `
  const_inst r1 w =
    Inst (Const r1 w)`

val seq_list_def = Define `
  (seq_list [] = Skip) /\
  (seq_list [x] = x) /\
  (seq_list (x::xs) = Seq x (seq_list xs))`

val stubs_def = Define `
  stubs sp bp =
    [(0:num, seq_list [move_inst bp 3; (* init base pointer *)
                       move_inst sp 4; (* init stack pointer *)
                       const_inst 4 (word_offset store_length);
                       sub_inst 3 4;
                       (* heap start is in 2, heap end is in 3 *)
                       Call (SOME (Skip,0,0,1)) (INL 5) NONE;
                       Halt 0w (* success! *)]);
     (1, Halt 2w (* not enough stack space *))]`;

val compile_def = Define `
  compile f sp bp prog =
    let without_stack = stubs sp bp ++ stack_remove$compile (sp,bp) prog in
    let with_target_names = stack_names$compile f without_stack in
      stack_to_lab$compile with_target_names`;

val _ = export_theory();
