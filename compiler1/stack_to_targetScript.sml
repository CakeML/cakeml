open preamble stackLangTheory
     stack_to_labTheory
     stack_removeTheory
     stack_namesTheory
     lab_to_targetTheory;
     

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

val stub0_def = Define `
  stub0 sp bp =
    (0:num, seq_list [move_inst bp 3; (* init base pointer *)
                      move_inst sp 4; (* init stack pointer *)
                      move_inst 0 sp;
                      sub_inst 0 bp;
                      const_inst 4 (word_offset store_length);
                      sub_inst 3 4;
                      (* stack length in 0,
                         first program point in 1,
                         heap start is in 2,
                         heap end is in 3 *)
                      Call NONE (INL 1) NONE])`;

val stub1_def = Define `
  stub1 =
    (1:num, seq_list [Set Handler 0;
                      Set ProgStart 1;
                      Set CurrHeap 2;
                      Set LastFree 3;
                      Call NONE (INL 5) NONE])`

val compile_def = Define `
  compile c enc f sp bp prog =
    let prog' = stub1 :: prog in
    let without_stack = stub0 sp bp :: stack_remove$compile (sp,bp) prog' in
    let with_target_names = stack_names$compile f without_stack in
    let sec_list = stack_to_lab$compile with_target_names in 
      lab_to_target$compile c enc sec_list`;

val _ = export_theory();
