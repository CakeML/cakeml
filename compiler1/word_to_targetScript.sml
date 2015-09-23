open preamble stack_to_targetTheory
     word_allocTheory word_instTheory
     word_to_stackTheory
     stack_to_targetTheory;

val _ = new_theory "word_to_target";

(*
Order of compilation (and their status):
1) Flatten expressions to binary (Done)
2) Inst select (At proof)
3) SSA (Done)
5) Dead code elim (not written yet)
4) 3 to 2 regs for certain configs (Done)
5) reg_alloc (Done)
6) word_to_stack
*)

(*TODO: Maybe chain the max vars in a neater way instead of recomputing*)
(*TODO: probably need to change reg_count to handle the restricted regs*)
val compile_single_def = Define`
  compile_single two_reg_arith reg_count (name_num:num,arg_count,prog) =
  let maxv = max_var prog + 1 in
  let inst_prog = inst_select maxv prog in
  let ssa_prog = full_ssa_cc_trans arg_count inst_prog in
  let prog = if two_reg_arith then three_to_two_reg ssa_prog
                              else ssa_prog in
  let reg_prog = word_alloc reg_count prog in
    (name_num,word_to_stack$compile reg_prog arg_count reg_count)`

(*TODO: Compilation function probably needs to take an alist of (argcount,prog) -- this is a guess*)

val get_conf_props_def = Define `
  get_conf_props ((f,sp,bp,(c,enc,l)):'a stack_conf) =
    (c.two_reg_arith, c.reg_count - 4)`;

val compile_def = Define `
  compile start (conf:'a stack_conf) prog =
    let (two_reg_arith,reg_count) = get_conf_props conf in
    let prog = MAP (compile_single two_reg_arith reg_count) prog in
      stack_to_target$compile start conf prog`

val _ = export_theory ();
