open HolKernel bossLib boolLib EmitTeX basis_emitTheory
open BytecodeTheory bytecodeTerminationTheory bytecodeEvalTheory
val _ = new_theory "bytecode_emit"

val _ = Parse.disable_tyabbrev_printing "env"
val _ = Parse.disable_tyabbrev_printing "alist"

val data = map
  (fn th => EmitML.DATATYPE [QUOTE (datatype_thm_to_string th)])
  [datatype_bc_stack_op,
   datatype_loc,
   datatype_bc_inst,
   datatype_bc_value,
   datatype_bc_state]

val init_bc_state_def =  Define`
  init_bc_state = <|
    stack := [];
    code := [];
    pc := 0;
    refs := FEMPTY;
    handler := 0;
    inst_length := λi. 0 |>`

val defs = map EmitML.DEFN [
optionTheory.OPTION_BIND_def,
is_Label_def,bc_fetch_aux_def,bc_fetch_def,
bc_find_loc_aux_def,bc_find_loc_def,
bump_pc_def,bool_to_tag_def,unit_tag_def,closure_tag_def,block_tag_def,
bool_to_val_def,unit_val_def,isNumber_def,
bc_eval_stack_def,bc_eval1_def,bc_eval_def,
init_bc_state_def]

val _ = EmitML.eSML "bytecode" (
  (EmitML.OPEN ["int","fmap"])
::(EmitML.MLSIG "type num = numML.num")
::(EmitML.MLSIG "type int = intML.int")
::(EmitML.MLSIG "type ('a,'b) fmap = ('a,'b) fmapML.fmap")
::data@defs)

val _ = export_theory ();
