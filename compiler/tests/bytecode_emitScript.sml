open HolKernel bossLib boolLib EmitTeX basis_emitTheory
open CompilerLibTheory PrinterTheory BytecodeTheory bytecodeTerminationTheory bytecodeEvalTheory
val _ = new_theory "bytecode_emit"

val _ = Parse.temp_type_abbrev("string",``:char list``)
val _ = Parse.disable_tyabbrev_printing "env"
val _ = Parse.disable_tyabbrev_printing "alist"
val _ = Parse.disable_tyabbrev_printing "tvarN"
val _ = Feedback.set_trace "Greek tyvars" 0 (* EmitML should do this *)

val data = map
  (fn th => EmitML.DATATYPE [QUOTE (datatype_thm_to_string th)])
  [AstTheory.datatype_lit,
   AstTheory.datatype_id,
   SemanticPrimitivesTheory.datatype_eq_result,
   datatype_bc_stack_op,
   datatype_loc,
   datatype_ov,
   datatype_bc_inst,
   datatype_bc_value,
   datatype_bc_state]

val init_bc_state_def =  Define`
  init_bc_state = <|
    stack := [];
    code := [Stop];
    pc := 0;
    refs := FEMPTY;
    handler := 0;
    output := "";
    cons_names := [];
    inst_length := λi. 0;
    clock := NONE |>`

val _ = new_constant("STRING",``:char -> string -> string``)
val _ = ConstMapML.prim_insert(``STRING``,(false,"","STRING",type_of``STRING``))
val _ = new_constant("CONCAT",``:string list -> string``)
val _ = ConstMapML.prim_insert(``CONCAT``,(false,"","CONCAT",type_of``CONCAT``))
val CONCAT_RULE = PURE_REWRITE_RULE[mk_thm([],mk_eq(``FLAT:string list -> string``,``CONCAT``))]

val defs = map EmitML.DEFN [
optionTheory.OPTION_BIND_def,
fapply_def,
SemanticPrimitivesTheory.int_to_string_def,
SemanticPrimitivesTheory.id_to_string_def,
the_def,
LibTheory.lookup_def,
intersperse_def,
ov_to_string_def,
is_Block_def,is_Label_def,bc_fetch_aux_def,bc_fetch_def,
bc_find_loc_aux_def,bc_find_loc_def,
bump_pc_def,bool_to_tag_def,unit_tag_def,closure_tag_def,block_tag_def,
bool_to_val_def,unit_val_def,isNumber_def,
bc_equality_result_to_val_def,
bv_to_ov_def,
bc_equal_def,
bc_eval_stack_def,
CONCAT_RULE(CONV_RULE(PURE_REWRITE_CONV[mk_thm([],mk_eq(``CONS:char -> string -> string``,``STRING``))]) bc_eval1_def),
bc_eval_compute,
init_bc_state_def
,bytecodeLabelsTheory.collect_labels_def
,bytecodeLabelsTheory.all_labels_def
,bytecodeLabelsTheory.inst_labels_def
,bytecodeLabelsTheory.code_labels_def
,bytecodeLabelsTheory.strip_labels_def
]

val _ = EmitML.eSML "bytecode" (
  (EmitML.OPEN ["int","fmap","string"])
::(EmitML.MLSIG "type num = numML.num")
::(EmitML.MLSIG "type int = intML.int")
::(EmitML.MLSIG "type ('a,'b) fmap = ('a,'b) fmapML.fmap")
::(EmitML.MLSTRUCT "fun STRING c s = String.^(Char.toString c,s);")
::(EmitML.MLSTRUCT "val CONCAT = String.concat;")
::data@defs)

val _ = export_theory ();
