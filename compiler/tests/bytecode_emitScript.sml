open HolKernel bossLib boolLib EmitTeX basis_emitTheory
open CompilerLibTheory PrinterTheory BytecodeTheory bytecodeTerminationTheory bytecodeEvalTheory
open bytecodeLabelsTheory
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

val real_inst_length_def = zDefine `
  real_inst_length bc =
   case bc of
     Stack Pop => 0
   | Stack (Pops v25) => if v25 < 268435456 then 4 else 1
   | Stack (Shift v26 v27) =>
       if v26 + v27 < 268435456 then
         if v27 = 0 then 1
         else if v26 = 0 then 5
         else if v26 = 1 then 4
         else if v26 ≤ 1 + v27 then ((v26 − 1) * 10 + 16) DIV 2 − 1
         else (v26 * 10 + ((v26 − 1) * 10 + 20)) DIV 2 − 1
       else 1
   | Stack (PushInt v28) =>
       if v28 < 268435456 then if v28 < 0 then 1 else 4 else 1
   | Stack (Cons v29 v30) =>
       if v29 < 268435456 then
         if v30 = 0 then 4 else if v30 < 32768 then 34 else 1
       else 1
   | Stack (Load v31) => if v31 < 268435456 then 4 else 1
   | Stack (Store v32) => if v32 < 268435456 then 4 else 1
   | Stack (LoadRev v33) => 5
   | Stack (El v34) => if v34 < 268435456 then 6 else 1
   | Stack (TagEq v35) => if v35 < 268435456 then 28 else 1
   | Stack IsBlock => 25
   | Stack Equal => 5
   | Stack Add => 3
   | Stack Sub => 3
   | Stack Mult => 8
   | Stack Div => 11
   | Stack Mod => 11
   | Stack Less => 11
   | Label l => 0
   | Jump _ => 2
   | JumpIf _ => 5
   | Call _ => 2
   | CallPtr => 3
   | PushPtr _ => 7
   | Return => 0
   | PushExc => 3
   | PopExc => 5
   | Ref => 23
   | Deref => 1
   | Update => 3
   | Stop => 9
   | Tick => 1
   | Print => 5
   | PrintC v13 => 25`

val () = ([],``!bc. x = real_inst_length bc``)
  |> (Cases THEN TRY (Cases_on `b`)) |> fst |> map (rand o snd)
  |> map (REWRITE_CONV [real_inst_length_def] THENC EVAL)
  |> computeLib.add_funs

val real_inst_length_ok = store_thm("real_inst_length_ok",
  ``length_ok real_inst_length``,
  EVAL_TAC \\ SIMP_TAC std_ss []);

val real_init_bc_state_def =  Define`
  real_init_bc_state = <|
    stack := [];
    code := [];
    pc := 0;
    refs := FEMPTY;
    handler := 0;
    output := "";
    cons_names := [];
    inst_length := real_inst_length;
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
bool_to_val_def,unit_val_def,
bc_equality_result_to_val_def,
bv_to_ov_def,
bc_equal_def,
bc_eval_stack_def,
CONCAT_RULE(CONV_RULE(PURE_REWRITE_CONV[mk_thm([],mk_eq(``CONS:char -> string -> string``,``STRING``))]) bc_eval1_def),
bc_eval_compute,
real_inst_length_def,
real_init_bc_state_def,
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
