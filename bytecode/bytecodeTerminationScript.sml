open HolKernel Defn boolLib bossLib BytecodeTheory lcsymtacs
val _ = new_theory"bytecodeTermination"

fun register name (def,ind) = let
  val _ = save_thm(name^"_def", def)
  val _ = save_thm(name^"_ind", ind)
  val _ = computeLib.add_persistent_funs [name^"_def"]
in (def,ind) end

val _ = export_rewrites
["Bytecode.bc_fetch_aux_def","Bytecode.bool_to_tag_def","Bytecode.bool_to_val_def"
,"Bytecode.unit_tag_def","Bytecode.unit_val_def","Bytecode.closure_tag_def","Bytecode.block_tag_def"
,"Bytecode.is_Label_def","Bytecode.is_Block_def","Bytecode.bc_equality_result_to_val_def"
,"CompilerLib.the_def","CompilerLib.fapply_def"]

val _ = Parse.overload_on("next_addr", ``λil ls. SUM (MAP (SUC o il) (FILTER ($~ o is_Label) ls))``)

val _ = register "bc_equal" (
  tprove_no_defn ((bc_equal_def,bc_equal_ind),
  WF_REL_TAC `measure (\x. case x of INL (v1,v2) => bc_value_size v1 | INR (vs1,vs2) => bc_value1_size vs1)`));

val _ = export_theory()
