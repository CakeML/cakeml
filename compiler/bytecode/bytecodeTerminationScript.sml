open HolKernel Defn boolLib bossLib BytecodeTheory LabelsTheory lcsymtacs
val _ = new_theory"bytecodeTermination"

fun register name (def,ind) = let
  val _ = save_thm(name^"_def", def)
  val _ = save_thm(name^"_ind", ind)
  val _ = computeLib.add_persistent_funs [name^"_def"]
in (def,ind) end

val _ = save_thm ("bc_fetch_aux_def", bc_fetch_aux_def);
val _ = export_rewrites["bc_fetch_aux_def"];
val _ = save_thm("bc_fetch_def",bc_fetch_def);
val _ = save_thm("bump_pc_def",bump_pc_def);
val _ = save_thm("bc_find_loc_def",bc_find_loc_def);
val _ = save_thm("bc_find_loc_aux_def",bc_find_loc_aux_def);
val _ = save_thm("bc_next_rules",bc_next_rules);
val _ = save_thm("bc_next_ind",bc_next_ind);
val _ = save_thm("bc_next_cases",bc_next_cases);
val _ = save_thm("bc_stack_op_cases",bc_stack_op_cases);
val _ = save_thm("bc_stack_op_ind",bc_stack_op_ind);
val _ = save_thm("bool_to_tag_def",bool_to_tag_def);
val _ = save_thm("bool_to_val_def",bool_to_val_def);
val _ = save_thm("unit_tag_def",unit_tag_def);
val _ = save_thm("unit_val_def",unit_val_def);
val _ = save_thm("closure_tag_def",closure_tag_def);
val _ = save_thm("block_tag_def",block_tag_def);
val _ = save_thm("is_Label_def",is_Label_def);
val _ = export_rewrites["is_Label_def","bool_to_tag_def","bool_to_val_def",
                        "unit_tag_def","unit_val_def","closure_tag_def",
                        "block_tag_def"];
val _ = Parse.overload_on("next_addr", ``λil ls. SUM (MAP (SUC o il) (FILTER ($~ o is_Label) ls))``)

val _ = register "calculate_labels" (
  tprove_no_defn ((calculate_labels_def,calculate_labels_ind),
  WF_REL_TAC `measure (LENGTH o SND o SND o SND o SND)` >> rw[]))

val _ = register "replace_labels" (
  tprove_no_defn ((replace_labels_def,replace_labels_ind),
  WF_REL_TAC `measure (LENGTH o SND o SND)` >> rw[]))

val _ = register "bc_equal" (
  tprove_no_defn ((bc_equal_def,bc_equal_ind),
  WF_REL_TAC `measure (\x. case x of INL (v1,v2) => bc_value_size v1 | INR (vs1,vs2) => bc_value1_size vs1)`));

val _ = export_rewrites["CompilerLib.the_def","CompilerLib.fapply_def"]

val _ = export_theory()
