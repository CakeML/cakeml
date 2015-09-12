structure compilerComputeLib = struct
local

open HolKernel boolLib bossLib computeLib
open modLangTheory source_to_modTheory
open conLangTheory mod_to_conTheory
open decLangTheory con_to_decTheory
open exhLangTheory dec_to_exhTheory
open patLangTheory exh_to_patTheory
open closLangTheory pat_to_closTheory
open clos_mtiTheory
open clos_numberTheory
open clos_callTheory
open clos_annotateTheory
open bvlTheory clos_to_bvlTheory

open wordLangTheory
open stackLangTheory stack_removeTheory stack_namesTheory stack_to_labTheory stack_to_targetTheory
open labLangTheory lab_to_targetTheory

val SUC_TO_NUMERAL_RULE = CONV_RULE(!Defn.SUC_TO_NUMERAL_DEFN_CONV_hook)

fun add_compiler_compset compset = let
  fun add_datatype t = compute_basicLib.add_datatype t compset
  (* modLang *)
  val () = add_datatype ``:modLang$exp``
  val () = add_datatype ``:modLang$dec``
  val () = add_datatype ``:modLang$prompt``
  (* source_to_mod *)
  val () = add_thms
    [source_to_modTheory.compile_prog_def
    ,source_to_modTheory.compile_top_def
    ,source_to_modTheory.compile_decs_def
    ,source_to_modTheory.compile_dec_def
    ,source_to_modTheory.compile_exp_def
    ,source_to_modTheory.alloc_defs_def
    ,source_to_modTheory.Bool_def
    ] compset
  (* conLang *)
  val () = add_thms
    [bind_tag_def
    ,chr_tag_def
    ,div_tag_def
    ,eq_tag_def
    ,subscript_tag_def
    ,true_tag_def
    ,false_tag_def
    ,nil_tag_def
    ,cons_tag_def
    ,none_tag_def
    ,some_tag_def
    ] compset
  val () = add_datatype``:conLang$op``
  val () = add_datatype``:conLang$pat``
  val () = add_datatype``:conLang$exp``
  val () = add_datatype``:conLang$dec``
  val () = add_datatype``:conLang$prompt``
  (* mod_to_con *)
  val () = add_thms
    [mod_to_conTheory.compile_prog_def
    ,mod_to_conTheory.compile_prompt_def
    ,mod_to_conTheory.compile_decs_def
    ,mod_to_conTheory.compile_exp_def
    ,mod_to_conTheory.compile_pat_def
    ,mod_to_conTheory.lookup_tag_env_def
    ,mod_to_conTheory.lookup_tag_flat_def
    ,mod_to_conTheory.insert_tag_env_def
    ,mod_to_conTheory.mod_tagenv_def
    ,mod_to_conTheory.get_tagenv_def
    ,mod_to_conTheory.get_exh_def
    ,mod_to_conTheory.alloc_tag_def
    ,mod_to_conTheory.alloc_tags_def
    ] compset
  (* decLang *)
  (* con_to_dec *)
  val () = add_thms
    [con_to_decTheory.compile_prog_def
    ,con_to_decTheory.compile_prompt_def
    ,con_to_decTheory.init_globals_def
    ,con_to_decTheory.init_global_funs_def
    ,con_to_decTheory.compile_decs_def
    ] compset
  (* exhLang *)
  val () = add_datatype``:exhLang$pat``
  val () = add_datatype``:exhLang$exp``
  (* dec_to_exh *)
  val () = add_thms
    [dec_to_exhTheory.is_unconditional_def
    ,dec_to_exhTheory.add_default_def
    ,dec_to_exhTheory.get_tags_def
    ,dec_to_exhTheory.exhaustive_match_def
    ,dec_to_exhTheory.tuple_tag_def
    ,dec_to_exhTheory.compile_exp_def
    ,dec_to_exhTheory.compile_pat_def
    ] compset
  (* patLang *)
  val () = add_datatype``:patLang$exp``
  val () = add_datatype``:patLang$op``
  (* exh_to_pat *)
  val () = add_thms
    [exh_to_patTheory.compile_exp_def
    ,exh_to_patTheory.compile_row_def
    ,exh_to_patTheory.compile_pat_def
    ,exh_to_patTheory.sLet_def
    ,exh_to_patTheory.sIf_def
    ,exh_to_patTheory.ground_def
    ,exh_to_patTheory.pure_def
    ,SUC_TO_NUMERAL_RULE exh_to_patTheory.Let_Els_def
    ,exh_to_patTheory.pure_op_def
    ,exh_to_patTheory.pure_op_op_def
    ,exh_to_patTheory.Bool_def
    ] compset
  (* closLang *)
  val () = add_datatype``:closLang$exp``
  val () = add_datatype``:closLang$op``
  val () = add_thms [closLangTheory.max_app_def] compset
  (* pat_to_clos *)
  val () = add_thms
    [pat_to_closTheory.compile_def
    ,pat_to_closTheory.string_tag_def
    ,pat_to_closTheory.vector_tag_def
    (*,pat_to_closTheory.pat_tag_shift_def*)
    ] compset
  (* clos_mti *)
  val () = add_thms
    [clos_mtiTheory.intro_multi_def
    ,clos_mtiTheory.collect_args_def
    ] compset
  (* clos_number *)
  val () = add_thms
    [clos_numberTheory.renumber_code_locs_def]
    compset
  (* clos_call *)
  val () = add_datatype``:clos_call$val_approx``
  val () = add_thms
    [clos_callTheory.get_free_vars_def
    ,clos_callTheory.merge_def
    ,clos_callTheory.call_intro_def
    ,clos_callTheory.calls_def
    ,clos_callTheory.calls_body_def
    ,clos_callTheory.adjust_all_def
    ,clos_callTheory.calls_app_def
    ,clos_callTheory.Seq_def
    ,clos_callTheory.pure_def
    ,clos_callTheory.pure_op_def
    ,clos_callTheory.calls_op_def
    ,clos_callTheory.adjust_vars_def
    ,clos_callTheory.dest_Clos_def
    ] compset
  (* clos_annotate *)
  val () = add_thms
    [clos_annotateTheory.get_var_def
    ,clos_annotateTheory.new_env_def
    ,clos_annotateTheory.annotate_def
    ,clos_annotateTheory.shift_def
    ] compset
  (* bvl *)
  val () = add_datatype``:bvl$exp``
  (* clos_to_bvl *)

  (* wordLang*)
  val () = add_datatype``:'a wordLang$num_exp``
  val () = add_datatype``:'a wordLang$exp``
  val () = add_datatype``:'a wordLang$prog``
  
  (*stackLang*)
  val () = add_datatype``:'a stackLang$prog``

  (*stack_remove*)
  val () = add_thms
    [stack_removeTheory.compile_def,
    stack_removeTheory.prog_comp_def,
    stack_removeTheory.comp_def,
    stack_removeTheory.stack_err_lab_def,
    stack_removeTheory.store_length_def,
    stack_removeTheory.store_offset_def,
    stack_removeTheory.store_pos_def,
    stack_removeTheory.word_offset_def
    ] compset

  (*stack names*)
  val () = add_thms
    [stack_namesTheory.find_name_def,
    stack_namesTheory.inst_find_name_def,
    stack_namesTheory.compile_def,
    stack_namesTheory.prog_comp_def,
    stack_namesTheory.comp_def,
    stack_namesTheory.ri_find_name_def
    ] compset

  (*stack_to_lab*)
  val () = add_thms
    [stack_to_labTheory.max_lab_def,
    stack_to_labTheory.no_ret_def,
    stack_to_labTheory.compile_def,
    stack_to_labTheory.prog_to_section_def,
    stack_to_labTheory.flatten_def,
    stack_to_labTheory.compile_jump_def
    ] compset
 
  (*stack_to_target*)
  val () = add_thms
    [stack_to_targetTheory.move_inst_def,
    stack_to_targetTheory.stub1_def,
    stack_to_targetTheory.compile_def,
    stack_to_targetTheory.seq_list_def,
    stack_to_targetTheory.stub0_def,
    stack_to_targetTheory.sub_inst_def,
    stack_to_targetTheory.const_inst_def
    ] compset

  (*labLang*)
  val () = add_datatype``:lab``
  val () = add_datatype``:'a asm_with_lab``
  val () = add_datatype``:'a line``
  val () = add_datatype``:'a sec``

  (*lab_to_target*)
  val () = add_thms
    [lab_to_targetTheory.ffi_offset_def,
    lab_to_targetTheory.sec_lengths_update_def,
    lab_to_targetTheory.compile_def,
    lab_to_targetTheory.compile_lab_def,
    lab_to_targetTheory.prog_to_bytes_def,
    lab_to_targetTheory.line_bytes_def,
    lab_to_targetTheory.remove_labels_def,
    lab_to_targetTheory.remove_labels_loop_def,
    lab_to_targetTheory.filter_labs_def,
    lab_to_targetTheory.pad_code_def,
    lab_to_targetTheory.pad_section_def,
    lab_to_targetTheory.pad_bytes_def,
    lab_to_targetTheory.all_asm_ok_def,
    lab_to_targetTheory.sec_asm_ok_def,
    lab_to_targetTheory.all_lengths_update_def,
    lab_to_targetTheory.sec_length_def,
    lab_to_targetTheory.all_lengths_ok_def,
    lab_to_targetTheory.sec_lengths_ok_def,
    lab_to_targetTheory.enc_secs_again_def,
    lab_to_targetTheory.full_sec_length_def,
    lab_to_targetTheory.find_pos_def,
    lab_to_targetTheory.enc_line_again_def,
    lab_to_targetTheory.get_jump_offset_def,
    lab_to_targetTheory.get_label_def,
    lab_to_targetTheory.lab_inst_def,
    lab_to_targetTheory.compute_labels_def,
    lab_to_targetTheory.sec_labs_def,
    lab_to_targetTheory.asm_line_labs_def,
    lab_to_targetTheory.enc_sec_list_def,
    lab_to_targetTheory.enc_sec_def,
    lab_to_targetTheory.enc_line_def
    ] compset

in () end

in

val add_compiler_compset = add_compiler_compset

val the_compiler_compset =
  let
    val c = compute_basicLib.the_basic_compset
    (*Needs fixing val () = compute_semanticsLib.add_ast_compset c*)
    val () = add_compiler_compset c
  in
    c
  end

(*Testing*)
(*
val compset = the_compiler_compset
val eval = computeLib.CBV_CONV compset

val foo = eval`` stack_to_lab$compile [(0:num,Skip)]``
val foo2 = eval ``stack_to_target$compile (LN,1:num,2:num,c) [0,(Seq Skip (StackStore 5 3 ))]``
*)

end
end
