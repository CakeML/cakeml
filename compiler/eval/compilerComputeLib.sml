structure compilerComputeLib :> compilerComputeLib =
struct

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
open clos_freeTheory
open clos_removeTheory
open clos_knownTheory
open bvlTheory clos_to_bvlTheory
open bviTheory bvl_to_bviTheory bvl_inlineTheory bvl_constTheory bvl_handleTheory bvl_jumpTheory
open dataLangTheory bvi_to_dataTheory data_simpTheory data_liveTheory data_spaceTheory
open wordLangTheory data_to_wordTheory word_instTheory word_allocTheory word_removeTheory
open stackLangTheory word_to_wordTheory word_to_stackTheory stack_removeTheory stack_namesTheory db_varsTheory
open labLangTheory stack_to_labTheory lab_filterTheory
open backendTheory
open semanticsComputeLib reg_allocComputeLib

(*Order of thms shown below:
First, all the small compilation steps between ILs + IL to IL transforms

src -> mod -> con -> dec -> exh -> pat -> clos -> bvl -> data -> word
-> stack -> lab -> target

Then all the _to_target scripts linking things up
lab -> stack -> word -> ...

*)

in

val add_compiler_compset = computeLib.extend_compset
  [computeLib.Tys
    [ (* ---- configurations ---- *)
     ``:source_to_mod$config``
    ,``:mod_to_con$config``
    ,``:clos_to_bvl$config``
    ,``:bvl_to_bvi$config``
    ,``:data_to_word$config``
    ,``:word_to_word$config``
    ,``:'a word_to_stack$config``
    ,``:stack_to_lab$config``
    ,``:'a lab_to_target$config``
    ,``:'a asm_config``
    ,``:'a backend$config``
      (* modLang *)
    ,``:modLang$exp``
    ,``:modLang$dec``
    ,``:modLang$prompt``
    ]
  (* TODO: move (to basicCompute or HOL) *)
  ,computeLib.Defs
    [ (* ---- source_to_mod ---- *)
     source_to_modTheory.compile_prog_def
    ,source_to_modTheory.compile_top_def
    ,source_to_modTheory.compile_decs_def
    ,source_to_modTheory.compile_dec_def
    ,source_to_modTheory.compile_exp_def
    ,source_to_modTheory.alloc_defs_def
    ,source_to_modTheory.Bool_def
    ,source_to_modTheory.compile_def
    ,source_to_modTheory.empty_config_def
      (* ---- conLang ---- *)
    ,prim_tagsTheory.bind_tag_def
    ,prim_tagsTheory.chr_tag_def
    ,prim_tagsTheory.div_tag_def
    ,prim_tagsTheory.subscript_tag_def
    ,prim_tagsTheory.true_tag_def
    ,prim_tagsTheory.false_tag_def
    ,prim_tagsTheory.nil_tag_def
    ,prim_tagsTheory.cons_tag_def
    ,prim_tagsTheory.none_tag_def
    ,prim_tagsTheory.some_tag_def
    ,conLangTheory.num_defs_def
    ]
  ,computeLib.Tys
    [``:conLang$op``
    ,``:conLang$pat``
    ,``:conLang$exp``
    ,``:conLang$dec``
    ,``:conLang$prompt``
    ]
  ,computeLib.Defs
    [ (* ---- mod_to_con ---- *)
     mod_to_conTheory.compile_prog_def
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
    ,mod_to_conTheory.compile_def
    ,mod_to_conTheory.empty_config_def
      (* decLang *)
      (* ---- con_to_dec ---- *)
    ,con_to_decTheory.compile_prog_def
    ,con_to_decTheory.compile_prompt_def
    ,con_to_decTheory.init_globals_def
    ,con_to_decTheory.init_global_funs_def
    ,con_to_decTheory.compile_decs_def
    ,con_to_decTheory.compile_def
    ]
  ,computeLib.Tys
    [ (* ---- exhLang ---- *)
     ``:exhLang$pat``
    ,``:exhLang$exp``
    ]
  ,computeLib.Defs
    [ (* ---- dec_to_exh ---- *)
     dec_to_exhTheory.is_unconditional_def
    ,dec_to_exhTheory.add_default_def
    ,dec_to_exhTheory.get_tags_def
    ,dec_to_exhTheory.exhaustive_match_def
    ,dec_to_exhTheory.tuple_tag_def
    ,dec_to_exhTheory.compile_exp_def
    ,dec_to_exhTheory.compile_pat_def
    ]
  ,computeLib.Tys
    [ (* ---- patLang ---- *)
     ``:patLang$exp``
    ,``:patLang$op``
    ]
      (* ---- exh_to_pat ---- *)
  ,computeLib.Defs
    [exh_to_patTheory.compile_exp_def
    ,exh_to_patTheory.compile_row_def
    ,exh_to_patTheory.compile_pat_def
    ,exh_to_patTheory.sLet_def
    ,exh_to_patTheory.sIf_def
    ,exh_to_patTheory.ground_def
    ,exh_to_patTheory.pure_def
    ,numLib.SUC_RULE exh_to_patTheory.Let_Els_def
    ,exh_to_patTheory.pure_op_def
    ,exh_to_patTheory.pure_op_op_eqn
    ,exh_to_patTheory.Bool_def
    ,exh_to_patTheory.compile_def
    ]
  ,computeLib.Tys
    [ (* ---- closLang ---- *)
     ``:closLang$exp``
    ,``:closLang$op``
    ,``:clos_known$val_approx``
    ]
  ,computeLib.Defs
    [closLangTheory.pure_def
    ,closLangTheory.pure_op_def
      (* ---- pat_to_clos ---- *)
    ,pat_to_closTheory.compile_def
    ,pat_to_closTheory.string_tag_def
    ,pat_to_closTheory.vector_tag_def
    ,pat_to_closTheory.compile_def
      (*,pat_to_closTheory.pat_tag_shift_def*)
      (* ---- clos_mti ---- *)
    ,clos_mtiTheory.intro_multi_def
    ,clos_mtiTheory.collect_args_def
    ,clos_mtiTheory.collect_apps_def
    ,clos_mtiTheory.compile_def
      (* ---- clos_number ---- *)
    ,clos_numberTheory.renumber_code_locs_def
    ]
  ,computeLib.Defs
    [clos_callTheory.calls_def
    ,clos_callTheory.closed_def
    ,clos_callTheory.code_list_def
    ,clos_callTheory.compile_def
    ,clos_callTheory.calls_def
    ,clos_callTheory.calls_list_def
    ,clos_callTheory.insert_each_def_compute
      (* ---- clos_annotate ---- *)
    ,clos_annotateTheory.get_var_def
    ,clos_annotateTheory.shifted_env_def
    ,clos_annotateTheory.annotate_def
    ,clos_annotateTheory.shift_def
    ,clos_annotateTheory.compile_def
      (* ---- clos_free----  *)
    ,clos_freeTheory.free_def
      (* ---- clos_remove ---- *)
    ,clos_removeTheory.no_overlap_def
    ,clos_removeTheory.no_overlap_def_compute
    ,clos_removeTheory.remove_def
    ,clos_removeTheory.const_0_def
    ,clos_removeTheory.compile_def
      (* ---- clos_known---- *)
    ,clos_knownTheory.merge_def
    ,clos_knownTheory.compile_def
    ,clos_knownTheory.dest_Clos_def
    ,clos_knownTheory.known_def
    ,clos_knownTheory.known_op_def
    ,clos_knownTheory.clos_gen_def
    ]
  ,computeLib.Tys
    [ (* ---- bvl ---- *)
     ``:bvl$exp``
    ]
  ,computeLib.Defs
    [ (* ---- clos_to_bvl ---- *)
     clos_to_bvlTheory.closure_tag_def
    ,clos_to_bvlTheory.recc_Let0_def
    ,clos_to_bvlTheory.default_config_def
    ,clos_to_bvlTheory.compile_def
    ,clos_to_bvlTheory.compile_prog_def
    ,clos_to_bvlTheory.init_code_def
    ,clos_to_bvlTheory.block_equality_code_def
    ,clos_to_bvlTheory.equality_code_def
    ,clos_to_bvlTheory.check_closure_def
    ,clos_to_bvlTheory.ToList_code_def
    ,clos_to_bvlTheory.generate_partial_app_closure_fn_def
    ,clos_to_bvlTheory.generate_generic_app_def
    ,bvlTheory.mk_tick_def
    ,clos_to_bvlTheory.partial_app_fn_location_def
    ,clos_to_bvlTheory.mk_cl_call_def
    ,clos_to_bvlTheory.ToList_location_def
    ,clos_to_bvlTheory.block_equality_location_def
    ,clos_to_bvlTheory.equality_location_def
    ,clos_to_bvlTheory.num_stubs_def
    ,clos_to_bvlTheory.build_recc_lets_def
    ,clos_to_bvlTheory.recc_Let_def
    ,clos_to_bvlTheory.recc_Lets_def
    ,clos_to_bvlTheory.mk_el_def
    ,clos_to_bvlTheory.build_aux_def
    ,clos_to_bvlTheory.code_for_recc_case_def
    ,clos_to_bvlTheory.free_let_def
    ,clos_to_bvlTheory.mk_label_def
    ,clos_to_bvlTheory.compile_op_def
    ,clos_to_bvlTheory.mk_const_def
    ,clos_to_bvlTheory.partial_app_tag_def
    ,bvlTheory.Bool_def
    ,prim_tagsTheory.bool_to_tag_def
    ,clos_to_bvlTheory.clos_tag_shift_def
    ,clos_to_bvlTheory.compile_exps_def
    ,clos_to_bvlTheory.code_merge_def
    ,clos_to_bvlTheory.code_split_def
    ,clos_to_bvlTheory.code_sort_def
      (* ---- bvl_inline ---- *)
    ,bvl_inlineTheory.inline_def
    ,bvl_inlineTheory.is_small_aux_def
    ,bvl_inlineTheory.is_small_def
    ,bvl_inlineTheory.is_rec_def
    ,bvl_inlineTheory.must_inline_def
    ,bvl_inlineTheory.inline_all_def
    ,bvl_inlineTheory.compile_prog_def
      (* ---- bvl_const ---- *)
    ,bvl_constTheory.SmartOp_def
    ,bvl_constTheory.compile_exp_def
    ,bvl_constTheory.extract_list_def
    ,bvl_constTheory.compile_def
    ,bvl_constTheory.delete_var_def
    ,bvl_constTheory.dest_Op_Const_def
    ,bvl_constTheory.extract_def
    ,bvl_constTheory.getConst_def
    ,bvl_constTheory.isConst_def
    ,bvl_constTheory.is_simple_def
      (* ---- bvl_handle ---- *)
    ,bvl_handleTheory.LetLet_def
    ,bvl_handleTheory.SmartLet_def
    ,bvl_handleTheory.OptionalLetLet_def
    ,bvl_handleTheory.compile_def
    ,bvl_handleTheory.compile_exp_def
    ,bvl_handleTheory.dest_Seq_def
    ,bvl_handleTheory.compile_seqs_compute
    ,bvl_handleTheory.compile_any_def
      (* ---- bvl_jump ---- *)
    ,bvl_jumpTheory.JumpList_def
    ,bvl_jumpTheory.Jump_def
    ]
  ,computeLib.Tys
    [ (* ---- bvi ---- *)
     ``:bvi$exp``
    ]
  ,computeLib.Defs
    [ (* ---- bvl_to_bvi ---- *)
     bvl_to_bviTheory.destLet_def
    ,bvl_to_bviTheory.alloc_glob_count_def
    ,bvl_to_bviTheory.num_stubs_def
    ,bvl_to_bviTheory.compile_prog_def
    ,bvl_to_bviTheory.compile_list_def
    ,bvl_to_bviTheory.compile_single_def
    ,bvl_to_bviTheory.compile_def
    ,bvl_to_bviTheory.compile_op_def
    ,bvl_to_bviTheory.stubs_def
    ,bvl_to_bviTheory.num_stubs_def
    ,bvl_to_bviTheory.CopyGlobals_code_def
    ,bvl_to_bviTheory.AllocGlobal_code_def
    ,bvl_to_bviTheory.InitGlobals_code_def
    ,bvl_to_bviTheory.ListLength_code_def
    ,bvl_to_bviTheory.CopyGlobals_location_eq
    ,bvl_to_bviTheory.AllocGlobal_location_eq
    ,bvl_to_bviTheory.InitGlobals_max_def
    ,bvl_to_bviTheory.InitGlobals_location_eq
    ,bvl_to_bviTheory.ListLength_location_eq
    ,bvl_to_bviTheory.compile_int_def
    ,bvl_to_bviTheory.compile_exps_def
    ,bvl_to_bviTheory.compile_aux_def
    ,bvl_to_bviTheory.optimise_def
    ,bvl_to_bviTheory.default_config_def
      (* ---- bvi_let ---- *)
    ,bvi_letTheory.extract_def
    ,bvi_letTheory.extract_list_def
    ,bvi_letTheory.delete_var_def
    ,bvi_letTheory.compile_def
    ,bvi_letTheory.compile_exp_def
    ]
  ,computeLib.Tys
    [ (* ---- data ---- *)
     ``:dataLang$prog``
      (* ---- data_to_word ---- *)
    ,``:data_to_word$word_op_type``
    ]
  ,computeLib.Defs
    [dataLangTheory.mk_ticks_def
    ,dataLangTheory.num_stubs_def
      (* ---- bvi_to_data ---- *)
    ,bvi_to_dataTheory.op_space_reset_def
    ,bvi_to_dataTheory.op_requires_names_eqn
    ,bvi_to_dataTheory.optimise_def
    ,bvi_to_dataTheory.compile_prog_def
    ,bvi_to_dataTheory.compile_part_def
    ,bvi_to_dataTheory.compile_exp_def
    ,bvi_to_dataTheory.compile_def
    ,bvi_to_dataTheory.iAssign_def
      (* ---- data_simp ---- *)
    ,data_simpTheory.pSeq_def
    ,data_simpTheory.simp_def
      (* ---- data_space ---- *)
    ,data_spaceTheory.pMakeSpace_def
    ,data_spaceTheory.space_def
    ,data_spaceTheory.op_space_req_def
    ,data_spaceTheory.compile_def
      (* ---- data_live ---- *)
    ,data_liveTheory.is_pure_def
    ,data_liveTheory.compile_def
    ]
  ,computeLib.Tys
    [ (* wordLang *)
     ``:'a wordLang$num_exp``
    ,``:'a wordLang$exp``
    ,``:'a wordLang$prog``
    ]
  ,computeLib.Defs
    [wordLangTheory.every_var_exp_def
    ,wordLangTheory.num_exp_def
    ,wordLangTheory.word_op_def
    ,wordLangTheory.every_var_imm_def
    ,wordLangTheory.every_stack_var_def
    ,wordLangTheory.every_var_def
    ,wordLangTheory.every_name_def
    ,wordLangTheory.every_var_inst_def
    ,wordLangTheory.num_stubs_def
    ,wordLangTheory.raise_stub_location_eq
      (* ---- data_to_word ---- *)
    ,data_to_wordTheory.adjust_var_def
    ,data_to_wordTheory.adjust_set_def
    ,data_to_wordTheory.Unit_def
    ,data_to_wordTheory.GiveUp_def
    ,data_to_wordTheory.make_header_def
    ,data_to_wordTheory.tag_mask_def
    ,data_to_wordTheory.encode_header_def
    ,data_to_wordTheory.list_Seq_def
    ,data_to_wordTheory.shift_def
    ,data_to_wordTheory.StoreEach_def
    ,data_to_wordTheory.shift_length_def
    ,data_to_wordTheory.max_heap_limit_def
    ,data_to_wordTheory.all_ones_def
    ,data_to_wordTheory.maxout_bits_def
    ,data_to_wordTheory.ptr_bits_def
    ,data_to_wordTheory.real_addr_def
    ,data_to_wordTheory.real_offset_def
    ,data_to_wordTheory.real_byte_offset_def
    ,data_to_wordTheory.lookup_word_op_def
    ,data_to_wordTheory.FromList_location_eq
    ,data_to_wordTheory.FromList1_location_eq
    ,data_to_wordTheory.RefByte_location_eq
    ,data_to_wordTheory.RefArray_location_eq
    ,data_to_wordTheory.Replicate_location_eq
    ,data_to_wordTheory.AllocVar_def
    ,data_to_wordTheory.MakeBytes_def
    ,data_to_wordTheory.SmallLsr_def
    ,data_to_wordTheory.RefByte_code_def
    ,data_to_wordTheory.FromList_code_def
    ,data_to_wordTheory.FromList1_code_def
    ,data_to_wordTheory.RefArray_code_def
    ,data_to_wordTheory.Replicate_code_def
    ,data_to_wordTheory.get_names_def
    ,data_to_wordTheory.assign_def
    ,data_to_wordTheory.comp_def
    ,data_to_wordTheory.compile_part_def
    ,data_to_wordTheory.stubs_def
    ,data_to_wordTheory.compile_def
      (* ---- wordLang word_to_word ---- *)
    ,word_to_wordTheory.compile_single_def
    ,word_to_wordTheory.full_compile_single_def
    ,word_to_wordTheory.next_n_oracle_def
    ,word_to_wordTheory.compile_def
      (* ---- wordLang word_simp ---- *)
    ,word_simpTheory.SmartSeq_def
    ,word_simpTheory.Seq_assoc_def
    ,word_simpTheory.dest_Seq_def
    ,word_simpTheory.dest_If_def
    ,word_simpTheory.dest_If_Eq_Imm_def
    ,word_simpTheory.dest_Seq_Assign_Const_def
    ,word_simpTheory.apply_if_opt_def
    ,word_simpTheory.simp_if_def
    ,word_simpTheory.compile_exp_def
      (* ---- wordLang remove must terminate ---- *)
    ,word_removeTheory.remove_must_terminate_def
      (* ---- wordLang inst_select and inst flattening ---- *)
    ,word_instTheory.three_to_two_reg_def
    ,word_instTheory.pull_exp_def
    ,word_instTheory.inst_select_def
    ,word_instTheory.inst_select_exp_def
    ,word_instTheory.flatten_exp_def
    ,word_instTheory.op_consts_def
    ,word_instTheory.optimize_consts_def
    ,word_instTheory.pull_ops_def
    ,word_instTheory.convert_sub_def
    ,word_instTheory.rm_const_def
    ,word_instTheory.is_const_def
      (* ---- wordLang ssa form and interface to reg allocator ---- *)
    ,word_allocTheory.big_union_def
    ,word_allocTheory.word_alloc_def
    ,word_allocTheory.full_ssa_cc_trans_def
    ,word_allocTheory.limit_var_def
    ,word_allocTheory.max_var_def
    ,word_allocTheory.max_var_inst_def
    ,word_allocTheory.max_var_exp_def
    ,word_allocTheory.max3_def
    ,word_allocTheory.setup_ssa_def
    ,word_allocTheory.oracle_colour_ok_def
    ,word_allocTheory.every_even_colour_def
    ,word_allocTheory.check_colouring_ok_alt_def
    ,word_allocTheory.get_prefs_def
    ,word_allocTheory.get_clash_tree_def
    ,word_allocTheory.get_reads_exp_def
    ,word_allocTheory.get_delta_inst_def
    ,word_allocTheory.ssa_cc_trans_def
    ,word_allocTheory.get_live_def
    ,word_allocTheory.numset_list_insert_def
    ,word_allocTheory.get_live_exp_def
    ,word_allocTheory.get_live_inst_def
    ,word_allocTheory.apply_colour_def
    ,word_allocTheory.apply_colour_inst_def
    ,word_allocTheory.apply_colour_imm_def
    ,word_allocTheory.apply_colour_exp_def
    ,word_allocTheory.ssa_cc_trans_exp_def
    ,word_allocTheory.list_next_var_rename_move_def
    ,word_allocTheory.ssa_cc_trans_inst_def
    ,word_allocTheory.fix_inconsistencies_def
    ,word_allocTheory.fake_moves_def
    ,word_allocTheory.merge_moves_def
    ,word_allocTheory.fake_move_def
    ,word_allocTheory.list_next_var_rename_def
    ,word_allocTheory.next_var_rename_def
    ,word_allocTheory.even_list_def
    ,word_allocTheory.option_lookup_def
    ,word_allocTheory.apply_nummap_key_def
    ,word_allocTheory.remove_dead_def
    ,word_allocTheory.remove_dead_inst_def
    ]
  ,computeLib.Tys
    [ (* ---- stackLang ---- *)
     ``:'a stackLang$prog``
    ,``:stackLang$store_name``
    ]
  ,computeLib.Defs
    [stackLangTheory.list_Seq_def
    ,stackLangTheory.word_shift_def
    ,stackLangTheory.num_stubs_def
    ,stackLangTheory.gc_stub_location_eq
      (* ---- word_to_stack ---- *)
    ,word_to_stackTheory.wReg1_def
    ,word_to_stackTheory.wReg2_def
    ,word_to_stackTheory.wRegImm2_def
    ,word_to_stackTheory.wRegWrite1_def
    ,word_to_stackTheory.wStackLoad_def
    ,word_to_stackTheory.wStackStore_def
    ,word_to_stackTheory.wMoveSingle_def
    ,word_to_stackTheory.wMoveAux_def
    ,word_to_stackTheory.format_var_def
    ,word_to_stackTheory.wMove_def
    ,word_to_stackTheory.wInst_def
    ,word_to_stackTheory.bits_to_word_def
    ,word_to_stackTheory.word_list_def
    ,word_to_stackTheory.write_bitmap_def
    ,word_to_stackTheory.insert_bitmap_def
    ,word_to_stackTheory.wLive_def
    ,word_to_stackTheory.SeqStackFree_def
    ,word_to_stackTheory.stack_arg_count_def
    ,word_to_stackTheory.stack_free_def
    ,word_to_stackTheory.stack_move_def_compute
    ,word_to_stackTheory.StackArgs_def
    ,word_to_stackTheory.comp_def
    ,word_to_stackTheory.raise_stub_def
    ,word_to_stackTheory.compile_prog_def
    ,word_to_stackTheory.compile_word_to_stack_def
    ,word_to_stackTheory.compile_def
    ,word_to_stackTheory.call_dest_def
    ,word_to_stackTheory.StackHandlerArgs_def
    ,word_to_stackTheory.PopHandler_def
    ,word_to_stackTheory.PushHandler_def
      (* ---- stack_alloc ---- *)
    ,stack_allocTheory.memcpy_code_def
    ,stack_allocTheory.word_gc_move_loop_code_def
    ,stack_allocTheory.compile_def
    ,stack_allocTheory.prog_comp_def
    ,stack_allocTheory.comp_def
    ,stack_allocTheory.next_lab_def
    ,stack_allocTheory.stubs_def
    ,stack_allocTheory.word_gc_code_def
    ,stack_allocTheory.word_gc_move_roots_bitmaps_code_def
    ,stack_allocTheory.word_gc_move_bitmaps_code_def
    ,stack_allocTheory.word_gc_move_bitmap_code_def
    ,stack_allocTheory.word_gc_move_code_def
    ,stack_allocTheory.word_gc_move_list_code_def
    ,stack_allocTheory.clear_top_inst_def
      (* ---- stack_remove ---- *)
    ,stack_removeTheory.max_stack_alloc_def
    ,stack_removeTheory.word_offset_def
    ,stack_removeTheory.store_list_def
    ,stack_removeTheory.store_pos_def
    ,stack_removeTheory.store_length_def
    ,stack_removeTheory.store_offset_def
    ,stack_removeTheory.stack_err_lab_def
    ,stack_removeTheory.single_stack_alloc_def
    ,stack_removeTheory.stack_alloc_def
    ,stack_removeTheory.comp_def
    ,stack_removeTheory.prog_comp_def
    ,stack_removeTheory.halt_inst_def
    ,stack_removeTheory.store_list_code_def
    ,stack_removeTheory.init_memory_def
    ,stack_removeTheory.store_init_def
    ,stack_removeTheory.init_code_def
    ,stack_removeTheory.init_stubs_def
    ,stack_removeTheory.compile_def
    ]
  ,computeLib.Tys
    [ (* ---- db_vars ---- *)
     ``:db_var_set``
    ]
  ,computeLib.Defs
    [db_varsTheory.mk_Union_def
    ,db_varsTheory.vars_to_list_def
    ,db_varsTheory.vars_from_list_def
    ,db_varsTheory.vars_flatten_def
    ,db_varsTheory.has_var_def
    ,db_varsTheory.db_to_set_acc_def
    ,db_varsTheory.db_to_set_def
    ,db_varsTheory.list_mk_Union_def
      (* ---- stack names ---- *)
    ,stack_namesTheory.find_name_def
    ,stack_namesTheory.ri_find_name_def
    ,stack_namesTheory.inst_find_name_def
    ,stack_namesTheory.dest_find_name_def
    ,stack_namesTheory.comp_def
    ,stack_namesTheory.prog_comp_def
    ,stack_namesTheory.compile_def
    ,stack_namesTheory.x64_names_def
    ,stack_namesTheory.arm_names_def
    ,stack_namesTheory.arm8_names_def
    ,stack_namesTheory.mips_names_def
    ,stack_namesTheory.riscv_names_def
      (* ---- stack_to_lab ---- *)
    ,stack_to_labTheory.no_ret_def
    ,stack_to_labTheory.compile_jump_def
    ,stack_to_labTheory.negate_def
    ,stack_to_labTheory.flatten_def
    ,stack_to_labTheory.prog_to_section_def
    ,stack_to_labTheory.compile_def
    ]
  ,computeLib.Tys
    [ (* ---- labLang ---- *)
     ``:lab``
    ,``:'a asm_with_lab``
    ,``:'a line``
    ,``:'a sec``
    ]
  ,computeLib.Defs
    [ (* ---- lab_filter ---- *)
     lab_filterTheory.not_skip_def
    ,lab_filterTheory.filter_skip_def
      (* ---- lab_to_target ---- *)
    ,lab_to_targetTheory.ffi_offset_def
    ,lab_to_targetTheory.sec_length_def
    ,lab_to_targetTheory.lab_inst_def
    ,lab_to_targetTheory.enc_line_def
    ,lab_to_targetTheory.enc_sec_def
    ,lab_to_targetTheory.enc_sec_list_def
    ,lab_to_targetTheory.asm_line_labs_def
    ,lab_to_targetTheory.sec_labs_def
    ,lab_to_targetTheory.lab_insert_def
    ,lab_to_targetTheory.section_labels_def
    ,lab_to_targetTheory.compute_labels_alt_def
    ,lab_to_targetTheory.find_pos_def
    ,lab_to_targetTheory.get_label_def
    ,lab_to_targetTheory.get_jump_offset_def
    ,lab_to_targetTheory.enc_lines_again_def
    ,lab_to_targetTheory.enc_secs_again_def
    ,lab_to_targetTheory.lines_upd_lab_len_def
    ,lab_to_targetTheory.upd_lab_len_def
    ,lab_to_targetTheory.lab_lookup_def
    ,lab_to_targetTheory.line_length_def
    ,lab_to_targetTheory.line_ok_light_def
    ,lab_to_targetTheory.sec_ok_light_def
    ,lab_to_targetTheory.pad_bytes_def
    ,lab_to_targetTheory.add_nop_def
    ,lab_to_targetTheory.pad_section_def
    ,lab_to_targetTheory.pad_code_def
    ,lab_to_targetTheory.loc_to_pc_comp_def
    ,lab_to_targetTheory.is_Label_def
    ,lab_to_targetTheory.check_lab_def
    ,lab_to_targetTheory.all_labels_def
    ,lab_to_targetTheory.sec_names_def
    ,lab_to_targetTheory.remove_labels_loop_def
    ,lab_to_targetTheory.remove_labels_def
    ,lab_to_targetTheory.line_bytes_def
    ,lab_to_targetTheory.prog_to_bytes_def
    ,lab_to_targetTheory.find_ffi_index_limit_def
    ,lab_to_targetTheory.compile_lab_def
    ,lab_to_targetTheory.compile_def
      (* ---- Everything in backend theory ---- *)
    ,backendTheory.to_mod_def
    ,backendTheory.to_target_def
    ,backendTheory.from_source_def
    ,backendTheory.from_mod_def
    ,backendTheory.from_con_def
    ,backendTheory.from_dec_def
    ,backendTheory.from_exh_def
    ,backendTheory.from_pat_def
    ,backendTheory.from_clos_def
    ,backendTheory.from_bvl_def
    ,backendTheory.from_bvi_def
    ,backendTheory.from_data_def
    ,backendTheory.from_word_def
    ,backendTheory.from_stack_def
    ,backendTheory.from_lab_def
    ,backendTheory.compile_def
    ,backendTheory.to_pat_def
    ,backendTheory.to_lab_def
    ,backendTheory.to_stack_def
    ,backendTheory.to_word_def
    ,backendTheory.to_data_def
    ,backendTheory.to_bvi_def
    ,backendTheory.to_bvl_def
    ,backendTheory.to_clos_def
    ,backendTheory.to_exh_def
    ,backendTheory.to_con_def
    ,backendTheory.to_dec_def
    ,backendTheory.to_livesets_def
    ,backendTheory.from_livesets_def
    ,backendTheory.prim_config_def
    ]
  ,computeLib.Tys
    [ (*asm -- 'a should be 64*)
     ``:'a asm_config``
    ,``:'a reg_imm``
    ,``:binop``
    ,``:cmp``
    ,``:shift``
    ,``:'a arith``
    ,``:'a addr``
    ,``:mem_op``
    ,``:'a inst``
    ,``:'a asm``
    ]
  ,computeLib.Extenders
    [basicComputeLib.add_basic_compset
    ,semanticsComputeLib.add_ast_compset
    ,reg_allocComputeLib.add_reg_alloc_compset
    ]
  ]

end

end
