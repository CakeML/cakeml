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
open bvlTheory clos_to_bvlTheory
open bviTheory bvl_to_bviTheory bvl_inlineTheory bvl_constTheory bvl_handleTheory bvl_jumpTheory
open bvpTheory bvi_to_bvpTheory bvp_simpTheory bvp_liveTheory bvp_spaceTheory
open parmoveTheory reg_allocTheory state_transformerTheory
open wordLangTheory bvp_to_wordTheory word_instTheory word_allocTheory
open stackLangTheory word_to_stackTheory stack_removeTheory stack_namesTheory db_varsTheory
open labLangTheory stack_to_labTheory lab_filterTheory
open backendTheory
open compute_semanticsLib

(*Order of thms shown below:
First, all the small compilation steps between ILs + IL to IL transforms

src -> mod -> con -> dec -> exh -> pat -> clos -> bvl -> bvp -> word
-> stack -> lab -> target

Then all the _to_target scripts linking things up
lab -> stack -> word -> ...

*)

in

fun add_compiler_compset compset =
let
  val add_datatype = compute_basicLib.add_datatype compset
  val add_thms = Lib.C computeLib.add_thms compset
in
  (*configurations*)
    add_datatype``:source_to_mod$config``;
    add_datatype``:mod_to_con$config``;
    add_datatype``:clos_to_bvl$config``;
    add_datatype``:bvp_to_word$config``;
    add_datatype``:word_to_stack$config``;
    add_datatype``:stack_to_lab$config``;
    add_datatype``:'a lab_to_target$config``;
    add_datatype``:'a asm_config``;
    add_datatype``:'a backend$config``;

  (* modLang *)
    add_datatype ``:modLang$exp``
  ; add_datatype ``:modLang$dec``
  ; add_datatype ``:modLang$prompt``
  (* source_to_mod *)
  ; add_thms
    [source_to_modTheory.compile_prog_def
    ,source_to_modTheory.compile_top_def
    ,source_to_modTheory.compile_decs_def
    ,source_to_modTheory.compile_dec_def
    ,source_to_modTheory.compile_exp_def
    ,source_to_modTheory.alloc_defs_def
    ,source_to_modTheory.Bool_def
    ,source_to_modTheory.compile_def
    ]

  (* conLang *)
  ; add_thms
    [conLangTheory.bind_tag_def
    ,conLangTheory.chr_tag_def
    ,conLangTheory.div_tag_def
    ,conLangTheory.eq_tag_def
    ,conLangTheory.subscript_tag_def
    ,conLangTheory.true_tag_def
    ,conLangTheory.false_tag_def
    ,conLangTheory.nil_tag_def
    ,conLangTheory.cons_tag_def
    ,conLangTheory.none_tag_def
    ,conLangTheory.some_tag_def
    ,conLangTheory.num_defs_def
    ]
  ; add_datatype``:conLang$op``
  ; add_datatype``:conLang$pat``
  ; add_datatype``:conLang$exp``
  ; add_datatype``:conLang$dec``
  ; add_datatype``:conLang$prompt``
  (* mod_to_con *)
  ; add_thms
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
    ,mod_to_conTheory.compile_def
    ]

  (* decLang *)
  (* con_to_dec *)
  ; add_thms
    [con_to_decTheory.compile_prog_def
    ,con_to_decTheory.compile_prompt_def
    ,con_to_decTheory.init_globals_def
    ,con_to_decTheory.init_global_funs_def
    ,con_to_decTheory.compile_decs_def
    ,con_to_decTheory.compile_def
    ]

  (* exhLang *)
  ; add_datatype``:exhLang$pat``
  ; add_datatype``:exhLang$exp``
  (* dec_to_exh *)
  ; add_thms
    [dec_to_exhTheory.is_unconditional_def
    ,dec_to_exhTheory.add_default_def
    ,dec_to_exhTheory.get_tags_def
    ,dec_to_exhTheory.exhaustive_match_def
    ,dec_to_exhTheory.tuple_tag_def
    ,dec_to_exhTheory.compile_exp_def
    ,dec_to_exhTheory.compile_pat_def
    ]

  (* patLang *)
  ; add_datatype``:patLang$exp``
  ; add_datatype``:patLang$op``
  (* exh_to_pat *)
  ; add_thms
    [exh_to_patTheory.compile_exp_def
    ,exh_to_patTheory.compile_row_def
    ,exh_to_patTheory.compile_pat_def
    ,exh_to_patTheory.sLet_def
    ,exh_to_patTheory.sIf_def
    ,exh_to_patTheory.ground_def
    ,exh_to_patTheory.pure_def
    ,numLib.SUC_RULE exh_to_patTheory.Let_Els_def
    ,exh_to_patTheory.pure_op_def
    ,exh_to_patTheory.pure_op_op_def
    ,exh_to_patTheory.Bool_def
    ,exh_to_patTheory.compile_def
    ]

  (* closLang *)
  ; add_datatype``:closLang$exp``
  ; add_datatype``:closLang$op``
  ; add_thms [closLangTheory.max_app_def]
  (* pat_to_clos *)
  ; add_thms
    [pat_to_closTheory.compile_def
    ,pat_to_closTheory.string_tag_def
    ,pat_to_closTheory.vector_tag_def
    ,pat_to_closTheory.compile_def
    (*,pat_to_closTheory.pat_tag_shift_def*)
    ]
  (* clos_mti *)
  ; add_thms
    [clos_mtiTheory.intro_multi_def
    ,clos_mtiTheory.collect_args_def
    ]
  (* clos_number *)
  ; add_thms
    [clos_numberTheory.renumber_code_locs_def]
  (* clos_call *)
  ; add_datatype``:clos_call$val_approx``
  ; add_thms
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
    ]
  (* clos_annotate *)
  ; add_thms
    [clos_annotateTheory.get_var_def
    ,clos_annotateTheory.shifted_env_def
    ,clos_annotateTheory.annotate_def
    ,clos_annotateTheory.shift_def
    ]
  (* clos_free *)
  ; add_thms
    [clos_freeTheory.free_def
    ]
  (* clos_remove *)
  ; add_thms
    [clos_removeTheory.no_overlap_def
    ,clos_removeTheory.no_overlap_def_compute
    ,clos_removeTheory.remove_def
    ,clos_removeTheory.const_0_def
    ,clos_removeTheory.pure_def
    ,clos_removeTheory.pure_op_def
    ,clos_removeTheory.MAPi_def
    ]

  (* bvl *)
  ; add_datatype``:bvl$exp``
  (* clos_to_bvl *)
  ; add_thms
    [clos_to_bvlTheory.closure_tag_def
    ,clos_to_bvlTheory.recc_Let0_def
    ,clos_to_bvlTheory.compile_def
    ,clos_to_bvlTheory.init_code_def
    ,clos_to_bvlTheory.block_equality_code_def
    ,clos_to_bvlTheory.equality_code_def
    ,clos_to_bvlTheory.check_closure_def
    ,clos_to_bvlTheory.RaiseEq_def
    ,clos_to_bvlTheory.ToList_code_def
    ,clos_to_bvlTheory.generate_partial_app_closure_fn_def
    ,clos_to_bvlTheory.generate_generic_app_def
    ,clos_to_bvlTheory.mk_tick_def
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
    ,clos_to_bvlTheory.Bool_def
    ,clos_to_bvlTheory.bool_to_tag_def
    ,clos_to_bvlTheory.clos_tag_shift_def
    ,clos_to_bvlTheory.compile_exps_def
    ]
  (* bvl_inline *)
  ; add_thms
    [bvl_inlineTheory.inline_def]
  (* bvl_const *)
  ; add_thms
    [bvl_constTheory.isConst_def
    ,bvl_constTheory.compile_exps_def
    ,bvl_constTheory.compile_op_def
    ,bvl_constTheory.getConst_def
    ]
  (* bvl_handle *)
  ; add_thms
    [bvl_handleTheory.compile_def]
  (* bvl_jump *)
  ; add_thms
    [bvl_jumpTheory.JumpList_def
    ,bvl_jumpTheory.Jump_def
    ]
  (* bvi *)
  ; add_datatype``:bvi$exp``
  (* bvl_to_bvi *)
  ; add_thms
    [bvl_to_bviTheory.destLet_def
    ,bvl_to_bviTheory.num_stubs_def
    ,bvl_to_bviTheory.compile_prog_def
    ,bvl_to_bviTheory.compile_list_def
    ,bvl_to_bviTheory.compile_single_def
    ,bvl_to_bviTheory.compile_def
    ,bvl_to_bviTheory.compile_op_def
    ,bvl_to_bviTheory.bvi_stubs_def
    ,bvl_to_bviTheory.CopyGlobals_code_def
    ,bvl_to_bviTheory.AllocGlobal_code_def
    ,bvl_to_bviTheory.InitGlobals_code_def
    ,bvl_to_bviTheory.CopyGlobals_location_def
    ,bvl_to_bviTheory.AllocGlobal_location_def
    ,bvl_to_bviTheory.InitGlobals_location_def
    ,bvl_to_bviTheory.compile_int_def
    ,bvl_to_bviTheory.compile_exps_def
    ,bvl_to_bviTheory.optimise_def
    ]

  (* bvp *)
  ; add_datatype``:bvp$prog``
  ; add_thms
    [bvpTheory.mk_ticks_def]
  (* bvi_to_bvp *)
  ; add_thms
    [bvi_to_bvpTheory.op_space_reset_def
    ,bvi_to_bvpTheory.optimise_def
    ,bvi_to_bvpTheory.compile_prog_def
    ,bvi_to_bvpTheory.compile_part_def
    ,bvi_to_bvpTheory.compile_exp_def
    ,bvi_to_bvpTheory.compile_def
    ,bvi_to_bvpTheory.iAssign_def
    ]
  (*bvp_simp*)
  ; add_thms
    [bvp_simpTheory.pSeq_def
    ,bvp_simpTheory.simp_def
    ]
  (*bvp_space*)
  ; add_thms
    [bvp_spaceTheory.pMakeSpace_def
    ,bvp_spaceTheory.space_def
    ,bvp_spaceTheory.op_space_req_def
    ,bvp_spaceTheory.compile_def
    ]
  (*bvp_live*)
  ; add_thms
    [bvp_liveTheory.compile_def
    ]

  (* wordLang *)
  ; add_datatype``:wordLang$store_name``
  ; add_datatype``:'a wordLang$num_exp``
  ; add_datatype``:'a wordLang$exp``
  ; add_datatype``:'a wordLang$prog``
  ; add_thms
    [wordLangTheory.every_var_exp_def
    ,wordLangTheory.num_exp_def
    ,wordLangTheory.word_op_def
    ,wordLangTheory.every_var_imm_def
    ,wordLangTheory.every_stack_var_def
    ,wordLangTheory.every_var_def
    ,wordLangTheory.every_name_def
    ,wordLangTheory.every_var_inst_def
    ]
  (* bvp_to_word *)
  ; add_thms
    [bvp_to_wordTheory.adjust_var_def
    ,bvp_to_wordTheory.compile_def
    ,bvp_to_wordTheory.compile_part_def
    ,bvp_to_wordTheory.assign_def
    ,bvp_to_wordTheory.comp_def
    ,bvp_to_wordTheory.adjust_set_def
    ]
  (*wordLang inst_select and inst flattening*)
  ; add_thms
    [word_instTheory.three_to_two_reg_def
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
    ]
  (*wordLang ssa form and interface to reg allocator*)
  ; add_thms
    [word_allocTheory.call_arg_convention_def
    ,word_allocTheory.word_alloc_def
    ,word_allocTheory.full_ssa_cc_trans_def
    ,word_allocTheory.limit_var_def
    ,word_allocTheory.max_var_def
    ,word_allocTheory.max_var_inst_def
    ,word_allocTheory.max_var_exp_def
    ,word_allocTheory.list_max_def
    ,word_allocTheory.max3_def
    ,word_allocTheory.max2_def
    ,word_allocTheory.setup_ssa_def
    ,word_allocTheory.ssa_cc_trans_def
    ,word_allocTheory.oracle_colour_ok_def
    ,word_allocTheory.every_even_colour_def
    ,word_allocTheory.check_colouring_ok_alt_def
    ,word_allocTheory.get_prefs_def
    ,word_allocTheory.get_clash_sets_def
    ,word_allocTheory.get_writes_def
    ,word_allocTheory.get_live_def
    ,word_allocTheory.numset_list_insert_def
    ,word_allocTheory.get_live_exp_def
    ,word_allocTheory.get_live_inst_def
    ,word_allocTheory.get_writes_inst_def
    ,word_allocTheory.apply_colour_def
    ,word_allocTheory.apply_colour_inst_def
    ,word_allocTheory.apply_colour_imm_def
    ,word_allocTheory.apply_colour_exp_def
    ,word_allocTheory.ssa_cc_trans_exp_def
    ,word_allocTheory.list_next_var_rename_move_def
    ,word_allocTheory.ssa_cc_trans_inst_def
    ,word_allocTheory.merge_moves_def
    ,word_allocTheory.fix_inconsistencies_def
    ,word_allocTheory.fake_moves_def
    ,word_allocTheory.even_list_def
    ,word_allocTheory.fake_move_def
    ,word_allocTheory.list_next_var_rename_def
    ,word_allocTheory.next_var_rename_def
    ,word_allocTheory.option_lookup_def
    ,word_allocTheory.post_alloc_conventions_def
    ,word_allocTheory.apply_nummap_key_def
    ]
    (*Not needed word_allocTheory.pre_alloc_conventions_def"*)

  (*reg_alloc TODO: maybe make a top level computelib for reg_alloc itself*)
  ; add_datatype ``:ra_state``
  (*monadic*)
  ; add_thms
    [state_transformerTheory.MWHILE_DEF
    ,state_transformerTheory.BIND_DEF
    ,state_transformerTheory.UNIT_DEF
    ,state_transformerTheory.FOREACH_def
    ,pairTheory.UNCURRY_DEF
    ,state_transformerTheory.IGNORE_BIND_DEF
    ]

  (*sorting*)
  ; add_thms
    [sortingTheory.PARTITION_DEF
    ,sortingTheory.PART_DEF
    ,sortingTheory.QSORT_DEF
    ]

  ; add_thms
    [reg_allocTheory.is_stack_var_def
    ,reg_allocTheory.undir_move_insert_def
    ,reg_allocTheory.reg_alloc_def
    ,reg_allocTheory.maybe_flip_def
    ,reg_allocTheory.briggs_coalesce_def
    ,reg_allocTheory.do_briggs_step_def
    ,reg_allocTheory.briggs_has_work_def
    ,reg_allocTheory.total_colour_def
    ,reg_allocTheory.aux_move_pref_def
    ,reg_allocTheory.move_pref_def
    ,reg_allocTheory.first_match_col_def
    ,reg_allocTheory.resort_moves_def
    ,reg_allocTheory.moves_to_sp_def
    ,reg_allocTheory.unspill_def
    ,reg_allocTheory.pri_move_insert_def
    ,reg_allocTheory.aux_pref_def
    ,reg_allocTheory.rpt_do_step2_def
    ,reg_allocTheory.do_step2_def
    ,reg_allocTheory.full_simplify_def
    ,reg_allocTheory.full_coalesce_def
    ,reg_allocTheory.full_coalesce_aux_def
    ,reg_allocTheory.deg_comparator_def
    ,reg_allocTheory.sec_ra_state_def
    ,reg_allocTheory.rpt_do_step_def
    ,reg_allocTheory.has_work_def
    ,reg_allocTheory.do_step_def
    ,reg_allocTheory.get_clock_def
    ,reg_allocTheory.dec_clock_def
    ,reg_allocTheory.coalesce_def
    ,reg_allocTheory.respill_def
    ,reg_allocTheory.pair_rename_def
    ,reg_allocTheory.do_coalesce_def
    ,reg_allocTheory.force_add_def
    ,reg_allocTheory.split_avail_def
    ,reg_allocTheory.is_coalesceable_move_def
    ,reg_allocTheory.is_valid_move_def
    ,reg_allocTheory.george_ok_def
    ,reg_allocTheory.briggs_ok_def
    ,reg_allocTheory.freeze_def
    ,reg_allocTheory.spill_def
    ,reg_allocTheory.max_non_coalesced_def
    ,reg_allocTheory.simplify_def
    ,reg_allocTheory.set_unavail_moves_def
    ,reg_allocTheory.revive_moves_def
    ,reg_allocTheory.dec_deg_def
    ,reg_allocTheory.dec_one_def
    ,reg_allocTheory.inc_one_def
    ,reg_allocTheory.get_edges_def
    ,reg_allocTheory.add_coalesce_def
    ,reg_allocTheory.freeze_node_def
    ,reg_allocTheory.add_unavail_moves_def
    ,reg_allocTheory.set_move_rel_def
    ,reg_allocTheory.get_unavail_moves_def
    ,reg_allocTheory.add_avail_moves_def
    ,reg_allocTheory.add_avail_moves_pri_def
    ,reg_allocTheory.set_avail_moves_def
    ,reg_allocTheory.set_avail_moves_pri_def
    ,reg_allocTheory.get_avail_moves_def
    ,reg_allocTheory.get_avail_moves_pri_def
    ,reg_allocTheory.set_coalesced_def
    ,reg_allocTheory.get_coalesced_def
    ,reg_allocTheory.set_deg_def
    ,reg_allocTheory.get_move_rel_def
    ,reg_allocTheory.get_colours_def
    ,reg_allocTheory.set_freeze_worklist_def
    ,reg_allocTheory.get_freeze_worklist_def
    ,reg_allocTheory.set_simp_worklist_def
    ,reg_allocTheory.get_simp_worklist_def
    ,reg_allocTheory.get_spill_worklist_def
    ,reg_allocTheory.set_spill_worklist_def
    ,reg_allocTheory.add_freeze_worklist_def
    ,reg_allocTheory.add_spill_worklist_def
    ,reg_allocTheory.add_simp_worklist_def
    ,reg_allocTheory.spill_colouring_def
    ,reg_allocTheory.get_deg_def
    ,reg_allocTheory.get_degs_def
    ,reg_allocTheory.push_stack_def
    ,reg_allocTheory.get_graph_def
    ,reg_allocTheory.get_stack_def
    ,reg_allocTheory.init_ra_state_def
    ,reg_allocTheory.split_priority_def
    ,reg_allocTheory.considered_var_def
    ,reg_allocTheory.in_moves_set_def
    ,reg_allocTheory.in_moves_def
    ,reg_allocTheory.count_degrees_def
    ,reg_allocTheory.option_filter_def
    ,reg_allocTheory.assign_colour2_def
    ,reg_allocTheory.remove_colours_def
    ,reg_allocTheory.unbound_colours_def
    ,reg_allocTheory.alloc_colouring_def
    ,reg_allocTheory.id_colour_def
    ,reg_allocTheory.alloc_colouring_aux_def
    ,reg_allocTheory.assign_colour_def
    ,reg_allocTheory.list_g_insert_def
    ,reg_allocTheory.clash_sets_to_sp_g_def
    ,reg_allocTheory.clique_g_insert_def
    ,reg_allocTheory.lookup_g_def
    ,reg_allocTheory.undir_g_insert_def
    ,reg_allocTheory.dir_g_insert_def
    ,reg_allocTheory.is_alloc_var_def
    ,reg_allocTheory.is_phy_var_def
    ]

  (*parmove -- same TODO as allocator*)
  ; add_thms
    [parmoveTheory.pmov_def
    ,parmoveTheory.parmove_def
    ,parmoveTheory.fstep_def
    ,listTheory.splitAtPki_DEF
    ]

  (*stackLang*)
  ; add_datatype``:'a stackLang$prog``
  (*word_to_stack*)
  ; add_thms
    [word_to_stackTheory.wReg1_def
    ,word_to_stackTheory.write_bitmap_def
    ,word_to_stackTheory.compile_def
    ,word_to_stackTheory.raise_stub_def
    ,word_to_stackTheory.comp_def
    ,word_to_stackTheory.StackArgs_def
    ,word_to_stackTheory.stack_move_def_compute
    ,word_to_stackTheory.stack_move_def
    ,word_to_stackTheory.stack_free_def
    ,word_to_stackTheory.stack_arg_count_def
    ,word_to_stackTheory.CallAny_def
    ,word_to_stackTheory.SeqStackFree_def
    ,word_to_stackTheory.wLive_def
    ,word_to_stackTheory.wLiveAux_def
    ,word_to_stackTheory.wStackStore_def
    ,word_to_stackTheory.word_list_def
    ,word_to_stackTheory.bits_to_word_def
    ,word_to_stackTheory.wInst_def
    ,word_to_stackTheory.wMove_def
    ,word_to_stackTheory.format_result_def
    ,word_to_stackTheory.format_var_def
    ,word_to_stackTheory.pair_swap_def
    ,word_to_stackTheory.wMoveAux_def
    ,word_to_stackTheory.wMoveSingle_def
    ,word_to_stackTheory.wRegWrite1_def
    ,word_to_stackTheory.wStackLoad_def
    ,word_to_stackTheory.wReg2_def
    ,word_to_stackTheory.wRegImm2_def
    ,word_to_stackTheory.compile_prog_def
    ,word_to_stackTheory.compile_single_def
    ,word_to_stackTheory.next_n_oracle_def
    ]
  (*stack_alloc*)
  ; add_thms
    [stack_allocTheory.stubs_def
    ,stack_allocTheory.next_lab_def
    ,stack_allocTheory.comp_def
    ,stack_allocTheory.prog_comp_def
    ,stack_allocTheory.compile_def
    ]
  (*stack_remove*)
  ; add_thms
    [stack_removeTheory.max_stack_alloc_def
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
    ,stack_removeTheory.list_Seq_def
    ,stack_removeTheory.halt_inst_def
    ,stack_removeTheory.init_code_def
    ,stack_removeTheory.init_code_def
    ,stack_removeTheory.init_stubs_def
    ,stack_removeTheory.compile_def
    ]
  (*db_vars*)
  ; add_datatype``:db_var_set``
  ; add_thms
    [db_varsTheory.mk_Union_def
    ,db_varsTheory.vars_to_list_def
    ,db_varsTheory.has_var_def
    ,db_varsTheory.db_to_set_acc_def
    ,db_varsTheory.db_to_set_def
    ,db_varsTheory.list_mk_Union_def
    ]
  (*stack names*)
  ; add_thms
    [stack_namesTheory.find_name_def
    ,stack_namesTheory.ri_find_name_def
    ,stack_namesTheory.inst_find_name_def
    ,stack_namesTheory.dest_find_name_def
    ,stack_namesTheory.comp_def
    ,stack_namesTheory.prog_comp_def
    ,stack_namesTheory.compile_def
    ,stack_namesTheory.x64_names_def
    ]
  (*stack_to_lab*)
  ; add_thms
    [stack_to_labTheory.no_ret_def
    ,stack_to_labTheory.compile_jump_def
    ,stack_to_labTheory.negate_def
    ,stack_to_labTheory.flatten_def
    ,stack_to_labTheory.prog_to_section_def
    ,stack_to_labTheory.compile_def
    ]
  (*labLang*)
  ; add_datatype``:lab``
  ; add_datatype``:'a asm_with_lab``
  ; add_datatype``:'a line``
  ; add_datatype``:'a sec``
  (*lab_filter*)
  ; add_thms
    [lab_filterTheory.not_skip_def
    ,lab_filterTheory.filter_skip_def
    ]
  (*lab_to_target*)
  ; add_thms
    [lab_to_targetTheory.ffi_offset_def
    ,lab_to_targetTheory.sec_lengths_update_def
    ,lab_to_targetTheory.compile_def
    ,lab_to_targetTheory.compile_lab_def
    ,lab_to_targetTheory.prog_to_bytes_def
    ,lab_to_targetTheory.line_bytes_def
    ,lab_to_targetTheory.remove_labels_def
    ,lab_to_targetTheory.remove_labels_loop_def
    ,lab_to_targetTheory.filter_labs_def
    ,lab_to_targetTheory.pad_code_def
    ,lab_to_targetTheory.pad_section_def
    ,lab_to_targetTheory.pad_bytes_def
    ,lab_to_targetTheory.all_asm_ok_def
    ,lab_to_targetTheory.sec_asm_ok_def
    ,lab_to_targetTheory.all_lengths_update_def
    ,lab_to_targetTheory.sec_length_def
    ,lab_to_targetTheory.all_lengths_ok_def
    ,lab_to_targetTheory.sec_lengths_ok_def
    ,lab_to_targetTheory.enc_secs_again_def
    ,lab_to_targetTheory.full_sec_length_def
    ,lab_to_targetTheory.find_pos_def
    ,lab_to_targetTheory.enc_line_again_def
    ,lab_to_targetTheory.get_jump_offset_def
    ,lab_to_targetTheory.get_label_def
    ,lab_to_targetTheory.lab_inst_def
    ,lab_to_targetTheory.compute_labels_def
    ,lab_to_targetTheory.sec_labs_def
    ,lab_to_targetTheory.asm_line_labs_def
    ,lab_to_targetTheory.enc_sec_list_def
    ,lab_to_targetTheory.enc_sec_def
    ,lab_to_targetTheory.enc_line_def
    ]
  (*Everything in backend theory*)
  ; add_thms
    [backendTheory.to_mod_def
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
    ,backendTheory.from_bvp_def
    ,backendTheory.from_word_def
    ,backendTheory.from_stack_def
    ,backendTheory.from_lab_def
    ,backendTheory.compile_def
    ,backendTheory.to_pat_def
    ,backendTheory.to_lab_def
    ,backendTheory.to_stack_def
    ,backendTheory.to_word_def
    ,backendTheory.to_bvp_def
    ,backendTheory.to_bvi_def
    ,backendTheory.to_bvl_def
    ,backendTheory.to_clos_def
    ,backendTheory.to_exh_def
    ,backendTheory.to_con_def
    ,backendTheory.to_dec_def
    ]
  (*Missing def from miscTheory used in lab_to_target.
  TODO: Move into HOL or move into lab_to_target itself?*)
  ; add_thms[miscTheory.lookup_any_def]

  (*asm -- 'a should be 64*)
  ; add_datatype ``:'a asm_config``
  ; add_datatype ``:'a reg_imm``
  ; add_datatype ``:binop``
  ; add_datatype ``:cmp``
  ; add_datatype ``:shift``
  ; add_datatype ``:'a arith``
  ; add_datatype ``:'a addr``
  ; add_datatype ``:mem_op``
  ; add_datatype ``:'a inst``
  ; add_datatype ``:'a asm``
  end

val the_compiler_compset =
  let
    val c = compute_basicLib.the_basic_compset
    val () = compute_semanticsLib.add_ast_compset c
    val () = add_compiler_compset c
  in
    c
  end

end



end
