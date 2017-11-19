structure backendComputeLib :> backendComputeLib =
struct

local

open HolKernel boolLib bossLib computeLib
open modLangTheory source_to_modTheory
open conLangTheory mod_to_conTheory
open decLangTheory con_to_decTheory
open exhLangTheory dec_to_exhTheory exh_reorderTheory
open patLangTheory exh_to_patTheory
open closLangTheory pat_to_closTheory
open clos_mtiTheory
open clos_numberTheory
open clos_callTheory
open clos_annotateTheory
open clos_knownTheory
open bvlTheory clos_to_bvlTheory
open bviTheory bvl_to_bviTheory bvl_inlineTheory bvl_constTheory bvl_handleTheory bvl_jumpTheory bvi_tailrecTheory
open dataLangTheory bvi_to_dataTheory data_simpTheory data_liveTheory data_spaceTheory
open wordLangTheory data_to_wordTheory word_instTheory word_allocTheory word_removeTheory
open stackLangTheory word_to_wordTheory word_to_stackTheory stack_removeTheory stack_namesTheory db_varsTheory
open labLangTheory stack_to_labTheory lab_filterTheory
open asmTheory backendTheory
open semanticsComputeLib reg_allocComputeLib

(*Order of thms shown below:
First, all the small compilation steps between ILs + IL to IL transforms

src -> mod -> con -> dec -> exh -> pat -> clos -> bvl -> data -> word
-> stack -> lab -> target

Then all the _to_target scripts linking things up
lab -> stack -> word -> ...

*)

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars (merge_grammars ["backend"])
end

open Parse

in

val add_backend_compset = computeLib.extend_compset
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
    ,``:modLang$op``
    ,``:modLang$exp``
    ,``:modLang$dec``
    ,``:modLang$prompt``
    (* backend_common *)
    ,``:backend_common$tra``
    ]
  ,computeLib.Defs
    [ (* ---- source_to_mod ---- *)
     source_to_modTheory.compile_prog_def
    ,source_to_modTheory.compile_top_def
    ,source_to_modTheory.compile_decs_def
    ,source_to_modTheory.compile_dec_def
    ,source_to_modTheory.compile_exp_def
    ,source_to_modTheory.compile_pat_def
    ,source_to_modTheory.pat_tups_def
    ,source_to_modTheory.om_tra_def
    ,source_to_modTheory.make_varls_def
    ,source_to_modTheory.alloc_defs_def
    ,source_to_modTheory.Bool_def
    ,source_to_modTheory.compile_def
    ,source_to_modTheory.empty_config_def
    ,source_to_modTheory.astOp_to_modOp_def
      (* ---- conLang ---- *)
    ,backend_commonTheory.orphan_trace_def
    ,backend_commonTheory.mk_cons_def
    ,backend_commonTheory.mk_union_def
    ,backend_commonTheory.bind_tag_def
    ,backend_commonTheory.chr_tag_def
    ,backend_commonTheory.div_tag_def
    ,backend_commonTheory.subscript_tag_def
    ,backend_commonTheory.true_tag_def
    ,backend_commonTheory.false_tag_def
    ,backend_commonTheory.nil_tag_def
    ,backend_commonTheory.cons_tag_def
    ,backend_commonTheory.none_tag_def
    ,backend_commonTheory.some_tag_def
    ,backend_commonTheory.tuple_tag_def
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
    ,mod_to_conTheory.insert_tag_env_def
    ,mod_to_conTheory.get_tagenv_def
    ,mod_to_conTheory.get_exh_def
    ,mod_to_conTheory.alloc_tag_def
    ,mod_to_conTheory.alloc_tags_def
    ,mod_to_conTheory.compile_def
    ,mod_to_conTheory.empty_config_def
      (* decLang *)
      (* ---- con_to_dec ---- *)
    ,con_to_decTheory.init_globals_def
    ,con_to_decTheory.init_global_funs_def
    ,con_to_decTheory.od_tra_def
    ,con_to_decTheory.compile_decs_def
    ,con_to_decTheory.compile_prompt_def
    ,con_to_decTheory.compile_prog_def
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
    ,dec_to_exhTheory.get_tags_def
    ,dec_to_exhTheory.exhaustive_match_def
    ,dec_to_exhTheory.add_default_def
    ,dec_to_exhTheory.compile_pat_def
    ,dec_to_exhTheory.compile_exp_def
    ,dec_to_exhTheory.compile_def
    ,exh_reorderTheory.is_const_con_def
    ,exh_reorderTheory.isPcon_def
    ,exh_reorderTheory.isPvar_def
    ,exh_reorderTheory.const_cons_sep_def
    ,exh_reorderTheory.const_cons_fst_def
    ,exh_reorderTheory.compile_def
    ]
  ,computeLib.Tys
    [ (* ---- patLang ---- *)
     ``:patLang$exp``
    ,``:patLang$op``
    ]
      (* ---- exh_to_pat ---- *)
  ,computeLib.Defs
    [exh_to_patTheory.Bool_def
    ,exh_to_patTheory.isBool_def
    ,exh_to_patTheory.sIf_def
    ,exh_to_patTheory.pure_op_op_eqn
    ,exh_to_patTheory.pure_op_def
    ,exh_to_patTheory.pure_def
    ,exh_to_patTheory.ground_def
    ,exh_to_patTheory.sLet_def
    ,numLib.SUC_RULE exh_to_patTheory.Let_Els_def
    ,exh_to_patTheory.compile_pat_def
    ,exh_to_patTheory.compile_row_def
    ,exh_to_patTheory.compile_exp_def
    ,exh_to_patTheory.compile_def
    ]
  ,computeLib.Tys
    [ (* ---- closLang ---- *)
     ``:closLang$exp``
    ,``:closLang$op``
    ,``:clos_known$val_approx``
    ,``:clos_known$globalOpt``
    ]
  ,computeLib.Defs
    [closLangTheory.pure_def
    ,closLangTheory.pure_op_def
      (* ---- pat_to_clos ---- *)
    ,pat_to_closTheory.dest_WordToInt_def
    ,pat_to_closTheory.CopyByteStr_def
    ,pat_to_closTheory.CopyByteAw8_def
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
    ,clos_callTheory.free_def
    ,clos_callTheory.closed_def
    ,clos_callTheory.code_list_def
    ,clos_callTheory.compile_def
    ,clos_callTheory.calls_def
    ,clos_callTheory.calls_list_def
    ,clos_callTheory.insert_each_def_compute
    ,clos_callTheory.GENLIST_Var_def
      (* ---- clos_annotate ---- *)
    ,clos_annotateTheory.get_var_def
    ,clos_annotateTheory.shifted_env_def
    ,clos_annotateTheory.annotate_def
    ,clos_annotateTheory.shift_def
    ,clos_annotateTheory.compile_def
    ,clos_annotateTheory.const_0_def
    ,clos_annotateTheory.no_overlap_def_compute
    ,clos_annotateTheory.alt_free_def
      (* ---- clos_known---- *)
    ,clos_knownTheory.merge_def
    ,clos_knownTheory.compile_def
    ,clos_knownTheory.dest_Clos_def
    ,clos_knownTheory.known_def
    ,clos_knownTheory.known_op_def
    ,clos_knownTheory.isGlobal_def
    ,clos_knownTheory.gO_destApx_def
    ,clos_knownTheory.clos_gen_def
    ]
  ,computeLib.Tys
    [ (* ---- bvl ---- *)
     ``:bvl$exp``
    ]
  ,computeLib.Defs
    [ (* ---- clos_to_bvl ---- *)
     backend_commonTheory.closure_tag_def
    ,backend_commonTheory.clos_tag_shift_def
    ,backend_commonTheory.partial_app_tag_def
    ,clos_to_bvlTheory.recc_Let0_def
    ,clos_to_bvlTheory.partial_app_fn_location_def
    ,clos_to_bvlTheory.default_config_def
    ,clos_to_bvlTheory.compile_def
    ,clos_to_bvlTheory.compile_prog_def
    ,clos_to_bvlTheory.init_code_def
    ,clos_to_bvlTheory.block_equality_code_def
    ,clos_to_bvlTheory.equality_code_def
    ,clos_to_bvlTheory.check_closure_def
    ,clos_to_bvlTheory.ToList_code_def
    ,clos_to_bvlTheory.generic_app_fn_location_def
    ,clos_to_bvlTheory.generate_partial_app_closure_fn_def
    ,clos_to_bvlTheory.generate_generic_app_def
    ,clos_to_bvlTheory.num_added_globals_def
    ,clos_to_bvlTheory.partial_app_label_table_loc_def
    ,clos_to_bvlTheory.partial_app_fn_location_code_def
    ,clos_to_bvlTheory.init_globals_def
    ,bvlTheory.mk_tick_def
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
    ,bvlTheory.Bool_def
    ,backend_commonTheory.bool_to_tag_def
    ,clos_to_bvlTheory.compile_exps_def
    ,clos_to_bvlTheory.code_merge_def
    ,clos_to_bvlTheory.code_split_def
    ,clos_to_bvlTheory.code_sort_def
      (* ---- bvl_inline ---- *)
    ,bvl_inlineTheory.inline_def
    ,bvl_inlineTheory.is_small_aux_def
    ,bvl_inlineTheory.is_small_def
    ,bvl_inlineTheory.is_rec_def
    ,bvl_inlineTheory.var_list_def
    ,bvl_inlineTheory.dest_op_def
    ,bvl_inlineTheory.let_op_def
    ,bvl_inlineTheory.let_op_sing_def
    ,bvl_inlineTheory.must_inline_def
    ,bvl_inlineTheory.inline_all_def
    ,bvl_inlineTheory.optimise_def
    ,bvl_inlineTheory.compile_prog_def
      (* ---- bvl_const ---- *)
    ,bvl_constTheory.dest_simple_def
    ,bvl_constTheory.SmartOp_def
    ,bvl_constTheory.extract_def
    ,bvl_constTheory.extract_list_def
    ,bvl_constTheory.delete_var_def
    ,bvl_constTheory.compile_def
    ,bvl_constTheory.compile_exp_def
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
    ,``:bvi_tailrec$assoc_op``
    ,``:bvi_tailrec$v_ty``
    ]
  ,computeLib.Defs
    [ (* ---- bvl_to_bvi ---- *)
     bvl_to_bviTheory.destLet_def
    ,bvl_to_bviTheory.alloc_glob_count_def
    ,backend_commonTheory.bvl_num_stubs_def
    ,backend_commonTheory.bvl_to_bvi_namespaces_def
    ,bvl_to_bviTheory.compile_prog_def
    ,bvl_to_bviTheory.compile_list_def
    ,bvl_to_bviTheory.compile_single_def
    ,bvl_to_bviTheory.compile_def
    ,bvl_to_bviTheory.compile_op_def
    ,bvl_to_bviTheory.stubs_def
    ,bvl_to_bviTheory.CopyGlobals_code_def
    ,bvl_to_bviTheory.AllocGlobal_code_def
    ,bvl_to_bviTheory.InitGlobals_code_def
    ,bvl_to_bviTheory.ListLength_code_def
    ,bvl_to_bviTheory.FromListByte_code_def
    ,bvl_to_bviTheory.SumListLength_code_def
    ,bvl_to_bviTheory.ConcatByte_code_def
    ,bvl_to_bviTheory.CopyGlobals_location_eq
    ,bvl_to_bviTheory.AllocGlobal_location_eq
    ,bvl_to_bviTheory.InitGlobals_max_def
    ,bvl_to_bviTheory.InitGlobals_location_eq
    ,bvl_to_bviTheory.ListLength_location_eq
    ,bvl_to_bviTheory.FromListByte_location_eq
    ,bvl_to_bviTheory.SumListLength_location_eq
    ,bvl_to_bviTheory.ConcatByte_location_eq
    ,bvl_to_bviTheory.compile_int_def
    ,bvl_to_bviTheory.compile_exps_def
    ,bvl_to_bviTheory.compile_aux_def
    ,bvl_to_bviTheory.default_config_def
      (* ---- bvi_let ---- *)
    ,bvi_letTheory.extract_def
    ,bvi_letTheory.extract_list_def
    ,bvi_letTheory.delete_var_def
    ,bvi_letTheory.compile_def
    ,bvi_letTheory.compile_exp_def
      (* ---- bvi_tailrec ---- *)
    ,bvi_tailrecTheory.dummy_def
    ,bvi_tailrecTheory.small_int_def
    ,bvi_tailrecTheory.is_arith_op_def
    ,bvi_tailrecTheory.is_const_def
    ,bvi_tailrecTheory.is_num_rel_def
    ,bvi_tailrecTheory.is_rec_def
    ,bvi_tailrecTheory.to_op_def
    ,bvi_tailrecTheory.from_op_def
    ,bvi_tailrecTheory.op_eq_def
    ,bvi_tailrecTheory.apply_op_def
    ,bvi_tailrecTheory.id_from_op_def
    ,bvi_tailrecTheory.index_of_def
    ,bvi_tailrecTheory.args_from_def
    ,bvi_tailrecTheory.get_bin_args_def
    ,bvi_tailrecTheory.try_update_def
    ,bvi_tailrecTheory.no_err_def
    ,bvi_tailrecTheory.is_rec_or_rec_binop_def
    ,bvi_tailrecTheory.assoc_swap_def
    ,bvi_tailrecTheory.rewrite_op_def
    ,bvi_tailrecTheory.decide_ty_def
    ,bvi_tailrecTheory.LAST1_def
    ,bvi_tailrecTheory.scan_expr_def
    ,bvi_tailrecTheory.push_call_def
    ,bvi_tailrecTheory.mk_tailcall_def
    ,bvi_tailrecTheory.rewrite_def
    ,bvi_tailrecTheory.check_exp_def
    ,bvi_tailrecTheory.let_wrap_def
    ,bvi_tailrecTheory.mk_aux_call_def
    ,bvi_tailrecTheory.compile_exp_def
    ,bvi_tailrecTheory.compile_prog_def
    ]
  ,computeLib.Tys
    [ (* ---- data ---- *)
     ``:dataLang$prog``
      (* ---- data_to_word ---- *)
    ,``:data_to_word$word_op_type``
    ,``:data_to_word$gc_kind``
    ]
  ,computeLib.Defs
    [dataLangTheory.mk_ticks_def
    ,backend_commonTheory.data_num_stubs_def
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
      (* word_bignum *)
    ,``:word_bignum$address``
    ,``:'a word_bignum$mini``
    ]
  ,computeLib.Defs
    [wordLangTheory.every_var_exp_def
    ,wordLangTheory.num_exp_def
    ,wordLangTheory.word_sh_def
    ,wordLangTheory.word_op_def
    ,wordLangTheory.every_var_imm_def
    ,wordLangTheory.every_stack_var_def
    ,wordLangTheory.every_var_def
    ,wordLangTheory.every_name_def
    ,wordLangTheory.every_var_inst_def
    ,wordLangTheory.max_var_def
    ,wordLangTheory.max_var_inst_def
    ,wordLangTheory.max_var_exp_def
    ,backend_commonTheory.word_num_stubs_def
    ,wordLangTheory.raise_stub_location_eq
      (* ---- data_to_word ---- *)
    ,data_to_wordTheory.adjust_var_def
    ,data_to_wordTheory.adjust_set_def
    ,data_to_wordTheory.Unit_def
    ,data_to_wordTheory.GiveUp_def
    ,data_to_wordTheory.BignumHalt_def
    ,data_to_wordTheory.make_header_def
    ,data_to_wordTheory.tag_mask_def
    ,data_to_wordTheory.encode_header_def
    ,data_to_wordTheory.list_Seq_def
    ,wordLangTheory.shift_def
    ,data_to_wordTheory.StoreEach_def
    ,data_to_wordTheory.small_shift_length_def
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
    ,data_to_wordTheory.AnyArith_location_eq
    ,data_to_wordTheory.Add_location_eq
    ,data_to_wordTheory.Sub_location_eq
    ,data_to_wordTheory.Mul_location_eq
    ,data_to_wordTheory.Div_location_eq
    ,data_to_wordTheory.Mod_location_eq
    ,data_to_wordTheory.Compare1_location_eq
    ,data_to_wordTheory.Compare_location_eq
    ,data_to_wordTheory.Equal1_location_eq
    ,data_to_wordTheory.Equal_location_eq
    ,data_to_wordTheory.LongDiv1_location_eq
    ,data_to_wordTheory.LongDiv_location_eq
    ,data_to_wordTheory.MemCopy_location_eq
    ,data_to_wordTheory.Bignum_location_eq
    ,data_to_wordTheory.ByteCopy_location_eq
    ,data_to_wordTheory.ByteCopyAdd_location_eq
    ,data_to_wordTheory.ByteCopySub_location_eq
    ,data_to_wordTheory.ByteCopyNew_location_eq
    ,data_to_wordTheory.Bignum_location_eq
    ,data_to_wordTheory.get_gen_size_def
    ,data_to_wordTheory.AllocVar_def
    ,data_to_wordTheory.MakeBytes_def
    ,data_to_wordTheory.WriteLastByte_aux_def
    ,data_to_wordTheory.WriteLastBytes_def
    ,data_to_wordTheory.SmallLsr_def
    ,data_to_wordTheory.RefByte_code_def
    ,data_to_wordTheory.Maxout_bits_code_def
    ,data_to_wordTheory.Make_ptr_bits_code_def
    ,data_to_wordTheory.FromList_code_def
    ,data_to_wordTheory.FromList1_code_def
    ,data_to_wordTheory.RefArray_code_def
    ,data_to_wordTheory.Replicate_code_def
    ,data_to_wordTheory.AnyArith_code_def
    ,data_to_wordTheory.Add_code_def
    ,data_to_wordTheory.Sub_code_def
    ,data_to_wordTheory.Mul_code_def
    ,data_to_wordTheory.Div_code_def
    ,data_to_wordTheory.Mod_code_def
    ,data_to_wordTheory.Compare1_code_def
    ,data_to_wordTheory.Compare_code_def
    ,data_to_wordTheory.Equal1_code_def
    ,data_to_wordTheory.Equal_code_def
    ,data_to_wordTheory.LongDiv_code_def
    ,data_to_wordTheory.LongDiv1_code_def
    ,data_to_wordTheory.MemCopy_code_def
    ,data_to_wordTheory.ByteCopy_code_def
    ,data_to_wordTheory.ByteCopyAdd_code_def
    ,data_to_wordTheory.ByteCopySub_code_def
    ,data_to_wordTheory.ByteCopyNew_code_def
    ,data_to_wordTheory.get_names_def
    ,data_to_wordTheory.LoadWord64_def
    ,data_to_wordTheory.LoadBignum_def
    ,data_to_wordTheory.WriteWord64_def
    ,data_to_wordTheory.WriteWord64_on_32_def
    ,data_to_wordTheory.WriteWord32_on_32_def
    ,data_to_wordTheory.WordOp64_on_32_def
    ,data_to_wordTheory.WordShift64_on_32_def
    ,data_to_wordTheory.ShiftVar_def
    ,data_to_wordTheory.AnyHeader_def
    ,data_to_wordTheory.AddNumSize_def
    ,multiwordTheory.n2mw_def
    ,multiwordTheory.i2mw_def
    ,data_to_wordTheory.bignum_words_def
    ,data_to_wordTheory.Smallnum_def
    ,data_to_wordTheory.MemEqList_def
    ,data_to_wordTheory.assign_def
    ,data_to_wordTheory.fp_cmp_inst_def
    ,data_to_wordTheory.fp_bop_inst_def
    ,data_to_wordTheory.fp_uop_inst_def
    ,data_to_wordTheory.comp_def
    ,data_to_wordTheory.compile_part_def
    ,data_to_wordTheory.stubs_def
    ,data_to_wordTheory.compile_def
      (* word_bignum *)
    ,word_bignumTheory.mc_cmp_code_def
    ,word_bignumTheory.mc_sub_loop2_code_def
    ,word_bignumTheory.generated_bignum_stubs_def
    ,word_bignumTheory.compile_def
    ,word_bignumTheory.DivCode_def
    ,word_bignumTheory.div_location_def
    ,word_bignumTheory.SeqIndex_def
    ,word_bignumTheory.SeqTempImmNot_def
    ,word_bignumTheory.SeqTempImm_def
    ,word_bignumTheory.SeqTemp_def
    ,word_bignumTheory.TempOut_def
    ,word_bignumTheory.TempIn2_def
    ,word_bignumTheory.TempIn1_def
    ,word_bignumTheory.compile_exp_def
    ,word_bignumTheory.install_def
    ,word_bignumTheory.code_acc_next_def
    ,word_bignumTheory.has_compiled_def
    ,word_bignumTheory.mc_iop_code_def
    ,word_bignumTheory.mc_isub_flip_code_def
    ,word_bignumTheory.mc_imul_code_def
    ,word_bignumTheory.mc_mul_code_def
    ,word_bignumTheory.mc_mul_pass_code_def
    ,word_bignumTheory.mc_imul1_code_def
    ,word_bignumTheory.mc_iadd_code_def
    ,word_bignumTheory.mc_sub_code_def
    ,word_bignumTheory.mc_sub_loop_code_def
    ,word_bignumTheory.mc_sub1_code_def
    ,word_bignumTheory.mc_sub_loop1_code_def
    ,word_bignumTheory.mc_iadd2_code_def
    ,word_bignumTheory.mc_iadd3_code_def
    ,word_bignumTheory.mc_add_code_def
    ,word_bignumTheory.mc_add_loop_code_def
    ,word_bignumTheory.mc_add_loop2_code_def
    ,word_bignumTheory.mc_add_loop1_code_def
    ,word_bignumTheory.mc_iadd1_code_def
    ,word_bignumTheory.mc_idiv_code_def
    ,word_bignumTheory.mc_idiv0_code_def
    ,word_bignumTheory.mc_idiv_mod_header_code_def
    ,word_bignumTheory.mc_div_sub_call_code_def
    ,word_bignumTheory.mc_div_sub1_code_def
    ,word_bignumTheory.mc_div_sub_aux_code_def
    ,word_bignumTheory.mc_div_sub_aux1_code_def
    ,word_bignumTheory.mc_add1_call_code_def
    ,word_bignumTheory.mc_add1_code_def
    ,word_bignumTheory.mc_div_code_def
    ,word_bignumTheory.mc_div3_code_def
    ,word_bignumTheory.mc_div2_code_def
    ,word_bignumTheory.mc_copy_down_code_def
    ,word_bignumTheory.mc_fix_code_def
    ,word_bignumTheory.mc_simple_div1_code_def
    ,word_bignumTheory.mc_div_loop_code_def
    ,word_bignumTheory.mc_div_sub_loop_code_def
    ,word_bignumTheory.mc_div_sub_code_def
    ,word_bignumTheory.mc_div_adjust_code_def
    ,word_bignumTheory.mc_adjust_aux_code_def
    ,word_bignumTheory.mc_adj_cmp_code_def
    ,word_bignumTheory.mc_div_guess_code_def
    ,word_bignumTheory.mc_div_test_code_def
    ,word_bignumTheory.mc_cmp2_code_def
    ,word_bignumTheory.mc_top_two_code_def
    ,word_bignumTheory.mc_cmp_mul2_code_def
    ,word_bignumTheory.mc_cmp3_code_def
    ,word_bignumTheory.mc_mul_by_single2_code_def
    ,word_bignumTheory.mc_div_r1_code_def
    ,word_bignumTheory.mc_single_mul_add_code_def
    ,word_bignumTheory.mc_single_mul_code_def
    ,word_bignumTheory.mc_mul_by_single_code_def
    ,word_bignumTheory.mc_simple_div_code_def
    ,word_bignumTheory.mc_calc_d_code_def
    ,word_bignumTheory.mc_div1_code_def
    ,word_bignumTheory.mc_single_div_code_def
    ,word_bignumTheory.mc_div0_code_def
    ,word_bignumTheory.mc_compare_code_def
    ,word_bignumTheory.mc_copy_over_code_def
    ,word_bignumTheory.mc_mul_zero_code_def
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
    ,word_simpTheory.strip_const_def
    ,word_simpTheory.const_fp_exp_def
    ,word_simpTheory.const_fp_move_cs_def
    ,word_simpTheory.const_fp_inst_cs_def
    ,word_simpTheory.get_var_imm_cs_def
    ,word_simpTheory.is_gc_const_def
    ,word_simpTheory.const_fp_loop_def
    ,word_simpTheory.const_fp_def
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
    ,word_allocTheory.get_forced_def
    ,word_allocTheory.big_union_def
    ,word_allocTheory.word_alloc_def
    ,word_allocTheory.full_ssa_cc_trans_def
    ,word_allocTheory.limit_var_def
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
    ,backend_commonTheory.stack_num_stubs_def
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
    ,stack_allocTheory.SetNewTrigger_def
    ,stack_allocTheory.word_gc_code_def
    ,stack_allocTheory.word_gc_partial_or_full_def
    ,stack_allocTheory.word_gc_move_roots_bitmaps_code_def
    ,stack_allocTheory.word_gc_move_bitmaps_code_def
    ,stack_allocTheory.word_gc_move_bitmap_code_def
    ,stack_allocTheory.word_gc_move_code_def
    ,stack_allocTheory.word_gc_move_list_code_def
    ,stack_allocTheory.word_gen_gc_partial_move_code_def
    ,stack_allocTheory.word_gen_gc_partial_move_bitmap_code_def
    ,stack_allocTheory.word_gen_gc_partial_move_bitmaps_code_def
    ,stack_allocTheory.word_gen_gc_partial_move_roots_bitmaps_code_def
    ,stack_allocTheory.word_gen_gc_partial_move_list_code_def
    ,stack_allocTheory.word_gen_gc_partial_move_ref_list_code_def
    ,stack_allocTheory.word_gen_gc_partial_move_data_code_def
    ,stack_allocTheory.word_gen_gc_move_code_def
    ,stack_allocTheory.word_gen_gc_move_bitmap_code_def
    ,stack_allocTheory.word_gen_gc_move_bitmaps_code_def
    ,stack_allocTheory.word_gen_gc_move_roots_bitmaps_code_def
    ,stack_allocTheory.word_gen_gc_move_list_code_def
    ,stack_allocTheory.word_gen_gc_move_data_code_def
    ,stack_allocTheory.word_gen_gc_move_refs_code_def
    ,stack_allocTheory.word_gen_gc_move_loop_code_def
    ,stack_allocTheory.clear_top_inst_def
      (* ---- stack_remove ---- *)
    ,stack_removeTheory.max_stack_alloc_def
    ,stack_removeTheory.upshift_def
    ,stack_removeTheory.compile_def
    ,stack_removeTheory.init_stubs_def
    ,stack_removeTheory.init_code_def
    ,stack_removeTheory.store_init_def
    ,stack_removeTheory.init_memory_def
    ,stack_removeTheory.store_list_code_def
    ,stack_removeTheory.halt_inst_def
    ,stack_removeTheory.prog_comp_def
    ,stack_removeTheory.comp_def
    ,stack_removeTheory.stack_load_def
    ,stack_removeTheory.stack_store_def
    ,stack_removeTheory.downshift_def
    ,stack_removeTheory.store_offset_def
    ,stack_removeTheory.stack_free_def
    ,stack_removeTheory.single_stack_free_def
    ,stack_removeTheory.stack_alloc_def
    ,stack_removeTheory.single_stack_alloc_def
    ,stack_removeTheory.stack_err_lab_def
    ,stack_removeTheory.store_length_def
    ,stack_removeTheory.store_list_def
    ,stack_removeTheory.store_pos_def
    ,stack_removeTheory.word_offset_def
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
    ,stack_namesTheory.ri_find_name_def
    ,stack_namesTheory.inst_find_name_def
    ,stack_namesTheory.dest_find_name_def
    ,stack_namesTheory.comp_def
    ,stack_namesTheory.prog_comp_def
    ,stack_namesTheory.compile_def
    (* ---- stack_to_lab ---- *)
    ,stack_to_labTheory.is_gen_gc_def
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
    ,``:'a asm_or_cbw``
    ,``:'a line``
    ,``:'a sec``
    ]
  ,computeLib.Defs
    [labLangTheory.Section_num_def
    ,labLangTheory.Section_lines_def
      (* ---- lab_filter ---- *)
    ,lab_filterTheory.not_skip_def
    ,lab_filterTheory.filter_skip_def
      (* ---- lab_to_target ---- *)
    ,lab_to_targetTheory.ffi_offset_def
    ,lab_to_targetTheory.lab_inst_def
    ,lab_to_targetTheory.cbw_to_asm_def
    ,lab_to_targetTheory.enc_line_def
    ,lab_to_targetTheory.enc_sec_def
    ,lab_to_targetTheory.enc_sec_list_def
    ,lab_to_targetTheory.section_labels_def
    ,lab_to_targetTheory.compute_labels_alt_def
    ,lab_to_targetTheory.find_pos_def
    ,lab_to_targetTheory.get_label_def
    ,lab_to_targetTheory.get_jump_offset_def
    ,lab_to_targetTheory.enc_lines_again_def
    ,lab_to_targetTheory.enc_secs_again_def
    ,lab_to_targetTheory.lines_upd_lab_len_def
    ,lab_to_targetTheory.upd_lab_len_def
    ,lab_to_targetTheory.line_ok_light_def
    ,lab_to_targetTheory.sec_ok_light_def
    ,lab_to_targetTheory.pad_bytes_def
    ,lab_to_targetTheory.add_nop_def
    ,lab_to_targetTheory.pad_section_def
    ,lab_to_targetTheory.pad_code_def
    ,lab_to_targetTheory.remove_labels_loop_def
    ,lab_to_targetTheory.remove_labels_def
    ,lab_to_targetTheory.line_bytes_def
    ,lab_to_targetTheory.prog_to_bytes_def
    ,lab_to_targetTheory.find_ffi_names_def
    ,lab_to_targetTheory.list_add_if_fresh_def
    ,lab_to_targetTheory.get_ffi_index_def
    ,lab_to_targetTheory.sec_length_def
    ,lab_to_targetTheory.compile_lab_def
    ,lab_to_targetTheory.compile_def
      (* ---- Everything in backend theory ---- *)
    ,backendTheory.attach_bitmaps_def
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
    [
     ``:architecture``
    ,``:'a asm_config``
    ,``:'a reg_imm``
    ,``:binop``
    ,``:cmp``
    ,``:shift``
    ,``:'a arith``
    ,``:'a addr``
    ,``:memop``
    ,``:'a inst``
    ,``:'a asm``
    ]
  ,computeLib.Extenders
    [basicComputeLib.add_basic_compset
    ,basisComputeLib.add_basis_compset
    ,semanticsComputeLib.add_ast_compset
    ,semanticsComputeLib.add_namespace_compset
    ,reg_allocComputeLib.add_reg_alloc_compset
    ]
  ]

end

end
