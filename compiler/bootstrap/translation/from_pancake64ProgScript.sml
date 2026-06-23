(*
  Translate the pan_to_target part of the 64-bit compiler.
*)
Theory from_pancake64Prog
Ancestors
  ml_translator to_target64Prog std_prelude panLang crepLang
  pan_simp loopLang loop_to_word pan_to_crep
  loop_call loop_live crep_arith crep_to_loop pan_to_word
  word_to_word backend pan_to_target panPtreeConversion
  pan_globals crep_inline pan_structs
Libs
  preamble ml_translatorLib

open preamble;
open ml_translatorLib ml_translatorTheory;
open to_target64ProgTheory std_preludeTheory;

val _ = translation_extends "to_target64Prog";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "from_pancake64Prog");
val _ = ml_translatorLib.use_sub_check true;

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";

Theorem NOT_NIL_AND_LEMMA[local]:
  (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

Theorem option_map_thm[local]:
  OPTION_MAP f x = case x of NONE => NONE | SOME y => SOME(f y)
Proof
  Cases_on ‘x’ \\ rw[]
QED

val extra_preprocessing = ref [MEMBER_INTRO,MAP,parserProgTheory.OPTION_BIND_THM,option_map_thm];

fun preprocess def =
def |> RW (!extra_preprocessing)
    |> CONV_RULE (DEPTH_CONV BETA_CONV)
    |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
    |> REWRITE_RULE [NOT_NIL_AND_LEMMA];

val matches = ref ([]: term list);

fun def_of_const tm = let
val res = dest_thy_const tm handle HOL_ERR _ =>
  failwith ("Unable to translate: " ^ term_to_string tm)
val name = (#Name res)
fun def_from_thy thy name =
DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
  DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
      DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
        DB.fetch thy name
val def = def_from_thy (#Thy res) name handle HOL_ERR _ =>
  failwith ("Unable to find definition of " ^ name)

val insts = if exists (fn term => can (find_term (can (match_term term))) (concl def))
                      (!matches)
            then [alpha |-> ``:64``,beta|->``:64``] else []

val def = def |> RW (!extra_preprocessing)
              |> INST_TYPE insts
              |> CONV_RULE (DEPTH_CONV BETA_CONV)
              (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
              |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
                      in def end

val _ = (find_def_for_const := def_of_const);

val _ = use_long_names:=true;

val spec64 = INST_TYPE[alpha|->``:64``]

val conv64 = GEN_ALL o CONV_RULE (wordsLib.WORD_CONV) o spec64 o SPEC_ALL

val conv64_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec64 o SPEC_ALL

val gconv = CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV)

val econv = CONV_RULE wordsLib.WORD_EVAL_CONV

val _ = matches:= [``foo:'a wordLang$prog``,``foo:'a wordLang$exp``,``foo:'a word``,
                   ``foo: 'a reg_imm``,``foo:'a arith``,``foo: 'a addr``,
                   ``foo:'a stackLang$prog``, “foo:'a pan_to_crep$context”]

open panLangTheory;

val _ = register_type “:64 panLang$exp”;

val _ = register_type “:64 panLang$prog”;

val _ = register_type “:64 panLang$decl”;

val _ = translate $ size_of_sh_with_ctxt_def;

val _ = translate $ shape_to_str_def;

val _ = translate $ spec64 exp_ids_def;

open crepLangTheory;

val _ = register_type “:64 crepLang$exp”;

val _ = register_type “:64 crepLang$prog”;

val _ = translate $ spec64 var_cexp_def;

val _ = translate $ spec64 nested_decs_def;

val _ = translate $ spec64 nested_seq_def;

Theorem lem[local]:
  dimindex(:64) = 64
Proof
  EVAL_TAC
QED

val _ = translate $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] $ spec64 stores_def;

val _ = translate $ spec64 store_globals_def;

val _ = translate $ spec64 load_globals_def;

val _ = translate $ spec64 assign_ret_def;

val _ = translate $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] $ spec64 load_shape_def;

open pan_simpTheory;

val _ = translate $ spec64 SmartSeq_def;

val _ = translate $ spec64 seq_assoc_def;

val _ = translate $ spec64 seq_call_ret_def;

val _ = translate $ conv64 ret_to_tail_def;

val _ = translate $ conv64 compile_def;

val _ = translate $ conv64 compile_prog_def;

open pan_structsTheory;

val _ = translate $ compile_shape_def;

val _ = translate $ afindi_def;

val _ = translate $ conv64 old_exp_shape_def;

val _ = translate $ conv64 compile_exp_def;

val _ = translate $ conv64 compile_def;

val _ = translate $ conv64 compile_decs_def;

val _ = translate $ conv64 get_names_def;

val _ = translate $ conv64 compile_top_def;

open pan_globalsTheory;

val _ = register_type “:64 pan_globals$context”;

val _ = translate $ conv64 compile_exp_def;

val _ = translate $ fresh_name_def;

val _ = translate $ conv64 var_exp_def;

val _ = translate $ conv64 free_var_ids_def;

val _ = translate $ conv64 shape_val_def;

val _ = translate $ conv64 compile_def;

val _ = translate size_of_shape_def;

val _ = translate_no_ind $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] $ conv64 compile_decs_def;

Theorem pan_globals_compile_decs_ind[local]:
  pan_globals_compile_decs_ind
Proof
  once_rewrite_tac [fetch "-" "pan_globals_compile_decs_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD,bytes_in_word_def]
QED

val _ = pan_globals_compile_decs_ind |> update_precondition;

val _ = translate $ spec64 is_function_def;

val _ = translate $ spec64 resort_decls_def;

val _ = translate fperm_name_def;

val _ = translate $ spec64 fperm_def;

val _ = translate $ spec64 fperm_decs_def;

val _ = translate $ spec64 functions_def;

val _ = translate $ spec64 new_main_name_def;

val _ = translate $ spec64 dec_shapes_def;

val _ = translate $ spec64 panLangTheory.nested_seq_def;

val _ = translate $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] $ spec64 compile_top_def;

open loopLangTheory;

val _ = register_type “:64 loopLang$exp”;

val _ = register_type “:64 loopLang$prog”;

val _ = translate $ spec64 acc_vars_def;

val _ = translate $ spec64 nested_seq_def;

open loop_to_wordTheory;

val _ = translate $ spec64 comp_exp_def;

val _ = translate $ spec64 find_reg_imm_def;

val _ = translate $ spec64 comp_def;

val _ = translate $ spec64 comp_func_def;

val _ = translate $ spec64 compile_prog_def;

val _ = translate $ spec64 compile_def;

open crep_inlineTheory;

val _ = translate $ spec64 panLangTheory.inlinable_def;

val _ = translate $ spec64 var_prog_def;

val _ = translate $ spec64 vmax_prog_def;

val _ = translate $ spec64 has_return_def;

val _ = translate $ spec64 return_in_loop_def;

val _ = translate $ spec64 transform_rec_def;

val _ = translate $ spec64 arg_load_def;

val _ = translate $ spec64 not_branch_ret_def;

val _ = translate $ spec64 unreach_elim_def;

val _ = translate $ spec64 standalone_eoc_def;

val _ = translate $ spec64 assign_eoc_def;

val _ = translate $ spec64 standalone_branch_def;

val _ = translate $ spec64 assign_branch_def;

val _ = translate $ spec64 inline_tail_def;

val _ = translate $ spec64 inline_standalone_eoc_def;

val _ = translate $ spec64 inline_assign_eoc_def;

val _ = translate $ spec64 inline_standalone_branch_def;

val _ = translate $ spec64 inline_assign_branch_def;

val _ = translate $ spec64 inline_prog_def;

val _ = translate $ INST_TYPE[alpha|->``:num list``,beta|->``:64``] compile_inl_prog_def;

val _ = translate $ spec64 compile_inl_top_def;

open pan_to_crepTheory;

val _ = translate $ spec64 ret_hdl_def;

val _ = translate $ INST_TYPE[alpha|->“:num”] ret_var_def;

val _ = translate $ INST_TYPE[alpha|->“:64 crepLang$exp”] cexp_heads_def;

val _ = translate $ spec64 comp_field_def;

val _ = translate $ spec64 exp_hdl_def;

val _ = translate $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem]
                  $ INST_TYPE[alpha|->“:64”,
                              beta|->“:64”]
                  compile_exp_def;

val res = translate_no_ind $ spec64 compile_def;

val ind_lemma = Q.prove(
  `^(hd (hyp res))`,
  PURE_REWRITE_TAC [fetch "-" "pan_to_crep_compile_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum (match_mp_tac o MP_CANON)
  \\ rpt strip_tac
  \\ FULL_SIMP_TAC bool_ss[panLangTheory.prog_11, panLangTheory.prog_distinct]
  \\ rveq
  \\ metis_tac []) |> update_precondition;

val _ = translate $ spec64 mk_ctxt_def;

val _ = translate $ spec64 comp_func_def;

val _ = translate $ make_funcs_def;

val _ = translate $ INST_TYPE[alpha|->“:64”,
                              beta|->“:mlstring”,
                              gamma|->“:(mlstring # shape) list”,
                              delta|->“:64”] get_eids_def;

val _ = translate $ spec64 compile_to_crep_def;

val _ = translate $ spec64 compile_prog_def;

open loop_callTheory;

val _ = translate $ spec64 comp_def;

open loop_liveTheory;

val _ = translate $ spec64 vars_of_exp_def;

val res = translate $ spec64 shrink_def;

val _ = translate $ spec64 mark_all_def;

val _ = translate $ spec64 comp_def;

val _ = translate $ spec64 optimise_def;

open crep_arithTheory;

val _ = translate $ spec64 dest_const_def;

val _ = translate $ spec64 dest_2exp_def;

val _ = translate $ spec64 mul_const_def;

val _ = translate $ spec64 simp_exp_def;

val _ = translate $ spec64 simp_prog_def;

open crep_to_loopTheory;

val _ = translate $ spec64 prog_if_def;

val _ = translate $ spec64 compile_crepop_def;

val _ = translate $ spec64 compile_exp_def;

val _ = translate $ spec64 compile_def;

val _ = translate $ spec64 comp_func_def;

val _ = translate $ make_funcs_def;

val _ = translate $ spec64 compile_prog_def;

open pan_to_wordTheory;

val _ = translate $ spec64 compile_prog_def;

open word_to_wordTheory;

(* TODO: duplicate *)
val _ = translate $ spec64 compile_single_def;

val _ = translate $ spec64 full_compile_single_def;

val _ = translate $ spec64 compile_def;

open backendTheory;

(* TODO: duplicated from compiler64ProgScript. *)
val _ = translate $ INST_TYPE[alpha|->“:word8 list”,
                              beta|->“:word64 list”,
                              gamma|->“:64”,
                              delta|->“:64”] attach_bitmaps_def;

val _ = translate $ INST_TYPE[alpha|->“:64 word list”,
                              beta|->“:64”] from_lab_def;

val _ = translate $ SIMP_RULE std_ss [dimword_def,lem,backend_commonTheory.word_shift_def]
                  $ SIMP_RULE std_ss [data_to_wordTheory.max_heap_limit_def]
                  $ INST_TYPE[alpha|->“:64”,
                              beta|->“:64 word list”] from_stack_def;

val _ = translate $ spec64 from_word_def;

open pan_to_targetTheory;

val _ = translate $ spec64 exports_def;

val _ = translate $ spec64 compile_prog_def;

(* ptree conversion *)

open panPtreeConversionTheory;

val res = translate argsNT_def;

val res = translate destLf_def;

val res = translate destTOK_def;

val res = translate conv_ident_def;

val res = translate conv_ffi_ident_def;

val res = translate isNT_def;

val res = translate conv_int_def;

Theorem conv_const_thm:
  conv_const t =
  case conv_int t of NONE => (NONE:'a panLang$exp option)
                  | SOME x => SOME(Const(i2w x))
Proof
  Cases_on ‘conv_int t’ \\ rw[conv_const_def]
QED

val res = translate $ spec64 conv_const_thm;

val res = translate conv_nat_def;

Theorem conv_nat_side[local]:
  ∀x. panptreeconversion_conv_nat_side x
Proof
  rw [fetch "-" "panptreeconversion_conv_nat_side_def"]
  >> gs[integerTheory.INT_GE_CALCULATE]
QED

val _ = update_precondition conv_nat_side;


val res = translate $ PURE_REWRITE_RULE [option_map_thm] $ spec64 conv_var_def;

val res = translate $ conv_shift_def;

Overload ptree_size[local] = ``parsetree_size (K 0) (K 0) (K 0)``;

val res = translate $ conv_default_shape_def;

Theorem OPT_MMAP_eq_MAP[local]:
  OPT_MMAP f xs = (OPT_MMAP I o MAP f) xs
Proof
  simp [miscTheory.OPT_MMAP_MAP_o]
QED

val res = translate $ listTheory.OPT_MMAP_def;

val res = conv_Shape_def
  |> REWRITE_RULE [OPT_MMAP_eq_MAP, parserProgTheory.OPTION_BIND_THM, option_map_thm]
  |> SIMP_RULE bool_ss [o_DEF]
  |> translate

Theorem panptreeconversion_conv_shape_side[local]:
  !sh. panptreeconversion_conv_shape_side sh
Proof
  recInduct conv_Shape_ind
  >> rw []
  >> ONCE_REWRITE_TAC [fetch "-" "panptreeconversion_conv_shape_side_def"]
  >> rw []
  >> intLib.COOPER_TAC
QED

val _ = update_precondition panptreeconversion_conv_shape_side;

val res = translate $ conv_binop_def;

Theorem OPTION_MAP2_thm[local]:
  OPTION_MAP2 f x y =
  case x of
    NONE => NONE
  | SOME x =>
      (case y of
         NONE => NONE
       | SOME y => SOME(f x y))
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’ \\ rw[]
QED

Theorem FOLDR_eta[local]:
  FOLDR (λt. f t) = FOLDR (λt e. f t e)
Proof
  CONV_TAC(DEPTH_CONV ETA_CONV) \\ rw[]
QED

val res = translate conv_cmp_def;

val res = translate kw_def;

val res = translate $ spec64 isSubOp_def;

val res = translate $ preprocess $ spec64 conv_Shift_def;

val res = translate $ conv_panop_def;


val res = conv_Exp_def
  |> REWRITE_RULE [OPT_MMAP_eq_MAP, parserProgTheory.OPTION_BIND_THM, option_map_thm]
  |> SIMP_RULE bool_ss [o_DEF]
  |> spec64
  |> time translate_no_ind

Theorem panptreeconversion_conv_arglist_ind[local]:
  panptreeconversion_conv_arglist_ind (: 'b)
Proof
  ONCE_REWRITE_TAC [fetch "-" "panptreeconversion_conv_arglist_ind_def"]
  >> rpt gen_tac
  >> disch_then strip_assume_tac
  >> rpt (qpat_x_assum `!x. _` (assume_named_tac "forall_IH"))
  >> ho_match_mp_tac conv_Exp_ind
  >> rpt strip_tac
  >> rpt (label_x_assum "forall_IH" irule ORELSE label_x_assum "forall_IH" kall_tac)
  >> simp []
  >> simp [DISJ_IMP_THM]
  (* down to only a couple of goals *)
  >> rw []
  >> gs []
QED

val _ = update_precondition panptreeconversion_conv_arglist_ind;

val res = translate $ spec64 $ SIMP_RULE std_ss [option_map_thm, OPTION_MAP2_thm] conv_NonRecStmt_def;

val res = translate $ spec64 $ add_locs_annot_def;

val res = translate butlast_def;

val res = translate $ spec64 $ conv_Dec_def;

val res = translate $ spec64 $ conv_GlobalDec_def;

val res = translate $ spec64 $ conv_DecCall_def;

val res = preprocess $ spec64 conv_Prog_def |> translate_no_ind;

Theorem conv_Prog_ind:
  panptreeconversion_conv_handle_ind
Proof
  PURE_REWRITE_TAC [fetch "-" "panptreeconversion_conv_handle_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (spec64 $ latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac \\ simp[]
  \\ fs[]
QED

val _ = conv_Prog_ind  |> update_precondition;

val res = translate $ conv_inline_def;

val res  = translate $ conv_export_def;

val res = translate $ conv_FieldNameList_def;

val res = translate $ conv_StructName_def;

val res = translate_no_ind $ spec64 conv_TopDec_def;

val res = translate_no_ind $ spec64 conv_TopDecList_def;

Theorem panptreeconversion_conv_topdeclist_ind[local]:
  panptreeconversion_conv_topdeclist_ind
Proof
  once_rewrite_tac [fetch "-" "panptreeconversion_conv_topdeclist_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac $ spec64 conv_TopDecList_ind
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD]
QED

val _ = panptreeconversion_conv_topdeclist_ind |> update_precondition;

val res = translate $ spec64 panLexerTheory.dest_lexErrorT_def;

val res = translate $ spec64 collect_globals_def;

val res = translate $ spec64 localise_exp_def;

val res = translate_no_ind $ preprocess $ spec64 localise_prog_def;

Theorem panptreeconversion_localise_prog_ind[local]:
  panptreeconversion_localise_prog_ind
Proof
  once_rewrite_tac [fetch "-" "panptreeconversion_localise_prog_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac localise_prog_ind
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD]
QED

val _ = panptreeconversion_localise_prog_ind |> update_precondition;

val res = translate $ spec64 localise_topdec_def;

val res = translate $ spec64 localise_topdecs_def;

val res = translate $ spec64 parse_topdecs_to_ast_def;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
