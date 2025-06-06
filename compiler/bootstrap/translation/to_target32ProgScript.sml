(*
  Translate the final part of the compiler backend for 32-bit targets.
*)
open preamble;
open evaluateTheory
open ml_translatorLib ml_translatorTheory;
open to_word32ProgTheory std_preludeTheory;

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "to_target32Prog"

val _ = translation_extends "to_word32Prog";
val _ = ml_translatorLib.use_string_type true;
val _ = ml_translatorLib.use_sub_check true;

val () = computeLib.set_skip computeLib.the_compset “COND” (SOME 1);

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "to_target32Prog");

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";

Triviality NOT_NIL_AND_LEMMA:
  (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

val matches = ref ([]: term list);
val inst_tyargs = ref ([]:hol_type list);

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

  val insts = if exists (fn term => can (find_term (can (match_term term))) (concl def)) (!matches) then map (fn x => x |-> ``:32``) (!inst_tyargs)  else []

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

val spec32 = INST_TYPE[alpha|->``:32``]

val conv32 = GEN_ALL o CONV_RULE (wordsLib.WORD_CONV) o spec32 o SPEC_ALL

val conv32_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec32 o SPEC_ALL

val gconv = CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV)

val econv = CONV_RULE wordsLib.WORD_EVAL_CONV

val _ = matches:= [``foo:'a wordLang$prog``,``foo:'a wordLang$exp``,``foo:'a word``,``foo: 'a reg_imm``,``foo:'a arith``,``foo: 'a addr``,``foo:'a stackLang$prog``]

val _ = inst_tyargs := [alpha]

open word_to_stackTheory

val r = translate (chunk_to_bits_def |> conv32);
val r = translate (chunk_to_bitmap_def |> conv32);
Theorem const_words_to_bitmap_ind = const_words_to_bitmap_ind |> conv32;
val r = translate (const_words_to_bitmap_def |> conv32);

val _ = translate (conv32 write_bitmap_def|> (RW (!extra_preprocessing)))

(* TODO: The paired let trips up the translator's single line def mechanism, unable to find a smaller failing example yet *)
val _ = translate (conv32 (wLive_def |> SIMP_RULE std_ss [LET_THM]))

(* TODO: the name is messed up (pair_) *)
val _ = translate PAIR_MAP

val _ = translate parmoveTheory.fstep_def

val parmove_fstep_side = Q.prove(`
  ∀x. parmove_fstep_side x ⇔ T`,
  EVAL_TAC>>rw[]>>Cases_on`v18`>>fs[]) |> update_precondition

val _ = translate (spec32 word_to_stackTheory.wMove_def)

val _ = translate (spec32 call_dest_def)

val _ = translate (wInst_def |> conv32)
val _ = translate (spec32 comp_def)

val _ = translate (compile_word_to_stack_def |> INST_TYPE [beta |-> ``:32``])

val _ = translate (compile_def |> INST_TYPE [alpha|->``:32``,beta|->``:32``]);

(* stack_rawcall *)

val res = translate (stack_rawcallTheory.dest_case_pmatch |> conv32);
val res = translate (stack_rawcallTheory.comp_seq_def |> conv32);
val res = translate (stack_rawcallTheory.seq_stack_alloc_pmatch |> conv32);
val res = translate (stack_rawcallTheory.collect_info_def |> conv32);
val res = translate (stack_rawcallTheory.comp_pmatch |> conv32);
val res = translate (stack_rawcallTheory.comp_top_pmatch |> conv32);
val res = translate (stack_rawcallTheory.compile_def |> conv32);

open stack_allocTheory

val inline_simp = SIMP_RULE std_ss [bytes_in_word_def,
                                    backend_commonTheory.word_shift_def]
val _ = translate (SetNewTrigger_def |> inline_simp |> conv32)
val _ = translate (conv32 clear_top_inst_def)
val _ = translate (memcpy_code_def |> inline_simp |> conv32)
val _ = translate (word_gc_move_code_def |> inline_simp |> conv32)

val _ = translate (word_gc_move_bitmap_code_def |> inline_simp |> conv32);
val _ = translate (word_gc_move_bitmaps_code_def |> inline_simp |> conv32);
val _ = translate (word_gc_move_roots_bitmaps_code_def |> inline_simp |> conv32);
val _ = translate (word_gc_move_list_code_def |> inline_simp |> conv32);
val _ = translate (word_gc_move_loop_code_def |> inline_simp |> conv32);

val _ = translate (stack_allocTheory.word_gen_gc_move_code_def |> inline_simp |> conv32);
val _ = translate (stack_allocTheory.word_gen_gc_move_bitmap_code_def |> inline_simp |> conv32);
val _ = translate (stack_allocTheory.word_gen_gc_move_bitmaps_code_def |> inline_simp |> conv32);
val _ = translate (stack_allocTheory.word_gen_gc_move_roots_bitmaps_code_def |> inline_simp |> conv32);
val _ = translate (stack_allocTheory.word_gen_gc_move_list_code_def |> inline_simp |> conv32);
val _ = translate (stack_allocTheory.word_gen_gc_move_data_code_def |> inline_simp |> conv32);
val _ = translate (stack_allocTheory.word_gen_gc_move_refs_code_def |> inline_simp |> conv32);
val _ = translate (stack_allocTheory.word_gen_gc_move_loop_code_def |> inline_simp |> conv32);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_code_def |> inline_simp |> conv32);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_bitmap_code_def |> inline_simp |> conv32);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_bitmaps_code_def |> inline_simp |> conv32);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_roots_bitmaps_code_def |> inline_simp |> conv32);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_list_code_def |> inline_simp |> conv32);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_ref_list_code_def |> inline_simp |> conv32);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_data_code_def |> inline_simp |> conv32);
val r = translate (stack_allocTheory.word_gc_partial_or_full_def |> inline_simp |> conv32);
val r = translate (stack_allocTheory.word_gc_code_def |> inline_simp |> conv32);

val _ = translate (spec32 stubs_def);

val _ = translate (spec32 comp_def(*pmatch*));

val _ = translate (spec32 compile_def);

(*
val stack_alloc_comp_side = Q.prove(`
  ∀n m prog. stack_alloc_comp_side n m prog ⇔ T`,
`(∀prog n m. stack_alloc_comp_side n m prog ⇔ T) ∧
 (∀opt prog (x:num) (y:num) (z:num) n m. opt = SOME(prog,x,y,z) ⇒ stack_alloc_comp_side n m prog ⇔ T) ∧
 (∀opt prog (x:num) (y:num) (z:num) n m. opt = (prog,x,y,z) ⇒ stack_alloc_comp_side n m prog ⇔ T) ∧
 (∀opt prog (x:num) (y:num) n m. opt = SOME(prog,x,y) ⇒ stack_alloc_comp_side n m prog ⇔ T) ∧
 (∀opt prog (x:num) (y:num) n m. opt = (prog,x,y) ⇒ stack_alloc_comp_side n m prog ⇔ T)`
  suffices_by fs[]
  >> ho_match_mp_tac(TypeBase.induction_of ``:32 stackLang$prog``)
  >> fs[]
  >> rpt strip_tac
  >> rw[Once(fetch "-" "stack_alloc_comp_side_def")]
  >> fs[]
  >> metis_tac[option_nchotomy, pair_CASES]) |> update_precondition

val stack_alloc_prog_comp_side = Q.prove(`∀prog. stack_alloc_prog_comp_side prog ⇔ T`,
  fs[fetch "-" "stack_alloc_prog_comp_side_def", stack_alloc_comp_side]) |> update_precondition;

val stack_alloc_compile_side = Q.prove(`∀conf prog. stack_alloc_compile_side conf prog ⇔ T`,
  fs[fetch "-" "stack_alloc_compile_side_def", stack_alloc_prog_comp_side]) |> update_precondition;
*)

open stack_removeTheory

val each_def =
  copy_each_def |> inline_simp |> conv32 |> SPEC_ALL |> CONV_RULE (RAND_CONV EVAL);
val loop_def =
  (copy_loop_def |> inline_simp |> conv32 |> SPEC_ALL |> CONV_RULE (RAND_CONV EVAL)
    |> REWRITE_RULE [GSYM each_def]);

val _ = translate each_def;
val _ = translate loop_def;

(* Might be better to inline this *)
val _ = translate (conv32 word_offset_def)
val _ = translate (conv32 store_offset_def |> SIMP_RULE std_ss [word_mul_def,word_2comp_def] |> conv32)

val _ = translate (comp_def |> inline_simp |> conv32)

val _ = translate (prog_comp_def |> INST_TYPE [beta|->``:32``])

val _ = translate (store_list_code_def |> inline_simp |> conv32)
val _ = translate (init_memory_def |> inline_simp |> conv32)
val _ = translate (init_code_def |> inline_simp |> conv32 |> SIMP_RULE std_ss [word_mul_def]|>gconv|>SIMP_RULE std_ss[w2n_n2w] |> conv32)

val _ = translate (spec32 compile_def)

open stack_namesTheory

val _ = translate (spec32 comp_def)
val _ = translate (prog_comp_def |> INST_TYPE [beta |-> ``:32``])
val _ = translate (compile_def |> INST_TYPE [beta |-> ``:32``])

open stack_to_labTheory

val _ = matches := [``foo:'a labLang$prog``,``foo:'a
  labLang$sec``,``foo:'a labLang$line``,``foo:'a
  labLang$asm_with_lab``,``foo:'a labLang$line list``,``foo:'a
  inst``,``foo:'a asm_config``] @ (!matches)

val _ = translate (flatten_def |> spec32)

val _ = translate (stack_to_labTheory.is_Seq_def |> spec32)

val _ = translate (compile_def |> spec32)

val _ = translate (stack_to_labTheory.compile_no_stubs_def |> spec32)

open lab_filterTheory lab_to_targetTheory asmTheory
open monadic_encTheory monadic_enc32Theory ml_monad_translatorLib;

(* The record types used for the monadic state and exceptions *)
val exn_type   = ``:monadic_enc32$state_exn_32``;
val _          = register_exn_type exn_type;
val STATE_EXN_TYPE_def =  theorem "MONADIC_ENC32_STATE_EXN_32_TYPE_def"
val exn_ri_def         = STATE_EXN_TYPE_def;

val exn_functions = [
    (raise_Fail_def, handle_Fail_def),
    (raise_Subscript_def, handle_Subscript_def)
];
val refs_manip_list = [] : (string * thm * thm) list;
val rarrays_manip_list = [] : (string * thm * thm * thm * thm * thm * thm) list;

val add_type_theories  = ([] : string list);
val store_pinv_def_opt = NONE : thm option;

val state_type_32 = ``:enc_state_32``;
val store_hprop_name_32   = "ENC_STATE_32";
val farrays_manip_list_32 = [
    ("hash_tab_32", get_hash_tab_32_def, set_hash_tab_32_def, hash_tab_32_length_def, hash_tab_32_sub_def, update_hash_tab_32_def)];

val _ = translate (hash_reg_imm_def |> INST_TYPE [alpha|->``:32``])
val _ = translate hash_binop_def
val _ = translate hash_cmp_def
val _ = translate hash_shift_def
val _ = translate (hash_arith_def |> INST_TYPE [alpha|->``:32``] |> SIMP_RULE std_ss [roll_hash_def])
val _ = translate hash_memop_def
val _ = translate (hash_fp_def |> SIMP_RULE std_ss [roll_hash_def])
val _ = translate (hash_inst_def |> INST_TYPE [alpha|->``:32``] |> SIMP_RULE std_ss [roll_hash_def])
val _ = translate (hash_asm_def |> INST_TYPE [alpha|->``:32``] |> SIMP_RULE std_ss [roll_hash_def])

(* Initialization *)

val res = start_dynamic_init_fixed_store_translation
            refs_manip_list
            rarrays_manip_list
            farrays_manip_list_32
            store_hprop_name_32
            state_type_32
            exn_ri_def
            exn_functions
            add_type_theories
            store_pinv_def_opt;

val _ = translate (lab_inst_def |> INST_TYPE [alpha |-> ``:32``])
val _ = translate (cbw_to_asm_def |> INST_TYPE [alpha |-> ``:32``])
val _ = m_translate lookup_ins_table_32_def;
val _ = m_translate enc_line_hash_32_def;
val _ = m_translate enc_line_hash_32_ls_def;
val _ = m_translate enc_sec_hash_32_ls_def;
val _ = m_translate enc_sec_hash_32_ls_full_def;

val _ = m_translate_run enc_secs_32_aux_def;

val _ = translate enc_secs_32_def;

Triviality monadic_enc32_enc_line_hash_32_ls_side_def:
  ∀a b c d e.
  d ≠ 0 ⇒
  monadic_enc32_enc_line_hash_32_ls_side a b c d e ⇔ T
Proof
  Induct_on`e`>>
  simp[Once (fetch "-" "monadic_enc32_enc_line_hash_32_ls_side_def")]>>
  EVAL_TAC>>rw[]>>fs[]
QED

Triviality monadic_enc32_enc_sec_hash_32_ls_side_def:
  ∀a b c d e.
  d ≠ 0 ⇒
  monadic_enc32_enc_sec_hash_32_ls_side a b c d e ⇔ T
Proof
  Induct_on`e`>>
  simp[Once (fetch "-" "monadic_enc32_enc_sec_hash_32_ls_side_def")]>>
  metis_tac[monadic_enc32_enc_line_hash_32_ls_side_def]
QED

Theorem monadic_enc32_enc_secs_32_side_def[allow_rebind] = Q.prove(`
  monadic_enc32_enc_secs_32_side a b c ⇔ T`,
  EVAL_TAC>>
  rw[]>>
  metis_tac[monadic_enc32_enc_sec_hash_32_ls_side_def,DECIDE``1n ≠ 0``])
  |> update_precondition;

val _ = translate (spec32 filter_skip_def)

val _ = translate (get_jump_offset_def |>INST_TYPE [alpha|->``:32``,beta |-> ``:32``])

val word_2compl_eq = prove(
  ``!w:'a word. -w = 0w - w``,
  fs []);

val _ = translate (conv32 reg_imm_ok_def |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY,
                                               word_2compl_eq])

val _ = translate (conv32 arith_ok_def |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY])

val _ = translate (fp_ok_def |> conv32)
val _ = translate (conv32 inst_ok_def |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY])

(* TODO: there may be a better rewrite for aligned (in to_word32Prog's translation of offset_ok) *)

val _ = translate (spec32 asmTheory.asm_ok_def)

val res = translate (zero_labs_acc_of_def |> spec32)
val res = translate (line_get_zero_labs_acc_def |> spec32)
val res = translate (sec_get_zero_labs_acc_def |> spec32)
val res = translate (get_zero_labs_acc_def |> spec32)
val res = translate (zero_labs_acc_exist_def |> INST_TYPE[alpha |-> ``:num``, beta |->``:32``])

(* Add in hidden argument to compile_lab *)
Definition remove_labels_hash_def:
  remove_labels_hash init_clock c pos labs ffis hash_size sec_list =
    remove_labels_loop init_clock c pos labs ffis (enc_secs_32 c.encode hash_size sec_list)
End

Triviality remove_labels_hash_correct:
  remove_labels_hash c.init_clock c.asm_conf c.pos c.labels ffis c.hash_size sec_list =
  remove_labels c.init_clock c.asm_conf c.pos c.labels ffis sec_list
Proof
  simp [FUN_EQ_THM, remove_labels_hash_def, remove_labels_def,
        enc_secs_32_correct]
QED

val res = translate (remove_labels_hash_def |> spec32);

val res = translate $ INST_TYPE[alpha|->``:8``] $ get_memop_info_def;
val res = translate_no_ind $ spec32 $ get_shmem_info_def;

Theorem get_shmem_info_ind:
  lab_to_target_get_shmem_info_ind
Proof
  PURE_REWRITE_TAC [fetch "-" "lab_to_target_get_shmem_info_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (spec32 $ latest_ind ())
  \\ rpt strip_tac >>
  TRY (last_x_assum match_mp_tac>>
       rpt strip_tac>>fs[])>>
  gvs[]>>
  qmatch_asmsub_abbrev_tac ‘shmem_info ++ X’>>
  qpat_abbrev_tac ‘RH = shmem_info ++ _’>>
  ‘RH = shmem_info ++ X’ by simp[Abbr ‘RH’, Abbr ‘X’,shmem_rec_component_equality]>>
  fs[Abbr ‘X’]
QED

val _ = get_shmem_info_ind |> update_precondition;

val compile_lab_thm = compile_lab_def
  |> spec32 |> REWRITE_RULE [GSYM remove_labels_hash_correct];

val res = translate compile_lab_thm;
val res = translate (spec32 compile_def)

(* explorer specific functions *)

val res = presLangTheory.asm_cmp_to_display_def |> spec32 |> translate;
val res = presLangTheory.asm_asm_to_display_def |> spec32 |> translate;
val res = presLangTheory.lab_asm_to_display_def |> spec32
          |> REWRITE_RULE [presLangTheory.string_imp_def] |> translate;
val res = presLangTheory.lab_line_to_display_def |> spec32 |> translate;
val res = presLangTheory.lab_fun_to_display_def |> spec32 |> translate;
val res = presLangTheory.stack_prog_to_display_def |> spec32
          |> REWRITE_RULE [presLangTheory.string_imp_def] |> translate;
val res = presLangTheory.stack_fun_to_display_def |> spec32 |> translate;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
