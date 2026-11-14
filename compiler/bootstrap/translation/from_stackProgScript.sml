(*
  Translate the backend from stackLang to target code.
*)
Theory from_stackProg[no_sig_docs]
Ancestors
  evaluate ml_translator from_labProg std_prelude stack_alloc
  stack_remove stack_names stack_to_lab
Libs
  preamble ml_translatorLib

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = translation_extends "from_labProg";
val _ = ml_translatorLib.use_sub_check true;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "from_stackProg");

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";

Theorem NOT_NIL_AND_LEMMA[local]:
  (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val {Thy,Name,...} = dest_thy_const tm
  val def = DB.fetch Thy (Name ^ "_pmatch") handle HOL_ERR _ =>
            DB.fetch Thy (Name ^ "_def") handle HOL_ERR _ =>
            DB.fetch Thy (Name ^ "_DEF") handle HOL_ERR _ =>
            DB.fetch Thy (Name ^ "_thm") handle HOL_ERR _ =>
            DB.fetch Thy Name
  val insts = match_type (type_of (prim_mk_const {Thy = Thy, Name = Name}))
                         (type_of tm)
  in def |> INST_TYPE insts |> REWRITE_RULE (!extra_preprocessing)
         |> CONV_RULE (DEPTH_CONV BETA_CONV)
         |> REWRITE_RULE [NOT_NIL_AND_LEMMA] end;

val _ = find_def_for_const := def_of_const;
val _ = use_long_names := true;

val _ = translate stack_to_labTheory.is_gen_gc_def;

(* stack_rawcall *)

val res = translate (stack_rawcallTheory.dest_case_pmatch);
val res = translate (stack_rawcallTheory.comp_seq_def);
val res = translate (stack_rawcallTheory.seq_stack_alloc_pmatch);
val res = translate (stack_rawcallTheory.collect_info_def);
val res = translate (stack_rawcallTheory.comp_pmatch);
val res = translate (stack_rawcallTheory.comp_top_pmatch);
val res = translate (stack_rawcallTheory.compile_def);

val inline_simp = SIMP_RULE std_ss [backend_commonTheory.word_shift_def]
val _ = translate (stack_allocTheory.SetNewTrigger_def |> inline_simp)
val _ = translate (stack_allocTheory.clear_top_inst_def)
val _ = translate (stack_allocTheory.memcpy_code_def |> inline_simp)
val _ = translate (stack_allocTheory.word_gc_move_code_def |> inline_simp)

val _ = translate (stack_allocTheory.word_gc_move_bitmap_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gc_move_bitmaps_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gc_move_roots_bitmaps_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gc_move_list_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gc_move_loop_code_def |> inline_simp);

val _ = translate (stack_allocTheory.word_gen_gc_move_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gen_gc_move_bitmap_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gen_gc_move_bitmaps_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gen_gc_move_roots_bitmaps_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gen_gc_move_list_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gen_gc_move_data_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gen_gc_move_refs_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gen_gc_move_loop_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_bitmap_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_bitmaps_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_roots_bitmaps_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_list_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_ref_list_code_def |> inline_simp);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_data_code_def |> inline_simp);
val r = translate (stack_allocTheory.word_gc_partial_or_full_def |> INST_TYPE [alpha|->``:num``]);

val r = translate (stack_allocTheory.word_gc_code_def |> inline_simp);

val _ = translate (stack_allocTheory.stubs_def);

val _ = translate (stack_allocTheory.comp_def(*pmatch*));

val _ = translate (stack_allocTheory.compile_def);

val each_def =
  stack_removeTheory.copy_each_def |> inline_simp;
val loop_def =
  (stack_removeTheory.copy_loop_def |> inline_simp
    |> REWRITE_RULE [GSYM each_def]);

val _ = translate each_def;
val _ = translate loop_def;

(* Might be better to inline this *)
val _ = translate (stack_removeTheory.word_offset_def)
val _ = translate (stack_removeTheory.store_offset_def |> SIMP_RULE std_ss [word_mul_def,word_2comp_def])

val _ = translate (stack_removeTheory.comp_def |> inline_simp)

val _ = translate (stack_removeTheory.prog_comp_def)

val _ = translate (stack_removeTheory.store_list_code_def |> inline_simp)
val _ = translate (stack_removeTheory.init_memory_def |> inline_simp)
val _ = translate (stack_removeTheory.init_code_def |> inline_simp |> SIMP_RULE std_ss [word_mul_def]|>SIMP_RULE std_ss[w2n_n2w])

val _ = translate (stack_removeTheory.compile_def)

val _ = translate (stack_namesTheory.comp_def)
val _ = translate (stack_namesTheory.prog_comp_def)
val _ = translate (stack_namesTheory.compile_def)

val _ = translate (stack_to_labTheory.flatten_def)

val _ = translate (stack_to_labTheory.is_Seq_def)

val _ = translate (stack_to_labTheory.compile_def)

val _ = translate (stack_to_labTheory.compile_no_stubs_def)

val _ = translate $ SIMP_RULE std_ss
  [data_to_wordTheory.max_heap_limit_def, backend_commonTheory.word_shift_def]
  backendTheory.from_stack_def;

val r = presLangTheory.store_name_to_display_def |> translate;
val res = presLangTheory.stack_prog_to_display_def
          |> REWRITE_RULE [presLangTheory.string_imp_def] |> translate;
val res = presLangTheory.stack_fun_to_display_def |> translate;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
val _ = ml_translatorLib.clean_on_exit := true;
