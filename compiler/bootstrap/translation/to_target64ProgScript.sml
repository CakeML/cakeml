open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open to_word64ProgTheory std_preludeTheory;

val _ = new_theory "to_target64Prog"

val _ = translation_extends "to_word64Prog";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "to_target64Prog");

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";

val NOT_NIL_AND_LEMMA = Q.prove(
  `(b <> [] /\ x) = if b = [] then F else x`,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

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

  val insts = if exists (fn term => can (find_term (can (match_term term))) (concl def)) (!matches) then map (fn x => x |-> ``:64``) (!inst_tyargs)  else []

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

val _ = matches:= [``foo:'a wordLang$prog``,``foo:'a wordLang$exp``,``foo:'a word``,``foo: 'a reg_imm``,``foo:'a arith``,``foo: 'a addr``,``foo:'a stackLang$prog``]

val _ = inst_tyargs := [alpha]

open word_to_stackTheory

val _ = translate (conv64 write_bitmap_def|> (RW (!extra_preprocessing)))

(* TODO: The paired let trips up the translator's single line def mechanism, unable to find a smaller failing example yet *)
val _ = translate (conv64 (wLive_def |> SIMP_RULE std_ss [LET_THM]))

local
  val ths = ml_translatorLib.eq_lemmas();
in
  fun find_equality_type_thm tm =
    first (can (C match_term tm) o rand o snd o strip_imp o concl) ths
end

val EqualityType_NUM = find_equality_type_thm``NUM``
val EqualityType_CHAR = find_equality_type_thm``CHAR``
val EqualityType_WORD = find_equality_type_thm``WORD``

val EqualityType_SUM_TYPE_NUM_NUM = find_equality_type_thm``SUM_TYPE NUM NUM``
  |> Q.GENL[`a`,`b`]
  |> Q.ISPECL[`NUM`,`NUM`]
  |> SIMP_RULE std_ss [EqualityType_NUM];

val EqualityType_PAIR_TYPE_NUM_NUM = find_equality_type_thm ``PAIR_TYPE _ _``
  |> Q.GENL[`b`,`c`]
  |> Q.ISPECL[`NUM`,`NUM`]
  |> SIMP_RULE std_ss [EqualityType_NUM];

val EqualityType_PAIR_TYPE_NUM_NUM_NUM = find_equality_type_thm ``PAIR_TYPE _ _``
  |> Q.GENL[`b`,`c`]
  |> Q.ISPECL[`NUM`,`PAIR_TYPE NUM NUM`]
  |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_PAIR_TYPE_NUM_NUM];

val EqualityType_LIST_TYPE_CHAR = find_equality_type_thm``LIST_TYPE CHAR``
  |> Q.GEN`a` |> Q.ISPEC`CHAR` |> SIMP_RULE std_ss [EqualityType_CHAR]

val EqualityType_ASM_CMP_TYPE = find_equality_type_thm``ASM_CMP_TYPE``
  |> SIMP_RULE std_ss []
val EqualityType_ASM_REG_IMM_TYPE = find_equality_type_thm``ASM_REG_IMM_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_WORD]
val EqualityType_AST_SHIFT_TYPE = find_equality_type_thm``AST_SHIFT_TYPE``
  |> SIMP_RULE std_ss []
val EqualityType_ASM_BINOP_TYPE = find_equality_type_thm``ASM_BINOP_TYPE``
  |> SIMP_RULE std_ss []
val EqualityType_ASM_ADDR_TYPE = find_equality_type_thm``ASM_ADDR_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_WORD]
val EqualityType_ASM_MEMOP_TYPE = find_equality_type_thm``ASM_MEMOP_TYPE``
  |> SIMP_RULE std_ss []
val EqualityType_ASM_ARITH_TYPE = find_equality_type_thm``ASM_ARITH_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_AST_SHIFT_TYPE,
                       EqualityType_ASM_BINOP_TYPE,EqualityType_ASM_REG_IMM_TYPE]
val EqualityType_ASM_FP_TYPE = find_equality_type_thm``ASM_FP_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM]
val EqualityType_ASM_INST_TYPE = find_equality_type_thm``ASM_INST_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_WORD,EqualityType_ASM_ADDR_TYPE,
                       EqualityType_ASM_MEMOP_TYPE,EqualityType_ASM_ARITH_TYPE,
                       EqualityType_ASM_FP_TYPE]

val EqualityType_STACKLANG_STORE_NAME_TYPE = find_equality_type_thm``STACKLANG_STORE_NAME_TYPE``
  |> SIMP_RULE std_ss []

val STACKLANG_PROG_TYPE_def = theorem"STACKLANG_PROG_TYPE_def";
val STACKLANG_PROG_TYPE_ind = theorem"STACKLANG_PROG_TYPE_ind";

val STACKLANG_PROG_TYPE_no_closures = Q.prove(
  `∀a b. STACKLANG_PROG_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac STACKLANG_PROG_TYPE_ind
  \\ rw[STACKLANG_PROG_TYPE_def]
  \\ rw[no_closures_def] \\
  TRY (
    qmatch_rename_tac`no_closures y` \\
    qmatch_assum_rename_tac`OPTION_TYPE _ x y` \\
    Cases_on`x` \\ fs[OPTION_TYPE_def] \\ rw[no_closures_def] \\
    qmatch_rename_tac`no_closures y` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x y` \\
    Cases_on`x` \\ fs[PAIR_TYPE_def] \\
    rw[no_closures_def] \\
    metis_tac[EqualityType_def,EqualityType_PAIR_TYPE_NUM_NUM,EqualityType_PAIR_TYPE_NUM_NUM_NUM]) \\
  metis_tac[EqualityType_def,
            EqualityType_NUM,
            EqualityType_LIST_TYPE_CHAR,
            EqualityType_SUM_TYPE_NUM_NUM,
            EqualityType_STACKLANG_STORE_NAME_TYPE,
            EqualityType_ASM_CMP_TYPE,
            EqualityType_ASM_REG_IMM_TYPE,
            EqualityType_WORD |> (INST_TYPE[alpha|->``:5``]),
            EqualityType_ASM_INST_TYPE]);

val ctor_same_type_def = semanticPrimitivesTheory.ctor_same_type_def;

val STACKLANG_PROG_TYPE_types_match = Q.prove(
  `∀a b c d. STACKLANG_PROG_TYPE a b ∧ STACKLANG_PROG_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac STACKLANG_PROG_TYPE_ind
  \\ rw[STACKLANG_PROG_TYPE_def]
  \\ Cases_on`c` \\ fs[STACKLANG_PROG_TYPE_def,types_match_def,ctor_same_type_def]
  \\ rw[] \\
  TRY (
    qmatch_rename_tac`types_match y1 y2` \\
    qmatch_assum_rename_tac`OPTION_TYPE _ x1 y1` \\
    qmatch_assum_rename_tac`OPTION_TYPE _ x2 y2` \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[OPTION_TYPE_def] \\
    rw[types_match_def,ctor_same_type_def] \\
    qmatch_rename_tac`types_match y1 y2` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x1 y1` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x2 y2` \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[PAIR_TYPE_def] \\
    rw[types_match_def,ctor_same_type_def] \\
    metis_tac[EqualityType_def,EqualityType_PAIR_TYPE_NUM_NUM,EqualityType_PAIR_TYPE_NUM_NUM_NUM]) \\
  metis_tac[EqualityType_def,
            EqualityType_NUM,
            EqualityType_LIST_TYPE_CHAR,
            EqualityType_SUM_TYPE_NUM_NUM,
            EqualityType_STACKLANG_STORE_NAME_TYPE,
            EqualityType_ASM_CMP_TYPE,
            EqualityType_ASM_REG_IMM_TYPE,
            EqualityType_WORD |> (INST_TYPE[alpha|->``:5``]),
            EqualityType_ASM_INST_TYPE]);

val STACKLANG_PROG_TYPE_11 = Q.prove(
  `∀a b c d. STACKLANG_PROG_TYPE a b ∧ STACKLANG_PROG_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac STACKLANG_PROG_TYPE_ind
  \\ rw[STACKLANG_PROG_TYPE_def]
  \\ Cases_on`c` \\ fs[STACKLANG_PROG_TYPE_def]
  \\ rw[EQ_IMP_THM] \\
  TRY (
    qmatch_rename_tac`y1 = y2` \\
    qmatch_assum_rename_tac`OPTION_TYPE _ x y1` \\
    qmatch_assum_rename_tac`OPTION_TYPE _ x y2` \\
    Cases_on`x` \\ fs[OPTION_TYPE_def] \\ rw[] \\
    qmatch_rename_tac`y1 = y2` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x y1` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x y2` \\
    Cases_on`x` \\ fs[PAIR_TYPE_def] \\ rw[] \\
    metis_tac[EqualityType_def,EqualityType_PAIR_TYPE_NUM_NUM,EqualityType_PAIR_TYPE_NUM_NUM_NUM]) \\
  TRY (
    qmatch_rename_tac`x1 = x2` \\
    qmatch_assum_rename_tac`OPTION_TYPE _ x1 y` \\
    qmatch_assum_rename_tac`OPTION_TYPE _ x2 y` \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[OPTION_TYPE_def] \\ rw[] \\
    qmatch_rename_tac`x1 = x2` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x1 y` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x2 y` \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[PAIR_TYPE_def] \\ rw[] \\
    metis_tac[EqualityType_def,EqualityType_PAIR_TYPE_NUM_NUM,EqualityType_PAIR_TYPE_NUM_NUM_NUM]) \\
  metis_tac[EqualityType_def,
            EqualityType_NUM,
            EqualityType_LIST_TYPE_CHAR,
            EqualityType_SUM_TYPE_NUM_NUM,
            EqualityType_STACKLANG_STORE_NAME_TYPE,
            EqualityType_ASM_CMP_TYPE,
            EqualityType_ASM_REG_IMM_TYPE,
            EqualityType_WORD |> (INST_TYPE[alpha|->``:5``]),
            EqualityType_ASM_INST_TYPE]);

val EqualityType_STACKLANG_PROG_TYPE = Q.prove(
  `EqualityType STACKLANG_PROG_TYPE`,
  metis_tac[EqualityType_def,STACKLANG_PROG_TYPE_no_closures,STACKLANG_PROG_TYPE_types_match,STACKLANG_PROG_TYPE_11])
  |> store_eq_thm;

(* TODO: the name is messed up (pair_) *)
val _ = translate PAIR_MAP

val _ = translate parmoveTheory.fstep_def

val parmove_fstep_side = Q.prove(`
  ∀x. parmove_fstep_side x ⇔ T`,
  EVAL_TAC>>rw[]>>Cases_on`v18`>>fs[]) |> update_precondition

val _ = translate (spec64 word_to_stackTheory.wMove_def)

val _ = translate (spec64 call_dest_def)

val _ = translate (wInst_def |> conv64)
val _ = translate (spec64 comp_def)

val _ = translate (compile_word_to_stack_def |> INST_TYPE [beta |-> ``:64``])

val _ = translate (compile_def |> INST_TYPE [alpha|->``:64``,beta|->``:64``]);

open stack_allocTheory

val inline_simp = SIMP_RULE std_ss [bytes_in_word_def,
                                    backend_commonTheory.word_shift_def]
val _ = translate (SetNewTrigger_def |> inline_simp |> conv64)
val _ = translate (conv64 clear_top_inst_def)
val _ = translate (memcpy_code_def |> inline_simp |> conv64)
val _ = translate (word_gc_move_code_def |> inline_simp |> conv64)

val _ = translate (word_gc_move_bitmap_code_def |> inline_simp |> conv64);
val _ = translate (word_gc_move_bitmaps_code_def |> inline_simp |> conv64);
val _ = translate (word_gc_move_roots_bitmaps_code_def |> inline_simp |> conv64);
val _ = translate (word_gc_move_list_code_def |> inline_simp |> conv64);
val _ = translate (word_gc_move_loop_code_def |> inline_simp |> conv64);

val _ = translate (stack_allocTheory.word_gen_gc_move_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_move_bitmap_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_move_bitmaps_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_move_roots_bitmaps_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_move_list_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_move_data_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_move_refs_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_move_loop_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_bitmap_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_bitmaps_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_roots_bitmaps_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_list_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_ref_list_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_data_code_def |> inline_simp |> conv64);
val r = translate (stack_allocTheory.word_gc_partial_or_full_def |> inline_simp |> conv64);
val r = translate (stack_allocTheory.word_gc_code_def |> inline_simp |> conv64);

val _ = translate (spec64 stubs_def);

val _ = translate (spec64 comp_def(*pmatch*));

val _ = translate (spec64 compile_def);

(*
val stack_alloc_comp_side = Q.prove(`
  ∀n m prog. stack_alloc_comp_side n m prog ⇔ T`,
`(∀prog n m. stack_alloc_comp_side n m prog ⇔ T) ∧
 (∀opt prog (x:num) (y:num) (z:num) n m. opt = SOME(prog,x,y,z) ⇒ stack_alloc_comp_side n m prog ⇔ T) ∧
 (∀opt prog (x:num) (y:num) (z:num) n m. opt = (prog,x,y,z) ⇒ stack_alloc_comp_side n m prog ⇔ T) ∧
 (∀opt prog (x:num) (y:num) n m. opt = SOME(prog,x,y) ⇒ stack_alloc_comp_side n m prog ⇔ T) ∧
 (∀opt prog (x:num) (y:num) n m. opt = (prog,x,y) ⇒ stack_alloc_comp_side n m prog ⇔ T)`
  suffices_by fs[]
  >> ho_match_mp_tac(TypeBase.induction_of ``:64 stackLang$prog``)
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

(* Might be better to inline this *)
val _ = translate (conv64 word_offset_def)
val _ = translate (conv64 store_offset_def |> SIMP_RULE std_ss [word_mul_def,word_2comp_def] |> conv64)

val _ = translate (comp_def |> inline_simp |> conv64)

val _ = translate (prog_comp_def |> INST_TYPE [beta|->``:64``])

val _ = translate (store_list_code_def |> inline_simp |> conv64)
val _ = translate (init_memory_def |> inline_simp |> conv64)
val _ = translate (init_code_def |> inline_simp |> conv64 |> SIMP_RULE std_ss [word_mul_def]|>gconv|>SIMP_RULE std_ss[w2n_n2w] |> conv64)

val _ = translate (spec64 compile_def)

open stack_namesTheory

val _ = translate (spec64 comp_def)
val _ = translate (prog_comp_def |> INST_TYPE [beta |-> ``:64``])
val _ = translate (compile_def |> INST_TYPE [beta |-> ``:64``])

open stack_to_labTheory

val _ = matches := [``foo:'a labLang$prog``,``foo:'a labLang$sec``,``foo:'a labLang$line``,``foo:'a labLang$asm_with_lab``,``foo:'a labLang$line list``,``foo:'a inst``,``foo:'a asm_config``] @ (!matches)

val _ = translate (flatten_def |> spec64)

val _ = translate (compile_def |> spec64)

open lab_filterTheory lab_to_targetTheory asmTheory

val _ = translate (spec64 filter_skip_def)

val _ = translate (get_jump_offset_def |>INST_TYPE [alpha|->``:64``,beta |-> ``:64``])

val word_2compl_eq = prove(
  ``!w:'a word. -w = 0w - w``,
  fs []);

val _ = translate (conv64 reg_imm_ok_def |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY,
                                               word_2compl_eq])

val _ = translate (conv64 arith_ok_def |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY])

val _ = translate (fp_ok_def |> conv64)
val _ = translate (conv64 inst_ok_def |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY])

(* TODO: there may be a better rewrite for aligned (in to_word64Prog's translation of offset_ok) *)

val _ = translate (spec64 asmTheory.asm_ok_def)

val _ = translate (spec64 compile_def)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
