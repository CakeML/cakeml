open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open sexp_parserProgTheory std_preludeTheory;

val _ = new_theory "to_word64Prog"

val _ = translation_extends "sexp_parserProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "to_word64Prog");

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";

val NOT_NIL_AND_LEMMA = Q.prove(
  `(b <> [] /\ x) = if b = [] then F else x`,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

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

  val insts = if exists (fn term => can (find_term (can (match_term term))) (concl def)) (!matches) then [alpha |-> ``:64``,beta|->``:64``] else []

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

open data_to_wordTheory

val we_simp = SIMP_RULE std_ss [word_extract_w2w_mask,w2w_id]

val wcomp_simp = SIMP_RULE std_ss [word_2comp_def]

val _ = translate stack_to_labTheory.is_gen_gc_def

val _ = translate adjust_set_def

val _ = translate (make_header_def |> SIMP_RULE std_ss [word_lsl_n2w]|> conv64_RHS)

val _ = translate (shift_left_def |> conv64)
val _ = translate (shift_right_def |> spec64 |> CONV_RULE fcpLib.INDEX_CONV)

val i2w_eq_n2w_lemma = prove(
  ``i2w (& (k * n)) = n2w (k * n)``,
  fs [integer_wordTheory.i2w_def]);

val lemma2 = prove(
  ``8 * x < (2**64) <=> x < (2**64) DIV 8``,
  fs []) |> SIMP_RULE std_ss []

val _ = translate (get_gen_size_def |> spec64
    |> SIMP_RULE (srw_ss()) [dimword_def,bytes_in_word_def,word_mul_n2w]
    |> REWRITE_RULE [GSYM i2w_eq_n2w_lemma,lemma2]);

val _ = translate (tag_mask_def |> conv64_RHS |> we_simp |> conv64_RHS |> SIMP_RULE std_ss [shift_left_rwt] |> SIMP_RULE std_ss [Once (GSYM shift_left_rwt),word_2comp_def] |> conv64)

val _ = translate (encode_header_def |> conv64_RHS)

(* Manual inlines : shift_def, bytes_in_word because of 'a arg *)
val inline_simp =
    SIMP_RULE std_ss [backend_commonTheory.word_shift_def,bytes_in_word_def];

val _ = register_type ``:64 wordLang$prog``;

val _ = translate (StoreEach_def |> inline_simp |> conv64);

local
  val ths = ml_translatorLib.eq_lemmas();
in
  fun find_equality_type_thm tm =
    first (can (C match_term tm) o rand o snd o strip_imp o concl) ths
end

val EqualityType_NUM = find_equality_type_thm``NUM``
val EqualityType_WORD = find_equality_type_thm``WORD``
val EqualityType_UNIT_TYPE = find_equality_type_thm ``UNIT_TYPE``
val EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE =
  find_equality_type_thm ``SPTREE_SPT_TYPE UNIT_TYPE``
  |> Q.GEN`a` |> Q.ISPEC`UNIT_TYPE` |> SIMP_RULE std_ss [EqualityType_UNIT_TYPE];
val EqualityType_OPTION_TYPE_NUM = find_equality_type_thm``OPTION_TYPE NUM``
  |> Q.GEN`a` |> Q.ISPEC`NUM` |> SIMP_RULE std_ss [EqualityType_NUM]
val EqualityType_LIST_TYPE_NUM = find_equality_type_thm ``LIST_TYPE NUM``
  |> Q.GEN`a` |> Q.ISPEC`NUM` |> SIMP_RULE std_ss [EqualityType_NUM];
val EqualityType_PAIR_TYPE_NUM_NUM = find_equality_type_thm ``PAIR_TYPE _ _``
  |> Q.GENL[`b`,`c`]
  |> Q.ISPECL[`NUM`,`NUM`]
  |> SIMP_RULE std_ss [EqualityType_NUM];
val EqualityType_LIST_TYPE_PAIR_TYPE_NUM_NUM = find_equality_type_thm ``LIST_TYPE _``
  |> Q.GEN`a` |> Q.ISPEC`PAIR_TYPE NUM NUM` |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_PAIR_TYPE_NUM_NUM];

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

val WORDLANG_EXP_TYPE_def = theorem"WORDLANG_EXP_TYPE_def";
val WORDLANG_EXP_TYPE_ind = theorem"WORDLANG_EXP_TYPE_ind";

val WORDLANG_EXP_TYPE_no_closures = Q.prove(
  `∀a b. WORDLANG_EXP_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac WORDLANG_EXP_TYPE_ind \\
  rw[WORDLANG_EXP_TYPE_def] \\
  rw[no_closures_def] \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x y` \\
    qhdtm_x_assum`LIST_TYPE`mp_tac \\
    last_x_assum mp_tac \\
    map_every qid_spec_tac[`y`,`x`] \\
    Induct \\ rw[LIST_TYPE_def] \\
    rw[no_closures_def] \\
    metis_tac[] ) \\
  metis_tac[EqualityType_def,
            EqualityType_NUM,
            EqualityType_WORD,
            EqualityType_AST_SHIFT_TYPE,
            EqualityType_ASM_BINOP_TYPE,
            EqualityType_STACKLANG_STORE_NAME_TYPE]);

val ctor_same_type_def = semanticPrimitivesTheory.ctor_same_type_def;

val WORDLANG_EXP_TYPE_types_match = Q.prove(
  `∀a b c d. WORDLANG_EXP_TYPE a b ∧ WORDLANG_EXP_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac WORDLANG_EXP_TYPE_ind \\
  rw[WORDLANG_EXP_TYPE_def] \\
  Cases_on`c` \\ fs[WORDLANG_EXP_TYPE_def] \\
  rw[types_match_def,ctor_same_type_def] \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` \\
    qhdtm_x_assum`LIST_TYPE`mp_tac \\
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y2` \\
    qhdtm_x_assum`LIST_TYPE`mp_tac \\
    last_x_assum mp_tac \\
    map_every qid_spec_tac[`y1`,`x1`,`y2`,`x2`] \\
    Induct \\ rw[LIST_TYPE_def] \\
    Cases_on`x1` \\ fs[LIST_TYPE_def] \\
    rw[types_match_def,ctor_same_type_def] \\
    metis_tac[] ) \\
  metis_tac[EqualityType_def,
            EqualityType_NUM,
            EqualityType_WORD,
            EqualityType_AST_SHIFT_TYPE,
            EqualityType_ASM_BINOP_TYPE,
            EqualityType_STACKLANG_STORE_NAME_TYPE]);

val WORDLANG_EXP_TYPE_11 = Q.prove(
  `∀a b c d. WORDLANG_EXP_TYPE a b ∧ WORDLANG_EXP_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac WORDLANG_EXP_TYPE_ind \\
  rw[WORDLANG_EXP_TYPE_def] \\
  Cases_on`c` \\ fs[WORDLANG_EXP_TYPE_def] \\
  rw[EQ_IMP_THM] \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x y1` \\
    qhdtm_x_assum`LIST_TYPE`mp_tac \\
    qmatch_assum_rename_tac`LIST_TYPE _ x y2` \\
    qhdtm_x_assum`LIST_TYPE`mp_tac \\
    last_x_assum mp_tac \\
    map_every qid_spec_tac[`y1`,`y2`,`x`] \\
    Induct \\ rw[LIST_TYPE_def] \\
    metis_tac[] ) \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y` \\
    qhdtm_x_assum`LIST_TYPE`mp_tac \\
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y` \\
    qhdtm_x_assum`LIST_TYPE`mp_tac \\
    last_x_assum mp_tac \\
    map_every qid_spec_tac[`y`,`x1`,`x2`] \\
    Induct \\ rw[LIST_TYPE_def] \\
    Cases_on`x1` \\ fs[LIST_TYPE_def] \\
    metis_tac[] ) \\
  metis_tac[EqualityType_def,
            EqualityType_NUM,
            EqualityType_WORD,
            EqualityType_AST_SHIFT_TYPE,
            EqualityType_ASM_BINOP_TYPE,
            EqualityType_STACKLANG_STORE_NAME_TYPE])

val EqualityType_WORDLANG_EXP_TYPE = Q.prove(
  `EqualityType WORDLANG_EXP_TYPE`,
  metis_tac[EqualityType_def,WORDLANG_EXP_TYPE_no_closures,WORDLANG_EXP_TYPE_types_match,WORDLANG_EXP_TYPE_11])
  |> store_eq_thm;

val WORDLANG_PROG_TYPE_def = theorem"WORDLANG_PROG_TYPE_def";
val WORDLANG_PROG_TYPE_ind = theorem"WORDLANG_PROG_TYPE_ind";

val EqualityType_CHAR = find_equality_type_thm``CHAR``

val EqualityType_LIST_TYPE_CHAR = find_equality_type_thm``LIST_TYPE CHAR``
  |> Q.GEN`a` |> Q.ISPEC`CHAR` |> SIMP_RULE std_ss [EqualityType_CHAR]

val WORDLANG_PROG_TYPE_no_closures = Q.prove(
  `∀a b. WORDLANG_PROG_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac WORDLANG_PROG_TYPE_ind
  \\ rw[WORDLANG_PROG_TYPE_def]
  \\ rw[no_closures_def] \\
  TRY (
    qmatch_assum_rename_tac`OPTION_TYPE (_ _ (_ _ (_ WORDLANG_PROG_TYPE _))) x y` \\
    Cases_on`x` \\ fs[OPTION_TYPE_def] \\ rw[no_closures_def] \\
    qmatch_rename_tac`no_closures y` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x y` \\
    Cases_on`x` \\ fs[PAIR_TYPE_def] \\
    rw[no_closures_def] >-
      metis_tac[EqualityType_def,EqualityType_NUM] \\
    qmatch_rename_tac`no_closures y` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x y` \\
    Cases_on`x` \\ fs[PAIR_TYPE_def] \\
    rw[no_closures_def] >-
      metis_tac[EqualityType_def,EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE] \\
    qmatch_rename_tac`no_closures y` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x y` \\
    Cases_on`x` \\ fs[PAIR_TYPE_def] \\
    rw[no_closures_def] \\
    metis_tac[EqualityType_def,EqualityType_PAIR_TYPE_NUM_NUM]) \\
  TRY (
    qmatch_rename_tac`no_closures y` \\
    qmatch_assum_rename_tac`_ x y` \\
    Cases_on`x` \\ fs[OPTION_TYPE_def] \\ rw[no_closures_def] \\
    qmatch_rename_tac`no_closures y` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x y` \\
    Cases_on`x` \\ fs[PAIR_TYPE_def] \\
    rw[no_closures_def] >-
      metis_tac[EqualityType_def,EqualityType_NUM] \\
    qmatch_rename_tac`no_closures y` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x y` \\
    Cases_on`x` \\ fs[PAIR_TYPE_def] \\
    rw[no_closures_def] \\
    metis_tac[EqualityType_def,EqualityType_PAIR_TYPE_NUM_NUM]) \\
  metis_tac[EqualityType_def,EqualityType_NUM,
            EqualityType_WORDLANG_EXP_TYPE,
            EqualityType_LIST_TYPE_PAIR_TYPE_NUM_NUM,
            EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE,
            EqualityType_ASM_REG_IMM_TYPE,
            EqualityType_OPTION_TYPE_NUM,
            EqualityType_LIST_TYPE_NUM,
            EqualityType_LIST_TYPE_CHAR,
            EqualityType_STACKLANG_STORE_NAME_TYPE,
            EqualityType_ASM_INST_TYPE,
            EqualityType_WORD |> (INST_TYPE[alpha|->``:5``]),
            EqualityType_ASM_CMP_TYPE]);


val WORDLANG_PROG_TYPE_types_match = Q.prove(
  `∀a b c d. WORDLANG_PROG_TYPE a b ∧ WORDLANG_PROG_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac WORDLANG_PROG_TYPE_ind \\
  rw[WORDLANG_PROG_TYPE_def] \\
  Cases_on`c` \\ fs[WORDLANG_PROG_TYPE_def] \\
  rw[types_match_def,ctor_same_type_def] \\
  TRY (
    qmatch_rename_tac`_ y1 y2` \\
    qmatch_assum_rename_tac`OPTION_TYPE (_ _) x1 y1` \\
    qmatch_assum_rename_tac`OPTION_TYPE (_ _) x2 y2` \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[OPTION_TYPE_def] \\
    rw[types_match_def,ctor_same_type_def] \\
    qmatch_rename_tac`_ y1 y2` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x1 y1` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x2 y2` \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[PAIR_TYPE_def] \\
    rw[types_match_def,ctor_same_type_def] >-
      metis_tac[EqualityType_def,EqualityType_NUM] \\
    qmatch_rename_tac`_ y1 y2` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x1 y1` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x2 y2` \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[PAIR_TYPE_def] \\
    rw[types_match_def,ctor_same_type_def] >-
      metis_tac[EqualityType_def,EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE] \\
    qmatch_rename_tac`_ y1 y2` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x1 y1` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x2 y2` \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[PAIR_TYPE_def] \\
    rw[types_match_def,ctor_same_type_def] \\
    metis_tac[EqualityType_def,EqualityType_PAIR_TYPE_NUM_NUM,EqualityType_NUM]) \\
  metis_tac[EqualityType_def,EqualityType_NUM,
            EqualityType_PAIR_TYPE_NUM_NUM,
            EqualityType_WORDLANG_EXP_TYPE,
            EqualityType_LIST_TYPE_PAIR_TYPE_NUM_NUM,
            EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE,
            EqualityType_ASM_REG_IMM_TYPE,
            EqualityType_OPTION_TYPE_NUM,
            EqualityType_LIST_TYPE_NUM,
            EqualityType_LIST_TYPE_CHAR,
            EqualityType_STACKLANG_STORE_NAME_TYPE,
            EqualityType_ASM_INST_TYPE,
            EqualityType_WORD |> (INST_TYPE[alpha|->``:5``]),
            EqualityType_ASM_CMP_TYPE])

val WORDLANG_PROG_TYPE_11 = Q.prove(
  `∀a b c d. WORDLANG_PROG_TYPE a b ∧ WORDLANG_PROG_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac WORDLANG_PROG_TYPE_ind \\
  rw[WORDLANG_PROG_TYPE_def] \\
  Cases_on`c` \\ fs[WORDLANG_PROG_TYPE_def] \\
  rw[EQ_IMP_THM] \\
  TRY (
    qmatch_rename_tac`y1 = y2` \\
    qmatch_assum_rename_tac`OPTION_TYPE (_ _) x y1` \\
    qmatch_assum_rename_tac`OPTION_TYPE (_ _) x y2` \\
    Cases_on`x` \\ fs[OPTION_TYPE_def] \\ rw[] \\
    qmatch_rename_tac`y1 = y2` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x y1` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x y2` \\
    Cases_on`x` \\ fs[PAIR_TYPE_def] \\
    rw[] >-
      metis_tac[EqualityType_def,EqualityType_NUM] \\
    qmatch_rename_tac`y1 = y2` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x y1` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x y2` \\
    Cases_on`x` \\ fs[PAIR_TYPE_def] \\
    rw[] >-
      metis_tac[EqualityType_def,EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE] \\
    qmatch_rename_tac`y1 = y2` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x y1` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x y2` \\
    Cases_on`x` \\ fs[PAIR_TYPE_def] \\
    rw[] \\
    metis_tac[EqualityType_def,EqualityType_PAIR_TYPE_NUM_NUM,EqualityType_NUM]) \\
  TRY (
    qmatch_rename_tac`x1 = x2` \\
    qmatch_assum_rename_tac`OPTION_TYPE (_ _) x1 y` \\
    qmatch_assum_rename_tac`OPTION_TYPE (_ _) x2 y` \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[OPTION_TYPE_def] \\
    rw[] \\
    qmatch_rename_tac`x1 = x2` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x1 y` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x2 y` \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[PAIR_TYPE_def] \\
    rw[] >-
      metis_tac[EqualityType_def,EqualityType_NUM] \\
    qmatch_rename_tac`x1 = x2` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x1 y` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x2 y` \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[PAIR_TYPE_def] \\
    rw[] >-
      metis_tac[EqualityType_def,EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE] \\
    qmatch_rename_tac`x1 = x2` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x1 y` \\
    qmatch_assum_rename_tac`PAIR_TYPE _ _ x2 y` \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[PAIR_TYPE_def] \\
    rw[] \\
    metis_tac[EqualityType_def,EqualityType_PAIR_TYPE_NUM_NUM,EqualityType_NUM]) \\
  metis_tac[EqualityType_def,EqualityType_NUM,
            EqualityType_PAIR_TYPE_NUM_NUM,
            EqualityType_WORDLANG_EXP_TYPE,
            EqualityType_LIST_TYPE_PAIR_TYPE_NUM_NUM,
            EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE,
            EqualityType_ASM_REG_IMM_TYPE,
            EqualityType_OPTION_TYPE_NUM,
            EqualityType_LIST_TYPE_NUM,
            EqualityType_LIST_TYPE_CHAR,
            EqualityType_STACKLANG_STORE_NAME_TYPE,
            EqualityType_ASM_INST_TYPE,
            EqualityType_WORD |> (INST_TYPE[alpha|->``:5``]),
            EqualityType_ASM_CMP_TYPE]);

val EqualityType_WORDLANG_PROG_TYPE = Q.prove(
  `EqualityType WORDLANG_PROG_TYPE`,
  metis_tac[EqualityType_def,WORDLANG_PROG_TYPE_no_closures,WORDLANG_PROG_TYPE_types_match,WORDLANG_PROG_TYPE_11])
  |> store_eq_thm;

val _ = translate (all_ones_def |> conv64_RHS |> we_simp |> SIMP_RULE std_ss [shift_left_rwt,shift_right_rwt] |> wcomp_simp |> conv64 |> wcomp_simp |> conv64)

val _ = translate (maxout_bits_def |> SIMP_RULE std_ss [word_lsl_n2w] |> conv64)

val _ = translate (ptr_bits_def  |> conv64)

val _ = translate (real_addr_def |> inline_simp |> conv64_RHS |> SIMP_RULE std_ss [LET_THM])

val _ = translate (real_offset_def |> inline_simp |> conv64)
val _ = translate (real_byte_offset_def |> inline_simp |> conv64)
val _ = translate (GiveUp_def |> wcomp_simp |> conv64)

val _ = matches:= [``foo:'a wordLang$prog``,``foo:'a wordLang$exp``]

val assign_rw = Q.prove(`
  (i < 0 ⇒ n2w (Num (4 * (0 -i))) = n2w (Num (ABS (4*(0-i))))) ∧
  (¬(i < 0) ⇒ n2w (Num (4 * i)) = n2w (Num (ABS (4*i))))`,
  rw[]
  >-
    (`0 ≤ 4* -i` by intLib.COOPER_TAC>>
    metis_tac[integerTheory.INT_ABS_EQ_ID])
  >>
    `0 ≤ 4*i` by intLib.COOPER_TAC>>
    metis_tac[integerTheory.INT_ABS_EQ_ID])

(* TODO: word_mul should maybe target a real op ?
   TODO: econv might be going too far with case simplification
*)

val _ = translate (ShiftVar_def |> inline_simp |> conv64);
val _ = translate (LoadWord64_def |> inline_simp |> conv64)
val _ = translate (WriteWord64_def |> inline_simp |> conv64)
val _ = translate (LoadBignum_def |> inline_simp |> conv64)

val Smallnum_alt = prove(
  ``Smallnum i =
    if i < 0 then 0w − n2w (Num (ABS (4 * (0 − i))))
             else n2w (Num (ABS (4 * i)))``,
  fs [Smallnum_def] \\ Cases_on `i` \\ fs [integerTheory.INT_ABS_NUM]);

val _ = translate (Smallnum_alt |> inline_simp |> conv64)
val _ = translate (MemEqList_def |> inline_simp |> conv64)

val _ = save_thm("n2mw_ind",multiwordTheory.n2mw_ind |> inline_simp |> conv64);
val _ = translate (multiwordTheory.n2mw_def |> inline_simp |> conv64);
val _ = translate (multiwordTheory.i2mw_def |> inline_simp |> conv64);
val _ = translate (bignum_words_def |> inline_simp |> conv64);
val _ = translate (BignumHalt_def |> inline_simp |> conv64);
val _ = translate(Maxout_bits_code_def |> conv64);
val _ = translate(Make_ptr_bits_code_def |> inline_simp |> conv64);
val _ = translate(SilentFFI_def |> inline_simp |> wcomp_simp |> conv64);
val _ = translate(AllocVar_def |> inline_simp |> wcomp_simp |> conv64);

(*val _ = translate (assign_pmatch |> SIMP_RULE std_ss [assign_rw] |> inline_simp |> conv64 |> we_simp |> SIMP_RULE std_ss[SHIFT_ZERO,shift_left_rwt] |> SIMP_RULE std_ss [word_mul_def,LET_THM]|>gconv)*)

val _ = translate (assign_def |> SIMP_RULE std_ss [assign_rw] |> inline_simp |> conv64 |> we_simp |> SIMP_RULE std_ss[SHIFT_ZERO,shift_left_rwt] |> SIMP_RULE std_ss [word_mul_def,LET_THM]|>gconv)

val lemma = Q.prove(`!A B. A = B ==> B ≠ A ==> F`,metis_tac[])

(*
val data_to_word_assign_side = Q.prove(`
  ∀a b c d e f g. data_to_word_assign_side a b c d e f g ⇔ T`,
  rpt strip_tac>>
  simp[fetch "-" "data_to_word_assign_side_def",NULL]>>
  Cases_on`e`>>fs[]>>
  Cases_on`f`>>fs[]>>
  TRY(Cases_on`t`)>>TRY(Cases_on`t'`)>>
  TRY(Cases_on`w`)>>fs[]>>
  TRY(Cases_on`(encode_header a 3 1):word64 option`)>>
  TRY(Cases_on`o'`)>>
  TRY(Cases_on`s`)>>
  metis_tac[word_op_type_nchotomy,option_nchotomy,NOT_NONE_SOME,list_distinct]) |> update_precondition
*)

val _ = save_thm ("comp_ind",data_to_wordTheory.comp_ind|> conv64|> wcomp_simp)
(* Inlines the let k = 8 manually *)
val _ = translate (comp_def |> conv64 |> wcomp_simp |> conv64 |> SIMP_RULE std_ss[LET_THM |> INST_TYPE [alpha|->``:num``]]);

open word_simpTheory word_allocTheory word_instTheory

val _ = matches:= [``foo:'a wordLang$prog``,``foo:'a wordLang$exp``,``foo:'a word``,``foo: 'a reg_imm``,``foo:'a arith``,``foo: 'a addr``]

val _ = translate (const_fp_inst_cs_def |> spec64 |> econv)

val rws = Q.prove(`
  ($+ = λx y. x + y) ∧
  ($&& = λx y. x && y) ∧
  ($|| = λx y. x || y) ∧
  ($?? = λx y. x ?? y)`,
  fs[FUN_EQ_THM])

val _ = translate (wordLangTheory.word_op_def |> ONCE_REWRITE_RULE [rws,WORD_NOT_0] |> spec64 |> gconv)

val word_msb_rw = Q.prove(
  `word_msb (a:word64) ⇔ (a>>>63) <> 0w`,
  rw[word_msb_def,fcpTheory.CART_EQ,word_index,word_lsr_def,fcpTheory.FCP_BETA]
  \\ rw[EQ_IMP_THM]
  >- ( qexists_tac`0` \\ simp[] )
  \\ `i = 0` by decide_tac \\ fs[]);

val arith_shift_right_ind_orig = arith_shift_right_ind;

val arith_shift_right_ind = (
  arith_shift_right_ind_orig |> spec64
  |> SIMP_RULE std_ss [word_msb_rw]
  |> CONV_RULE (QUANT_CONV(LAND_CONV fcpLib.INDEX_CONV)) |> gconv)
  |> curry save_thm "arith_shift_right_ind";

val _ = translate (
  arith_shift_right_def |> spec64
  |> SIMP_RULE std_ss [word_msb_rw]
  |> CONV_RULE fcpLib.INDEX_CONV |> gconv);

val _ = translate miscTheory.any_word64_ror_def;

val res = translate (wordLangTheory.word_sh_def
  |> INST_TYPE [``:'a``|->``:64``]
  |> REWRITE_RULE [miscTheory.word_ror_eq_any_word64_ror]
  |> RW[shift_left_rwt,shift_right_rwt,arith_shift_right_rwt] |> conv64)

val _ = translate (asmTheory.word_cmp_def |> REWRITE_RULE[WORD_LO,WORD_LT] |> spec64 |> REWRITE_RULE[word_msb_rw]);

(* TODO: remove when pmatch is fixed *)
val _ = translate (spec64 const_fp_loop_def)

val _ = translate (spec64 compile_exp_def)

val _ = translate (wordLangTheory.max_var_inst_def |> conv64)
val _ = translate (spec64 wordLangTheory.max_var_def)

val _ = translate (conv64_RHS integer_wordTheory.WORD_LEi)

val _ = translate (asmTheory.offset_ok_def |> SIMP_RULE std_ss [alignmentTheory.aligned_bitwise_and] |> conv64)
val res = translate_no_ind (inst_select_exp_pmatch |> conv64 |> SIMP_RULE std_ss [word_mul_def,word_2comp_def] |> conv64)

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum (match_mp_tac o MP_CANON)
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]
  \\ rveq
  THEN1
   (last_x_assum (match_mp_tac o MP_CANON)
    \\ fs [] \\ rveq \\ fs [])
  THEN1
   (Cases_on `exp` \\ fs []
    \\ Cases_on `b` \\ fs []
    \\ Cases_on `l` \\ fs []
    \\ Cases_on `t` \\ fs []
    \\ Cases_on `h'` \\ fs []
    \\ Cases_on `t'` \\ fs [])
  \\ fs []
  \\ Cases_on `e2` \\ fs [])
  |> update_precondition;

val _ = translate (op_consts_pmatch|>conv64|>econv)

val _ = translate (convert_sub_pmatch |> conv64 |> SIMP_RULE std_ss [word_2comp_def,word_mul_def] |> conv64)

val _ = translate (spec64 pull_exp_def(*_pmatch*)) (* TODO: MAP pull_exp inside pmatch seems to throw the translator into an infinite loop *)

val word_inst_pull_exp_side = Q.prove(`
  ∀x. word_inst_pull_exp_side x ⇔ T`,
  ho_match_mp_tac pull_exp_ind>>rw[]>>
  simp[Once (fetch "-" "word_inst_pull_exp_side_def"),
      fetch "-" "word_inst_optimize_consts_side_def",
      wordLangTheory.word_op_def]>>
  metis_tac[]) |> update_precondition

val _ = translate (spec64 inst_select_def(*pmatch*))

val _ = translate (spec64 list_next_var_rename_move_def)

val _ = translate (conv64 ssa_cc_trans_inst_def)
val _ = translate (spec64 full_ssa_cc_trans_def)

val _ = translate (conv64 remove_dead_inst_def)
val _ = translate (conv64 get_live_inst_def)
val _ = translate (spec64 remove_dead_def)

val lem = Q.prove(`
  dimindex(:64) = 64 ∧
  dimindex(:32) = 32`,
  EVAL_TAC);

val _ = translate (INST_TYPE [alpha|->``:64``,beta|->``:64``] get_forced_pmatch
                  |> SIMP_RULE (bool_ss++ARITH_ss) [lem])

val _ = translate (get_delta_inst_def |> conv64)
val _ = translate (wordLangTheory.every_var_inst_def |> conv64)
val _ = translate select_reg_alloc_def
val _ = translate (INST_TYPE [alpha|->``:64``,beta|->``:64``]  word_alloc_def)

val res = translate_no_ind (spec64 three_to_two_reg_pmatch);

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ disch_then strip_assume_tac
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac \\ fs []
  \\ rveq \\ fs []
  \\ rename1 `NONE <> a` \\ Cases_on `a` \\ fs [] \\ PairCases_on `x` \\ fs [])
  |> update_precondition;

val word_inst_three_to_two_reg_side = Q.prove(`
∀prog. word_inst_three_to_two_reg_side prog ⇔ T`,
`(∀prog. word_inst_three_to_two_reg_side prog ⇔ T) /\
 (∀opt (a:num) (b:num_set) c (d:num) (e:num). opt = SOME(a,b,c,d,e) ==> word_inst_three_to_two_reg_side c) /\
(∀opt (a:num) (b:num_set) c (d:num) (e:num). opt = (a,b,c,d,e) ==> word_inst_three_to_two_reg_side c) /\
 (∀opt (a:num) b (c:num) (d:num). opt = SOME(a,b,c,d) ==> word_inst_three_to_two_reg_side b) /\
 (∀opt (a:num_set) b (c:num) (d:num). opt = (a,b,c,d) ==> word_inst_three_to_two_reg_side b) /\
 (∀opt (a:num) b (c:num) (d:num). opt = (a,b,c,d) ==> word_inst_three_to_two_reg_side b) /\
(∀opt a (b:num) (c:num). opt = (a,b,c) ==> word_inst_three_to_two_reg_side a)`
   suffices_by fs[]
>> ho_match_mp_tac(TypeBase.induction_of ``:64 prog``)
>> rpt strip_tac
>> fs[]
>> rw[Once(fetch "-" "word_inst_three_to_two_reg_side_def")]
>> fs[]
>> POP_ASSUM(ASSUME_TAC o RW.PURE_ONCE_RW_RULE[fetch"-" "word_inst_three_to_two_reg_side_def"])
>> fs[]
>> metis_tac[pair_CASES,option_CASES]) |> update_precondition

val res = translate_no_ind (spec64 word_removeTheory.remove_must_terminate_pmatch);

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ disch_then strip_assume_tac
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum (match_mp_tac o MP_CANON)
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]
  \\ rveq \\ fs []
  \\ rename1 `NONE <> a`
  \\ Cases_on `a` \\ fs []
  \\ PairCases_on `x` \\ fs [])
  |> update_precondition;

val word_remove_remove_must_terminate_side = Q.prove(`
∀prog. word_remove_remove_must_terminate_side prog ⇔ T`,
`(∀prog. word_remove_remove_must_terminate_side prog ⇔ T) /\
 (∀opt (a:num) (b:num_set) c (d:num) (e:num). opt = SOME(a,b,c,d,e) ==> word_remove_remove_must_terminate_side c) /\
(∀opt (a:num) (b:num_set) c (d:num) (e:num). opt = (a,b,c,d,e) ==> word_remove_remove_must_terminate_side c) /\
 (∀opt (a:num) b (c:num) (d:num). opt = SOME(a,b,c,d) ==> word_remove_remove_must_terminate_side b) /\
 (∀opt (a:num_set) b (c:num) (d:num). opt = (a,b,c,d) ==> word_remove_remove_must_terminate_side b) /\
 (∀opt (a:num) b (c:num) (d:num). opt = (a,b,c,d) ==> word_remove_remove_must_terminate_side b) /\
(∀opt a (b:num) (c:num). opt = (a,b,c) ==> word_remove_remove_must_terminate_side a)`
   suffices_by fs[]
>> ho_match_mp_tac(TypeBase.induction_of ``:64 prog``)
>> rpt strip_tac
>> fs[]
>> rw[Once(fetch "-" "word_remove_remove_must_terminate_side_def")]
>> fs[]
>> POP_ASSUM(ASSUME_TAC o RW.PURE_ONCE_RW_RULE[fetch"-" "word_remove_remove_must_terminate_side_def"])
>> fs[]
>> metis_tac[pair_CASES,option_CASES]) |> update_precondition;

val res = translate (spec64 word_to_wordTheory.compile_alt);

(* TODO: remove when pmatch is fixed
val word_simp_const_fp_loop_side = Q.prove(`
∀prog nm. word_simp_const_fp_loop_side prog nm ⇔ T`,
`(∀prog nm. word_simp_const_fp_loop_side prog nm ⇔ T) /\
 (∀opt (a:num) (b:num_set) c (d:num) (e:num) nm. opt = SOME(a,b,c,d,e) ==> word_simp_const_fp_loop_side c nm) /\
(∀opt (a:num) (b:num_set) c (d:num) (e:num) nm. opt = (a,b,c,d,e) ==> word_simp_const_fp_loop_side c nm) /\
 (∀opt (a:num) b (c:num) (d:num) nm. opt = SOME(a,b,c,d) ==> word_simp_const_fp_loop_side b nm) /\
 (∀opt (a:num_set) b (c:num) (d:num) nm. opt = (a,b,c,d) ==> word_simp_const_fp_loop_side b nm) /\
 (∀opt (a:num) b (c:num) (d:num) nm. opt = (a,b,c,d) ==> word_simp_const_fp_loop_side b nm) /\
(∀opt a (b:num) (c:num) nm. opt = (a,b,c) ==> word_simp_const_fp_loop_side a nm)`
   suffices_by fs[]
>> ho_match_mp_tac(TypeBase.induction_of ``:64 prog``)
>> rpt strip_tac
>> fs[]
>> rw[Once(fetch "-" "word_simp_const_fp_loop_side_def")]
>> fs[]
>> POP_ASSUM(ASSUME_TAC o RW.PURE_ONCE_RW_RULE[fetch"-" "word_simp_const_fp_loop_side_def"])
>> fs[]
>> metis_tac[pair_CASES,option_CASES]) |> update_precondition

val word_simp_const_fp_side = Q.prove(`
  ∀prog. word_simp_const_fp_side prog ⇔ T`,
  fs[fetch "-" "word_simp_const_fp_side_def",
     word_simp_const_fp_loop_side]) |> update_precondition

val word_simp_compile_exp_side = Q.prove(`
  ∀prog. word_simp_compile_exp_side prog ⇔ T`,
  fs[fetch "-" "word_simp_compile_exp_side_def",
     word_simp_const_fp_side]) |> update_precondition
*)

(*
val word_inst_inst_select_side = Q.prove(`
∀prog c n. word_inst_inst_select_side c n prog ⇔ T`,
`(∀prog c n. word_inst_inst_select_side c n prog ⇔ T) /\
 (∀opt (a:num) (b:num_set) c (d:num) (e:num) x n. opt = SOME(a,b,c,d,e) ==> word_inst_inst_select_side x n c) /\
(∀opt (a:num) (b:num_set) c (d:num) (e:num) x n. opt = (a,b,c,d,e) ==> word_inst_inst_select_side x n c) /\
 (∀opt (a:num) b (c:num) (d:num) x n. opt = SOME(a,b,c,d) ==> word_inst_inst_select_side x n b) /\
 (∀opt (a:num_set) b (c:num) (d:num) x n. opt = (a,b,c,d) ==> word_inst_inst_select_side x n b) /\
 (∀opt (a:num) b (c:num) (d:num) x n. opt = (a,b,c,d) ==> word_inst_inst_select_side x n b) /\
(∀opt a (b:num) (c:num) x n. opt = (a,b,c) ==> word_inst_inst_select_side x n a)`
   suffices_by fs[]
>> ho_match_mp_tac(TypeBase.induction_of ``:64 prog``)
>> rpt strip_tac
>> fs[]
>> rw[Once(fetch "-" "word_inst_inst_select_side_def")]
>> fs[]
>> POP_ASSUM(ASSUME_TAC o RW.PURE_ONCE_RW_RULE[fetch"-" "word_inst_inst_select_side_def"])
>> fs[]
>> metis_tac[pair_CASES,option_CASES,fetch "asm" "reg_imm_nchotomy"]) |> update_precondition
*)

(*
val word_to_word_compile_side = Q.prove(`
  ∀x y z. word_to_word_compile_side x y z ⇔ T`,
  fs[fetch"-""word_to_word_compile_side_def",word_to_wordTheory.next_n_oracle_def,word_inst_inst_select_side]) |> update_precondition
*)

val _ = translate(FromList_code_def |> conv64 |> econv)
val _ = translate(FromList1_code_def |> inline_simp |> conv64)
val _ = translate(MakeBytes_def |> conv64)
val _ = translate(WriteLastByte_aux_def |> conv64)
val _ = translate(WriteLastBytes_def |> conv64)
val _ = translate(RefByte_code_def |> inline_simp |> conv64 |> SIMP_RULE std_ss[SmallLsr_def])
val _ = translate(RefArray_code_def |> inline_simp |> conv64|>econv)
val _ = translate(Replicate_code_def|> inline_simp |> conv64)
val _ = translate(AddNumSize_def|> conv64)
val _ = translate(AnyHeader_def|> inline_simp |> conv64)
val _ = translate(AnyArith_code_def|> inline_simp |> conv64)
val _ = translate(Add_code_def|> conv64)
val _ = translate(Sub_code_def|> conv64)
val _ = translate(Mul_code_def|> conv64)
val _ = translate(Div_code_def|> conv64)
val _ = translate(Mod_code_def|> conv64)
val _ = translate(MemCopy_code_def|> inline_simp |> conv64)
val r = translate(ByteCopy_code_def |> inline_simp |> conv64)
val r = translate(ByteCopyAdd_code_def |> conv64)
val r = translate(ByteCopySub_code_def |> conv64 |> econv)
val r = translate(ByteCopyNew_code_def |> conv64)

val r = translate(Install_code_def |> conv64)
val r = translate(InstallCode_code_def |> inline_simp |> conv64)
val r = translate(InstallData_code_def |> inline_simp |> conv64)

val _ = translate(Append_code_def|> inline_simp |> conv64 |> we_simp |> econv |> SIMP_RULE std_ss [shift_left_rwt])
val _ = translate(AppendMainLoop_code_def|> inline_simp |> conv64)
val _ = translate(AppendLenLoop_code_def|> inline_simp |> conv64)
val _ = translate(AppendFastLoop_code_def|> inline_simp |> conv64)

val _ = translate(Compare1_code_def|> inline_simp |> conv64)
val _ = translate(Compare_code_def|> inline_simp |> conv64)

val _ = translate(Equal1_code_def|> inline_simp |> conv64)
val _ = translate(Equal_code_def|> inline_simp |> SIMP_RULE std_ss [backend_commonTheory.closure_tag_def,backend_commonTheory.partial_app_tag_def] |> conv64)


val _ = translate(LongDiv1_code_def|> inline_simp |> wcomp_simp |> conv64)
val _ = translate(LongDiv_code_def|> inline_simp |> conv64)

val _ = translate (word_bignumTheory.generated_bignum_stubs_eq |> inline_simp |> conv64)

val res = translate (data_to_wordTheory.compile_def
                     |> SIMP_RULE std_ss [data_to_wordTheory.stubs_def] |> conv64_RHS);

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
