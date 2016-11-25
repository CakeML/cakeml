open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open to_dataProgTheory;

val _ = new_theory "to_word64Prog"

val _ = translation_extends "to_dataProg";

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

val _ = translate adjust_set_def

val _ = translate (make_header_def |> SIMP_RULE std_ss [word_lsl_n2w]|> conv64_RHS)

val shift_left_def = Define`
  shift_left (a : 'a word) n =
  if n = 0 then a
  else if (a = 0w) \/ n > dimindex(:'a) then 0w
  else if n > 32 then shift_left (a << 32) (n - 32)
  else if n > 16 then shift_left (a << 16) (n - 16)
  else if n > 8 then shift_left (a << 8) (n - 8)
  else shift_left (a << 1) (n - 1)`

val shift_left_rwt = Q.prove(
  `!a n. a << n = shift_left a n`,
  completeInduct_on `n`
  \\ rw [Once shift_left_def]
  \\ qpat_x_assum `!n. P` (assume_tac o GSYM)
  \\ fs [])

val shift_right_def = Define`
  shift_right (a : 'a word) n =
  if n = 0 then a
  else if (a = 0w) \/ n > dimindex(:'a) then 0w
  else if n > 32 then shift_right (a >>> 32) (n - 32)
  else if n > 16 then shift_right (a >>> 16) (n - 16)
  else if n > 8 then shift_right (a >>> 8) (n - 8)
  else shift_right (a >>> 1) (n - 1)`

val shift_right_rwt = Q.prove(
  `!a n. a >>> n = shift_right a n`,
  completeInduct_on `n`
  \\ rw [Once shift_right_def]
  \\ qpat_x_assum `!n. P` (assume_tac o GSYM)
  \\ fs [])

val arith_shift_right_def = Define`
  arith_shift_right (a : 'a word) n =
  if n = 0 then a
  else if (a = 0w) \/ n > dimindex(:'a) /\ ~word_msb a then 0w
  else if (a = -1w) \/ n > dimindex(:'a) /\ word_msb a then -1w
  else if n > 32 then arith_shift_right (a >> 32) (n - 32)
  else if n > 16 then arith_shift_right (a >> 16) (n - 16)
  else if n > 8 then arith_shift_right (a >> 8) (n - 8)
  else arith_shift_right (a >> 1) (n - 1)`

val arith_shift_right_rwt = Q.prove(
  `!a n. a >> n = arith_shift_right a n`,
  completeInduct_on `n`
  \\ rw [Once arith_shift_right_def]
  \\ qpat_x_assum `!n. P` (assume_tac o GSYM)
  \\ fs [SIMP_RULE (srw_ss()) [] wordsTheory.ASR_UINT_MAX])

val _ = translate (shift_left_def |> conv64)
val _ = translate (shift_right_def |> spec64 |> CONV_RULE fcpLib.INDEX_CONV)

val _ = translate (tag_mask_def |> conv64_RHS |> we_simp |> conv64_RHS |> SIMP_RULE std_ss [shift_left_rwt] |> SIMP_RULE std_ss [Once (GSYM shift_left_rwt),word_2comp_def] |> conv64)

val _ = translate (encode_header_def |> conv64_RHS)

(* Manual inlines : shift_def, bytes_in_word because of 'a arg *)
val inline_simp = SIMP_RULE std_ss [shift_def,bytes_in_word_def]

val _ = translate (StoreEach_def |> inline_simp |> conv64)

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
  |> Q.GENL[`c`,`b`]
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
val EqualityType_ASM_INST_TYPE = find_equality_type_thm``ASM_INST_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_WORD,EqualityType_ASM_ADDR_TYPE,
                       EqualityType_ASM_MEMOP_TYPE,EqualityType_ASM_ARITH_TYPE]

val EqualityType_STACKLANG_STORE_NAME_TYPE = find_equality_type_thm``STACKLANG_STORE_NAME_TYPE``
  |> SIMP_RULE std_ss []

val EqualityType_WORDLANG_NUM_EXP_TYPE = find_equality_type_thm``WORDLANG_NUM_EXP_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_WORD]

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
            EqualityType_STACKLANG_STORE_NAME_TYPE,
            EqualityType_WORDLANG_NUM_EXP_TYPE]);

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
            EqualityType_STACKLANG_STORE_NAME_TYPE,
            EqualityType_WORDLANG_NUM_EXP_TYPE]);

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
            EqualityType_STACKLANG_STORE_NAME_TYPE,
            EqualityType_WORDLANG_NUM_EXP_TYPE])

val EqualityType_WORDLANG_EXP_TYPE = Q.prove(
  `EqualityType WORDLANG_EXP_TYPE`,
  metis_tac[EqualityType_def,WORDLANG_EXP_TYPE_no_closures,WORDLANG_EXP_TYPE_types_match,WORDLANG_EXP_TYPE_11])
  |> store_eq_thm;

val WORDLANG_PROG_TYPE_def = theorem"WORDLANG_PROG_TYPE_def";
val WORDLANG_PROG_TYPE_ind = theorem"WORDLANG_PROG_TYPE_ind";

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
            EqualityType_STACKLANG_STORE_NAME_TYPE,
            EqualityType_ASM_INST_TYPE,
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
            EqualityType_STACKLANG_STORE_NAME_TYPE,
            EqualityType_ASM_INST_TYPE,
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
            EqualityType_STACKLANG_STORE_NAME_TYPE,
            EqualityType_ASM_INST_TYPE,
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
    fs[GSYM integerTheory.INT_ABS_EQ_ID])
  >>
    `0 ≤ 4*i` by intLib.COOPER_TAC>>
    fs[GSYM integerTheory.INT_ABS_EQ_ID])

(* TODO: word_mul should maybe target a real op ?
   TODO: econv might be going too far with case simplification
*)

val _ = translate (LoadWord64_def |> inline_simp |> conv64)
val _ = translate (WriteWord64_def |> inline_simp |> conv64)
val _ = translate (LoadBignum_def |> inline_simp |> conv64)

val _ = translate (assign_def |> SIMP_RULE std_ss [assign_rw] |> inline_simp |> conv64 |> we_simp |> SIMP_RULE std_ss[SHIFT_ZERO,shift_left_rwt] |> SIMP_RULE std_ss [word_mul_def,LET_THM]|>gconv)

(*
val data_to_word_assign_side = Q.prove(`
  ∀a b c d e f g. data_to_word_assign_side a b c d e f g ⇔ T`,
  rw[]>>
  simp[fetch "-" "data_to_word_assign_side_def",NULL]>>
  Cases_on`e`>>rw[]>>
  Cases_on`f`>>TRY(Cases_on`t`)>>TRY(Cases_on`t'`)>>fs[]) |> update_precondition
*)

val _ = save_thm ("comp_ind",data_to_wordTheory.comp_ind|> conv64|> wcomp_simp)
(* Inlines the let k = 8 manually *)
val _ = translate (comp_def |> conv64 |> wcomp_simp |> conv64 |> SIMP_RULE std_ss[LET_THM |> INST_TYPE [alpha|->``:num``]])

open word_simpTheory word_allocTheory word_instTheory

val _ = matches:= [``foo:'a wordLang$prog``,``foo:'a wordLang$exp``,``foo:'a word``,``foo: 'a reg_imm``,``foo:'a arith``,``foo: 'a addr``]

val _ = translate (INST_TYPE [beta|->``:64``]const_fp_inst_cs_def)

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

val arith_shift_right_ind_orig = theorem"arith_shift_right_ind"

val arith_shift_right_ind = (
  arith_shift_right_ind_orig |> spec64
  |> SIMP_RULE std_ss [word_msb_rw]
  |> CONV_RULE (QUANT_CONV(LAND_CONV fcpLib.INDEX_CONV)) |> gconv)
  |> curry save_thm "arith_shift_right_ind"

val _ = translate (
  arith_shift_right_def |> spec64
  |> SIMP_RULE std_ss [word_msb_rw]
  |> CONV_RULE fcpLib.INDEX_CONV |> gconv)

val _ = translate (wordLangTheory.word_sh_def |> RW[shift_left_rwt,shift_right_rwt,arith_shift_right_rwt] |> conv64)

val _ = translate (wordLangTheory.num_exp_def |> conv64)

val _ = translate (asmTheory.word_cmp_def |> REWRITE_RULE[WORD_LO,WORD_LT] |> spec64 |> REWRITE_RULE[word_msb_rw])

val _ = translate (spec64 compile_exp_def)

val _ = translate (spec64 max_var_def)

val _ = translate (conv64_RHS integer_wordTheory.w2i_eq_w2n)
val _ = translate (conv64_RHS integer_wordTheory.WORD_LEi)

val _ = translate (asmTheory.offset_ok_def |> SIMP_RULE std_ss [alignmentTheory.aligned_bitwise_and] |> conv64)
val _ = translate (inst_select_exp_def |> conv64 |> SIMP_RULE std_ss [word_mul_def,word_2comp_def] |> conv64)

val _ = translate (op_consts_def|>conv64|>econv)

val _ = translate (convert_sub_def |> conv64 |> SIMP_RULE std_ss [word_2comp_def,word_mul_def] |> conv64)

val _ = translate (spec64 pull_exp_def)

val word_inst_pull_exp_side = Q.prove(`
  ∀x. word_inst_pull_exp_side x ⇔ T`,
  ho_match_mp_tac pull_exp_ind>>rw[]>>
  simp[Once (fetch "-" "word_inst_pull_exp_side_def"),
      fetch "-" "word_inst_optimize_consts_side_def",
      wordLangTheory.word_op_def]>>
  metis_tac[]) |> update_precondition

val _ = translate (spec64 inst_select_def)

val _ = translate (spec64 list_next_var_rename_move_def)

val word_alloc_list_next_var_rename_move_side = Q.prove(`
  ∀x y z. word_alloc_list_next_var_rename_move_side x y z ⇔ T`,
  simp[fetch "-" "word_alloc_list_next_var_rename_move_side_def"]>>
  Induct_on`z`>>fs[list_next_var_rename_def]>>rw[]>>
  rpt(pairarg_tac>>fs[])>>
  res_tac>>rpt var_eq_tac>>fs[]) |> update_precondition

val _ = translate (spec64 full_ssa_cc_trans_def)

val word_alloc_full_ssa_cc_trans_side = Q.prove(`
  ∀x y. word_alloc_full_ssa_cc_trans_side x y`,
  simp[fetch "-" "word_alloc_full_ssa_cc_trans_side_def"]>>
  rw[]>>pop_assum kall_tac>>
  map_every qid_spec_tac [`v6`,`v7`,`y`]>>
  ho_match_mp_tac ssa_cc_trans_ind>>
  rw[]>>
  simp[Once (fetch "-" "word_alloc_ssa_cc_trans_side_def")]>>
  map_every qid_spec_tac [`ssa`,`na`]>>
  Induct_on`ls`>>fs[list_next_var_rename_def]>>rw[]>>
  rpt(pairarg_tac>>fs[])>>
  res_tac>>rpt var_eq_tac>>fs[]) |> update_precondition

val _ = translate (spec64 remove_dead_def)

val _ = translate (INST_TYPE [alpha|->``:64``,beta|->``:64``] get_forced_def)

val _ = translate (INST_TYPE [alpha|->``:64``,beta|->``:64``]  word_alloc_def)

val word_alloc_apply_colour_side = Q.prove(`
  ∀x y. word_alloc_apply_colour_side x y ⇔ T`,
  ho_match_mp_tac apply_colour_ind>>rw[]>>
  simp[Once(fetch"-""word_alloc_apply_colour_side_def")])

val word_alloc_word_alloc_side = Q.prove(`
  ∀v w x y z. word_alloc_word_alloc_side v w x y z ⇔ T`,
  simp[Once(fetch"-""word_alloc_word_alloc_side_def"),
  Once(fetch"-""word_alloc_oracle_colour_ok_side_def"),
  word_alloc_apply_colour_side]) |> update_precondition

val _ = translate (spec64 three_to_two_reg_def)

val _ = translate (spec64 word_removeTheory.remove_must_terminate_def)

val _ = translate (spec64 word_to_wordTheory.compile_def)

val word_to_word_compile_side = Q.prove(`
  ∀x y z. word_to_word_compile_side x y z ⇔ T`,
  simp[fetch"-""word_to_word_compile_side_def"]>>
  Induct_on`z`>>fs[word_to_wordTheory.next_n_oracle_def]) |> update_precondition

val _ = translate(Maxout_bits_code_def |> conv64)
val _ = translate(Make_ptr_bits_code_def |> inline_simp |> conv64)
val _ = translate(AllocVar_def |> inline_simp |> wcomp_simp |> conv64)
val _ = translate(FromList_code_def |> conv64 |> econv)
val _ = translate(FromList1_code_def |> inline_simp |> conv64)
val _ = translate(MakeBytes_def |> conv64)
val _ = translate(RefByte_code_def |> inline_simp |> conv64 |> SIMP_RULE std_ss[SmallLsr_def])
val _ = translate(RefArray_code_def |> inline_simp |> conv64|>econv)
val _ = translate(Replicate_code_def|> inline_simp |> conv64)

val _ = translate (data_to_wordTheory.compile_def |> SIMP_RULE std_ss [data_to_wordTheory.stubs_def] |> conv64_RHS)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory();
