open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open basisProgTheory;

val _ = new_theory "to_dataProg"
val _ = translation_extends "basisProg";

(* This is the compiler "preamble" that translates the compile functions down to dataLang *)

val RW = REWRITE_RULE
val RW1 = ONCE_REWRITE_RULE
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];
val dest_fun_type = dom_rng
val mk_fun_type = curry op -->;
fun list_mk_fun_type [ty] = ty
  | list_mk_fun_type (ty1::tys) =
      mk_fun_type ty1 (list_mk_fun_type tys)
  | list_mk_fun_type _ = fail()

val _ = add_preferred_thy "-";
val _ = add_preferred_thy "termination";

val NOT_NIL_AND_LEMMA = Q.prove(
  `(b <> [] /\ x) = if b = [] then F else x`,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val _ = use_long_names:=true;

(* TODO:
   this is a discrepancy between HOL's standard libraries and
   mllist. probably the compiler should be using the mllist versions? *)
val res = translate EL;
val list_el_side = Q.prove(
  `!n xs. list_el_side n xs = (n < LENGTH xs)`,
  Induct THEN Cases_on `xs` THEN ONCE_REWRITE_TAC [fetch "-" "list_el_side_def"]
  THEN FULL_SIMP_TAC (srw_ss()) [CONTAINER_def])
  |> update_precondition;
(* -- *)

val res = translate (source_to_modTheory.compile_exp_def);

val source_to_mod_compile_exp_side_def = theorem"source_to_mod_compile_exp_side_def"
val source_to_mod_compile_exp_side = Q.prove(
  `(∀x y z. source_to_mod_compile_exp_side x y z ⇔ T) ∧
   (∀x y z. source_to_mod_compile_exps_side x y z ⇔ T) ∧
   (∀x y z. source_to_mod_compile_pes_side x y z ⇔ T) ∧
   (∀x y z. source_to_mod_compile_funs_side x y z ⇔ T)`,
  ho_match_mp_tac source_to_modTheory.compile_exp_ind \\ rw[]
  \\ rw[Once source_to_mod_compile_exp_side_def]
  \\ rw[definition"source_to_mod_astop_to_modop_side_def"])
  |> CONJUNCTS
  |> map update_precondition;

val _ = translate (source_to_modTheory.compile_def);

val _ = translate (mod_to_conTheory.compile_def);

val r = translate con_to_decTheory.compile_decs_def;
val con_to_dec_compile_decs_side_def = theorem"con_to_dec_compile_decs_side_def";
val con_to_dec_compile_decs_side = Q.prove(
  `∀x y z. con_to_dec_compile_decs_side x y z ⇔ T`,
  Induct_on`z` \\ rw[Once con_to_dec_compile_decs_side_def])
  |> update_precondition;

val r = translate (con_to_decTheory.compile_def);

val r = translate (exh_reorderTheory.compile_def);

val exh_reorder_compile_side_def = theorem"exh_reorder_compile_side_def"
val exh_reorder_compile_side = Q.prove(`
  ∀x. exh_reorder_compile_side x ⇔ T`,
  recInduct exh_reorderTheory.compile_ind>>
  rw[]>>
  rw[Once exh_reorder_compile_side_def]>>
  TRY(first_x_assum match_mp_tac \\ rw[]) \\
  TRY(asm_exists_tac \\ rw[]) \\
  fs[Once exh_reorderTheory.compile_cons])|>update_precondition;

val r = translate (dec_to_exhTheory.compile_def);

val dec_to_exh_compile_side_def = definition"dec_to_exh_compile_side_def";
val dec_to_exh_compile_side = Q.prove(
  `∀x y. dec_to_exh_compile_side x y ⇔ T`,
  rw[dec_to_exh_compile_side_def,Once exh_reorderTheory.compile_cons])
  |> update_precondition;

val r = translate (exh_to_patTheory.pure_op_op_pmatch);
val r = translate (exh_to_patTheory.compile_def);

local
  val ths = ml_translatorLib.eq_lemmas();
in
  fun find_equality_type_thm tm =
    first (can (C match_term tm) o rand o snd o strip_imp o concl) ths
end

val EqualityType_CHAR = find_equality_type_thm``CHAR``
val EqualityType_INT = find_equality_type_thm``INT``
val EqualityType_NUM = find_equality_type_thm``NUM``
val EqualityType_BOOL = find_equality_type_thm``BOOL``
val EqualityType_WORD = find_equality_type_thm``WORD``

val EqualityType_LIST_TYPE_CHAR = find_equality_type_thm``LIST_TYPE CHAR``
  |> Q.GEN`a` |> Q.ISPEC`CHAR` |> SIMP_RULE std_ss [EqualityType_CHAR]

val EqualityType_AST_LIT_TYPE = find_equality_type_thm``AST_LIT_TYPE``
  |> SIMP_RULE std_ss [EqualityType_CHAR,EqualityType_LIST_TYPE_CHAR,
                       EqualityType_INT,EqualityType_BOOL,EqualityType_WORD]

val EqualityType_AST_OPN_TYPE = find_equality_type_thm``AST_OPN_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_OPB_TYPE = find_equality_type_thm``AST_OPB_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_OPW_TYPE = find_equality_type_thm``AST_OPW_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_WORD_SIZE_TYPE = find_equality_type_thm``AST_WORD_SIZE_TYPE`` |> SIMP_RULE std_ss []
val EqualityType_AST_SHIFT_TYPE = find_equality_type_thm``AST_SHIFT_TYPE`` |> SIMP_RULE std_ss []

val EqualityType_AST_OP_TYPE = find_equality_type_thm``AST_OP_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM,
                       EqualityType_AST_OPB_TYPE,EqualityType_AST_OPN_TYPE,EqualityType_AST_OPW_TYPE,
                       EqualityType_AST_WORD_SIZE_TYPE,EqualityType_AST_SHIFT_TYPE,
                       EqualityType_LIST_TYPE_CHAR]

val EqualityType_FPSEM_FP_BOP_TYPE = find_equality_type_thm ``FPSEM_FP_BOP_TYPE``
val EqualityType_FPSEM_FP_UOP_TYPE = find_equality_type_thm ``FPSEM_FP_UOP_TYPE``
val EqualityType_FPSEM_FP_CMP_TYPE = find_equality_type_thm ``FPSEM_FP_CMP_TYPE``

val EqualityType_MODLANG_OP_TYPE = find_equality_type_thm``MODLANG_OP_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM,
                       EqualityType_AST_OPB_TYPE,EqualityType_AST_OPN_TYPE,EqualityType_AST_OPW_TYPE,
                       EqualityType_AST_WORD_SIZE_TYPE,EqualityType_AST_SHIFT_TYPE,
                       EqualityType_LIST_TYPE_CHAR,
                       EqualityType_FPSEM_FP_BOP_TYPE,
                       EqualityType_FPSEM_FP_UOP_TYPE,
                       EqualityType_FPSEM_FP_CMP_TYPE
                       ]

val EqualityType_CONLANG_OP_TYPE = find_equality_type_thm``CONLANG_OP_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_AST_OP_TYPE]

val EqualityType_PATLANG_OP_TYPE = find_equality_type_thm``PATLANG_OP_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_CONLANG_OP_TYPE]

val EqualityType_BACKEND_COMMON_TRA_TYPE = find_equality_type_thm``BACKEND_COMMON_TRA_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM]

val ctor_same_type_def = semanticPrimitivesTheory.ctor_same_type_def

val EXHLANG_PAT_TYPE_def = theorem"EXHLANG_PAT_TYPE_def";
val EXHLANG_PAT_TYPE_ind = theorem"EXHLANG_PAT_TYPE_ind";

val EXHLANG_PAT_TYPE_no_closures = Q.prove(
  `∀a b. EXHLANG_PAT_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac EXHLANG_PAT_TYPE_ind
  \\ rw[EXHLANG_PAT_TYPE_def]
  \\ rw[no_closures_def]
  \\ TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,no_closures_def] >>
    qx_gen_tac`p` >>
    simp[PULL_EXISTS,no_closures_def] >>
    rw[] >>
    METIS_TAC[EqualityType_def] ) >>
  metis_tac[EqualityType_NUM,
            EqualityType_AST_LIT_TYPE,
            EqualityType_LIST_TYPE_CHAR,
            EqualityType_def]);

val EXHLANG_PAT_TYPE_types_match = Q.prove(
  `∀a b c d. EXHLANG_PAT_TYPE a b ∧ EXHLANG_PAT_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac EXHLANG_PAT_TYPE_ind \\
  rw[EXHLANG_PAT_TYPE_def] \\
  Cases_on`c` \\ fs[EXHLANG_PAT_TYPE_def,types_match_def,ctor_same_type_def] \\ rw[] \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`x2`,`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] ) >>
    qx_gen_tac`p` >>
    gen_tac >> Cases >> simp[PULL_EXISTS,LIST_TYPE_def] >>
    rw[types_match_def,ctor_same_type_def] >>
    PROVE_TAC[EqualityType_def] ) >>
  metis_tac[EqualityType_NUM,
            EqualityType_AST_LIT_TYPE,
            EqualityType_LIST_TYPE_CHAR,
            EqualityType_def]);

val EXHLANG_PAT_TYPE_11 = Q.prove(
  `∀a b c d. EXHLANG_PAT_TYPE a b ∧ EXHLANG_PAT_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac EXHLANG_PAT_TYPE_ind \\
  rw[EXHLANG_PAT_TYPE_def] \\
  Cases_on`c` \\ fs[EXHLANG_PAT_TYPE_def] \\ rw[EQ_IMP_THM] \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`y1`,`x`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >>
    rw[] >>
    metis_tac[]) >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y`,`x1`,`x2`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >- (
      Cases \\ rw[LIST_TYPE_def] ) \\
    gen_tac \\ Cases \\ rw[LIST_TYPE_def] >>
    metis_tac[]) >>
  metis_tac[EqualityType_NUM,
            EqualityType_AST_LIT_TYPE,
            EqualityType_LIST_TYPE_CHAR,
            EqualityType_def]);

val EqualityType_EXHLANG_PAT_TYPE = Q.store_thm("EqualityType_EXHLANG_PAT_TYPE",
  `EqualityType EXHLANG_PAT_TYPE`,
  metis_tac[EqualityType_def,EXHLANG_PAT_TYPE_no_closures,
    EXHLANG_PAT_TYPE_types_match,EXHLANG_PAT_TYPE_11])
  |> store_eq_thm

val PATLANG_EXP_TYPE_def = theorem"PATLANG_EXP_TYPE_def";
val PATLANG_EXP_TYPE_ind = theorem"PATLANG_EXP_TYPE_ind";

val PATLANG_EXP_TYPE_no_closures = Q.prove(
  `∀a b. PATLANG_EXP_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac PATLANG_EXP_TYPE_ind \\
  rw[PATLANG_EXP_TYPE_def] \\ rw[no_closures_def] \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,no_closures_def] >>
    qx_gen_tac`p` >>
    simp[PULL_EXISTS,no_closures_def] >>
    rw[] >>
    METIS_TAC[EqualityType_def] ) >>
  metis_tac[EqualityType_NUM,
            EqualityType_BACKEND_COMMON_TRA_TYPE,
            EqualityType_MODLANG_OP_TYPE,
            EqualityType_CONLANG_OP_TYPE,
            EqualityType_PATLANG_OP_TYPE,
            EqualityType_AST_LIT_TYPE,
            EqualityType_def]);

val PATLANG_EXP_TYPE_types_match = Q.prove(
  `∀a b c d. PATLANG_EXP_TYPE a b ∧ PATLANG_EXP_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac PATLANG_EXP_TYPE_ind \\
  rw[PATLANG_EXP_TYPE_def] \\
  Cases_on`c` \\ fs[PATLANG_EXP_TYPE_def,types_match_def,ctor_same_type_def] \\ rw[] \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`x2`,`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] ) >>
    qx_gen_tac`p` >>
    gen_tac >> Cases >> simp[PULL_EXISTS,LIST_TYPE_def] >>
    rw[types_match_def,ctor_same_type_def] >>
    PROVE_TAC[EqualityType_def] ) >>
  metis_tac[EqualityType_NUM,
            EqualityType_BACKEND_COMMON_TRA_TYPE,
            EqualityType_MODLANG_OP_TYPE,
            EqualityType_CONLANG_OP_TYPE,
            EqualityType_PATLANG_OP_TYPE,
            EqualityType_AST_LIT_TYPE,
            EqualityType_def]);

val PATLANG_EXP_TYPE_11 = Q.prove(
  `∀a b c d. PATLANG_EXP_TYPE a b ∧ PATLANG_EXP_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac PATLANG_EXP_TYPE_ind \\
  rw[PATLANG_EXP_TYPE_def] \\
  Cases_on`c` \\ fs[PATLANG_EXP_TYPE_def] \\ rw[EQ_IMP_THM] \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`y1`,`x`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >>
    rw[] >>
    metis_tac[]) >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y`,`x1`,`x2`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >- (
      Cases \\ rw[LIST_TYPE_def] ) \\
    gen_tac \\ Cases \\ rw[LIST_TYPE_def] >>
    metis_tac[]) >>
  metis_tac[EqualityType_NUM,
            EqualityType_BACKEND_COMMON_TRA_TYPE,
            EqualityType_MODLANG_OP_TYPE,
            EqualityType_CONLANG_OP_TYPE,
            EqualityType_PATLANG_OP_TYPE,
            EqualityType_AST_LIT_TYPE,
            EqualityType_def]);

val EqualityType_PATLANG_EXP_TYPE = Q.prove(
  `EqualityType PATLANG_EXP_TYPE`,
  metis_tac[EqualityType_def,PATLANG_EXP_TYPE_no_closures,PATLANG_EXP_TYPE_types_match,PATLANG_EXP_TYPE_11])
  |> store_eq_thm

val r = translate (pat_to_closTheory.compile_def);

val pat_to_clos_compile_side = Q.prove(`
  ∀x. pat_to_clos_compile_side x ⇔ T`,
  recInduct pat_to_closTheory.compile_ind>>
  rw[]>>
  simp[Once (fetch "-" "pat_to_clos_compile_side_def")]>>
  Cases_on`es`>>fs[])|>update_precondition;

val _ = translate(clos_mtiTheory.intro_multi_def)

val clos_mti_intro_multi_side = Q.prove(`
  ∀max_app a. clos_mti_intro_multi_side max_app a ⇔ T`,
  ho_match_mp_tac clos_mtiTheory.intro_multi_ind>>
  `∀max_app z. intro_multi max_app [z] ≠ []` by
    (rw[] >> CCONTR_TAC>>fs[]>>
     Q.SPECL_THEN [`z`,`max_app`] mp_tac clos_mtiTheory.intro_multi_sing >>fs[])>>
  rw[]>>
  simp[Once (fetch "-" "clos_mti_intro_multi_side_def")]>>
  metis_tac[])|>update_precondition

(* number
TODO: make this not have to be explicitly translated, probably by renaming it to renumber_code_locs_list_def
*)
val _ = translate (clos_numberTheory.renumber_code_locs_def)

(* known *)
(*val _ = patternMatchesLib.ENABLE_PMATCH_CASES();*)

val _ = translate clos_knownTheory.merge_alt

val num_abs_intro = Q.prove(`
  ∀x. Num x = if 0 ≤ x then Num (ABS x) else Num x`,
  rw[]>>intLib.COOPER_TAC);

val _ = translate (clos_knownTheory.known_op_def |> ONCE_REWRITE_RULE [num_abs_intro] |> SIMP_RULE std_ss []);

(*
(* TODO:
   This is uglier than previously, to prevent SIMP_RULE from rewriting guards
   OF PMATCH_ROWs to K T *)
val lemma = ``(if 0 <= i /\ q
            then (EL (Num i) xs,g)
            else x)`` |> (ONCE_REWRITE_CONV [num_abs_intro] THENC SIMP_CONV std_ss [])

val _ = translate (clos_knownTheory.known_op_pmatch |> ONCE_REWRITE_RULE [lemma]);
*)

val clos_known_known_op_side = Q.prove(`
  ∀a b c. clos_known_known_op_side a b c ⇔ T`,
  rpt strip_tac >> Cases_on `b` >>
  simp[Once (fetch"-" "clos_known_known_op_side_def")]>>
  fs[]>>rw[]>>
  intLib.COOPER_TAC) |> update_precondition;

(*
val clos_known_known_op_side = Q.prove(`
  ∀a b c. clos_known_known_op_side a b c ⇔ T`,
  rpt strip_tac >> Cases_on `b` >>
  simp[Once (fetch"-" "clos_known_known_op_side_def")]>>
  fs[clos_known_merge_side]>-
  metis_tac[option_nchotomy]>-
  (rpt strip_tac >-
  metis_tac[option_nchotomy] >-
  intLib.COOPER_TAC))
*)

val r = translate (clos_knownTheory.known_def)

val clos_known_known_side = Q.prove(`
  ∀a b c. clos_known_known_side a b c ⇔ T`,
  ho_match_mp_tac clos_knownTheory.known_ind>>
  `∀z a b c. known [z] a b ≠ ([],c)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac clos_knownTheory.known_sing_EQ_E>>
    fs[])>>
  rw[]>>simp[Once (fetch"-" "clos_known_known_side_def")]>>
  metis_tac[FST,PAIR]) |> update_precondition

val r = translate clos_knownTheory.compile_def

val clos_known_compile_side = Q.prove(
  `∀x y. clos_known_compile_side x y ⇔ T`,
  EVAL_TAC \\ rw[] \\ strip_tac \\
  imp_res_tac clos_knownTheory.known_sing_EQ_E \\
  fs[]) |> update_precondition;

(* call *)

val r = translate (clos_callTheory.calls_def)

val clos_call_free_side = Q.prove(`
  ∀a. clos_call_free_side a ⇔ T`,
  ho_match_mp_tac clos_callTheory.free_ind>>rw[]>>
  simp[Once (fetch "-" "clos_call_free_side_def")]>>rw[]>>
  CCONTR_TAC>>fs[]>>
  imp_res_tac clos_callTheory.free_SING>>fs[]>>
  metis_tac[]) |> update_precondition

val clos_call_calls_side = Q.prove(`
  ∀a b. clos_call_calls_side a b ⇔ T`,
  ho_match_mp_tac clos_callTheory.calls_ind>>
  (*Move from calls proof*)
  `∀a b c. calls [a] b ≠ ([],c)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac clos_callTheory.calls_sing>>fs[])>>
  rw[]>> simp[Once (fetch"-" "clos_call_calls_side_def"),Once (fetch "-" "clos_call_closed_side_def"),clos_call_free_side]>>
  TRY(metis_tac[])>>
  ntac 2 strip_tac>>
  simp[LAMBDA_PROD]>> rw[fetch "-" "clos_call_closed_side_def",clos_call_free_side]
  >> rw[GSYM LAMBDA_PROD]) |> update_precondition

val r = translate clos_callTheory.compile_def

val clos_call_compile_side = Q.prove(
  `∀x y. clos_call_compile_side x y = T`,
  EVAL_TAC \\ rw[] \\ strip_tac \\
  imp_res_tac clos_callTheory.calls_sing \\
  fs[]) |> update_precondition;

(* shift *)
val r = translate (clos_annotateTheory.shift_def)

val clos_annotate_shift_side = Q.prove(`
  ∀a b c d. clos_annotate_shift_side a b c d ⇔ T`,
  ho_match_mp_tac clos_annotateTheory.shift_ind>>
  `∀a b c d. shift [a] b c d ≠ []` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac clos_annotateTheory.shift_SING>>
    fs[])>>
  rw[]>>
  simp[Once (fetch "-" "clos_annotate_shift_side_def")]>>
  rw[]>> metis_tac[]) |> update_precondition

val r = translate clos_annotateTheory.compile_def

val clos_annotate_alt_free_side = Q.prove(
  `∀x. clos_annotate_alt_free_side x ⇔ T`,
  ho_match_mp_tac clos_annotateTheory.alt_free_ind \\ rw[] \\
  simp[Once(fetch "-" "clos_annotate_alt_free_side_def")] \\
  rw[] \\ fs[] \\
  CCONTR_TAC \\ fs[] \\
  imp_res_tac clos_annotateTheory.alt_free_SING \\ fs[] \\
  METIS_TAC[]) |> update_precondition;

val clos_annotate_compile_side = Q.prove(
  `∀x. clos_annotate_compile_side x = T`,
  EVAL_TAC \\ rw[clos_annotate_alt_free_side] \\
  METIS_TAC[clos_annotateTheory.shift_SING,clos_annotateTheory.alt_free_SING,
            FST,PAIR,list_distinct]) |> update_precondition;

val r = translate clos_to_bvlTheory.compile_def

val BVL_EXP_TYPE_def = theorem"BVL_EXP_TYPE_def";
val BVL_EXP_TYPE_ind = theorem"BVL_EXP_TYPE_ind";

local
  val ths = ml_translatorLib.eq_lemmas();
in
  fun find_equality_type_thm tm =
    first (can (C match_term tm) o rand o snd o strip_imp o concl) ths
end

val EqualityType_CLOSLANG_OP_TYPE = find_equality_type_thm``CLOSLANG_OP_TYPE``
  |> SIMP_RULE std_ss [
      EqualityType_NUM,EqualityType_INT,
      EqualityType_AST_SHIFT_TYPE,
      EqualityType_AST_OPW_TYPE,
      EqualityType_AST_WORD_SIZE_TYPE,
      EqualityType_LIST_TYPE_CHAR,
      EqualityType_BOOL,
      EqualityType_FPSEM_FP_BOP_TYPE,
      EqualityType_FPSEM_FP_UOP_TYPE,
      EqualityType_FPSEM_FP_CMP_TYPE
      ]

val EqualityType_OPTION_TYPE_NUM = find_equality_type_thm``OPTION_TYPE NUM``
  |> Q.GEN`a` |> Q.ISPEC`NUM` |> SIMP_RULE std_ss [EqualityType_NUM]

val BVL_EXP_TYPE_no_closures = Q.prove(
  `∀a b. BVL_EXP_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac BVL_EXP_TYPE_ind \\
  rw[BVL_EXP_TYPE_def] \\ rw[no_closures_def] \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,no_closures_def] >>
    qx_gen_tac`p` >>
    simp[PULL_EXISTS,no_closures_def] >>
    rw[] >>
    METIS_TAC[EqualityType_def] ) >>
  metis_tac[EqualityType_NUM,
            EqualityType_CLOSLANG_OP_TYPE,
            EqualityType_OPTION_TYPE_NUM,
            EqualityType_def]);

val BVL_EXP_TYPE_types_match = Q.prove(
  `∀a b c d. BVL_EXP_TYPE a b ∧ BVL_EXP_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac BVL_EXP_TYPE_ind \\
  rw[BVL_EXP_TYPE_def] \\
  Cases_on`c` \\ fs[BVL_EXP_TYPE_def,types_match_def,ctor_same_type_def] \\ rw[] \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`x2`,`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] ) >>
    qx_gen_tac`p` >>
    gen_tac >> Cases >> simp[PULL_EXISTS,LIST_TYPE_def] >>
    rw[types_match_def,ctor_same_type_def] >>
    PROVE_TAC[EqualityType_def] ) >>
  metis_tac[EqualityType_NUM,
            EqualityType_CLOSLANG_OP_TYPE,
            EqualityType_OPTION_TYPE_NUM,
            EqualityType_def]);

val BVL_EXP_TYPE_11 = Q.prove(
  `∀a b c d. BVL_EXP_TYPE a b ∧ BVL_EXP_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac BVL_EXP_TYPE_ind \\
  rw[BVL_EXP_TYPE_def] \\
  Cases_on`c` \\ fs[BVL_EXP_TYPE_def] \\ rw[EQ_IMP_THM] \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`y1`,`x`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >>
    rw[] >>
    metis_tac[]) >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y`,`x1`,`x2`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >- (
      Cases \\ rw[LIST_TYPE_def] ) \\
    gen_tac \\ Cases \\ rw[LIST_TYPE_def] >>
    metis_tac[]) >>
  metis_tac[EqualityType_NUM,
            EqualityType_CLOSLANG_OP_TYPE,
            EqualityType_OPTION_TYPE_NUM,
            EqualityType_def]);

val EqualityType_BVL_EXP_TYPE = Q.prove(
  `EqualityType BVL_EXP_TYPE`,
  metis_tac[EqualityType_def,BVL_EXP_TYPE_no_closures,BVL_EXP_TYPE_types_match,BVL_EXP_TYPE_11])
  |> store_eq_thm;

val bvl_jump_jumplist_side = Q.prove(`
  ∀a b. bvl_jump_jumplist_side a b ⇔ T`,
  completeInduct_on`LENGTH (b:bvl$exp list)`>>
  rw[Once (fetch "-" "bvl_jump_jumplist_side_def")]
  >-
    (Cases_on`b`>>fs[])
  >>
  fs[PULL_FORALL]>>
  first_assum match_mp_tac>>
  fs[]
  >-
    (Cases_on`x1`>>fs[ADD_DIV_RWT,ADD1])
  >>
    `SUC x1 DIV 2 < SUC x1` by
      fs[]>>
    simp[]) |> update_precondition;

val clos_to_bvl_recc_lets_side = Q.prove(`
  ∀a b c d.
  c = LENGTH b ⇒
  clos_to_bvl_recc_lets_side a b c d`,
  ho_match_mp_tac clos_to_bvlTheory.recc_Lets_ind>>
  rw[]>>
  simp[Once (fetch"-" "clos_to_bvl_recc_lets_side_def")]>>
  Cases_on`b`>>fs[]) |> update_precondition;

val clos_to_bvl_compile_exps_side = Q.prove(`
  ∀max_app a b. clos_to_bvl_compile_exps_side max_app a b`,
  ho_match_mp_tac clos_to_bvlTheory.compile_exps_ind>>
  `∀max_app a b c. compile_exps max_app [a] b ≠ ([],c)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac clos_to_bvlTheory.compile_exps_SING>>
    fs[])>>
  rw[]>>
  simp[Once (fetch "-" "clos_to_bvl_compile_exps_side_def")]>>
  TRY (metis_tac[])>>
  rw[]
  >-
    (fs[fetch"-" "clos_to_bvl_build_recc_lets_side_def"]>>
    match_mp_tac clos_to_bvl_recc_lets_side>>
    simp[LENGTH_TL])
  >>
  first_x_assum(qspecl_then[`max_app`,`x1`,`x43`,`x41`] assume_tac)>>
  CCONTR_TAC>>fs[]) |> update_precondition;

val clos_to_bvl_compile_prog_side = Q.prove(`
  ∀max_app x. clos_to_bvl_compile_prog_side max_app x ⇔ T`,
  ho_match_mp_tac clos_to_bvlTheory.compile_prog_ind>>rw[]>>
  simp[Once (fetch "-" "clos_to_bvl_compile_prog_side_def"),clos_to_bvl_compile_exps_side])
  |> update_precondition;

val clos_to_bvl_compile_side = Q.prove(`
  ∀x y. clos_to_bvl_compile_side x y ⇔ T`,
  rw[Once (fetch "-" "clos_to_bvl_compile_side_def"),
  Once (fetch "-" "clos_call_compile_side_def"),
  Once (fetch "-" "clos_to_bvl_compile_prog_side_def"),
  Once (fetch "-" "clos_known_compile_side_def")]
  >-
    (EVAL_TAC>>simp[bvl_jump_jumplist_side])
  >-
    simp[clos_to_bvl_compile_exps_side]
  >-
    simp[clos_to_bvl_compile_prog_side]
  >>
    `∃z. compile x.do_mti x.max_app [y] = [z]` by
      (Cases_on`x.do_mti`>>fs[clos_mtiTheory.compile_def]>>
      metis_tac[clos_mtiTheory.intro_multi_sing])>>
    ntac 2 (pop_assum mp_tac)>>
    specl_args_of_then ``renumber_code_locs_list`` (clos_numberTheory.renumber_code_locs_length|>CONJUNCT1) assume_tac>>
    rw[]>>fs[]>>
    fs[LENGTH_EQ_NUM_compute]) |> update_precondition

val _ = translate (bvl_handleTheory.LetLet_def |> SIMP_RULE std_ss [MAPi_enumerate_MAP])

val _ = translate(bvl_handleTheory.compile_def)

val bvl_handle_compile_side = Q.prove(`
  ∀x y z. bvl_handle_compile_side x y z ⇔ T`,
  ho_match_mp_tac bvl_handleTheory.compile_ind>>
  `∀a b c d e. bvl_handle$compile a b [c] ≠ ([],d,e)` by
  (CCONTR_TAC>>fs[]>>
  imp_res_tac bvl_handleTheory.compile_sing>>
  fs[])>>
  rw[]>>
  simp[Once (fetch "-" "bvl_handle_compile_side_def")]>>
  TRY (metis_tac[])>>
  rw[]>>fs[]>>
  metis_tac[])|>update_precondition

val _ = translate (bvl_inlineTheory.inline_def)

val bvl_inline_inline_side = Q.prove(`
  ∀x y. bvl_inline_inline_side x y ⇔ T`,
  ho_match_mp_tac bvl_inlineTheory.inline_ind>>
  `∀a b. bvl_inline$inline a [b] ≠ []` by
    (CCONTR_TAC>>fs[]>>
    pop_assum (mp_tac o Q.AP_TERM`LENGTH`)>>
    simp[bvl_inlineTheory.LENGTH_inline])>>
  rw[]>>
  simp[Once (fetch "-" "bvl_inline_inline_side_def")])|>update_precondition

val _ = translate (bvl_constTheory.compile_def)

val bvl_const_compile_side = Q.prove(`
  ∀x y. bvl_const_compile_side x y ⇔ T`,
  ho_match_mp_tac bvl_constTheory.compile_ind>>
  `∀a b. bvl_const$compile a [b] ≠ []` by
    (CCONTR_TAC>>fs[]>>
    pop_assum (mp_tac o Q.AP_TERM`LENGTH`)>>
    simp[bvl_constTheory.compile_length])>>
  rw[]>>
  simp[Once (fetch "-" "bvl_const_compile_side_def")])|>update_precondition

val _ = translate(bvl_to_bviTheory.compile_int_def)

val bvl_to_bvi_compile_int_side = Q.prove(`
  ∀x. bvl_to_bvi_compile_int_side x ⇔ T`,
  completeInduct_on`Num(ABS x)`>>
  simp[Once (fetch "-" "bvl_to_bvi_compile_int_side_def")]>>
  rw[]>>fs[PULL_FORALL]>>
  first_assum MATCH_MP_TAC>>
  intLib.COOPER_TAC) |> update_precondition

val BVI_EXP_TYPE_def = theorem"BVI_EXP_TYPE_def";
val BVI_EXP_TYPE_ind = theorem"BVI_EXP_TYPE_ind";

val BVI_EXP_TYPE_no_closures = Q.prove(
  `∀a b. BVI_EXP_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac BVI_EXP_TYPE_ind \\
  rw[BVI_EXP_TYPE_def] \\ rw[no_closures_def] \\
  TRY (
    qmatch_assum_rename_tac`OPTION_TYPE _ x y` \\
    Cases_on`x` \\ fs[OPTION_TYPE_def] \\
    rw[no_closures_def] \\ NO_TAC) \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qpat_x_assum`∀a b. MEM a x1 ⇒ _` mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,no_closures_def] >>
    qx_gen_tac`p` >>
    simp[PULL_EXISTS,no_closures_def] >>
    rw[] >>
    METIS_TAC[EqualityType_def] ) >>
  metis_tac[EqualityType_NUM,
            EqualityType_CLOSLANG_OP_TYPE,
            EqualityType_OPTION_TYPE_NUM,
            EqualityType_def]);

val BVI_EXP_TYPE_types_match = Q.prove(
  `∀a b c d. BVI_EXP_TYPE a b ∧ BVI_EXP_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac BVI_EXP_TYPE_ind \\
  rw[BVI_EXP_TYPE_def] \\
  Cases_on`c` \\ fs[BVI_EXP_TYPE_def,types_match_def,ctor_same_type_def] \\ rw[] \\
  TRY (
    qmatch_assum_rename_tac`OPTION_TYPE _ x1 y1` \\
    qhdtm_x_assum`OPTION_TYPE`mp_tac \\
    qmatch_assum_rename_tac`OPTION_TYPE BVI_EXP_TYPE x2 y2` \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[OPTION_TYPE_def] \\
    rw[] \\ rw[types_match_def,ctor_same_type_def] \\
    metis_tac[]) \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qpat_x_assum`∀a b. MEM a x2 ⇒ _` mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`x2`,`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] ) >>
    qx_gen_tac`p` >>
    gen_tac >> Cases >> simp[PULL_EXISTS,LIST_TYPE_def] >>
    rw[types_match_def,ctor_same_type_def] >>
    PROVE_TAC[EqualityType_def] ) >>
  metis_tac[EqualityType_NUM,
            EqualityType_CLOSLANG_OP_TYPE,
            EqualityType_OPTION_TYPE_NUM,
            EqualityType_def]);

val BVI_EXP_TYPE_11 = Q.prove(
  `∀a b c d. BVI_EXP_TYPE a b ∧ BVI_EXP_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac BVI_EXP_TYPE_ind \\
  rw[BVI_EXP_TYPE_def] \\
  Cases_on`c` \\ fs[BVI_EXP_TYPE_def] \\ rw[EQ_IMP_THM] \\
  TRY (
    qmatch_assum_rename_tac`OPTION_TYPE BVI_EXP_TYPE x y1` \\
    qhdtm_x_assum`OPTION_TYPE`mp_tac \\
    qmatch_assum_rename_tac`OPTION_TYPE BVI_EXP_TYPE x y2` \\
    Cases_on`x` \\ fs[OPTION_TYPE_def] \\ rw[] \\
    metis_tac[]) \\
  TRY (
    qmatch_assum_rename_tac`OPTION_TYPE BVI_EXP_TYPE x1 y` \\
    qhdtm_x_assum`OPTION_TYPE`mp_tac \\
    qmatch_assum_rename_tac`OPTION_TYPE BVI_EXP_TYPE x2 y` \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[OPTION_TYPE_def] \\ rw[] \\
    metis_tac[]) \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qpat_x_assum`∀a b. MEM a x ⇒ _` mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`y1`,`x`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >>
    rw[] >>
    metis_tac[]) >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qpat_x_assum`∀a b. MEM a x2 ⇒ _` mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y`,`x1`,`x2`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >- (
      Cases \\ rw[LIST_TYPE_def] ) \\
    gen_tac \\ Cases \\ rw[LIST_TYPE_def] >>
    metis_tac[]) >>
  metis_tac[EqualityType_NUM,
            EqualityType_CLOSLANG_OP_TYPE,
            EqualityType_OPTION_TYPE_NUM,
            EqualityType_def]);

val EqualityType_BVI_EXP_TYPE = Q.prove(
  `EqualityType BVI_EXP_TYPE`,
  metis_tac[EqualityType_def,BVI_EXP_TYPE_no_closures,BVI_EXP_TYPE_types_match,BVI_EXP_TYPE_11])
  |> store_eq_thm;

val _ = translate(bvi_letTheory.compile_def)

val bvi_let_compile_side = Q.prove(`
  ∀x y z. bvi_let_compile_side x y z ⇔ T`,
  ho_match_mp_tac bvi_letTheory.compile_ind>>rw[]>>
  `∀a b c . bvi_let$compile a b [c] ≠ []` by
    (CCONTR_TAC>>fs[]>>
    pop_assum (mp_tac o Q.AP_TERM`LENGTH`)>>
    simp[bvi_letTheory.compile_length])>>
  rw[]>>simp[Once (fetch "-" "bvi_let_compile_side_def")]>>
  Cases_on`z`>>fs[]>>
  strip_tac>>fs[ADD1]) |> update_precondition

val _ = translate(bvi_letTheory.compile_exp_def);

val _ = translate bvi_tailrecTheory.scan_expr_def

val bvi_tailrec_scan_expr_side = Q.prove (
  `!a0 a1 a2. bvi_tailrec_scan_expr_side a0 a1 a2 <=> T`,
  ho_match_mp_tac bvi_tailrecTheory.scan_expr_ind \\ rw []
  \\ simp [Once (fetch "-" "bvi_tailrec_scan_expr_side_def")]
  \\ PURE_FULL_CASE_TAC \\ fs [])
  |> update_precondition

val rewrite_alt_def = Define `
  rewrite_alt loc next op acc ts x =
    case x of
      Var n => (F, Var n)
    | If xi xt xe =>
        let (ti, tyi, ri, iop) = HD (scan_expr ts loc [xi]) in
        let (rt, yt) = rewrite_alt loc next op acc ti xt in
        let (re, ye) = rewrite_alt loc next op acc ti xe in
        let zt = if rt then yt else apply_op op xt (Var acc) in
        let ze = if re then ye else apply_op op xe (Var acc) in
          (rt ∨ re, If xi zt ze)
    | Let xs x =>
        let ys = scan_expr ts loc xs in
        let tt = MAP (FST o SND) ys in
        let tr = (case LAST1 ys of SOME c => FST c | NONE => ts) in
        let (r, y) = rewrite_alt loc next op (acc + LENGTH xs) (tt ++ tr) x in
          (r, Let xs y)
    | Tick x =>
        let (r, y) = rewrite_alt loc next op acc ts x in (r, Tick y)
    | Raise x => (F, Raise x)
    | exp =>
        case rewrite_op ts op loc exp of
          (F, _)    => (F, apply_op op exp (Var acc))
        | (T, exp1) =>
          case get_bin_args exp1 of
            NONE => (F, apply_op op exp (Var acc))
          | SOME (call, exp2) =>
              (T, push_call next op acc exp2 (args_from call))`;

val _ = translate rewrite_alt_def

val rewrite_alt_side = Q.prove (
  `!a0 a1 a2 a3 a4 a5. to_dataprog_rewrite_alt_side a0 a1 a2 a3 a4 a5 <=> T`,
  ho_match_mp_tac (theorem "rewrite_alt_ind") \\ rw []
  \\ once_rewrite_tac [fetch "-" "to_dataprog_rewrite_alt_side_def"]
  \\ rw []
  \\ PURE_FULL_CASE_TAC \\ fs []) |> update_precondition

val rewrite_alt_lem = Q.prove (
  `!loc next op acc ts x.
     bvi_tailrec$rewrite (loc,next,op,acc,ts) x =
     rewrite_alt loc next op acc ts x`,
  ho_match_mp_tac (fetch "-" "rewrite_alt_ind") \\ rw []
  \\ once_rewrite_tac [rewrite_alt_def]
  \\ CASE_TAC
  \\ fs [bvi_tailrecTheory.rewrite_def]
  \\ rpt (pairarg_tac \\ fs []));

val _ = translate rewrite_alt_lem

val _ = translate(bvi_tailrecTheory.compile_prog_def);

val _ = translate(bvl_to_bviTheory.compile_aux_def);

(* TODO: better way to translate Boolean pmatch patterns *)
(* this code turns the
      case ... | CopyByte T => ... | _ => last_case
   in compile_op into
      case ... | CopyByte b => if b then ... else last_case | _ => last_case
*)
val def = bvl_to_bviTheory.compile_op_pmatch;
val rows = def |> SPEC_ALL |> concl |> rhs |> rand
           |> listSyntax.dest_list |> #1
val bad_row = rows |> List.rev |> el 3
val default_row = rows |> last
val (_,_,default_exp) = patternMatchesSyntax.dest_PMATCH_ROW default_row
val (pat,guard,exp) = patternMatchesSyntax.dest_PMATCH_ROW bad_row
val pat_var = mk_var("b",bool);
val new_pat = mk_abs(pat_var,mk_comb(pat |> dest_abs |> #2 |> rator,pat_var))
val new_guard = mk_abs(pat_var,guard |> dest_abs |> #2)
val new_exp = mk_abs(pat_var,
  mk_cond(pat_var, exp |> dest_abs |> #2, default_exp |> dest_abs |> #2))
val new_row = patternMatchesSyntax.mk_PMATCH_ROW (new_pat,new_guard,new_exp)
val goal = def |> SPEC_ALL |> concl |> Term.subst[bad_row |-> new_row]
val some_v_T = prove(``(some (v:unit). T) = SOME ()``, rw[some_def]);
val new_def = prove(goal,
  rewrite_tac[bvl_to_bviTheory.compile_op_def]
  \\ PURE_TOP_CASE_TAC
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[]))
  \\ rewrite_tac[patternMatchesTheory.PMATCH_def,
                 patternMatchesTheory.PMATCH_ROW_def,
                 patternMatchesTheory.PMATCH_ROW_COND_def]
  \\ simp[]
  \\ PURE_TOP_CASE_TAC
  \\ simp[some_v_T]);
val r = translate new_def;

val _ = translate(bvl_to_bviTheory.compile_exps_def);

val bvl_to_bvi_compile_exps_side = Q.prove(`
  ∀x y. bvl_to_bvi_compile_exps_side x y ⇔ T`,
  ho_match_mp_tac bvl_to_bviTheory.compile_exps_ind>>
  `∀a b c d. bvl_to_bvi$compile_exps a [b] ≠ ([],c,d)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac bvl_to_bviTheory.compile_exps_LENGTH>>
    fs[])>>
  rw[]>>simp[Once (fetch "-" "bvl_to_bvi_compile_exps_side_def")]>>
  metis_tac[]) |> update_precondition

val _ = translate(bvl_to_bviTheory.compile_single_def);

val bvl_to_bvi_compile_single_side = Q.prove(`
  ∀x y. bvl_to_bvi_compile_single_side x y ⇔ T`,
  EVAL_TAC \\ rw[]
  \\ imp_res_tac bvl_to_bviTheory.compile_exps_LENGTH
  \\ CCONTR_TAC \\ fs[]) |> update_precondition

val _ = translate(bvl_to_bviTheory.compile_list_def);

val _ = translate(bvl_to_bviTheory.compile_prog_def);

val _ = translate(bvl_inlineTheory.let_op_def);

val let_op_SING_NOT_NIL = store_thm("let_op_SING_NOT_NIL[simp]",
  ``let_op [x] <> []``,
  Cases_on `x` \\ fs [bvl_inlineTheory.let_op_def]
  \\ CASE_TAC \\ fs []);

val bvl_inline_let_op_side = Q.prove(`
  ∀a. bvl_inline_let_op_side a ⇔ T`,
  ho_match_mp_tac bvl_inlineTheory.let_op_ind \\ rw []
  \\ once_rewrite_tac [fetch "-" "bvl_inline_let_op_side_def"] \\ fs [])
  |> update_precondition;

val _ = translate(bvl_handleTheory.compile_exp_def);

val bvl_handle_compile_exp_side = Q.prove(`
  ∀x y z. bvl_handle_compile_exp_side x y z ⇔ T`,
  EVAL_TAC \\ rpt strip_tac
  \\ pop_assum(mp_tac o Q.AP_TERM`LENGTH`)
  \\ rw[]) |> update_precondition;

val _ = translate(bvl_inlineTheory.inline_all_def);

val bvl_inline_inline_all_side = Q.prove(`
  ∀a b c d e f. bvl_inline_inline_all_side a b c d e f ⇔ T`,
  ho_match_mp_tac bvl_inlineTheory.inline_all_ind>>
  rw[]>>simp[Once (fetch "-" "bvl_inline_inline_all_side_def")]>>
  CCONTR_TAC>>fs[]>>
  pop_assum (mp_tac o Q.AP_TERM`LENGTH`)>>
  simp[bvl_inlineTheory.LENGTH_inline]) |> update_precondition

val _ = translate(bvl_inlineTheory.compile_prog_def);

val _ = translate(bvl_to_bviTheory.compile_def)

val _ = translate (bvi_to_dataTheory.op_requires_names_pmatch)
val _ = translate (COUNT_LIST_compute)

(* TODO: For some reason, the following def on sptrees fails to translate in a standalone manner (when the rest of this file's translation isn't loaded). Needs investigation. *)
val _ = translate (list_to_num_set_def)

val _ = translate (bvi_to_dataTheory.compile_def)

val bvi_to_data_compile_side = Q.prove(`
  ∀a b c d e. bvi_to_data_compile_side a b c d e ⇔ T`,
  ho_match_mp_tac bvi_to_dataTheory.compile_ind>>
  `∀a b c d e f g. bvi_to_data$compile a b c d [e] ≠ (f,[],g)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac bvi_to_dataTheory.compile_SING_IMP>>
    fs[])>>
  rw[]>>
  simp[Once (fetch "-" "bvi_to_data_compile_side_def")]>>
  fs[FALSE_def]>>
  metis_tac[])|>update_precondition

local
  val ths = ml_translatorLib.eq_lemmas();
in
  fun find_equality_type_thm tm =
    first (can (C match_term tm) o rand o snd o strip_imp o concl) ths
end

val EqualityType_UNIT_TYPE = find_equality_type_thm ``UNIT_TYPE``
val EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE =
  find_equality_type_thm ``SPTREE_SPT_TYPE UNIT_TYPE``
  |> Q.GEN`a` |> Q.ISPEC`UNIT_TYPE` |> SIMP_RULE std_ss [EqualityType_UNIT_TYPE];

val EqualityType_LIST_TYPE_NUM = find_equality_type_thm ``LIST_TYPE NUM``
  |> Q.GEN`a` |> Q.ISPEC`NUM` |> SIMP_RULE std_ss [EqualityType_NUM];

val EqualityType_OPTION_TYPE_NUM = find_equality_type_thm ``OPTION_TYPE NUM``
  |> Q.GEN`a` |> Q.ISPEC`NUM` |> SIMP_RULE std_ss [EqualityType_NUM];

val EqualityType_OPTION_TYPE_SPTREE_SPT_TYPE_UNIT_TYPE = find_equality_type_thm``OPTION_TYPE _``
  |> Q.GEN`a` |> Q.ISPEC`SPTREE_SPT_TYPE UNIT_TYPE`
  |> SIMP_RULE std_ss [EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE];

val EqualityType_PAIR_TYPE_NUM_SPTREE_SPT_TYPE_UNIT_TYPE = find_equality_type_thm``PAIR_TYPE _ _``
  |> Q.GENL[`b`,`c`]
  |> Q.ISPECL[`NUM`,`SPTREE_SPT_TYPE UNIT_TYPE`]
  |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE];

val EqualityType_OPTION_TYPE_PAIR_TYPE_NUM_SPTREE_SPT_TYPE_UNIT_TYPE = find_equality_type_thm``OPTION_TYPE _``
  |> Q.GEN`a` |> Q.ISPEC`PAIR_TYPE NUM (SPTREE_SPT_TYPE UNIT_TYPE)`
  |> SIMP_RULE std_ss [EqualityType_PAIR_TYPE_NUM_SPTREE_SPT_TYPE_UNIT_TYPE];

val DATALANG_PROG_TYPE_def = theorem"DATALANG_PROG_TYPE_def";
val DATALANG_PROG_TYPE_ind = theorem"DATALANG_PROG_TYPE_ind";

val DATALANG_PROG_TYPE_no_closures = Q.prove(
  `∀a b. DATALANG_PROG_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac DATALANG_PROG_TYPE_ind \\
  rw[DATALANG_PROG_TYPE_def] \\ rw[no_closures_def] \\
  TRY (
    qmatch_assum_rename_tac`OPTION_TYPE (_ _ DATALANG_PROG_TYPE) x y` \\
    Cases_on`x` \\ fs[OPTION_TYPE_def] \\
    rw[no_closures_def] \\
    qmatch_assum_rename_tac`PAIR_TYPE _ DATALANG_PROG_TYPE x y` \\
    Cases_on`x` \\ fs[PAIR_TYPE_def] \\
    rw[no_closures_def] \\
    metis_tac[EqualityType_def,EqualityType_NUM] ) \\
  metis_tac[EqualityType_def,EqualityType_NUM,
            EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE,
            EqualityType_LIST_TYPE_NUM,
            EqualityType_OPTION_TYPE_NUM,
            EqualityType_OPTION_TYPE_SPTREE_SPT_TYPE_UNIT_TYPE,
            EqualityType_OPTION_TYPE_PAIR_TYPE_NUM_SPTREE_SPT_TYPE_UNIT_TYPE,
            EqualityType_CLOSLANG_OP_TYPE]);

val DATALANG_PROG_TYPE_types_match = Q.prove(
  `∀a b c d. DATALANG_PROG_TYPE a b ∧ DATALANG_PROG_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac DATALANG_PROG_TYPE_ind \\
  rw[DATALANG_PROG_TYPE_def] \\
  Cases_on`c` \\ fs[DATALANG_PROG_TYPE_def] \\
  rw[types_match_def,ctor_same_type_def] \\
  TRY (
    qmatch_assum_rename_tac`OPTION_TYPE (_ _ DATALANG_PROG_TYPE) x1 y1` \\
    qpat_x_assum`OPTION_TYPE (_ _ DATALANG_PROG_TYPE) x1 y1` mp_tac \\
    qmatch_assum_rename_tac`OPTION_TYPE (_ _ DATALANG_PROG_TYPE) x2 y2` \\
    qpat_x_assum`OPTION_TYPE (_ _ DATALANG_PROG_TYPE) x2 y2` mp_tac \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[OPTION_TYPE_def] \\
    rw[types_match_def,ctor_same_type_def] \\
    rw[types_match_def,ctor_same_type_def] \\
    qmatch_assum_rename_tac`PAIR_TYPE _ DATALANG_PROG_TYPE x1 y1` \\
    qpat_x_assum`PAIR_TYPE _ DATALANG_PROG_TYPE x1 y1` mp_tac \\
    qmatch_assum_rename_tac`PAIR_TYPE _ DATALANG_PROG_TYPE x2 y2` \\
    qpat_x_assum`PAIR_TYPE _ DATALANG_PROG_TYPE x2 y2` mp_tac \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[PAIR_TYPE_def] \\
    rw[types_match_def,ctor_same_type_def] \\
    rw[types_match_def,ctor_same_type_def] \\
    metis_tac[EqualityType_def,EqualityType_NUM] ) \\
  metis_tac[EqualityType_def,EqualityType_NUM,
            EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE,
            EqualityType_LIST_TYPE_NUM,
            EqualityType_OPTION_TYPE_NUM,
            EqualityType_OPTION_TYPE_SPTREE_SPT_TYPE_UNIT_TYPE,
            EqualityType_OPTION_TYPE_PAIR_TYPE_NUM_SPTREE_SPT_TYPE_UNIT_TYPE,
            EqualityType_CLOSLANG_OP_TYPE]);

val DATALANG_PROG_TYPE_11 = Q.prove(
  `∀a b c d. DATALANG_PROG_TYPE a b ∧ DATALANG_PROG_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac DATALANG_PROG_TYPE_ind \\ rw[EQ_IMP_THM] \\
  fs[DATALANG_PROG_TYPE_def] \\ rw[] \\
  TRY(Cases_on`c`) \\ fs[DATALANG_PROG_TYPE_def] \\ rw[] \\
  TRY (
    qmatch_assum_rename_tac`OPTION_TYPE (_ _ DATALANG_PROG_TYPE) x y1` \\
    qpat_x_assum`OPTION_TYPE (_ _ DATALANG_PROG_TYPE) x y1` mp_tac \\
    qmatch_assum_rename_tac`OPTION_TYPE (_ _ DATALANG_PROG_TYPE) x y2` \\
    qpat_x_assum`OPTION_TYPE (_ _ DATALANG_PROG_TYPE) x y2` mp_tac \\
    Cases_on`x` \\ fs[OPTION_TYPE_def] \\ rw[] \\
    qmatch_assum_rename_tac`PAIR_TYPE _ DATALANG_PROG_TYPE x y1` \\
    qpat_x_assum`PAIR_TYPE _ DATALANG_PROG_TYPE x y1` mp_tac \\
    qmatch_assum_rename_tac`PAIR_TYPE _ DATALANG_PROG_TYPE x y2` \\
    qpat_x_assum`PAIR_TYPE _ DATALANG_PROG_TYPE x y2` mp_tac \\
    Cases_on`x` \\ fs[PAIR_TYPE_def] \\
    rw[] \\
    metis_tac[EqualityType_def,EqualityType_NUM] ) \\
  TRY (
    qmatch_assum_rename_tac`OPTION_TYPE (_ _ DATALANG_PROG_TYPE) x1 y` \\
    qpat_x_assum`OPTION_TYPE (_ _ DATALANG_PROG_TYPE) x1 y` mp_tac \\
    qmatch_assum_rename_tac`OPTION_TYPE (_ _ DATALANG_PROG_TYPE) x2 y` \\
    qpat_x_assum`OPTION_TYPE (_ _ DATALANG_PROG_TYPE) x2 y` mp_tac \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[OPTION_TYPE_def] \\
    rw[] \\
    qmatch_assum_rename_tac`PAIR_TYPE _ DATALANG_PROG_TYPE x1 y` \\
    qpat_x_assum`PAIR_TYPE _ DATALANG_PROG_TYPE x1 y` mp_tac \\
    qmatch_assum_rename_tac`PAIR_TYPE _ DATALANG_PROG_TYPE x2 y` \\
    qpat_x_assum`PAIR_TYPE _ DATALANG_PROG_TYPE x2 y` mp_tac \\
    Cases_on`x1` \\ Cases_on`x2` \\ fs[PAIR_TYPE_def] \\
    rw[] \\
    metis_tac[EqualityType_def,EqualityType_NUM] ) \\
  metis_tac[EqualityType_def,EqualityType_NUM,
            EqualityType_SPTREE_SPT_TYPE_UNIT_TYPE,
            EqualityType_LIST_TYPE_NUM,
            EqualityType_OPTION_TYPE_NUM,
            EqualityType_OPTION_TYPE_SPTREE_SPT_TYPE_UNIT_TYPE,
            EqualityType_OPTION_TYPE_PAIR_TYPE_NUM_SPTREE_SPT_TYPE_UNIT_TYPE,
            EqualityType_CLOSLANG_OP_TYPE]);

val EqualityType_DATALANG_PROG_TYPE = Q.prove(
  `EqualityType DATALANG_PROG_TYPE`,
  metis_tac[EqualityType_def,DATALANG_PROG_TYPE_no_closures,DATALANG_PROG_TYPE_types_match,DATALANG_PROG_TYPE_11])
  |> store_eq_thm;

(*TODO: pmatch for bvl_space is broken *)
val _ = translate data_spaceTheory.space_def

val _ = translate (bvi_to_dataTheory.compile_prog_def)

(*val data_space_space_side = Q.prove(`∀prog. data_space_space_side prog ⇔ T`,
`(∀prog. data_space_space_side prog ⇔ T) ∧
(∀opt (n:num) prog. opt = SOME(n,prog) ⇒ data_space_space_side prog ⇔ T) ∧
(∀opt (n:num) prog. opt = (n,prog) ⇒ data_space_space_side prog ⇔ T)`
  suffices_by simp[]
  >> ho_match_mp_tac (TypeBase.induction_of ``:dataLang$prog``)
  >> fs[]
  >> rpt strip_tac
  >> rw[Once (fetch "-" "data_space_space_side_def")]
  >> metis_tac[sum_CASES, pair_CASES]) |> update_precondition;

val bvi_to_data_compile_prog_side = Q.prove(`∀prog. bvi_to_data_compile_prog_side prog`,
  rw[fetch "-" "data_space_compile_side_def",
     fetch "-" "bvi_to_data_optimise_side_def",
     fetch "-" "bvi_to_data_compile_exp_side_def",
     fetch "-" "bvi_to_data_compile_part_side_def",
     fetch "-" "bvi_to_data_compile_prog_side_def",
     data_space_space_side]) |> update_precondition; *)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
