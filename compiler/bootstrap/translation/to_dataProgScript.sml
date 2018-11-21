open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open basisProgTheory;

val _ = new_theory "to_dataProg"
val _ = translation_extends "basisProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "to_dataProg");

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

val res = translate listTheory.REV_DEF;
val res = translate listTheory.TAKE_def;
val res = translate listTheory.DROP_def;

val res = translate source_to_flatTheory.compile_prog_def;

(* flat_reorder_match *)

val res = translate flat_reorder_matchTheory.compile_def;

val side_def = fetch "-" "flat_reorder_match_compile_side_def"

val flat_reorder_match_compile_side_simp = prove(
  ``!x. flat_reorder_match_compile_side x = T``,
  ho_match_mp_tac flat_reorder_matchTheory.compile_ind
  \\ rw []
  \\ once_rewrite_tac [side_def]
  \\ simp [FORALL_PROD]
  \\ rw [] \\ res_tac \\ fs [])
  |> update_precondition;

val res = translate flat_reorder_matchTheory.compile_decs_def;

val side_def = fetch "-" "flat_reorder_match_compile_decs_side_def"

val flat_reorder_match_compile_decs_side_simp = prove(
  ``!x. flat_reorder_match_compile_decs_side x = T``,
  Induct THEN1 fs [side_def]
  \\ Cases
  \\ once_rewrite_tac [side_def]
  \\ once_rewrite_tac [side_def] \\ fs [])
  |> update_precondition;

(* flat_uncheck_ctors *)

val res = translate flat_uncheck_ctorsTheory.compile_def;

val side_def = fetch "-" "flat_uncheck_ctors_compile_side_def"

val flat_uncheck_ctors_compile_side_simp = prove(
  ``!x. flat_uncheck_ctors_compile_side x = T``,
  ho_match_mp_tac flat_uncheck_ctorsTheory.compile_ind
  \\ rw []
  \\ once_rewrite_tac [side_def]
  \\ simp [FORALL_PROD]
  \\ rw [] \\ res_tac \\ fs [])
  |> update_precondition;

val res = translate flat_uncheck_ctorsTheory.compile_decs_def;

val side_def = fetch "-" "flat_uncheck_ctors_compile_decs_side_def"

val flat_uncheck_ctors_compile_decs_side_simp = prove(
  ``!x. flat_uncheck_ctors_compile_decs_side x = T``,
  Induct THEN1 fs [side_def]
  \\ Cases
  \\ once_rewrite_tac [side_def]
  \\ once_rewrite_tac [side_def] \\ fs [])
  |> update_precondition;

(* flat_exh_match *)

val res = translate flat_exh_matchTheory.compile_exps_def;

val side_def = fetch "-" "flat_exh_match_compile_exps_side_def"

val flat_exh_match_compile_exps_side_simp = prove(
  ``!y x. flat_exh_match_compile_exps_side y x = T``,
  ho_match_mp_tac flat_exh_matchTheory.compile_exps_ind
  \\ rw []
  \\ once_rewrite_tac [side_def]
  \\ simp [FORALL_PROD,TRUE_def,FALSE_def]
  \\ rw [] \\ res_tac \\ fs [])
  |> update_precondition;

val res = translate flat_exh_matchTheory.compile_decs_def;

(* flat_elim *)

val res = translate flat_elimTheory.removeFlatProg_def;

(* source_to_flat *)

val res = translate source_to_flatTheory.compile_flat_def;

val res = translate source_to_flatTheory.compile_def;

(* flat_to_pat *)

val res = translate flat_to_patTheory.compile_def;


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

val EqualityType_OPTION_TYPE_NUM = find_equality_type_thm``OPTION_TYPE NUM``
  |> Q.GEN`a` |> Q.ISPEC`NUM` |> SIMP_RULE std_ss [EqualityType_NUM]

val EqualityType_PAIR_TYPE_NUM_OPTION_TYPE_NUM =
  find_equality_type_thm``PAIR_TYPE NUM (OPTION_TYPE NUM)``
  |> Q.GEN`b` |> Q.ISPEC`NUM`
  |> Q.GEN`c` |> Q.ISPEC`OPTION_TYPE NUM`
  |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_OPTION_TYPE_NUM]

val EqualityType_OPTION_TYPE_PAIR_TYPE_NUM_OPTION_TYPE_NUM =
  find_equality_type_thm``OPTION_TYPE (PAIR_TYPE NUM (OPTION_TYPE NUM))``
  |> Q.GEN`a` |> Q.ISPEC`PAIR_TYPE NUM (OPTION_TYPE NUM)`
  |> SIMP_RULE std_ss [EqualityType_PAIR_TYPE_NUM_OPTION_TYPE_NUM]

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

val EqualityType_BACKEND_COMMON_TRA_TYPE = find_equality_type_thm``BACKEND_COMMON_TRA_TYPE``
  |> SIMP_RULE std_ss [EqualityType_NUM]

val EqualityType_FLATLANG_OP_TYPE = find_equality_type_thm``FLATLANG_OP_TYPE`` |> SIMP_RULE std_ss [EqualityType_NUM, EqualityType_AST_OPN_TYPE, EqualityType_AST_OPB_TYPE, EqualityType_AST_OPW_TYPE, EqualityType_LIST_TYPE_CHAR, EqualityType_FPSEM_FP_BOP_TYPE, EqualityType_FPSEM_FP_UOP_TYPE, EqualityType_FPSEM_FP_CMP_TYPE, EqualityType_AST_SHIFT_TYPE, EqualityType_AST_WORD_SIZE_TYPE]

val EqualityType_PATLANG_OP_TYPE = find_equality_type_thm``PATLANG_OP_TYPE`` |> SIMP_RULE std_ss [EqualityType_NUM,EqualityType_FLATLANG_OP_TYPE]

val ctor_same_type_def = semanticPrimitivesTheory.ctor_same_type_def

val FLATLANG_PAT_TYPE_def = theorem"FLATLANG_PAT_TYPE_def";
val FLATLANG_PAT_TYPE_ind = theorem"FLATLANG_PAT_TYPE_ind";

val FLATLANG_PAT_TYPE_no_closures = Q.prove(
  `∀a b. FLATLANG_PAT_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac FLATLANG_PAT_TYPE_ind
  \\ rw[FLATLANG_PAT_TYPE_def]
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
            EqualityType_OPTION_TYPE_PAIR_TYPE_NUM_OPTION_TYPE_NUM,
            EqualityType_AST_LIT_TYPE,
            EqualityType_LIST_TYPE_CHAR,
            EqualityType_def]);

val FLATLANG_PAT_TYPE_types_match = Q.prove(
  `∀a b c d. FLATLANG_PAT_TYPE a b ∧ FLATLANG_PAT_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac FLATLANG_PAT_TYPE_ind \\
  rw[FLATLANG_PAT_TYPE_def] \\
  Cases_on`c` \\ fs[FLATLANG_PAT_TYPE_def,types_match_def,ctor_same_type_def] \\ rw[] \\
  simp [semanticPrimitivesTheory.same_type_def] >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`x2`,`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def,semanticPrimitivesTheory.same_type_def] ) >>
    qx_gen_tac`p` >>
    gen_tac >> Cases >> simp[PULL_EXISTS,LIST_TYPE_def] >>
    rw[types_match_def,ctor_same_type_def,semanticPrimitivesTheory.same_type_def] >>
    PROVE_TAC[EqualityType_def] ) >>
  metis_tac[EqualityType_NUM,
            EqualityType_OPTION_TYPE_PAIR_TYPE_NUM_OPTION_TYPE_NUM,
            EqualityType_AST_LIT_TYPE,
            EqualityType_LIST_TYPE_CHAR,
            EqualityType_def]);

val FLATLANG_PAT_TYPE_11 = Q.prove(
  `∀a b c d. FLATLANG_PAT_TYPE a b ∧ FLATLANG_PAT_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac FLATLANG_PAT_TYPE_ind \\
  rw[FLATLANG_PAT_TYPE_def] \\
  Cases_on`c` \\ fs[FLATLANG_PAT_TYPE_def] \\ rw[EQ_IMP_THM] \\
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
            EqualityType_OPTION_TYPE_PAIR_TYPE_NUM_OPTION_TYPE_NUM,
            EqualityType_AST_LIT_TYPE,
            EqualityType_LIST_TYPE_CHAR,
            EqualityType_def]);

val EqualityType_FLATLANG_PAT_TYPE = Q.prove(
  `EqualityType FLATLANG_PAT_TYPE`,
  metis_tac[EqualityType_def,FLATLANG_PAT_TYPE_no_closures,
            FLATLANG_PAT_TYPE_types_match,FLATLANG_PAT_TYPE_11])
  |> store_eq_thm;

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
            EqualityType_OPTION_TYPE_PAIR_TYPE_NUM_OPTION_TYPE_NUM,
            EqualityType_BACKEND_COMMON_TRA_TYPE,
            EqualityType_AST_LIT_TYPE,
            EqualityType_PATLANG_OP_TYPE,
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
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def,semanticPrimitivesTheory.same_type_def] ) >>
    qx_gen_tac`p` >>
    gen_tac >> Cases >> simp[PULL_EXISTS,LIST_TYPE_def] >>
    rw[types_match_def,ctor_same_type_def,semanticPrimitivesTheory.same_type_def] >>
    PROVE_TAC[EqualityType_def] ) >>
  simp [semanticPrimitivesTheory.same_type_def] >>
  metis_tac[EqualityType_NUM,
            EqualityType_BACKEND_COMMON_TRA_TYPE,
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
            EqualityType_AST_LIT_TYPE,
            EqualityType_PATLANG_OP_TYPE,
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

val r = translate clos_knownTheory.free_def

val clos_known_free_side = Q.store_thm("clos_known_free_side",
  `!x. clos_known_free_side x`,
  ho_match_mp_tac clos_knownTheory.free_ind \\ rw []
  \\ `!xs ys l. free xs = (ys, l) ==> LENGTH xs = LENGTH ys` by
   (ho_match_mp_tac clos_knownTheory.free_ind
    \\ rw [] \\ fs [clos_knownTheory.free_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rw [])
  \\ `!x l. free [x] <> ([], l)` by (CCONTR_TAC \\ fs [] \\ last_x_assum drule \\ fs [])
  \\ once_rewrite_tac [fetch "-" "clos_known_free_side_def"] \\ fs []
  \\ rw [] \\ fs [] \\ metis_tac []) |> update_precondition;

val r = translate (clos_knownTheory.known_def)

val clos_known_known_side = Q.prove(`
  ∀a b c d. clos_known_known_side a b c d ⇔ T`,
  ho_match_mp_tac clos_knownTheory.known_ind
  \\ `∀z a b c d e. known a [z] b c ≠ ([],d)` by
   (CCONTR_TAC \\ fs[]
    \\ imp_res_tac clos_knownTheory.known_sing_EQ_E
    \\ fs[])
  \\ rw [] \\ simp [Once (fetch "-" "clos_known_known_side_def")]
  \\ metis_tac [FST,PAIR]) |> update_precondition;

val r = translate (clos_ticksTheory.remove_ticks_def);

val clos_ticks_remove_ticks_side = Q.prove(`
  ∀a. clos_ticks_remove_ticks_side a ⇔ T`,
  `∀z. clos_ticks$remove_ticks [z] ≠ []` by
   (CCONTR_TAC \\ fs[]
    \\ `LENGTH (clos_ticks$remove_ticks [z]) = 0` by metis_tac [LENGTH]
    \\ pop_assum mp_tac
    \\ rewrite_tac [clos_ticksTheory.LENGTH_remove_ticks] \\ fs [])
  \\ ho_match_mp_tac clos_ticksTheory.remove_ticks_ind \\ fs []
  \\ rw [] \\ simp [Once (fetch "-" "clos_ticks_remove_ticks_side_def")]
  \\ metis_tac [FST,PAIR]) |> update_precondition;

val r = translate (clos_letopTheory.let_op_def);

val clos_letop_let_op_side = Q.prove(`
  ∀a. clos_letop_let_op_side a ⇔ T`,
  `∀z. clos_letop$let_op [z] ≠ []` by
   (CCONTR_TAC \\ fs[]
    \\ `LENGTH (clos_letop$let_op [z]) = 0` by metis_tac [LENGTH]
    \\ pop_assum mp_tac
    \\ rewrite_tac [clos_letopTheory.LENGTH_let_op] \\ fs [])
  \\ ho_match_mp_tac clos_letopTheory.let_op_ind \\ fs []
  \\ rw [] \\ simp [Once (fetch "-" "clos_letop_let_op_side_def")]
  \\ metis_tac [FST,PAIR]) |> update_precondition;

val r = translate (clos_fvsTheory.remove_fvs_def);

val clos_fvs_remove_fvs_side = Q.prove(`
  ∀a b. clos_fvs_remove_fvs_side a b ⇔ T`,
  `∀a z. clos_fvs$remove_fvs a [z] ≠ []` by
   (CCONTR_TAC \\ fs[]
    \\ `LENGTH (clos_fvs$remove_fvs a [z]) = 0` by metis_tac [LENGTH]
    \\ pop_assum mp_tac
    \\ rewrite_tac [clos_fvsTheory.LENGTH_remove_fvs] \\ fs [])
  \\ ho_match_mp_tac clos_fvsTheory.remove_fvs_ind \\ fs []
  \\ rw [] \\ simp [Once (fetch "-" "clos_fvs_remove_fvs_side_def")]
  \\ metis_tac [FST,PAIR]) |> update_precondition;

val r = translate clos_knownTheory.compile_def

(* labels *)

val r = translate (clos_labelsTheory.remove_dests_def);

val clos_labels_remove_dests_side = Q.prove(`
  ∀a b. clos_labels_remove_dests_side a b ⇔ T`,
  `∀a z. clos_labels$remove_dests a [z] ≠ []` by
   (CCONTR_TAC \\ fs[]
    \\ `LENGTH (clos_labels$remove_dests a [z]) = 0` by metis_tac [LENGTH]
    \\ pop_assum mp_tac
    \\ rewrite_tac [clos_labelsTheory.LENGTH_remove_dests] \\ fs [])
  \\ ho_match_mp_tac clos_labelsTheory.remove_dests_ind \\ fs []
  \\ rw [] \\ simp [Once (fetch "-" "clos_labels_remove_dests_side_def")]
  \\ metis_tac [FST,PAIR]) |> update_precondition;

val r = translate clos_labelsTheory.compile_def;

val clos_labels_compile_side = Q.prove(`
  ∀a. clos_labels_compile_side a ⇔ T`,
  `∀a z. clos_labels$remove_dests a [z] ≠ []` by
   (CCONTR_TAC \\ fs[]
    \\ `LENGTH (clos_labels$remove_dests a [z]) = 0` by metis_tac [LENGTH]
    \\ pop_assum mp_tac
    \\ rewrite_tac [clos_labelsTheory.LENGTH_remove_dests] \\ fs [])
  \\ rw [] \\ simp [Once (fetch "-" "clos_labels_compile_side_def")])
 |> update_precondition;

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

val r = translate clos_to_bvlTheory.compile_common_def;
val r = translate clos_to_bvlTheory.compile_def;

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

val EqualityType_LIST_TYPE_NUM = find_equality_type_thm ``LIST_TYPE NUM``
  |> Q.GEN`a` |> Q.ISPEC`NUM` |> SIMP_RULE std_ss [EqualityType_NUM];

val EqualityType_OPTION_TYPE_LIST_TYPE_NUM =
  find_equality_type_thm``OPTION_TYPE (LIST_TYPE NUM)``
  |> Q.GEN `a` |> Q.ISPEC `LIST_TYPE NUM` |> SIMP_RULE std_ss [EqualityType_LIST_TYPE_NUM]

val CLOSLANG_EXP_TYPE_def = theorem"CLOSLANG_EXP_TYPE_def";
val CLOSLANG_EXP_TYPE_ind = theorem"CLOSLANG_EXP_TYPE_ind";

val OPTION_TYPE_def = std_preludeTheory.OPTION_TYPE_def;

val CLOSLANG_EXP_TYPE_no_closures = Q.prove(
  `!a b. CLOSLANG_EXP_TYPE a b ==> no_closures b`,
  ho_match_mp_tac CLOSLANG_EXP_TYPE_ind
  \\ rw [CLOSLANG_EXP_TYPE_def] \\ rw [no_closures_def]
  \\ TRY
   (match_mp_tac
     (EqualityType_BACKEND_COMMON_TRA_TYPE
      |> SIMP_RULE (srw_ss()) [EqualityType_def]
      |> CONJUNCT1)
    \\ asm_exists_tac \\ fs []
    \\ NO_TAC)
  \\ TRY
   (match_mp_tac
     (EqualityType_CLOSLANG_OP_TYPE
      |> SIMP_RULE (srw_ss()) [EqualityType_def]
      |> CONJUNCT1)
    \\ asm_exists_tac \\ fs []
    \\ NO_TAC)
  \\ TRY
   (match_mp_tac
     (EqualityType_OPTION_TYPE_NUM
      |> SIMP_RULE (srw_ss()) [EqualityType_def]
      |> CONJUNCT1)
    \\ asm_exists_tac \\ fs []
    \\ NO_TAC)
  \\ TRY
   (match_mp_tac
     (EqualityType_NUM
      |> SIMP_RULE (srw_ss()) [EqualityType_def]
      |> CONJUNCT1)
    \\ asm_exists_tac \\ fs []
    \\ NO_TAC)
  \\ TRY
   (qmatch_assum_rename_tac `OPTION_TYPE (LIST_TYPE _) x y`
    \\ qmatch_goalsub_rename_tac `no_closures y`
    \\ Cases_on `x` \\ fs [OPTION_TYPE_def]
    \\ rw [no_closures_def]
    \\ metis_tac [EqualityType_LIST_TYPE_NUM, EqualityType_def])
  \\ TRY
   (qmatch_assum_rename_tac `LIST_TYPE CLOSLANG_EXP_TYPE x1 y1`
    \\ qhdtm_x_assum `LIST_TYPE` mp_tac
    \\ last_x_assum mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ map_every qid_spec_tac [`y1`,`x1`]
    \\ Induct \\ simp [LIST_TYPE_def, PULL_EXISTS, no_closures_def]
    \\ qx_gen_tac `p`
    \\ simp [PULL_EXISTS, no_closures_def]
    \\ rw []
    \\ metis_tac [EqualityType_def])
  \\ qhdtm_x_assum `LIST_TYPE` mp_tac
  \\ last_x_assum mp_tac
  \\ last_x_assum mp_tac
  \\ rename1 `LIST_TYPE _ x y`
  \\ map_every qid_spec_tac [`a`,`y`,`x`]
  \\ rpt (pop_assum kall_tac)
  \\ Induct \\ rw [LIST_TYPE_def, PULL_EXISTS, no_closures_def]
  \\ fsrw_tac [DNF_ss] []
  \\ PairCases_on `h` \\ fs []
  \\ fs [PAIR_TYPE_def] \\ rw [] \\ fs [no_closures_def]
  \\ metis_tac [EqualityType_def, EqualityType_NUM]);

val CLOSLANG_EXP_TYPE_11 = Q.prove(
  `!a b c d. CLOSLANG_EXP_TYPE a b /\ CLOSLANG_EXP_TYPE c d ==> (a = c <=> b = d)`,
  ho_match_mp_tac CLOSLANG_EXP_TYPE_ind
  \\ rw [CLOSLANG_EXP_TYPE_def]
  \\ Cases_on `c` \\ fs [CLOSLANG_EXP_TYPE_def] \\ rw [EQ_IMP_THM]
  \\ TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`y1`,`x`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >>
    rw[] >>
    fsrw_tac [DNF_ss] [] >>
    TRY (
      PairCases_on `h` >> fs [] >>
      fs [PAIR_TYPE_def] >>
      rw [] >>
      metis_tac [EqualityType_def, EqualityType_NUM] ) >>
    metis_tac [] )
  \\ TRY (
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
    fsrw_tac [DNF_ss] [] >>
    TRY (
      PairCases_on `h` >> fs [] >>
      PairCases_on `h'` >> fs [] >>
      fs [PAIR_TYPE_def] >>
      rw [] >>
      metis_tac [EqualityType_def, EqualityType_NUM] ) >>
    metis_tac[])
  \\ metis_tac [EqualityType_def,
                EqualityType_NUM,
                EqualityType_OPTION_TYPE_NUM,
                EqualityType_OPTION_TYPE_LIST_TYPE_NUM,
                EqualityType_BACKEND_COMMON_TRA_TYPE,
                EqualityType_CLOSLANG_OP_TYPE]);

val CLOSLANG_EXP_TYPE_types_match = Q.prove(
  `!a b c d. CLOSLANG_EXP_TYPE a b /\ CLOSLANG_EXP_TYPE c d ==> types_match b d`,
  ho_match_mp_tac CLOSLANG_EXP_TYPE_ind
  \\ rw [CLOSLANG_EXP_TYPE_def]
  \\ Cases_on `c` \\ fs [CLOSLANG_EXP_TYPE_def, types_match_def, ctor_same_type_def] \\ rw[]
  \\ TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`x2`,`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def,semanticPrimitivesTheory.same_type_def] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def,semanticPrimitivesTheory.same_type_def] ) >>
    qx_gen_tac`p` >>
    gen_tac >> Cases >> simp[PULL_EXISTS,LIST_TYPE_def] >>
    rw[types_match_def,ctor_same_type_def,semanticPrimitivesTheory.same_type_def] >>
    TRY (
      PairCases_on `h` \\ PairCases_on `p` \\
      fsrw_tac [DNF_ss] [PAIR_TYPE_def] \\ rw [] \\
      fs [types_match_def, ctor_same_type_def] \\
      res_tac \\
      metis_tac [EqualityType_def, EqualityType_NUM] ) >>
    PROVE_TAC[EqualityType_def] ) >>
  simp [semanticPrimitivesTheory.same_type_def] >>
  metis_tac[EqualityType_NUM,
            EqualityType_CLOSLANG_OP_TYPE,
            EqualityType_OPTION_TYPE_NUM,
            EqualityType_OPTION_TYPE_LIST_TYPE_NUM,
            EqualityType_BACKEND_COMMON_TRA_TYPE,
            EqualityType_def]);

val EqualityType_CLOSLANG_EXP_TYPE = Q.prove(
  `EqualityType CLOSLANG_EXP_TYPE`,
  metis_tac [EqualityType_def,
             CLOSLANG_EXP_TYPE_no_closures,
             CLOSLANG_EXP_TYPE_types_match,
             CLOSLANG_EXP_TYPE_11]) |> store_eq_thm;

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

val _ = save_thm("same_type_def[simp]",
  semanticPrimitivesTheory.same_type_def);

val BVL_EXP_TYPE_types_match = Q.prove(
  `∀a b c d. BVL_EXP_TYPE a b ∧ BVL_EXP_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac BVL_EXP_TYPE_ind \\
  rw[BVL_EXP_TYPE_def] \\
  Cases_on`c` \\ fs[BVL_EXP_TYPE_def,types_match_def,ctor_same_type_def,semanticPrimitivesTheory.same_type_def] \\ rw[] \\
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
  clos_to_bvl_compile_prog_side v10 v11 = T`,
  fs [fetch "-" "clos_to_bvl_compile_prog_side_def"]
  \\ fs [clos_to_bvl_compile_exps_side])
 |> update_precondition;

val clos_to_bvl_compile_side = Q.prove(`
  clos_to_bvl_compile_side v10 v11 = T`,
  fs [fetch "-" "clos_to_bvl_compile_side_def"]
  \\ fs [clos_to_bvl_compile_exps_side,
         clos_to_bvl_compile_prog_side,
         fetch "-" "clos_to_bvl_init_code_side_def",
         fetch "-" "clos_to_bvl_generate_generic_app_side_def",
         fetch "-" "bvl_jump_jump_side_def",
         bvl_jump_jumplist_side])
  |> update_precondition;

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

val r = translate (bvl_inlineTheory.tick_inline_def)

val bvl_inline_tick_inline_side = Q.prove (
  `!a0 a1. bvl_inline_tick_inline_side a0 a1 <=> T`,
  ho_match_mp_tac bvl_inlineTheory.tick_inline_ind
  \\ `!a x. LENGTH (tick_inline a x) = LENGTH x` by
   (ho_match_mp_tac bvl_inlineTheory.tick_inline_ind \\ rw []
    \\ fs [bvl_inlineTheory.tick_inline_def]
    \\ every_case_tac \\ fs [])
  \\ `!a x. tick_inline a [x] <> []` by
   (CCONTR_TAC \\ fs [] \\ last_x_assum (qspecl_then [`a`,`[x]`] assume_tac) \\ rfs [])
  \\ rw [] \\ once_rewrite_tac [fetch "-" "bvl_inline_tick_inline_side_def"] \\ fs [])
  |> update_precondition;

val r = translate bvl_inlineTheory.tick_inline_all_def

val bvl_inline_tick_inline_all_side = Q.prove (
  `!a0 a1 a2 a3. bvl_inline_tick_inline_all_side a0 a1 a2 a3 <=> T`,
  ho_match_mp_tac bvl_inlineTheory.tick_inline_all_ind
  \\ `!(x:(num # bvl$exp) num_map) y. tick_inline x [y] <> []` by
   (CCONTR_TAC \\ fs []
    \\ Q.ISPECL_THEN [`x`,`[y]`] assume_tac bvl_inlineTheory.LENGTH_tick_inline
    \\ rfs [])
  \\ rw []
  \\ once_rewrite_tac [fetch "-" "bvl_inline_tick_inline_all_side_def"] \\ fs [])
  |> update_precondition;

(* ------------------------------------------------------------------------- *)
(* bvl_const (PMATCH translations)                                           *)
(* ------------------------------------------------------------------------- *)

val _ = translate bvl_constTheory.dest_simple_pmatch
val _ = translate bvl_constTheory.case_op_const_pmatch
val _ = translate bvl_constTheory.SmartOp_flip_pmatch
(* val r = translate bvl_constTheory.SmartOp2_pmatch *) (* prove_EvalPatBind failed *)
val _ = translate bvl_constTheory.SmartOp2_def
val _ = translate bvl_constTheory.SmartOp_pmatch
val _ = translate bvl_constTheory.extract_pmatch
val _ = translate bvl_constTheory.extract_list_def
val _ = translate bvl_constTheory.delete_var_pmatch

val _ = translate bvl_constTheory.compile_def

val bvl_const_compile_side = Q.prove(`
  ∀x y. bvl_const_compile_side x y ⇔ T`,
  ho_match_mp_tac bvl_constTheory.compile_ind>>
  `∀a b. bvl_const$compile a [b] ≠ []` by
    (CCONTR_TAC>>fs[]>>
    pop_assum (mp_tac o Q.AP_TERM`LENGTH`)>>
    simp[bvl_constTheory.compile_length])>>
  rw[]>>
  simp[Once (fetch "-" "bvl_const_compile_side_def")])|>update_precondition

val _ = translate bvl_constTheory.compile_exp_def

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* bvi_tailrec: Some PMATCH versions are translated 'manually'               *)
(* ------------------------------------------------------------------------- *)

val r = translate bvi_tailrecTheory.is_rec_def (*PMATCH*)
val r = translate bvi_tailrecTheory.is_const_PMATCH
val r = translate bvi_tailrecTheory.from_op_PMATCH
val r = translate bvi_tailrecTheory.op_eq_PMATCH
val r = translate bvi_tailrecTheory.index_of_PMATCH
val r = translate bvi_tailrecTheory.args_from_def (* PMATCH *)
val r = translate bvi_tailrecTheory.get_bin_args_PMATCH
val r = translate bvi_tailrecTheory.is_arith_PMATCH
val r = translate bvi_tailrecTheory.is_rel_PMATCH
(*val r = translate bvi_tailrecTheory.term_ok_any_PMATCH (* auto_prove failed for ind *)*)
val r = translate bvi_tailrecTheory.decide_ty_PMATCH
val r = translate bvi_tailrecTheory.arg_ty_PMATCH
val r = translate bvi_tailrecTheory.op_ty_PMATCH

val r = translate bvi_tailrecTheory.scan_expr_def

val bvi_tailrec_scan_expr_side = Q.store_thm("bvi_tailrec_scan_expr_side",
  `!a0 a1 a2. bvi_tailrec_scan_expr_side a0 a1 a2`,
  recInduct bvi_tailrecTheory.scan_expr_ind \\ rw []
  \\ once_rewrite_tac [fetch "-" "bvi_tailrec_scan_expr_side_def"] \\ fs []
  \\ FULL_CASE_TAC \\ fs []) |> update_precondition;

val r = translate bvi_tailrecTheory.rewrite_PMATCH

val bvi_tailrec_rewrite_side = Q.store_thm("bvi_tailrec_rewrite_side",
  `!v58 v59 v60 v56 v61 v57. bvi_tailrec_rewrite_side v58 v59 v60 v56 v61 v57`,
  recInduct bvi_tailrecTheory.rewrite_ind \\ rw []
  \\ once_rewrite_tac [fetch "-" "bvi_tailrec_rewrite_side_def"] \\ fs []
  \\ FULL_CASE_TAC \\ fs []) |> update_precondition;

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

val r = translate(bvl_inlineTheory.remove_ticks_def)

val bvl_inline_remove_ticks_side = Q.store_thm("bvl_inline_remove_ticks_side",
  `!a. bvl_inline_remove_ticks_side a`,
  ho_match_mp_tac bvl_inlineTheory.remove_ticks_ind
  \\ sg `!x. remove_ticks [x] <> []`
  >-
   (CCONTR_TAC \\ fs []
    \\ pop_assum (mp_tac o Q.AP_TERM `LENGTH`)
    \\ fs [bvl_inlineTheory.LENGTH_remove_ticks])
  \\ rw [] \\ rw [Once (fetch "-" "bvl_inline_remove_ticks_side_def")])
  |> update_precondition;

val _ = translate(bvl_inlineTheory.compile_prog_def);

val bvl_inline_compile_prog_side = Q.store_thm("bvl_inline_compile_prog_side",
  `!a b c d. bvl_inline_compile_prog_side a b c d`,
  rw [Once (fetch "-" "bvl_inline_compile_prog_side_def"),
      Once (fetch "-" "bvl_inline_compile_inc_side_def"),
      Once (fetch "-" "bvl_inline_optimise_side_def")]
  \\ strip_tac
  \\ pop_assum (mp_tac o Q.AP_TERM `LENGTH`)
  \\ fs [bvl_inlineTheory.LENGTH_remove_ticks])
  |> update_precondition;

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

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
