(*
  Translate the backend from closLang to target code.
*)
Theory from_closProg[no_sig_docs]
Ancestors
  ml_translator from_bvlProg backend[qualified]
Libs
  preamble ml_translatorLib

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = translation_extends "from_bvlProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "from_closProg");

(* ------------------------------------------------------------------------- *)
(* Setup                                                                     *)
(* ------------------------------------------------------------------------- *)

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

Theorem NOT_NIL_AND_LEMMA[local]:
  (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

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

(* ------------------------------------------------------------------------- *)
(* clos_mti                                                                  *)
(* ------------------------------------------------------------------------- *)

val r = translate clos_mtiTheory.intro_multi_def;

val clos_mti_intro_multi_side = Q.prove(`
  ∀max_app a. clos_mti_intro_multi_side max_app a ⇔ T`,
  ho_match_mp_tac clos_mtiTheory.intro_multi_ind>>
  `∀max_app z. intro_multi max_app [z] ≠ []` by
    (rw[] >> CCONTR_TAC>>fs[]>>
     Q.SPECL_THEN [`z`,`max_app`] mp_tac clos_mtiTheory.intro_multi_sing >>
     fs[])>>
  rw[]>>
  simp[Once (fetch "-" "clos_mti_intro_multi_side_def")]>>
  metis_tac[])|>update_precondition

val r = translate clos_mtiTheory.compile_inc_def;
val r = translate clos_mtiTheory.cond_mti_compile_inc_def;

(* ------------------------------------------------------------------------- *)
(* clos_number                                                               *)
(* ------------------------------------------------------------------------- *)

(* TODO:
 *   - make this not have to be explicitly translated, probably by renaming it
 *     to renumber_code_locs_list_def
 *)
val r = translate clos_numberTheory.renumber_code_locs_def;

val r = translate clos_numberTheory.ignore_table_def;
val r = translate clos_numberTheory.compile_inc_def;

(* ------------------------------------------------------------------------- *)
(* clos_op                                                                   *)
(* ------------------------------------------------------------------------- *)

val r = translate clos_opTheory.is_Var_pmatch;
val r = translate clos_opTheory.dest_Const_pmatch;
val r = translate clos_opTheory.dest_Constant_pmatch;
val r = translate clos_opTheory.dest_Cons_pmatch;
val r = translate clos_opTheory.dest_ElemAt_pmatch;
val r = translate clos_opTheory.dest_TagEq_pmatch;
val r = translate clos_opTheory.dest_LenEq_pmatch;
val r = translate clos_opTheory.dest_TagLenEq_pmatch;
val r = translate clos_opTheory.dest_Op_pmatch;
val r = translate clos_opTheory.eq_direct_def;
val r = translate clos_opTheory.eq_pure_list_def;
val r = translate clos_opTheory.SmartOp_def;

(* ------------------------------------------------------------------------- *)
(* clos_known                                                                *)
(* ------------------------------------------------------------------------- *)

val r = translate clos_knownTheory.merge_alt;

Theorem num_abs_intro[local]:
  ∀x. Num x = if 0 ≤ x then Num (ABS x) else Num x
Proof
  rw[]>>intLib.COOPER_TAC
QED

val r = translate (clos_knownTheory.known_op_def
                   |> ONCE_REWRITE_RULE [num_abs_intro]
                   |> SIMP_RULE std_ss []);

val clos_known_known_op_side = Q.prove(`
  ∀a b c. clos_known_known_op_side a b c ⇔ T`,
  rpt strip_tac >> Cases_on `b` >>
  simp[Once (fetch"-" "clos_known_known_op_side_def")]>>
  fs[]>>rw[]>>
  intLib.COOPER_TAC) |> update_precondition;

val r = translate clos_knownTheory.free_def;

Theorem clos_known_free_side = Q.prove(
  `!x. clos_known_free_side x`,
  ho_match_mp_tac clos_knownTheory.free_ind \\ rw []
  \\ `!xs ys l. clos_known$free xs = (ys, l) ==> LENGTH xs = LENGTH ys` by
   (ho_match_mp_tac clos_knownTheory.free_ind
    \\ rw [] \\ fs [clos_knownTheory.free_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rw [])
  \\ `!x l. clos_known$free [x] <> ([], l)` by (CCONTR_TAC \\ fs [] \\ last_x_assum drule \\ fs [])
  \\ once_rewrite_tac [fetch "-" "clos_known_free_side_def"] \\ fs []
  \\ rw [] \\ fs [] \\ metis_tac []) |> update_precondition;

val r = translate (clos_knownTheory.get_size_sc_aux_def |> REWRITE_RULE [GSYM sub_check_def]);

Theorem clos_known_get_size_sc_aux_ind[local]:
  clos_known_get_size_sc_aux_ind
Proof
  once_rewrite_tac [fetch "-" "clos_known_get_size_sc_aux_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD,sub_check_def]
QED

val _ = clos_known_get_size_sc_aux_ind |> update_precondition;

val r = translate (clos_knownTheory.get_size_sc_def |> REWRITE_RULE [GSYM sub_check_def]);

val r = translate clos_knownTheory.known_def;

val clos_known_known_side = Q.prove(`
  ∀a b c d. clos_known_known_side a b c d ⇔ T`,
  ho_match_mp_tac clos_knownTheory.known_ind
  \\ `∀z a b c d e. known a [z] b c ≠ ([],d)` by
   (CCONTR_TAC \\ fs[]
    \\ imp_res_tac clos_knownTheory.known_sing_EQ_E
    \\ fs[])
  \\ rw [] \\ simp [Once (fetch "-" "clos_known_known_side_def")]
  \\ metis_tac [FST,PAIR]) |> update_precondition;

val r = translate clos_ticksTheory.remove_ticks_def;

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

val r = translate clos_letopTheory.let_op_def;

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

val r = translate clos_fvsTheory.remove_fvs_def;

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

val r = translate clos_knownTheory.compile_def;

val r = translate clos_knownTheory.reset_inline_factor_def;
val r = translate clos_knownTheory.compile_inc_def;
val r = translate clos_knownTheory.known_compile_inc_def;
val r = translate clos_knownTheory.option_val_approx_spt_def;
val r = translate clos_knownTheory.option_upd_val_spt_def;
val r = translate clos_knownTheory.known_static_conf_def;

(* ------------------------------------------------------------------------- *)
(* clos_call                                                                 *)
(* ------------------------------------------------------------------------- *)

val r = translate clos_callTheory.calls_def;

val clos_call_free_side = Q.prove(`
  ∀a. clos_call_free_side a ⇔ T`,
  ho_match_mp_tac clos_callTheory.free_ind>>rw[]>>
  simp[Once (fetch "-" "clos_call_free_side_def")]>>rw[]>>
  CCONTR_TAC>>fs[]>>
  imp_res_tac clos_callTheory.free_SING>>fs[]>>
  metis_tac[]) |> update_precondition;

val clos_call_calls_side = Q.prove(`
  ∀a b. clos_call_calls_side a b ⇔ T`,
  ho_match_mp_tac clos_callTheory.calls_ind>>
  (*Move from calls proof*)
  `∀a b c. calls [a] b ≠ ([],c)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac clos_callTheory.calls_sing>>fs[])>>
  rw[]>> simp[Once (fetch"-" "clos_call_calls_side_def"),
              Once (fetch "-" "clos_call_closed_side_def"),
              clos_call_free_side]>>
  TRY(metis_tac[])>>
  ntac 2 strip_tac>>
  simp[LAMBDA_PROD]>>
  rw[fetch "-" "clos_call_closed_side_def",clos_call_free_side] >>
  rw[GSYM LAMBDA_PROD]) |> update_precondition;

val r = translate clos_callTheory.compile_def;
val r = translate clos_callTheory.compile_inc_def;
val r = translate clos_callTheory.cond_call_compile_inc_def;

(* ------------------------------------------------------------------------- *)
(* clos_annotate                                                             *)
(* ------------------------------------------------------------------------- *)

val r = translate clos_annotateTheory.shift_def;

val clos_annotate_shift_side = Q.prove(`
  ∀a b c d. clos_annotate_shift_side a b c d ⇔ T`,
  ho_match_mp_tac clos_annotateTheory.shift_ind>>
  `∀a b c d. shift [a] b c d ≠ []` by
    (CCONTR_TAC>>fs[]>>
    metis_tac[clos_annotateTheory.shift_SING,list_distinct])>>
  rw[]>>
  simp[Once (fetch "-" "clos_annotate_shift_side_def")]>>
  rw[]>> metis_tac[]) |> update_precondition;

val r = translate clos_annotateTheory.compile_def;

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

val r = translate clos_annotateTheory.compile_inc_def;

val clos_annotate_compile_inc_side = Q.prove(
  `∀x. clos_annotate_compile_inc_side x = T`,
  EVAL_TAC \\ rw[clos_annotate_alt_free_side]) |> update_precondition;

val r = translate clos_letopTheory.compile_inc_def;
val r = translate clos_fvsTheory.compile_inc_def;
val r = translate clos_ticksTheory.compile_inc_def;

(* ------------------------------------------------------------------------- *)
(* clos_to_bvl                                                               *)
(* ------------------------------------------------------------------------- *)

val r = translate clos_to_bvlTheory.add_part_def;
val r = translate clos_to_bvlTheory.add_parts_def;
val r = translate (clos_to_bvlTheory.compile_const_def |> DefnBase.one_line_ify NONE);
val r = translate clos_to_bvlTheory.compile_op_pmatch;

val r = translate (bvl_jumpTheory.JumpList_def |> REWRITE_RULE [GSYM mllistTheory.take_def,GSYM mllistTheory.drop_def]);

Theorem bvl_jump_jumplist_ind[local]:
  bvl_jump_jumplist_ind
Proof
  once_rewrite_tac [fetch "-" "bvl_jump_jumplist_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD,mllistTheory.take_def,mllistTheory.drop_def]
  \\ Cases_on`xs` \\ gvs[]
QED

val _ = bvl_jump_jumplist_ind |> update_precondition;

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
    (Cases_on`x1_n_`>>fs[ADD_DIV_RWT,ADD1,mllistTheory.take_def,mllistTheory.drop_def])
  >>
    `SUC x1_n_ DIV 2 < SUC x1_n_` by
      fs[]>>
    simp[mllistTheory.take_def]) |> update_precondition;

val r = translate (clos_to_bvlTheory.mk_cl_call_def |> REWRITE_RULE [GSYM sub_check_def])
val r = translate (clos_to_bvlTheory.generate_generic_app_def |> REWRITE_RULE [GSYM sub_check_def]);

val r = translate (clos_to_bvlTheory.generate_partial_app_closure_fn_def |> REWRITE_RULE [GSYM sub_check_def]);
val r = translate (clos_to_bvlTheory.recc_Let_def |> REWRITE_RULE [GSYM sub_check_def]);
val r = translate (clos_to_bvlTheory.recc_Let0_def |> REWRITE_RULE [GSYM sub_check_def]);
val r = translate (clos_to_bvlTheory.num_stubs_def |> REWRITE_RULE [GSYM sub_check_def]);

val r = translate (clos_to_bvlTheory.compile_exps_def |> REWRITE_RULE [GSYM sub_check_def]);

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
  rename1`compile_exps max_app [xx] yy = (_,zz)` >>
  first_x_assum(qspecl_then[`max_app`,`xx`,`yy`,`zz`] assume_tac)>>
  CCONTR_TAC>>fs[]) |> update_precondition;

val r = translate clos_to_bvlTheory.compile_common_def;

val r = translate (clos_to_bvlTheory.init_code_def |> REWRITE_RULE [GSYM sub_check_def]);
val r = translate (clos_to_bvlTheory.partial_app_fn_location_def |> REWRITE_RULE [GSYM sub_check_def]);

val r = translate (clos_to_bvlTheory.compile_prog_def |> REWRITE_RULE [GSYM sub_check_def]);

val r = translate clos_to_bvlTheory.compile_def;

val clos_to_bvl_compile_side = Q.prove(`
  clos_to_bvl_compile_side v10 v11 = T`,
  fs [fetch "-" "clos_to_bvl_compile_side_def"]
  \\ rw[clos_to_bvlTheory.num_stubs_def])
  |> update_precondition;

val r = translate clos_to_bvlTheory.extract_name_pmatch;
val r = translate clos_to_bvlTheory.compile_inc_def;

val res = translate clos_to_bvlTheory.clos_to_bvl_compile_inc_def

(* ------------------------------------------------------------------------- *)
(* backend                                                                   *)
(* ------------------------------------------------------------------------- *)

val _ = translate backendTheory.from_clos_def;

(* ------------------------------------------------------------------------- *)

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
val _ = ml_translatorLib.clean_on_exit := true;
