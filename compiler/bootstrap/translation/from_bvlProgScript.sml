(*
  Translate the backend from BVL to target code.
*)
Theory from_bvlProg[no_sig_docs]
Ancestors
  ml_translator from_bviProg
Libs
  preamble ml_translatorLib

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = translation_extends "from_bviProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "from_bvlProg");

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

(* N.B.
 * Do not remove this! prove_EvalPatRel depends on it (though it should be
 * expanded there, not added to the simpset).
 *)
Theorem same_type_def[simp] =
  semanticPrimitivesTheory.same_type_def

(* ------------------------------------------------------------------------- *)
(* bvl_const                                                                 *)
(* ------------------------------------------------------------------------- *)

val r = translate bvl_constTheory.dest_simple_pmatch;
val r = translate bvl_constTheory.dest_EqualInt_pmatch;
val r = translate bvl_constTheory.case_op_const_pmatch;
val r = translate bvl_constTheory.SmartOp_flip_pmatch;
(* val r = translate bvl_constTheory.SmartOp2_pmatch *) (* prove_EvalPatBind *)
val r = translate bvl_constTheory.SmartOp2_def;

Theorem bvl_const_smartop2_size:
  bvl_const_smartop2_side v = T
Proof
  PairCases_on ‘v’
  \\ fs [fetch "-" "bvl_const_smartop2_side_def"]
  \\ rpt strip_tac \\ gvs []
  \\ rw [] \\ intLib.COOPER_TAC
QED

val _ = update_precondition bvl_const_smartop2_size;

val r = translate bvl_constTheory.SmartOp_pmatch;
val r = translate bvl_constTheory.extract_pmatch;
val r = translate bvl_constTheory.extract_list_def;
val r = translate bvl_constTheory.delete_var_pmatch;
val r = translate bvl_constTheory.compile_def;

val bvl_const_compile_side = Q.prove(`
  ∀x y. bvl_const_compile_side x y ⇔ T`,
  ho_match_mp_tac bvl_constTheory.compile_ind>>
  `∀a b. bvl_const$compile a [b] ≠ []` by
    (CCONTR_TAC>>fs[]>>
    pop_assum (mp_tac o Q.AP_TERM`LENGTH`)>>
    simp[bvl_constTheory.compile_length])>>
  rw[]>>
  simp[Once (fetch "-" "bvl_const_compile_side_def")])
  |> update_precondition;

val r = translate bvl_constTheory.compile_exp_def;

(* ------------------------------------------------------------------------- *)
(* bvl_handle                                                                *)
(* ------------------------------------------------------------------------- *)

val r = translate (bvl_handleTheory.LetLet_def
                   |> SIMP_RULE std_ss [MAPi_enumerate_MAP]);

val r = translate bvl_handleTheory.compile_def;

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
  metis_tac[]) |> update_precondition;

val r = translate bvl_handleTheory.compile_exp_def;

val bvl_handle_compile_exp_side = Q.prove(`
  ∀x y z. bvl_handle_compile_exp_side x y z ⇔ T`,
  EVAL_TAC \\ rpt strip_tac
  \\ pop_assum(mp_tac o Q.AP_TERM`LENGTH`)
  \\ rw[]) |> update_precondition;

(* ------------------------------------------------------------------------- *)
(* bvl_inline                                                                *)
(* ------------------------------------------------------------------------- *)

val r = translate bvl_inlineTheory.tick_inline_def;

val bvl_inline_tick_inline_side = Q.prove (
  `!a0 a1. bvl_inline_tick_inline_side a0 a1 <=> T`,
  ho_match_mp_tac bvl_inlineTheory.tick_inline_ind
  \\ `!a x. LENGTH (tick_inline a x) = LENGTH x` by
   (ho_match_mp_tac bvl_inlineTheory.tick_inline_ind \\ rw []
    \\ fs [bvl_inlineTheory.tick_inline_def]
    \\ every_case_tac \\ fs [])
  \\ `!a x. tick_inline a [x] <> []` by
   (CCONTR_TAC \\ fs []
    \\ last_x_assum (qspecl_then [`a`,`[x]`] assume_tac)
    \\ rfs [])
  \\ rw [] \\ once_rewrite_tac [fetch "-" "bvl_inline_tick_inline_side_def"]
  \\ fs [])
  |> update_precondition;

val r = translate (bvl_inlineTheory.is_small_aux_def |> REWRITE_RULE [GSYM sub_check_def]);

Theorem bvl_inline_is_small_aux_ind[local]:
  bvl_inline_is_small_aux_ind
Proof
  once_rewrite_tac [fetch "-" "bvl_inline_is_small_aux_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD,sub_check_def]
QED

val _ = bvl_inline_is_small_aux_ind |> update_precondition;

val r = translate bvl_inlineTheory.tick_inline_all_def;

val bvl_inline_tick_inline_all_side = Q.prove (
  `!a0 a1 a2 a3. bvl_inline_tick_inline_all_side a0 a1 a2 a3 <=> T`,
  ho_match_mp_tac bvl_inlineTheory.tick_inline_all_ind
  \\ `!(x:(num # bvl$exp) num_map) y. tick_inline x [y] <> []` by
   (CCONTR_TAC \\ fs []
    \\ Q.ISPECL_THEN [`x`,`[y]`] assume_tac bvl_inlineTheory.LENGTH_tick_inline
    \\ rfs [])
  \\ rw []
  \\ once_rewrite_tac [fetch "-" "bvl_inline_tick_inline_all_side_def"]
  \\ fs [])
  |> update_precondition;

val r = translate bvl_inlineTheory.let_op_def;

Theorem let_op_SING_NOT_NIL[simp]:
   let_op [x] <> []
Proof
  Cases_on `x` \\ fs [bvl_inlineTheory.let_op_def]
  \\ CASE_TAC \\ fs []
QED

val bvl_inline_let_op_side = Q.prove(`
  ∀a. bvl_inline_let_op_side a ⇔ T`,
  ho_match_mp_tac bvl_inlineTheory.let_op_ind \\ rw []
  \\ once_rewrite_tac [fetch "-" "bvl_inline_let_op_side_def"] \\ fs [])
  |> update_precondition;

val r = translate bvl_inlineTheory.remove_ticks_def;

Theorem bvl_inline_remove_ticks_side = Q.prove(`
  !a. bvl_inline_remove_ticks_side a`,
  ho_match_mp_tac bvl_inlineTheory.remove_ticks_ind
  \\ sg `!x. remove_ticks [x] <> []`
  >-
   (CCONTR_TAC \\ fs []
    \\ pop_assum (mp_tac o Q.AP_TERM `LENGTH`)
    \\ fs [bvl_inlineTheory.LENGTH_remove_ticks])
  \\ rw [] \\ rw [Once (fetch "-" "bvl_inline_remove_ticks_side_def")])
  |> update_precondition;

val r = translate bvl_inlineTheory.compile_prog_def;

Theorem bvl_inline_compile_prog_side = Q.prove(`
  !a b c d. bvl_inline_compile_prog_side a b c d`,
  rw [Once (fetch "-" "bvl_inline_compile_prog_side_def"),
      Once (fetch "-" "bvl_inline_compile_inc_side_def"),
      Once (fetch "-" "bvl_inline_optimise_side_def")]
  \\ strip_tac
  \\ pop_assum (mp_tac o Q.AP_TERM `LENGTH`)
  \\ fs [bvl_inlineTheory.LENGTH_remove_ticks])
  |> update_precondition;

Theorem bvl_inline_compile_inc_side = Q.prove(`
  !a b c d e. bvl_inline_compile_inc_side a b c d e`,
  rw [Once (fetch "-" "bvl_inline_compile_prog_side_def"),
      Once (fetch "-" "bvl_inline_compile_inc_side_def"),
      Once (fetch "-" "bvl_inline_optimise_side_def")]
  \\ strip_tac
  \\ pop_assum (mp_tac o Q.AP_TERM `LENGTH`)
  \\ fs [bvl_inlineTheory.LENGTH_remove_ticks])
  |> update_precondition;

(* ------------------------------------------------------------------------- *)
(* bvi_let                                                                   *)
(* ------------------------------------------------------------------------- *)

val r = translate bvi_letTheory.compile_def;

val bvi_let_compile_side = Q.prove(`
  ∀x y z. bvi_let_compile_side x y z ⇔ T`,
  ho_match_mp_tac bvi_letTheory.compile_ind>>rw[]>>
  `∀a b c . bvi_let$compile a b [c] ≠ []` by
    (CCONTR_TAC>>fs[]>>
    pop_assum (mp_tac o Q.AP_TERM`LENGTH`)>>
    simp[bvi_letTheory.compile_length])>>
  rw[]>>simp[Once (fetch "-" "bvi_let_compile_side_def")]>>
  Cases_on`z`>>fs[]>>
  strip_tac>>fs[ADD1]) |> update_precondition;

val r = translate bvi_letTheory.compile_exp_def;

(* ------------------------------------------------------------------------- *)
(* bvi_tailrec                                                               *)
(* ------------------------------------------------------------------------- *)

val r = translate bvi_tailrecTheory.is_rec_PMATCH;
val r = translate bvi_tailrecTheory.is_const_PMATCH;
val r = translate bvi_tailrecTheory.from_op_PMATCH;
val r = translate bvi_tailrecTheory.op_eq_PMATCH;
val r = translate bvi_tailrecTheory.index_of_PMATCH;
val r = translate bvi_tailrecTheory.args_from_PMATCH;
val r = translate bvi_tailrecTheory.get_bin_args_PMATCH;
val r = translate bvi_tailrecTheory.is_arith_PMATCH;
val r = translate bvi_tailrecTheory.is_rel_PMATCH;
val r = translate bvi_tailrecTheory.decide_ty_PMATCH;
val r = translate bvi_tailrecTheory.arg_ty_PMATCH;
val r = translate bvi_tailrecTheory.op_ty_PMATCH;
val r = translate bvi_tailrecTheory.scan_expr_def;

val r = translate bvi_tailrecTheory.rewrite_PMATCH;

val r = translate bvi_tailrecTheory.compile_prog_def;

(* ------------------------------------------------------------------------- *)
(* bvi_inline                                                                *)
(* ------------------------------------------------------------------------- *)

val r = translate bvi_inlineTheory.bvi_mk_tick_def;

val r = translate bvi_inlineTheory.canonical_wrapper_def;
val r = translate bvi_inlineTheory.wrapper_ok_def;

val r = translate bvi_inlineTheory.inline_exp_def;

val r = translate (bvi_inlineTheory.remove_ticks_exp_def
                     |> PURE_REWRITE_RULE [oneline OPTION_MAP_DEF, o_THM]);

val r = translate bvi_inlineTheory.inline_all_def;
val r = translate bvi_inlineTheory.compile_inc_def;
val r = translate bvi_inlineTheory.compile_prog_def;

val _ = r |> hyp |> null orelse
        failwith "Unproved side condition in the translation of bvi_inlineTheory.compile_prog_def.";

(* ------------------------------------------------------------------------- *)
(* bvi_tmc                                                                   *)
(* ------------------------------------------------------------------------- *)

(* pure_exp/pure_exps is given by one mutually recursive definition, which is
   what cv_trans needs but which this translator's preprocessor cannot reduce
   to one line per function.  We therefore translate the equivalent non-mutual
   equations for pure_exps instead (the same split as bvi_let$compile_def vs
   bvi_let$compile_sing_def) and define pure_exp on top of them. *)

val r = translate bvi_tmcTheory.pure_exps_eqns;
val r = translate bvi_tmcTheory.pure_exp_eq;

(* bvi_to_cb_aux_sing/bvi_to_cb_aux, by contrast, the preprocessor handles as
   it stands. *)

val r = translate bvi_tmcTheory.bvi_to_cb_aux_def;

val r = translate bvi_tmcTheory.subst_def;

Theorem bvi_tmc_subst_side[local]:
  (∀xs e. bvi_tmc_subst_side xs e) ∧
  (∀xs es. bvi_tmc_substs_side xs es)
Proof
  ho_match_mp_tac bvi_tmcTheory.subst_ind>>
  rw[]>>
  simp[Once (fetch "-" "bvi_tmc_subst_side_def")]>>
  rw[LLOOKUP_THM]
QED

val _ = bvi_tmc_subst_side |> update_precondition;

(* ------------------------------------------------------------------------- *)
(* bvl_to_bvi                                                                *)
(* ------------------------------------------------------------------------- *)

val r = translate bvl_to_bviTheory.compile_int_def;
val r = translate bvl_to_bviTheory.compile_aux_def;
val r = translate bvl_to_bviTheory.compile_op_def;
val r = translate bvl_to_bviTheory.compile_exps_def;

val bvl_to_bvi_compile_exps_side = Q.prove(`
  ∀x y. bvl_to_bvi_compile_exps_side x y ⇔ T`,
  ho_match_mp_tac bvl_to_bviTheory.compile_exps_ind>>
  `∀a b c d. bvl_to_bvi$compile_exps a [b] ≠ ([],c,d)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac bvl_to_bviTheory.compile_exps_LENGTH>>
    fs[])>>
  rw[]>>simp[Once (fetch "-" "bvl_to_bvi_compile_exps_side_def")]>>
  metis_tac[]) |> update_precondition;

val r = translate bvl_to_bviTheory.compile_single_def;

val bvl_to_bvi_compile_single_side = Q.prove(`
  ∀x y. bvl_to_bvi_compile_single_side x y ⇔ T`,
  EVAL_TAC \\ rw[]
  \\ imp_res_tac bvl_to_bviTheory.compile_exps_LENGTH
  \\ CCONTR_TAC \\ fs[]) |> update_precondition;

val r = translate bvl_to_bviTheory.compile_list_def;
val r = translate bvl_to_bviTheory.compile_prog_def;
val r = translate bvl_to_bviTheory.compile_def;

val _ = r |> hyp |> null orelse
        failwith "Unproved side condition in the translation of bvl_to_bviTheory.compile_def.";

val r = translate bvl_to_bviTheory.compile_inc_def;
val r = translate bvl_to_bviTheory.bvl_to_bvi_compile_inc_all_def;

(* ------------------------------------------------------------------------- *)
(* backend                                                                   *)
(* ------------------------------------------------------------------------- *)

val _ = translate backendTheory.from_bvl_def;

(* ------------------------------------------------------------------------- *)

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
val _ = ml_translatorLib.clean_on_exit := true;
