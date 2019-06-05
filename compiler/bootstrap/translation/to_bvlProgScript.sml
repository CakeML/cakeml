(*
  Translate the backend phase from closLang to BVL.
*)
open preamble ml_translatorLib ml_translatorTheory to_closProgTheory
local open backendTheory in end

val _ = new_theory "to_bvlProg";
val _ = translation_extends "to_closProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "to_bvlProg");

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

(* ------------------------------------------------------------------------- *)
(* clos_to_bvl                                                               *)
(* ------------------------------------------------------------------------- *)

val r = translate clos_to_bvlTheory.compile_common_def;
val r = translate clos_to_bvlTheory.compile_def;

(* N.B.
 * Do not remove this! prove_EvalPatRel depends on it (though it should be
 * expanded there, not added to the simpset).
 *)
val _ = save_thm ("same_type_def[simp]",
  semanticPrimitivesTheory.same_type_def);

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

(* ------------------------------------------------------------------------- *)
(* bvl_const                                                                 *)
(* ------------------------------------------------------------------------- *)

val r = translate bvl_constTheory.dest_simple_pmatch;
val r = translate bvl_constTheory.case_op_const_pmatch;
val r = translate bvl_constTheory.SmartOp_flip_pmatch;
(* val r = translate bvl_constTheory.SmartOp2_pmatch *) (* prove_EvalPatBind *)
val r = translate bvl_constTheory.SmartOp2_def;
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

(* ------------------------------------------------------------------------- *)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
val _ = ml_translatorLib.clean_on_exit := true;
val _ = export_theory ();

