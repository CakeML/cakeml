(*
  Translate the backend phase from BVL to BVI.
*)
Theory to_bviProg
Ancestors
  ml_translator to_bvlProg
Libs
  preamble ml_translatorLib

open preamble ml_translatorLib ml_translatorTheory to_bvlProgTheory

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = translation_extends "to_bvlProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "to_bviProg");
val _ = ml_translatorLib.use_string_type true;

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

Triviality NOT_NIL_AND_LEMMA:
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

val r = translate bvl_to_bviTheory.get_names_def;

val bvl_to_bvi_get_names_side = Q.prove(`
  ∀x y. bvl_to_bvi_get_names_side x y ⇔ T`,
  EVAL_TAC \\ fs []) |> update_precondition;

val r = translate bvl_to_bviTheory.compile_list_def;
val r = translate bvl_to_bviTheory.compile_prog_def;
val r = translate bvl_to_bviTheory.compile_def;

val _ = r |> hyp |> null orelse
        failwith "Unproved side condition in the translation of bvl_to_bviTheory.compile_def.";

val r = translate bvl_to_bviTheory.compile_inc_def;
val r = translate bvl_to_bviTheory.bvl_to_bvi_compile_inc_all_def;

(* ------------------------------------------------------------------------- *)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
val _ = ml_translatorLib.clean_on_exit := true;
