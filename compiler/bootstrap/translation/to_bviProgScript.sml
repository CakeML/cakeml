(*
  Translate the backend phase from BVL to BVI.
*)
open preamble ml_translatorLib ml_translatorTheory to_bvlProgTheory

val _ = new_theory "to_bviProg";
val _ = translation_extends "to_bvlProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "to_bviProg");

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

Theorem bvi_tailrec_scan_expr_side = Q.prove(`
  !a0 a1 a2. bvi_tailrec_scan_expr_side a0 a1 a2`,
  recInduct bvi_tailrecTheory.scan_expr_ind \\ rw []
  \\ once_rewrite_tac [fetch "-" "bvi_tailrec_scan_expr_side_def"] \\ fs []
  \\ FULL_CASE_TAC \\ fs []) |> update_precondition;

val r = translate bvi_tailrecTheory.rewrite_PMATCH;

Theorem bvi_tailrec_rewrite_side = Q.prove(`
  !v58 v59 v60 v56 v61 v57. bvi_tailrec_rewrite_side v58 v59 v60 v56 v61 v57`,
  recInduct bvi_tailrecTheory.rewrite_ind \\ rw []
  \\ once_rewrite_tac [fetch "-" "bvi_tailrec_rewrite_side_def"] \\ fs []
  \\ FULL_CASE_TAC \\ fs []) |> update_precondition;

val r = translate bvi_tailrecTheory.compile_prog_def;

(* ------------------------------------------------------------------------- *)
(* bvl_to_bvi                                                                *)
(* ------------------------------------------------------------------------- *)

val r = translate bvl_to_bviTheory.compile_int_def;

val bvl_to_bvi_compile_int_side = Q.prove(`
  ∀x. bvl_to_bvi_compile_int_side x ⇔ T`,
  completeInduct_on`Num(ABS x)`>>
  simp[Once (fetch "-" "bvl_to_bvi_compile_int_side_def")]>>
  rw[]>>fs[PULL_FORALL]>>
  first_assum MATCH_MP_TAC>>
  intLib.COOPER_TAC) |> update_precondition;


val r = translate bvl_to_bviTheory.compile_aux_def;

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

(* ------------------------------------------------------------------------- *)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
val _ = ml_translatorLib.clean_on_exit := true;
val _ = export_theory ();

