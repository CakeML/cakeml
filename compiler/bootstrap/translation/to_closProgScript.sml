(*
  Translate the backend phase from flatLang to closLang.
*)
open preamble ml_translatorLib ml_translatorTheory to_flatProgTheory
local open flat_to_closTheory clos_mtiTheory clos_numberTheory
  clos_knownTheory clos_callTheory clos_annotateTheory in end

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "to_closProg";
val _ = translation_extends "to_flatProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "to_closProg");
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
(* flat_to_clos                                                               *)
(* ------------------------------------------------------------------------- *)

val r = translate flat_to_closTheory.dest_pat_pmatch;
val r = translate flat_to_closTheory.arg1_pmatch;
val r = translate flat_to_closTheory.arg2_pmatch;

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

Definition dest_sing_list_def:
  dest_sing_list x =
    dtcase x of [y] => SOME y | _ => NONE
End

val r = translate dest_sing_list_def;

Definition dest_App_Ord_pmatch:
  dest_App_Ord x =
    case x of App _ Ord es => dest_sing_list es | _ => NONE
End

val r = translate dest_App_Ord_pmatch;

Definition dest_App_WordToIntW8_pmatch:
  dest_App_WordToIntW8 x =
    case x of App _ (WordToInt W8) es => dest_sing_list es | _ => NONE
End

val r = translate dest_App_WordToIntW8_pmatch;

Theorem dest_nop_pmatch:
  dest_nop op e =
    case op of
    | WordFromInt W8 =>
        (dtcase dest_sing_list e of NONE => NONE | SOME e => dest_App_Ord e)
    | Chr =>
        (dtcase dest_sing_list e of NONE => NONE | SOME e => dest_App_WordToIntW8 e)
    | _ => NONE
Proof
  CONV_TAC(ONCE_DEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ Cases_on ‘op’ \\ fs [flat_to_closTheory.dest_nop_def]
  THEN1
   (Cases_on ‘w’ \\ fs []
    \\ Cases_on ‘e’ \\ fs [dest_sing_list_def]
    \\ Cases_on ‘t’ \\ fs [dest_sing_list_def]
    \\ fs [dest_App_Ord_pmatch,dest_App_WordToIntW8_pmatch]
    \\ CONV_TAC(ONCE_DEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV)
    \\ every_case_tac \\ fs [flat_to_closTheory.dest_nop_def,dest_sing_list_def])
  \\ fs [dest_App_Ord_pmatch,dest_App_WordToIntW8_pmatch]
  \\ CONV_TAC(ONCE_DEPTH_CONV patternMatchesLib.PMATCH_ELIM_CONV)
  \\ Cases_on ‘e’ \\ fs [dest_sing_list_def]
  \\ Cases_on ‘t’ \\ fs [dest_sing_list_def]
  \\ Cases_on ‘h’ \\ fs [dest_sing_list_def]
  \\ every_case_tac \\ fs [flat_to_closTheory.dest_nop_def,dest_sing_list_def]
QED

val r = translate dest_nop_pmatch;
val r = translate flat_to_closTheory.compile_def;

val flat_to_clos_compile_side = Q.prove(
  `∀m xs. flat_to_clos_compile_side m xs ⇔ T`,
  recInduct flat_to_closTheory.compile_ind>>
  rw[]>>
  simp[Once (fetch "-" "flat_to_clos_compile_side_def")]>>
  rw[]>>
  res_tac
  ) |> update_precondition

val r = translate flat_to_closTheory.compile_decs_def;

val r = translate flat_to_closTheory.inc_compile_decs_def;

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
val r = translate miscTheory.make_even_def;
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

val num_abs_intro = Q.prove(`
  ∀x. Num x = if 0 ≤ x then Num (ABS x) else Num x`,
  rw[]>>intLib.COOPER_TAC);

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

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
val _ = ml_translatorLib.clean_on_exit := true;
val _ = export_theory ();
