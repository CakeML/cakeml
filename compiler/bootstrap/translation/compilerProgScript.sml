open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open inferProgTheory;

val _ = new_theory "compilerProg"
val _ = translation_extends "inferProg";

(* This is the compiler "preamble" that translates the compile functions down to BVP *)

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

val NOT_NIL_AND_LEMMA = prove(
  ``(b <> [] /\ x) = if b = [] then F else x``,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
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

val _ = translate (source_to_modTheory.compile_def);

val _ = translate (mod_to_conTheory.compile_def);

val _ = translate (con_to_decTheory.compile_def);

val _ = translate (dec_to_exhTheory.compile_exp_def);

val _ = translate (exh_to_patTheory.pure_op_op_eqn);
val _ = translate (exh_to_patTheory.compile_def);

val _ = translate (pat_to_closTheory.compile_def);

val pat_to_clos_compile_side = prove(``
  ∀x. pat_to_clos_compile_side x ⇔ T``,
  recInduct pat_to_closTheory.compile_ind>>
  rw[]>>
  simp[Once (fetch "-" "pat_to_clos_compile_side_def")]>>
  Cases_on`es`>>fs[])|>update_precondition;

val _ = translate(clos_mtiTheory.intro_multi_def)

val clos_mti_intro_multi_side = prove(``
  ∀max_app a. clos_mti_intro_multi_side max_app a ⇔ T``,
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

val clos_number_renumber_code_locs_list_side = prove(``
  (∀a b. clos_number_renumber_code_locs_list_side a b ⇔ T) ∧
  (∀a b. clos_number_renumber_code_locs_side a b ⇔ T)``,
  ho_match_mp_tac clos_numberTheory.renumber_code_locs_ind>>rw[]>>
  simp[Once (fetch"-" "clos_number_renumber_code_locs_list_side_def")]>>
  metis_tac[clos_numberTheory.renumber_code_locs_length,LENGTH_MAP,SND]) |> update_precondition

(* known *)
val _ = translate clos_knownTheory.merge_alt

val num_abs_intro = prove(``
  ∀x. Num x = if 0 ≤ x then Num (ABS x) else Num x``,
  rw[]>>intLib.COOPER_TAC);

val _ = translate (clos_knownTheory.known_op_def |> ONCE_REWRITE_RULE [num_abs_intro] |> SIMP_RULE std_ss []);

val _ = translate (clos_knownTheory.known_def)

val clos_known_known_op_side = prove(``
  ∀a b c. clos_known_known_op_side a b c ⇔ T``,
  simp[Once (fetch"-" "clos_known_known_op_side_def")]>>rw[]>>
  intLib.COOPER_TAC)

val clos_known_known_side = prove(``
  ∀a b c. clos_known_known_side a b c ⇔ T``,
  ho_match_mp_tac clos_knownTheory.known_ind>>
  `∀z a b c. known [z] a b ≠ ([],c)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac clos_knownTheory.known_sing_EQ_E>>
    fs[])>>
  rw[]>>simp[Once (fetch"-" "clos_known_known_side_def")]>>
  metis_tac[FST,PAIR,clos_known_known_op_side]) |> update_precondition

(* call *)

val _ = translate (clos_callTheory.calls_def)

val clos_free_free_side = prove(``
  ∀a. clos_free_free_side a ⇔ T``,
  ho_match_mp_tac clos_freeTheory.free_ind>>rw[]>>
  simp[Once (fetch "-" "clos_free_free_side_def")]>>rw[]>>
  CCONTR_TAC>>fs[]>>
  imp_res_tac clos_freeTheory.free_SING>>fs[]>>
  metis_tac[]) |> update_precondition

val clos_call_calls_side = prove(``
  ∀a b. clos_call_calls_side a b ⇔ T``,
  ho_match_mp_tac clos_callTheory.calls_ind>>
  (*Move from calls proof*)
  `∀a b c. calls [a] b ≠ ([],c)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac clos_callTheory.calls_sing>>fs[])>>
  rw[]>> simp[Once (fetch"-" "clos_call_calls_side_def"),Once (fetch "-" "clos_call_closed_side_def"),clos_free_free_side]>>
  TRY(metis_tac[])>>
  ntac 2 strip_tac>>
  simp[LAMBDA_PROD]>> rw[fetch "-" "clos_call_closed_side_def",clos_free_free_side]
  >-
    metis_tac[LIST_REL_LENGTH,LAMBDA_PROD]
  >>
    simp[GSYM LAMBDA_PROD]>>rw[]
    >- (imp_res_tac clos_callTheory.calls_length>>fs[])
    >> metis_tac[LIST_REL_LENGTH,LAMBDA_PROD]) |> update_precondition

(* remove *)
val _ = save_thm ("remove_ind",clos_removeTheory.remove_alt_ind)

val _ = translate (clos_removeTheory.remove_alt)

val clos_remove_remove_side = prove(``
  ∀x. clos_remove_remove_side x ⇔ T``,
  recInduct clos_removeTheory.remove_alt_ind>>
  rw[]>>
  simp[Once (fetch "-" "clos_remove_remove_side_def")]>>
  rw[]>>
  imp_res_tac clos_removeTheory.remove_SING>>fs[]>>
  TRY(first_x_assum match_mp_tac>>fs[]>>metis_tac[])>>
  CCONTR_TAC>>fs[]>>
  imp_res_tac clos_removeTheory.remove_SING>>fs[])|>update_precondition

(* shift *)
val _ = translate (clos_annotateTheory.shift_def)

val clos_annotate_shift_side = prove(``
  ∀a b c d. clos_annotate_shift_side a b c d ⇔ T``,
  ho_match_mp_tac clos_annotateTheory.shift_ind>>
  `∀a b c d. shift [a] b c d ≠ []` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac clos_annotateTheory.shift_SING>>
    fs[])>>
  rw[]>>
  simp[Once (fetch "-" "clos_annotate_shift_side_def")]>>
  rw[]>> metis_tac[]) |> update_precondition

val _ = translate clos_to_bvlTheory.compile_def

val bvl_jump_jumplist_side = prove(``
  ∀a b. bvl_jump_jumplist_side a b ⇔ T``,
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
    simp[]);

val clos_to_bvl_recc_lets_side = prove(``
  ∀a b c d.
  c = LENGTH b ⇒
  clos_to_bvl_recc_lets_side a b c d``,
  ho_match_mp_tac clos_to_bvlTheory.recc_Lets_ind>>
  rw[]>>
  simp[Once (fetch"-" "clos_to_bvl_recc_lets_side_def")]>>
  Cases_on`b`>>fs[])

val clos_to_bvl_compile_exps_side = prove(``
  ∀max_app a b. clos_to_bvl_compile_exps_side max_app a b``,
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
  CCONTR_TAC>>fs[])

val clos_to_bvl_compile_prog_side = prove(``
  ∀max_app x. clos_to_bvl_compile_prog_side max_app x ⇔ T``,
  ho_match_mp_tac clos_to_bvlTheory.compile_prog_ind>>rw[]>>
  simp[Once (fetch "-" "clos_to_bvl_compile_prog_side_def"),clos_to_bvl_compile_exps_side])

val clos_to_bvl_compile_side = prove(``
  ∀x y. clos_to_bvl_compile_side x y ⇔ T``,
  rw[Once (fetch "-" "clos_to_bvl_compile_side_def"),
  Once (fetch "-" "clos_call_compile_side_def"),
  Once (fetch "-" "clos_to_bvl_compile_prog_side_def"),
  Once (fetch "-" "clos_remove_compile_side_def"),
  Once (fetch "-" "clos_known_compile_side_def")]
  >-
    (CCONTR_TAC>>fs[]>>
    imp_res_tac clos_callTheory.calls_sing>>
    fs[])
  >-
    (EVAL_TAC>>simp[bvl_jump_jumplist_side])
  >-
    simp[clos_to_bvl_compile_exps_side]
  >-
    simp[clos_to_bvl_compile_prog_side]
  >-
    (EVAL_TAC>>
    CCONTR_TAC >> fs[]>>
    Cases_on`free [v1]`>>
    imp_res_tac clos_freeTheory.free_SING>>fs[]>>
    imp_res_tac clos_annotateTheory.shift_SING>>fs[])
  >-
    (qpat_abbrev_tac`ls = v6'::A`>>
    Cases_on`remove ls`>>fs[Abbr`ls`]>>
    imp_res_tac clos_removeTheory.remove_LENGTH>>
    simp[])
  >-
    (CCONTR_TAC>>fs[]>>
    imp_res_tac clos_knownTheory.known_sing_EQ_E>>
    fs[])
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

val bvl_handle_compile_side = prove(``
  ∀x y z. bvl_handle_compile_side x y z ⇔ T``,
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

val bvl_inline_inline_side = prove(``
  ∀x y. bvl_inline_inline_side x y ⇔ T``,
  ho_match_mp_tac bvl_inlineTheory.inline_ind>>
  `∀a b. bvl_inline$inline a [b] ≠ []` by
    (CCONTR_TAC>>fs[]>>
    pop_assum (mp_tac o Q.AP_TERM`LENGTH`)>>
    simp[bvl_inlineTheory.LENGTH_inline])>>
  rw[]>>
  simp[Once (fetch "-" "bvl_inline_inline_side_def")])|>update_precondition

val _ = translate (bvl_constTheory.compile_def)

val bvl_const_compile_side = prove(``
  ∀x y. bvl_const_compile_side x y ⇔ T``,
  ho_match_mp_tac bvl_constTheory.compile_ind>>
  `∀a b. bvl_const$compile a [b] ≠ []` by
    (CCONTR_TAC>>fs[]>>
    pop_assum (mp_tac o Q.AP_TERM`LENGTH`)>>
    simp[bvl_constTheory.compile_length])>>
  rw[]>>
  simp[Once (fetch "-" "bvl_const_compile_side_def")])|>update_precondition

val _ = translate(bvl_to_bviTheory.compile_int_def)

val bvl_to_bvi_compile_int_side = prove(``
  ∀x. bvl_to_bvi_compile_int_side x ⇔ T``,
  completeInduct_on`Num(ABS x)`>>
  simp[Once (fetch "-" "bvl_to_bvi_compile_int_side_def")]>>
  rw[]>>fs[PULL_FORALL]>>
  first_assum MATCH_MP_TAC>>
  intLib.COOPER_TAC) |> update_precondition

val _ = translate(bvl_to_bviTheory.compile_def)

val bvl_inline_inline_all_side = prove(``
  ∀a b c d. bvl_inline_inline_all_side a b c d ⇔ T``,
  ho_match_mp_tac bvl_inlineTheory.inline_all_ind>>
  rw[]>>simp[Once (fetch "-" "bvl_inline_inline_all_side_def")]>>
  CCONTR_TAC>>fs[]>>
  pop_assum (mp_tac o Q.AP_TERM`LENGTH`)>>
  simp[bvl_inlineTheory.LENGTH_inline])

val bvi_let_compile_side = prove(``
  ∀x y z. bvi_let_compile_side x y z ⇔ T``,
  ho_match_mp_tac bvi_letTheory.compile_ind>>rw[]>>
  `∀a b c . bvi_let$compile a b [c] ≠ []` by
    (CCONTR_TAC>>fs[]>>
    pop_assum (mp_tac o Q.AP_TERM`LENGTH`)>>
    simp[bvi_letTheory.compile_length])>>
  rw[]>>simp[Once (fetch "-" "bvi_let_compile_side_def")]>>
  Cases_on`z`>>fs[]>>
  strip_tac>>fs[ADD1])

val bvl_to_bvi_compile_exps_side = prove(``
  ∀x y. bvl_to_bvi_compile_exps_side x y ⇔ T``,
  ho_match_mp_tac bvl_to_bviTheory.compile_exps_ind>>
  `∀a b c d. bvl_to_bvi$compile_exps a [b] ≠ ([],c,d)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac bvl_to_bviTheory.compile_exps_LENGTH>>
    fs[])>>
  rw[]>>simp[Once (fetch "-" "bvl_to_bvi_compile_exps_side_def")]>>
  metis_tac[])

val bvl_to_bvi_compile_list_side = prove(``
  ∀x y. bvl_to_bvi_compile_list_side x y ⇔ T``,
  Induct_on`y`>>rw[]>>
  simp[Once (fetch "-" "bvl_to_bvi_compile_list_side_def")]>>
  EVAL_TAC>>rw[]>>simp[bvi_let_compile_side,bvl_to_bvi_compile_exps_side]>>
  CCONTR_TAC>>fs[]>>imp_res_tac bvl_to_bviTheory.compile_exps_LENGTH>>
  fs[])

val bvl_to_bvi_compile_side = prove(``
  ∀w x y z. bvl_to_bvi_compile_side w x y z ⇔ T``,
  EVAL_TAC>>
  rpt strip_tac
  >-
    fs[bvl_to_bvi_compile_list_side]
  >-
    (pop_assum (mp_tac o Q.AP_TERM`LENGTH`)>>
    simp[bvl_handleTheory.compile_length])
  >>
    simp[bvl_inline_inline_all_side]) |> update_precondition

val _ = translate (bvi_to_dataTheory.op_requires_names_eqn)
val _ = translate (COUNT_LIST_compute)

(* TODO: For some reason, the following def on sptrees fails to translate in a standalone manner (when the rest of this file's translation isn't loaded). Needs investigation. *)
val _ = translate (list_to_num_set_def)

val _ = translate (bvi_to_dataTheory.compile_def)

val bvi_to_data_compile_side = prove(``
  ∀a b c d e. bvi_to_data_compile_side a b c d e ⇔ T``,
  ho_match_mp_tac bvi_to_dataTheory.compile_ind>>
  `∀a b c d e f g. bvi_to_data$compile a b c d [e] ≠ (f,[],g)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac bvi_to_dataTheory.compile_SING_IMP>>
    fs[])>>
  rw[]>>
  simp[Once (fetch "-" "bvi_to_data_compile_side_def")]>>
  fs[FALSE_def]>>
  metis_tac[])|>update_precondition

val _ = translate (bvi_to_dataTheory.compile_prog_def)

val _ = export_theory();
