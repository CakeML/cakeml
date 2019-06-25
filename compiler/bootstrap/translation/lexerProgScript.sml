(*
  Translate the compiler's lexer.
*)
open preamble
     lexer_funTheory lexer_implTheory to_dataProgTheory
     ml_translatorLib ml_translatorTheory

val _ = new_theory "lexerProg"

val _ = translation_extends "to_dataProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "lexerProg");

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

Theorem NOT_NIL_AND_LEMMA:
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
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val _ = translate get_token_eqn

val _ = translate (next_token_def |> SIMP_RULE std_ss [next_sym_eq])

val _ = translate lexer_fun_def

val l2n_side = Q.prove(`
  ∀b a. a ≠ 0 ⇒ l2n_side a b`,
  Induct>>
  rw[Once (fetch"-""l2n_side_def")]) |> update_precondition;

val num_from_dec_string_alt_side = Q.prove(`
  ∀x. num_from_dec_string_alt_side x ⇔ T`,
  simp[Once (fetch"-""num_from_dec_string_alt_side_def")]>>
  strip_tac>>CONJ_TAC
  >-
    simp[Once (fetch"-""s2n_side_def"),l2n_side]
  >>
    simp[Once (fetch"-""unhex_alt_side_def"),Once (fetch"-""unhex_side_def"),isDigit_def,isHexDigit_def]>>Cases>>
    fs[ORD_CHR]>>
    strip_tac>>
    fs[]) |> update_precondition;

val num_from_hex_string_alt_side = Q.prove(`
  ∀x. num_from_hex_string_alt_side x ⇔ T`,
  simp[Once (fetch"-""num_from_hex_string_alt_side_def")]>>
  strip_tac>>CONJ_TAC
  >-
    simp[Once (fetch"-""s2n_side_def"),l2n_side]
  >>
    simp[Once (fetch"-""unhex_alt_side_def"),Once (fetch"-""unhex_side_def"),isDigit_def,isHexDigit_def]>>Cases>>
    fs[ORD_CHR]>>
    strip_tac>>
    fs[]) |> update_precondition;

val read_string_side = Q.prove(`
  ∀x y l.
  read_string_side x y l ⇔ T`,
  ho_match_mp_tac read_string_ind>>
  rw[]>>
  simp[Once (fetch"-""read_string_side_def")]);

val next_sym_alt_side = Q.prove(`
  ∀x l. next_sym_alt_side x l ⇔ T`,
  ho_match_mp_tac next_sym_alt_ind>>rw[]>>
  simp[Once (fetch"-""next_sym_alt_side_def"),num_from_dec_string_alt_side,read_string_side,num_from_hex_string_alt_side]>>
  rw[]>>
  fs[FALSE_def]);

val lexer_fun_aux_side = Q.prove(`
  ∀x l. lexer_fun_aux_side x l ⇔ T`,
  ho_match_mp_tac lexer_fun_aux_ind>>rw[]>>
  simp[Once (fetch"-""lexer_fun_aux_side_def"),
       Once (fetch"-""next_token_side_def"),next_sym_alt_side]) |> update_precondition

val lexer_fun_side = Q.prove(`
  ∀x. lexer_fun_side x ⇔ T`,
  EVAL_TAC>>fs[lexer_fun_aux_side]) |> update_precondition

val () = Feedback.set_trace "TheoryPP.include_docs" 0

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
