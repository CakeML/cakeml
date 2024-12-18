(*
  Translate pancake's lexer
*)
open preamble
     panLexerTheory locationTheory
     caml_parserProgTheory
     ml_translatorLib ml_translatorTheory

val _ = new_theory "pancake_lexProg"
val _ = translation_extends "caml_parserProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "pancake_lexProg");

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

val _ = ml_translatorLib.use_string_type true;
val _ = register_type “:panLexer$token”;

val _ = ml_translatorLib.use_string_type false;

val _ = translate (next_atom_def |> REWRITE_RULE [GSYM sub_check_def]);

val _ = translate pancake_lex_def;

Theorem unhex_alt_1_side[local]:
  ∀x. unhex_alt_1_side x
Proof
  simp[Once (fetch "-" "unhex_alt_1_side_def"),
       Once (fetch "lexerProg" "unhex_side_def"),
       isHexDigit_def]>>
  Cases>>
  fs[ORD_CHR]>>
  strip_tac>>
  fs[]
QED

val _ = update_precondition unhex_alt_1_side;

Theorem num_from_dec_string_alt_1_side[local]:
  ∀x. num_from_dec_string_alt_1_side x
Proof
  simp[Once (fetch"-""num_from_dec_string_alt_1_side_def")]>>
  strip_tac>>CONJ_TAC
  >-
    simp[Once (fetch"lexerProg""s2n_side_def"), (fetch "lexerProg" "l2n_side")]
  >>
    simp[Once (fetch"-""unhex_alt_1_side_def"),Once (fetch"lexerProg""unhex_side_def"),isDigit_def,isHexDigit_def]>>Cases>>
    fs[ORD_CHR]>>
    strip_tac>>
    fs[]
QED

val _ = update_precondition num_from_dec_string_alt_1_side;

Theorem next_atom_side[local]:
  ∀x y. next_atom_side x y
Proof
  ho_match_mp_tac next_atom_ind>>
  rw []>>
  simp [Once (fetch "-" "next_atom_side_def")]>>
  rpt strip_tac >>
  fs [num_from_dec_string_alt_1_side]
QED

val _ = update_precondition next_atom_side;

Theorem next_token_2_side[local]:
  ∀x y. next_token_2_side x y
Proof
  simp [Once (fetch "-" "next_token_2_side_def"), next_atom_side]
QED

val _ = update_precondition next_token_2_side;

Theorem pancake_lex_aux_side[local]:
  ∀s n. pancake_lex_aux_side s n
Proof
  ho_match_mp_tac pancake_lex_aux_ind>>rw[]>>
  simp [Once (fetch "-" "pancake_lex_aux_side_def"), next_token_2_side]
QED

val _ = update_precondition pancake_lex_aux_side;

Theorem pancake_lex_side[local]:
  ∀x. pancake_lex_side x
Proof
  simp[Once (fetch "-" "pancake_lex_side_def"), pancake_lex_aux_side]
QED

val _ = update_precondition pancake_lex_side;

val () = Feedback.set_trace "TheoryPP.include_docs" 0

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
val _ = ml_translatorLib.clean_on_exit := true;

val _ = export_theory();
