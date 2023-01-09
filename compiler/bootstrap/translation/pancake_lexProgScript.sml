(*
  Translate pancake's lexer
*)
open preamble;
open ml_translatorLib ml_translatorTheory;
open panLexerTheory locationTheory;
open caml_parserProgTheory;

val _ = new_theory "pancake_lexProg"

val _ = translation_extends "caml_parserProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "pancake_lexerProg");

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

Theorem num_from_dec_string_side_lemma:
  ∀x. num_from_dec_string_side x
Proof

QED

Theorem next_token_2_side_lemma:
  ∀x. next_token_2 x
Proof

QED

Theorem pancake_lex_aux_side_lemma:
  ∀x. pancake_lex_aux x
Proof

QED

Theorem pancake_lex_side_lemma:
  ∀x. pancake_lex_side x
Proof

QED

val _ = translate pancake_lex_def;
