(*
  Translate pancake's lexer
*)
Theory pancake_parseProg
Ancestors
  panPEG pancake_lexProg ml_translator
Libs
  preamble ml_translatorLib

open preamble
     panPEGTheory
     pancake_lexProgTheory
     ml_translatorLib ml_translatorTheory;

val _ = translation_extends "pancake_lexProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "pancake_parseProg");
val _ = ml_translatorLib.use_string_type true;

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

val _ = register_type “:(panLexer$token, pancakeNT, locs) parsetree”;
val _ = register_type “:pancakeNT”;

val _ = translate $ INST_TYPE [alpha|->“:panLexer$token”,
                             beta|->“:(panLexer$token, pancakeNT, locs) parsetree list”,
                             gamma|->“:string”] mknt_def

val _ = translate $ INST_TYPE [alpha|->“:string list”] extract_sum_def

val _ = translate extract_sum_def

val _ = translate $ INST_TYPE [alpha|->“:panLexer$token”,
                             beta|->“:(panLexer$token, pancakeNT, locs) parsetree list”,
                             gamma|->“:string”] choicel_def;

val _ = translate choicel_def;

val _ = translate pegf_def;

val _ = translate seql_def;

val _ = translate consume_tok_def;

val _ = translate mknode_def;

val _ = translate mksubtree_def;

val _ = translate mkleaf_def;

val _ = translate keep_tok_def;

val _ = translate keep_kw_def;

val _ = translate consume_kw_def;

val _ = translate keep_ident_def;

val _ = translate try_def;

val _ = translate keep_nat_def;

val _ = translate keep_int_def;

val _ = translate pancake_peg_def;

val _ = translate parse_def;

Theorem parse_side_lemma = Q.prove(`
  !x. parse_side x = T`,
  SIMP_TAC std_ss [fetch "-" "parse_side_def",
                   parserProgTheory.peg_exec_side_def,
                   parserProgTheory.coreloop_side_def] \\
  rpt strip_tac \\
  assume_tac PEG_wellformed \\
  drule_then strip_assume_tac pegexecTheory.peg_exec_total \\
  first_x_assum $ qspec_then `x` strip_assume_tac \\
  gvs [pegexecTheory.peg_exec_def,
       pegexecTheory.coreloop_def,
       AllCaseEqs(),
       pegexecTheory.evalcase_distinct,
       SIMP_CONV (srw_ss()) [pancake_peg_def] ``pancake_peg.start``,
       IS_SOME_EXISTS] \\
  rename1 ‘_ = SOME (Result rr)’ \\
  qexists_tac `Result rr`\\
  pop_assum (REWRITE_TAC o single o GSYM) \\
  rpt (AP_THM_TAC ORELSE AP_TERM_TAC) \\
  rw[FUN_EQ_THM] \\
  rpt(PURE_FULL_CASE_TAC >> gvs[FDOM_FLOOKUP]) \\
  gvs [flookup_thm])
  |> update_precondition;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);
