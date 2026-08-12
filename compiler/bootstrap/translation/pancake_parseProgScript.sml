(*
  Translate pancake's parser
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

Definition peg_pancake_rules_def:
  peg_pancake_rules n fk k tf3 errs eo r i =
  case FLOOKUP pancake_peg.rules n of
  | NONE => Looped
  | SOME x => pegexec$EV x i r eo errs (appf1 tf3 k) fk
End

val r = peg_pancake_rules_def
  |> RW [pancake_peg_def, oneline OPTION_BIND_def]
  |> SRULE [FUPDATE_LIST, parserProgTheory.option_CASE_FLOOKUP_SIMP, FOLDL]
  |> translate;

val r = parse_def
  |> RW [pegexecTheory.peg_exec_def, GSYM peg_pancake_rules_def,
         pegexecTheory.coreloop_def, parserProgTheory.INTRO_FLOOKUP]
  |> SRULE [pancake_peg_def]
  |> translate;

Theorem parse_side_lemma:
  !x. parse_side x = T
Proof
  SIMP_TAC std_ss [fetch "-" "parse_side_def"]
  \\ rpt strip_tac
  \\ assume_tac PEG_wellformed
  \\ drule_then strip_assume_tac pegexecTheory.peg_exec_total
  \\ first_x_assum $ qspec_then `x` strip_assume_tac
  \\ pop_assum mp_tac
  \\ rewrite_tac [pegexecTheory.coreloop_def,
                  pegexecTheory.peg_exec_def, GSYM peg_pancake_rules_def,
                  parserProgTheory.INTRO_FLOOKUP]
  \\ simp [pancake_peg_def]
  \\ qmatch_goalsub_abbrev_tac ‘OWHILE _ f2’ \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘OWHILE _ g2’
  \\ gvs [AllCaseEqs()]
  \\ qsuff_tac ‘f2 = g2’ >- (strip_tac \\ gvs [])
  \\ unabbrev_all_tac
  \\ rpt $ pop_assum kall_tac
  \\ simp [pancake_peg_def, SF ETA_ss]
QED

val _ = update_precondition parse_side_lemma;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);
