open HolKernel boolLib bossLib lcsymtacs listTheory pred_setTheory compilerTheory
open HolKernel terminationTheory compilerTerminationTheory ml_translatorLib

val _ = new_theory"ml_compiler"

(* translator setup *)

val _ = translate_into_module "REPL";

val _ = std_preludeLib.std_prelude ();

val _ = add_preferred_thy "-";
val _ = add_preferred_thy "termination";
val _ = add_preferred_thy "compilerTermination";

val NOT_NIL_AND_LEMMA = prove(
  ``(b <> [] /\ x) = if b = [] then F else x``,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy "compilerTermination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW [MEMBER_INTRO,MAP]
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> RW [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

(* compiler *)

val _ = translate (def_of_const ``stackshift``);

val _ = rich_listTheory.BUTLASTN_REVERSE |> Q.SPECL [`n`,`REVERSE l`]
  |> REWRITE_RULE [REVERSE_REVERSE,LENGTH_REVERSE] |> UNDISCH
  |> translate

val butlastn_side_def = prove(
  ``!n l. butlastn_side n l = (n <= LENGTH l)``,
  SIMP_TAC std_ss [fetch "-" "butlastn_side_def"])
  |> update_precondition;

val _ = translate finite_mapTheory.FUPDATE_LIST_THM;

val option_CASE_thm = prove(
  ``option_CASE x f g = case x of NONE => f | SOME y => g y``,
  CONV_TAC (DEPTH_CONV ETA_CONV) THEN SIMP_TAC std_ss []);

val _ = translate (def_of_const ``build_exh_env``
                   |> ONCE_REWRITE_RULE [option_CASE_thm] |> RW [I_THM])

val NEQ_El_pat = prove(
  ``(!n. uop <> El_pat n) = case uop of El_pat n => F | _ => T``,
  Cases_on `uop` THEN SRW_TAC [] []);

val _ = translate (patLangTheory.fo_pat_def |> RW [NEQ_El_pat]);
val _ = translate patLangTheory.pure_pat_def;

val _ = register_type ``:bc_inst``;

val compile_thm =
  compilerTerminationTheory.compile_def
  |> SIMP_RULE std_ss [o_DEF,stringTheory.IMPLODE_EXPLODE_I];

val _ = translate compile_thm;

(* because the original theorems have termination side-conditions *)
val _ = save_thm("inf_type_to_string_ind",inferTheory.inf_type_to_string_ind)
val _ = translate inferTheory.inf_type_to_string_def;

val _ = translate compile_top_def;

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory()
