
open HolKernel Parse boolLib bossLib;

val _ = new_theory "ml_repl_step";

open repl_funTheory CompilerTheory CompilerLibTheory;
open ToIntLangTheory ToBytecodeTheory terminationTheory ElabTheory;
open compilerTerminationTheory inferTheory CompilerPrimitivesTheory;
open BytecodeTheory mmlParseTheory mmlPEGTheory;

open arithmeticTheory listTheory finite_mapTheory pred_setTheory;
open ml_translatorLib ml_translatorTheory std_preludeTheory;

val _ = translation_extends "std_prelude";

(* translator setup *)

val lemma = prove(
  ``(b <> [] /\ x) = if b = [] then F else x``,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

fun def_of_const tm = let
  val res = dest_thy_const tm
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy "compilerTermination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW [MEMBER_INTRO,MAP]
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY] |> RW [lemma]
  in def end

val _ = (find_def_for_const := def_of_const);

(* compiler *)

val _ = register_type ``:bc_inst``;

val fapply_thm = prove(
  ``fapply d x f = case FLOOKUP f x of NONE => d | SOME y => y``,
  SRW_TAC [] [fapply_def,FLOOKUP_DEF]);

val _ = translate fapply_thm;
val _ = translate compile_dec_def;
(* val _ = translate compile_top_def; *)

(* parser *)

val _ = (find_def_for_const := (fn _ => fail()));

val _ = translate FUPDATE_LIST;
val _ = translate (def_of_const ``pnt``);
val _ = translate (def_of_const ``sumID``);
val _ = translate (def_of_const ``bindNT``);
val _ = translate (def_of_const ``mktokLf``);
val _ = translate (def_of_const ``destSymbolT``);
val _ = translate (def_of_const ``destAlphaT``);
val _ = translate (def_of_const ``OPTION_BIND``);
val _ = translate (def_of_const ``isUpper``);
val _ = translate (def_of_const ``assert``);
val _ = translate (def_of_const ``peg_V``);
val _ = translate (def_of_const ``pegf``);
val _ = translate (def_of_const ``seql``);
val _ = translate (def_of_const ``destLongidT``);
val _ = translate (def_of_const ``isLower``);
val _ = translate (def_of_const ``isAlpha``);
val _ = translate (def_of_const ``peg_longV``);
val _ = translate (def_of_const ``peg_Eapp``);
val _ = translate (def_of_const ``tokeq``);
val _ = translate (def_of_const ``isInt``);
val _ = translate (def_of_const ``isLongidT``);
val _ = translate (def_of_const ``isTyvarT``);
val _ = translate (def_of_const ``choicel``);
val _ = translate (def_of_const ``mk_linfix``);
val _ = translate (def_of_const ``peg_linfix``);
val _ = translate (def_of_const ``peg_nonfix``);
val _ = translate (def_of_const ``try``);
val _ = translate (def_of_const ``peg_Type``);
val _ = translate (def_of_const ``mk_rinfix``);
val _ = translate (def_of_const ``isAlphaSym``);
val _ = translate (def_of_const ``calcTyOp``);
val _ = translate (def_of_const ``peg_DType``);
val _ = translate (def_of_const ``peg_TypeName``);
val _ = translate (def_of_const ``peg_TypeDec``);
val _ = translate (def_of_const ``peg_UQConstructorName``);
val _ = translate (def_of_const ``mmlPEG``);

val _ = export_theory();
