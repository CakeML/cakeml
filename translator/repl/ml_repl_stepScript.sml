
open HolKernel Parse boolLib bossLib;

val _ = new_theory "ml_repl_step";

open repl_funTheory CompilerTheory CompilerLibTheory;
open ToIntLangTheory ToBytecodeTheory terminationTheory ElabTheory;
open compilerTerminationTheory inferTheory CompilerPrimitivesTheory;
open BytecodeTheory mmlParseTheory mmlPEGTheory;

open arithmeticTheory listTheory finite_mapTheory pred_setTheory;
open ml_translatorLib ml_translatorTheory std_preludeTheory;


(* translator setup *)

val _ = translation_extends "std_prelude";

val _ = add_preferred_thy "-";
val _ = add_preferred_thy "termination";
val _ = add_preferred_thy "compilerTermination";

val NOT_NIL_AND_LEMMA = prove(
  ``(b <> [] /\ x) = if b = [] then F else x``,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val OPTION_BIND_THM = prove(
  ``!x y. OPTION_BIND x y = case x of NONE => NONE | SOME i => y i``,
  Cases THEN SRW_TAC [] []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
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
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> RW [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);


(* compiler *)

val fapply_thm = prove(
  ``fapply d x f = case FLOOKUP f x of NONE => d | SOME y => y``,
  SRW_TAC [] [fapply_def,FLOOKUP_DEF]);

val _ = translate fapply_thm;
val _ = translate compile_top_def;


(* elaborator *)

val _ = translate (def_of_const ``elab_top``);


(* parsing: peg_exec and mmlPEG *)

val _ = translate (def_of_const ``mmlPEG``);

val INTRO_FLOOKUP = prove(
  ``(if n IN FDOM G.rules
     then EV (G.rules ' n) i r y fk
     else Result NONE) =
    (case FLOOKUP G.rules n of
       NONE => Result NONE
     | SOME x => EV x i r y fk)``,
  SRW_TAC [] [finite_mapTheory.FLOOKUP_DEF]);

val _ = translate (def_of_const ``coreloop`` |> RW [INTRO_FLOOKUP]
                   |> SPEC_ALL |> RW1 [FUN_EQ_THM]);
val _ = translate (def_of_const ``peg_exec``);


(* parsing: mmlvalid *)

val LENGTH_LEMMA = prove(
  ``!l. ((LENGTH l = 1) ==> l <> []) /\
        ((LENGTH l = 2) ==> l <> [] /\ TL l <> [])``,
  Cases THEN FULL_SIMP_TAC std_ss [LENGTH]
  THEN Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [LENGTH]);

val if_and_lemma = METIS_PROVE []
  ``(if b1 /\ b2 then x else y) = if b1 then (if b2 then x else y) else y``

val monad_unitbind_assert = prove(
  ``!b x. monad_unitbind (assert b) x = if b then x else NONE``,
  Cases THEN EVAL_TAC THEN SIMP_TAC std_ss []);

val _ = translate (mmlvalidTheory.mml_okrule_eval_th
          |> RW [monad_unitbind_assert,NOT_NIL_AND_LEMMA,if_and_lemma])

val mml_okrule_side_def = prove(
  ``!x y. mml_okrule_side x y = T``,
  SIMP_TAC std_ss [fetch "-" "mml_okrule_side_def"]
  THEN FULL_SIMP_TAC std_ss [LENGTH_LEMMA]
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
  |> update_precondition;

val _ = translate grammarTheory.ptree_head_def

val res = translate
  (((mmlvalidTheory.mmlvalid_thm |> CONJUNCTS) @
    (mmlvalidTheory.mmlvalidL_def |> CONJUNCTS))
   |> map GEN_ALL |> LIST_CONJ)


(* parsing: ptree converstion *)

val _ = (extra_preprocessing :=
  [MEMBER_INTRO,MAP,OPTION_BIND_THM,monad_unitbind_assert]);

val _ = translate (def_of_const ``ptree_Expr``);
val _ = translate (def_of_const ``ptree_REPLTop``);


(* parsing: top-level parser *)

val _ = translate (RW [monad_unitbind_assert,mmlParseREPLTop_def] parse_top_def);

val parse_top_side_def = prove(
  ``!x. parse_top_side x = T``,
  SIMP_TAC std_ss [fetch "-" "parse_top_side_def",
    fetch "-" "peg_exec_side_def", fetch "-" "coreloop_side_def"]
  THEN REPEAT STRIP_TAC
  THEN STRIP_ASSUME_TAC (Q.SPEC `x` owhile_REPLTop_total)
  THEN FULL_SIMP_TAC std_ss [INTRO_FLOOKUP] THEN POP_ASSUM MP_TAC
  THEN CONV_TAC (DEPTH_CONV ETA_CONV) THEN FULL_SIMP_TAC std_ss [])
  |> update_precondition;


(* type inference: t_walkstar *)

val PRECONDITION_INTRO = prove(
  ``(b ==> (x = y)) ==> (x = if PRECONDITION b then y else x)``,
  Cases_on `b` THEN SIMP_TAC std_ss [PRECONDITION_def]);

val t_vwalk_ind = store_thm("t_vwalk_ind",
  ``!P.
      (!s v.
        (!v1 u. FLOOKUP s v = SOME v1 /\ v1 = Infer_Tuvar u ==> P s u) ==>
        P s v) ==>
      (!s v. t_wfs s ==> P s v)``,
  NTAC 3 STRIP_TAC
  THEN Cases_on `t_wfs s` THEN FULL_SIMP_TAC std_ss []
  THEN HO_MATCH_MP_TAC (unifyTheory.t_vwalk_ind |> Q.SPEC `P (s:num |-> infer_t)`
       |> DISCH_ALL |> RW [AND_IMP_INTRO])
  THEN FULL_SIMP_TAC std_ss []);

val _ = translate
  (unifyTheory.t_vwalk_eqn
    |> SIMP_RULE std_ss [PULL_FORALL] |> SPEC_ALL
    |> MATCH_MP PRECONDITION_INTRO);

val t_vwalk_side_def = store_thm("t_vwalk_side_def",
  ``!s v. t_vwalk_side s v <=> t_wfs s``,
  STRIP_TAC THEN REVERSE (Cases_on `t_wfs s`) THEN FULL_SIMP_TAC std_ss []
  THEN1 (ONCE_REWRITE_TAC [fetch "-" "t_vwalk_side_cases"]
         THEN FULL_SIMP_TAC std_ss [])
  THEN STRIP_TAC THEN POP_ASSUM (fn th => MP_TAC th THEN MP_TAC th)
  THEN Q.SPEC_TAC (`v`,`v`) THEN Q.SPEC_TAC (`s`,`s`)
  THEN HO_MATCH_MP_TAC t_vwalk_ind
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss []
  THEN ONCE_REWRITE_TAC [fetch "-" "t_vwalk_side_cases"]
  THEN FULL_SIMP_TAC std_ss [PULL_FORALL])
  |> update_precondition;

val _ = translate unifyTheory.t_walk_eqn;

val t_walkstar_ind = store_thm("t_walkstar_ind",
  ``!P.
      (!s t.
         (!ts tc0 a. t_walk s t = Infer_Tapp ts tc0 /\ MEM a ts ==> P s a) ==>
         P s t) ==>
      !s t. t_wfs s ==> P s t``,
  METIS_TAC [unifyTheory.t_walkstar_ind]);

val expand_lemma = prove(
  ``t_walkstar s = \x. t_walkstar s x``,
  SIMP_TAC std_ss [FUN_EQ_THM]);

val _ = translate
  (unifyTheory.t_walkstar_eqn
    |> RW1 [expand_lemma] |> SIMP_RULE std_ss [PULL_FORALL]
    |> SPEC_ALL |> MATCH_MP PRECONDITION_INTRO)

val t_walkstar_side_def = store_thm("t_walkstar_side_def",
  ``!s v. t_walkstar_side s v <=> t_wfs s``,
  STRIP_TAC THEN REVERSE (Cases_on `t_wfs s`) THEN FULL_SIMP_TAC std_ss []
  THEN1 (ONCE_REWRITE_TAC [fetch "-" "t_walkstar_side_cases"]
         THEN FULL_SIMP_TAC std_ss [])
  THEN STRIP_TAC THEN POP_ASSUM (fn th => MP_TAC th THEN MP_TAC th)
  THEN Q.SPEC_TAC (`v`,`v`) THEN Q.SPEC_TAC (`s`,`s`)
  THEN HO_MATCH_MP_TAC t_walkstar_ind THEN REPEAT STRIP_TAC
  THEN ONCE_REWRITE_TAC [fetch "-" "t_walkstar_side_cases"]
  THEN FULL_SIMP_TAC std_ss [fetch "-" "t_walk_side_def"]
  THEN METIS_TAC [])
  |> update_precondition;


val _ = export_theory();
