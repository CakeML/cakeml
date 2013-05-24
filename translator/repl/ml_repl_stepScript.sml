
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

val OPTION_BIND_THM = prove(
  ``!x y. OPTION_BIND x y = case x of NONE => NONE | SOME i => y i``,
  Cases THEN SRW_TAC [] []);

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


(* type inference *)

val PRECONDITION_INTRO = prove(
  ``(b ==> (x = y)) ==> (x = if PRECONDITION b then y else x)``,
  Cases_on `b` THEN SIMP_TAC std_ss [PRECONDITION_def]);

val vwalk_ind = store_thm("vwalk_ind",
  ``!P.
      (!s v.
        (!v1 u. FLOOKUP s v = SOME v1 /\ v1 = Var u ==> P s u) ==>
        P s v) ==>
      (!s v. wfs s ==> P s v)``,
  NTAC 3 STRIP_TAC
  THEN Cases_on `wfs s` THEN FULL_SIMP_TAC std_ss []
  THEN HO_MATCH_MP_TAC (walkTheory.vwalk_ind |> Q.SPEC `P (s:'a subst)`
       |> DISCH_ALL |> RW [AND_IMP_INTRO])
  THEN FULL_SIMP_TAC std_ss []);

val res = translate
  (walkTheory.vwalk_def
    |> SIMP_RULE std_ss [PULL_FORALL] |> SPEC_ALL
    |> MATCH_MP PRECONDITION_INTRO);

val vwalk_side_def = store_thm("vwalk_side_def",
  ``!s v. vwalk_side s v <=> wfs s``,
  STRIP_TAC THEN Cases_on `wfs s` THEN FULL_SIMP_TAC std_ss []
  THEN1 (IMP_RES_TAC (walkTheory.vwalk_ind |> DISCH_ALL)
         THEN POP_ASSUM HO_MATCH_MP_TAC THEN REPEAT STRIP_TAC
         THEN ONCE_REWRITE_TAC [fetch "-" "vwalk_side_cases"]
         THEN FULL_SIMP_TAC std_ss [PULL_FORALL])
  THEN ONCE_REWRITE_TAC [fetch "-" "vwalk_side_cases"]
  THEN FULL_SIMP_TAC std_ss [])
  |> update_precondition;

val res = translate (def_of_const ``walk``)

val oc_ind = store_thm("oc_ind",
  ``!P.
      (!s t v.
        (!t1 t2. walk s t = Pair t1 t2 ==> P s t1 v /\ P s t2 v) ==>
        P s t v) ==>
      (!s t v. wfs s ==> P (s:'a subst) (t:'a term) (v:num))``,
  REPEAT STRIP_TAC THEN Q.SPEC_TAC (`t`,`t`)
  THEN HO_MATCH_MP_TAC walkstarTheory.walkstar_ind
  THEN REPEAT STRIP_TAC THEN METIS_TAC []);

val res = translate
  (walkstarTheory.oc_walking |> MATCH_MP PRECONDITION_INTRO)

val oc_side_lemma = prove(
  ``!s t v. wfs s ==> wfs s ==> oc_side s t v``,
  HO_MATCH_MP_TAC oc_ind THEN REPEAT STRIP_TAC
  THEN FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
  THEN ONCE_REWRITE_TAC [fetch "-" "oc_side_cases"]
  THEN ASM_SIMP_TAC std_ss [fetch "-" "walk_side_def",PULL_FORALL]
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
  |> SIMP_RULE std_ss [];

val oc_side_def = store_thm("oc_side_def",
  ``!s t v. oc_side s t v <=> wfs s``,
  STRIP_TAC THEN Cases_on `wfs s` THEN FULL_SIMP_TAC std_ss [oc_side_lemma]
  THEN ONCE_REWRITE_TAC [fetch "-" "oc_side_cases"]
  THEN FULL_SIMP_TAC std_ss [])
  |> update_precondition;

val unify_ind = store_thm("unify_ind",
  ``!P.
     (!s t1 t2.
        (!t1a t1d t2a t2d sx.
           walk s t1 = Pair t1a t1d /\ walk s t2 = Pair t2a t2d /\
           unify s t1a t2a = SOME sx ==>
           P sx t1d t2d) /\
        (!t1a t1d t2a t2d.
           walk s t1 = Pair t1a t1d /\ walk s t2 = Pair t2a t2d ==>
           P s t1a t2a) ==>
        P s t1 t2) ==>
     !s t1 t2. wfs s ==> P s t1 t2``,
  NTAC 2 STRIP_TAC THEN HO_MATCH_MP_TAC unifDefTheory.unify_ind
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss []
  THEN Q.PAT_ASSUM `!s1 t1 t2. bbb ==> bbbb` MATCH_MP_TAC
  THEN REPEAT STRIP_TAC
  THEN METIS_TAC [unifDefTheory.unify_uP |> RW [def_of_const ``uP``]]);

val res = translate
  (def_of_const ``unify``
    |> SIMP_RULE std_ss [OPTION_BIND_THM, def_of_const ``ext_s_check``]
    |> SPEC_ALL |> MATCH_MP PRECONDITION_INTRO)

val unify_side_lemma = prove(
  ``!s t v. wfs s ==> wfs s ==> unify_side s t v``,
  HO_MATCH_MP_TAC unify_ind THEN REPEAT STRIP_TAC
  THEN FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
  THEN ONCE_REWRITE_TAC [fetch "-" "unify_side_cases"]
  THEN ASM_SIMP_TAC std_ss [fetch "-" "walk_side_def",PULL_FORALL]
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []
  THEN METIS_TAC [unifDefTheory.unify_uP |> RW [def_of_const ``uP``]])
  |> SIMP_RULE std_ss [];

val unify_side_def = store_thm("unify_side_def",
  ``!s t v. unify_side s t v <=> wfs s``,
  STRIP_TAC THEN Cases_on `wfs s` THEN FULL_SIMP_TAC std_ss [unify_side_lemma]
  THEN ONCE_REWRITE_TAC [fetch "-" "unify_side_cases"]
  THEN FULL_SIMP_TAC std_ss [])
  |> update_precondition;

val _ = export_theory();
