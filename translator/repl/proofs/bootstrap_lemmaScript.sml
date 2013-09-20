
open HolKernel Parse boolLib bossLib;

val _ = new_theory "bootstrap_lemma";

open ml_translatorTheory;
open AstTheory LibTheory AltBigStepTheory SemanticPrimitivesTheory;
open terminationTheory;
open bigBigEquivTheory;
open arithmeticTheory listTheory combinTheory pairTheory;
open integerTheory;
open lcsymtacs;

infix \\ val op \\ = op THEN;

val fname = ``"parse_elaborate_infertype_compile"``
val a = ``a:'a -> v -> bool``
val b = ``b:'b -> v -> bool``
val exp = ``(App Opapp (Var (Short ^fname)) (Var (Short "input"))):exp``
val decls = ``ds:decs``

val lookup_APPEND = prove(
  ``!xs ys.
      lookup name (xs ++ ys) =
         case lookup name xs of
         | NONE => lookup name ys
         | res => res``,
  Induct \\ SRW_TAC [] [lookup_def]
  \\ Cases_on `h` \\ SRW_TAC [] [lookup_def]
  \\ METIS_TAC[alistTheory.ALOOKUP_APPEND]);

val lookup_IMP_APPEND = prove(
  ``!env rest.
      (lookup name env = SOME res) ==>
      (lookup name (env ++ rest) = SOME res)``,
  SIMP_TAC std_ss [lookup_APPEND]);

val Eval_Var_LOOKUP = prove(
  ``Eval env (Var (Short name)) P =
    ?v. (lookup name env = SOME v) /\ P v``,
  SIMP_TAC std_ss [Eval_def]
  \\ ONCE_REWRITE_TAC [evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) []);

val lemma = prove(
  ``(!env.
      DeclAssum ^decls env ==>
      Eval env (Var (Short "parse_elaborate_infertype_compile"))
        ((a --> b) f)) ==>
    Decls NONE [] init_envC empty_store [] ^decls cenv2 s2 env /\
    Decls NONE [] init_envC empty_store [("input",i)] ^decls cenv2 s2 env /\
    (lookup "input" env = NONE) /\
    ^a input i ==>
    ?env cenv2 s2.
      Decls NONE [] init_envC empty_store [("input",i)]
        (SNOC
          (Dlet (Pvar "it")
             (App Opapp (Var (Short "parse_elaborate_infertype_compile"))
                (Var (Short "input")))) ^decls) cenv2 s2 env /\
      Eval env (Var (Short "it")) (^b (f input))``,
  REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [SNOC_APPEND,Decls_APPEND,PULL_EXISTS]
  \\ SIMP_TAC std_ss [merge_def,APPEND_NIL]
  \\ Q.LIST_EXISTS_TAC [`s2`,`cenv2`,`s2`,`env`]
  \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [Decls_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_decs'_cases]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_decs'_cases,PULL_EXISTS]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_dec'_cases,PULL_EXISTS]
  \\ SIMP_TAC (srw_ss()) [combine_dec_result_def,pmatch'_def,pat_bindings_def]
  \\ SIMP_TAC (srw_ss()) [merge_def,bind_def,emp_def,APPEND]
  \\ SIMP_TAC std_ss [Eval_Var_SIMP]
  \\ SUFF_TAC ``Eval (env ++ [("input",i)]) ^exp (^b (f input))`` THEN1
   (SIMP_TAC std_ss [Eval_def] \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `res` \\ IMP_RES_TAC evaluate'_empty_store_IMP
    \\ FULL_SIMP_TAC std_ss [])
  \\ MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] Eval_Arrow)
  \\ REPEAT STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [DeclAssum_def,PULL_EXISTS]
    \\ RES_TAC \\ POP_ASSUM MP_TAC
    \\ SIMP_TAC std_ss [Eval_def]
    \\ ONCE_REWRITE_TAC [evaluate'_cases]
    \\ SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC lookup_IMP_APPEND
    \\ IMP_RES_TAC alistTheory.ALOOKUP_prefix
    \\ FULL_SIMP_TAC std_ss [])
  \\ SIMP_TAC std_ss [Eval_def]
  \\ ONCE_REWRITE_TAC [evaluate'_cases]
  \\ SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `i` \\ FULL_SIMP_TAC std_ss [lookup_APPEND] \\ EVAL_TAC)
  |> UNDISCH_ALL
  |> SIMP_RULE std_ss [Eval_Var_LOOKUP,PULL_EXISTS]
  |> SIMP_RULE std_ss [Decls_def]

val _ = save_thm("bootstrap_lemma1",lemma);
val _ = save_thm("bootstrap_lemma2",eval_decs'_to_eval_decs_simple_pat);

val _ = export_theory();
