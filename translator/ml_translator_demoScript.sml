open HolKernel Parse boolLib bossLib; val _ = new_theory "ml_translator_demo";

open arithmeticTheory listTheory combinTheory pairTheory;
open ml_translatorLib ml_translatorTheory;


(* qsort translation *)

val res = translate listTheory.APPEND;
val res = translate sortingTheory.PART_DEF;
val res = translate sortingTheory.PARTITION_DEF;
val res = translate sortingTheory.QSORT_DEF;

val _ = finalise_translation ();

(* using the certificte theorem *)

val (qsort_eval,_) = get_cert "QSORT"

val Eval_Var_lemma = prove(
  ``Eval env (Var name) P = ?x. (lookup name env = SOME x) /\ P x``,
  SIMP_TAC (srw_ss()) [Eval_def,Once MiniMLTheory.evaluate'_cases]);

val Eval_QSORT_EXPANDED = save_thm("Eval_QSORT_EXPANDED",let
  val th = MATCH_MP Eval_Arrow qsort_eval
  val th1 = ASSUME ``Eval env (Var "R") ((a --> a --> BOOL) R)``
  val th = MATCH_MP th th1
  val th = MATCH_MP Eval_Arrow th
  val th1 = ASSUME ``Eval env (Var "xs") ((LIST_TYPE a) xs)``
  val th = MATCH_MP th th1
  val th = REWRITE_RULE [Eval_def] th
  val th = DISCH_ALL th
  val th = SIMP_RULE std_ss [Eval_Var_lemma] th
  val th = SIMP_RULE std_ss [PULL_EXISTS,PULL_FORALL] th
  in th end)

val ML_QSORT_CORRECT = store_thm ("ML_QSORT_CORRECT",
  ``!env a ord R l xs.
      DeclAssum ml_translator_demo_decls env /\
      LIST_TYPE a l xs /\ (lookup "xs" env = SOME xs) /\
      (a --> a --> BOOL) ord R /\ (lookup "R" env = SOME R) /\
      transitive ord /\ total ord
      ==>
      ?l' xs'.
        evaluate' empty_store env
            (App Opapp (App Opapp (Var "QSORT") (Var "R")) (Var "xs"))
            (empty_store,Rval xs') /\
        (LIST_TYPE a l' xs') /\ PERM l l' /\ SORTED ord l'``,
  REPEAT STRIP_TAC THEN IMP_RES_TAC Eval_QSORT_EXPANDED
  THEN METIS_TAC [sortingTheory.QSORT_PERM,sortingTheory.QSORT_SORTED]);


val _ = export_theory();

