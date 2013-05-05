
open HolKernel Parse boolLib bossLib; val _ = new_theory "BankersQueue";

open listTheory arithmeticTheory ml_translatorLib mini_preludeTheory listLib;

val _ = translation_extends "mini_prelude";

(* implementation *)

val _ = Hol_datatype `queue = QUEUE of num => 'a list => num => 'a list`;

val empty_def = mlDefine `empty = QUEUE 0 [] 0 []`;

val is_empty_def = mlDefine `
  is_empty (QUEUE lenf _ _ _) = (lenf = 0)`;

val checkf_def = mlDefine `
  checkf (QUEUE lenf f lenr r) =
    if lenr <= lenf then QUEUE lenf f lenr r
                    else QUEUE (lenf + lenr) (f ++ REVERSE r) 0 []`;

val snoc_def = mlDefine `
  snoc (QUEUE lenf f lenr r) x = checkf (QUEUE lenf f (lenr+1) (x::r))`;

val head_def = mlDefine `
  head (QUEUE lenf (x::xs) lenr r) = x`;

val tail_def = mlDefine `
  tail (QUEUE lenf (x::xs) lenr r) = checkf (QUEUE (lenf-1) xs lenr r)`;

(* verification proof *)

val queue_inv_def = Define `
  queue_inv q (QUEUE lenf f lenr r) <=>
    (q = f ++ REVERSE r) /\ (lenr = LENGTH r) /\
    (lenf = LENGTH f) /\ lenr <= lenf`;

val empty_thm = prove(
  ``!xs. queue_inv xs empty = (xs = [])``,
  EVAL_TAC THEN SIMP_TAC std_ss []);

val is_empty_thm = prove(
  ``!q xs. queue_inv xs q ==> (is_empty q = (xs = []))``,
  Cases THEN Cases_on `l` THEN EVAL_TAC THEN SRW_TAC [] []
  THEN FULL_SIMP_TAC std_ss [REVERSE_DEF,LENGTH_NIL,REV_DEF]);

val snoc_thm = prove(
  ``!q xs x. queue_inv xs q ==> queue_inv (xs ++ [x]) (snoc q x)``,
  Cases THEN Cases_on `l` THEN1
   (EVAL_TAC THEN SRW_TAC [] []
    THEN FULL_SIMP_TAC std_ss [LENGTH_NIL,REV_DEF,APPEND,LENGTH] THEN EVAL_TAC)
  THEN FULL_SIMP_TAC std_ss [queue_inv_def,snoc_def,checkf_def]
  THEN SRW_TAC [] [queue_inv_def] THEN DECIDE_TAC);

val head_thm = prove(
  ``!q x xs. queue_inv (x::xs) q ==> (head q = x)``,
  Cases THEN Cases_on `l` THEN EVAL_TAC THEN SRW_TAC [] []
  THEN FULL_SIMP_TAC (srw_ss()) [REVERSE_DEF,LENGTH_NIL,REV_DEF]);

val tail_thm = prove(
  ``!q x xs. queue_inv (x::xs) q ==> queue_inv xs (tail q)``,
  Cases THEN Cases_on `l` THEN1
   (FULL_SIMP_TAC std_ss [queue_inv_def,APPEND,tail_def]
    THEN Cases_on `l0` THEN FULL_SIMP_TAC (srw_ss()) []
    THEN REPEAT STRIP_TAC THEN `F` by DECIDE_TAC)
  THEN FULL_SIMP_TAC std_ss [queue_inv_def,APPEND,tail_def]
  THEN Cases_on `l0` THEN FULL_SIMP_TAC (srw_ss()) [queue_inv_def,checkf_def]
  THEN SRW_TAC [] [queue_inv_def] THEN DECIDE_TAC);

val _ = export_theory();
