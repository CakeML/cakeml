
open HolKernel Parse boolLib bossLib; val _ = new_theory "PhysicistsQueue";

open listTheory arithmeticTheory ml_translatorLib mini_preludeTheory;

val _ = translation_extends "mini_prelude";

(* implementation *)

val _ = Hol_datatype `queue = QUEUE of 'a list => num => 'a list => num => 'a list`;

val empty_def = mlDefine `
  empty = QUEUE [] 0 [] 0 []`;

val is_empty_def = mlDefine `
  is_empty (QUEUE _ lenf _ _ _) = (lenf = 0)`;

val checkw_def = mlDefine `
  (checkw (QUEUE [] lenf f lenr r) = QUEUE f lenf f lenr r) /\
  (checkw q = q)`;

val check_def = mlDefine `
  check (QUEUE w lenf f lenr r) =
    if lenr <= lenf
      then checkw (QUEUE w lenf f lenr r)
      else checkw (QUEUE f (lenf + lenr) (f ++ REVERSE r) 0 [])`;

val snoc_def = mlDefine `
  snoc (QUEUE w lenf f lenr r) x =
    check (QUEUE w lenf f (lenr+1) (x::r))`;

val head_def = mlDefine `
  head (QUEUE (x::xs) lenf f lenr r) = x`;

val tail_def = mlDefine `
  tail (QUEUE (x::xs) lenf f lenr r) = check (QUEUE xs (lenf-1) (TL f) lenr r)`;

(* verification proof *)

val queue_inv_def = Define `
  queue_inv q (QUEUE w lenf f lenr r) <=>
    (q = f ++ REVERSE r) /\ (lenr = LENGTH r) /\ (lenf = LENGTH f) /\
    lenr <= lenf /\ ((w = []) ==> (q = [])) /\ isPREFIX w f`;

val empty_thm = prove(
  ``!xs. queue_inv xs empty = (xs = [])``,
  EVAL_TAC THEN SIMP_TAC std_ss []);

val is_empty_thm = prove(
  ``!q xs. queue_inv xs q ==> (is_empty q = (xs = []))``,
  Cases THEN Cases_on `l` THEN EVAL_TAC THEN SRW_TAC [] []
  THEN Cases_on `l0` THEN FULL_SIMP_TAC (srw_ss()) [APPEND_eq_NIL,LENGTH_NIL]);

val isPREFIX_APPEND = prove(
  ``!xs ys. isPREFIX xs (xs ++ ys)``,
  Induct THEN FULL_SIMP_TAC (srw_ss()) [isPREFIX]);

val isPREFIX_REFL = prove(
  ``!xs ys. isPREFIX xs xs``,
  Induct THEN FULL_SIMP_TAC (srw_ss()) [isPREFIX]);

val snoc_thm = prove(
  ``!q xs x. queue_inv xs q ==> queue_inv (xs ++ [x]) (snoc q x)``,
  Cases THEN Cases_on `l`
  THEN FULL_SIMP_TAC (srw_ss()) [queue_inv_def,snoc_def,check_def,checkw_def]
  THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss())
    [queue_inv_def,snoc_def,check_def,checkw_def,ADD1]
  THEN Cases_on `l0` THEN FULL_SIMP_TAC (srw_ss())
    [queue_inv_def,snoc_def,check_def,checkw_def,ADD1]
  THEN FULL_SIMP_TAC std_ss [isPREFIX_APPEND,GSYM APPEND_ASSOC]
  THEN DECIDE_TAC);

val head_thm = prove(
  ``!q x xs. queue_inv (x::xs) q ==> (head q = x)``,
  Cases THEN Cases_on `l` THEN EVAL_TAC THEN SRW_TAC [] []
  THEN Cases_on `l0` THEN FULL_SIMP_TAC (srw_ss()) [REVERSE_DEF,LENGTH_NIL]);

val tail_thm = prove(
  ``!q x xs. queue_inv (x::xs) q ==> queue_inv xs (tail q)``,
  Cases THEN Cases_on `l`
  THEN FULL_SIMP_TAC (srw_ss()) [queue_inv_def,tail_def,check_def,checkw_def]
  THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss())
    [queue_inv_def,tail_def,check_def,checkw_def,ADD1] THEN Cases_on `l0`
  THEN FULL_SIMP_TAC (srw_ss()) [REVERSE_DEF,LENGTH_NIL,isPREFIX_REFL,checkw_def]
  THEN1 (Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL,checkw_def,queue_inv_def]
    THEN FULL_SIMP_TAC std_ss [queue_inv_def]
    THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss())
      [LENGTH_NIL,checkw_def,isPREFIX_REFL,isPREFIX_APPEND])
  THEN1 (Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL,checkw_def,queue_inv_def]
    THEN FULL_SIMP_TAC std_ss [queue_inv_def]
    THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss())
      [LENGTH_NIL,checkw_def,isPREFIX_REFL,isPREFIX_APPEND] THEN DECIDE_TAC));

val _ = export_theory();
