
open HolKernel Parse boolLib bossLib; val _ = new_theory "RealTimeQueue";

open listTheory arithmeticTheory ml_translatorLib mini_preludeTheory;

val _ = translation_extends "mini_prelude";

(* implementation *)

val _ = Hol_datatype `queue = QUEUE of 'a list => 'a list => 'a list`;

val empty_def = mlDefine `
  empty = QUEUE [] [] []`;

val is_empty_def = mlDefine `
  (is_empty (QUEUE [] _ _) = T) /\
  (is_empty _ = F)`;

val rotate_def = mlDefine `
  (rotate (QUEUE [] (y::_) a) = y::a) /\
  (rotate (QUEUE (x::xs) (y::ys) a) = x::rotate (QUEUE xs ys (y::a)))`

val exec_def = mlDefine `
  (exec (QUEUE f r (x::s)) = QUEUE f r s) /\
  (exec (QUEUE f r []) = let f = rotate (QUEUE f r []) in QUEUE f [] f)`

val snoc_def = mlDefine `
  snoc (QUEUE f r s) x = exec (QUEUE f (x::r) s)`;

val head_def = mlDefine `
  head (QUEUE (x::f) r s) = x`;

val tail_def = mlDefine `
  tail (QUEUE (x::f) r s) = exec (QUEUE f r s)`;

(* verification proof *)

val prop_def = Define `
  prop d q (QUEUE f r s) =
    (q = f ++ REVERSE r) /\ (LENGTH s + LENGTH r = LENGTH f + d)`

val queue_inv_def = Define `
  queue_inv q (QUEUE f r s) = prop 0 q (QUEUE f r s)`

val empty_thm = prove(
  ``!xs. queue_inv xs empty = (xs = [])``,
  EVAL_TAC THEN SIMP_TAC std_ss []);

val is_empty_thm = prove(
  ``!q xs. queue_inv xs q ==> (is_empty q = (xs = []))``,
  Cases THEN Cases_on `l`
  THEN SRW_TAC [] [LENGTH_NIL,queue_inv_def,is_empty_def,prop_def,LENGTH]);

val rotate_thm = prove(
  ``!f r s.
      (LENGTH r = LENGTH f + 1) ==>
      (rotate (QUEUE f r s) = f ++ REVERSE r ++ s)``,
  Induct
  THEN Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL,rotate_def]
  THEN Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL,rotate_def]
  THEN REPEAT STRIP_TAC THEN1 `F` by DECIDE_TAC
  THEN `LENGTH (h'::t') = LENGTH f + 1` by (EVAL_TAC THEN DECIDE_TAC)
  THEN FULL_SIMP_TAC std_ss [REVERSE_DEF,GSYM APPEND_ASSOC,APPEND]);

val exec_thm = prove(
  ``prop 1 xs (QUEUE f r s) ==>
    queue_inv xs (exec (QUEUE f r s))``,
  Cases_on `s` THEN FULL_SIMP_TAC (srw_ss())
    [rotate_thm,exec_def,LET_DEF,prop_def,queue_inv_def]
  THEN REPEAT STRIP_TAC THEN DECIDE_TAC);

val snoc_thm = prove(
  ``!q xs x. queue_inv xs q ==> queue_inv (xs ++ [x]) (snoc q x)``,
  Cases THEN FULL_SIMP_TAC (srw_ss())
    [rotate_thm,LET_DEF,prop_def,queue_inv_def,snoc_def]
  THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC exec_thm
  THEN FULL_SIMP_TAC (srw_ss()) [prop_def] THEN DECIDE_TAC);

val head_thm = prove(
  ``!q x xs. queue_inv (x::xs) q ==> (head q = x)``,
  Cases THEN Cases_on `l` THEN FULL_SIMP_TAC (srw_ss())
    [rotate_thm,LET_DEF,prop_def,queue_inv_def,head_def]
  THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL,REVERSE_DEF]);

val tail_thm = prove(
  ``!q x xs. queue_inv (x::xs) q ==> queue_inv xs (tail q)``,
  Cases THEN Cases_on `l` THEN FULL_SIMP_TAC (srw_ss())
    [rotate_thm,LET_DEF,prop_def,queue_inv_def,tail_def]
  THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL,REVERSE_DEF]
  THEN MATCH_MP_TAC exec_thm THEN EVAL_TAC THEN DECIDE_TAC);

val _ = export_theory();
