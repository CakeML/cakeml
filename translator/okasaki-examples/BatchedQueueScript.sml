(*
  This is an example of applying the translator to the Batched Queue
  algorithm from Chris Okasaki's book.
*)
open HolKernel Parse boolLib bossLib;

open listTheory arithmeticTheory ml_translatorLib ListProgTheory;

val _ = set_grammar_ancestry ["list", "arithmetic", "ListProg"];

val _ = new_theory "BatchedQueue";

val _ = translation_extends "ListProg";

(* implementation *)

Datatype:
  queue = QUEUE ('a list) ('a list)
End

Definition empty_def:
  empty = QUEUE [] []
End
val r = translate empty_def;

Definition is_empty_def:
  (is_empty (QUEUE [] xs) = T) /\
  (is_empty _ = F)
End
val r = translate is_empty_def;

Definition checkf_def:
  (checkf (QUEUE [] xs) = QUEUE (REVERSE xs) []) /\
  (checkf q = q)
End
val r = translate checkf_def;

Definition snoc_def:
  snoc (QUEUE f r) x = checkf (QUEUE f (x::r))
End
val r = translate snoc_def;

Definition head_def:
  head (QUEUE (x::f) r) = x
End
val r = translate head_def;

Definition tail_def:
  tail (QUEUE (x::f) r) = checkf (QUEUE f r)
End
val r = translate tail_def;

(* verification proof *)

Definition queue_inv_def:
  queue_inv q (QUEUE xs ys) <=>
    (q = xs ++ REVERSE ys) /\ ((xs = []) ==> (ys = []))
End

Triviality empty_thm:
  !xs. queue_inv xs empty = (xs = [])
Proof
  EVAL_TAC THEN SIMP_TAC std_ss []
QED

Triviality is_empty_thm:
  !q xs. queue_inv xs q ==> (is_empty q = (xs = []))
Proof
  Cases THEN Cases_on `l` THEN EVAL_TAC THEN SRW_TAC [] [REV_DEF]
QED

Triviality snoc_thm:
  !q xs x. queue_inv xs q ==> queue_inv (xs ++ [x]) (snoc q x)
Proof
  Cases THEN Cases_on `l` THEN FULL_SIMP_TAC (srw_ss())
    [queue_inv_def,snoc_def,REVERSE_DEF,checkf_def,APPEND]
QED

Triviality head_thm:
  !q x xs. queue_inv (x::xs) q ==> (head q = x)
Proof
  Cases THEN Cases_on `l` THEN FULL_SIMP_TAC (srw_ss())
    [queue_inv_def,head_def,REVERSE_DEF,checkf_def,APPEND]
  THEN REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []
QED

Triviality tail_thm:
  !q x xs. queue_inv (x::xs) q ==> queue_inv xs (tail q)
Proof
  Cases THEN Cases_on `l` THEN EVAL_TAC THEN SRW_TAC [] []
  THEN TRY (Cases_on `t`) THEN EVAL_TAC
  THEN FULL_SIMP_TAC (srw_ss()) [REVERSE_DEF,REV_DEF]
QED

val _ = export_theory();
