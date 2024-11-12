(*
  This is an example of applying the translator to the Real-Time
  Heap algorithm from Chris Okasaki's book.
*)
open HolKernel Parse boolLib bossLib; val _ = new_theory "RealTimeQueue";

open listTheory arithmeticTheory ml_translatorLib ListProgTheory;

val _ = translation_extends "ListProg";

(* implementation *)

Datatype:
  queue = QUEUE ('a list) ('a list) ('a list)
End

Definition empty_def:
  empty = QUEUE [] [] []
End
val r = translate empty_def;

Definition is_empty_def:
  (is_empty (QUEUE [] _ _) = T) /\
  (is_empty _ = F)
End
val r = translate is_empty_def;

Definition rotate_def:
  (rotate (QUEUE [] (y::_) a) = y::a) /\
  (rotate (QUEUE (x::xs) (y::ys) a) = x::rotate (QUEUE xs ys (y::a)))
End
val r = translate rotate_def;

Definition exec_def:
  (exec (QUEUE f r (x::s)) = QUEUE f r s) /\
  (exec (QUEUE f r []) = let f = rotate (QUEUE f r []) in QUEUE f [] f)
End
val r = translate exec_def;

Definition snoc_def:
  snoc (QUEUE f r s) x = exec (QUEUE f (x::r) s)
End
val r = translate snoc_def;

Definition head_def:
  head (QUEUE (x::f) r s) = x
End
val r = translate head_def;

Definition tail_def:
  tail (QUEUE (x::f) r s) = exec (QUEUE f r s)
End
val r = translate tail_def;

(* verification proof *)

Definition prop_def:
  prop d q (QUEUE f r s) <=>
    (q = f ++ REVERSE r) /\ (LENGTH s + LENGTH r = LENGTH f + d)
End

Definition queue_inv_def:
  queue_inv q (QUEUE f r s) <=> prop 0 q (QUEUE f r s)
End

Triviality empty_thm:
  !xs. queue_inv xs empty = (xs = [])
Proof
  EVAL_TAC THEN SIMP_TAC std_ss []
QED

Triviality is_empty_thm:
  !q xs. queue_inv xs q ==> (is_empty q = (xs = []))
Proof
  Cases THEN Cases_on `l`
  THEN SRW_TAC [] [LENGTH_NIL,queue_inv_def,is_empty_def,prop_def,LENGTH]
QED

Triviality rotate_thm:
  !f r s.
      (LENGTH r = LENGTH f + 1) ==>
      (rotate (QUEUE f r s) = f ++ REVERSE r ++ s)
Proof
  Induct
  THEN Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL,rotate_def]
  THEN Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL,rotate_def]
  THEN REPEAT STRIP_TAC
  THEN `LENGTH (h'::t') = LENGTH f + 1` by (EVAL_TAC THEN DECIDE_TAC)
  THEN FULL_SIMP_TAC std_ss [REVERSE_DEF,GSYM APPEND_ASSOC,APPEND]
QED

Triviality exec_thm:
  prop 1 xs (QUEUE f r s) ==>
    queue_inv xs (exec (QUEUE f r s))
Proof
  Cases_on `s` THEN FULL_SIMP_TAC (srw_ss())
    [rotate_thm,exec_def,LET_DEF,prop_def,queue_inv_def]
  THEN REPEAT STRIP_TAC THEN DECIDE_TAC
QED

Triviality snoc_thm:
  !q xs x. queue_inv xs q ==> queue_inv (xs ++ [x]) (snoc q x)
Proof
  Cases THEN FULL_SIMP_TAC (srw_ss())
    [rotate_thm,LET_DEF,prop_def,queue_inv_def,snoc_def]
  THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC exec_thm
  THEN FULL_SIMP_TAC (srw_ss()) [prop_def] THEN DECIDE_TAC
QED

Triviality head_thm:
  !q x xs. queue_inv (x::xs) q ==> (head q = x)
Proof
  Cases THEN Cases_on `l` THEN FULL_SIMP_TAC (srw_ss())
    [rotate_thm,LET_DEF,prop_def,queue_inv_def,head_def]
  THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL,REVERSE_DEF]
QED

Triviality tail_thm:
  !q x xs. queue_inv (x::xs) q ==> queue_inv xs (tail q)
Proof
  Cases THEN Cases_on `l` THEN FULL_SIMP_TAC (srw_ss())
    [rotate_thm,LET_DEF,prop_def,queue_inv_def,tail_def]
  THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL,REVERSE_DEF]
  THEN MATCH_MP_TAC exec_thm THEN EVAL_TAC THEN DECIDE_TAC
QED

val _ = export_theory();
