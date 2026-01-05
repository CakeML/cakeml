(*
  This is an example of applying the translator to the Bankers Queue
  algorithm from Chris Okasaki's book.
*)
Theory BankersQueue
Ancestors
  list arithmetic ListProg
Libs
  ml_translatorLib listLib

val _ = translation_extends "ListProg";

(* implementation *)

Datatype:
  queue = QUEUE num ('a list) num ('a list)
End

Definition empty_def:
  empty = QUEUE 0 [] 0 []
End
val r = translate empty_def;

Definition is_empty_def:
  is_empty (QUEUE lenf _ _ _) = (lenf = 0)
End
val r = translate is_empty_def;

Definition checkf_def:
  checkf (QUEUE lenf f lenr r) =
    if lenr <= lenf then QUEUE lenf f lenr r
                    else QUEUE (lenf + lenr) (f ++ REVERSE r) 0 []
End
val r = translate checkf_def;

Definition snoc_def:
  snoc (QUEUE lenf f lenr r) x = checkf (QUEUE lenf f (lenr+1) (x::r))
End
val r = translate snoc_def;

Definition head_def:
  head (QUEUE lenf (x::xs) lenr r) = x
End
val r = translate head_def;

Definition tail_def:
  tail (QUEUE lenf (x::xs) lenr r) = checkf (QUEUE (lenf-1) xs lenr r)
End
val r = translate tail_def;

(* verification proof *)

Definition queue_inv_def:
  queue_inv q (QUEUE lenf f lenr r) <=>
    (q = f ++ REVERSE r) /\ (lenr = LENGTH r) /\
    (lenf = LENGTH f) /\ lenr <= lenf
End

Theorem empty_thm[local]:
  !xs. queue_inv xs empty = (xs = [])
Proof
  EVAL_TAC THEN SIMP_TAC std_ss []
QED

Theorem is_empty_thm[local]:
  !q xs. queue_inv xs q ==> (is_empty q = (xs = []))
Proof
  Cases THEN Cases_on `l` THEN EVAL_TAC THEN SRW_TAC [] []
  THEN FULL_SIMP_TAC std_ss [REVERSE_DEF,LENGTH_NIL,REV_DEF]
QED

Theorem snoc_thm[local]:
  !q xs x. queue_inv xs q ==> queue_inv (xs ++ [x]) (snoc q x)
Proof
  Cases THEN Cases_on `l` THEN1
   (EVAL_TAC THEN SRW_TAC [] []
    THEN FULL_SIMP_TAC std_ss [LENGTH_NIL,REV_DEF,APPEND,LENGTH] THEN EVAL_TAC)
  THEN FULL_SIMP_TAC std_ss [queue_inv_def,snoc_def,checkf_def]
  THEN SRW_TAC [] [queue_inv_def] THEN DECIDE_TAC
QED

Theorem head_thm[local]:
  !q x xs. queue_inv (x::xs) q ==> (head q = x)
Proof
  Cases THEN Cases_on `l` THEN EVAL_TAC THEN SRW_TAC [] []
  THEN FULL_SIMP_TAC (srw_ss()) [REVERSE_DEF,LENGTH_NIL,REV_DEF]
QED

Theorem tail_thm[local]:
  !q x xs. queue_inv (x::xs) q ==> queue_inv xs (tail q)
Proof
  Cases THEN Cases_on `l` THEN1
   (FULL_SIMP_TAC std_ss [queue_inv_def,APPEND,tail_def]
    THEN Cases_on `l0` THEN FULL_SIMP_TAC (srw_ss()) []
    THEN REPEAT STRIP_TAC THEN `F` by DECIDE_TAC)
  THEN FULL_SIMP_TAC std_ss [queue_inv_def,APPEND,tail_def]
  THEN Cases_on `l0` THEN FULL_SIMP_TAC (srw_ss()) [queue_inv_def,checkf_def]
  THEN SRW_TAC [] [queue_inv_def] THEN DECIDE_TAC
QED

