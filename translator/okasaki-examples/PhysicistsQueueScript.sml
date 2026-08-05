(*
  This is an example of applying the translator to the Physicists
  Heap algorithm from Chris Okasaki's book.
*)
Theory PhysicistsQueue
Ancestors
  list arithmetic ListProg
Libs
  ml_translatorLib

val _ = translation_extends "ListProg";

(* implementation *)

Datatype:
  queue = QUEUE ('a list) num ('a list) num ('a list)
End

Definition empty_def:
  empty = QUEUE [] 0 [] 0 []
End
val r = translate empty_def;

Definition is_empty_def:
  is_empty (QUEUE _ lenf _ _ _) = (lenf = 0)
End
val r = translate is_empty_def;

Definition checkw_def:
  (checkw (QUEUE [] lenf f lenr r) = QUEUE f lenf f lenr r) /\
  (checkw q = q)
End
val r = translate checkw_def;

Definition check_def:
  check (QUEUE w lenf f lenr r) =
    if lenr <= lenf
      then checkw (QUEUE w lenf f lenr r)
      else checkw (QUEUE f (lenf + lenr) (f ++ REVERSE r) 0 [])
End
val r = translate check_def;

Definition snoc_def:
  snoc (QUEUE w lenf f lenr r) x =
    check (QUEUE w lenf f (lenr+1) (x::r))
End
val r = translate snoc_def;

Definition head_def:
  head (QUEUE (x::xs) lenf f lenr r) = x
End
val r = translate head_def;

Definition tail_def:
  tail (QUEUE (x::xs) lenf f lenr r) = check (QUEUE xs (lenf-1) (TL f) lenr r)
End
val r = translate tail_def;

(* verification proof *)

Definition queue_inv_def:
  queue_inv q (QUEUE w lenf f lenr r) <=>
    (q = f ++ REVERSE r) /\ (lenr = LENGTH r) /\ (lenf = LENGTH f) /\
    lenr <= lenf /\ ((w = []) ==> (q = [])) /\ isPREFIX w f
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
  THEN Cases_on `l0` THEN FULL_SIMP_TAC (srw_ss()) [APPEND_eq_NIL,LENGTH_NIL]
QED

Theorem isPREFIX_APPEND[local]:
  !xs ys. isPREFIX xs (xs ++ ys)
Proof
  Induct THEN FULL_SIMP_TAC (srw_ss()) [isPREFIX]
QED

Theorem isPREFIX_REFL[local]:
  !xs ys. isPREFIX xs xs
Proof
  Induct THEN FULL_SIMP_TAC (srw_ss()) [isPREFIX]
QED

Theorem snoc_thm[local]:
  !q xs x. queue_inv xs q ==> queue_inv (xs ++ [x]) (snoc q x)
Proof
  Cases THEN Cases_on `l`
  THEN FULL_SIMP_TAC (srw_ss()) [queue_inv_def,snoc_def,check_def,checkw_def]
  THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss())
    [queue_inv_def,snoc_def,check_def,checkw_def,ADD1]
  THEN Cases_on `l0` THEN FULL_SIMP_TAC (srw_ss())
    [queue_inv_def,snoc_def,check_def,checkw_def,ADD1]
  THEN FULL_SIMP_TAC std_ss [isPREFIX_APPEND,GSYM APPEND_ASSOC]
  THEN DECIDE_TAC
QED

Theorem head_thm[local]:
  !q x xs. queue_inv (x::xs) q ==> (head q = x)
Proof
  Cases THEN Cases_on `l` THEN EVAL_TAC THEN SRW_TAC [] []
  THEN Cases_on `l0` THEN FULL_SIMP_TAC (srw_ss()) [REVERSE_DEF,LENGTH_NIL]
QED

Theorem tail_thm[local]:
  !q x xs. queue_inv (x::xs) q ==> queue_inv xs (tail q)
Proof
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
      [LENGTH_NIL,checkw_def,isPREFIX_REFL,isPREFIX_APPEND] THEN DECIDE_TAC)
QED

