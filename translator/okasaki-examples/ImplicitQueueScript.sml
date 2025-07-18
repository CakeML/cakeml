(*
  This is an example of applying the translator to the Implicit
  Queue algorithm from Chris Okasaki's book.
*)
open HolKernel Parse boolLib bossLib;

open listTheory arithmeticTheory ml_translatorLib ListProgTheory;

val _ = set_grammar_ancestry ["list", "arithmetic", "ListProg"];

val _ = new_theory "ImplicitQueue";

val _ = translation_extends "ListProg";

(* Okasaki page 174 *)

(* implementation *)

(* The following datatype is defined slightly differently from the one
   Okasaki defines. The definition Okasaki uses is not supported by
   HOL4's Hol_datatype function. *)

Datatype:
  times = Once 'a | Twice times times
End

Datatype:
  digit = Zero | One ('a times) | Two ('a times) ('a times)
End

Datatype:
  queue = Shallow ('a digit)
        | Deep ('a digit) queue ('a digit)
End

Definition empty_def:
  empty = Shallow Zero
End
val r = translate empty_def;

Definition is_empty_def:
  (is_empty (Shallow Zero) = T) /\
  (is_empty _ = F)
End
val r = translate is_empty_def;

Definition snoc_def:
  (snoc (Shallow Zero) y = Shallow (One y)) /\
  (snoc (Shallow (One x)) y = Deep (Two x y) empty Zero) /\
  (snoc (Deep f m Zero) y = Deep f m (One y)) /\
  (snoc (Deep f m (One x)) y = Deep f (snoc m (Twice x y)) Zero)
End
val r = translate snoc_def;

Definition head_def:
  (head (Shallow (One x)) = x) /\
  (head (Deep (One x) m r) = x) /\
  (head (Deep (Two x y) m r) = x)
End
val r = translate head_def;

Definition tail_def:
  (tail (Shallow (One x)) = empty) /\
  (tail (Deep (Two x y) m r) = Deep (One y) m r) /\
  (tail (Deep (One x) q r) =
     if is_empty q then Shallow r else
       case head q of Twice y z => Deep (Two y z) (tail q) r)
End
val r = translate tail_def;

(* verification *)

Definition exps_def:
  (exps (Once x) = [x]) /\
  (exps (Twice t1 t2) = exps t1 ++ exps t2)
End

Definition digits_def:
  (digits Zero = []) /\
  (digits (One x) = exps x) /\
  (digits (Two x y) = exps x ++ exps y)
End

Definition flatten_def:
  (flatten (Shallow x) = digits x) /\
  (flatten (Deep d1 t d2) = digits d1 ++ flatten t ++ digits d2)
End

Definition only_digits_def:
  (only_digits Zero = []) /\
  (only_digits (One x) = [x]) /\
  (only_digits (Two x y) = [x;y])
End

Definition depth_def:
  (depth n (Once x) <=> (n = 0:num)) /\
  (depth n (Twice t1 t2) <=> ~(n = 0) /\ depth (n-1) t1 /\ depth (n-1) t2)
End

Definition ddepth_def:
  ddepth n d = EVERY (\d. depth n d) (only_digits d)
End

Definition two_def:
  (two (Two _ _) = T) /\ (two _ = F)
End

Definition queue_ok_def:
  (queue_ok n (Shallow x) <=> ~two x /\ ddepth n x) /\
  (queue_ok n (Deep x1 t x2) <=>
     ~(x1 = Zero) /\ queue_ok (n+1) t /\ ~two x2 /\ ddepth n x1 /\ ddepth n x2)
End

Definition queue_inv_def:
  queue_inv q t <=> queue_ok 0 t /\ (q = flatten t)
End

Triviality empty_thm:
  queue_inv [] empty
Proof
  EVAL_TAC
QED

Triviality exps_NOT_NIL:
  !e. ~(exps e = [])
Proof
  Induct THEN EVAL_TAC THEN FULL_SIMP_TAC std_ss [APPEND_eq_NIL]
QED

Triviality is_empty_thm:
  !xs q. queue_inv xs q ==> (is_empty q = (xs = []))
Proof
  Cases THEN Cases THEN EVAL_TAC
  THEN1 (Cases_on `d` THEN EVAL_TAC THEN SIMP_TAC std_ss [exps_NOT_NIL])
  THEN1 (Cases_on `d0` THEN EVAL_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ]
         THEN SIMP_TAC std_ss [exps_NOT_NIL,APPEND_eq_NIL])
  THEN Cases_on `d` THEN EVAL_TAC
QED

Triviality flatten_snoc:
  !x y n. queue_ok n x ==> (flatten (snoc x y) = flatten x ++ exps y)
Proof
  Induct THEN Cases_on `d`
  THEN FULL_SIMP_TAC (srw_ss()) [snoc_def,flatten_def,digits_def,
      empty_def,queue_ok_def,two_def] THEN REPEAT STRIP_TAC
  THEN RES_TAC THEN FULL_SIMP_TAC std_ss [exps_def,APPEND_ASSOC]
QED

Triviality queue_ok_snoc:
  !q y n. queue_ok n q /\ depth n y ==> queue_ok n (snoc q y)
Proof
  Induct THEN Cases_on `d`
  THEN FULL_SIMP_TAC (srw_ss()) [snoc_def,queue_ok_def,ddepth_def,two_def,
    only_digits_def,EVERY_DEF,empty_def] THEN REPEAT STRIP_TAC
  THEN Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC
  THEN FULL_SIMP_TAC (srw_ss()) [depth_def]
QED

Triviality snoc_thm:
  !q xs x. queue_inv xs q ==> queue_inv (xs ++ [x]) (snoc q (Once x))
Proof
  STRIP_TAC THEN SIMP_TAC std_ss [queue_inv_def] THEN REPEAT STRIP_TAC
  THEN IMP_RES_TAC flatten_snoc THEN FULL_SIMP_TAC std_ss [exps_def]
  THEN MATCH_MP_TAC queue_ok_snoc THEN FULL_SIMP_TAC std_ss [] THEN EVAL_TAC
QED

Triviality depth_0:
  !e. depth 0 e ==> ?x. e = Once x
Proof
  Cases THEN SIMP_TAC (srw_ss()) [depth_def]
QED

Triviality head_thm:
  !q x xs. queue_inv (x::xs) q ==> (head q = Once x)
Proof
  Cases THEN TRY (Cases_on `d`) THEN TRY (Cases_on `d0`)
  THEN EVAL_TAC THEN SIMP_TAC (srw_ss()) []
  THEN REPEAT STRIP_TAC THEN IMP_RES_TAC depth_0
  THEN FULL_SIMP_TAC (srw_ss()) [exps_def]
QED

Triviality depth_IMP:
  !t n. depth n t ==> (LENGTH (exps t) = 2**n)
Proof
  Induct THEN1 (EVAL_TAC THEN FULL_SIMP_TAC std_ss [])
  THEN Cases THEN FULL_SIMP_TAC std_ss [depth_def,ADD1]
  THEN REPEAT STRIP_TAC THEN RES_TAC
  THEN FULL_SIMP_TAC (srw_ss()) [exps_def,GSYM ADD1,EXP] THEN DECIDE_TAC
QED

Triviality LENGTH_EQ_APPEND_EQ:
  !xs xs2 ys ys2.
      (LENGTH xs = LENGTH ys) /\ (xs ++ xs2 = ys ++ ys2) ==> (xs2 = ys2)
Proof
  Induct THEN Cases_on `ys` THEN FULL_SIMP_TAC (srw_ss()) [ADD1]
QED

Triviality is_empty_EQ:
  !q. is_empty q = (q = Shallow Zero)
Proof
  Cases THEN Cases_on `d` THEN EVAL_TAC
QED

Triviality tail_lemma:
  !q n x xs.
      queue_ok n q /\ (exps x ++ xs = flatten q) /\ depth n x ==>
      queue_ok n (tail q) /\ (xs = flatten (tail q))
Proof
  Induct THEN1 (Cases_on `d`
    THEN FULL_SIMP_TAC (srw_ss()) [flatten_def,digits_def,exps_NOT_NIL,tail_def,
           queue_ok_def,empty_def,ddepth_def,EVERY_DEF,two_def,only_digits_def]
    THEN REPEAT STRIP_TAC THEN IMP_RES_TAC depth_IMP
    THEN Cases_on `xs` THEN FULL_SIMP_TAC std_ss []
    THEN Q.PAT_X_ASSUM `exps x ++ h::t' = exps t` (ASSUME_TAC o GSYM)
    THEN FULL_SIMP_TAC (srw_ss()) []
    THEN DECIDE_TAC)
  THEN REVERSE (Cases_on `d0`)
  THEN FULL_SIMP_TAC (srw_ss()) [flatten_def,digits_def,exps_NOT_NIL,tail_def,
           queue_ok_def,empty_def,ddepth_def,EVERY_DEF,two_def,only_digits_def]
  THEN1 (METIS_TAC [LENGTH_EQ_APPEND_EQ,APPEND_ASSOC,depth_IMP])
  THEN Cases_on `is_empty q` THEN FULL_SIMP_TAC std_ss []
  THEN1 (Cases_on `d` THEN FULL_SIMP_TAC (srw_ss()) [flatten_def,digits_def,
       exps_NOT_NIL,tail_def,queue_ok_def,empty_def,ddepth_def,
       EVERY_DEF,two_def,only_digits_def] THEN REPEAT STRIP_TAC
    THEN NTAC 2 (POP_ASSUM MP_TAC)
    THEN FULL_SIMP_TAC std_ss [is_empty_EQ,flatten_def,digits_def,APPEND_NIL]
    THEN REPEAT STRIP_TAC THEN METIS_TAC
      [LENGTH_EQ_APPEND_EQ,APPEND_ASSOC,depth_IMP,APPEND_NIL,APPEND_ASSOC])
  THEN NTAC 5 STRIP_TAC
  THEN Cases_on `head q` THEN1
   (POP_ASSUM MP_TAC
    THEN Cases_on `q` THEN FULL_SIMP_TAC std_ss [head_def]
    THEN Cases_on `d'` THEN TRY (Cases_on `d0`) THEN STRIP_TAC
    THEN FULL_SIMP_TAC std_ss [head_def,is_empty_def,queue_ok_def,
      ddepth_def,only_digits_def,EVERY_DEF,depth_def,two_def])
  THEN FULL_SIMP_TAC (srw_ss()) [flatten_def,queue_ok_def,ddepth_def,
         only_digits_def,digits_def]
  THEN `xs = flatten q ++ digits d` by METIS_TAC
    [LENGTH_EQ_APPEND_EQ,APPEND_ASSOC,depth_IMP,APPEND_NIL,APPEND_ASSOC]
  THEN FULL_SIMP_TAC (srw_ss()) []
  THEN sg `depth n t' ∧ depth n t0` THEN1
   (Cases_on `q` THEN FULL_SIMP_TAC std_ss [head_def]
    THEN Cases_on `d'` THEN TRY (Cases_on `d0`) THEN STRIP_TAC
    THEN FULL_SIMP_TAC std_ss [head_def,is_empty_def,queue_ok_def,
      ddepth_def,only_digits_def,EVERY_DEF,depth_def,two_def])
  THEN FULL_SIMP_TAC std_ss []
  THEN sg `?ts. flatten q = exps (head q) ++ ts` THEN1
   (Cases_on `q` THEN FULL_SIMP_TAC std_ss [is_empty_def] THEN1
     (Cases_on `d'` THEN FULL_SIMP_TAC std_ss [is_empty_def]
      THEN FULL_SIMP_TAC std_ss [head_def,is_empty_def,queue_ok_def,digits_def,
        ddepth_def,only_digits_def,EVERY_DEF,depth_def,two_def,flatten_def]
      THEN Q.EXISTS_TAC `[]` THEN FULL_SIMP_TAC (srw_ss()) [])
    THEN FULL_SIMP_TAC std_ss [exps_def,flatten_def]
    THEN Q.PAT_X_ASSUM `head xx = yy` MP_TAC
    THEN Q.PAT_X_ASSUM `queue_ok (n + 1) xx` MP_TAC THEN Cases_on `d0`
    THEN SIMP_TAC std_ss [head_def,is_empty_def,queue_ok_def,digits_def,exps_def,
      ddepth_def,only_digits_def,EVERY_DEF,depth_def,two_def,flatten_def,digits_def]
    THEN SIMP_TAC (srw_ss()) [digits_def,exps_def])
  THEN Q.PAT_X_ASSUM `!x.bbb` (MP_TAC o GSYM o Q.SPECL [`n+1`,`head q`,`ts`])
  THEN FULL_SIMP_TAC std_ss []
  THEN MATCH_MP_TAC (METIS_PROVE [] ``b /\ (b1 ==> b2) ==> (b ==> b1) ==> b2``)
  THEN FULL_SIMP_TAC std_ss [exps_def,depth_def]
QED

Triviality tail_thm:
  !q x xs. queue_inv (x::xs) q ==> queue_inv xs (tail q)
Proof
  FULL_SIMP_TAC std_ss [queue_inv_def] THEN NTAC 4 STRIP_TAC
  THEN MATCH_MP_TAC tail_lemma THEN Q.EXISTS_TAC `Once x`
  THEN FULL_SIMP_TAC std_ss [exps_def,APPEND,depth_def]
QED

val _ = export_theory();
