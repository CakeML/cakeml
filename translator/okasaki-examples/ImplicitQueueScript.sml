
open HolKernel Parse boolLib bossLib; val _ = new_theory "ImplicitQueue";

open listTheory arithmeticTheory ml_translatorLib mini_preludeTheory;

val _ = translation_extends "mini_prelude";

(* Okasaki page 174 *)

(* implementation *)

(* The following datatype is defined slightly differently from the one
   Okasaki defines. The definition Okasaki uses is not supported by
   HOL4's Hol_datatype function. *)

val _ = Hol_datatype `times = Once of 'a | Twice of times => times`;
val _ = Hol_datatype `digit = Zero | One of 'a times | Two of 'a times => 'a times`;
val _ = Hol_datatype `queue = Shallow of 'a digit
                            | Deep of 'a digit => queue => 'a digit`;

val empty_def = mlDefine `
  empty = Shallow Zero`;

val is_empty_def = mlDefine `
  (is_empty (Shallow Zero) = T) /\
  (is_empty _ = F)`;

val snoc_def = mlDefine `
  (snoc (Shallow Zero) y = Shallow (One y)) /\
  (snoc (Shallow (One x)) y = Deep (Two x y) empty Zero) /\
  (snoc (Deep f m Zero) y = Deep f m (One y)) /\
  (snoc (Deep f m (One x)) y = Deep f (snoc m (Twice x y)) Zero)`

val head_def = mlDefine `
  (head (Shallow (One x)) = x) /\
  (head (Deep (One x) m r) = x) /\
  (head (Deep (Two x y) m r) = x)`;

val tail_def = mlDefine `
  (tail (Shallow (One x)) = empty) /\
  (tail (Deep (Two x y) m r) = Deep (One y) m r) /\
  (tail (Deep (One x) q r) =
     if is_empty q then Shallow r else
       case head q of Twice y z => Deep (Two y z) (tail q) r)`

(* verification *)

val exps_def = Define `
  (exps (Once x) = [x]) /\
  (exps (Twice t1 t2) = exps t1 ++ exps t2)`;

val digits_def = Define `
  (digits Zero = []) /\
  (digits (One x) = exps x) /\
  (digits (Two x y) = exps x ++ exps y)`;

val flatten_def = Define `
  (flatten (Shallow x) = digits x) /\
  (flatten (Deep d1 t d2) = digits d1 ++ flatten t ++ digits d2)`;

val only_digits_def = Define `
  (only_digits Zero = []) /\
  (only_digits (One x) = [x]) /\
  (only_digits (Two x y) = [x;y])`;

val depth_def = Define `
  (depth n (Once x) <=> (n = 0:num)) /\
  (depth n (Twice t1 t2) <=> ~(n = 0) /\ depth (n-1) t1 /\ depth (n-1) t2)`;

val ddepth_def = Define `
  ddepth n d = EVERY (\d. depth n d) (only_digits d)`;

val two_def = Define `
  (two (Two _ _) = T) /\ (two _ = F)`;

val queue_ok_def = Define `
  (queue_ok n (Shallow x) <=> ~two x /\ ddepth n x) /\
  (queue_ok n (Deep x1 t x2) <=>
     ~(x1 = Zero) /\ queue_ok (n+1) t /\ ~two x2 /\ ddepth n x1 /\ ddepth n x2)`;

val queue_inv_def = Define `
  queue_inv q t <=> queue_ok 0 t /\ (q = flatten t)`;

val empty_thm = prove(
  ``queue_inv [] empty``,
  EVAL_TAC);

val exps_NOT_NIL = prove(
  ``!e. ~(exps e = [])``,
  Induct THEN EVAL_TAC THEN FULL_SIMP_TAC std_ss [APPEND_eq_NIL]);

val is_empty_thm = prove(
  ``!xs q. queue_inv xs q ==> (is_empty q = (xs = []))``,
  Cases THEN Cases THEN EVAL_TAC
  THEN1 (Cases_on `d` THEN EVAL_TAC THEN SIMP_TAC std_ss [exps_NOT_NIL])
  THEN1 (Cases_on `d0` THEN EVAL_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ]
         THEN SIMP_TAC std_ss [exps_NOT_NIL,APPEND_eq_NIL])
  THEN Cases_on `d` THEN EVAL_TAC);

val flatten_snoc = prove(
  ``!x y n. queue_ok n x ==> (flatten (snoc x y) = flatten x ++ exps y)``,
  Induct THEN Cases_on `d`
  THEN FULL_SIMP_TAC (srw_ss()) [snoc_def,flatten_def,digits_def,
      empty_def,queue_ok_def,two_def] THEN REPEAT STRIP_TAC
  THEN RES_TAC THEN FULL_SIMP_TAC std_ss [exps_def,APPEND_ASSOC]);

val queue_ok_snoc = prove(
  ``!q y n. queue_ok n q /\ depth n y ==> queue_ok n (snoc q y)``,
  Induct THEN Cases_on `d`
  THEN FULL_SIMP_TAC (srw_ss()) [snoc_def,queue_ok_def,ddepth_def,two_def,
    only_digits_def,EVERY_DEF,empty_def] THEN REPEAT STRIP_TAC
  THEN Q.PAT_ASSUM `!x.bbb` MATCH_MP_TAC
  THEN FULL_SIMP_TAC (srw_ss()) [depth_def]);

val snoc_thm = prove(
  ``!q xs x. queue_inv xs q ==> queue_inv (xs ++ [x]) (snoc q (Once x))``,
  STRIP_TAC THEN SIMP_TAC std_ss [queue_inv_def] THEN REPEAT STRIP_TAC
  THEN IMP_RES_TAC flatten_snoc THEN FULL_SIMP_TAC std_ss [exps_def]
  THEN MATCH_MP_TAC queue_ok_snoc THEN FULL_SIMP_TAC std_ss [] THEN EVAL_TAC);

val depth_0 = prove(
  ``!e. depth 0 e ==> ?x. e = Once x``,
  Cases THEN SIMP_TAC (srw_ss()) [depth_def]);

val head_thm = prove(
  ``!q x xs. queue_inv (x::xs) q ==> (head q = Once x)``,
  Cases THEN TRY (Cases_on `d`) THEN TRY (Cases_on `d0`)
  THEN EVAL_TAC THEN SIMP_TAC (srw_ss()) []
  THEN REPEAT STRIP_TAC THEN IMP_RES_TAC depth_0
  THEN FULL_SIMP_TAC (srw_ss()) [exps_def])

val depth_IMP = prove(
  ``!t n. depth n t ==> (LENGTH (exps t) = 2**n)``,
  Induct THEN1 (EVAL_TAC THEN FULL_SIMP_TAC std_ss [])
  THEN Cases THEN FULL_SIMP_TAC std_ss [depth_def,ADD1]
  THEN REPEAT STRIP_TAC THEN RES_TAC
  THEN FULL_SIMP_TAC (srw_ss()) [exps_def,GSYM ADD1,EXP] THEN DECIDE_TAC);

val LENGTH_EQ_APPEND_EQ = prove(
  ``!xs xs2 ys ys2.
      (LENGTH xs = LENGTH ys) /\ (xs ++ xs2 = ys ++ ys2) ==> (xs2 = ys2)``,
  Induct THEN Cases_on `ys` THEN FULL_SIMP_TAC (srw_ss()) [ADD1]);

val is_empty_EQ = prove(
  ``!q. is_empty q = (q = Shallow Zero)``,
  Cases THEN Cases_on `d` THEN EVAL_TAC);

val tail_lemma = prove(
  ``!q n x xs.
      queue_ok n q /\ (exps x ++ xs = flatten q) /\ depth n x ==>
      queue_ok n (tail q) /\ (xs = flatten (tail q))``,
  Induct THEN1 (Cases_on `d`
    THEN FULL_SIMP_TAC (srw_ss()) [flatten_def,digits_def,exps_NOT_NIL,tail_def,
           queue_ok_def,empty_def,ddepth_def,EVERY_DEF,two_def,only_digits_def]
    THEN REPEAT STRIP_TAC THEN IMP_RES_TAC depth_IMP
    THEN Cases_on `xs` THEN FULL_SIMP_TAC std_ss []
    THEN Q.PAT_ASSUM `exps x ++ h::t' = exps t` (ASSUME_TAC o GSYM)
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
  THEN `depth n t' ∧ depth n t0` by ALL_TAC THEN1
   (Cases_on `q` THEN FULL_SIMP_TAC std_ss [head_def]
    THEN Cases_on `d'` THEN TRY (Cases_on `d0`) THEN STRIP_TAC
    THEN FULL_SIMP_TAC std_ss [head_def,is_empty_def,queue_ok_def,
      ddepth_def,only_digits_def,EVERY_DEF,depth_def,two_def])
  THEN FULL_SIMP_TAC std_ss []
  THEN `?ts. flatten q = exps (head q) ++ ts` by ALL_TAC THEN1
   (Cases_on `q` THEN FULL_SIMP_TAC std_ss [is_empty_def] THEN1
     (Cases_on `d'` THEN FULL_SIMP_TAC std_ss [is_empty_def]
      THEN FULL_SIMP_TAC std_ss [head_def,is_empty_def,queue_ok_def,digits_def,
        ddepth_def,only_digits_def,EVERY_DEF,depth_def,two_def,flatten_def]
      THEN Q.EXISTS_TAC `[]` THEN FULL_SIMP_TAC (srw_ss()) [])
    THEN FULL_SIMP_TAC std_ss [exps_def,flatten_def]
    THEN Q.PAT_ASSUM `head xx = yy` MP_TAC
    THEN Q.PAT_ASSUM `queue_ok (n + 1) xx` MP_TAC THEN Cases_on `d0`
    THEN SIMP_TAC std_ss [head_def,is_empty_def,queue_ok_def,digits_def,exps_def,
      ddepth_def,only_digits_def,EVERY_DEF,depth_def,two_def,flatten_def,digits_def]
    THEN SIMP_TAC (srw_ss()) [digits_def,exps_def])
  THEN Q.PAT_ASSUM `!x.bbb` (MP_TAC o GSYM o Q.SPECL [`n+1`,`head q`,`ts`])
  THEN FULL_SIMP_TAC std_ss []
  THEN MATCH_MP_TAC (METIS_PROVE [] ``b /\ (b1 ==> b2) ==> (b ==> b1) ==> b2``)
  THEN FULL_SIMP_TAC std_ss [exps_def,depth_def]);

val tail_thm = prove(
  ``!q x xs. queue_inv (x::xs) q ==> queue_inv xs (tail q)``,
  FULL_SIMP_TAC std_ss [queue_inv_def] THEN NTAC 4 STRIP_TAC
  THEN MATCH_MP_TAC tail_lemma THEN Q.EXISTS_TAC `Once x`
  THEN FULL_SIMP_TAC std_ss [exps_def,APPEND,depth_def]);

val _ = export_theory();
