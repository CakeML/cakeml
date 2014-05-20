open HolKernel Parse boolLib bossLib; val _ = new_theory "bvl_to_bvp";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory bytecodeEvalTheory bvlTheory;
open bvl_inlineTheory bvpTheory;

infix \\ val op \\ = op THEN;

(* translation of BVL to BVP *)

val index_of_def = Define `
  (index_of n [] = 0:num) /\
  (index_of n (x::xs) = if x = n then 0 else 1 + index_of n xs)`;

val bComp_def = tDefine "bComp" `
  (bComp (n:num) (env:num list) [] = (Skip,[]:num list,n)) /\
  (bComp n env (x::y::xs) =
     let (c1,v1,n1) = bComp n env [x] in
     let (c2,vs,n2) = bComp n1 env (y::xs) in
       (Seq c1 c2, HD v1 :: vs, n2)) /\
  (bComp n env [Var v] =
    (Move n (index_of v env), [n], n+1)) /\
  (bComp n env [If x1 x2 x3] =
     let (c1,v1,n1) = bComp n env [x1] in
     let (c2,v2,n2) = bComp n1 env [x2] in
     let (c3,v3,n3) = bComp n2 env [x3] in
       (If [Prog c1; Assert (HD v1) T]
          (Seq c2 (Move n3 (HD v2)))
          (Seq c2 (Move n3 (HD v3))),
        [n3],n3+1)) /\
  (bComp n env [Let xs x2] =
     let (c1,vs,n1) = bComp n env xs in
     let (c2,v2,n2) = bComp n1 vs [x2] in
       (Seq c1 c2, v2, n2)) /\
  (bComp n env [Raise x1] =
     let (c1,v1,n1) = bComp n env [x1] in
       (Seq c1 (Raise (HD v1)), v1, n1)) /\
  (bComp n env [Handle x1 x2] =
     let (c1,v1,n1) = bComp n env [x1] in
     let (c2,v2,n2) = bComp (n1+1) env [x2] in
       (Handle (Seq c1 (Move n2 (HD v1))) n2 n1
               (Seq c2 (Move n2 (HD v2))), [n2], n2+1)) /\
  (bComp n env [Op op xs] =
     let (c1,vs,n1) = bComp n env xs in
       (Seq c1 (Assign n1 op vs), [n1], n1+1)) /\
  (bComp n env [Tick x1] =
     let (c1,v1,n1) = bComp n env [x1] in
       (Seq Tick c1, v1, n1)) /\
  (bComp n env [Call dest xs] =
     let (c1,vs,n1) = bComp n env xs in
       (Seq c1 (Call n1 dest vs), [n1], n+1))`
 (WF_REL_TAC `measure (bvl_exp1_size o SND o SND)`);

val _ = export_theory();
