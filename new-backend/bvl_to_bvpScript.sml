open HolKernel Parse boolLib bossLib; val _ = new_theory "bvl_to_bvp";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory bvlTheory;
open bvl_inlineTheory bvpTheory;

infix \\ val op \\ = op THEN;

(* translation of BVL to BVP *)

val index_of_def = Define `
  (index_of n [] = 0:num) /\
  (index_of n (x::xs) = if x = n then 0 else 1 + index_of n xs)`;

val bComp_def = tDefine "bComp" `
  (bComp (n:num) (env:num list) tail [] =
    (Skip,[]:num list,n)) /\
  (bComp n env tail (x::y::xs) =
     let (c1,v1,n1) = bComp n env F [x] in
     let (c2,vs,n2) = bComp n1 env F (y::xs) in
       (Seq c1 c2, HD v1 :: vs, n2)) /\
  (bComp n env tail [Var v] =
     if tail
     then (Return (index_of v env), [n], n+1)
     else (Move n (index_of v env), [n], n+1)) /\
  (bComp n env tail [If x1 x2 x3] =
     let (c1,v1,n1) = bComp n env F [x1] in
     let (c2,v2,n2) = bComp n1 env tail [x2] in
     let (c3,v3,n3) = bComp n2 env tail [x3] in
       if tail then
         (If [Prog c1; Assert (HD v1) T] c2 c3,[n3],n3+1)
       else
         (If [Prog c1; Assert (HD v1) T]
            (Seq c2 (Move n3 (HD v2)))
            (Seq c3 (Move n3 (HD v3))),
          [n3],n3+1)) /\
  (bComp n env tail [Let xs x2] =
     let (c1,vs,n1) = bComp n env F xs in
     let (c2,v2,n2) = bComp n1 vs tail [x2] in
       (Seq c1 c2, v2, n2)) /\
  (bComp n env tail [Raise x1] =
     let (c1,v1,n1) = bComp n env F [x1] in
       (Seq c1 (Raise (HD v1)), v1, n1)) /\
  (bComp n env tail [Handle x1 x2] =
     let (c1,v1,n1) = bComp n env F [x1] in
     let (c2,v2,n2) = bComp (n1+1) env F [x2] in
     let c3 = Handle (Seq c1 (Move n2 (HD v1))) n2 n1
                     (Seq c2 (Move n2 (HD v2))) in
       (if tail then Seq c3 (Return n2) else c3, [n2], n2+1)) /\
  (bComp n env tail [Op op xs] =
     let (c1,vs,n1) = bComp n env F xs in
     let c2 = Seq c1 (Assign n1 op vs) in
       (if tail then Seq c2 (Return n1) else c2, [n1], n1+1)) /\
  (bComp n env tail [Tick x1] =
     let (c1,v1,n1) = bComp n env F [x1] in
     let c2 = Seq Tick c1 in
       (if tail then Seq c2 (Return n1) else c2, v1, n1)) /\
  (bComp n env tail [Call dest xs] =
     let (c1,vs,n1) = bComp n env F xs in
     let ret = (if tail then NONE else SOME n1) in
       (Seq c1 (Call ret dest vs), [n1], n+1))`
 (WF_REL_TAC `measure (bvl_exp1_size o SND o SND o SND)`);

val _ = export_theory();
