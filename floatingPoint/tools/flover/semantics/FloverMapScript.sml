(**
  A simple Map datatype for FloVer, implement a version based on lists and one
  based on trees
**)
open MachineTypeTheory ExpressionsTheory;
open preambleFloVer;

val _ = new_theory "FloverMap";

Datatype:
  cmp = Lt | Eq | Gt
End

Definition exprCompare_def:
  exprCompare (e1:real expr) e2 =
    case e1, e2 of
      |(Var (n1:num)), (Var n2) =>
                 if (n1 < n2)
                 then Lt
                 else
                     if (n1 = n2) then Eq else Gt
      | (Var n), _ => Lt
      | (Const _ _), Var _ => Gt
      | Const m1 v1, Const m2 v2 =>
          if m1 = m2
          then
              (if (v1 < v2)
               then Lt
               else if (v1 = v2)
               then Eq
               else Gt)
          else (if morePrecise m1 m2 then Lt else Gt)
      | Const _ _, _ => Lt
      | Unop u1 e1, Unop u2 e2 =>
        if u1 = u2
        then exprCompare e1 e2
        else (if u1 = Neg then Lt else Gt)
      | Unop _ _, Binop _ _ _ => Lt
      | Unop _ _, Downcast _ _ => Lt
      | Unop _ _, Fma _ _ _ => Lt
      | Unop _ _, _ => Gt
      | Downcast m1 e1, Downcast m2 e2 =>
          if m1 = m2
          then exprCompare e1 e2
          else (if morePrecise m1 m2 then Lt else Gt)
      | Downcast _ _, Binop _ _ _ => Lt
      | Downcast _ _, _ => Gt
      | Binop b1 e11 e12, Binop b2 e21 e22 =>
        let res = case b1, b2 of
                 | Plus, Plus => Eq
                 | Plus, _ => Lt
                 | Sub, Sub => Eq
                 | Sub, Plus => Gt
                 | Sub, _ => Lt
                 | Mult, Mult => Eq
                 | Mult, Div => Lt
                 | Mult, _ => Gt
                 | Div, Div => Eq
                 | Div, _ => Gt
        in
          (case res of
             | Eq =>
               (case exprCompare e11 e21  of
                  | Eq => exprCompare e12 e22
                  | Lt => Lt
                  | Gt => Gt)
             | _ => res)
      | Fma e1 e2 e3, Fma e4 e5 e6 =>
        (case exprCompare e1 e4 of
         | Eq =>
           (case exprCompare e2 e5 of
           | Eq => exprCompare e3 e6
           | Lt => Lt
           | Gt => Gt)
         | Lt => Lt
         | Gt => Gt)
      | _ , Fma e1 e2 e3 => Lt
      | Fma e1 e2 e3, _ => Gt
      |_ , _ => Gt
End

Theorem exprCompare_refl:
  !e. exprCompare e e = Eq
Proof
  Induct \\ rpt strip_tac \\ simp[ Once exprCompare_def]
  \\ Cases_on `b` \\ fs[]
QED

Definition FloverMapList_insert_def:
  (FloverMapList_insert e k NIL = [(e,k)]) /\
  (FloverMapList_insert e k ((e1,l1) :: el) =
   case exprCompare e e1 of
     | Lt => (e,k)::(e1,l1)::el
     | Eq  => (e1,l1) :: el
     | Gt => (e1,l1):: FloverMapList_insert e k el)
End

Definition FloverMapList_find_def:
  (FloverMapList_find e NIL = NONE) /\
  (FloverMapList_find e ((e1,k)::el) = if exprCompare e e1 = Eq then SOME k
                                       else FloverMapList_find e el)
End

Datatype:
  binTree = Node 'a binTree binTree | Leaf 'a | LeafN
End

Definition FloverMapTree_insert_def:
  (FloverMapTree_insert e k LeafN = Leaf (e,k)) /\
  (FloverMapTree_insert e k (Leaf (e1,k1)) =
     case (exprCompare e e1) of
            | Lt => Node (e1,k1) (Leaf (e,k)) (LeafN)
            | Eq => Leaf (e1,k)
            | Gt => Node (e1,k1) (LeafN) (Leaf (e,k))) /\
  (FloverMapTree_insert e k (Node (e1,k1) tl tr) =
     case (exprCompare e e1) of
            | Lt => Node (e1,k1) (FloverMapTree_insert e k tl) tr
            | Eq => (Node (e1, k) tl tr)
            | Gt => Node (e1,k1) tl (FloverMapTree_insert e k tr))
End

Definition FloverMapTree_find_def:
  (FloverMapTree_find e (LeafN) = NONE) /\
  (FloverMapTree_find e (Leaf (e1,k1)) =
     if exprCompare e e1 = Eq then SOME k1 else NONE) /\
  (FloverMapTree_find e (Node (e1,k1) tl tr) =
    case (exprCompare e e1) of
      | Lt => FloverMapTree_find e tl
      | Eq => SOME k1
      | Gt => FloverMapTree_find e tr)
End

Definition FloverMapTree_mem_def:
  FloverMapTree_mem e tMap =
    case (FloverMapTree_find e tMap) of
      | SOME _ => T
      | _ => F
End

Definition FloverMapTree_empty_def:
  FloverMapTree_empty = LeafN
End

Theorem FloverMapTree_find_injective:
  !e a b Tree.
      FloverMapTree_find e Tree = SOME a /\
      FloverMapTree_find e Tree = SOME b ==>
      a = b
Proof
  rpt strip_tac
  \\ Cases_on `Tree` \\ fs[FloverMapTree_find_def]
QED

Theorem FloverMapTree_correct:
  !Tree k v.
      FloverMapTree_find k (FloverMapTree_insert k v Tree) = SOME v
Proof
  Induct_on `Tree`
  \\ fs[FloverMapTree_find_def, FloverMapTree_insert_def]
  \\ rpt strip_tac \\ fs[exprCompare_refl]
  >- (Cases_on `a` \\ fs[FloverMapTree_insert_def]
      \\ Cases_on `exprCompare k q` \\ fs[FloverMapTree_find_def]
      \\ first_x_assum irule \\ fs[])
  \\ Cases_on `a` \\ fs[FloverMapTree_insert_def]
  \\ Cases_on `exprCompare k q` \\ fs[FloverMapTree_find_def, exprCompare_refl]
QED

Theorem exprCompare_eq:
  !e1 e2. exprCompare e1 e2 = Eq <=> e1 = e2
Proof
  Induct_on `e1` \\ Cases_on `e2` \\ simp[Once exprCompare_def] \\ rpt strip_tac
  >- (EVERY_CASE_TAC \\ fs[])
  >- (EVERY_CASE_TAC \\ fs[])
  >- (first_x_assum (qspec_then `e` assume_tac)
      \\ Cases_on `u' = u` \\ fs[]
      \\ EVERY_CASE_TAC \\ fs[])
  >- (first_x_assum (qspec_then `e0` assume_tac)
      \\ first_x_assum (qspec_then `e` assume_tac)
      \\ EVERY_CASE_TAC \\ fs[])
  >- (first_x_assum (qspec_then `e1'''` assume_tac)
      \\ first_x_assum (qspec_then `e0` assume_tac)
      \\ first_x_assum (qspec_then `e` assume_tac)
      \\ EVERY_CASE_TAC \\ fs[])
  \\ first_x_assum (qspec_then `e` assume_tac)
  \\ every_case_tac \\ fs[]
QED

Theorem exprCompare_neq:
  !e1 e2. exprCompare e1 e2 <> Eq <=> e1 <> e2
Proof
  Induct_on `e1` \\ Cases_on `e2` \\ simp[Once exprCompare_def] \\ rpt strip_tac
  >- (EVERY_CASE_TAC \\ fs[])
  >- (EVERY_CASE_TAC \\ fs[])
  >- (first_x_assum (qspec_then `e` assume_tac)
      \\ Cases_on `u' = u` \\ fs[]
      \\ EVERY_CASE_TAC \\ fs[])
  >- (first_x_assum (qspec_then `e0` assume_tac)
      \\ first_x_assum (qspec_then `e` assume_tac)
      \\ EVERY_CASE_TAC \\ fs[])
  >- (first_x_assum (qspec_then `e1'''` assume_tac)
      \\ first_x_assum (qspec_then `e0` assume_tac)
      \\ first_x_assum (qspec_then `e` assume_tac)
      \\ EVERY_CASE_TAC \\ fs[])
  \\ first_x_assum (qspec_then `e` assume_tac)
  \\ every_case_tac \\ fs[]
QED

Theorem map_find_add:
  ! e1 e2 m map1.
      FloverMapTree_find e1 (FloverMapTree_insert e2 m map1) =
      if (e1 = e2)
      then SOME m
      else FloverMapTree_find e1 map1
Proof
  Induct_on `map1` \\ rpt strip_tac
  \\ fs[FloverMapTree_insert_def, FloverMapTree_find_def, exprCompare_eq]
  >- (Cases_on `a` \\ fs[FloverMapTree_insert_def]
      \\ Cases_on `exprCompare e2 q` \\ fs[FloverMapTree_find_def]
      \\ Cases_on `exprCompare e1 q` \\ fs[exprCompare_eq] \\ rveq
      >- (`e2 <> e1`
            by (Cases_on `exprCompare e2 e1 = Eq` \\ fs[exprCompare_neq])
          \\ fs[])
      >- (Cases_on `e1 = e2` \\ fs[])
      >- (`e1 <> e2`
            by (Cases_on `exprCompare e1 e2 = Eq` \\ fs[exprCompare_neq])
          \\ fs[])
      >- (`e1 <> e2`
            by (Cases_on `exprCompare e1 e2 = Eq` \\ fs[exprCompare_neq])
          \\ fs[])
      >- (Cases_on `e1 = e2` \\ fs[])
      \\ `e2 <> e1`
          by (Cases_on `exprCompare e2 e1 = Eq` \\ fs[exprCompare_neq])
      \\ fs[])
  \\ Cases_on `a` \\ fs[FloverMapTree_insert_def]
  \\ Cases_on `exprCompare e2 q` \\ fs[FloverMapTree_find_def]
  \\ Cases_on `exprCompare e1 q` \\ fs[exprCompare_eq] \\ rveq
  >- (`e2 <> e1`
        by (Cases_on `exprCompare e2 e1 = Eq` \\ fs[exprCompare_neq])
      \\ fs[])
  >- (Cases_on `e1 = e2` \\ fs[])
  >- (`e1 <> e2`
        by (Cases_on `exprCompare e1 e2 = Eq` \\ fs[exprCompare_neq])
      \\ fs[])
  >- (`e1 <> e2`
        by (Cases_on `exprCompare e1 e2 = Eq` \\ fs[exprCompare_neq])
      \\ fs[])
  >- (Cases_on `e1 = e2` \\ fs[])
  \\ `e2 <> e1`
      by (Cases_on `exprCompare e2 e1 = Eq` \\ fs[exprCompare_neq])
  \\ fs[]
QED

Theorem map_mem_add:
  !e1 e2 m map1.
      FloverMapTree_mem e1 (FloverMapTree_insert e2 m map1) =
      (e1 = e2 \/ FloverMapTree_mem e1 map1)
Proof
  fs[FloverMapTree_mem_def, map_find_add]
  \\ rpt strip_tac \\ Cases_on `e1 = e2` \\ fs[]
QED

val _ = export_theory();
