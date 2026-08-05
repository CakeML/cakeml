(*
  Define unionWith for sptrees
*)
Theory sptree_unionWith
Ancestors
  sptree
Libs
  preamble

Definition unionWith_def:
  unionWith f LN t = t ∧
  unionWith f (LS x) t =
    (case t of
     | LN => LS x
     | BN t1 t2 => mk_BS t1 x t2
     | LS y =>
        (case f x y of NONE => LN | SOME r => LS r)
     | BS t1 y t2 =>
        (case f x y of NONE => mk_BN t1 t2 | SOME r => mk_BS t1 r t2)) ∧
  unionWith f (BN u1 u2) t =
    (case t of
     | LN => BN u1 u2
     | LS y => BS u1 y u2
     | BN t1 t2 => mk_BN (unionWith f u1 t1) (unionWith f u2 t2)
     | BS t1 y t2 => mk_BS (unionWith f u1 t1) y (unionWith f u2 t2)) ∧
  unionWith f (BS u1 x u2) t =
    (case t of
     | LN => mk_BS u1 x u2
     | LS y =>
        (case f x y of NONE => BN u1 u2 | SOME r => BS u1 r u2)
     | BN t1 t2 => mk_BS (unionWith f u1 t1) x (unionWith f u2 t2)
     | BS t1 y t2 =>
        (let z1 = unionWith f u1 t1 in
         let z2 = unionWith f u2 t2 in
           case f x y of NONE => mk_BN z1 z2 | SOME r => mk_BS z1 r z2))
End

Theorem lookup_mk_BN_BS:
  lookup n (mk_BN t1 t2) = lookup n (BN t1 t2) ∧
  lookup n (mk_BS t1 x t2) = lookup n (BS t1 x t2)
Proof
  Cases_on ‘t1’ \\ Cases_on ‘t2’
  \\ fs [mk_BS_def,mk_BN_def,lookup_def]
QED

Theorem wf_unionWith:
  ∀f t1 t2. wf t1 ∧ wf t2 ⇒ wf (unionWith f t1 t2)
Proof
  gen_tac \\ Induct
  \\ fs [unionWith_def,wf_def]
  \\ Cases_on ‘t2’ \\ fs [wf_def]
  \\ rw [] \\ every_case_tac \\ fs [wf_def]
  \\ rpt $ irule sptreeTheory.wf_mk_BN
  \\ rpt $ irule sptreeTheory.wf_mk_BS \\ fs []
QED

Theorem lookup_unionWith:
  ∀f x y n.
    lookup n (unionWith f x y) =
    case lookup n x of
    | NONE => lookup n y
    | SOME i => case lookup n y of
                | NONE => SOME i
                | SOME j => f i j
Proof
  Induct_on ‘x’ \\ rw [unionWith_def]
  \\ Cases_on ‘y’ \\ rw [unionWith_def,lookup_def,lookup_mk_BN_BS]
  \\ every_case_tac \\ gvs [lookup_def,lookup_mk_BN_BS]
QED

