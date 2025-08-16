(*
  Addition of linear terms with real-valued coefficients
*)
Theory real_plus
Ancestors
  sptree real
Libs
  preamble

Definition plus_def:
  plus LN t = t ∧
  plus (LS x) t =
    (case t of
     | LN => LS (x:real)
     | BN t1 t2 => mk_BS t1 x t2
     | LS y =>
        (let r = x + y in if r = 0 then LN else LS r)
     | BS t1 y t2 =>
        (let r = x + y in if r = 0 then mk_BN t1 t2 else mk_BS t1 r t2)) ∧
  plus (BN u1 u2) t =
    (case t of
     | LN => BN u1 u2
     | LS y => BS u1 y u2
     | BN t1 t2 => mk_BN (plus u1 t1) (plus u2 t2)
     | BS t1 y t2 => mk_BS (plus u1 t1) y (plus u2 t2)) ∧
  plus (BS u1 x u2) t =
    (case t of
     | LN => mk_BS u1 x u2
     | LS y =>
        (let r = x + y in if r = 0 then BN u1 u2 else BS u1 r u2)
     | BN t1 t2 => mk_BS (plus u1 t1) x (plus u2 t2)
     | BS t1 y t2 =>
        (let z1 = plus u1 t1 in
         let z2 = plus u2 t2 in
         let r = x + y in if r = 0 then mk_BN z1 z2 else mk_BS z1 r z2))
End

Definition coeff_def:
  coeff n t =
    case lookup n t of
    | SOME r => r
    | NONE => 0:real
End

Triviality lookup_mk_BN_BS:
  lookup n (mk_BN t1 t2) = lookup n (BN t1 t2) ∧
  lookup n (mk_BS t1 x t2) = lookup n (BS t1 x t2)
Proof
  Cases_on ‘t1’ \\ Cases_on ‘t2’ \\ fs [mk_BS_def,mk_BN_def,lookup_def]
QED

Theorem coef_plus:
  ∀t1 t2 n. coeff n (plus t1 t2) = coeff n t1 + coeff n t2
Proof
  Induct
  \\ fs [plus_def,coeff_def,lookup_def,lookup_mk_BN_BS]
  \\ Cases_on ‘t2’ \\ fs [lookup_def,lookup_mk_BN_BS]
  \\ rw [] \\ fs [lookup_def,lookup_mk_BN_BS]
QED

Definition every_def[nocompute]:
  every P t ⇔ ∀n v. lookup n t = SOME v ⇒ P v
End

Theorem every_thm[compute]:
  every P LN = T ∧
  every P (LS x) = P x ∧
  every P (BN t1 t2) = (every P t1 ∧ every P t2) ∧
  every P (BS t1 x t2) = (P x ∧ every P t1 ∧ every P t2) ∧
  every P (mk_BN t1 t2) = (every P t1 ∧ every P t2) ∧
  every P (mk_BS t1 x t2) = (P x ∧ every P t1 ∧ every P t2)
Proof
  fs [every_def,lookup_mk_BN_BS, SF CONJ_ss, lookup_def]
  \\ rw [] \\ eq_tac \\ rw []
  >- (first_x_assum $ irule_at Any
      \\ qexists_tac ‘2 * n + 2’ \\ fs [EVEN_ADD,EVEN_DOUBLE])
  >- (first_x_assum $ irule_at Any
      \\ qexists_tac ‘2 * n + 1’ \\ fs [EVEN_ADD,EVEN_DOUBLE])
  >- (Cases_on ‘n’ \\ fs [] \\ every_case_tac \\ fs [] \\ res_tac)
  >- (first_x_assum $ qspec_then ‘0’ mp_tac \\ fs [])
  >- (first_x_assum $ qspec_then ‘2 * n + 2’ mp_tac \\ fs []
      \\ fs [EVEN_ADD,EVEN_DOUBLE])
  >- (first_x_assum $ qspec_then ‘2 * n + 1’ mp_tac \\ fs []
      \\ fs [EVEN_ADD,EVEN_DOUBLE])
  \\ Cases_on ‘n’ \\ gvs []
  \\ every_case_tac \\ fs [] \\ res_tac
QED

Definition linear_ok_def:
  linear_ok t ⇔ wf t ∧ every (λx. x ≠ 0:real) t
End

Theorem linear_ok_plus:
  ∀t1 t2. linear_ok t1 ∧ linear_ok t2 ⇒ linear_ok (plus t1 t2)
Proof
  Induct
  \\ fs [plus_def,wf_def,linear_ok_def,every_thm]
  \\ Cases_on ‘t2’ \\ fs [wf_def,every_thm]
  \\ rw [] \\ fs [wf_def,every_thm]
  \\ rpt $ irule sptreeTheory.wf_mk_BN
  \\ rpt $ irule sptreeTheory.wf_mk_BS \\ fs []
QED

