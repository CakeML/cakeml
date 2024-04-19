(*
    Props for Pancake ITree semantics and correspondence proof.
*)

open preamble panLangTheory;
local open alignmentTheory
           miscTheory     (* for read_bytearray *)
           wordLangTheory (* for word_op and word_sh *)
           ffiTheory
           itreeTauTheory
           panSemTheory
           panLangTheory
           panItreeSemTheory in end;

val _ = new_theory "panItreeProps";

val _ = temp_set_fixity "≈" (Infixl 500);
Overload "≈" = “itree_wbisim”;
val _ = temp_set_fixity ">>=" (Infixl 500);
Overload ">>=" = “itree_bind”;
Overload "case" = “itree_CASE”;

Theorem itree_bind_ret_inv:
  itree_bind t k = Ret x ⇒ ∃r. (k r) = Ret x
Proof
  disch_tac >>
  Cases_on ‘t’ >>
  fs [itreeTauTheory.itree_bind_thm] >>
  metis_tac []
QED

Theorem itree_bind_ret_tree:
  itree_bind t k = Ret x ⇒
  ∃y. t = Ret y
Proof
  disch_tac >>
  Cases_on ‘t’
  >- (metis_tac [itreeTauTheory.itree_bind_thm]) >>
  fs [itreeTauTheory.itree_bind_def]
QED

Theorem itree_bind_ret_inv_gen:
  itree_bind t k = Ret x ⇒
  ∃y. t = Ret y ∧ (k y) = Ret x
Proof
  disch_tac >>
  Cases_on ‘t’
  >- (qexists_tac ‘x'’ >> rw [] >>
      fs [itreeTauTheory.itree_bind_thm]) >>
  fs [itreeTauTheory.itree_bind_def]
QED

Theorem itree_bind_left_ident_over_f:
  f $ Ret x >>= k = f (k x)
Proof
  AP_TERM_TAC >>
  rw [itreeTauTheory.itree_bind_thm]
QED

Theorem itree_eq_imp_wbisim:
  t = t' ⇒ t ≈ t'
Proof
  rw [Once itreeTauTheory.itree_wbisim_strong_coind] >>
  rw [itreeTauTheory.itree_wbisim_refl]
QED

Theorem itree_bind_left_ident_wbisim:
  Ret r >>= k ≈ k r
Proof
  rw [itree_eq_imp_wbisim]
QED

Theorem itree_bind_thm_wbisim:
  t ≈ Ret r ⇒ t >>= k ≈ k r
Proof
  disch_tac >>
  drule itreeTauTheory.itree_bind_resp_t_wbisim >>
  rw [itree_bind_left_ident_wbisim]
QED

Theorem itree_wbisim_bind_trans:
  t1 ≈ t2 ∧ t1 >>= k ≈ t3 ⇒
  t2 >>= k ≈ t3
Proof
  strip_tac >>
  irule itreeTauTheory.itree_wbisim_trans >>
  qexists_tac ‘t1 >>= k’ >>
  strip_tac
  >- (irule itreeTauTheory.itree_bind_resp_t_wbisim >>
      rw [itreeTauTheory.itree_wbisim_sym])
  >- (rw [])
QED

Theorem itree_wbisim_neq:
  Ret r ≈ Ret r' ⇔ r = r'
Proof
  EQ_TAC >>
  rw [Once itreeTauTheory.itree_wbisim_cases]
QED

Theorem nat_not_const_eq:
  ¬(∀k:num. k = 0)
Proof
  rw []
QED

val _ = export_theory();
