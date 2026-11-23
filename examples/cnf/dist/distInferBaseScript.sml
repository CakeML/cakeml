(*
    Properties of inference relations shared by the distributed specifications
 *)
Theory distInferBase
Ancestors
  pred_set
Libs
  bossLib

Definition cut_elimination_def:
  cut_elimination infer ⇔
    (∀facts facts' fact fact'.
       infer facts fact ∧ infer (fact INSERT facts') fact' ⇒
       infer (facts ∪ facts') fact')
End

Definition assumption_def:
  assumption infer ⇔ (∀fact. infer {fact} fact)
End

Definition monotonic_def:
  monotonic infer ⇔
    (∀facts facts' fact.
       infer facts fact ⇒ infer (facts ∪ facts') fact)
End

Theorem cut_elim_lemma1:
  ∀oprems facts infer fact.
    FINITE facts ∧ facts ⊆ infer oprems ∧
    infer (oprems ∪ facts) fact ∧
    cut_elimination infer ∧ monotonic infer ⇒
    infer oprems fact
Proof
  ntac 3 strip_tac >> Induct_on ‘FINITE’ >>
  rw[] >> gvs[IN_DEF] >>
  first_x_assum irule >>
  gvs[monotonic_def] >>
  first_x_assum rev_dxrule >>
  strip_tac >>
  gvs[cut_elimination_def] >>
  first_x_assum $ qspecl_then [‘oprems ∪ facts’,‘oprems ∪ facts’] assume_tac >>
  gvs[] >>
  first_x_assum irule >>
  first_x_assum $ irule_at $ Pos last >>
  pop_assum mp_tac >>
  match_mp_tac EQ_IMPLIES >>
  AP_THM_TAC >> AP_TERM_TAC >>
  rw[SET_EQ_SUBSET,SUBSET_DEF]
QED

Theorem cut_elim_lemma2:
  ∀oprems facts infer fact.
    FINITE facts ∧ facts ⊆ infer oprems ∧ infer facts fact ∧
    cut_elimination infer ∧ monotonic infer ⇒
    infer oprems fact
Proof
  ntac 3 strip_tac >> Induct_on ‘FINITE’ >>
  rw[]
  >- (gvs[monotonic_def] >> res_tac >> fs[]) >>
  gvs[IN_DEF] >>
  irule cut_elim_lemma1 >>
  gvs[] >>
  first_assum $ irule_at $ Pos hd >>
  gvs[cut_elimination_def] >>
  first_assum $ rev_drule_then drule >>
  strip_tac
QED
