(*
  Correctness proof for the parser; showing that the parse_prog implementation
  conforms to the specification (semantics$parse).
*)
Theory parserProof
Ancestors
  semantics cmlParse pegComplete pegSound
Libs
  preamble

Theorem parse_prog_correct0:
  (parse_prog s = Failure fl fe ⇒ parse s = NONE) ∧
  (parse_prog s = Success s' a eo ⇒ parse s = SOME a ∧ s' = [])
Proof
  simp[parse_prog_def, parse_def, pegresult_bind_def, cmlPEGTheory.pnt_def] >>
  ‘∃r. peg_eval cmlPEG (s, nt (mkNT nTopLevelDecs) I) r’
    by simp[pegTheory.peg_eval_total] >>
  drule_then assume_tac pegexecTheory.pegexec >>
  Cases_on ‘r’ >> simp[destResult_def] >~
  [‘peg_eval _ _ (Failure fl fe)’]
  >- (DEEP_INTRO_TAC some_intro >> simp[] >> rw[] >>
      drule_then drule completeness >> simp[] >>
      disch_then $ qspec_then ‘[]’ mp_tac >> gs[] >>
      dxrule_then assume_tac (cj 1 pegTheory.peg_deterministic) >> simp[]) >~
  [‘Success rest pts eo’]
  >- (Cases_on ‘rest’ >~
      [‘Success (h::t) _ _ ’]
      >- (Cases_on ‘h’ >> simp[destResult_def] >> strip_tac >> gvs[] >>
          DEEP_INTRO_TAC some_intro >> rw[] >>
          drule_then drule completeness >> simp[] >>
          disch_then $ qspec_then ‘[]’ mp_tac >> gs[] >>
          dxrule_then assume_tac (cj 1 pegTheory.peg_deterministic) >>
          simp[]) >>
      simp[destResult_def] >> Cases_on ‘pts’ >> simp[optlift_def] >~
      [‘Success [] [] _’]
      >- (rw[] >> DEEP_INTRO_TAC some_intro >> rw[] >>
          drule_then drule completeness >> simp[] >>
          disch_then $ qspec_then ‘[]’ mp_tac >> gs[] >>
          dxrule_then assume_tac (cj 1 pegTheory.peg_deterministic) >>
          simp[]) >~
      [‘Success [] (pt::pts) _’] >>
      Cases_on ‘ptree_TopLevelDecs pt’ >> simp[optlift_def] >~
      [‘ptree_TopLevelDecs pt = NONE’]
      >- (rw[] >> DEEP_INTRO_TAC some_intro >> simp[] >>
          qx_gen_tac ‘pt2’ >>
          drule_then strip_assume_tac peg_sound >> gvs[] >> strip_tac >>
          qspec_then ‘pt2’ mp_tac completeness >> simp[] >>
          disch_then $ qspecl_then [‘s’, ‘[]’] mp_tac >> gs[] >>
          strip_tac >>
          dxrule_then assume_tac (cj 1 pegTheory.peg_deterministic) >>
          gvs[]) >>
      rw[] >> DEEP_INTRO_TAC some_intro >> simp[] >>
      drule_then strip_assume_tac peg_sound >> gvs[] >> reverse conj_tac
      >- metis_tac[] >>
      qx_gen_tac ‘pt2’ >> strip_tac >>
      qspec_then ‘pt2’ mp_tac completeness >> simp[] >>
      disch_then $ qspecl_then [‘s’, ‘[]’] mp_tac >> gs[] >>
      strip_tac >>
      dxrule_then assume_tac (cj 1 pegTheory.peg_deterministic) >>
      gvs[])
QED

Theorem parse_prog_correct:
  (parse s = NONE ⇔ ∃fl fe. parse_prog s = Failure fl fe) ∧
  (parse s = SOME a ⇔ ∃eo. parse_prog s = Success [] a eo)
Proof
  conj_tac >> eq_tac >> strip_tac >~
  [‘parse_prog s = Failure fl fe’]
  >- (drule $ cj 1 parse_prog_correct0 >> simp[]) >~
  [‘parse s = NONE’]
  >- (Cases_on ‘parse_prog s’ >> simp[] >> drule $ cj 2 parse_prog_correct0 >>
      simp[]) >~
  [‘parse_prog s = Success [] a e0’]
  >- (drule $ cj 2 parse_prog_correct0 >> simp[]) >>
  Cases_on ‘parse_prog s’ >> simp[]
  >- (drule $ cj 2 parse_prog_correct0 >> simp[]) >>
  drule $ cj 1 parse_prog_correct0 >> simp[]
QED

