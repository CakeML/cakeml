(*
  Formalization of the CP to ILP phase (misc constraints)
*)
Theory cp_to_ilp_misc
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* equivalent definition to circuit_sem *)

Theorem PLUS_MOD_NEQ:
  0 < a ∧ a < c ⇒ (a + b) MOD c ≠ b
Proof
  strip_tac>>
  Cases_on‘b ≥ c’
  >-(
    ‘(a + b) MOD c < c’ suffices_by intLib.ARITH_TAC>>
    simp[MOD_LESS])
  >-(
    ‘b MOD c = b’ by (irule LESS_MOD>>intLib.ARITH_TAC)>>
    ‘(a + b) MOD c ≠ b MOD c’ suffices_by metis_tac[]>>
    DEP_REWRITE_TAC[GSYM gcdTheory.MOD_EQ]>>
    simp[])
QED

Theorem ADD_1_MOD_EQ:
  0 < (c:num) ⇒ (a MOD c = b MOD c ⇔ (a + 1) MOD c = (b + 1) MOD c)
Proof
  strip_tac>>
  Cases_on‘b ≤ a’
  >-simp[GSYM gcdTheory.MOD_EQ]
  >-(
    fs[NOT_LE]>>
    drule_then assume_tac LT_IMP_LE>>
    qmatch_goalsub_abbrev_tac‘x = y ⇔ z = w’>>
    ‘y = x ⇔ w = z’ suffices_by simp[]>>
    unabbrev_all_tac>>
    simp[GSYM gcdTheory.MOD_EQ])
QED

Theorem circuit_sem_alt:
  circuit_sem Xs w ⇔
  EVERY (λX. 0 ≤ varc w X ∧ Num (varc w X) < LENGTH Xs) Xs ∧
  ALL_DISTINCT (MAP (varc w) Xs) ∧
  ∃pos.
    pos 0 = 0 ∧
    (∀i. i < LENGTH Xs ⇒ pos i < LENGTH Xs) ∧
    ALL_DISTINCT (GENLIST pos $ LENGTH Xs) ∧
    ∀i. i < LENGTH Xs ⇒
      pos (Num (varc w (EL i Xs))) = (pos i + 1) MOD LENGTH Xs
Proof
  qmatch_goalsub_abbrev_tac‘_ MOD n’>>
  simp[circuit_sem_def]>>
  qmatch_goalsub_abbrev_tac‘FUNPOW suc _ _’>>
  qmatch_goalsub_abbrev_tac‘P ∧ Q ⇔ P ∧ R’>>
  ‘P ⇒ (Q ⇔ R)’ suffices_by metis_tac[]>>
  simp[Abbr‘P’,EVERY_MEM,MEM_EL,SF DNF_ss]>>
  rw[Abbr‘Q’,Abbr‘R’]>>
  ‘∀i. i < n ⇒
    varc w (EL i Xs) = &Num (varc w (EL i Xs))’ by (
    metis_tac[integerTheory.INT_OF_NUM])>>
  ‘ALL_DISTINCT (MAP (varc w) Xs) ⇒
   (∀i j. i < n ∧ j < n ⇒ (suc i = suc j ⇔ i = j)) ∧
   (∀i. i < n ⇒ ∃j. j < n ∧ i = suc j)’ by (
    simp[EL_ALL_DISTINCT_EL_EQ,EL_MAP]>>
    strip_tac>>
    CONJ_ASM1_TAC
    >-(rw[Abbr‘suc’]>>metis_tac[])
    >-cheat(* suc injectivity implies surjectivity *)
    )>>
  ‘∀i j. i < n ⇒ FUNPOW suc j i < n’ by (
    Induct_on‘j’>>
    simp[FUNPOW_0,FUNPOW_SUC])>>
  iff_tac
  >-(
    qabbrev_tac‘step = (λn. FUNPOW suc n 0)’>>
    strip_tac>>
    ‘∀i j. i < n ∧ j < n ⇒ (step i = step j ⇔ i = j)’ by (
      rw[]>>
      iff_tac>>
      simp[]>>
      rename1‘_ ⇒ i = j’>>
      qmatch_goalsub_abbrev_tac‘P ⇒ Q’>>
      ‘¬Q ⇒ ¬P’ suffices_by metis_tac[]>>
      rw[Abbr‘P’,Abbr‘Q’]>>
      ‘step i < n’ by simp[Abbr‘step’]>>
      first_x_assum $ drule_then assume_tac>>
      wlog_tac ‘i < j’ [‘i’,‘j’]
      >-(
        ‘j < i’ by metis_tac[LESS_CASES_IMP]>>
        first_x_assum $ drule_then assume_tac>>
        metis_tac[])
      >-(
        ‘0 < j - i ∧ j - i < n’ by (CONJ_TAC>>simp[])>>
        first_x_assum $ drule_all_then assume_tac>>
        pop_assum mp_tac>>
        simp[Abbr‘step’,GSYM FUNPOW_ADD])
      )>>
    ‘∀i. i < n ⇒ ∃j. j < n ∧ step j = i’ by cheat
      (* step injectivity implies surjectivity *)>>
    ‘∀i j. i < n ∧ j < n ⇒ (suc i = suc j ⇔ i = j)’ by cheat>>
    CONJ_ASM1_TAC
    >-(
      pop_assum mp_tac>>
      simp[Abbr‘suc’,EL_ALL_DISTINCT_EL_EQ,EL_MAP]>>
      metis_tac[])
    >-(
      ‘∀i j. i < n ∧ j < n ⇒
        ((λk. if k < n then @m. m < n ∧ step m = k else k) i = j ⇔
        step j = i)’ by (
        rw[]>>
        SELECT_ELIM_TAC>>
        metis_tac[])>>
      qmatch_asmsub_abbrev_tac‘_ ⇒ (pos _ = _ ⇔ step _ = _)’>>
      qexists‘pos’>>
      qmatch_goalsub_abbrev_tac‘P ∧ Q ∧ R ∧ Z’>>
      ‘P ∧ Q ∧ R ∧ (Q ⇒ Z)’ suffices_by metis_tac[]>>
      simp[Abbr‘P’,Abbr‘Q’,Abbr‘R’,Abbr‘Z’]>>
      rpt CONJ_TAC
      >-(Cases_on‘0 < n’>>fs[Abbr‘step’])
      >-(
        rw[Abbr‘pos’]>>
        SELECT_ELIM_TAC>>
        simp[])
      >-(
        simp[EL_ALL_DISTINCT_EL_EQ]>>
        metis_tac[])
      >-(
        rw[]>>
        cheat(* to prove: step ((pos i + 1) MOD n) = suc i *)
      )))
  >-(
    strip_tac>>
    rename1‘pos 0 = 0’>>
    last_x_assum $ drule_all_then mp_tac>>
    rw[]>>
    fs[EL_ALL_DISTINCT_EL_EQ,EL_MAP]>>
    ‘∀i j k. (i < n ∧ j < n) ⇒
      (FUNPOW suc k i = j ⇔ (pos i + k) MOD n = pos j)’
      suffices_by simp[PLUS_MOD_NEQ]>>
    Induct_on‘k’
    >-rw[FUNPOW]>>
    rw[FUNPOW_SUC,ADD1]>>
    rename1‘_ = pos j’>>
    ‘∃h. h < n ∧ j = suc h’ by simp[]>>
    fs[]>>
    pure_rewrite_tac[ADD_ASSOC]>>
    simp[GSYM ADD_1_MOD_EQ])
QED

(* Misc constraints are not yet implemented in the CP semantics
   (misc_constr_sem always returns T)
   These are placeholders for future work *)

Definition encode_misc_constr_def:
  encode_misc_constr bnd c name =
  []
End

Theorem encode_misc_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Misc c) ∧
  misc_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_misc_constr bnd c name)
Proof
  rw[encode_misc_constr_def]>>
  cheat
QED

Theorem encode_misc_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_misc_constr bnd c name) ⇒
  misc_constr_sem c wi
Proof
  rw[encode_misc_constr_def,misc_constr_sem_def]>>
  cheat
QED

(* Concrete encodings *)
Definition cencode_misc_constr_def:
  cencode_misc_constr bnd c name ec =
  (List [], ec)
End

Theorem cencode_misc_constr_sem:
  valid_assignment bnd wi ∧
  cencode_misc_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_misc_constr bnd c name) ec ec'
Proof
  rw[cencode_misc_constr_def,encode_misc_constr_def]>>
  simp[enc_rel_def]
QED
