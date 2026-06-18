(*
  Formalization of the CP to ILP phase (misc constraints)
*)
Theory cp_to_ilp_misc
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp cp_to_ilp_linear

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

Theorem FINITE_INJ_IMP_SURJ:
  ∀s. FINITE s ⇔ ∀f. INJ f s s ⇒ SURJ f s s
Proof
  metis_tac[INFINITE_INJ_NOT_SURJ]
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
  Cases_on‘n = 0’
  >-( (* trivial case: n = 0 *)
    simp[EL_ALL_DISTINCT_EL_EQ,EL_MAP]>>
    iff_tac>>
    rw[]>>
    qexists‘(λn. 0)’>>
    simp[])>>
  fs[NOT_ZERO]>>
  qmatch_goalsub_abbrev_tac‘FUNPOW suc _ _’>>
  qabbrev_tac‘dom = (λi. i < n)’>>
  ‘FINITE dom’ by (
    ‘dom = count n’ by simp[Abbr‘dom’,EXTENSION,IN_COUNT]>>
    simp[])>>
  fs[FINITE_INJ_IMP_SURJ]>>
  qmatch_goalsub_abbrev_tac‘P ∧ Q ⇔ P ∧ R’>>
  ‘P ⇒ (Q ⇔ R)’ suffices_by metis_tac[]>>
  simp[Abbr‘P’,EVERY_MEM,MEM_EL,SF DNF_ss]>>
  rw[Abbr‘Q’,Abbr‘R’]>>
  ‘∀i j. dom i ⇒ dom (FUNPOW suc j i)’ by (
    Induct_on‘j’>>
    simp[FUNPOW_0,FUNPOW_SUC])>>
  iff_tac
  >-( (* forward direction *)
    qabbrev_tac‘step = (λn. FUNPOW suc n 0)’>>
    ‘∀m. suc (step m) = step (m + 1)’ by (
      rw[Abbr‘step’,GSYM FUNPOW_SUC,ADD1])>>
    strip_tac>>
    ‘∀m k. 0 < k ∧ dom k ⇒ step (m + k) ≠ step m’ by (
      simp[Once ADD_COMM]>>
      simp[Abbr‘step’,FUNPOW_ADD])>>
    ‘INJ step dom dom’ by (
      simp[INJ_DEF,IN_APP]>>
      CONJ_TAC
      >-simp[Abbr‘step’]
      >-(
        ntac 3 strip_tac>>
        rename1‘_ ⇒ i = j’>>
        simp[Once MONO_NOT_EQ]>>
        strip_tac>>
        wlog_tac ‘i < j’ [‘i’,‘j’]
        >-(
          ‘j < i’ by metis_tac[LESS_CASES_IMP]>>
          first_x_assum $ drule_then assume_tac>>
          metis_tac[])
        >-(
          ‘0 < j - i ∧ dom (j - i)’ by (CONJ_TAC>>fs[Abbr‘dom’])>>
          first_x_assum $ drule_all_then (qspec_then ‘i’ mp_tac)>>
          ‘i + (j - i) = j’ suffices_by metis_tac[]>>
          simp[intLib.ARITH_PROVE“0n < j - i ⇒ i + (j - i) = j”]
          )))>>
    last_x_assum $ drule_then assume_tac>>
    fs[INJ_DEF,SURJ_DEF,IN_APP]>>
    ‘step n = step 0’ by (
      ‘dom (step n)’ by simp[Abbr‘step’]>>
      first_assum $ drule_then assume_tac>>
      fs[Abbr‘dom’]>>
      rename1‘step m = step n’>>
      ‘step (n - m + m) = step m ⇒ m = 0’ suffices_by
        metis_tac[intLib.ARITH_PROVE“(m:num) < n ⇒ n - m + m = n”]>>
      simp[Once MONO_NOT_EQ])>>
    CONJ_ASM1_TAC
    >-(
      rw[EL_ALL_DISTINCT_EL_EQ,EL_MAP]>>
      iff_tac>>
      simp[]>>
      pop_assum mp_tac>>
      first_assum $ drule_then assume_tac>>
      strip_tac>>
      first_assum $ drule_then assume_tac>>
      rw[Once MONO_NOT_EQ]>>
      rename1‘step i ≠ step j’>>
      ‘step (i + 1) ≠ step (j + 1)’ suffices_by metis_tac[]>>
      ‘i ≠ j’ by metis_tac[]>>
      wlog_tac‘i < j’ [‘i’,‘j’]
      >-(
        ‘j < i’ by metis_tac[LESS_CASES_IMP]>>
        first_x_assum $ drule_then assume_tac>>
        metis_tac[])
      >-(
        Cases_on‘j + 1 < n’
        >-(
          ‘dom (i + 1) ∧ dom (j + 1)’ by simp[Abbr‘dom’]>>
          qmatch_goalsub_abbrev_tac‘step a ≠ step b’>>
          ‘a ≠ b’ suffices_by metis_tac[]>>
          simp[Abbr‘a’,Abbr‘b’])
        >-(
          ‘j + 1 = n ∧ 0 < i + 1 ∧ dom (i + 1)’ by fs[NOT_LESS,Abbr‘dom’]>>
          simp[]>>
          ‘(i + 1) + 0 = (i + 1)’ suffices_by metis_tac[]>>
          simp[ADD_0])))>>
    qabbrev_tac‘pos = (λk. if dom k then @m. dom m ∧ step m = k else k)’>>
    ‘∀i j. dom i ∧ dom j ⇒ (pos i = j ⇔ step j = i)’ by (
      rw[Abbr‘pos’]>>
      SELECT_ELIM_TAC>>
      metis_tac[])>>
    qexists‘pos’>>
    CONJ_TAC
    >-(
      pop_assum $ rev_drule_all_then assume_tac>>
      simp[Abbr‘step’])>>
    CONJ_ASM1_TAC
    >-(
      rw[Abbr‘pos’]>>
      SELECT_ELIM_TAC>>
      fs[SURJ_DEF,IN_APP])>>
    CONJ_TAC
    >-(
      rw[ALL_DISTINCT_GENLIST]>>
      metis_tac[])
    >-(
      rw[]>>
      rename1‘pos (suc i)’>>
      ‘dom ((pos i + 1) MOD n)’ by fs[Abbr‘dom’]>>
      ‘dom (suc i)’ by simp[]>>
      qmatch_goalsub_abbrev_tac‘pos a = b’>>
      simp[Abbr‘a’,Abbr‘b’]>>
      simp[Abbr‘pos’]>>
      SELECT_ELIM_TAC>>
      fs[SURJ_DEF,IN_APP]>>
      rw[]>>
      rename1‘suc (step x)’>>
      Cases_on‘x + 1 < n’
      >-simp[Abbr‘step’,GSYM FUNPOW_SUC,ADD1]
      >-(
        fs[NOT_LESS]>>
        ‘x + 1 = n’ by fs[Abbr‘dom’]>>
        simp[])))
  >-( (* backward direction *)
    ‘∀i j. dom i ⇒ dom (FUNPOW suc j i)’ by (
      Induct_on‘j’>>
      simp[FUNPOW_0,FUNPOW_SUC])>>
    strip_tac>>
    rename1‘pos 0 = 0’>>
    fs[EL_ALL_DISTINCT_EL_EQ,EL_MAP]>>
    ‘∀i j k. (dom i ∧ dom j) ⇒
      (FUNPOW suc k i = j ⇔ (pos i + k) MOD n = pos j)’
      suffices_by simp[PLUS_MOD_NEQ]>>
    Induct_on‘k’
    >-rw[FUNPOW]>>
    rw[FUNPOW_SUC,ADD1]>>
    rename1‘_ (FUNPOW _ k i) = _’>>
    ‘INJ suc dom dom’ by (
      rfs[INJ_DEF,IN_APP]>>
      rw[Abbr‘suc’]>>
      metis_tac[integerTheory.INT_OF_NUM])>>
    last_x_assum $ drule_then assume_tac>>
    fs[SURJ_DEF,IN_APP]>>
    first_x_assum $ drule_then assume_tac>>
    fs[]>>
    pop_assum (fn thm => simp[GSYM thm])>>
    fs[INJ_DEF,IN_APP]>>
    ‘dom (FUNPOW suc k i)’ by simp[]>>
    pure_rewrite_tac[ADD_ASSOC]>>
    simp[GSYM ADD_1_MOD_EQ]>>
    metis_tac[])
QED

Definition cencode_knapsack1_def:
  cencode_knapsack1 name (n:num) Xs cs t =
  List (cmk_lin_eq (name ^ toString n) (ZIP(cs,Xs)) t)
End

Definition cencode_knapsack_def:
  cencode_knapsack css Xs ts name =
  let lxs = LENGTH Xs in
  if
    EVERY (λcs. LENGTH cs = lxs) css ∧
    LENGTH ts = LENGTH css
  then
    flat_app (MAPi (λn (cs,t). cencode_knapsack1 name n Xs cs t) (ZIP (css,ts)))
  else
    cfalse_constr
End

Definition encode_knapsack_def[simp]:
  encode_knapsack css Xs ts name =
  abstr $ cencode_knapsack css Xs ts name
End

Theorem encode_knapsack_sem_1:
  knapsack_sem css Xs ts wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_knapsack css Xs ts name)
Proof
  rw[cencode_knapsack_def,knapsack_sem_def]>>
  gvs[LIST_REL_EL_EQN,EVERY_FLAT,EVERY_MEM,MEM_MAPi,
    PULL_EXISTS,cencode_knapsack1_def]>>
  rw[]>>
  pairarg_tac>>gvs[eval_iclin_term_CONS,EL_ZIP,EL_MAP]>>
  first_x_assum drule_all>>
  intLib.ARITH_TAC
QED

Theorem encode_knapsack_sem_2:
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_knapsack css Xs ts name) ⇒
  knapsack_sem css Xs ts wi
Proof
  rw[cencode_knapsack_def,knapsack_sem_def]>>
  gvs[LIST_REL_EL_EQN,EVERY_FLAT,EVERY_MEM,MEM_MAPi,
    PULL_EXISTS,cencode_knapsack1_def,cfalse_constr_def]>>
  rw[]>>first_x_assum drule>>
  pairarg_tac>>rw[]>>gvs[SF DNF_ss,eval_iclin_term_CONS,EL_ZIP,EL_MAP]>>
  intLib.ARITH_TAC
QED

Definition encode_misc_constr_def:
  encode_misc_constr bnd c name =
  case c of
    Knapsack css Xs ts =>
    encode_knapsack css Xs ts name
  | _ => [] (* TODO *)
End

Theorem encode_misc_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Misc c) ∧
  misc_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_misc_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_misc_constr_def,misc_constr_sem_def]
  >-
    (drule encode_knapsack_sem_1>>rw[])
QED

Theorem encode_misc_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_misc_constr bnd c name) ⇒
  misc_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_misc_constr_def,misc_constr_sem_def]
  >-  cheat
  >- (
    irule encode_knapsack_sem_2>>
    gvs[]>>metis_tac[])
QED

(* Concrete encodings *)
Definition cencode_misc_constr_def:
  cencode_misc_constr bnd c name ec =
  case c of
    Knapsack css Xs ts =>
    (cencode_knapsack css Xs ts name, ec)
  | _ => (Nil,ec) (* TODO *)
End

Theorem cencode_misc_constr_sem:
  valid_assignment bnd wi ∧
  cencode_misc_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_misc_constr bnd c name) ec ec'
Proof
  Cases_on`c`>>
  rw[cencode_misc_constr_def,encode_misc_constr_def]
QED
