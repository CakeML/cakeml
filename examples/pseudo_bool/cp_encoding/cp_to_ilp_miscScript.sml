(*
  Formalization of the CP to ILP phase (misc constraints)
*)
Theory cp_to_ilp_misc
Libs
  preamble
Ancestors
  pbc cp ilp int_bitwiseExtra
  cp_to_ilp cp_to_ilp_linear cp_to_ilp_counting

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

(* The successor-iteration m ↦ (suc^m) 0 is injective on the domain {i | i < n}
   whenever suc maps the domain into itself and has no nontrivial cycle through
   any point (a return after 0 < k < n steps is impossible). Shared by
   circuit_sem_alt, circuit_sem_alt_strong and encode_circuit_sem_1. *)
Theorem FUNPOW_step_INJ:
  (∀i. i < n ⇒ suc i < n) ∧
  (∀i k. i < n ∧ 0 < k ∧ k < n ⇒ FUNPOW suc k i ≠ i) ⇒
  INJ (λm. FUNPOW suc m 0) (λi. i < n) (λi. i < n)
Proof
  strip_tac>>
  `∀j i. i < n ⇒ FUNPOW suc j i < n` by
    (Induct>>rw[FUNPOW_0,FUNPOW_SUC]>>metis_tac[])>>
  simp[INJ_DEF,IN_APP]>>
  ntac 3 strip_tac>>
  rename1`_ ⇒ i = j`>>
  simp[Once MONO_NOT_EQ]>>strip_tac>>
  wlog_tac `i < j` [`i`,`j`]
  >- (`j < i` by metis_tac[LESS_CASES_IMP]>>metis_tac[])>>
  `FUNPOW suc (j − i) (FUNPOW suc i 0) = FUNPOW suc j 0` by
    (simp[GSYM FUNPOW_ADD]>>AP_THM_TAC>>AP_TERM_TAC>>simp[])>>
  `FUNPOW suc i 0 < n` by (first_x_assum irule>>simp[])>>
  `FUNPOW suc (j − i) (FUNPOW suc i 0) ≠ FUNPOW suc i 0` by
    (first_x_assum irule>>simp[])>>
  metis_tac[]
QED

Theorem circuit_sem_alt:
  circuit_sem Xs w ⇔
  EVERY (λX. 0 ≤ varc w X ∧ Num (varc w X) < LENGTH Xs) Xs ∧
  ALL_DISTINCT (MAP (varc w) Xs) ∧
  ∃pos.
    pos 0 = 0 ∧
    (∀i. i < LENGTH Xs ⇒ pos i < LENGTH Xs) ∧
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
      fs[SURJ_DEF,IN_APP])
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
    strip_tac>>
    rename1‘pos 0 = 0’>>
    fs[EL_ALL_DISTINCT_EL_EQ,EL_MAP]>>
    ‘INJ suc dom dom’ by (
      rfs[INJ_DEF,IN_APP]>>
      rw[Abbr‘suc’]>>
      metis_tac[integerTheory.INT_OF_NUM])>>
    last_x_assum $ drule_then assume_tac>>
    ‘∀i j. dom i ⇒ pos (FUNPOW suc j i) = (pos i + j) MOD n’ by (
      Induct_on‘j’>>
      rw[FUNPOW_SUC,ADD1])>>
    ntac 3 strip_tac>>
    rename1‘FUNPOW _ j i ≠ i’>>
    first_x_assum $ drule_then assume_tac>>
    pop_assum $ qspec_then‘j’ assume_tac>>
    strip_tac>>
    ‘pos (FUNPOW suc j i) ≠ pos i’ suffices_by metis_tac[]>>
    simp[PLUS_MOD_NEQ])
QED

Theorem circuit_sem_alt_strong:
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

(* Position (Hamiltonian-cycle) constraints.
   pos i is the auxiliary binary integer (name,i) giving the position of node i
   in the traversal.

   We pin pos 0 = 0, keep every pos i ∈ [0,n-1], and reify the successor
   relation pos (Xs[i]) = (pos i + 1) MOD n :
     Xs[i] = 0  ⇒  pos i = n-1   (since pos 0 = 0)
     Xs[i] = j  ⇒  pos j = pos i + 1   (j ≠ 0) *)
Definition cencode_circuit_pos_def:
  cencode_circuit_pos bnd Xs name =
  let
    n = LENGTH Xs;
    n1 = n - 1
  in
    Append
      (* pos 0 = 0 *)
      (List [
        (SOME $ mk_name name
          («pos0eq0»),
        mk_ubnd_bin (ub_num name 0 n1) 0)])
      (* pos i < n for i = 0 to n-1 *)
      (Append (List
        (GENLIST
        (λi. SOME $ mk_name name
          («pos» ^ toString i ^ «lt» ^ toString n),
        mk_ubnd_bin (ub_num name i n1) (&n1)) n))
      (* for 0 ≤ i, j < n *)
      (flat_app (MAPi
        (λi X.
            (flat_app $ GENLIST
              (λj.
                let
                  cond = INL (Eq X (&j))
                in
                 List $ mk_annotate
                 [
                   mk_name name («pos_suc_» ^ toString i ^ «_» ^ toString j ^ «_ge»);
                   mk_name name («pos_suc_» ^ toString i ^ «_» ^ toString j ^ «_le»)
                 ]
                 (if j = 0
                 then
                   (* Xs[i] = 0  ⇒  pos i = n-1  *)
                   (MAP
                     (λcc. bits_imply bnd [Pos cond] cc)
                       (mk_bounds_bin (ub_num name i n1) (&n1) (&n1)))
                 else
                   (* Xs[i] = j  ⇒  pos j = pos i + 1 *)
                   [
                     bits_imply bnd [Pos cond] $
                       mk_constraint_ge_bin (-1) (ub_num name i n1) 1 (ub_num name j n1) 1;
                     bits_imply bnd [Pos cond] $
                       mk_constraint_ge_bin 1 (ub_num name i n1) (-1) (ub_num name j n1) (-1);
                   ]))
              n))
        Xs)))
End

(* The static circuit constraints:
     - every successor Xs[i] lies in [0, n-1];
     - the successors are all-distinct (reusing cencode_all_different), so they
       form a permutation of 0..n-1;
     - the positions form a single Hamiltonian cycle (cencode_circuit_pos). *)
Definition cencode_circuit_aux_def:
  cencode_circuit_aux bnd Xs name =
  let n = LENGTH Xs in
    Append
      (Append
        (flat_app (MAPi
          (λi X. List $ mk_annotate
            [
              mk_name name (toString i ^ «lb»);
              mk_name name (toString i ^ «ub»)
            ]
            (mk_bounds X 0 &(n - 1)))
          Xs))
        (cencode_all_different bnd Xs name))
      (cencode_circuit_pos bnd Xs name)
End

(* Add the reifications for all Xs *)
Definition cencode_circuit_def:
  cencode_circuit bnd Xs name ec =
  let n = LENGTH Xs in
  if n = 0 then (Nil, ec) else
  let (xs, ec') =
    fold_cenc
      (λX ec'. fold_cenc (λj ec. cencode_full_eq bnd X (&j) ec) (COUNT_LIST n) ec')
      Xs
      ec
  in
    (Append xs (cencode_circuit_aux bnd Xs name), ec')
End

Definition encode_circuit_def:
  encode_circuit bnd Xs name =
  let n = LENGTH Xs in
  if n = 0 then [] else
  (FLAT $ MAP
    (λX. FLAT $ GENLIST (λi. encode_full_eq bnd X (&i)) (LENGTH Xs))
    Xs) ++
  (abstr $ cencode_circuit_aux bnd Xs name)
End

Theorem cencode_circuit_sem:
  valid_assignment bnd wi ∧
  cencode_circuit bnd Xs name ec = (es, ec') ⇒
  enc_rel wi es (encode_circuit bnd Xs name) ec ec'
Proof
  simp[cencode_circuit_def,encode_circuit_def]>>
  IF_CASES_TAC>>
  rw[]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_abstr>>
  irule_at Any enc_rel_fold_cenc>>
  pop_assum (fn thm => irule_at Any thm)>>
  rw[]>>
  simp[GSYM MAP_COUNT_LIST]>>
  irule_at Any enc_rel_fold_cenc>>
  pop_assum (fn thm => irule_at Any thm)>>
  rw[]>>
  simp[enc_rel_encode_full_eq]
QED

Theorem pair_idfun:
  (λ(a,b). (a,b)) = I
Proof
  cong_tac NONE>>
  simp[]
QED

Theorem encode_circuit_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Misc (Circuit Xs)) ∧
  circuit_sem Xs wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_circuit bnd Xs name)
Proof
  strip_tac>>
  ‘∀i. i < LENGTH Xs ⇒ ∀n. 0 < n ∧ n < LENGTH Xs ⇒
    FUNPOW (λi. Num (varc wi $ EL i Xs)) n i ≠ i’ by fs[circuit_sem_def]>>
  ntac 3 (last_x_assum mp_tac)>>
  qmatch_asmsub_abbrev_tac‘Q’>>
  fs[circuit_sem_alt_strong,encode_circuit_def]>>
  IF_CASES_TAC>>
  fs[GSYM LENGTH_NON_NIL]>>
  qmatch_goalsub_abbrev_tac‘_ ⇒ P’>>
  simp[EVERY_MEM]>>
  rw[Abbr‘P’,EVERY_FLAT]
  >-((* reifications Xs[i]=j *)
    qmatch_goalsub_abbrev_tac‘EVERY P _’>>
    simp[EVERY_MAP]>>
    simp[EVERY_MEM]>>
    simp[Abbr‘P’,EVERY_FLAT,EVERY_GENLIST,reify_avar_def,reify_reif_def])>>
  simp[cencode_circuit_aux_def]>>
  rpt CONJ_TAC
  >-((* bounds 0 ≤ Xs[i] < n *)
    simp[mk_bounds_def,mk_annotate_def,o_ABS_R,EVERY_FLAT,EVERY_MAP]>>
    rw[EVERY_MEM,integerTheory.INT_GE,GSYM integerTheory.INT_NEG_MINUS1]>>
    last_assum $ drule_then mp_tac>>
    rename1‘0 ≤ a ∧ Num _ < b’>>
    simp[intLib.ARITH_PROVE“0 ≤ (a:int) ∧ Num a < (b:num) ⇒ a ≤ &(b − 1)”])
  >-((* all different Xs[i] = Xs[j] iff i = j
       should try to take advantage of what has been proved *)
    simp[cencode_all_different_def,
      cencode_all_different_except_aux_def,o_ABS_R,EVERY_FLAT]>>
    qmatch_goalsub_abbrev_tac‘EVERY P _’>>
    rw[EVERY_MEM,MEM_MAPi,SF DNF_ss]>>
    simp[Abbr‘P’,EVERY_FLAT]>>
    qmatch_goalsub_abbrev_tac‘EVERY P _’>>
    rw[EVERY_MEM,MEM_MAPi,SF DNF_ss]>>
    rw[Abbr‘P’,reify_avar_def,reify_flag_def,
      GSYM integerTheory.INT_NEG_MINUS1]>>
    ntac 4 (pop_assum mp_tac)>>
    simp[integerTheory.INT_GT,integerTheory.INT_NOT_LT,
      integerTheory.INT_GE,GSYM integerTheory.int_sub]>>
    qmatch_goalsub_abbrev_tac‘a - b’>>
    simp[intLib.ARITH_PROVE“1 ≤ (a:int) - b ⇔ b < a”]>>
    fs[integerTheory.INT_LT_LE,EL_ALL_DISTINCT_EL_EQ]>>
    rw[Abbr‘a’,Abbr‘b’]>>
    fs[EL_MAP])>>
  (* constraints on position variables *)
  fs[MEM_EL,SF DNF_ss,cencode_circuit_pos_def]>>
  qabbrev_tac‘n = LENGTH Xs’>>
  qabbrev_tac‘dom = (λi. i < n)’>>
  qabbrev_tac‘suc = λm. Num (varc wi $ EL m Xs)’>>
  qabbrev_tac‘step = (λm. FUNPOW suc m 0)’>>
  fs[]>>
  ‘∀i. dom i ⇒
    eval_lin_term
      (reify_avar cs wi)
      (ub_num name i (n − 1)) = &pos i’ by (
    rw[ub_num_num_of_bits,reify_avar_def,reify_flag_def]>>
    qmatch_goalsub_abbrev_tac‘BIT _ m’>>
    qmatch_goalsub_abbrev_tac‘num_of_bits (GENLIST f _) = p’>>
    ‘FINITE dom’ by (
      ‘dom = count n’ by simp[Abbr‘dom’,EXTENSION,IN_COUNT]>>
      simp[])>>
    ‘INJ step dom dom’ by (
      simp[Abbr‘step’,Abbr‘dom’]>>
      irule FUNPOW_step_INJ>>
      metis_tac[])>>
    ‘SURJ step dom dom’ by fs[FINITE_INJ_IMP_SURJ]>>
    fs[INJ_DEF,SURJ_DEF,IN_APP]>>
    ‘∀i. dom i ⇒ pos (step i) = i’ by (
      ‘∀i. dom (SUC i) ⇒ dom i’ by rw[ADD1,Abbr‘dom’]>>
      simp[Abbr‘step’]>>
      Induct>>
      simp[FUNPOW_SUC]>>
      strip_tac>>
      fs[ADD1])>>
    ‘m ≤ n - 1’ by (
      simp[Abbr‘m’]>>
      SELECT_ELIM_TAC>>
      simp[Abbr‘dom’])>>
    ‘m = p’ by (
      first_assum $ drule_then assume_tac>>
      fs[Abbr‘m’,Abbr‘p’]>>
      SELECT_ELIM_TAC>>
      metis_tac[])>>
    ‘m < 2 ** LENGTH (bits_of_num (n − 1))’ by
      metis_tac[LESS_LENGTH_bits_of_num,LESS_EQ_LESS_TRANS]>>
    simp[Abbr‘f’,num_of_bits_GENLIST_BIT]>>
    gvs[LESS_MOD])>>
  rpt CONJ_TAC
  >-simp[iconstraint_sem_def,ub_num_neg]
  >-simp[EVERY_MAP,EVERY_GENLIST,iconstraint_sem_def,
      ub_num_neg,integerTheory.INT_GE,SUB_LESS_OR_EQ]
  >-(
    last_x_assum kall_tac>>
    simp[o_ABS_R,EVERY_FLAT]>>
    qmatch_goalsub_abbrev_tac‘EVERY P _’>>
    rw[EVERY_MEM,MEM_MAPi,SF DNF_ss]>>
    simp[Abbr‘P’,EVERY_FLAT,EVERY_MAP,EVERY_GENLIST]>>
    simp[COND_RAND,pair_idfun,iconstraint_sem_def,GSYM IMP_CONJ_THM,ub_num_neg,
      reify_avar_def,reify_reif_def,integerTheory.INT_GE]>>
    strip_tac>>
    rename1‘if j = _ then _ _ (_ i _) = _ ⇒ _ else _’>>
    qmatch_goalsub_abbrev_tac‘if _ then P1 ⇒ Q1 else _ ⇒ P2 ⇒ Q2’>>
    ‘P1 ⇔ suc i = 0’ by simp[Abbr‘P1’,Abbr‘suc’]>>
    ‘P2 ⇔ suc i = j’ by simp[Abbr‘P2’,Abbr‘suc’,Abbr‘dom’,
      intLib.ARITH_PROVE“0 ≤ a ⇒ (a = &b ⇔ Num a = b)”]>>
    ‘Q1 ⇔ pos i + 1 = n’ by (
      last_x_assum mp_tac>>
      simp[Abbr‘dom’,Abbr‘Q1’,])>>
    ‘Q2 ⇔ pos i + 1 = pos j’ by (
      simp[Abbr‘Q2’]>>
      rename1‘a + _ = b’>>
      simp[intLib.ARITH_PROVE“1 ≤ -&a + &b ∧ -1 ≤ &a + -&b ⇔ a + 1 = b”])>>
    rfs[Abbr‘dom’]>>
    first_x_assum $ drule_then kall_tac>>
    first_x_assum $ drule_then mp_tac>>
    last_x_assum mp_tac>>
    strip_tac>>strip_tac>>
    `∀a b. a < n ∧ b < n ⇒ (pos a = pos b ⇔ a = b)` by
      (qpat_x_assum`ALL_DISTINCT (GENLIST _ _)` mp_tac>>
       simp[EL_ALL_DISTINCT_EL_EQ,EL_GENLIST])>>
    `pos i < n ∧ suc i < n` by metis_tac[]>>
    `pos (suc i) = if pos i + 1 = n then 0 else pos i + 1` by
      (IF_CASES_TAC>>gvs[arithmeticTheory.LESS_MOD,arithmeticTheory.DIVMOD_ID])>>
    rw[]>>gvs[]>>metis_tac[])
QED

Theorem encode_circuit_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_circuit bnd Xs name) ⇒
  circuit_sem Xs wi
Proof
  strip_tac>>
  Cases_on`Xs = []`
  >- gvs[circuit_sem_def]>>
  `0 < LENGTH Xs` by (Cases_on`Xs`>>gvs[])>>
  gvs[encode_circuit_def,cencode_circuit_aux_def,append_thm,EVERY_APPEND]>>
  simp[circuit_sem_alt]>>
  rpt conj_tac
  >- ( (* bounds 0 ≤ Xs[i] < n *)
    qpat_x_assum`EVERY _ (FLAT (MAPi _ Xs))` mp_tac>>
    simp[EVERY_FLAT,EVERY_MEM,MEM_MAPi,PULL_EXISTS,o_DEF]>>
    strip_tac>>
    `∀m. m < LENGTH Xs ⇒
       0 ≤ varc wi (EL m Xs) ∧ varc wi (EL m Xs) ≤ &(LENGTH Xs − 1)` by (
      rw[]>>first_x_assum drule>>
      simp[GSYM EVERY_MEM,integerTheory.INT_GE])>>
    rw[]>>gvs[MEM_EL]>>
    first_x_assum drule>>strip_tac>>
    intLib.ARITH_TAC)
  >- ( (* ALL_DISTINCT: reuse all_different_except soundness with iS = [] *)
    `all_different_except_sem Xs [] wi` suffices_by
      simp[all_different_except_sem_def]>>
    irule encode_all_different_except_aux_sem_2>>
    gvs[encode_all_different_except_aux_def,cencode_all_different_def]>>
    metis_tac[])
  >- ( (* ∃pos *)
    qabbrev_tac`pos = λi. num_of_bits
      (GENLIST (λb. wb (neiv name i b (SOME «bin»)))
        (LENGTH (bits_of_num (LENGTH Xs − 1))))`>>
    `∀i. eval_lin_term wb (ub_num name i (LENGTH Xs − 1)) = &(pos i)` by
      simp[Abbr`pos`,ub_num_num_of_bits]>>
    qexists`pos`>>
    qpat_x_assum`EVERY _ (abstr (cencode_circuit_pos _ _ _))` mp_tac>>
    simp[cencode_circuit_pos_def,append_thm,EVERY_APPEND]>>
    strip_tac>>
    (* pos 0 = 0 from the pos0eq0 constraint *)
    `pos 0 = 0` by (
      qpat_x_assum`_ ≥ 0` mp_tac>>
      simp[iconstraint_sem_def,ub_num_neg]>>gs[]>>strip_tac>>
      gs[integerTheory.INT_GE,integerTheory.INT_NEG_GE0,
        integerTheory.INT_OF_NUM_LE])>>
    (* pos m < n from the pos<n constraints *)
    `∀m. m < LENGTH Xs ⇒ pos m < LENGTH Xs` by (
      rw[]>>
      qpat_x_assum`EVERY _ (abstrl (GENLIST _ _))` mp_tac>>
      simp[EVERY_MAP,EVERY_GENLIST,iconstraint_sem_def,ub_num_neg]>>
      strip_tac>>first_x_assum drule>>
      gs[integerTheory.INT_GE,integerTheory.INT_LE_NEG,
        integerTheory.INT_OF_NUM_LE])>>
    (* reification consistency for Xs[i] = j, from encode_full_eq *)
    `∀X j. MEM X Xs ∧ j < LENGTH Xs ⇒
       (wb (INL (Eq X (&j))) ⇔ varc wi X = &j)` by (
      qpat_x_assum`EVERY _ (FLAT (MAP _ Xs))` mp_tac>>
      simp[EVERY_FLAT,EVERY_MAP,EVERY_GENLIST,EVERY_MEM]>>
      rw[]>>first_x_assum drule_all>>simp[])>>
    (* range bounds 0 ≤ Xs[m] ≤ n-1 *)
    `∀m. m < LENGTH Xs ⇒
       0 ≤ varc wi (EL m Xs) ∧ varc wi (EL m Xs) ≤ &(LENGTH Xs − 1)` by (
      qpat_x_assum`EVERY _ (FLAT (MAPi ($o _ ∘ (λi X. List _)) Xs))` mp_tac>>
      simp[EVERY_FLAT,EVERY_MEM,MEM_MAPi,PULL_EXISTS,o_DEF]>>
      rw[]>>first_x_assum drule>>
      simp[GSYM EVERY_MEM,integerTheory.INT_GE])>>
    (* the bulky constraint assumptions are spent; drop them so the
       remaining simplification stays cheap *)
    qpat_x_assum`EVERY _ (FLAT (MAP _ Xs))` kall_tac>>
    qpat_x_assum`EVERY _ (abstrl (GENLIST _ _))` kall_tac>>
    qpat_x_assum`EVERY _ (FLAT (MAPi ($o _ ∘ (λi X. List _)) Xs))` kall_tac>>
    qpat_x_assum`_ ≥ 0` kall_tac>>
    simp[]
    >- ((* successor: pos (Xs[i]) = (pos i + 1) MOD n *)
      rw[]>>
      `varc wi (EL i Xs) = &(Num (varc wi (EL i Xs)))` by
        metis_tac[integerTheory.INT_OF_NUM]>>
      qabbrev_tac`v = Num (varc wi (EL i Xs))`>>
      `v < LENGTH Xs` by
        (`&v ≤ &(LENGTH Xs - 1)` by metis_tac[]>>gs[integerTheory.INT_OF_NUM_LE])>>
      `wb (INL (Eq (EL i Xs) (&v)))` by
        (last_x_assum(qspecl_then[`EL i Xs`,`v`]mp_tac)>>simp[MEM_EL]>>metis_tac[])>>
      `pos v < LENGTH Xs ∧ pos i < LENGTH Xs` by metis_tac[]>>
      qpat_x_assum`EVERY _ (FLAT (MAPi ($o _ ∘ (λi X. flat_app _)) Xs))` mp_tac>>
      simp[EVERY_FLAT,EVERY_MEM,MEM_MAPi,PULL_EXISTS,o_DEF,append_thm,
        abstrl_mk_annotate]>>
      disch_then(qspec_then`i`mp_tac)>>
      simp[MEM_FLAT,MEM_MAP,MEM_GENLIST,PULL_EXISTS,append_thm,abstrl_mk_annotate]>>
      disch_then(fn th => mp_tac (Q.SPEC`v` (CONV_RULE SWAP_FORALL_CONV th)))>>
      simp[]>>
      strip_tac>>Cases_on`v`>>
      qpat_x_assum`∀x. MEM x _ ⇒ _`mp_tac>>
      simp[DISJ_IMP_THM,FORALL_AND_THM,bits_imply_sem,iconstraint_sem_def,
        pbcTheory.eval_lin_term_append,pair_idfun,ub_num_neg]>>
      strip_tac
      >~ [`pos (SUC _) = _`]
      >- ((* Xs[i] = v+1: pos (v+1) = pos i + 1, in range *)
        `pos (SUC n) = pos i + 1` by (
          qpat_x_assum`-&pos i + &pos (SUC n) ≥ 1`mp_tac>>
          qpat_x_assum`&pos i + -&pos (SUC n) ≥ -1`mp_tac>>
          rpt (pop_assum kall_tac)>>intLib.ARITH_TAC)>>
        simp[arithmeticTheory.LESS_MOD])>>
      (* Xs[i] = 0: pos i = n-1, so (pos i + 1) MOD n = 0 *)
      gs[integerTheory.INT_GE,integerTheory.INT_LE_NEG,integerTheory.INT_OF_NUM_LE]>>
      `pos i + 1 = LENGTH Xs` by (
        `0 < LENGTH Xs` by (Cases_on`Xs`>>fs[])>>
        qpat_x_assum`LENGTH Xs ≤ pos i + 1`mp_tac>>
        qpat_x_assum`pos i ≤ LENGTH Xs − 1`mp_tac>>
        qpat_x_assum`0 < LENGTH Xs`mp_tac>>
        rpt (pop_assum kall_tac)>>intLib.ARITH_TAC)>>
      simp[arithmeticTheory.DIVMOD_ID]))
QED

Definition cencode_knapsack1_def:
  cencode_knapsack1 name (n:num) Xs cs t =
  List (cmk_lin_eq name (toString n ^ «_») (ZIP(cs,Xs)) t)
End

Definition cencode_knapsack_def:
  cencode_knapsack css Xs Ts name =
  let lxs = LENGTH Xs in
  if
    EVERY (λcs. LENGTH cs = lxs) css ∧
    LENGTH Ts = LENGTH css
  then
    flat_app (MAPi (λn (cs,t). cencode_knapsack1 name n Xs cs t) (ZIP (css,Ts)))
  else
    cfalse_constr
End

Definition encode_knapsack_def:
  encode_knapsack css Xs Ts name =
  abstr $ cencode_knapsack css Xs Ts name
End

Theorem encode_knapsack_sem_1:
  knapsack_sem css Xs Ts wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_knapsack css Xs Ts name)
Proof
  rw[cencode_knapsack_def,encode_knapsack_def,knapsack_sem_def]>>
  gvs[LIST_REL_EL_EQN,EVERY_FLAT,EVERY_MEM,MEM_MAPi,
    PULL_EXISTS,cencode_knapsack1_def]>>
  rw[]>>
  pairarg_tac>>gvs[eval_iclin_term_CONS,EL_ZIP,EL_MAP]>>
  first_x_assum drule_all>>
  intLib.ARITH_TAC
QED

Theorem encode_knapsack_sem_2:
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_knapsack css Xs Ts name) ⇒
  knapsack_sem css Xs Ts wi
Proof
  rw[cencode_knapsack_def,encode_knapsack_def,knapsack_sem_def]>>
  gvs[LIST_REL_EL_EQN,EVERY_FLAT,EVERY_MEM,MEM_MAPi,
    PULL_EXISTS,cencode_knapsack1_def,cfalse_constr_def]>>
  rw[]>>first_x_assum drule>>
  pairarg_tac>>rw[]>>gvs[SF DNF_ss,eval_iclin_term_CONS,EL_ZIP,EL_MAP]>>
  intLib.ARITH_TAC
QED

(* --- MinDistance ---
   Mirrors GCS's MinDistance::define_proof_model group-for-group
   (gcs/constraints/min_distance/min_distance.cc:120-266); every filtering
   conditional below is ported from the corresponding C++ guard, not
   invented, per the request doc's steer to match GCS's actual
   implementation. *)

Definition varc_lb_def:
  varc_lb bnd (Z:'a varc) = case Z of INL z => FST (bnd z) | INR c => c
End

Definition varc_ub_def:
  varc_ub bnd (Z:'a varc) = case Z of INL z => SND (bnd z) | INR c => c
End

(* candidate sites: those reachable by some position's declared domain
   (mirrors GCS's is_site[]/_sites, built once from initial domains in
   prepare() — a fixed set, never re-derived from a narrowed state) *)
Definition md_sites_def:
  md_sites bnd Xs (n:num) =
  FILTER (λa. EXISTS (λX. MEM a (domlist bnd X)) Xs) (GENLIST (λa. &a) n)
End

Definition md_positions_at_def:
  md_positions_at bnd Xs (a:int) = FILTER (λX. MEM a (domlist bnd X)) Xs
End

(* all a<b pairs drawn from a (sorted, distinct) candidate-sites list *)
Definition md_site_pairs_def:
  md_site_pairs (sites:int list) =
  FLAT (MAPi (λi a. MAP (λb. (a,b)) (DROP (i+1) sites)) sites)
End

(* {0} ∪ {D[a,b] : a<b candidate}, sorted and deduplicated *)
Definition md_levels_def:
  md_levels D (sites:int list) =
  QSORT $<=
    (nub (0i :: MAP (λp. dist_at D (Num (FST p)) (Num (SND p))) (md_site_pairs sites)))
End

Definition md_u_flag_def[simp]:
  md_u_flag name (a:int) = INR (name, Values [a] (SOME «u»))
End

Definition md_d_flag_def[simp]:
  md_d_flag name (a:int) = INR (name, Values [a] (SOME «d»))
End

Definition md_w_flag_def[simp]:
  md_w_flag name (a:int) (b:int) = INR (name, Values [a;b] (SOME «w»))
End

Definition md_m_flag_def[simp]:
  md_m_flag name (t:int) = INR (name, Values [t] (SOME «m»))
End

(* witnesses at exactly distance t: duplicates (only meaningful at t=0,
   the unique value a duplicate can attain, since D's diagonal is zero)
   and off-diagonal candidate pairs at distance exactly t *)
Definition md_witnesses_at_def:
  md_witnesses_at bnd Xs name (sites:int list) D (t:int) =
  (if t = 0 then
     MAP (md_d_flag name)
       (FILTER (λa. LENGTH (md_positions_at bnd Xs a) ≥ 2) sites)
   else []) ++
  MAP (λp. md_w_flag name (FST p) (SND p))
    (FILTER (λp. dist_at D (Num (FST p)) (Num (SND p)) = t) (md_site_pairs sites))
End

(* Group (i): site-used flags, u_a ⇔ count_a ≥ 1 *)
Definition cencode_md_u_def:
  cencode_md_u bnd Xs name (a:int) =
  cbimply_var bnd (md_u_flag name a)
    ([], MAP (λX. (1i,Pos (INL (Eq X a)))) (md_positions_at bnd Xs a), 1)
End

Definition cencode_md_us_def:
  cencode_md_us bnd Xs name (sites:int list) =
  flat_app (MAP (cencode_md_u bnd Xs name) sites)
End

(* Group (ii): duplicate bound at site a *)
Definition cencode_md_dup_def:
  cencode_md_dup bnd Xs Z name (a:int) =
  let pos = md_positions_at bnd Xs a in
  let cnt = MAP (λX. (-1i,Pos (INL (Eq X a)))) pos in
  if LENGTH pos < 2 then Nil
  else if varc_ub bnd Z ≤ 0 then Nil
  else if varc_lb bnd Z ≥ 1 then
    List [(SOME (mk_name name (int_to_string #"-" a ^ «_am1»)), ([], cnt, -1))]
  else
    let p = &LENGTH Xs : int in
    List [(SOME (mk_name name (int_to_string #"-" a ^ «_dupbnd»)),
           ([], cnt ++ [(-(p-1), Pos (INL (Ge Z 1)))], -p))]
End

Definition cencode_md_dups_def:
  cencode_md_dups bnd Xs Z name (sites:int list) =
  flat_app (MAP (cencode_md_dup bnd Xs Z name) sites)
End

(* Group (ii-b): fully reify d_a ⇔ count_a ≥ 2, for every site that can
   actually carry a duplicate; this is what md_witnesses_at's t=0 case
   relies on to be a genuine reification rather than a free proof var *)
Definition cencode_md_d_def:
  cencode_md_d bnd Xs name (a:int) =
  cbimply_var bnd (md_d_flag name a)
    ([], MAP (λX. (1i,Pos (INL (Eq X a)))) (md_positions_at bnd Xs a), 2)
End

Definition cencode_md_ds_def:
  cencode_md_ds bnd Xs name (sites:int list) =
  flat_app (MAP (cencode_md_d bnd Xs name)
    (FILTER (λa. LENGTH (md_positions_at bnd Xs a) ≥ 2) sites))
End

(* Group (ii-c): fully reify w_ab ⇔ u_a ∧ u_b for every candidate pair,
   the AND special case of cbimply_var (threshold 2 over 2 bits); needed
   since md_witnesses_at's t≠0 case relies on w_ab meaning exactly that *)
Definition cencode_md_w_def:
  cencode_md_w bnd name (p:int#int) =
  let (a,b) = p in
  cbimply_var bnd (md_w_flag name a b)
    ([], [(1i,Pos (md_u_flag name a)); (1i,Pos (md_u_flag name b))], 2)
End

Definition cencode_md_ws_def:
  cencode_md_ws bnd name (sites:int list) =
  flat_app (MAP (cencode_md_w bnd name) (md_site_pairs sites))
End

(* Group (iii): pair upper bounds, ¬u_a ∨ ¬u_b ∨ [z≤D[a,b]] *)
Definition cencode_md_pair_ub_def:
  cencode_md_pair_ub bnd D Z name (p:int#int) =
  let (a,b) = p in
  let dab = dist_at D (Num a) (Num b) in
  if varc_ub bnd Z ≤ dab then Nil
  else
    List [(SOME (mk_name name
             (int_to_string #"-" a ^ «_» ^ int_to_string #"-" b ^ «_pairub»)),
           ([], MAP (λl. (1i,l))
             [Neg (md_u_flag name a); Neg (md_u_flag name b);
              Neg (INL (Ge Z (dab+1)))], 1))]
End

Definition cencode_md_pair_ubs_def:
  cencode_md_pair_ubs bnd D Z name (sites:int list) =
  flat_app (MAP (cencode_md_pair_ub bnd D Z name) (md_site_pairs sites))
End

(* Group (iv): the ladder. prev is the previous level's accumulator flag
   (NONE at the bottom); at each level we may emit the guarded clause
   [z≥t] ∨ prev, then (unless this is the top level) fully reify a fresh
   accumulator flag as prev ∨ (witnesses at exactly t). *)
Definition cencode_md_ladder_aux_def:
  (cencode_md_ladder_aux bnd Xs Z name sites D prev [] = Nil) ∧
  (cencode_md_ladder_aux bnd Xs Z name sites D prev (t::ts) =
    let prev_lits = case prev of NONE => [] | SOME f => [Pos f] in
    let clause =
      if varc_lb bnd Z < t then
        List [(SOME (mk_name name (int_to_string #"-" t ^ «_lad»)),
               ([], MAP (λl. (1i,l)) (Pos (INL (Ge Z t)) :: prev_lits), 1))]
      else Nil
    in
    if NULL ts then clause
    else
      let ws = md_witnesses_at bnd Xs name sites D t in
      let new_flag = md_m_flag name t in
      let reif_row =
        cbimply_var bnd new_flag
          ([], MAP (λl. (1i,l)) (prev_lits ++ MAP Pos ws), 1)
      in
      Append clause
        (Append reif_row
          (cencode_md_ladder_aux bnd Xs Z name sites D (SOME new_flag) ts)))
End

Definition cencode_md_ladder_def:
  cencode_md_ladder bnd Xs Z name sites D (levels:int list) =
  cencode_md_ladder_aux bnd Xs Z name sites D NONE levels
End

(* Group (v): requirement clauses, when R is given: for each i<j with
   candidate values a for Xs[i], b for Xs[j] and D[a,b] < R[i][j],
   Xs[i]≠a ∨ Xs[j]≠b (this includes a=b, since D[a,a]=0 can be < R[i][j]) *)
Definition cencode_md_req_ij_def:
  cencode_md_req_ij bnd D Xi Xj (rij:int) name (i:num) (j:num) =
  flat_app (FLAT (MAP (λa.
    MAP (λb.
      if dist_at D (Num a) (Num b) < rij then
        List [(SOME (mk_name name
                 (toString i ^ «_» ^ toString j ^ «_» ^
                  int_to_string #"-" a ^ «_» ^ int_to_string #"-" b ^ «_req»)),
               ([], MAP (λl. (1i,l))
                 [Neg (INL (Eq Xi a)); Neg (INL (Eq Xj b))], 1))]
      else Nil)
    (domlist bnd Xj))
  (domlist bnd Xi)))
End

Definition cencode_md_reqs_def:
  cencode_md_reqs bnd Xs D (Ropt:(int list list) option) name =
  case Ropt of
    NONE => Nil
  | SOME Rm =>
    flat_app (FLAT (MAPi (λi Xi.
      FLAT (MAPi (λj Xj.
        if i < j then
          [cencode_md_req_ij bnd D Xi Xj (EL j (EL i Rm)) name i j]
        else []
      ) Xs)
    ) Xs))
End

(* the Ge Z atoms every group above references: every level (for the
   ladder's own [z≥t] clauses) and every level-plus-one (covering both
   group (iii)'s [z≤D[a,b]] = ¬[z≥D[a,b]+1], since every D[a,b] is itself
   a level, and group (ii)'s [z≥1], since 0 is always a level) *)
Definition md_ge_values_def:
  md_ge_values (levels:int list) = levels ++ MAP (λt. t+1) levels
End

(* well-formedness guard shared by encode/cencode; rejected exactly as
   GCS rejects it at post time (non-square/symmetric/zero-diag/negative D,
   bad R shape, p<2 — see min_distance.cc's constructor validation) *)
Definition min_distance_ok_def:
  min_distance_ok Xs D (Ropt:(int list list) option) ⇔
  2 ≤ LENGTH Xs ∧ dist_matrix_ok D ∧
  (case Ropt of
     NONE => T
   | SOME R => LENGTH R = LENGTH Xs ∧ EVERY (λrow. LENGTH row = LENGTH Xs) R)
End

Definition encode_min_distance_def:
  encode_min_distance bnd Xs D Z Ropt name =
  if min_distance_ok Xs D Ropt then
    let n = LENGTH D in
    let sites = md_sites bnd Xs n in
    let levels = md_levels D sites in
    encode_eq_grid bnd Xs sites ++
    FLAT (MAP (λv. encode_ge bnd Z v) (md_ge_values levels)) ++
    abstr (cencode_md_us bnd Xs name sites) ++
    abstr (cencode_md_ds bnd Xs name sites) ++
    abstr (cencode_md_ws bnd name sites) ++
    abstr (cencode_md_dups bnd Xs Z name sites) ++
    abstr (cencode_md_pair_ubs bnd D Z name sites) ++
    abstr (cencode_md_ladder bnd Xs Z name sites D levels) ++
    abstr (cencode_md_reqs bnd Xs D Ropt name)
  else [false_constr]
End

Definition cencode_min_distance_def:
  cencode_min_distance bnd Xs D Z Ropt name ec =
  if min_distance_ok Xs D Ropt then
    let n = LENGTH D in
    let sites = md_sites bnd Xs n in
    let levels = md_levels D sites in
    let (eqs,ec') = cencode_eq_grid bnd Xs sites ec in
    let (ges,ec'') = fold_cenc (λv ec. cencode_ge bnd Z v ec) (md_ge_values levels) ec' in
    (Append eqs
      (Append ges
      (Append (cencode_md_us bnd Xs name sites)
      (Append (cencode_md_ds bnd Xs name sites)
      (Append (cencode_md_ws bnd name sites)
      (Append (cencode_md_dups bnd Xs Z name sites)
      (Append (cencode_md_pair_ubs bnd D Z name sites)
      (Append (cencode_md_ladder bnd Xs Z name sites D levels)
              (cencode_md_reqs bnd Xs D Ropt name)))))))), ec'')
  else (cfalse_constr, ec)
End

(* --- MinDistance correctness --- *)

Theorem transitive_int_le[local]:
  transitive ((<=):int->int->bool)
Proof
  rw[relationTheory.transitive_def]>>intLib.ARITH_TAC
QED

Theorem SORTED_int_le_GENLIST[local]:
  SORTED $<= (GENLIST (λa:num. &a) n)
Proof
  simp[MATCH_MP SORTED_EL_LESS transitive_int_le]>>
  rw[]>>
  DEP_REWRITE_TAC[EL_GENLIST]>>
  gs[]>>
  intLib.ARITH_TAC
QED

Theorem SORTED_md_sites[simp]:
  SORTED $<= (md_sites bnd Xs n)
Proof
  rw[md_sites_def]>>
  irule SORTED_FILTER>>
  simp[transitive_int_le,SORTED_int_le_GENLIST]
QED

Theorem ALL_DISTINCT_md_sites[simp]:
  ALL_DISTINCT (md_sites bnd Xs n)
Proof
  rw[md_sites_def]>>
  irule FILTER_ALL_DISTINCT>>
  simp[ALL_DISTINCT_GENLIST]
QED

Theorem MEM_md_sites_bound:
  MEM a (md_sites bnd Xs n) ⇒ 0 ≤ a ∧ Num a < n
Proof
  rw[md_sites_def,MEM_FILTER,MEM_GENLIST]>>
  intLib.ARITH_TAC
QED

Theorem SORTED_md_levels[simp]:
  SORTED $<= (md_levels D sites)
Proof
  rw[md_levels_def]>>
  irule QSORT_SORTED>>
  simp[transitive_int_le,relationTheory.total_def]>>
  intLib.ARITH_TAC
QED

Theorem ALL_DISTINCT_md_levels[simp]:
  ALL_DISTINCT (md_levels D sites)
Proof
  rw[md_levels_def]>>
  metis_tac[ALL_DISTINCT_PERM,QSORT_PERM,all_distinct_nub]
QED

Theorem MEM_md_levels:
  MEM t (md_levels D sites) ⇔
  t = 0 ∨
  ∃p. MEM p (md_site_pairs sites) ∧
      t = dist_at D (Num (FST p)) (Num (SND p))
Proof
  simp[md_levels_def]>>
  qmatch_goalsub_abbrev_tac ‘MEM t (QSORT _ ls)’>>
  ‘MEM t (QSORT $<= ls) = MEM t ls’ by metis_tac[QSORT_PERM,MEM_PERM]>>
  simp[Abbr‘ls’,MEM_nub,MEM_MAP]>>
  metis_tac[]
QED

Theorem MEM_md_site_pairs:
  MEM (x,y) (md_site_pairs l) ⇔
  ∃i j. i < j ∧ j < LENGTH l ∧ x = EL i l ∧ y = EL j l
Proof
  simp[md_site_pairs_def,MEM_FLAT,MEM_MAPi,PULL_EXISTS,MEM_MAP,MEM_DROP]>>
  eq_tac
  >- (
    rw[]>>
    qexists_tac ‘i’>>
    qexists_tac ‘i + (m + 1)’>>
    simp[])>>
  rw[]>>
  qexists_tac ‘i’>>
  qexists_tac ‘j - i - 1’>>
  ‘i + (j - i - 1 + 1) = j’ by decide_tac>>
  simp[]
QED

Theorem md_site_pairs_complete:
  SORTED $<= sites ∧ ALL_DISTINCT sites ∧
  MEM a sites ∧ MEM b sites ∧ a < b ⇒
  MEM (a,b) (md_site_pairs sites)
Proof
  rw[MEM_md_site_pairs]>>
  gs[MEM_EL]>>
  rename1 ‘a = EL i sites’>>rename1 ‘b = EL j sites’>>
  ‘i ≠ j’ by (strip_tac>>gvs[]>>intLib.ARITH_TAC)>>
  Cases_on ‘i < j’
  >- metis_tac[]>>
  ‘j < i’ by simp[]>>
  qspec_then ‘sites’ mp_tac (MATCH_MP SORTED_EL_LESS transitive_int_le)>>
  simp[]>>
  disch_then (qspecl_then [‘j’,‘i’] mp_tac)>>
  simp[]>>
  strip_tac>>
  ‘F’ by intLib.ARITH_TAC>>
  fs[]
QED

Theorem dist_at_sym:
  dist_matrix_ok D ∧ a < LENGTH D ∧ b < LENGTH D ⇒
  dist_at D a b = dist_at D b a
Proof
  rw[dist_matrix_ok_def,dist_at_def]
QED

Theorem md_positions_at_FILTER[simp]:
  valid_assignment bnd wi ⇒
  FILTER (λX. varc wi X = a) (md_positions_at bnd Xs a) =
  FILTER (λX. varc wi X = a) Xs
Proof
  strip_tac>>
  Induct_on ‘Xs’>>rw[md_positions_at_def]>>
  gvs[md_positions_at_def]>>
  metis_tac[MEM_domlist]
QED

Theorem md_sites_complete:
  valid_assignment bnd wi ∧ MEM X Xs ∧ 0 ≤ varc wi X ∧ Num (varc wi X) < n ⇒
  MEM (varc wi X) (md_sites bnd Xs n)
Proof
  rw[md_sites_def,MEM_FILTER,MEM_GENLIST]
  >- (
    simp[EXISTS_MEM]>>
    qexists_tac ‘X’>>
    simp[]>>
    metis_tac[MEM_domlist])>>
  qexists_tac ‘Num (varc wi X)’>>
  intLib.ARITH_TAC
QED

Theorem eval_lin_term_ones[local]:
  ∀L g. eval_lin_term wb (MAP (λx.(1i,g x)) L) = iSUM (MAP (λx. b2i (lit wb (g x))) L)
Proof
  simp[eval_lin_term_def,MAP_MAP_o,combinTheory.o_DEF,eval_term_def,eval_lit_def]
QED

(* Group (i): u_a's row-sem, over an arbitrary satisfying wb that agrees
   with the semantics on the Eq atoms this row uses *)
Theorem cencode_md_u_sem:
  valid_assignment bnd wi ∧
  (∀X. MEM X Xs ⇒ (wb (INL (Eq X a)) ⇔ varc wi X = a)) ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (cencode_md_u bnd Xs name a)) ⇔
   (wb (md_u_flag name a) ⇔ ∃X. MEM X Xs ∧ varc wi X = a))
Proof
  rw[cencode_md_u_def]>>
  simp[lin_ge_sem,eval_lin_term_ones]>>
  ‘(∃X. MEM X (md_positions_at bnd Xs a) ∧ lit wb (Pos (INL (Eq X a)))) ⇔
   (∃X. MEM X Xs ∧ varc wi X = a)’ by (
    simp[md_positions_at_def,MEM_FILTER]>>
    eq_tac>>rw[]>>
    metis_tac[MEM_domlist])>>
  gvs[]>>
  metis_tac[]
QED

Theorem FILTER_MEM_CONG[local]:
  (∀x. MEM x l ⇒ (P x ⇔ Q x)) ⇒ FILTER P l = FILTER Q l
Proof
  Induct_on ‘l’>>rw[]>>metis_tac[]
QED

(* Group (ii-b): d_a's row-sem *)
Theorem iSUM_MAP_b2i_FILTER[local]:
  iSUM (MAP (λx. b2i (P x)) ls) = &(LENGTH (FILTER P ls))
Proof
  simp[GSYM iSUM_FILTER,combinTheory.o_DEF]
QED

Theorem cencode_md_d_sem:
  valid_assignment bnd wi ∧
  (∀X. MEM X Xs ⇒ (wb (INL (Eq X a)) ⇔ varc wi X = a)) ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (cencode_md_d bnd Xs name a)) ⇔
   (wb (md_d_flag name a) ⇔ 2 ≤ LENGTH (FILTER (λX. varc wi X = a) Xs)))
Proof
  rw[cencode_md_d_def]>>
  simp[lin_ge_sem,eval_lin_term_ones,iSUM_MAP_b2i_FILTER]>>
  ‘FILTER (λX. wb (INL (Eq X a))) (md_positions_at bnd Xs a) =
   FILTER (λX. varc wi X = a) Xs’ by (
    ‘FILTER (λX. wb (INL (Eq X a))) (md_positions_at bnd Xs a) =
     FILTER (λX. varc wi X = a) (md_positions_at bnd Xs a)’ by (
      irule FILTER_MEM_CONG>>
      simp[md_positions_at_def,MEM_FILTER]>>
      metis_tac[])>>
    simp[])>>
  simp[]>>
  Cases_on ‘wb (INR (name,Values [a] (SOME «d»)))’>>gvs[]>>
  intLib.ARITH_TAC
QED

(* Group (ii-c): w_ab's row-sem *)
Theorem cencode_md_w_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (cencode_md_w bnd name (a,b))) ⇔
   (wb (md_w_flag name a b) ⇔ wb (md_u_flag name a) ∧ wb (md_u_flag name b)))
Proof
  rw[cencode_md_w_def]>>
  simp[lin_ge_sem,eval_lin_term_def,iSUM_def]>>
  Cases_on ‘wb (md_u_flag name a)’>>Cases_on ‘wb (md_u_flag name b)’>>
  gvs[]>>
  intLib.ARITH_TAC
QED

Theorem varc_lb_le[simp]:
  valid_assignment bnd wi ⇒ varc_lb bnd Z ≤ varc wi Z
Proof
  rw[varc_lb_def]>>
  Cases_on ‘Z’>>gvs[varc_def]>>
  rename1 ‘bnd x’>>Cases_on ‘bnd x’>>gvs[]>>
  fs[valid_assignment_def]>>res_tac
QED

Theorem varc_le_ub[simp]:
  valid_assignment bnd wi ⇒ varc wi Z ≤ varc_ub bnd Z
Proof
  rw[varc_ub_def]>>
  Cases_on ‘Z’>>gvs[varc_def]>>
  rename1 ‘bnd x’>>Cases_on ‘bnd x’>>gvs[]>>
  fs[valid_assignment_def]>>res_tac
QED

Theorem LENGTH_FILTER_GE_1_EL:
  1 ≤ LENGTH (FILTER P l) ⇒ ∃i. i < LENGTH l ∧ P (EL i l)
Proof
  strip_tac>>
  ‘FILTER P l ≠ []’ by (strip_tac>>gvs[])>>
  ‘MEM (HD (FILTER P l)) (FILTER P l)’ by (Cases_on ‘FILTER P l’>>gvs[])>>
  gvs[MEM_FILTER,MEM_EL]>>
  metis_tac[]
QED

Theorem FILTER_LENGTH_GE_2_EL:
  ∀l. 2 ≤ LENGTH (FILTER P l) ⇒
  ∃i j. i < j ∧ j < LENGTH l ∧ P (EL i l) ∧ P (EL j l)
Proof
  Induct_on ‘l’>>rw[]
  >- (
    ‘1 ≤ LENGTH (FILTER P l)’ by simp[]>>
    drule LENGTH_FILTER_GE_1_EL>>rw[]>>
    qexists_tac ‘0’>>qexists_tac ‘i+1’>>simp[GSYM arithmeticTheory.ADD1])>>
  first_x_assum drule>>rw[]>>
  qexists_tac ‘i+1’>>qexists_tac ‘j+1’>>simp[GSYM arithmeticTheory.ADD1]
QED

Theorem md_pair_intro:
  dist_matrix_ok D ∧ i ≠ j ∧ i < LENGTH Xs ∧ j < LENGTH Xs ∧
  dist_at D (Num (varc wi (EL i Xs))) (Num (varc wi (EL j Xs))) = t ∧
  0 ≤ varc wi (EL i Xs) ∧ Num (varc wi (EL i Xs)) < LENGTH D ∧
  0 ≤ varc wi (EL j Xs) ∧ Num (varc wi (EL j Xs)) < LENGTH D ⇒
  md_pair Xs D wi t
Proof
  rw[md_pair_def]>>
  Cases_on ‘i < j’
  >- metis_tac[]>>
  ‘j < i’ by simp[]>>
  qexists_tac ‘j’>>qexists_tac ‘i’>>
  simp[]>>
  metis_tac[dist_at_sym]
QED

(* the semantic content of md_witnesses_at, once the u/d/w flags carry
   their intended meaning: a witness exists iff some pair of positions
   in Xs achieves distance exactly t *)
Theorem md_witnesses_at_sem:
  valid_assignment bnd wi ∧ dist_matrix_ok D ∧
  EVERY (λX. 0 ≤ varc wi X ∧ Num (varc wi X) < LENGTH D) Xs ∧
  sites = md_sites bnd Xs (LENGTH D) ∧
  (∀a. MEM a sites ⇒ (wb (md_u_flag name a) ⇔ ∃X. MEM X Xs ∧ varc wi X = a)) ∧
  (∀a. MEM a sites ⇒
     (wb (md_d_flag name a) ⇔ 2 ≤ LENGTH (FILTER (λX. varc wi X = a) Xs))) ∧
  (∀p. MEM p (md_site_pairs sites) ⇒
     (wb (md_w_flag name (FST p) (SND p)) ⇔
      wb (md_u_flag name (FST p)) ∧ wb (md_u_flag name (SND p)))) ⇒
  ((∃f. MEM f (md_witnesses_at bnd Xs name sites D t) ∧ wb f) ⇔
   md_pair Xs D wi t)
Proof
  strip_tac>>
  gvs[EVERY_MEM]>>
  eq_tac
  >- (
    strip_tac>>
    Cases_on ‘t = 0’>>
    gvs[md_witnesses_at_def,MEM_APPEND,MEM_MAP,MEM_FILTER]>>
    TRY (
      (* d_a witness: t = 0, a duplicate at the value y *)
      rename1 ‘2 ≤ LENGTH (FILTER (λX. varc wi X = y) Xs)’>>
      drule FILTER_LENGTH_GE_2_EL>>rw[]>>
      irule md_pair_intro>>conj_tac >- simp[]>>
      qexistsl_tac [‘i’,‘j’]>>
      simp[]>>
      metis_tac[MEM_EL,dist_matrix_ok_def,dist_at_def])>>
    (* w_{a,b} witness *)
    rename1 ‘MEM p (md_site_pairs (md_sites bnd Xs (LENGTH D)))’>>
    PairCases_on ‘p’>>gvs[]>>
    ‘MEM p0 (md_sites bnd Xs (LENGTH D)) ∧
     MEM p1 (md_sites bnd Xs (LENGTH D))’ by (
      qpat_x_assum ‘MEM (p0,p1) (md_site_pairs _)’ mp_tac>>
      rw[MEM_md_site_pairs]
      >- (simp[MEM_EL]>>qexists_tac ‘i’>>simp[])
      >> simp[MEM_EL]>>qexists_tac ‘j’>>simp[])>>
    ‘p0 < p1’ by (
      qpat_x_assum ‘MEM (p0,p1) (md_site_pairs _)’ mp_tac>>
      rw[MEM_md_site_pairs])>>
    qpat_x_assum ‘MEM (p0,p1) (md_site_pairs _)’ kall_tac>>
    pop_assum strip_assume_tac>>
    ‘∃X. MEM X Xs ∧ varc wi X = p0’ by (
      qpat_x_assum ‘∀a. MEM a (md_sites bnd Xs (LENGTH D)) ⇒
                      (wb (INR (name,Values [a] (SOME «u»))) ⇔ _)’
        (qspec_then ‘p0’ mp_tac)>>
      simp[])>>
    ‘∃X. MEM X Xs ∧ varc wi X = p1’ by (
      qpat_x_assum ‘∀a. MEM a (md_sites bnd Xs (LENGTH D)) ⇒
                      (wb (INR (name,Values [a] (SOME «u»))) ⇔ _)’
        (qspec_then ‘p1’ mp_tac)>>
      simp[])>>
    ‘∃i. i < LENGTH Xs ∧ varc wi (EL i Xs) = p0’ by (
      qpat_x_assum ‘∃X. MEM X Xs ∧ varc wi X = p0’ strip_assume_tac>>
      gvs[MEM_EL]>>
      qexists_tac ‘n’>>simp[])>>
    ‘∃j. j < LENGTH Xs ∧ varc wi (EL j Xs) = p1’ by (
      qpat_x_assum ‘∃X. MEM X Xs ∧ varc wi X = p1’ strip_assume_tac>>
      gvs[MEM_EL]>>
      qexists_tac ‘n’>>simp[])>>
    pop_assum strip_assume_tac>>
    qpat_x_assum ‘∃i. i < LENGTH Xs ∧ varc wi (EL i Xs) = p0’ strip_assume_tac>>
    irule md_pair_intro>>conj_tac >- simp[]>>
    qexistsl_tac [‘i’,‘j’]>>
    simp[]>>
    ‘i ≠ j’ by (strip_tac>>gvs[])>>
    simp[]>>
    metis_tac[MEM_EL])>>
  rw[md_pair_def]>>
  Cases_on ‘varc wi (EL i Xs) = varc wi (EL j Xs)’
  >- (
    (* duplicate case: t = 0 *)
    ‘t = 0’ by (
      gvs[dist_matrix_ok_def,dist_at_def]>>
      metis_tac[MEM_EL])>>
    gvs[]>>
    simp[md_witnesses_at_def,MEM_APPEND,MEM_MAP,MEM_FILTER]>>
    disj1_tac>>
    qexists_tac ‘varc wi (EL i Xs)’>>
    simp[]>>
    CONJ_TAC
    >- metis_tac[md_sites_complete,MEM_EL]>>
    CONJ_TAC
    >- (
      simp[GSYM iSUM_MAP_b2i_FILTER]>>
      irule FILTER_LENGTH_GE_2_EL>>
      qexistsl_tac [‘i’,‘j’]>>simp[]>>
      metis_tac[])>>
    metis_tac[])>>
  (* distinct-value case *)
  qabbrev_tac ‘a = varc wi (EL i Xs)’>>
  qabbrev_tac ‘b = varc wi (EL j Xs)’>>
  ‘MEM a sites ∧ MEM b sites’ by metis_tac[md_sites_complete,MEM_EL]>>
  ‘0 ≤ a ∧ Num a < LENGTH D ∧ 0 ≤ b ∧ Num b < LENGTH D’ by metis_tac[MEM_EL]>>
  ‘∃a' b'. (a' = a ∧ b' = b ∨ a' = b ∧ b' = a) ∧ a' < b'’ by (
    ‘a < b ∨ b < a’ by (unabbrev_all_tac>>intLib.ARITH_TAC)>>
    metis_tac[])>>
  ‘MEM (a',b') (md_site_pairs sites)’ by metis_tac[md_site_pairs_complete]>>
  ‘dist_at D (Num a') (Num b') = t’ by metis_tac[dist_at_sym]>>
  simp[md_witnesses_at_def,MEM_APPEND,MEM_MAP,MEM_FILTER]>>
  disj2_tac>>
  qexists_tac ‘(a',b')’>>
  simp[]>>
  ‘wb (md_u_flag name a') ∧ wb (md_u_flag name b')’ by metis_tac[MEM_EL]>>
  metis_tac[]
QED

Definition encode_misc_constr_def:
  encode_misc_constr bnd c name =
  case c of
    Circuit Xs =>
    encode_circuit bnd Xs name
  | Knapsack css Xs Ts =>
    encode_knapsack css Xs Ts name
  | MinDistance Xs D Z Ropt =>
    encode_min_distance bnd Xs D Z Ropt name
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
  >- metis_tac[encode_circuit_sem_1]
  >- metis_tac[encode_knapsack_sem_1]
QED

Theorem encode_misc_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_misc_constr bnd c name) ⇒
  misc_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_misc_constr_def,misc_constr_sem_def]
  >- metis_tac[encode_circuit_sem_2]
  >- metis_tac[encode_knapsack_sem_2]
QED

(* Concrete encodings *)
Definition cencode_misc_constr_def:
  cencode_misc_constr bnd c name ec =
  case c of
    Circuit Xs =>
    cencode_circuit bnd Xs name ec
  | Knapsack css Xs Ts =>
    (cencode_knapsack css Xs Ts name, ec)
  | MinDistance Xs D Z Ropt =>
    cencode_min_distance bnd Xs D Z Ropt name ec
End

Theorem cencode_misc_constr_sem:
  valid_assignment bnd wi ∧
  cencode_misc_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_misc_constr bnd c name) ec ec'
Proof
  Cases_on`c`>>
  rw[cencode_misc_constr_def,encode_misc_constr_def]
  >- metis_tac[cencode_circuit_sem]
  >- simp[cencode_knapsack_def,encode_knapsack_def]
QED
