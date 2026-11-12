(*
  Formalization of the CP to ILP phase (misc constraints)
*)
Theory cp_to_ilp_misc
Libs
  preamble
Ancestors
  pbc cp ilp int_bitwiseExtra
  cp_to_ilp cp_to_ilp_linear cp_to_ilp_counting

val _ = Parse.hide "dom";

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
    n1 = n - 1;
    ubs = GENLIST (λj. ub_num name j n1) n
  in
    Append
      (* pos 0 = 0 *)
      (List [
        (SOME $ mk_name name
          («pos0eq0»),
        mk_ubnd_bin (ub_num name 0 n1) 0)])
      (* pos i < n for i = 0 to n-1 *)
      (Append (List
        (MAPi
        (λi ubi. SOME $ mk_name name
          («pos» ^ toString i ^ «lt» ^ toString n),
        mk_ubnd_bin ubi (&n1)) ubs))
      (* for 0 ≤ i, j < n *)
      (flat_app (MAPi
        (λi X.
            let ubi = ub_num name i n1 in
            (flat_app $ MAPi
              (λj ubj.
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
                       (mk_bounds_bin ubi (&n1) (&n1)))
                 else
                   (* Xs[i] = j  ⇒  pos j = pos i + 1 *)
                   [
                     bits_imply bnd [Pos cond] $
                       mk_constraint_ge_bin (-1) ubi 1 ubj 1;
                     bits_imply bnd [Pos cond] $
                       mk_constraint_ge_bin 1 ubi (-1) ubj (-1);
                   ]))
              ubs))
        Xs)))
End

(* the same rows with each position's bit-sum written in place *)
Theorem cencode_circuit_pos_GENLIST:
  cencode_circuit_pos bnd Xs name =
  let
    n = LENGTH Xs;
    n1 = n - 1
  in
    Append
      (List [
        (SOME $ mk_name name
          («pos0eq0»),
        mk_ubnd_bin (ub_num name 0 n1) 0)])
      (Append (List
        (GENLIST
        (λi. SOME $ mk_name name
          («pos» ^ toString i ^ «lt» ^ toString n),
        mk_ubnd_bin (ub_num name i n1) (&n1)) n))
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
                   (MAP
                     (λcc. bits_imply bnd [Pos cond] cc)
                       (mk_bounds_bin (ub_num name i n1) (&n1) (&n1)))
                 else
                   [
                     bits_imply bnd [Pos cond] $
                       mk_constraint_ge_bin (-1) (ub_num name i n1) 1 (ub_num name j n1) 1;
                     bits_imply bnd [Pos cond] $
                       mk_constraint_ge_bin 1 (ub_num name i n1) (-1) (ub_num name j n1) (-1);
                   ]))
              n))
        Xs)))
Proof
  simp[cencode_circuit_pos_def,MAPi_GENLIST_GENLIST]
QED

(* The static circuit constraints:
     - every successor Xs[i] lies in [0, n-1] (each side emitted only when
       Xs[i]'s declared bounds do not imply it);
     - the successors are all-distinct (reusing cencode_all_different), so they
       form a permutation of 0..n-1;
     - the positions form a single Hamiltonian cycle (cencode_circuit_pos). *)
Definition cencode_circuit_aux_def:
  cencode_circuit_aux bnd Xs name =
  let n = LENGTH Xs in
    Append
      (Append
        (cmk_bounds_all bnd name «X_» Xs 0 (&n - 1))
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
    simp[cmk_bounds_all_sem,integerTheory.INT_GE]>>
    rw[]>>first_x_assum drule>>
    simp[intLib.ARITH_PROVE“0 ≤ (a:int) ∧ Num a < (b:num) ⇒ a ≤ &b − 1”])
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
  fs[MEM_EL,SF DNF_ss,cencode_circuit_pos_GENLIST]>>
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
    qpat_x_assum`EVERY _ (abstr (cmk_bounds_all _ _ _ _ _ _))` mp_tac>>
    simp[cmk_bounds_all_sem,integerTheory.INT_GE,EVERY_MEM]>>
    rw[]>>first_x_assum drule>>
    simp[intLib.ARITH_PROVE“0 ≤ (a:int) ∧ a ≤ &b − 1 ⇒ Num a < b”])
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
    simp[cencode_circuit_pos_GENLIST,append_thm,EVERY_APPEND]>>
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
      qpat_x_assum`EVERY _ (abstr (cmk_bounds_all _ _ _ _ _ _))` mp_tac>>
      simp[cmk_bounds_all_sem,integerTheory.INT_GE]>>
      rpt strip_tac>>first_x_assum (qspec_then`EL m Xs`mp_tac)>>simp[EL_MEM]>>
      qpat_x_assum`0 < LENGTH Xs`mp_tac>>rpt (pop_assum kall_tac)>>intLib.ARITH_TAC)>>
    (* the bulky constraint assumptions are spent; drop them so the
       remaining simplification stays cheap *)
    qpat_x_assum`EVERY _ (FLAT (MAP _ Xs))` kall_tac>>
    qpat_x_assum`EVERY _ (abstrl (GENLIST _ _))` kall_tac>>
    qpat_x_assum`EVERY _ (abstr (cmk_bounds_all _ _ _ _ _ _))` kall_tac>>
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

(* ------------------------------------------------------------------------
   min_distance. Encoding consists of the groups:
   (i) Site-used flags
   (ii) Duplicate bound
   (iii) Pair upper bounds
   (iv) Min-attained ladder
   (v) Requirement clauses

   Auxiliary definitions/theorems before final assembly are organized below:
   1. shared (preprocessing, specification, literals and atoms)
   2. range rows
   3. the counting shared by (ii) and (iv)
   4. the groups (i)-(v)

   Terms for the constructor MinDistance Xs Z D R:
   Xs: positions
   Z: objective
   D: distance matrix
   R: optional requirement matrix
   n (= LENGTH D): number/indices of sites
   ------------------------------------------------------------------------ *)

(* shared: preprocessing. The sites are the values in [0,n) the positions
   can take *)

(* d as a num, with negatives sent to 0 *)
Definition mindist_nnum_def:
  mindist_nnum (d:int) = if d < 0 then 0 else Num d
End

(* the sites X can take, ascending: its bounds clipped to [0,n) *)
Definition mindist_psites_def:
  mindist_psites bnd n X =
  let
    (lo,hi) = varc_bnd bnd X;
    l = mindist_nnum lo;
    h = MIN (mindist_nnum hi + 1) n
  in
    if hi < &l ∨ h ≤ l then [] else GENLIST (λk. l + k) (h - l)
End

(* site |-> the positions (as varcs, in order) that can take it *)
Definition mindist_pos_map_def:
  mindist_pos_map (xps : ('a varc # num list) list) =
  FOLDR (λ(X,ps) t.
    FOLDL (λt a. insert a (X :: lookup_any a t []) t) t ps) LN xps
End

Definition mindist_dtab_def:
  mindist_dtab (D:num list list) = sptree$fromList (MAP sptree$fromList D)
End

(* D[a][b]; the 0 fallback is never reached for a, b < n on a square D *)
Definition mindist_dist_def:
  mindist_dist (dt:num num_map num_map) a b = lookup_any b (lookup_any a dt LN) 0
End

(* site pairs a < b with their distance, in lexicographic order *)
Definition mindist_dpairs_def:
  (mindist_dpairs dt [] = []) ∧
  (mindist_dpairs dt (a::as) =
    MAP (λb. (a,b,mindist_dist dt a b)) as ++ mindist_dpairs dt as)
End

Definition mindist_prep_def:
  mindist_prep bnd Xs D =
  let
    dt = mindist_dtab D;
    xps = MAP (λX. (X, mindist_psites bnd (LENGTH D) X)) Xs;
    sites = MAP FST (toSortedAList (list_insert (FLAT (MAP SND xps)) LN));
    dps = mindist_dpairs dt sites;
    levels =
      MAP FST (toSortedAList (list_insert (0 :: MAP (λ(a,b,d). d) dps) LN))
  in
    (dt, xps, sites, mindist_pos_map xps, dps, levels)
End

(* the setting of the min_distance lemmas: a valid assignment, a square,
   zero-diagonal, symmetric D, every position's value a site index, and the
   preprocessing *)
Definition mindist_ctx_def:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ⇔
    valid_assignment bnd wi ∧
    EVERY (λrow. LENGTH row = LENGTH D) D ∧
    (∀i. i < LENGTH D ⇒ EL i (EL i D) = 0) ∧
    (∀i j. i < LENGTH D ∧ j < LENGTH D ⇒ EL i (EL j D) = EL j (EL i D)) ∧
    EVERY (λX. 0 ≤ varc wi X ∧ Num (varc wi X) < LENGTH D) Xs ∧
    mindist_prep bnd Xs D = (dt,xps,sites,pm,dps,levels)
End

Theorem lookup_any_insert[local]:
  lookup_any a (insert k v t) d = if a = k then v else lookup_any a t d
Proof
  rw[lookup_any_def,lookup_insert]
QED

(* a position's candidate sites: the in-range values within its bounds,
   without repetition *)
Theorem mindist_psites_thm[local]:
  (MEM a (mindist_psites bnd n X) ⇔
    FST (varc_bnd bnd X) ≤ &a ∧ &a ≤ SND (varc_bnd bnd X) ∧ a < n) ∧
  ALL_DISTINCT (mindist_psites bnd n X)
Proof
  Cases_on`varc_bnd bnd X`>>rename1`(lo,hi)`>>
  Cases_on`lo`>>Cases_on`hi`>>
  rw[mindist_psites_def,mindist_nnum_def,MEM_GENLIST,MIN_DEF,ALL_DISTINCT_GENLIST]>>
  intLib.COOPER_TAC
QED

Theorem lookup_any_FOLDL_cons[local]:
  ∀ps t. ALL_DISTINCT ps ⇒
    lookup_any a (FOLDL (λt a. insert a (X :: lookup_any a t []) t) t ps) [] =
    if MEM a ps then X :: lookup_any a t [] else lookup_any a t []
Proof
  Induct>>rw[lookup_any_insert]>>gvs[]
QED

Theorem mindist_at_pos_map[local]:
  ∀xps. EVERY (ALL_DISTINCT o SND) xps ⇒
    lookup_any a (mindist_pos_map xps) [] =
    MAP FST (FILTER (λ(X,ps). MEM a ps) xps)
Proof
  Induct>>simp[mindist_pos_map_def,lookup_any_def,FORALL_PROD]>>
  rw[GSYM lookup_any_def,GSYM mindist_pos_map_def,lookup_any_FOLDL_cons]
QED

Theorem mindist_dist_dtab[local]:
  EVERY (λrow. LENGTH row = LENGTH D) D ∧ a < LENGTH D ∧ b < LENGTH D ⇒
  mindist_dist (mindist_dtab D) a b = EL b (EL a D)
Proof
  rw[mindist_dist_def,lookup_any_def,mindist_dtab_def,lookup_fromList,EL_MAP]>>
  gvs[EVERY_EL]
QED

Theorem MEM_mindist_dpairs[local]:
  ∀l. SORTED $< l ⇒
  (MEM (a,b,d) (mindist_dpairs dt l) ⇔
    MEM a l ∧ MEM b l ∧ a < b ∧ d = mindist_dist dt a b)
Proof
  Induct>>rw[mindist_dpairs_def,MEM_MAP]>>
  gvs[SORTED_EQ,transitive_LESS]>>
  eq_tac>>rw[]>>gvs[]>>res_tac>>gvs[]
QED

Theorem mindist_prep_facts[local]:
  EVERY (λrow. LENGTH row = LENGTH D) D ∧
  mindist_prep bnd Xs D = (dt,xps,sites,pm,dps,levels) ⇒
  xps = MAP (λX. (X,mindist_psites bnd (LENGTH D) X)) Xs ∧
  dt = mindist_dtab D ∧
  SORTED $< sites ∧
  (∀a. MEM a sites ⇔ ∃X. MEM X Xs ∧ MEM a (mindist_psites bnd (LENGTH D) X)) ∧
  (∀a. MEM a sites ⇒ a < LENGTH D) ∧
  (∀a. lookup_any a pm [] =
      FILTER (λX. MEM a (mindist_psites bnd (LENGTH D) X)) Xs) ∧
  (∀a b d. MEM (a,b,d) dps ⇔
    MEM a sites ∧ MEM b sites ∧ a < b ∧ d = EL b (EL a D)) ∧
  SORTED $< levels ∧
  (∀t. MEM t levels ⇔
    t = 0 ∨ ∃a b. MEM a sites ∧ MEM b sites ∧ a < b ∧ t = EL b (EL a D))
Proof
  strip_tac>>
  gvs[mindist_prep_def]>>
  ‘∀a (s:unit num_map). lookup a s = SOME () ⇔ a ∈ domain s’
    by simp[domain_lookup]>>
  simp[SORTED_toSortedAList,MEM_toSortedAList,domain_list_insert,MEM_FLAT,MEM_MAP,
    EXISTS_PROD,PULL_EXISTS,MEM_mindist_dpairs,mindist_at_pos_map,EVERY_MAP,
    cj 2 mindist_psites_thm,FILTER_MAP,MAP_MAP_o,o_DEF]>>
  fs[SF CONJ_ss,cj 1 mindist_psites_thm,mindist_dist_dtab]>>
  simp[AC CONJ_ASSOC CONJ_COMM]
QED

(* a position's value, or a value equal to it, is among its candidate sites *)
Theorem mindist_val_psites[local]:
  valid_assignment bnd wi ⇒
  (varc wi X = &a ∧ a < n ⇒ MEM a (mindist_psites bnd n X)) ∧
  (varc wi X = varc wi Y ∧ 0 ≤ varc wi Y ∧ Num (varc wi Y) < n ⇒
    MEM (Num (varc wi Y)) (mindist_psites bnd n X))
Proof
  rw[mindist_psites_thm]>>
  qpat_x_assum`varc wi X = _`(SUBST_ALL_TAC o SYM)>>
  fs[iffRL integerTheory.INT_OF_NUM,varc_bnd_valid]
QED

(* each position's value is a site; so is every value a position takes *)
Theorem mindist_pos_site[local]:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ⇒
  EVERY (λX. MEM (Num (varc wi X)) sites) Xs ∧
  ∀a. MEM (&a) (MAP (varc wi) Xs) ⇒ MEM a sites
Proof
  strip_tac>>drule_then strip_assume_tac (iffLR mindist_ctx_def)>>
  drule_all_then strip_assume_tac mindist_prep_facts>>
  gvs[EVERY_MEM,MEM_MAP]>>rw[]>>
  first_assum (irule_at Any)>>
  metis_tac[mindist_val_psites,integerTheory.NUM_OF_INT]
QED

(* shared: specification *)

Definition mindist_valid_def:
  mindist_valid p D optR ⇔
  let n = LENGTH D in
    2 ≤ p ∧ n ≠ 0 ∧
    EVERY (λrow. LENGTH row = n) D ∧
    (let dt = mindist_dtab D in
      EVERY (λi. mindist_dist dt i i = 0) (COUNT_LIST n) ∧
      EVERY (λ(i,j,d). mindist_dist dt j i = d)
        (FLAT (MAPi (λi row. MAPi (λj d. (i,j,d)) row) D))) ∧
    case optR of
      NONE => T
    | SOME R =>
        LENGTH R = p ∧ EVERY (λrow. LENGTH row = p) R ∧
        EVERY (λb. b) (FLAT (MAPi (λi row. MAPi (λj r. i < j ⇒ 0 ≤ r) row) R))
End

Theorem mindist_valid_thm:
  mindist_valid p D optR ⇔
  2 ≤ p ∧ LENGTH D ≠ 0 ∧
  EVERY (λrow. LENGTH row = LENGTH D) D ∧
  (∀i. i < LENGTH D ⇒ EL i (EL i D) = 0) ∧
  (∀i j. i < LENGTH D ∧ j < LENGTH D ⇒ EL i (EL j D) = EL j (EL i D)) ∧
  case optR of
    NONE => T
  | SOME R =>
      LENGTH R = p ∧ EVERY (λrow. LENGTH row = p) R ∧
      ∀i j. i < j ∧ j < p ⇒ 0 ≤ EL j (EL i R)
Proof
  simp[mindist_valid_def]>>
  Cases_on`EVERY (λrow. LENGTH row = LENGTH D) D`>>simp[]>>
  simp[EVERY_MEM,MEM_COUNT_LIST,MEM_FLAT,MEM_MAPi,PULL_EXISTS,FORALL_PROD]>>
  fs[GSYM AND_IMP_INTRO,mindist_dist_dtab,EVERY_EL]>>
  Cases_on`optR`>>rw[EQ_IMP_THM]>>
  first_x_assum irule>>gvs[MEM_EL,PULL_EXISTS]
QED

(* some two distinct positions are at distance d *)
Definition mindist_realised_def:
  mindist_realised Xs D w d ⇔
  ∃i j. i < LENGTH Xs ∧ j < LENGTH Xs ∧ i ≠ j ∧
    pos_dist D Xs w i j = d
End

(* readings of a realised distance, for a zero-diagonal, symmetric D:
   0 from two positions on one value, or D[a][b] for values a < b that
   positions take; one realised by an ordered pair i < j; the Z line of
   mindistance_sem (lower bound and attainment over pairs i < j) over
   realised distances; and, as a lower bound on z, a duplicate case and a
   taken-pair case *)
Theorem mindist_realised_thm[local]:
  (∀i. i < LENGTH D ⇒ EL i (EL i (D:num list list)) = 0) ∧
  (∀i j. i < LENGTH D ∧ j < LENGTH D ⇒ EL i (EL j D) = EL j (EL i D)) ∧
  EVERY (λX. 0 ≤ varc w X ∧ Num (varc w X) < LENGTH D) Xs ⇒
  (∀d. mindist_realised Xs D w d ⇔
    (d = 0 ∧ ∃i j. i < LENGTH Xs ∧ j < LENGTH Xs ∧ i ≠ j ∧
      varc w (EL i Xs) = varc w (EL j Xs)) ∨
    ∃a b. a < b ∧ MEM (&a) (MAP (varc w) Xs) ∧ MEM (&b) (MAP (varc w) Xs) ∧
      EL b (EL a D) = d) ∧
  (∀d. mindist_realised Xs D w d ⇔
    ∃i j. i < j ∧ j < LENGTH Xs ∧
      pos_dist D Xs w i j = d) ∧
  (((∀i j. i < j ∧ j < LENGTH Xs ⇒
      z ≤ &pos_dist D Xs w i j) ⇔
    ∀d. mindist_realised Xs D w d ⇒ z ≤ &d) ∧
  ((∃i j. i < j ∧ j < LENGTH Xs ∧
      z = &pos_dist D Xs w i j) ⇔
    0 ≤ z ∧ mindist_realised Xs D w (Num z))) ∧
  ((∀d. mindist_realised Xs D w d ⇒ z ≤ &d) ⇔
    (∀i j. i < LENGTH Xs ∧ j < LENGTH Xs ∧ i ≠ j ∧
      varc w (EL i Xs) = varc w (EL j Xs) ⇒ z ≤ 0) ∧
    ∀a b. a < b ∧ MEM (&a) (MAP (varc w) Xs) ∧ MEM (&b) (MAP (varc w) Xs) ⇒
      z ≤ &EL b (EL a D))
Proof
  strip_tac>>
  conj_asm1_tac
  >- (
    rw[mindist_realised_def,pos_dist_def,EQ_IMP_THM]
    >- (
      Cases_on`varc w (EL i Xs) = varc w (EL j Xs)`
      >- (disj1_tac>>qpat_assum`i ≠ j`(irule_at Any)>>gvs[EVERY_EL])>>
      disj2_tac>>
      `∃n m. varc w (EL i Xs) = (&n:int) ∧ varc w (EL j Xs) = &m`
        by (gvs[EVERY_EL]>>metis_tac[integerTheory.NUM_POSINT_EXISTS])>>
      gvs[]>>
      Cases_on`n < m`
      >- (irule_at Any EQ_REFL>>gvs[]>>metis_tac[MEM_MAP_f,EL_MEM])>>
      qpat_x_assum`∀i j. _ ⇒ EL _ (EL _ D) = _`(irule_at Any)>>
      gvs[EVERY_EL]>>metis_tac[MEM_MAP_f,EL_MEM,integerTheory.NUM_OF_INT])
    >- (qpat_assum`i ≠ j`(irule_at Any)>>gvs[EVERY_EL])>>
    gvs[MEM_MAP,MEM_EL,intLib.ARITH_PROVE``(&a = x ⇔ 0 ≤ x ∧ a = Num x) ∧ (x = &a ⇔ 0 ≤ x ∧ a = Num (x:int))``]>>
    irule_at Any EQ_REFL>>rw[]>>strip_tac>>gvs[])>>
  conj_asm1_tac
  >- (
    qpat_x_assum`∀d. mindist_realised _ _ _ _ ⇔ _`kall_tac>>
    rw[mindist_realised_def,pos_dist_def,EQ_IMP_THM]
    >- (
      Cases_on`i < j`
      >- (irule_at Any EQ_REFL>>simp[])>>
      qexistsl_tac[`j`,`i`]>>simp[]>>
      qpat_x_assum`∀i j. _ ⇒ EL _ (EL _ D) = _`irule>>gvs[EVERY_EL])>>
    irule_at Any EQ_REFL>>simp[])>>
  conj_tac
  >- (
    qpat_x_assum`∀d. mindist_realised _ _ _ _ ⇔ _ ∨ _`kall_tac>>
    simp[PULL_EXISTS]>>
    metis_tac[integerTheory.INT_OF_NUM,integerTheory.NUM_OF_INT,integerTheory.INT_POS])>>
  qpat_x_assum`∀d. mindist_realised _ _ _ _ ⇔ ∃i j. _`kall_tac>>
  simp[DISJ_IMP_THM,FORALL_AND_THM,PULL_EXISTS]
QED

(* shared: literals and atoms *)

Definition mindist_flag_def:
  mindist_flag name tag vs = INR (name, Values vs (SOME tag))
End

(* the X = a literals the rows use *)
Definition mindist_eqpairs_def:
  mindist_eqpairs (xps : ('a varc # num list) list) =
  FLAT (MAP (λ(X,ps). MAP (λa. (X, &a)) ps) xps)
End

(* the z comparisons the rows use *)
Definition mindist_ztriples_def:
  mindist_ztriples bnd Z pm sites dps levels =
  let (zlo,zhi) = varc_bnd bnd Z in
  (if 0 < zhi ∧ zlo < 1 ∧ EXISTS (λa. 2 ≤ LENGTH (lookup_any a pm [])) sites
    then [(Z,Lexop GreaterEqual,1i)] else []) ++
  MAP (λ(a,b,d). (Z,Lexop LessEqual,&d))
    (FILTER (λ(a,b,d). &d < zhi) dps) ++
  MAP (λt. (Z,Lexop GreaterEqual,&t)) (FILTER (λt. zlo < &t) levels)
End

(* the atoms the rows use are faithful under wb: the Eq atoms, the u flags,
   and the z literals *)
Definition mindist_faith_def:
  mindist_faith bnd Xs Z D wi wb name (dt,xps,sites,pm,dps,levels) ⇔
    (∀X a. MEM X Xs ∧ MEM a (mindist_psites bnd (LENGTH D) X) ⇒
      (wb (INL (Eq X (&a))) ⇔ varc wi X = &a)) ∧
    (∀a. MEM a sites ⇒
      (wb (mindist_flag name «u» [&a]) ⇔ MEM (&a) (MAP (varc wi) Xs))) ∧
    (∀Zc. MEM Zc (mindist_ztriples bnd Z pm sites dps levels) ⇒
      (lit wb (reif_gen Zc) ⇔ reify_cmp_val wi Zc))
End

(* the atom rows make every Eq atom and every Z literal the rows use faithful *)
Theorem mindist_atoms_faithful[local]:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (FLAT
    (MAP (λ(X,v). encode_full_eq bnd X v) (mindist_eqpairs xps))) ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (FLAT (MAP (encode_reif_gen bnd)
    (mindist_ztriples bnd Z pm sites dps levels))) ⇒
  (∀X a. MEM X Xs ∧ MEM a (mindist_psites bnd (LENGTH D) X) ⇒
    (wb (INL (Eq X (&a))) ⇔ varc wi X = &a)) ∧
  (∀Zc. MEM Zc (mindist_ztriples bnd Z pm sites dps levels) ⇒
    (lit wb (reif_gen Zc) ⇔ reify_cmp_val wi Zc))
Proof
  strip_tac>>drule_then strip_assume_tac (iffLR mindist_ctx_def)>>
  rpt strip_tac
  >- (
    drule_all_then strip_assume_tac mindist_prep_facts>>gvs[]>>
    irule encode_full_eqs_sem_2>>
    qpat_assum`EVERY _ (FLAT (MAP (λ(X,v). _) _))`(irule_at Any)>>
    simp[mindist_eqpairs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]>>
    qpat_assum`MEM X Xs`(irule_at Any)>>simp[])>>
  irule encode_reif_gen_sem_lit>>
  first_assum (irule_at Any)>>
  qpat_x_assum`EVERY _ (FLAT (MAP (encode_reif_gen _) _))`
    (mp_tac o SRULE[EVERY_FLAT,EVERY_MAP,EVERY_MEM])>>
  disch_then drule>>simp[EVERY_MEM]
QED

(* each Z literal the rows use is faithful: [Z ≥ 1] at a site with two
   candidates, [Z ≤ D[a][b]] for an emitted pair row, [Z ≥ t] for a guarded
   level *)
Theorem mindist_zlits[local]:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ∧
  mindist_faith bnd Xs Z D wi wb name (dt,xps,sites,pm,dps,levels) ∧
  varc_bnd bnd Z = (zlo,zhi) ⇒
  (0 < zhi ∧ zlo < 1 ∧ MEM a sites ∧ 2 ≤ LENGTH (lookup_any a pm []) ⇒
    (lit wb (reif_gen (Z,Lexop GreaterEqual,1)) ⇔ varc wi Z ≥ 1)) ∧
  (MEM a sites ∧ MEM b sites ∧ a < b ∧ &EL b (EL a D) < zhi ⇒
    (lit wb (reif_gen (Z,Lexop LessEqual,&EL b (EL a D))) ⇔
    varc wi Z ≤ &EL b (EL a D))) ∧
  (MEM t levels ∧ zlo < &t ⇒
    (lit wb (reif_gen (Z,Lexop GreaterEqual,&t)) ⇔ varc wi Z ≥ &t))
Proof
  strip_tac>>drule_then strip_assume_tac (iffLR mindist_ctx_def)>>drule_then strip_assume_tac (iffLR mindist_faith_def)>>
  drule_all_then strip_assume_tac mindist_prep_facts>>
  rpt conj_tac>>strip_tac>>
  qpat_x_assum`∀Zc. MEM Zc (mindist_ztriples _ _ _ _ _ _) ⇒ _`
    (DEP_ONCE_REWRITE_TAC o single)>>
  gvs[cmpop_val_def,mindist_ztriples_def,MEM_MAP,MEM_FILTER,EXISTS_MEM,
    EXISTS_PROD]>>
  rw[]>>metis_tac[]
QED

Theorem mindist_reify_flags[local]:
  ALOOKUP cs name = SOME (Misc (MinDistance Xs Z D optR)) ⇒
  (reify_avar cs wi (mindist_flag name «u» [&a]) ⇔
    MEM (&a) (MAP (varc wi) Xs)) ∧
  (reify_avar cs wi (mindist_flag name «d» [&a]) ⇔
    2 ≤ LENGTH (FILTER (λX. varc wi X = &a) Xs)) ∧
  (reify_avar cs wi (mindist_flag name «w» [&a;&b]) ⇔
    MEM (&a) (MAP (varc wi) Xs) ∧ MEM (&b) (MAP (varc wi) Xs)) ∧
  (reify_avar cs wi (mindist_flag name «m» [&t]) ⇔
    ∃d. mindist_realised Xs D wi d ∧ d ≤ t)
Proof
  rw[mindist_flag_def,reify_avar_def,reify_flag_def,mindist_realised_def]>>
  metis_tac[]
QED

(* range rows: every position in [0,n) *)

Theorem mindist_range_sem[local]:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (cmk_bounds_all bnd name «X_» Xs 0 (&n − 1))) ⇔
  EVERY (λX. 0 ≤ varc wi X ∧ Num (varc wi X) < n) Xs)
Proof
  rw[cmk_bounds_all_sem,EVERY_MEM,EQ_IMP_THM]>>
  first_x_assum drule>>
  qspec_then`varc wi X`strip_assume_tac integerTheory.INT_NUM_CASES>>
  gvs[]>>intLib.ARITH_TAC
QED

(* shared by (ii) and (iv): counting the positions at a site *)

Theorem mindist_eq_count[local]:
  iSUM (MAP (b2i ∘ lit wb) (MAP (λX. Pos (INL (Eq X (&a)))) xs)) =
    &LENGTH (FILTER (λX. wb (INL (Eq X (&a)))) xs) ∧
  eval_lin_term wb (MAP (λl. (-1,l)) (MAP (λX. Pos (INL (Eq X (&a)))) xs)) =
    -&LENGTH (FILTER (λX. wb (INL (Eq X (&a)))) xs) ∧
  eval_lin_term wb (MAP (λX. (1,Pos (INL (Eq X (&a))))) xs) =
    &LENGTH (FILTER (λX. wb (INL (Eq X (&a)))) xs)
Proof
  simp[eval_lin_term_def,MAP_MAP_o,o_DEF,lit_def,
    SRULE[o_DEF] iSUM_FILTER]>>
  Induct_on`xs`>>rw[iSUM_def]>>intLib.ARITH_TAC
QED

Theorem LENGTH_FILTER_two[local]:
  ∀l. 2 ≤ LENGTH (FILTER P l) ⇔
  ∃i j. i < LENGTH l ∧ j < LENGTH l ∧ i ≠ j ∧ P (EL i l) ∧ P (EL j l)
Proof
  Induct>>rw[]
  >- (
    `2 ≤ SUC (LENGTH (FILTER P l)) ⇔ ∃k. k < LENGTH l ∧ P (EL k l)`
      by (`2 ≤ SUC (LENGTH (FILTER P l)) ⇔ FILTER P l ≠ []`
            by (Cases_on`FILTER P l`>>simp[])>>
          simp[FILTER_EQ_NIL,NOT_EVERY,EXISTS_MEM,MEM_EL,PULL_EXISTS]>>
          metis_tac[])>>
    simp[]>>eq_tac>>rw[]
    >- (qexistsl_tac[`0`,`SUC k`]>>simp[])>>
    Cases_on`i`>>gvs[]
    >- (Cases_on`j`>>gvs[]>>metis_tac[])>>
    metis_tac[])>>
  eq_tac>>rw[]
  >- (qexistsl_tac[`SUC i`,`SUC j`]>>simp[])>>
  Cases_on`i`>>Cases_on`j`>>gvs[]>>
  metis_tac[]
QED

Theorem mindist_at_filter[local]:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ∧
  mindist_faith bnd Xs Z D wi wb name (dt,xps,sites,pm,dps,levels) ∧
  MEM a sites ⇒
  FILTER (λX. wb (INL (Eq X (&a)))) (lookup_any a pm []) =
  FILTER (λX. varc wi X = &a) Xs
Proof
  strip_tac>>drule_then strip_assume_tac (iffLR mindist_ctx_def)>>
  drule_then strip_assume_tac (iffLR mindist_faith_def)>>
  drule_all_then strip_assume_tac mindist_prep_facts>>
  qpat_x_assum`∀a. MEM a sites ⇔ _`kall_tac>>
  qpat_assum`∀a. MEM a sites ⇒ _`(drule_then assume_tac)>>
  rw[FILTER_FILTER,rich_listTheory.FILTER_EQ]>>
  Cases_on`varc wi X = &a`
  >- (drule_all_then assume_tac (cj 1 mindist_val_psites)>>gvs[])>>
  CCONTR_TAC>>gvs[]
QED

(* two distinct positions with equal values sit at a site with two candidates *)
Theorem mindist_same_site[local]:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ∧
  i < LENGTH Xs ∧ j < LENGTH Xs ∧ i ≠ j ∧
  varc wi (EL i Xs) = varc wi (EL j Xs) ⇒
  ∃a. varc wi (EL i Xs) = &a ∧ varc wi (EL j Xs) = &a ∧
      MEM a sites ∧ 2 ≤ LENGTH (lookup_any a pm [])
Proof
  strip_tac>>drule_then strip_assume_tac (iffLR mindist_ctx_def)>>
  drule_all_then strip_assume_tac mindist_prep_facts>>
  qpat_x_assum`∀a. MEM a sites ⇔ _`kall_tac>>
  drule_all_then assume_tac mindist_pos_site>>
  gvs[LENGTH_FILTER_two,
    intLib.ARITH_PROVE``(&a = x ⇔ 0 ≤ x ∧ a = Num x) ∧ (x = &a ⇔ 0 ≤ x ∧ a = Num (x:int))``]>>
  qpat_assum`_ ≠ _`(irule_at Any)>>
  gvs[EVERY_EL,mindist_val_psites]
QED

(* (i) site-used flags: u_a ⇔ ∃i. x_i = a *)

Definition mindist_used_def:
  mindist_used bnd name pm sites =
  flat_app (MAP
    (λa. cencode_some_eq bnd (mindist_flag name «u» [&a]) (lookup_any a pm []) (&a))
    sites)
End

Theorem mindist_used_iff[local]:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ∧
  (∀X a. MEM X Xs ∧ MEM a (mindist_psites bnd (LENGTH D) X) ⇒
    (wb (INL (Eq X (&a))) ⇔ varc wi X = &a)) ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (mindist_used bnd name pm sites)) ⇔
  ∀a. MEM a sites ⇒
    (wb (mindist_flag name «u» [&a]) ⇔ MEM (&a) (MAP (varc wi) Xs)))
Proof
  strip_tac>>drule_then strip_assume_tac (iffLR mindist_ctx_def)>>
  drule_all_then strip_assume_tac mindist_prep_facts>>
  simp[mindist_used_def,cencode_some_eq_def]>>
  simp[EVERY_FLAT,EVERY_MAP]>>
  simp[EVERY_SND,EVERY_REVERSE]>>
  simp[EVERY_MEM,MEM_MAP,PULL_EXISTS,lit_def,MEM_FILTER]>>
  metis_tac[mindist_val_psites,mindist_psites_thm]
QED

(* (ii) duplicate bound: two positions on one site force z ≤ 0 *)

(* at most one position on a site unless z can be 0:
   count_a + (p-1)[z ≥ 1] ≤ p *)
Definition mindist_dup_def:
  mindist_dup Z name p zlo zhi pm sites =
  if zhi ≤ 0 then Nil else
  let amo = (1 ≤ zlo) in
  flat_app (MAP (λa.
    let xs = lookup_any a pm [] in
    if LENGTH xs < 2 then Nil else
    let
      lbl = SOME (mk_name name («mindist_dup_» ^ toString a));
      lits = MAP (λX. Pos (INL (Eq X (&a)))) xs
    in
      if amo then List [(lbl, at_most_one lits)]
      else
        List [(lbl, ([], MAP (λl. (-1,l)) lits ++
          [(1 - &p, reif_gen (Z,Lexop GreaterEqual,1))], -&p))]) sites)
End

(* the arithmetic of one site's mindist_dup row, for a count c of its
   positions out of p and the reified B = [z ≥ 1]: the negated row read as an
   upper bound, and that bound forcing z ≤ 0 exactly when two positions are
   at the site *)
Theorem mindist_dup_arith[local]:
  (-c + (1 − p) * b2i B ≥ -p ⇔ c + (p − 1) * b2i B ≤ p) ∧
  ((zlo:int) ≤ z ∧ (zlo < 1 ⇒ (B ⇔ z ≥ 1)) ⇒
    ((if 1 ≤ zlo then LENGTH (FILTER (P:'x -> bool) l) ≤ 1
      else &LENGTH (FILTER P l) + (&LENGTH l − 1) * b2i B ≤ &LENGTH l) ⇔
    (2 ≤ LENGTH (FILTER P l) ⇒ z ≤ 0)))
Proof
  qspecl_then[`P`,`l`]assume_tac LENGTH_FILTER_LEQ>>
  Cases_on`B`>>rw[b2i_def]>>intLib.ARITH_TAC
QED

Theorem mindist_dup_sem:
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (mindist_dup Z name p zlo zhi pm sites)) ⇔
  (0 < zhi ⇒
    ∀a. MEM a sites ∧ 2 ≤ LENGTH (lookup_any a pm []) ⇒
      if 1 ≤ zlo then
        LENGTH (FILTER (λX. wb (INL (Eq X (&a)))) (lookup_any a pm [])) ≤ 1
      else
        &LENGTH (FILTER (λX. wb (INL (Eq X (&a)))) (lookup_any a pm [])) +
        (&p − 1) * b2i (lit wb (reif_gen (Z,Lexop GreaterEqual,1))) ≤ &p)
Proof
  rw[mindist_dup_def]
  >- intLib.ARITH_TAC>>
  fs[integerTheory.INT_NOT_LE]>>
  simp[EVERY_FLAT,EVERY_MAP]>>
  simp[EVERY_SND,SF COND_elim_ss]>>
  Cases_on`1 ≤ zlo`>>simp[EVERY_MEM,mindist_eq_count,cj 1 mindist_dup_arith]>>
  simp[DISJ_EQ_IMP,NOT_LESS,AND_IMP_INTRO]
QED

(* one site's mindist_dup row: two positions at the site force z ≤ 0 *)
Theorem mindist_dup_at[local]:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ∧
  mindist_faith bnd Xs Z D wi wb name (dt,xps,sites,pm,dps,levels) ∧
  varc_bnd bnd Z = (zlo,zhi) ∧
  0 < zhi ∧ MEM a sites ∧ 2 ≤ LENGTH (lookup_any a pm []) ⇒
  ((if 1 ≤ zlo then
      LENGTH (FILTER (λX. wb (INL (Eq X (&a)))) (lookup_any a pm [])) ≤ 1
    else
      &LENGTH (FILTER (λX. wb (INL (Eq X (&a)))) (lookup_any a pm [])) +
      (&LENGTH Xs − 1) * b2i (lit wb (reif_gen (Z,Lexop GreaterEqual,1))) ≤
      &LENGTH Xs) ⇔
    ∀i j. i < LENGTH Xs ∧ j < LENGTH Xs ∧ i ≠ j ∧
      varc wi (EL i Xs) = &a ∧ varc wi (EL j Xs) = &a ⇒ varc wi Z ≤ 0)
Proof
  strip_tac>>drule_then strip_assume_tac (iffLR mindist_ctx_def)>>
  drule_then strip_assume_tac (iffLR mindist_faith_def)>>
  drule_then (qspec_then`Z`mp_tac) varc_bnd_valid>>simp[]>>strip_tac>>
  drule_all_then (fn th => rewrite_tac[th]) mindist_at_filter>>
  `zlo < 1 ⇒ (lit wb (reif_gen (Z,Lexop GreaterEqual,1)) ⇔ varc wi Z ≥ 1)`
    by metis_tac[cj 1 mindist_zlits]>>
  drule_all_then (fn th => rewrite_tac[th]) (cj 2 mindist_dup_arith)>>
  simp[LENGTH_FILTER_two,PULL_EXISTS]
QED

Theorem mindist_dup_iff[local]:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ∧
  mindist_faith bnd Xs Z D wi wb name (dt,xps,sites,pm,dps,levels) ∧
  varc_bnd bnd Z = (zlo,zhi) ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (mindist_dup Z name (LENGTH Xs) zlo zhi pm sites)) ⇔
  ∀i j. i < LENGTH Xs ∧ j < LENGTH Xs ∧ i ≠ j ∧
    varc wi (EL i Xs) = varc wi (EL j Xs) ⇒ varc wi Z ≤ 0)
Proof
  strip_tac>>drule_then strip_assume_tac (iffLR mindist_ctx_def)>>
  simp[mindist_dup_sem]>>
  eq_tac>>rpt strip_tac
  >- (
    drule_then (qspec_then`Z`mp_tac) varc_bnd_valid>>simp[]>>strip_tac>>
    reverse (Cases_on`0 < zhi`)
    >- metis_tac[integerTheory.INT_LE_TRANS,integerTheory.INT_NOT_LT]>>
    drule_all mindist_same_site>>strip_tac>>
    qpat_x_assum`0 < zhi ⇒ _`drule_all>>
    drule_all_then (fn th => rewrite_tac[th]) mindist_dup_at>>
    metis_tac[])>>
  drule_all_then (fn th => rewrite_tac[th]) mindist_dup_at>>
  metis_tac[]
QED

(* (iii) pair upper bounds: ¬u_a ∨ ¬u_b ∨ [z ≤ D[a][b]] *)

(* z ≤ D[a,b] when sites a and b are both taken *)
Definition mindist_pair_def:
  mindist_pair Z name zhi dps =
  flat_app (MAP
    (λ(a,b,d).
      if zhi ≤ &d then Nil else
      List [(
        SOME (mk_name name («mindist_pair_» ^ toString a ^ «_» ^ toString b)),
        at_least_one [
          Neg (mindist_flag name «u» [&a]);
          Neg (mindist_flag name «u» [&b]);
          reif_gen (Z,Lexop LessEqual,&d)])])
    dps)
End

Theorem mindist_pair_sem:
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (mindist_pair Z name zhi dps)) ⇔
  ∀a b d. MEM (a,b,d) dps ∧ &d < zhi ⇒
    ¬wb (mindist_flag name «u» [&a]) ∨ ¬wb (mindist_flag name «u» [&b]) ∨
    lit wb (reif_gen (Z,Lexop LessEqual,&d))
Proof
  simp[mindist_pair_def]>>
  simp[EVERY_FLAT,EVERY_MAP]>>
  simp[EVERY_MEM,FORALL_PROD,SF COND_elim_ss]>>
  simp[GSYM integerTheory.INT_NOT_LT,SF CONJ_ss]>>
  simp[at_least_one_def]>>
  simp[RIGHT_AND_OVER_OR,EXISTS_OR_THM,lit_def,integerTheory.INT_NOT_LE,
    AND_IMP_INTRO]
QED

Theorem mindist_pair_iff[local]:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ∧
  mindist_faith bnd Xs Z D wi wb name (dt,xps,sites,pm,dps,levels) ∧
  varc_bnd bnd Z = (zlo,zhi) ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (mindist_pair Z name zhi dps)) ⇔
  ∀a b. a < b ∧ MEM (&a) (MAP (varc wi) Xs) ∧ MEM (&b) (MAP (varc wi) Xs) ⇒
    varc wi Z ≤ &EL b (EL a D))
Proof
  strip_tac>>drule_then strip_assume_tac (iffLR mindist_ctx_def)>>drule_then strip_assume_tac (iffLR mindist_faith_def)>>
  drule_all_then assume_tac mindist_zlits>>
  drule_all_then strip_assume_tac mindist_pos_site>>
  drule_all_then strip_assume_tac mindist_prep_facts>>
  qpat_x_assum`∀a. MEM a sites ⇔ _`kall_tac>>
  drule_then (qspec_then`Z`mp_tac) varc_bnd_valid>>simp[]>>strip_tac>>
  simp[mindist_pair_sem,PULL_EXISTS]>>
  eq_tac>>rw[]>>
  metis_tac[integerTheory.INT_LE_TRANS,integerTheory.INT_NOT_LT]
QED

(* (iv) min-attained ladder: z is at least the least realised distance *)

(* distance |-> the site pairs at that distance, in lexicographic order *)
Definition mindist_pairs_map_def:
  mindist_pairs_map (dps:(num # num # num) list) =
  FOLDR (λ(a,b,d) t. insert d ((a,b) :: lookup_any d t []) t) LN dps
End

(* the witnesses at distance t, with their definitions: at t = 0 the
   duplicate witnesses d_a ⇔ count_a ≥ 2 for each site with two candidate
   positions, and w_ab ⇔ u_a ∧ u_b for the site pairs at t *)
Definition mindist_ws_def:
  mindist_ws bnd name pm sites pmap t =
  (if t = 0 then MAP
    (λa. let d = mindist_flag name «d» [&a] in
      (cbimply_var bnd d
        ([], MAP (λX. (1, Pos (INL (Eq X (&a))))) (lookup_any a pm []), 2),
      Pos d))
    (FILTER (λa. 2 ≤ LENGTH (lookup_any a pm [])) sites)
  else []) ++
  MAP
    (λ(a,b). let w = mindist_flag name «w» [&a;&b] in
      (cbimply_var bnd w
        ([], [(1, Pos (mindist_flag name «u» [&a]));
          (1, Pos (mindist_flag name «u» [&b]))], 2),
      Pos w))
    (lookup_any t pmap [])
End

(* the min-attained ladder over the ascending levels: the guard
   [z ≥ t] ∨ m_acc at each level above z's lower bound, and below the top
   level m_t ⇔ m_acc ∨ (witnesses at distance t), where m_t holds iff two
   positions are at distance at most t *)
Definition mindist_ladder_def:
  (mindist_ladder bnd Z name zlo pm sites pmap macc [] = Nil) ∧
  (mindist_ladder bnd Z name zlo pm sites pmap macc (t::ts) =
    let
      prev = (case macc of NONE => [] | SOME m => [m]);
      guard =
        if zlo < &t then
        List [(SOME (mk_name name («mindist_guard_» ^ toString t)),
          at_least_one (reif_gen (Z,Lexop GreaterEqual,&t) :: prev))]
        else Nil
    in
      if NULL ts then guard else
      let ws = mindist_ws bnd name pm sites pmap t in
        if NULL ws then
        Append guard (mindist_ladder bnd Z name zlo pm sites pmap macc ts)
        else
          let m = mindist_flag name «m» [&t] in
            Append guard
              (Append (flat_app (MAP FST ws))
                (Append
                  (cbimply_var bnd m (at_least_one (prev ++ MAP SND ws)))
                  (mindist_ladder bnd Z name zlo pm sites pmap
                    (SOME (Pos m)) ts))))
End

Theorem MEM_mindist_pairs_map[local]:
  ∀dps. MEM (a,b) (lookup_any t (mindist_pairs_map dps) []) ⇔ MEM (a,b,t) dps
Proof
  Induct
  >- simp[mindist_pairs_map_def,lookup_any_def]>>
  simp[FORALL_PROD]>>
  gvs[mindist_pairs_map_def,lookup_any_insert]>>
  rw[]>>simp[]
QED

(* one step down the ascending levels t0::ts, upward closed under P: the
   tail keeps both properties, "below every later level" means "at most t0",
   t0 is the minimum, and t0 is not the last level *)
Theorem mindist_level_step[local]:
  SORTED $< ((t0:num)::ts) ∧
  (∀d t. P d ∧ MEM t (t0::ts) ∧ t ≤ d ⇒ MEM d (t0::ts)) ⇒
  SORTED $< ts ∧
  (∀d t. P d ∧ MEM t ts ∧ t ≤ d ⇒ MEM d ts) ∧
  ((∃d. P d ∧ ∀t. MEM t ts ⇒ d < t) ⇔ ∃d. P d ∧ d ≤ t0) ∧
  (∀d. (∀t. t = t0 ∨ MEM t ts ⇒ d < t) ⇔ d < t0) ∧
  (ts ≠ [] ⇒ LAST (t0::ts) = LAST ts ∧ t0 ≠ LAST ts)
Proof
  rw[SORTED_EQ,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,DISJ_IMP_THM,
    FORALL_AND_THM,EQ_IMP_THM,LAST_CONS_cond]
  >- (
    first_x_assum drule_all>>rw[]>>
    qpat_x_assum`∀y. MEM y ts ⇒ _`drule>>decide_tac)
  >- (
    first_assum (irule_at Any)>>
    spose_not_then (assume_tac o SRULE[NOT_LESS_EQUAL])>>
    drule_then assume_tac LESS_IMP_LESS_OR_EQ>>
    qpat_x_assum`∀d. P d ∧ t0 ≤ d ⇒ _`drule_all>>rw[]>>strip_tac>>
    qpat_x_assum`∀t. MEM t ts ⇒ d < t`drule>>simp[])
  >- (
    first_assum (irule_at Any)>>rw[]>>
    qpat_x_assum`∀y. MEM y ts ⇒ _`drule>>decide_tac)
  >- (first_x_assum drule>>decide_tac)>>
  drule_then (assume_tac o SRULE[]) MEM_LAST_NOT_NIL>>
  qpat_x_assum`∀y. MEM y ts ⇒ _`drule>>decide_tac
QED

Theorem EXISTS_LE_SPLIT[local]:
  (∃d. P d ∧ d ≤ t) ⇔ (∃d. P d ∧ d < t) ∨ P (t:num)
Proof
  simp[LESS_OR_EQ,LEFT_AND_OVER_OR,EXISTS_OR_THM]
QED

(* the ladder's guard at level t: [z ≥ t] or the accumulated m, with the
   accumulated m read as an optional literal *)
Theorem mindist_guard_sem[local]:
  ((∃l. MEM l (case macc of NONE => [] | SOME m => [m]) ∧ lit wb l) ⇔
    case macc of NONE => F | SOME l => lit wb l) ∧
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (
    if (zlo:int) < &(t:num) then
    List [(
      lbl,
      at_least_one (reif_gen (Z,Lexop GreaterEqual,&t) ::
        case macc of NONE => [] | SOME m => [m]))]
    else Nil)) ⇔
  (zlo < &t ⇒
    lit wb (reif_gen (Z,Lexop GreaterEqual,&t)) ∨
    case macc of NONE => F | SOME l => lit wb l))
Proof
  Cases_on`macc`>>rw[RIGHT_AND_OVER_OR,EXISTS_OR_THM]
QED

Theorem mindist_ladder_sem:
  ∀ts macc.
    valid_assignment bnd wi ∧ SORTED $< ts ∧
    (∀d t. Pd d ∧ MEM t ts ∧ t ≤ d ⇒ MEM d ts) ∧
    (∀t. MEM t ts ∧ zlo < &t ⇒
      (lit wb (reif_gen (Z,Lexop GreaterEqual,&t)) ⇔ varc wi Z ≥ &t)) ∧
    (∀t.
      MEM t ts ∧
      EVERY (λx. iconstraint_sem x (wi,wb))
        (abstr (flat_app (MAP FST (mindist_ws bnd name pm sites prm t)))) ⇒
      ((∃w. MEM w (mindist_ws bnd name pm sites prm t) ∧ lit wb (SND w)) ⇔
      Pd t)) ∧
    ((case macc of NONE => F | SOME l => lit wb l) ⇔
      ∃d. Pd d ∧ ∀t. MEM t ts ⇒ d < t) ⇒
    (EVERY (λx. iconstraint_sem x (wi,wb))
      (abstr (mindist_ladder bnd Z name zlo pm sites prm macc ts)) ⇔
    (∀t. MEM t ts ∧ t ≠ LAST ts ⇒
      EVERY (λx. iconstraint_sem x (wi,wb))
        (abstr (flat_app (MAP FST (mindist_ws bnd name pm sites prm t)))) ∧
      (¬NULL (mindist_ws bnd name pm sites prm t) ⇒
        (wb (mindist_flag name «m» [&t]) ⇔ ∃d. Pd d ∧ d ≤ t))) ∧
    (∀t. MEM t ts ∧ zlo < &t ⇒ varc wi Z ≥ &t ∨ ∃d. Pd d ∧ d < t))
Proof
  Induct
  >- simp[mindist_ladder_def]>>
  rpt gen_tac>>strip_tac>>
  rename1`t0::ts`>>
  drule_all_then strip_assume_tac mindist_level_step>>
  fs[]>>
  fs[RIGHT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM]>>
  Cases_on`ts = []`
  >- simp[mindist_ladder_def,mindist_guard_sem]>>
  fs[]>>
  simp[Once mindist_ladder_def,NULL_EQ]>>
  Cases_on`mindist_ws bnd name pm sites prm t0 = []`
  >- (
    simp[mindist_guard_sem]>>
    qpat_x_assum`∀m. _ ⇒ (_ (abstr (mindist_ladder _ _ _ _ _ _ _ m _)) ⇔ _)`
      (DEP_ONCE_REWRITE_TAC o single)>>
    gvs[EXISTS_LE_SPLIT,NULL_EQ]>>asm_rewrite_tac[]>>
    simp[AC CONJ_ASSOC CONJ_COMM])>>
  simp[mindist_guard_sem,MEM_MAP,RIGHT_AND_OVER_OR,EXISTS_OR_THM,PULL_EXISTS]>>
  reverse (Cases_on`EVERY (λx. iconstraint_sem x (wi,wb))
    (FLAT (MAP (λls. abstr ls) (MAP FST (mindist_ws bnd name pm sites prm t0))))`)
  >- asm_rewrite_tac[]>>
  gvs[EXISTS_LE_SPLIT]>>
  Cases_on`wb (mindist_flag name «m» [&t0]) ⇔ (∃d. Pd d ∧ d < t0) ∨ Pd t0`>>
  gvs[]>>
  qpat_x_assum`∀m. _ ⇒ (_ (abstr (mindist_ladder _ _ _ _ _ _ _ m _)) ⇔ _)`
    (DEP_ONCE_REWRITE_TAC o single)>>
  gvs[NULL_EQ]>>asm_rewrite_tac[]>>
  simp[AC CONJ_ASSOC CONJ_COMM]
QED

(* a level's witnesses: their definition rows, and which of them are set *)
Theorem mindist_ws_sem[local]:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (FLAT (MAP
    (λls. abstr ls)
    (MAP FST (mindist_ws bnd name pm sites prm t)))) ⇔
  (t = 0 ⇒ ∀a. MEM a sites ∧ 2 ≤ LENGTH (lookup_any a pm []) ⇒
    (wb (mindist_flag name «d» [&a]) ⇔
       2 ≤ LENGTH (FILTER (λX. wb (INL (Eq X (&a)))) (lookup_any a pm [])))) ∧
    (∀a b. MEM (a,b) (lookup_any t prm []) ⇒
      (wb (mindist_flag name «w» [&a;&b]) ⇔
        wb (mindist_flag name «u» [&a]) ∧ wb (mindist_flag name «u» [&b])))) ∧
  ((∃w. MEM w (mindist_ws bnd name pm sites prm t) ∧ lit wb (SND w)) ⇔
    (t = 0 ∧ ∃a. MEM a sites ∧ 2 ≤ LENGTH (lookup_any a pm []) ∧
      wb (mindist_flag name «d» [&a])) ∨
    ∃a b. MEM (a,b) (lookup_any t prm []) ∧ wb (mindist_flag name «w» [&a;&b]))
Proof
  strip_tac>>
  `EVERY (λx. iconstraint_sem x (wi,wb))
    (FLAT (MAP (λls. abstr ls) (MAP FST (mindist_ws bnd name pm sites prm t)))) ⇔
    ∀w. MEM w (mindist_ws bnd name pm sites prm t) ⇒
      EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (FST w))`
    by (rw[EVERY_FLAT,EVERY_MEM,MEM_MAP,PULL_EXISTS]>>metis_tac[])>>
  pop_assum (fn th => rewrite_tac[th])>>
  Cases_on`t = 0`>>
  simp[mindist_ws_def,RIGHT_AND_OVER_OR,EXISTS_OR_THM]>>
  simp[MEM_MAP,MEM_FILTER,PULL_EXISTS,FORALL_PROD,EXISTS_PROD,
    EVERY_REVERSE,iconstraint_sem_def,mindist_eq_count,DISJ_IMP_THM,
    FORALL_AND_THM,eval_lin_term_def,iSUM_def,lit_def]>>
  simp[integerTheory.int_ge]>>
  metis_tac[]
QED

Theorem mindist_realised_level[local]:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ∧
  mindist_realised Xs D wi d ⇒
  MEM d levels
Proof
  strip_tac>>drule_then strip_assume_tac (iffLR mindist_ctx_def)>>
  drule_all_then strip_assume_tac mindist_pos_site>>
  drule_all_then strip_assume_tac mindist_prep_facts>>
  qpat_x_assum`∀a. MEM a sites ⇔ _`kall_tac>>
  drule_all_then (fn th => fs[th]) (cj 1 mindist_realised_thm)>>
  metis_tac[]
QED

(* a set duplicate witness d_a means two positions share a value *)
Theorem mindist_dup_wits[local]:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ∧
  mindist_faith bnd Xs Z D wi wb name (dt,xps,sites,pm,dps,levels) ∧
  (∀a. MEM a sites ∧ 2 ≤ LENGTH (lookup_any a pm []) ⇒
    (wb (mindist_flag name «d» [&a]) ⇔
      2 ≤ LENGTH (FILTER (λX. wb (INL (Eq X (&a)))) (lookup_any a pm [])))) ⇒
  ((∃a. MEM a sites ∧ 2 ≤ LENGTH (lookup_any a pm []) ∧
        wb (mindist_flag name «d» [&a])) ⇔
    ∃i j. i < LENGTH Xs ∧ j < LENGTH Xs ∧ i ≠ j ∧
      varc wi (EL i Xs) = varc wi (EL j Xs))
Proof
  strip_tac>>eq_tac>>strip_tac
  >- (
    qpat_x_assum`∀a. _ ∧ _ ⇒ (wb _ ⇔ _)`drule_all>>
    drule_all_then (fn th => rewrite_tac[th]) mindist_at_filter>>
    gvs[LENGTH_FILTER_two]>>
    strip_tac>>qpat_assum`_ ≠ _`(irule_at Any)>>fs[])>>
  drule_all_then strip_assume_tac mindist_same_site>>
  qpat_assum`MEM a sites`(irule_at Any)>>
  qpat_x_assum`∀a. _ ∧ _ ⇒ (wb _ ⇔ _)`drule_all>>
  drule_all_then (fn th => rewrite_tac[th]) mindist_at_filter>>
  gvs[LENGTH_FILTER_two]>>
  strip_tac>>qpat_assum`_ ≠ _`(irule_at Any)>>fs[]
QED

(* a set pair witness w_ab at distance t means two values a < b that
   positions take are at distance t *)
Theorem mindist_pair_wits[local]:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ∧
  mindist_faith bnd Xs Z D wi wb name (dt,xps,sites,pm,dps,levels) ∧
  (∀a b. MEM (a,b) (lookup_any t (mindist_pairs_map dps) []) ⇒
    (wb (mindist_flag name «w» [&a;&b]) ⇔
      wb (mindist_flag name «u» [&a]) ∧ wb (mindist_flag name «u» [&b]))) ⇒
  ((∃a b. MEM (a,b) (lookup_any t (mindist_pairs_map dps) []) ∧
          wb (mindist_flag name «w» [&a;&b])) ⇔
    ∃a b. a < b ∧ MEM (&a) (MAP (varc wi) Xs) ∧ MEM (&b) (MAP (varc wi) Xs) ∧
      EL b (EL a D) = t)
Proof
  strip_tac>>drule_then strip_assume_tac (iffLR mindist_ctx_def)>>drule_then strip_assume_tac (iffLR mindist_faith_def)>>
  drule_all_then strip_assume_tac mindist_pos_site>>
  drule_all_then strip_assume_tac mindist_prep_facts>>
  qpat_x_assum`∀a. MEM a sites ⇔ _`kall_tac>>
  fs[MEM_mindist_pairs_map]>>
  metis_tac[]
QED

Theorem mindist_wit_realised[local]:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ∧
  mindist_faith bnd Xs Z D wi wb name (dt,xps,sites,pm,dps,levels) ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (FLAT (MAP (λls. abstr ls) (MAP FST
      (mindist_ws bnd name pm sites
        (mindist_pairs_map dps) t)))) ⇒
  ((∃w. MEM w (mindist_ws bnd name pm sites (mindist_pairs_map dps) t) ∧
      lit wb (SND w)) ⇔
  mindist_realised Xs D wi t)
Proof
  strip_tac>>drule_then strip_assume_tac (iffLR mindist_ctx_def)>>
  drule_then (fn th => fs[th]) mindist_ws_sem>>
  drule_all_then (fn th => rewrite_tac[th]) (cj 1 mindist_realised_thm)>>
  drule_all_then (fn th => rewrite_tac[th]) mindist_pair_wits>>
  Cases_on`t = 0`>>gvs[]>>
  drule_all_then (fn th => rewrite_tac[th]) mindist_dup_wits
QED

Theorem mindist_ladder_inst[local]:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ∧
  mindist_faith bnd Xs Z D wi wb name (dt,xps,sites,pm,dps,levels) ∧
  varc_bnd bnd Z = (zlo,zhi) ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (mindist_ladder bnd Z name zlo pm sites
      (mindist_pairs_map dps) NONE levels)) ⇔
    (∀t. MEM t levels ∧ t ≠ LAST levels ⇒
      EVERY (λx. iconstraint_sem x (wi,wb))
        (abstr (flat_app (MAP FST (mindist_ws bnd name
          pm sites (mindist_pairs_map dps) t)))) ∧
      (¬NULL (mindist_ws bnd name pm sites (mindist_pairs_map dps) t) ⇒
        (wb (mindist_flag name «m» [&t]) ⇔
        ∃d. mindist_realised Xs D wi d ∧ d ≤ t))) ∧
    (∀t. MEM t levels ∧ zlo < &t ⇒
      varc wi Z ≥ &t ∨ ∃d. mindist_realised Xs D wi d ∧ d < t))
Proof
  strip_tac>>drule_then strip_assume_tac (iffLR mindist_ctx_def)>>
  drule_then strip_assume_tac (iffLR mindist_faith_def)>>
  irule mindist_ladder_sem>>
  drule_all mindist_prep_facts>>strip_tac>>
  rpt conj_tac
  >- (rpt strip_tac>>drule_all mindist_realised_level>>simp[])
  >- (
    rpt strip_tac>>
    qpat_x_assum`EVERY _ (abstr (flat_app _))`(assume_tac o SRULE[])>>
    drule_all mindist_wit_realised>>simp[])
  >- (
    rpt strip_tac>>
    drule_all (cj 3 mindist_zlits)>>simp[])
  >- (simp[]>>metis_tac[DECIDE ``∀d:num. ¬(d < 0)``])>>
  simp[]
QED

Theorem mindist_attain[local]:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ∧
  2 ≤ LENGTH Xs ∧
  mindist_faith bnd Xs Z D wi wb name (dt,xps,sites,pm,dps,levels) ∧
  varc_bnd bnd Z = (zlo,zhi) ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (if EXISTS (λt. zlo < &t) levels then
      mindist_ladder bnd Z name zlo pm sites
        (mindist_pairs_map dps) NONE levels
      else Nil)) ∧
  (∀d. mindist_realised Xs D wi d ⇒ varc wi Z ≤ &d) ⇒
  0 ≤ varc wi Z ∧ mindist_realised Xs D wi (Num (varc wi Z))
Proof
  strip_tac>>drule_then strip_assume_tac (iffLR mindist_ctx_def)>>
  drule_then strip_assume_tac (iffLR mindist_faith_def)>>
  drule_then (qspec_then`Z`mp_tac) varc_bnd_valid>>simp[]>>strip_tac>>
  (* mu: the least realised distance *)
  `∃mu. mindist_realised Xs D wi mu ∧ ∀d. d < mu ⇒ ¬mindist_realised Xs D wi d`
    by (irule arithmeticTheory.WOP>>
        simp[mindist_realised_def,PULL_EXISTS]>>
        qexistsl_tac[`0`,`1`]>>simp[])>>
  `varc wi Z = &mu` suffices_by simp[]>>
  simp[GSYM integerTheory.INT_LE_ANTISYM]>>
  (* z < mu would violate the ladder's guard at level mu *)
  CCONTR_TAC>>
  fs[integerTheory.INT_NOT_LE]>>
  drule_all mindist_realised_level>>strip_tac>>
  `zlo < &mu` by metis_tac[integerTheory.INT_LET_TRANS]>>
  qpat_x_assum`EVERY _ (abstr (if _ then _ else _))`
    (mp_tac o SRULE[SF COND_elim_ss,DISJ_EQ_IMP])>>
  impl_tac
  >- (simp[EXISTS_MEM]>>first_assum (irule_at Any)>>simp[])>>
  strip_tac>>
  drule_all_then (fn th => fs[th]) mindist_ladder_inst>>
  qpat_x_assum`∀t. MEM t levels ∧ zlo < &t ⇒ _`drule_all>>
  strip_tac
  >- metis_tac[integerTheory.int_ge,integerTheory.INT_NOT_LE]>>
  metis_tac[]
QED

(* (v) requirement clauses: x_i ≠ a ∨ x_j ≠ b when D[a][b] < R_ij *)

(* requirements: positions i < j cannot take sites closer than R[i,j]. The
   scan over both positions' sites is inherent: each test decides a row. *)
Definition mindist_req_row_def:
  (mindist_req_row dt name pre j Xi psi ((Xj,psj)::xps) (r::rs) =
    Append
      (if r ≤ 0 then Nil else
        let pre_j = pre ^ toString j ^ «_» in
        flat_app (MAP (λa.
          let pre_a = pre_j ^ toString a ^ «_» in
          flat_app (MAP (λb.
            if &(mindist_dist dt a b) < r then
              List [(
                SOME (mk_name name (pre_a ^ toString b)),
                at_least_one [
                  Neg (INL (Eq Xi (&a)));
                  Neg (INL (Eq Xj (&b)))])]
            else Nil) psj)) psi))
      (mindist_req_row dt name pre (j+1) Xi psi xps rs)) ∧
  (mindist_req_row dt name pre j Xi psi _ _ = Nil)
End

Definition mindist_req_def:
  (mindist_req dt name i ((Xi,psi)::xps) (Ri::Rs) =
    Append
      (mindist_req_row dt name («mindist_req_» ^ toString i ^ «_») (i+1)
        Xi psi xps (DROP (i+1) Ri))
      (mindist_req dt name (i+1) xps Rs)) ∧
  (mindist_req dt name i _ _ = Nil)
End

Theorem mindist_req_row_sem[local]:
  ∀xps rs j.
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (mindist_req_row dt name pre j Xi psi xps rs)) ⇔
  ∀m a b.
    m < LENGTH xps ∧ m < LENGTH rs ∧ MEM a psi ∧ MEM b (SND (EL m xps)) ∧
    &mindist_dist dt a b < EL m rs ⇒
    ¬wb (INL (Eq Xi (&a))) ∨ ¬wb (INL (Eq (FST (EL m xps)) (&b)))
Proof
  Induct>>simp[mindist_req_row_def]>>
  gen_tac>>PairCases_on`h`>>rename1`(Xj,psj)::xps`>>
  namedCases_on`rs`["","r rs"]>>simp[mindist_req_row_def]>>
  gen_tac>>
  CONV_TAC (RAND_CONV (HO_REWR_CONV arithmeticTheory.FORALL_NUM))>>
  simp[SF COND_elim_ss,MAP_MAP_o,o_DEF]>>
  simp[EVERY_FLAT,EVERY_MAP]>>
  simp[EVERY_MEM,SF COND_elim_ss,RIGHT_AND_OVER_OR,EXISTS_OR_THM,lit_def]>>
  Cases_on`r ≤ 0`>>
  fs[AND_IMP_INTRO,GSYM RIGHT_FORALL_IMP_THM,GSYM CONJ_ASSOC,
    intLib.ARITH_PROVE``r ≤ 0 ⇒ ¬(&n < r:int)``]
QED

Theorem mindist_req_sem:
  ∀xps Rs i.
  EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (mindist_req dt name i xps Rs)) ⇔
  ∀k m a b.
    k < LENGTH xps ∧ k < LENGTH Rs ∧
    m < LENGTH (DROP (k + 1) xps) ∧ m < LENGTH (DROP (k + i + 1) (EL k Rs)) ∧
    MEM a (SND (EL k xps)) ∧ MEM b (SND (EL m (DROP (k + 1) xps))) ∧
    &mindist_dist dt a b < EL m (DROP (k + i + 1) (EL k Rs)) ⇒
    ¬wb (INL (Eq (FST (EL k xps)) (&a))) ∨
    ¬wb (INL (Eq (FST (EL m (DROP (k + 1) xps))) (&b)))
Proof
  Induct>>simp[mindist_req_def]>>
  gen_tac>>PairCases_on`h`>>rename1`(Xi,psi)::xps`>>
  namedCases_on`Rs`["","R Rs"]>>simp[mindist_req_def,mindist_req_row_sem]>>
  gen_tac>>
  CONV_TAC (RAND_CONV (HO_REWR_CONV arithmeticTheory.FORALL_NUM))>>
  simp[ADD1]
QED

Theorem mindist_req_iff[local]:
  mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ∧
  mindist_faith bnd Xs Z D wi wb name (dt,xps,sites,pm,dps,levels) ∧
  LENGTH R = LENGTH Xs ∧ EVERY (λrow. LENGTH row = LENGTH Xs) R ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (mindist_req dt name 0 xps R)) ⇔
  ∀i j. i < j ∧ j < LENGTH Xs ⇒
    EL j (EL i R) ≤
      &pos_dist D Xs wi i j)
Proof
  strip_tac>>drule_then strip_assume_tac (iffLR mindist_ctx_def)>>
  drule_then strip_assume_tac (iffLR mindist_faith_def)>>
  drule_all_then strip_assume_tac mindist_prep_facts>>
  gvs[mindist_req_sem,EL_DROP,EL_MAP,pos_dist_def]>>
  eq_tac>>rpt strip_tac
  >- (
    (* R[i][j] > dist i j would violate the row for the two current sites *)
    CCONTR_TAC>>fs[integerTheory.INT_NOT_LE]>>
    `LENGTH (EL i R) = LENGTH Xs ∧
      0 ≤ varc wi (EL i Xs) ∧ Num (varc wi (EL i Xs)) < LENGTH D ∧
      0 ≤ varc wi (EL j Xs) ∧ Num (varc wi (EL j Xs)) < LENGTH D` by gvs[EVERY_EL]>>
    qpat_x_assum`∀k m a b. _`(qspecl_then[`i`,`j − (i + 1)`,
      `Num (varc wi (EL i Xs))`,`Num (varc wi (EL j Xs))`]mp_tac)>>
    simp[EL_DROP,EL_MAP,mindist_val_psites,EL_MEM,integerTheory.INT_OF_NUM]>>
    gvs[mindist_dist_dtab,EVERY_EL])>>
  (* a violated row would put two positions closer than R allows *)
  `LENGTH (EL k R) = LENGTH Xs` by gvs[EVERY_EL]>>
  `a < LENGTH D ∧ b < LENGTH D` by gvs[mindist_psites_thm,EL_DROP,EL_MAP]>>
  gvs[EL_DROP,EL_MAP,mindist_dist_dtab,EVERY_EL]>>
  simp[EL_MEM]>>CCONTR_TAC>>fs[]>>
  qpat_x_assum`∀i j. _`(qspecl_then[`k`,`k + (m + 1)`]mp_tac)>>
  simp[integerTheory.INT_NOT_LE]
QED

(* the assembled encoder and its correctness *)

Definition mindist_rows_def:
  mindist_rows bnd Xs Z optR name n (dt,xps,sites,pm,dps,levels) =
  let
    (zlo,zhi) = varc_bnd bnd Z;
    reqs = (case optR of NONE => Nil | SOME R => mindist_req dt name 0 xps R);
    ladder =
      if EXISTS (λt. zlo < &t) levels then
        mindist_ladder bnd Z name zlo pm sites
          (mindist_pairs_map dps) NONE levels
      else Nil
  in
    flat_app [
      cmk_bounds_all bnd name «X_» Xs 0 (&n - 1);
      mindist_used bnd name pm sites;
      mindist_dup Z name (LENGTH Xs) zlo zhi pm sites;
      mindist_pair Z name zhi dps;
      reqs; ladder]
End

Definition cencode_mindistance_def:
  cencode_mindistance bnd Xs Z D optR name ec =
  if ¬mindist_valid (LENGTH Xs) D optR then (cfalse_constr, ec) else
  let
    pr = mindist_prep bnd Xs D;
    (dt,xps,sites,pm,dps,levels) = pr;
    (eqs,ec1) = cencode_full_eqs bnd (mindist_eqpairs xps) ec;
    (zs,ec2) = fold_cenc (cencode_reif_gen bnd)
      (mindist_ztriples bnd Z pm sites dps levels) ec1
  in
    (Append eqs (Append zs
      (mindist_rows bnd Xs Z optR name (LENGTH D) pr)), ec2)
End

Definition encode_mindistance_def:
  encode_mindistance bnd Xs Z D optR name =
  if ¬mindist_valid (LENGTH Xs) D optR then abstr cfalse_constr else
  let
    pr = mindist_prep bnd Xs D;
    (dt,xps,sites,pm,dps,levels) = pr
  in
    FLAT (MAP (λ(X,v). encode_full_eq bnd X v) (mindist_eqpairs xps)) ++
    FLAT (MAP (encode_reif_gen bnd)
      (mindist_ztriples bnd Z pm sites dps levels)) ++
    abstr (mindist_rows bnd Xs Z optR name (LENGTH D) pr)
End

Theorem cencode_mindistance_sem:
  valid_assignment bnd wi ∧
  cencode_mindistance bnd Xs Z D optR name ec = (es, ec') ⇒
  enc_rel wi es (encode_mindistance bnd Xs Z D optR name) ec ec'
Proof
  rw[cencode_mindistance_def,encode_mindistance_def]>>
  rpt (pairarg_tac>>gvs[])>>
  REWRITE_TAC[GSYM APPEND_ASSOC]>>
  irule enc_rel_Append>>qexists_tac`ec1`>>conj_tac
  >- (irule enc_rel_cencode_full_eqs>>simp[])>>
  irule enc_rel_Append>>qexists_tac`ec'`>>simp[]>>
  irule enc_rel_fold_cenc>>
  first_x_assum (irule_at Any)>>
  rw[]>>
  irule enc_rel_encode_reif_gen>>simp[]
QED

Theorem encode_mindistance_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Misc (MinDistance Xs Z D optR)) ∧
  mindistance_sem Xs Z D optR wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_mindistance bnd Xs Z D optR name)
Proof
  simp[SF CONJ_ss,mindistance_sem_def,cj 3 mindist_realised_thm,
    cj 4 mindist_realised_thm]>>
  rw[encode_mindistance_def]
  >- (
    gvs[mindist_valid_thm,mindist_realised_def,EVERY_EL]>>
    Cases_on`optR`>>gvs[])>>
  pairarg_tac>>gvs[mindist_rows_def]>>
  pairarg_tac>>gvs[]>>
  drule_then assume_tac mindist_reify_flags>>
  drule_all_then (fn th => fs[th]) (cj 5 mindist_realised_thm)>>
  `mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels) ∧
    mindist_faith bnd Xs Z D wi (reify_avar cs wi) name
      (dt,xps,sites,pm,dps,levels)`
    by simp[mindist_ctx_def,mindist_faith_def,reify_avar_def,reify_reif_def,
      lit_reify_avar_reif_gen_alt]>>
  drule_then strip_assume_tac (iffLR mindist_faith_def)>>
  rpt conj_tac
  >- simp[encode_full_eqs_reify]
  >- simp[EVERY_FLAT,EVERY_MAP,encode_reif_gen_sem_reify_avar]
  >- simp[mindist_range_sem]
  >- (drule_all mindist_used_iff>>simp[])
  >- drule_all_then (fn th => asm_rewrite_tac[th]) mindist_dup_iff
  >- drule_all_then (fn th => asm_rewrite_tac[th]) mindist_pair_iff
  >- (Cases_on`optR`>>gvs[]>>drule_all mindist_req_iff>>simp[])>>
  simp[SF COND_elim_ss,DISJ_EQ_IMP]>>strip_tac>>
  drule_all_then (fn th => simp[th]) mindist_ladder_inst>>
  simp[mindist_ws_sem]>>
  conj_tac
  >- (rpt strip_tac>>drule_all_then (fn th => simp[th]) mindist_at_filter)>>
  rpt strip_tac>>
  qpat_x_assum`0 ≤ varc wi Z`
    (strip_assume_tac o MATCH_MP integerTheory.NUM_POSINT_EXISTS)>>
  gvs[]>>
  Cases_on`t ≤ n`>>simp[integerTheory.int_ge]>>
  first_assum (irule_at Any)>>simp[]
QED

Theorem encode_mindistance_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_mindistance bnd Xs Z D optR name) ⇒
  mindistance_sem Xs Z D optR wi
Proof
  strip_tac>>
  reverse (Cases_on`mindist_valid (LENGTH Xs) D optR`)
  >- gvs[encode_mindistance_def,cfalse_constr_def]>>
  gvs[encode_mindistance_def]>>
  pairarg_tac>>gvs[mindist_rows_def]>>
  pairarg_tac>>gvs[]>>
  qpat_assum`mindist_valid _ _ _`(strip_assume_tac o SRULE[mindist_valid_thm])>>
  drule_all_then (fn th => fs[th]) mindist_range_sem>>
  `mindist_ctx bnd Xs D wi (dt,xps,sites,pm,dps,levels)`
    by simp[mindist_ctx_def]>>
  drule_all_then strip_assume_tac mindist_atoms_faithful>>
  drule_all_then (fn th => fs[th]) mindist_used_iff>>
  `mindist_faith bnd Xs Z D wi wb name (dt,xps,sites,pm,dps,levels)`
    by simp[mindist_faith_def]>>
  drule_all_then (fn th => fs[th]) mindist_dup_iff>>
  drule_all_then (fn th => fs[th]) mindist_pair_iff>>
  simp[mindistance_sem_def,cj 3 mindist_realised_thm,cj 4 mindist_realised_thm]>>
  conj_asm1_tac
  >- drule_all_then (fn th => asm_rewrite_tac[th]) (cj 5 mindist_realised_thm)>>
  drule_all mindist_attain>>strip_tac>>
  simp[]>>
  Cases_on`optR`>>gvs[]>>
  drule_all_then (fn th => fs[th]) mindist_req_iff
QED

Definition encode_misc_constr_def:
  encode_misc_constr bnd c name =
  case c of
    Circuit Xs =>
    encode_circuit bnd Xs name
  | Knapsack css Xs Ts =>
    encode_knapsack css Xs Ts name
  | MinDistance Xs Z D optR =>
    encode_mindistance bnd Xs Z D optR name
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
  >- metis_tac[encode_mindistance_sem_1]
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
  >- metis_tac[encode_mindistance_sem_2]
QED

(* Concrete encodings *)
Definition cencode_misc_constr_def:
  cencode_misc_constr bnd c name ec =
  case c of
    Circuit Xs =>
    cencode_circuit bnd Xs name ec
  | Knapsack css Xs Ts =>
    (cencode_knapsack css Xs Ts name, ec)
  | MinDistance Xs Z D optR =>
    cencode_mindistance bnd Xs Z D optR name ec
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
  >- metis_tac[cencode_mindistance_sem]
QED
