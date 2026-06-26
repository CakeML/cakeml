(*
  Formalization of the CP to ILP phase (misc constraints)
*)
Theory cp_to_ilp_misc
Libs
  preamble
Ancestors
  pbc cp ilp ilp_to_pb
  cp_to_ilp cp_to_ilp_linear cp_to_ilp_counting

(***
  TODO: move this (and dependency on ilp_to_pb.
  Proof-only integer variables, encoded in binary (reusable).

  The CP to ILP encoding supports only fresh Boolean reif/flag vars.

  For now, we only need upper-bounded natural numbers, i.e.,
    in the range 0 ≤ n < UB.

  Each such n will be represented with sufficient bits to fit UB.
***)

(* a * (Σ As) + b * (Σ Bs) ≥ c, where As,Bs are weighted-literal sums *)
Definition mk_constraint_ge_bin_def[simp]:
  mk_constraint_ge_bin (a:int) As (b:int) Bs (c:int) =
  ([],
  MAP (λ(ai,li). (a * ai, li)) As ++
    MAP (λ(bi,li). (b * bi, li)) Bs,
  c)
End

(* Σ As ≥ lbnd *)
Definition mk_lbnd_bin_def[simp]:
  mk_lbnd_bin As lbnd =
  mk_constraint_ge_bin 1 As 0 [] lbnd
End

(* Σ As ≤ ubnd *)
Definition mk_ubnd_bin_def[simp]:
  mk_ubnd_bin As ubnd =
  mk_constraint_ge_bin (-1) As 0 [] (-ubnd)
End

(* the pair of constraints [Σ As ≥ lbnd; Σ As ≤ ubnd] *)
Definition mk_bounds_bin_def[simp]:
  mk_bounds_bin As lbnd ubnd =
  [mk_lbnd_bin As lbnd;mk_ubnd_bin As ubnd]
End

(* Generates the sum-of-bits sequence for an
  upper bounded number (<= n)
  name[p,b0] + 2 * name[p,b1]  + ... *)
Definition ub_num_def:
  ub_num name (p:num) (n:num) =
  let h = LENGTH (bits_of_num n) in
  GENLIST (λi. (&(2**i),
    Pos $ neiv name p i (SOME «bin»))) h
End

Theorem ub_num_num_of_bits:
  eval_lin_term wb (ub_num name p n) =
  &num_of_bits (GENLIST (λi.
    wb (neiv name p i (SOME «bin»))) (LENGTH (bits_of_num n)))
Proof
  rw[num_of_bits_GENLIST,ub_num_def,eval_lin_term_def,MAP_GENLIST,o_DEF]
QED

Theorem ub_num_neg:
  eval_lin_term wb (MAP (λ(ai,li). (-1 * ai,li)) (ub_num name p n)) =
  -eval_lin_term wb (ub_num name p n)
Proof
  simp[eval_lin_term_def,ub_num_def,MAP_GENLIST,o_DEF]>>
  simp[GSYM MAP_COUNT_LIST,GSYM integerTheory.INT_MUL_ASSOC,
    iSUM_MAP_lin_const]>>
  rename1‘-1 * a’>>
  simp[GSYM integerTheory.INT_NEG_MINUS1]
QED

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

Theorem abstrl_GENLIST:
  abstrl (GENLIST f n) = GENLIST (λi. SND (f i)) n
Proof
  Induct_on‘n’>>
  simp[GENLIST,SNOC_APPEND]
QED

Theorem iSUM_eq_0:
  (∀x. MEM x ls ⇒ x = 0) ⇒ iSUM ls = 0
Proof
  Induct_on‘ls’>>
  simp[iSUM_def]
QED

Theorem pair_idfun:
  (λ(a,b). (a,b)) = I
Proof
  cong_tac NONE>>
  simp[]
QED

Theorem predicate_if_else:
  P (if b then x else y) ⇔
  if b then P x else P y
Proof
  IF_CASES_TAC>>
  simp[]
QED

Theorem num_of_bits_bits_of_num_bnd:
  ∀n bnd. n ≤ bnd ⇒ num_of_bits (bits_of_num_bnd n bnd) = n
Proof
  cheat
QED

Theorem LENGTH_ZIPOP:
  LENGTH $ ZIPOP op ls1 ls2 = MAX (LENGTH ls1) (LENGTH ls2)
Proof
  cheat
QED

Theorem LENGTH_neg_list:
  LENGTH $ neg_list ls = LENGTH ls
Proof
  simp[neg_list_def]
QED

Theorem LENGTH_bits_of_num_bnd:
  ∀n bnd. n ≤ bnd ⇒ LENGTH (bits_of_num_bnd n bnd) = LENGTH (bits_of_num bnd)
Proof
  rw[bits_of_num_bnd_def,LENGTH_ZIPOP,fls_list_bnd_def,LENGTH_neg_list]>>
  cheat
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
    qmatch_goalsub_abbrev_tac‘bits_of_num_bnd m _’>>
    qmatch_goalsub_abbrev_tac‘num_of_bits (GENLIST f _) = p’>>
    ‘FINITE dom’ by (
      ‘dom = count n’ by simp[Abbr‘dom’,EXTENSION,IN_COUNT]>>
      simp[])>>
    ‘INJ step dom dom’ by (
      simp[INJ_DEF,IN_APP]>>
      cheat (* this follows from assm 0.
      consult the proof of Theorem circuit_sem_alt_strong *)
      )>>
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
    ‘num_of_bits (GENLIST f (LENGTH (bits_of_num_bnd m (n - 1)))) = p’
      suffices_by metis_tac[GSYM LENGTH_bits_of_num_bnd]>>
    simp[Abbr‘f’,GENLIST_ID]>>
    simp[num_of_bits_bits_of_num_bnd]>>
    first_assum $ drule_then assume_tac>>
    fs[Abbr‘m’,Abbr‘p’]>>
    SELECT_ELIM_TAC>>
    metis_tac[])>>
  rpt CONJ_TAC
  >-simp[iconstraint_sem_def,ub_num_neg]
  >-simp[abstrl_GENLIST,EVERY_GENLIST,iconstraint_sem_def,
      ub_num_neg,integerTheory.INT_GE,SUB_LESS_OR_EQ]
  >-(
    last_x_assum kall_tac>>
    simp[o_ABS_R,EVERY_FLAT]>>
    qmatch_goalsub_abbrev_tac‘EVERY P _’>>
    rw[EVERY_MEM,MEM_MAPi,SF DNF_ss]>>
    simp[Abbr‘P’,EVERY_FLAT,EVERY_MAP,EVERY_GENLIST]>>
    simp[predicate_if_else,iconstraint_sem_def,GSYM IMP_CONJ_THM,
      pair_idfun,ub_num_neg,reify_avar_def,reify_reif_def,
      integerTheory.INT_GE]>>
    strip_tac>>
    rename1‘if j = _ then _ _ (_ i _) = _ ⇒ _ else _’>>
    qmatch_goalsub_abbrev_tac‘if _ then P1 ⇒ Q1 else _ ⇒ P2 ⇒ Q2’>>
    ‘P1 ⇔ suc i = 0’ by simp[Abbr‘P1’,Abbr‘suc’]>>
    ‘P2 ⇔ suc i = j’ by simp[Abbr‘P2’,Abbr‘suc’,Abbr‘dom’,
      intLib.ARITH_PROVE“0 ≤ a ⇒ (a = &b ⇔ Num a = b)”]>>
    ‘Q1 ⇔ pos i + 1 = n’ by (
      last_x_assum mp_tac>>
      simp[Abbr‘dom’,Abbr‘Q1’])>>
    ‘Q2 ⇔ pos i + 1 = pos j’ by (
      simp[Abbr‘Q2’]>>
      rename1‘a + _ = b’>>
      simp[intLib.ARITH_PROVE“1 ≤ -&a + &b ∧ -1 ≤ &a + -&b ⇔ a + 1 = b”])>>
    rfs[Abbr‘dom’]>>
    first_x_assum $ drule_then kall_tac>>
    first_x_assum $ drule_then mp_tac>>
    last_x_assum mp_tac>>
    cheat)
QED

Theorem encode_circuit_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_circuit bnd Xs name) ⇒
  circuit_sem Xs wi
Proof
  cheat
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

Definition encode_knapsack_def:
  encode_knapsack css Xs ts name =
  abstr $ cencode_knapsack css Xs ts name
End

Theorem encode_knapsack_sem_1:
  knapsack_sem css Xs ts wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_knapsack css Xs ts name)
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
    (encode_knapsack css Xs ts name) ⇒
  knapsack_sem css Xs ts wi
Proof
  rw[cencode_knapsack_def,encode_knapsack_def,knapsack_sem_def]>>
  gvs[LIST_REL_EL_EQN,EVERY_FLAT,EVERY_MEM,MEM_MAPi,
    PULL_EXISTS,cencode_knapsack1_def,cfalse_constr_def]>>
  rw[]>>first_x_assum drule>>
  pairarg_tac>>rw[]>>gvs[SF DNF_ss,eval_iclin_term_CONS,EL_ZIP,EL_MAP]>>
  intLib.ARITH_TAC
QED

Definition encode_misc_constr_def:
  encode_misc_constr bnd c name =
  case c of
    Circuit Xs =>
    encode_circuit bnd Xs name
  | Knapsack css Xs ts =>
    encode_knapsack css Xs ts name
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
  | Knapsack css Xs ts =>
    (cencode_knapsack css Xs ts name, ec)
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
