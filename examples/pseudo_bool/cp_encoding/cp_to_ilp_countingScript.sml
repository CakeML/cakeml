(*
  Formalization of the CP to ILP phase (counting constraints)
*)
Theory cp_to_ilp_counting
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* AllDifferentExcept, AllDifferent is just a special case *)

(* Ensure that X is not in any of the iS *)
Definition check_neqs_def:
  check_neqs X iS =
  MAP (λv. Neg (INL (Eq X v))) iS
End

Definition cencode_all_different_except_aux_def:
  cencode_all_different_except_aux bnd Xs iS name =
  flat_app (MAPi (λi X.
    flat_app (MAPi (λj Y.
      if i < j
      then
        let neqs = check_neqs X iS ++ check_neqs Y iS in
        List [
          (SOME $ mk_name name
            (toString i ^ «gt» ^ toString j),
            bits_imply bnd (Pos (neiv name i j NONE)::neqs) (mk_gt X Y));
          (SOME $ mk_name name
            (toString i ^ «lt» ^ toString j),
            bits_imply bnd (Neg (neiv name i j NONE)::neqs) (mk_gt Y X))]
      else
        Nil) Xs)) Xs)
End

Definition cencode_all_different_except_def:
  cencode_all_different_except bnd Xs iS name ec =
  let
    (xs,ec') = cencode_eq_grid bnd Xs iS ec
  in
    (Append xs
      (cencode_all_different_except_aux bnd Xs iS name), ec')
End

Definition encode_all_different_except_aux_def:
  encode_all_different_except_aux bnd Xs iS name =
  abstr (cencode_all_different_except_aux bnd Xs iS name)
End

Definition encode_all_different_except_def:
  encode_all_different_except bnd Xs iS name =
    encode_eq_grid bnd Xs iS ++
    encode_all_different_except_aux bnd Xs iS name
End

Theorem EVERY_lit_check_neqs[simp]:
  EVERY (lit wb) (check_neqs X iS) ⇔
  ∀v. MEM v iS ⇒ ¬wb (INL (Eq X v))
Proof
  rw[check_neqs_def,EVERY_MAP]>>
  rw[EVERY_MEM]
QED

Theorem EL_FILTER[local]:
  ∀Xs n.
  n < LENGTH Xs ∧
  P (EL n Xs) ⇒
  ∃m.
    m < LENGTH (FILTER P Xs) ∧
    EL n Xs = EL m (FILTER P Xs)
Proof
  Induct>>rw[]>>
  Cases_on`n`>>gvs[]
  >- (qexists_tac`0`>>simp[])>>
  first_x_assum drule_all>>rw[]>>
  qexists_tac`SUC m`>>simp[]
QED

Theorem EL_FILTER2[local]:
  ∀Xs n n'.
  n < n' ∧
  n' < LENGTH Xs ∧
  P (EL n Xs) ∧ P (EL n' Xs) ⇒
  ∃m m'.
    m < m' ∧
    m' < LENGTH (FILTER P Xs) ∧
    EL n Xs = EL m (FILTER P Xs) ∧
    EL n' Xs = EL m' (FILTER P Xs)
Proof
  Induct>>rw[]>>
  Cases_on`n`>>
  Cases_on`n'`>>gvs[]
  >- (
    qexists_tac`0`>>simp[]>>
    drule_all EL_FILTER>>rw[]>>
    qexists_tac`SUC m`>>simp[])>>
  first_x_assum $ drule_all>>rw[]>>
  qexists_tac`SUC m`>>
  qexists_tac`SUC m'`>>
  simp[]
QED

Theorem encode_all_different_except_aux_sem_1:
  valid_assignment bnd wi ∧
  (ALOOKUP cs name = SOME (Counting (AllDifferentExcept Xs iS')) ∨
  ALOOKUP cs name = SOME (Counting (SymmetricAllDifferent (Xs,start))) ∨
  ALOOKUP cs name = SOME (Misc (Circuit Xs))) ∧
  all_different_except_sem Xs iS wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_all_different_except_aux bnd Xs iS name)
Proof
  rw[encode_all_different_except_aux_def,cencode_all_different_except_aux_def,
    all_different_except_sem_def]>>
  simp[EVERY_MEM,MEM_MAPi,MEM_FLAT,PULL_EXISTS]>>rw[]>>
  simp[reify_avar_def,reify_flag_def,reify_reif_def]>>
  gvs[FILTER_MAP,o_DEF]>>
  rw[]>>
  drule_at (Pos (el 2))
    (EL_FILTER2 |> Q.GEN `P` |> Q.ISPEC `(λx. ¬MEM (varc wi x) iS)`)>>
  simp[]>>
  disch_then drule_all>>
  rw[]>>
  gvs[EL_ALL_DISTINCT_EL_EQ,EL_MAP]>>
  rename1`varc _ (EL xx _) + -1 * varc _ (EL yy _)`>>
  first_x_assum(qspecl_then [`xx`,`yy`] mp_tac)>>
  simp[]>>
  intLib.ARITH_TAC
QED

Theorem encode_all_different_except_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting (AllDifferentExcept Xs iS')) ∧
  all_different_except_sem Xs iS wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_all_different_except bnd Xs iS name)
Proof
  rw[encode_all_different_except_def,cencode_all_different_except_def]>>
  simp[reify_avar_def,reify_flag_def,reify_reif_def]>>
  simp[encode_all_different_except_aux_sem_1]
QED

Theorem FILTER_EL[local]:
  ∀Xs n.
  n < LENGTH (FILTER P Xs) ⇒
  ∃m.
    m < LENGTH Xs ∧
    EL m Xs = EL n (FILTER P Xs) ∧
    P (EL m Xs)
Proof
  Induct>>rw[]>>
  Cases_on`n`>>gvs[]
  >- (qexists_tac`0`>>simp[])>>
  first_x_assum drule_all>>rw[]>>
  qexists_tac`SUC m`>>gvs[]
QED

Theorem FILTER_EL2[local]:
  ∀Xs n n'.
  n < n' ∧
  n' < LENGTH (FILTER P Xs) ⇒
  ∃m m'.
    m < m' ∧
    m' < LENGTH Xs ∧
    EL m Xs = EL n (FILTER P Xs) ∧
    EL m' Xs = EL n' (FILTER P Xs) ∧
    P (EL m Xs) ∧ P (EL m' Xs)
Proof
  Induct>>rw[]
  >- (
    Cases_on`n`>>
    Cases_on`n'`>>gvs[]
    >- (
      qexists_tac`0`>>simp[]>>
      drule_all FILTER_EL>>rw[]>>
      qexists_tac`SUC m`>>gvs[])
    >- (
      first_x_assum $ drule_all>>rw[]>>
      qexists_tac`SUC m`>>
      qexists_tac`SUC m'`>>
      gvs[]))>>
  first_x_assum drule_all>>rw[]>>
  qexists_tac`SUC m`>>
  qexists_tac`SUC m'`>>
  gvs[]
QED

Theorem all_different_except_sem_imp:
  (∀i j. i < j ∧ j < LENGTH Xs ⇒
    let X = EL i Xs in
    let Y = EL j Xs in
    if (wb:'a avar -> bool) (neiv (name:mlstring) i j NONE)
    then ¬ MEM (varc wi X) iS ∧  ¬ MEM (varc wi Y) iS ⇒ varc wi X > varc wi Y
    else ¬ MEM (varc wi X) iS ∧  ¬ MEM (varc wi Y) iS ⇒ varc wi Y > varc wi X) ⇒
  all_different_except_sem Xs iS wi
Proof
  rw[all_different_except_sem_def,EL_ALL_DISTINCT_EL_EQ]>>
  Cases_on`n1 = n2`>>simp[]>>
  wlog_tac `n1 < n2` [`n1`,`n2`]
  >- (
    `n2 < n1` by fs[]>>
    first_x_assum drule>>simp[])>>
  drule_all FILTER_EL2>>
  rw[]>>
  first_x_assum drule_all>>gvs[EL_MAP]>>rw[]>>
  intLib.ARITH_TAC
QED

Theorem encode_all_different_except_aux_sem_2:
  valid_assignment bnd wi ∧
  (∀X i.
    MEM X Xs ∧ MEM i iS ⇒
    (wb (INL (Ge X i)) ⇔ varc wi X ≥ i) ∧
    (wb (INL (Ge X (i + 1))) ⇔ varc wi X ≥ i + 1) ∧
    (wb (INL (Eq X i)) ⇔ varc wi X = i)) ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_all_different_except_aux bnd Xs iS name) ⇒
  all_different_except_sem Xs iS wi
Proof
  strip_tac>>
  irule all_different_except_sem_imp>>
  gs[encode_all_different_except_def]>>
  pop_assum mp_tac>>
  simp[EVERY_MEM,cencode_all_different_except_aux_def,
    encode_all_different_except_aux_def,
    MEM_FLAT,MEM_MAPi,PULL_EXISTS,SF DNF_ss]>>
  rw[]>>
  qexistsl [‘name’,‘wb’]>>
  rpt strip_tac>>
  rename1 ‘[i;j]’>>
  ‘i < LENGTH Xs’ by fs[]>>
  first_x_assum $ drule_then rev_drule>>
  simp[SF DNF_ss]>>
  rw[]>>
  qpat_x_assum`_ ⇒ _` mp_tac>>
  (* two subgoals*)
  (reverse impl_tac >- intLib.ARITH_TAC)>>
  rw[]>>
  gvs[MEM_EL,PULL_EXISTS]>>
  first_x_assum (drule_at (Pos last))>>rw[]>>
  first_assum (qspec_then`i` mp_tac)>>
  first_x_assum (qspec_then`j` mp_tac)>>
  simp[]>>
  CCONTR_TAC>>gvs[]
QED

Theorem encode_all_different_except_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_all_different_except bnd Xs iS name) ⇒
  all_different_except_sem Xs iS wi
Proof
  strip_tac>>
  irule encode_all_different_except_aux_sem_2>>
  gs[encode_all_different_except_def]>>
  metis_tac[]
QED

Theorem cencode_all_different_except_sem:
  valid_assignment bnd wi ∧
  cencode_all_different_except bnd Xs iS name ec = (es, ec') ⇒
  enc_rel wi es (encode_all_different_except bnd Xs iS name) ec ec'
Proof
  rw[cencode_all_different_except_def,encode_all_different_except_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_encode_eq_grid>>simp[]>>
  simp[encode_all_different_except_aux_def]
QED

(* These are convenient because they are reused *)
Definition cencode_all_different_def:
  cencode_all_different bnd Xs name =
  cencode_all_different_except_aux bnd Xs [] name
End

Definition encode_all_different_def:
  encode_all_different bnd Xs name =
  encode_all_different_except_aux bnd Xs [] name
End

Theorem encode_all_different_sem_1:
  valid_assignment bnd wi ∧
  (ALOOKUP cs name = SOME (Counting (AllDifferentExcept Xs iS)) ∨
  ALOOKUP cs name = SOME (Counting (SymmetricAllDifferent (Xs,start))) ∨
  ALOOKUP cs name = SOME (Misc (Circuit Xs))) ∧
  all_different_except_sem Xs [] wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_all_different bnd Xs name)
Proof
  rw[encode_all_different_def]>>
  irule encode_all_different_except_aux_sem_1>>
  simp[]
QED

Theorem encode_all_different_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_all_different bnd Xs name) ⇒
  all_different_except_sem Xs [] wi
Proof
  rw[encode_all_different_def]>>
  irule encode_all_different_except_aux_sem_2>>
  simp[]>>
  metis_tac[]
QED

Theorem encode_all_different_alt:
  encode_all_different bnd Xs name =
  abstr (cencode_all_different bnd Xs name)
Proof
  rw[cencode_all_different_def,encode_all_different_def,
    encode_all_different_except_aux_def]
QED

(* TODO: move, perhaps generalize? *)
Definition cmk_bounds_def:
  cmk_bounds name tag X a b =
  List
  (mk_annotate
    [mk_name name (tag ^ «_lb»);mk_name name (tag ^ «_ub»)]
    (mk_bounds X a b))
End

(* Give uniform bound lb ≤ Xs ≤ ub *)
Definition cmk_bounds_all_def:
  cmk_bounds_all name Xs lb ub =
  flat_app
    (MAPi
      (λi X.
        cmk_bounds name («X_» ^ toString (i+1)) X lb ub) Xs)
End

Theorem cmk_bounds_all_sem:
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (cmk_bounds_all name Xs lb ub)) ⇔
  (∀X. MEM X Xs ⇒
    varc wi X ≥ lb ∧ varc wi X ≤ ub)
Proof
  rw[cmk_bounds_all_def,EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi]>>
  simp[PULL_EXISTS,cmk_bounds_def,MEM_EL]
QED

Definition cencode_symmetric_all_different_aux_def:
  cencode_symmetric_all_different_aux bnd Xs start name =
  let n = LENGTH Xs in
  Append
  (* All different *)
  (cencode_all_different bnd Xs name)
  (* Range *)
  (Append (cmk_bounds_all name Xs start (start + &n -1))
  (* Involution *)
  (flat_app (MAPi (λi X.
    flat_app (MAPi (λj Y.
      if i < j
      then
        (* Xs[i]={j+start} ⇒ Xs[j]={i+start} *)
        cbimply_var bnd (INL (Eq X (&j + start)))
          ([],[(1, Pos (INL (Eq Y (&i + start))))],1)
      else
        Nil) Xs)) Xs)))
End

Definition cencode_symmetric_all_different_def:
  cencode_symmetric_all_different bnd Xs start name ec =
  let
    n = LENGTH Xs;
    (xs,ec') = cencode_eq_grid bnd Xs (GENLIST (λi. start + &i) n) ec
  in
    (Append xs
      (cencode_symmetric_all_different_aux bnd Xs start name), ec')
End

Definition encode_symmetric_all_different_def:
  encode_symmetric_all_different bnd Xs start name =
  let
    n = LENGTH Xs;
  in
    encode_eq_grid bnd Xs (GENLIST (λi. start + &i) n) ++
      (abstr (cencode_symmetric_all_different_aux bnd Xs start name))
End

Theorem symmetric_all_different_sem_alt:
  symmetric_all_different_sem (Xs,start) w ⇔
  let n = LENGTH Xs in
    ALL_DISTINCT (MAP (varc w) Xs) ∧
    EVERY (λX. start ≤ varc w X ∧ varc w X < start + &n) Xs ∧
    (∀i j. i < n ∧ j < n ⇒
      (varc w (EL i Xs) = &j + start
      ⇔
      varc w (EL j Xs) = &i + start))
Proof
  rw[symmetric_all_different_sem_def]>>eq_tac>>
  rw[]
  >- (
    rw[EL_ALL_DISTINCT_EL_EQ]>>
    eq_tac>>rw[]>>
    gvs[EL_MAP]>>
    first_assum(qspec_then `n1` mp_tac)>>
    first_x_assum(qspec_then `n2` mp_tac)>>
    simp[])
  >- (
    first_assum(qspec_then `i` mp_tac)>>
    first_x_assum(qspec_then `j` mp_tac)>>
    rw[]>>eq_tac>>rw[]>>gvs[]>>
    `∀n.Num (&n + start − start) = n` by intLib.ARITH_TAC>>
    gvs[])
  >- (
    gvs[EVERY_EL]>>last_x_assum drule>>rw[]>>
    first_x_assum(qspecl_then[`i`,`Num (varc w Xs❲i❳ − start)`] mp_tac)>>
    simp[]>>
    intLib.ARITH_TAC)
QED

Theorem encode_symmetric_all_different_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting (SymmetricAllDifferent (Xs,start))) ∧
  symmetric_all_different_sem (Xs,start) wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_symmetric_all_different bnd Xs start name)
Proof
  rw[encode_symmetric_all_different_def,cencode_symmetric_all_different_def,
    symmetric_all_different_sem_alt]>>
  simp[reify_avar_def,reify_flag_def,reify_reif_def]>>
  simp[cencode_symmetric_all_different_aux_def]>>rw[]
  >- (
    (* all different *)
    simp[GSYM encode_all_different_alt]>>
    irule encode_all_different_sem_1>>
    simp[all_different_except_sem_def])
  >- (
    (* range *)
    fs[cmk_bounds_all_sem,EVERY_MEM]>>
    rw[]>>first_x_assum drule>>
    rpt (pop_assum kall_tac)>>
    intLib.ARITH_TAC)>>
  (* involution *)
  simp[EVERY_FLAT,Once EVERY_MEM]>>
  simp[MEM_FLAT,MEM_MAPi,PULL_EXISTS,EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi]>>rw[]>>rw[]>>
  simp[iconstraint_sem_def,reify_avar_def,reify_reif_def,oneline b2i_def]>>
  rw[]
QED

Theorem encode_symmetric_all_different_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_symmetric_all_different bnd Xs start name) ⇒
  symmetric_all_different_sem (Xs,start) wi
Proof
  rw[symmetric_all_different_sem_alt,encode_symmetric_all_different_def,
    cencode_symmetric_all_different_aux_def]
  >- (
    gvs[GSYM (encode_all_different_alt)]>>
    drule_all encode_all_different_sem_2>>
    simp[all_different_except_sem_def])
  >- (
    (* range *)
    fs[cmk_bounds_all_sem,EVERY_MEM]>>
    rw[]>>first_x_assum drule>>
    rpt (pop_assum kall_tac)>>
    intLib.ARITH_TAC)>>
  (* involution *)
  qpat_x_assum`EVERY _ (FLAT _)` mp_tac>>
  simp[EVERY_FLAT,Once EVERY_MEM]>>
  simp[MEM_FLAT,MEM_MAPi,PULL_EXISTS,EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,PULL_FORALL]>>
  Cases_on`i=j`>>simp[]>>
  wlog_tac `i < j` [`i`,`j`]
  >- (
    `j < i` by fs[]>>
    first_x_assum drule>>simp[])>>
  disch_then (qspecl_then[`i`,`j`] mp_tac)>>
  simp[iconstraint_sem_def,reify_avar_def,reify_reif_def,oneline b2i_def]>>
  gvs[MEM_GENLIST,PULL_EXISTS,MEM_EL]>>
  first_assum (qspecl_then [`i`,`j`] mp_tac)>>
  first_x_assum (qspecl_then [`j`,`i`] mp_tac)>>
  rw[]>>
  metis_tac[integerTheory.INT_ADD_COMM]
QED

Theorem cencode_symmetric_all_different_sem:
  valid_assignment bnd wi ∧
  cencode_symmetric_all_different bnd Xs iS name ec = (es, ec') ⇒
  enc_rel wi es (encode_symmetric_all_different bnd Xs iS name) ec ec'
Proof
  rw[cencode_symmetric_all_different_def,encode_symmetric_all_different_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_encode_eq_grid>>simp[]
QED

Definition elm_def[simp]:
  elm name (v:int) =
  INR (name, Values [v] NONE)
End

(* encodes fnvalue_v ⇔ some X = v *)
Definition cencode_some_eq_def:
  cencode_some_eq bnd Xs v name =
  cbimply_var bnd (elm name v) (at_least_one $ MAP (λX. Pos (INL (Eq X v))) Xs)
End

Definition encode_some_eq_def:
  encode_some_eq bnd Xs v name =
  abstr $ cencode_some_eq bnd Xs v name
End

Theorem iSUM_ge_0:
  (∀x. MEM x ls ⇒ x ≥ 0) ⇒
  iSUM ls ≥ 0
Proof
  Induct_on`ls`>> rw[iSUM_def]>>
  fs[SF DNF_ss]>>
  intLib.ARITH_TAC
QED

Theorem b2i_alt:
  b2i b = if b then 1 else 0
Proof
  rw[]
QED

Theorem eval_lin_term_ge_1:
  eval_lin_term wb (MAP (λe. (1, f e)) ls) ≥ 1 ⇔
  ∃e. MEM e ls ∧ lit wb (f e)
Proof
  rw[eval_lin_term_def]>>
  Induct_on ‘ls’>>
  rw[iSUM_def,b2i_alt]
  >-(
    simp[SF DNF_ss]>>
    qmatch_goalsub_abbrev_tac`_ + iSUM lss ≥ _`>>
    `iSUM lss ≥ 0` by (
      irule iSUM_ge_0>>
      simp[Abbr`lss`,MEM_MAP,PULL_EXISTS,b2i_alt]>>
      rw[])>>
    intLib.ARITH_TAC)
  >- metis_tac[]
QED

Theorem encode_some_eq_sem:
  valid_assignment bnd wi ∧
  EVERY (λX. wb (INL (Eq X v)) ⇔ varc wi X = v) Xs ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (encode_some_eq bnd Xs v name) =
  (wb (elm name v) ⇔ ∃X. MEM X Xs ∧ wb (INL (Eq X v))))
Proof
  rw[cencode_some_eq_def,encode_some_eq_def,MEM_MAP,
    iconstraint_sem_def,eval_lin_term_ge_1,PULL_EXISTS]>>
  metis_tac[]
QED

Definition encode_n_value_def:
  encode_n_value bnd Xs Y name =
  let
    vals = union_dom bnd Xs
  in
    encode_eq_grid bnd Xs vals ++
    FLAT (MAP (λv. encode_some_eq bnd Xs v name) vals) ++
    encode_bitsum (MAP (elm name) vals) Y
End

Theorem encode_n_value_aux:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (encode_n_value bnd Xs Y name) ⇔
    (∀v. MEM v (union_dom bnd Xs) ⇒ (
      EVERY (λX. wb (INL (Ge X v)) ⇔ varc wi X ≥ v) Xs ∧
      EVERY (λX. wb (INL (Ge X (v + 1))) ⇔ varc wi X ≥ v + 1) Xs ∧
      EVERY (λX. wb (INL (Eq X v)) ⇔ varc wi X = v) Xs ∧
      (wb (INR (name,Values [v] NONE)) ⇔ MEM v (MAP (varc wi) Xs)))) ∧
    &LENGTH (FILTER (λx. wb (INR (name,Values [x] NONE))) (union_dom bnd Xs)) =
      varc wi Y)
Proof
  strip_tac>>
  simp[encode_n_value_def]>>
  irule LEFT_AND_CONG>>rw[]
  >- (
    simp[IMP_CONJ_THM, SF DNF_ss]>>
    simp[CONJ_ASSOC]>>
    irule LEFT_AND_CONG>>rw[]
    >- (
      simp[EVERY_MEM]>>metis_tac[])>>
    simp[EVERY_FLAT,Once EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
    drule encode_some_eq_sem>>
    fs[EVERY_MEM]>>
    metis_tac[])
  >- (
    drule_then (fn thm => simp[thm]) encode_bitsum_sem>>
    simp[MAP_MAP_o]>>
    simp[iSUM_FILTER,o_DEF,encode_some_eq_sem,MEM_MAP,EVERY_MEM])
QED

Theorem encode_n_value_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting (NValue Xs Y)) ∧
  n_value_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_n_value bnd Xs Y name)
Proof
  strip_tac>>
  gs[encode_n_value_aux,n_value_sem_def]>>
  CONJ_TAC>>
  simp[reify_avar_def,reify_reif_def,reify_flag_def]>>
  DEP_REWRITE_TAC[GSYM ALL_DISTINCT_CARD_LIST_TO_SET]>>
  CONJ_TAC
  >-(
    irule FILTER_ALL_DISTINCT>>
    simp[ALL_DISTINCT_union_dom])>>
  qmatch_asmsub_abbrev_tac ‘Num _ = c1’>>
  qmatch_goalsub_abbrev_tac ‘&c2 = _’>>
  ‘c1 = c2’ suffices_by intLib.ARITH_TAC>>
  gs[Abbr‘c1’,Abbr‘c2’]>>
  cong_tac (SOME 1)>>
  simp[SET_EQ_SUBSET,SUBSET_DEF,MEM_FILTER]>>
  drule_then mp_tac EVERY_MEM_union_dom>>
  simp[EVERY_MEM,MEM_MAP,SF DNF_ss]
QED

Theorem encode_n_value_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_n_value bnd Xs Y name) ⇒
  n_value_sem Xs Y wi
Proof
  simp[satTheory.AND_IMP]>>
  strip_tac>>
  simp[encode_n_value_aux,n_value_sem_def]>>
  strip_tac>>
  pop_assum (fn thm => simp[GSYM thm])>>
  CONJ_TAC
  >-intLib.ARITH_TAC>>
  DEP_REWRITE_TAC[GSYM ALL_DISTINCT_CARD_LIST_TO_SET]>>
  CONJ_TAC
  >-(
    irule FILTER_ALL_DISTINCT>>
    simp[ALL_DISTINCT_union_dom])>>
  cong_tac (SOME 1)>>
  gs[SET_EQ_SUBSET,SUBSET_DEF,MEM_FILTER,MEM_MAP]>>
  CONJ_TAC>>
  ntac 2 strip_tac
  >-metis_tac[]>>
  match_mp_tac $ METIS_PROVE[] “(Q ∧ (Q ⇒ P)) ⇒ P ∧ Q”>>
  CONJ_TAC
  >-(
    drule_then mp_tac EVERY_MEM_union_dom>>
    simp[EVERY_MEM])>>
  metis_tac[]
QED

Definition cencode_n_value_def:
  cencode_n_value bnd Xs Y name ec =
  let
    vals = union_dom bnd Xs;
    (xs,ec') = cencode_eq_grid bnd Xs vals ec
  in
    (Append
      (Append xs
        (flat_app $ MAP (λv.
          cencode_some_eq bnd Xs v name) vals))
      (cencode_bitsum (MAP (elm name) vals) Y name), ec')
End

Theorem cencode_n_value_sem:
  valid_assignment bnd wi ∧
  cencode_n_value bnd Xs Y name ec = (es, ec') ⇒
  enc_rel wi es (encode_n_value bnd Xs Y name) ec ec'
Proof
  rw[cencode_n_value_def,encode_n_value_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]>>
  irule enc_rel_Append>>
  qmatch_asmsub_abbrev_tac ‘(xs,_)’>>
  qexists ‘ec'’>>
  CONJ_TAC
  >-(
    irule enc_rel_Append>>
    qexists ‘ec'’>>
    simp[enc_rel_encode_eq_grid]>>
    irule enc_rel_abstr_cong>>
    simp[abstr_flat_app,encode_some_eq_def,MAP_MAP_o,o_DEF])>>
  simp[cencode_bitsum_def]
QED

Definition eqi_def[simp]:
  eqi name (i:num) ann =
    INR (name, Indices [i] (SOME ann))
End

Definition cencode_count_aux_def:
  cencode_count_aux bnd Xs Y name =
  flat_app
    (MAPi
      (λi X.
        let
          ge = eqi name i («ge»);
          le = eqi name i («le»);
          eq = eqi name i («eq»)
        in
          Append (cbimply_var bnd (ge) (mk_ge X Y))
            (Append (cbimply_var bnd (le) (mk_le X Y))
              (cbimply_var bnd (eq) ([],[(1i,Pos ge);(1i,Pos le)],2i)))
      ) Xs
    )
End

Definition split_varc_in_list_def:
  split_varc_in_list Xs =
  let (Xsc,Xsv) = PARTITION ISR Xs in
    (REVERSE Xsv, MAP OUTR Xsc)
End

(* In Xs Y : Y is a member of Xs.
  Split into cases where Xs is Var or Const *)
Definition cencode_in_def:
  cencode_in bnd (Xs:mlstring varc list) Y name ec =
  let (Xsv,Xsc) = split_varc_in_list Xs in
  let (cs_enc,ec') = cencode_eq_grid bnd [Y] Xsc ec in
  let var_lits =
    GENLIST (λi. Pos $ eqi name i («eq»)) (LENGTH Xsv) in
  let con_lits =
    MAP (λc. Pos (INL (Eq Y c))) Xsc in
  (Append cs_enc
    (Append (cencode_count_aux bnd Xsv Y name)
            (cat_least_one name (var_lits ++ con_lits))), ec')
End

Definition encode_in_def:
  encode_in bnd (Xs:mlstring varc list) Y name =
  let (Xsv,Xsc) = split_varc_in_list Xs in
  encode_eq_grid bnd [Y] Xsc ++
  abstr (cencode_count_aux bnd Xsv Y name) ++
  [at_least_one
    (GENLIST (λi. Pos $ eqi name i («eq»)) (LENGTH Xsv) ++
     MAP (λc. Pos (INL (Eq Y c))) Xsc)]
End

Definition cencode_count_def:
  cencode_count bnd Xs Y Z name =
  Append
    (cencode_count_aux bnd Xs Y name)
    (cencode_bitsum (GENLIST (λi. eqi name i («eq»)) (LENGTH Xs)) Z name)
End

Definition encode_count_def:
  encode_count bnd Xs Y Z name = abstr $ cencode_count bnd Xs Y Z name
End

Definition cencode_at_most_one_def:
  cencode_at_most_one bnd Xs Y name =
  Append
    (cencode_count_aux bnd Xs Y name)
    (cat_most_one name (GENLIST (λi. Pos $ eqi name i («eq»)) (LENGTH Xs)))
End

Definition encode_at_most_one_def:
  encode_at_most_one bnd Xs Y name = abstr $ cencode_at_most_one bnd Xs Y name
End

Theorem encode_count_aux_sem_1:
  valid_assignment bnd wi ∧
  (ALOOKUP cs name = SOME (Counting (Count Xs Y Z)) ∨
  ALOOKUP cs name = SOME (Counting (In Xs' Y)) ∧ Xs = FILTER ISL Xs' ∨
  ALOOKUP cs name = SOME (Counting (AtMostOne Xs Y)))
  ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (abstr $ cencode_count_aux bnd Xs Y name)
Proof
  rw[cencode_count_aux_def]>>
  rw[EVERY_FLAT,Once EVERY_MEM,MEM_MAPi,EVERY_APPEND]>>
  simp[iconstraint_sem_def,reify_avar_def,
    reify_flag_def,reify_flag_counting_def]>>
  intLib.ARITH_TAC
QED

Theorem PART_FILTER:
  ∀Xs ls rs xs ys.
  PART P Xs ls rs = (xs,ys) ⇒
  xs = REVERSE (FILTER P Xs) ++ ls ∧
  ys = REVERSE (FILTER ($~ o P) Xs) ++ rs
Proof
  Induct>>rw[PART_DEF]>>
  first_x_assum drule>>rw[]
QED

Theorem PARTITION_FILTER:
  PARTITION P Xs = (xs,ys) ⇒
  xs = REVERSE (FILTER P Xs) ∧
  ys = REVERSE (FILTER ($~ o P) Xs)
Proof
  rw[PARTITION_DEF]>>
  drule PART_FILTER>>rw[]
QED

Theorem split_varc_in_list_eq:
  split_varc_in_list Xs = (Xsv,Xsc) ⇒
  Xsv = FILTER ISL Xs ∧
  Xsc = REVERSE (MAP OUTR (FILTER ISR Xs))
Proof
  rw[split_varc_in_list_def]>>
  pairarg_tac>>gvs[]>>
  drule PARTITION_FILTER>>rw[]>>
  simp[FILTER_EQ,MAP_REVERSE]
QED

Theorem encode_in_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting (In Xs Y)) ∧
  in_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_in bnd Xs Y name)
Proof
  rw[encode_in_def,in_sem_def]>>
  pairarg_tac>>rw[]>>
  simp[reify_avar_def,reify_reif_def]
  >- (
    irule encode_count_aux_sem_1>>
    gvs[]>>
    metis_tac[split_varc_in_list_eq])>>
  gvs[MEM_MAP,MEM_GENLIST,PULL_EXISTS,reify_avar_def,
    reify_flag_def,reify_flag_counting_def,MEM_FLAT,AllCaseEqs(),
    SF DNF_ss,reify_reif_def]>>
  drule split_varc_in_list_eq>>rw[]>>
  Cases_on`y`>>gvs[]
  >- (
    `MEM (INL x) (FILTER ISL Xs)` by fs[MEM_FILTER]>>
    DISJ1_TAC>>gvs[MEM_EL]>>
    first_x_assum $ irule_at Any>>
    gvs[])>>
  simp[varc_def,MEM_MAP,MEM_FILTER]>>
  metis_tac[ISR,OUTR]
QED

Theorem encode_count_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting (Count Xs Y Z)) ∧
  count_sem Xs Y Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_count bnd Xs Y Z name)
Proof
  rw[cencode_count_def,encode_count_def,count_sem_def]
  >-
    metis_tac[encode_count_aux_sem_1]>>
  drule_then (fn thm => simp[thm]) encode_bitsum_sem>>
  cong_tac NONE>>
  simp[MAP_GENLIST,o_ABS_R,reify_avar_def,
    reify_flag_def,reify_flag_counting_def,GENLIST_EL_MAP]
QED

Theorem encode_at_most_one_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting (AtMostOne Xs Y)) ∧
  at_most_one_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_at_most_one bnd Xs Y name)
Proof
  rw[cencode_at_most_one_def,encode_at_most_one_def,at_most_one_sem_def]
  >-
    metis_tac[encode_count_aux_sem_1]>>
  simp[MAP_GENLIST,o_ABS_R,reify_avar_def,
    reify_flag_def,reify_flag_counting_def,GENLIST_EL_MAP]
QED

Theorem encode_count_aux_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr $ cencode_count_aux bnd Xs Y name) ∧
  i < LENGTH Xs ⇒
  (wb (INR (name,Indices [i] (SOME «eq»))) ⇔ varc wi Xs❲i❳ = varc wi Y)
Proof
  rw[cencode_count_aux_def, EVERY_FLAT]>>
  gs[Once EVERY_MEM,MEM_MAPi,SF DNF_ss,iconstraint_sem_def]>>
  last_x_assum kall_tac>>
  last_x_assum $ drule_then (fn thm => assume_tac $ GSYM thm)>>
  last_x_assum $ drule_then (fn thm => assume_tac $ GSYM thm)>>
  last_x_assum $ drule_then (fn thm => assume_tac $ GSYM thm)>>
  pop_assum SUBST_ALL_TAC>>
  pop_assum SUBST_ALL_TAC>>
  pop_assum SUBST_ALL_TAC>>
  intLib.ARITH_TAC
QED

Theorem encode_in_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_in bnd Xs Y name) ⇒
  in_sem Xs Y wi
Proof
  rw[encode_in_def]>>
  pairarg_tac>>
  gs[EVERY_FLAT,MEM_GENLIST,in_sem_def]>>
  drule split_varc_in_list_eq>>rw[]
  >- (
    drule_all encode_count_aux_sem_2>>
    rw[MEM_MAP]>>
    metis_tac[MEM_EL,MEM_FILTER])
  >- (
    gvs[MEM_FLAT,MEM_MAP,AllCaseEqs(),Once EVERY_MEM,SF DNF_ss,MEM_FILTER]>>
    first_x_assum $ irule_at Any>>
    Cases_on`y`>>gvs[varc_def])
QED

Theorem encode_count_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_count bnd Xs Y Z name) ⇒
  count_sem Xs Y Z wi
Proof
  rw[cencode_count_def,encode_count_def]>>
  drule_then (fn thm => gs[thm]) encode_bitsum_sem>>
  gs[MAP_GENLIST,o_ABS_R,count_sem_def]>>
  pop_assum (SUBST_ALL_TAC o SYM)>>
  cong_tac NONE>>
  rw[GENLIST_eq_MAP]>>
  cong_tac NONE>>
  metis_tac[encode_count_aux_sem_2]
QED

Theorem encode_at_most_one_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_at_most_one bnd Xs Y name) ⇒
  at_most_one_sem Xs Y wi
Proof
  rw[cencode_at_most_one_def,encode_at_most_one_def,EVERY_FLAT]>>
  gs[MEM_GENLIST,at_most_one_sem_def]>>
  pop_assum mp_tac>>
  match_mp_tac EQ_IMPLIES>>
  cong_tac NONE>>
  rw[MAP_GENLIST,GENLIST_eq_MAP]>>
  drule_all encode_count_aux_sem_2>>
  rw[]
QED

Theorem cencode_in_sem:
  valid_assignment bnd wi ∧
  cencode_in bnd Xs Y name ec = (es, ec') ⇒
  enc_rel wi es (encode_in bnd Xs Y name) ec ec'
Proof
  rw[cencode_in_def,encode_in_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]>>
  PURE_ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_encode_eq_grid>>simp[]>>
  irule enc_rel_abstr_cong>>
  simp[]
QED

(* Among: Y equals the number of times values from iS appear in Xs.
  NOTE: nub might need to be optimized here. *)
Definition cencode_among_aux_def:
  cencode_among_aux bnd Xs iS Y name =
    cencode_bitsum
      (FLAT (MAP (λX. MAP (λv. INL (Eq X v)) (nub iS)) Xs))
      Y name
End

Definition encode_among_def:
  encode_among bnd Xs iS Y name =
  encode_eq_grid bnd Xs iS ++
  abstr (cencode_among_aux bnd Xs iS Y name)
End

Theorem iSUM_ALL_DISTINCT_MEM:
  ∀ls.
  ALL_DISTINCT ls ∧
  (∀x. MEM x ls ⇒ (f x ⇔ y = x)) ⇒
  iSUM (MAP (λx. b2i (f x)) ls) =
  b2i (MEM y ls)
Proof
  Induct>>rw[iSUM_def]>>
  Cases_on`f h`>>gvs[]
QED

Theorem encode_among_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting (Among Xs iS Y)) ∧
  among_sem Xs iS Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_among bnd Xs iS Y name)
Proof
  rw[cencode_among_aux_def,encode_among_def,among_sem_def]>>
  simp[reify_avar_def,reify_reif_def]>>
  drule_then (fn thm => simp[thm]) encode_bitsum_sem>>
  simp[MAP_FLAT,pbc_encodeTheory.iSUM_FLAT,MAP_MAP_o,o_DEF]>>
  rw[reify_avar_def,reify_reif_def]>>
  cong_tac NONE>>
  PURE_REWRITE_TAC[Once (GSYM MEM_nub)]>>
  ho_match_mp_tac iSUM_ALL_DISTINCT_MEM>>
  simp[]
QED

Theorem encode_among_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_among bnd Xs iS Y name) ⇒
  among_sem Xs iS Y wi
Proof
  rw[cencode_among_aux_def,encode_among_def,EVERY_FLAT,among_sem_def]>>
  drule_then (fn thm => gs[thm]) encode_bitsum_sem>>
  pop_assum (SUBST_ALL_TAC o SYM)>>
  simp[MAP_FLAT,pbc_encodeTheory.iSUM_FLAT,MAP_MAP_o,o_DEF]>>
  cong_tac NONE>>
  PURE_REWRITE_TAC[Once (GSYM MEM_nub)]>>
  ho_match_mp_tac iSUM_ALL_DISTINCT_MEM>>
  rw[]
QED

Definition cencode_among_def:
  cencode_among bnd Xs iS Y name ec =
  let (xs,ec') = cencode_eq_grid bnd Xs iS ec in
  (Append xs (cencode_among_aux bnd Xs iS Y name), ec')
End

Theorem cencode_among_sem:
  valid_assignment bnd wi ∧
  cencode_among bnd Xs iS Y name ec = (es, ec') ⇒
  enc_rel wi es (encode_among bnd Xs iS Y name) ec ec'
Proof
  rw[cencode_among_def,encode_among_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_abstr>>
  simp[enc_rel_encode_eq_grid]
QED

(* AllEqual: linear chain x1=x2, x2=x3, ... *)
Definition equal_chain_def:
  (equal_chain i name X [] = []) ∧
  (equal_chain i name X (Y::Ys) =
    (SOME (mk_name name (toString i ^ «ge»)), mk_ge X Y)::
    (SOME (mk_name name (toString i ^ «le»)), mk_le X Y)::
    equal_chain (i+1) name Y Ys)
End

Definition cencode_all_equal_def:
  cencode_all_equal Xs name =
  case Xs of [] => Nil
  | (X::Xs) =>
    List (equal_chain 0 name X Xs)
End

Definition encode_all_equal_def:
  encode_all_equal Xs name =
  abstr $ cencode_all_equal Xs name
End

Theorem equal_chain_sem:
  ∀Xs i name X.
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstrl (equal_chain i name X Xs)) ⇔
  EVERY (λY. varc wi X = varc wi Y) Xs
Proof
  Induct>>rw[equal_chain_def]>>
  simp[Once CONJ_ASSOC]>>
  irule boolTheory.LEFT_AND_CONG>>rw[]>>
  intLib.ARITH_TAC
QED

Theorem encode_all_equal_sem_1:
  all_equal_sem Xs wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_all_equal Xs name)
Proof
  strip_tac>>
  gs[encode_all_equal_def,cencode_all_equal_def,all_equal_sem_def]>>
  Cases_on`Xs`>>
  rw[]>>fs[equal_chain_sem]>>
  simp[Once EQ_SYM_EQ]
QED

Theorem encode_all_equal_sem_2:
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_all_equal Xs name) ⇒
  all_equal_sem Xs wi
Proof
  gs[encode_all_equal_def,cencode_all_equal_def,all_equal_sem_def]>>
  Cases_on`Xs`>>
  rw[]>>fs[equal_chain_sem]>>
  simp[Once EQ_SYM_EQ]
QED

Definition encode_counting_constr_def:
  encode_counting_constr bnd c name =
  case c of
    AllEqual Xs => encode_all_equal Xs name
  | AllDifferentExcept Xs iS => encode_all_different_except bnd Xs iS name
  | SymmetricAllDifferent (Xs,start) => encode_symmetric_all_different bnd Xs start name
  | NValue Xs Y => encode_n_value bnd Xs Y name
  | In Xs Y => encode_in bnd Xs Y name
  | Count Xs Y Z => encode_count bnd Xs Y Z name
  | Among Xs iS Y => encode_among bnd Xs iS Y name
  | AtMostOne Xs Y => encode_at_most_one bnd Xs Y name
End

Theorem encode_counting_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting c) ∧
  counting_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_counting_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_counting_constr_def,counting_constr_sem_def]
  >- metis_tac[encode_all_equal_sem_1]
  >- metis_tac[encode_all_different_except_sem_1]
  >- (Cases_on`p`>>fs[]>>metis_tac[encode_symmetric_all_different_sem_1])
  >- metis_tac[encode_n_value_sem_1]
  >- metis_tac[encode_count_sem_1]
  >- metis_tac[encode_among_sem_1]
  >- metis_tac[encode_in_sem_1]
  >- metis_tac[encode_at_most_one_sem_1]
QED

Theorem encode_counting_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_counting_constr bnd c name) ⇒
  counting_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_counting_constr_def,counting_constr_sem_def]
  >- metis_tac[encode_all_equal_sem_2]
  >- metis_tac[encode_all_different_except_sem_2]
  >- (Cases_on`p`>>fs[]>>metis_tac[encode_symmetric_all_different_sem_2])
  >- metis_tac[encode_n_value_sem_2]
  >- metis_tac[encode_count_sem_2]
  >- metis_tac[encode_among_sem_2]
  >- metis_tac[encode_in_sem_2]
  >- metis_tac[encode_at_most_one_sem_2]
QED

Definition cencode_counting_constr_def:
  cencode_counting_constr bnd c name ec =
  case c of
    AllEqual Xs => (cencode_all_equal Xs name, ec)
  | AllDifferentExcept Xs iS => cencode_all_different_except bnd Xs iS name ec
  | SymmetricAllDifferent (Xs,start) => cencode_symmetric_all_different bnd Xs start name ec
  | NValue Xs Y => cencode_n_value bnd Xs Y name ec
  | Count Xs Y Z => (cencode_count bnd Xs Y Z name, ec)
  | Among Xs iS Y => cencode_among bnd Xs iS Y name ec
  | In Xs Y => cencode_in bnd Xs Y name ec
  | AtMostOne Xs Y => (cencode_at_most_one bnd Xs Y name, ec)
End

Theorem cencode_counting_constr_sem:
  valid_assignment bnd wi ∧
  cencode_counting_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_counting_constr bnd c name) ec ec'
Proof
  Cases_on ‘c’>>
  simp[cencode_counting_constr_def,encode_counting_constr_def]
  >- simp[cencode_all_equal_def,encode_all_equal_def]
  >- simp[cencode_all_different_except_sem]
  >- (Cases_on`p`>>simp[cencode_symmetric_all_different_sem])
  >- simp[cencode_n_value_sem]
  >- simp[cencode_count_def,encode_count_def]
  >- simp[cencode_among_sem]
  >- simp[cencode_in_sem]
  >- simp[cencode_at_most_one_def,encode_at_most_one_def]
QED
