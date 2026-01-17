(*
  Formalization of the CP to ILP phase (counting constraints)
*)
Theory cp_to_ilp_counting
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

Definition neiv_def[simp]:
  neiv name (i:num) j =
    INR (name, Indices [i;j] NONE)
End

(* AllDifferent: All variables must take distinct values
   For n variables, this requires O(n^2) pairwise inequality constraints *)
Definition cencode_all_different_def:
  cencode_all_different bnd Xs name =
  flat_app (MAPi (λi X.
    flat_app (MAPi (λj Y.
      if i < j then
        List [
          (SOME $ mk_name name (strlit"gt"),
            bits_imply bnd [Pos (neiv name i j)] (mk_gt X Y));
          (SOME $ mk_name name (strlit"lt"),
            bits_imply bnd [Neg (neiv name i j)] (mk_gt Y X))
        ]
      else Nil) Xs)) Xs)
End

Definition encode_all_different_def:
  encode_all_different bnd Xs name = abstr $ cencode_all_different bnd Xs name
End

Theorem encode_all_different_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting (AllDifferent Xs)) ∧
  all_different_sem Xs wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_all_different bnd Xs name)
Proof
  rw[encode_all_different_def,cencode_all_different_def,all_different_sem_def,EVERY_MEM]>>
  gvs[MEM_FLAT,MEM_MAPi]>>
  rename1 ‘if i < j then _ else _’>>
  Cases_on ‘i < j’>>
  gs[reify_avar_def,reify_flag_def]
  >- intLib.ARITH_TAC>>
  rw[]>>
  fs[EL_ALL_DISTINCT_EL_EQ,EL_MAP]>>
  first_x_assum $ qspecl_then [‘i’,‘j’] assume_tac>>
  intLib.ARITH_TAC
QED

Theorem all_different_sem_aux:
  (∀i j. i < j ∧ j < LENGTH Xs ⇒
    let X = EL i Xs in
    let Y = EL j Xs in
    if wb (neiv (name:mlstring) i j)
    then varc wi X > varc wi Y
    else varc wi Y > varc wi X) ⇒
  all_different_sem Xs wi
Proof
  rw[all_different_sem_def,EL_ALL_DISTINCT_EL_EQ]>>
  Cases_on`n1 = n2`>>simp[]>>
  wlog_tac `n1 < n2` [`n1`,`n2`]
  >- (
    `n2 < n1` by fs[]>>
    first_x_assum drule_all>>
    simp[])>>
  first_x_assum drule>>
  rw[EL_MAP]>>
  intLib.ARITH_TAC
QED

Theorem encode_all_different_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_all_different bnd Xs name) ⇒
  all_different_sem Xs wi
Proof
  strip_tac>>
  irule all_different_sem_aux>>
  gs[EVERY_MEM,encode_all_different_def,cencode_all_different_def,
    MEM_FLAT,MEM_MAPi,PULL_EXISTS]>>
  qexistsl [‘name’,‘wb’]>>
  rpt strip_tac>>
  rename1 ‘[i;j]’>>
  ‘i < LENGTH Xs’ by fs[]>>
  first_x_assum $ drule_then rev_drule>>
  simp[SF DNF_ss]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Definition elm_def[simp]:
  elm name (v:int) =
  INR (name, Values [v] NONE)
End

(* encodes fnvalue_v ⇔ some X = v *)
Definition encode_some_eq_def:
  encode_some_eq bnd Xs (v: int) name =
    bimply_bits bnd [Pos (elm name v)]
      ([], MAP (λX. (1i, Pos (INL (Eq X v)))) Xs, 1i)
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
  rw[encode_some_eq_def,iconstraint_sem_def,eval_lin_term_ge_1]>>
  metis_tac[]
QED

Definition reify_some_eq_def:
  reify_some_eq bnd Xs v name =
    (FLAT $ MAP (λX. encode_full_eq bnd X v) Xs) ++ encode_some_eq bnd Xs v name
End

Theorem FORALL_IMP_EQ[local] = METIS_PROVE []
  ``(∀x. P x ⇒ (Q x ⇔ R x)) ⇒ ((∀x. P x ⇒ Q x) ⇔ (∀x. P x ⇒ R x))``;

Theorem reify_some_eq_sem:
  valid_assignment bnd wi ⇒ (
  EVERY (λx. iconstraint_sem x (wi,wb)) (FLAT (MAP (λv. reify_some_eq bnd Xs v name)
    (union_dom bnd Xs))) ⇔
  ∀v. MEM v (union_dom bnd Xs) ⇒
      EVERY (λX. wb (INL (Ge X v)) ⇔ varc wi X ≥ v) Xs ∧
      EVERY (λX. wb (INL (Ge X (v + 1))) ⇔ varc wi X ≥ v + 1) Xs ∧
      EVERY (λX. wb (INL (Eq X v)) ⇔ varc wi X = v) Xs ∧
      (wb (elm name v) ⇔ ∃X. MEM X Xs ∧ wb (INL (Eq X v))))
Proof
  rw[reify_some_eq_def,EVERY_FLAT,EVERY_MAP]>>
  simp[Once EVERY_MEM,Once $ GSYM CONJ_ASSOC]>>
  ho_match_mp_tac FORALL_IMP_EQ>>
  rw[EVERY_CONJ,GSYM CONJ_ASSOC]>>
  match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC
  >- (irule EVERY_CONG>>simp[encode_ge_sem])>>
  strip_tac>>
  match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC
  >- (irule EVERY_CONG>>simp[encode_ge_sem])>>
  strip_tac>>
  match_mp_tac LEFT_AND_CONG>>
  CONJ_TAC
  >- (
    irule EVERY_CONG>>
    rw[]>>
    irule encode_eq_sem>>
    fs[EVERY_MEM])>>
  simp[encode_some_eq_sem]
QED

Theorem encode_n_value_sem_aux:
  valid_assignment bnd wi ∧
  (∀v. MEM v (union_dom bnd Xs) ⇒
    EVERY (λX. wb (INL (Eq X v)) ⇔ varc wi X = v) Xs ∧
    (wb (elm name v) ⇔ ∃X. MEM X Xs ∧ wb (INL (Eq X v)))) ⇒
  ∀v. MEM v (MAP (varc wi) Xs) ⇔ MEM v (FILTER (λv. wb (elm name v)) (union_dom bnd Xs))
Proof
  rw[MEM_FILTER,MEM_MAP]>>
  iff_tac>>
  strip_tac
  >-(
    CONJ_ASM2_TAC
    >- (
      gvs[EVERY_MEM]>>
      metis_tac[])>>
    drule_then assume_tac EVERY_MEM_union_dom>>
    fs[EVERY_MEM])>>
  gvs[EVERY_MEM]>>
  metis_tac[]
QED

Theorem list_set_eq:
  ∀ls1 ls2. (∀v. MEM v ls1 ⇔ MEM v ls2) ⇔ set ls1 = set ls2
Proof
  rw[SET_EQ_SUBSET]>>
  simp[GSYM SUBSET_DIFF_EMPTY,list_to_set_diff,GSYM NULL_EQ,NULL_FILTER]>>
  metis_tac[]
QED

(* NValue: Y equals the number of distinct values in Xs
   This is very complex and requires auxiliary variables *)

Definition encode_n_value_def:
  encode_n_value bnd Xs Y name =
  let
    vals = union_dom bnd Xs
  in
    (FLAT $ MAP (λv. reify_some_eq bnd Xs v name) vals) ++
    encode_bitsum (MAP (elm name) vals) Y
End

Theorem subset_varc_union_dom:
  valid_assignment bnd wi ⇒
  set $ MAP (varc wi) Xs ⊆ set $ union_dom bnd Xs
Proof
  strip_tac>>
  drule EVERY_MEM_union_dom>>
  rw[EVERY_MEM,SUBSET_DEF]>>
  gs[MEM_MAP]
QED

Theorem LENGTH_FILTER_subset:
  set ls1 ⊆ set ls2 ∧ ALL_DISTINCT ls2 ⇒
  LENGTH (FILTER (λv. MEM v ls1) ls2) = CARD (set ls1)
Proof
  rw[SUBSET_DEF]>>
  drule_then (qspec_then ‘(λv. MEM v ls1)’ assume_tac) FILTER_ALL_DISTINCT>>
  drule_then (fn thm => simp[thm]) $ GSYM ALL_DISTINCT_CARD_LIST_TO_SET>>
  irule $ METIS_PROVE[] “s1 = s2 ⇒ CARD s1 = CARD s2”>>
  rw[GSYM list_set_eq,MEM_FILTER]>>
  metis_tac[]
QED

Theorem encode_n_value_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting (NValue Xs Y)) ∧
  n_value_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_n_value bnd Xs Y name)
Proof
  rw[encode_n_value_def,n_value_sem_def]
  >-(
    rw[reify_some_eq_sem,reify_avar_def,reify_reif_def,reify_flag_def,MEM_MAP]>>
    metis_tac[])>>
  DEP_REWRITE_TAC[encode_bitsum_sem]>>
  simp[MAP_MAP_o]>>
  simp[o_DEF,iSUM_FILTER,reify_avar_def,reify_flag_def]>>
  DEP_REWRITE_TAC[subset_varc_union_dom,LENGTH_FILTER_subset]>>
  DEP_REWRITE_TAC[EVERY_MEM_union_dom,LENGTH_FILTER_subset]>>
  simp[]>>
  CONJ_TAC
  >-simp[GSYM ALL_DISTINCT_CARD_LIST_TO_SET,ALL_DISTINCT_union_dom]>>
  intLib.ARITH_TAC
QED

Theorem encode_n_value_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_n_value bnd Xs Y name) ⇒
  n_value_sem Xs Y wi
Proof
  strip_tac>>
  pop_assum mp_tac>>
  simp[encode_n_value_def,reify_some_eq_sem]>>
  DEP_REWRITE_TAC[encode_bitsum_sem]>>
  simp[MAP_MAP_o]>>
  rw[iSUM_FILTER,EVERY_MEM,
    METIS_PROVE[] “(∀x. P x ⇒ (Q x ∧ R x)) ⇔ (∀x. P x ⇒ Q x) ∧ (∀x. P x ⇒ R x)”]>>
  simp[n_value_sem_def]>>
  ‘LENGTH (FILTER (wb o elm name) (union_dom bnd Xs)) =
   CARD (set (MAP (varc wi) Xs))’ suffices_by intLib.ARITH_TAC>>
  DEP_REWRITE_TAC[GSYM ALL_DISTINCT_CARD_LIST_TO_SET]>>
  CONJ_TAC
  >-(
    irule FILTER_ALL_DISTINCT>>
    simp[ALL_DISTINCT_union_dom])>>
  CONG_TAC (SOME 1)>>
  simp[GSYM list_set_eq,MEM_FILTER,MEM_MAP]>>
  strip_tac>>
  iff_tac
  >-metis_tac[]>>
  strip_tac>>
  pure_rewrite_tac[Once $ METIS_PROVE[] “Q ∧ P ⇔ P ∧ (P ⇒ Q)”]>>
  CONJ_TAC
  >-(
    drule_then assume_tac EVERY_MEM_union_dom>>
    gs[EVERY_MEM])>>
  metis_tac[]
QED

Definition eqi_def[simp]:
  eqi name (i:num) ann =
    INR (name, Indices [i] (SOME ann))
End

Definition cencode_count_def:
  cencode_count bnd Xs Y Z name =
  Append
    (flat_app
      (MAPi
        (λi X.
          let
            ge = eqi name i (strlit"ge");
            le = eqi name i (strlit"le");
            eq = eqi name i (strlit"eq")
          in
            Append (cbimply_var bnd (ge) (mk_ge X Y))
              (Append (cbimply_var bnd (le) (mk_le X Y))
                (cbimply_var bnd (eq) ([],[(1i,Pos ge);(1i,Pos le)],2i)))
        ) Xs
      )
    )
    (cencode_bitsum (GENLIST (λi. eqi name i (strlit"eq")) (LENGTH Xs)) Z name)
End

Definition encode_count_def:
  encode_count bnd Xs Y Z name = abstr $ cencode_count bnd Xs Y Z name
End

Theorem encode_count_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting (Count Xs Y Z)) ∧
  count_sem Xs Y Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_count bnd Xs Y Z name)
Proof
  rw[cencode_count_def,encode_count_def,count_sem_def]
  >-(
  rw[EVERY_FLAT,Once EVERY_MEM,MEM_MAPi,EVERY_APPEND]>>
  simp[iconstraint_sem_def,reify_avar_def,reify_flag_def]>>
  intLib.ARITH_TAC
  )>>
  drule_then (fn thm => simp[thm]) encode_bitsum_sem>>
  cong_tac NONE>>
  simp[MAP_GENLIST,o_ABS_R,reify_avar_def,reify_flag_def,GENLIST_EL_MAP]
QED

Theorem encode_count_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_count bnd Xs Y Z name) ⇒
  count_sem Xs Y Z wi
Proof
  rw[cencode_count_def,encode_count_def,EVERY_FLAT]>>
  gs[Once EVERY_MEM,MEM_MAPi,SF DNF_ss,iconstraint_sem_def]>>
  drule_then (fn thm => gs[thm]) encode_bitsum_sem>>
  gs[MAP_GENLIST,o_ABS_R,count_sem_def]>>
  pop_assum (SUBST_ALL_TAC o SYM)>>
  cong_tac NONE>>
  rw[GENLIST_eq_MAP]>>
  cong_tac NONE>>
  last_x_assum kall_tac>>
  last_x_assum $ drule_then (fn thm => assume_tac $ GSYM thm)>>
  last_x_assum $ drule_then (fn thm => assume_tac $ GSYM thm)>>
  last_x_assum $ drule_then (fn thm => assume_tac $ GSYM thm)>>
  pop_assum SUBST_ALL_TAC>>
  pop_assum SUBST_ALL_TAC>>
  pop_assum SUBST_ALL_TAC>>
  intLib.ARITH_TAC
QED

(* Among: Y equals the number of times values from iS appear in Xs
   Y = Sum_i [Xs[i] ∈ iS] *)
Definition cencode_among_aux_def:
  cencode_among_aux bnd Xs iS Y name =
    Append
      (flat_app (MAPi
      (λi X.
      cbimply_var bnd (eqi name i (strlit"al1"))
        (at_least_one (MAP (λv. Pos (INL (Eq X v))) iS))) Xs))
      (cencode_bitsum (GENLIST (λi. eqi name i (strlit"al1")) (LENGTH Xs)) Y name)
End

Definition encode_among_def:
  encode_among bnd Xs iS Y name =
  FLAT (MAP (λX.
    FLAT (MAP (λv. encode_full_eq bnd X v) iS)) Xs) ++
  abstr (cencode_among_aux bnd Xs iS Y name)
End

Theorem encode_among_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Counting (Among Xs iS Y)) ∧
  among_sem Xs iS Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_among bnd Xs iS Y name)
Proof
  rw[cencode_among_aux_def,encode_among_def,among_sem_def]
  >-(
    simp[EVERY_FLAT,Once EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
    rw[Once EVERY_MEM,MEM_MAP]>>
    simp[reify_avar_def,reify_reif_def])
  >- (
    simp[EVERY_FLAT,o_DEF,Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,MEM_MAP]>>
    simp[reify_avar_def,reify_flag_def,reify_reif_def])>>
  drule_then (fn thm => simp[thm]) encode_bitsum_sem>>
  cong_tac NONE>>
  simp[MAP_GENLIST,o_ABS_R,GENLIST_eq_MAP]>>
  rw[reify_avar_def,reify_flag_def]
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
  qpat_x_assum`EVERY _ _` mp_tac>>
  simp[Once EVERY_MEM,MEM_MAPi,SF DNF_ss,iconstraint_sem_def,EVERY_FLAT,EVERY_MAP,MEM_MAP]>>
  qpat_x_assum`EVERY _ _` mp_tac>>
  simp[EVERY_MEM,MEM_MAPi,SF DNF_ss,iconstraint_sem_def,EVERY_FLAT,EVERY_MAP,MEM_MAP]>>
  rw[]>>
  cong_tac NONE>>
  rw[MAP_GENLIST,o_ABS_R,GENLIST_eq_MAP]>>
  cong_tac NONE>>
  gs[EVERY_MEM]>>
  last_x_assum $ drule_then assume_tac>>
  pop_assum (SUBST_ALL_TAC o SYM)>>
  metis_tac[MEM_EL]
QED

(* (encode_full_eq_ilist bnd X iS) extends (encode_full_eq bnd X v) from a single int ‘v’
   to an int list ‘iS’ *)
Definition encode_full_eq_ilist_def:
  encode_full_eq_ilist bnd _ [] = [] ∧
  encode_full_eq_ilist bnd X (i::iS) =
    encode_full_eq bnd X i ++ encode_full_eq_ilist bnd X iS
End

Definition cencode_full_eq_ilist_def:
  cencode_full_eq_ilist bnd X [] ec = (Nil,ec) ∧
  cencode_full_eq_ilist bnd X (i::iS) ec =
  let
    (x1,ec') = cencode_full_eq bnd X i ec;
    (x2,ec'') = cencode_full_eq_ilist bnd X iS ec'
  in
    (Append x1 x2,ec'')
End

Theorem cencode_full_eq_ilist_sem:
  ∀es ec. valid_assignment bnd wi ∧
  cencode_full_eq_ilist bnd X iS ec = (es, ec') ⇒
    enc_rel wi es (encode_full_eq_ilist bnd X iS) ec ec'
Proof
  Induct_on ‘iS’>>
  rw[cencode_full_eq_ilist_def,encode_full_eq_ilist_def]>>
  rpt (pairarg_tac>>fs[])>>
  ntac 2 (last_x_assum mp_tac)>>
  last_x_assum (SUBST_ALL_TAC o SYM)>>
  last_x_assum SUBST_ALL_TAC>>
  rpt strip_tac>>
  irule enc_rel_Append>>
  rename1 ‘cencode_full_eq _ _ _ _ = (_,ec0)’>>
  qexists ‘ec0’>>
  CONJ_TAC
  >-(
    irule enc_rel_encode_full_eq>>
    simp[])>>
  metis_tac[]
QED

Definition cencode_among_def:
  cencode_among bnd Xs iS Y name ec =
  let (xs,ec') =
    fold_cenc (λX ec.
      fold_cenc (λv ec. cencode_full_eq bnd X v ec) iS ec) Xs ec in
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
  irule enc_rel_fold_cenc>>
  first_x_assum $ irule_at Any>>
  rw[]>>
  irule enc_rel_fold_cenc>>
  first_x_assum $ irule_at Any>>
  rw[]>>
  irule enc_rel_encode_full_eq>>
  fs[]
QED

Definition encode_counting_constr_def:
  encode_counting_constr bnd c name =
  case c of
    AllDifferent Xs => encode_all_different bnd Xs name
  | NValue Xs Y => encode_n_value bnd Xs Y name
  | Count Xs Y Z => encode_count bnd Xs Y Z name
  | Among Xs iS Y => encode_among bnd Xs iS Y name
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
  >- metis_tac[encode_all_different_sem_1]
  >- metis_tac[encode_n_value_sem_1]
  >- metis_tac[encode_count_sem_1]
  >- metis_tac[encode_among_sem_1]
QED

Theorem encode_counting_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_counting_constr bnd c name) ⇒
  counting_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_counting_constr_def,counting_constr_sem_def]
  >- metis_tac[encode_all_different_sem_2]
  >- metis_tac[encode_n_value_sem_2]
  >- metis_tac[encode_count_sem_2]
  >- metis_tac[encode_among_sem_2]
QED

(* Concrete encodings - TODO *)
Definition cencode_counting_constr_def:
  cencode_counting_constr bnd c name ec =
  case c of
    AllDifferent Xs => (cencode_all_different bnd Xs name, ec)
  | Count Xs Y Z => (cencode_count bnd Xs Y Z name, ec)
  | Among Xs iS Y => cencode_among bnd Xs iS Y name ec
  | _ => (List [], ec)
End

Theorem cencode_counting_constr_sem:
  valid_assignment bnd wi ∧
  cencode_counting_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_counting_constr bnd c name) ec ec'
Proof
  Cases_on ‘c’>>
  simp[cencode_counting_constr_def,encode_counting_constr_def]
  >-simp[cencode_all_different_def,encode_all_different_def]
  >-cheat
  >-simp[cencode_count_def,encode_count_def]
  >-simp[cencode_among_sem]
QED
