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
      if i < j
      then
        List [
          (SOME $ mk_name name
            (int_to_string #"-" (&i) ^ strlit"gt" ^ int_to_string #"-" (&j)),
            bits_imply bnd [Pos (neiv name i j)] (mk_gt X Y));
          (SOME $ mk_name name
            (int_to_string #"-" (&i) ^ strlit"lt" ^ int_to_string #"-" (&j)),
            bits_imply bnd [Neg (neiv name i j)] (mk_gt Y X))]
      else
        Nil) Xs)) Xs)
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
    FLAT (MAP (λv. FLAT (MAP (λX. encode_full_eq bnd X v) Xs)) vals) ++
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
  ntac 2 (simp[EVERY_FLAT,EVERY_MAP])>>
  simp[GSYM EVERY_CONJ,Once EVERY_MEM]>>
  simp[EVERY_CONJ, Once $ METIS_PROVE[]
    “(P1 ∧ P2 ∧ P3) ∧ P4 ⇔ (P1 ∧ P2 ∧ P3) ∧ (P3 ⇒ P4)”]>>
  drule_then (fn thm => simp[thm]) encode_bitsum_sem>>
  simp[MAP_MAP_o]>>
  simp[iSUM_FILTER,o_DEF,encode_some_eq_sem,MEM_MAP,EVERY_MEM]>>
  metis_tac[]
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
    (xs,ec') =
      fold_cenc (λv ec.
        fold_cenc (λX ec. cencode_full_eq bnd X v ec) Xs ec) vals ec
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
    CONJ_TAC
    >-(
      pop_assum mp_tac>>
      qmatch_goalsub_abbrev_tac
        ‘fold_cenc cf _ _ = _ ⇒ enc_rel _ _ (FLAT (MAP f _)) _ _’>>
      rename1 ‘fold_cenc _ ls _’>>
      qid_spec_tac ‘ec'’>>
      qid_spec_tac ‘xs’>>
      qid_spec_tac ‘ec’>>
      qid_spec_tac ‘ls’>>
      ho_match_mp_tac enc_rel_fold_cenc>>
      simp[Abbr‘cf’,Abbr‘f’]>>
      strip_tac>>
      qmatch_goalsub_abbrev_tac
        ‘fold_cenc cf _ _ = _ ⇒ enc_rel _ _ (FLAT (MAP f _)) _ _’>>
      qid_spec_tac ‘Xs’>>
      ho_match_mp_tac enc_rel_fold_cenc>>
      simp[Abbr‘cf’,Abbr‘f’]>>
      metis_tac[enc_rel_encode_full_eq])>>
    irule enc_rel_abstr_cong>>
    simp[abstr_flat_app,encode_some_eq_def,MAP_MAP_o,o_DEF])>>
  simp[cencode_bitsum_def]
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
    intLib.ARITH_TAC)>>
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
      (flat_app
        (MAPi
          (λi X.
            cbimply_var bnd (eqi name i (strlit"al1"))
              (at_least_one (MAP (λv. Pos (INL (Eq X v))) iS)))
          Xs))
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
  >-(
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

(* (encode_full_eq_ilist bnd X iS) extends (encode_full_eq bnd X v)
   from a single int ‘v’ to an int list ‘iS’ *)
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

Definition cencode_counting_constr_def:
  cencode_counting_constr bnd c name ec =
  case c of
    AllDifferent Xs => (cencode_all_different bnd Xs name, ec)
  | NValue Xs Y => cencode_n_value bnd Xs Y name ec
  | Count Xs Y Z => (cencode_count bnd Xs Y Z name, ec)
  | Among Xs iS Y => cencode_among bnd Xs iS Y name ec
End

Theorem cencode_counting_constr_sem:
  valid_assignment bnd wi ∧
  cencode_counting_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_counting_constr bnd c name) ec ec'
Proof
  Cases_on ‘c’>>
  simp[cencode_counting_constr_def,encode_counting_constr_def]
  >-simp[cencode_all_different_def,encode_all_different_def]
  >-simp[cencode_n_value_sem]
  >-simp[cencode_count_def,encode_count_def]
  >-simp[cencode_among_sem]
QED
