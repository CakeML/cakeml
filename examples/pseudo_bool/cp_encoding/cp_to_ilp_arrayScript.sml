(*
  Formalization of the CP to ILP phase (array constraints)
*)
Theory cp_to_ilp_array
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* Element: Xs[Y - offset] = Z; index i gets rows only when Y may take
   offset + i *)
Definition cencode_element_aux_def:
  cencode_element_aux bnd Xs Yi Z name =
  let
    (Y,offset) = Yi;
    yb = varc_bnd bnd Y
  in
    flat_app $ MAPi
      (λi X.
        let y = offset + &i in
        if in_bnd yb y then
          let s = toString i in
          List [
            (SOME (mk_name name (s ^ «ge»)),
              bits_imply bnd [Pos $ INL (Eq Y y)] (mk_ge X Z));
            (SOME (mk_name name (s ^ «le»)),
              bits_imply bnd [Pos $ INL (Eq Y y)] (mk_le X Z))
          ]
        else Nil)
      Xs
End

Definition cencode_element_def:
  cencode_element bnd Xs Yi Z name ec =
  let
    len = LENGTH Xs;
    (Y,offset) = Yi;
    (xs,ec') =
      cencode_in_grid bnd (may_take bnd [Y] (GENLIST (λi. offset + &i) len)) ec
  in
    (Append
      xs
      (Append
        (cencode_proper_index bnd Yi (&len) name «»)
        (cencode_element_aux bnd Xs Yi Z name)),
    ec')
End

Definition encode_element_def:
  encode_element bnd Xs Yi Z name =
  let
    len = LENGTH Xs;
    (Y,offset) = Yi
  in
    encode_in_grid bnd (may_take bnd [Y] (GENLIST (λi. offset + &i) len)) ++
    abstr (cencode_proper_index bnd Yi (&len) name «») ++
    abstr (cencode_element_aux bnd Xs Yi Z name)
End

Theorem cencode_element_aux_sem[local]:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (cencode_element_aux bnd Xs (Y,offset) Z name)) ⇔
  ∀i. i < LENGTH Xs ∧ in_bnd (varc_bnd bnd Y) (offset + &i) ∧
    wb (INL (Eq Y (offset + &i))) ⇒
    varc wi (EL i Xs) = varc wi Z)
Proof
  strip_tac>>
  simp[cencode_element_aux_def,abstr_flat_app]>>
  simp[EVERY_FLAT,EVERY_MAP]>>
  simp[Once EVERY_EL,EL_MAPi,COND_RAND]>>
  eq_tac>>rw[]>>res_tac>>intLib.ARITH_TAC
QED

Theorem encode_element_sem_1:
  valid_assignment bnd wi ∧
  element_sem Xs Yi Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_element bnd Xs Yi Z name)
Proof
  PairCases_on ‘Yi’>>
  rename1 ‘(Y,offset)’>>
  rw[element_sem_def,mk_array_ind_def,encode_element_def,
    cencode_proper_index_sem_1,cencode_element_aux_sem]>>
  gvs[reify_avar_def,reify_reif_def]
QED

Theorem encode_element_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_element bnd Xs Yi Z name) ⇒
  element_sem Xs Yi Z wi
Proof
  PairCases_on ‘Yi’>>
  rename1 ‘element_sem _ (Y,offset) _ _’>>
  strip_tac>>
  gs[encode_element_def,cencode_element_aux_sem]>>
  drule_all_then strip_assume_tac cencode_proper_index_sem_2>>
  simp[element_sem_def,mk_array_ind_def]>>
  qabbrev_tac`k = Num (varc wi Y − offset)`>>
  `offset + &k = varc wi Y` by (
    simp[Abbr`k`,integerTheory.INT_OF_NUM]>>
    intLib.ARITH_TAC)>>
  `in_bnd (varc_bnd bnd Y) (offset + &k)` by metis_tac[in_bnd_varc]>>
  `wb (INL (Eq Y (offset + &k)))` by (
    qpat_x_assum`∀i. MEM i (GENLIST _ _) ∧ _ ⇒ _`(qspec_then`offset + &k`mp_tac)>>
    simp[MEM_GENLIST]>>
    metis_tac[])>>
  metis_tac[]
QED

Theorem cencode_element_sem:
  valid_assignment bnd wi ∧
  cencode_element bnd Xs Yi Z name ec = (es,ec') ⇒
  enc_rel wi es (encode_element bnd Xs Yi Z name) ec ec'
Proof
  PairCases_on ‘Yi’>>
  rename1 ‘(Y,offset)’>>
  rw[cencode_element_def,encode_element_def,UNCURRY_EQ]>>
  pure_rewrite_tac[GSYM APPEND_ASSOC]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_encode_in_grid>>
  first_assum (irule_at Any)>>
  simp[]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_abstr>>
  simp[enc_rel_abstr]
QED

(* Element2D: Xss[Y1 - offset1][Y2 - offset2] = Z; cell (i,j) gets rows only
   when Y1 may take offset1 + i and Y2 may take offset2 + j *)
Definition cencode_element2d_aux_def:
  cencode_element2d_aux bnd Xss Y1i Y2i Z name =
  let
    (Y1,offset1) = Y1i;
    (Y2,offset2) = Y2i;
    yb1 = varc_bnd bnd Y1;
    yb2 = varc_bnd bnd Y2
  in
    flat_app $ MAPi
      (λi Xs.
        let y1 = offset1 + &i in
        if in_bnd yb1 y1 then
          let si = toString i ^ «_» in
          flat_app $ MAPi
            (λj X.
              let y2 = offset2 + &j in
              if in_bnd yb2 y2 then
                let s = si ^ toString j in
                List [
                  (SOME (mk_name name (s ^ «ge»)),
                    bits_imply bnd
                      [Pos $ INL (Eq Y1 y1); Pos $ INL (Eq Y2 y2)]
                      (mk_ge X Z));
                  (SOME (mk_name name (s ^ «le»)),
                    bits_imply bnd
                      [Pos $ INL (Eq Y1 y1); Pos $ INL (Eq Y2 y2)]
                      (mk_le X Z))
                ]
              else Nil)
            Xs
        else Nil)
      Xss
End

Definition cencode_element2d_def:
  cencode_element2d bnd Xss Y1i Y2i Z name ec =
  let
    len1 = LENGTH Xss
  in
  if 0 < len1
  then
    let
      len2 = LENGTH $ HD Xss
    in
      if EVERY (λXs. LENGTH Xs = len2) Xss
      then
      let
        (Y1,offset1) = Y1i;
        (Y2,offset2) = Y2i;
        (xs',ec') =
          cencode_in_grid bnd
            (may_take bnd [Y1] (GENLIST (λi. offset1 + &i) len1)) ec;
        (xs'',ec'') =
          cencode_in_grid bnd
            (may_take bnd [Y2] (GENLIST (λj. offset2 + &j) len2)) ec'
        in
          (Append
            (Append xs' xs'')
            (Append
              (Append
                (cencode_proper_index bnd Y1i (&len1) name «1»)
                (cencode_proper_index bnd Y2i (&len2) name «2»))
              (cencode_element2d_aux
                bnd
                Xss
                Y1i
                Y2i
                Z
                name)),
          ec'')
    else (cfalse_constr,ec)
  else (cfalse_constr,ec)
End

Definition encode_element2d_def:
  encode_element2d bnd Xss Y1i Y2i Z name =
  if 0 < LENGTH Xss ∧ ∃l. EVERY (λXs. LENGTH Xs = l) Xss
  then
    let
      len1 = LENGTH Xss;
      len2 = LENGTH $ HD Xss;
      (Y1,offset1) = Y1i;
      (Y2,offset2) = Y2i
    in
      encode_in_grid bnd (may_take bnd [Y1] (GENLIST (λi. offset1 + &i) len1)) ++
      encode_in_grid bnd (may_take bnd [Y2] (GENLIST (λj. offset2 + &j) len2)) ++
      abstr (cencode_proper_index bnd Y1i (&len1) name «1») ++
      abstr (cencode_proper_index bnd Y2i (&len2) name «2») ++
      abstr (cencode_element2d_aux bnd Xss Y1i Y2i Z name)
  else [false_constr]
End

Theorem cencode_element2d_aux_sem[local]:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (cencode_element2d_aux bnd Xss (Y1,offset1) (Y2,offset2) Z name)) ⇔
  ∀i j. i < LENGTH Xss ∧ j < LENGTH (EL i Xss) ∧
    in_bnd (varc_bnd bnd Y1) (offset1 + &i) ∧ wb (INL (Eq Y1 (offset1 + &i))) ∧
    in_bnd (varc_bnd bnd Y2) (offset2 + &j) ∧ wb (INL (Eq Y2 (offset2 + &j))) ⇒
    varc wi (EL j (EL i Xss)) = varc wi Z)
Proof
  strip_tac>>
  simp[cencode_element2d_aux_def,abstr_flat_app]>>
  simp[EVERY_FLAT,EVERY_MAP]>>
  simp[Once EVERY_EL,EL_MAPi,COND_RAND,abstr_flat_app]>>
  simp[EVERY_FLAT,EVERY_MAP]>>
  simp[Once EVERY_EL,EL_MAPi,COND_RAND]>>
  eq_tac>>rw[]>>res_tac>>intLib.ARITH_TAC
QED

Theorem encode_element2d_sem_1:
  valid_assignment bnd wi ∧
  element2d_sem Xss Y1i Y2i Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_element2d bnd Xss Y1i Y2i Z name)
Proof
  PairCases_on ‘Y1i’>>
  PairCases_on ‘Y2i’>>
  rename1 ‘element2d_sem _ (Y1,offset1) (Y2,offset2) _ _’>>
  Cases_on ‘Xss = []’>>
  rw[element2d_sem_def,mk_array_ind_def]>>
  rename1 ‘EVERY (λXs. LENGTH Xs = len) _’>>
  ‘len = LENGTH (HD Xss)’ by (
    drule HEAD_MEM>>
    fs[EVERY_MEM])>>
  rw[encode_element2d_def,cencode_element2d_aux_sem,cencode_proper_index_sem_1]>>
  gvs[reify_avar_def,reify_reif_def]>>
  metis_tac[NOT_EVERY]
QED

Theorem encode_element2d_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_element2d bnd Xss Y1i Y2i Z name) ⇒
  element2d_sem Xss Y1i Y2i Z wi
Proof
  PairCases_on ‘Y1i’>>
  PairCases_on ‘Y2i’>>
  rename1 ‘element2d_sem _ (Y1,offset1) (Y2,offset2) _ _’>>
  strip_tac>>
  qpat_x_assum ‘EVERY _ (encode_element2d _ _ _ _ _ _)’ mp_tac>>
  simp[encode_element2d_def]>>
  IF_CASES_TAC>>
  simp[cencode_element2d_aux_sem]>>
  strip_tac>>
  ‘EVERY (λXs. LENGTH Xs = LENGTH (HD Xss)) Xss’ by (
    Cases_on ‘Xss’>>
    fs[])>>
  ‘0 ≤ varc wi Y1 − offset1 ∧ Num (varc wi Y1 − offset1) < LENGTH Xss’ by
    metis_tac[cencode_proper_index_sem_2]>>
  ‘0 ≤ varc wi Y2 − offset2 ∧ Num (varc wi Y2 − offset2) < LENGTH (HD Xss)’ by
    metis_tac[cencode_proper_index_sem_2]>>
  simp[element2d_sem_def,mk_array_ind_def]>>
  conj_tac
  >- (
    qexists ‘LENGTH (HD Xss)’>>
    simp[])>>
  qabbrev_tac`k1 = Num (varc wi Y1 − offset1)`>>
  qabbrev_tac`k2 = Num (varc wi Y2 − offset2)`>>
  `offset1 + &k1 = varc wi Y1` by (
    simp[Abbr`k1`,integerTheory.INT_OF_NUM]>>
    intLib.ARITH_TAC)>>
  `offset2 + &k2 = varc wi Y2` by (
    simp[Abbr`k2`,integerTheory.INT_OF_NUM]>>
    intLib.ARITH_TAC)>>
  `LENGTH (EL k1 Xss) = LENGTH (HD Xss)` by fs[EVERY_EL]>>
  `in_bnd (varc_bnd bnd Y1) (offset1 + &k1) ∧
   in_bnd (varc_bnd bnd Y2) (offset2 + &k2)` by
    metis_tac[in_bnd_varc]>>
  `wb (INL (Eq Y1 (offset1 + &k1)))` by (
    qpat_x_assum`∀i. MEM i (GENLIST (λi. offset1 + &i) _) ∧ _ ⇒ _`
      (qspec_then`offset1 + &k1`mp_tac)>>
    simp[MEM_GENLIST]>>
    metis_tac[])>>
  `wb (INL (Eq Y2 (offset2 + &k2)))` by (
    qpat_x_assum`∀i. MEM i (GENLIST (λj. offset2 + &j) _) ∧ _ ⇒ _`
      (qspec_then`offset2 + &k2`mp_tac)>>
    simp[MEM_GENLIST]>>
    metis_tac[])>>
  metis_tac[]
QED

Theorem cencode_element2d_len_lem[local]:
  (0 < LENGTH Xss ∧ ∃l. EVERY (λXs. LENGTH Xs = l) Xss) ⇔
  (0 < LENGTH Xss ∧ EVERY (λXs. LENGTH Xs = LENGTH (HD Xss)) Xss)
Proof
  Cases_on`Xss`>>
  rw[]
QED

Theorem cencode_element2d_sem:
  valid_assignment bnd wi ∧
  cencode_element2d bnd Xss Y1i Y2i Z name ec = (es,ec') ⇒
  enc_rel wi es (encode_element2d bnd Xss Y1i Y2i Z name) ec ec'
Proof
  PairCases_on ‘Y1i’>>
  PairCases_on ‘Y2i’>>
  simp[cencode_element2d_def,encode_element2d_def,cencode_element2d_len_lem]>>
  rw[UNCURRY_EQ]>>
  gvs[]>>
  pure_rewrite_tac[METIS_PROVE[APPEND_ASSOC]
    “a ++ b ++ c ++ d ++ e = a ++ b ++ (c ++ d ++ e)”]>>
  rpt (irule_at Any enc_rel_Append)>>
  ntac 3 (irule_at Any enc_rel_abstr)>>
  drule_at Any enc_rel_encode_in_grid>>
  disch_then $ irule_at Any>>
  rev_drule_at Any enc_rel_encode_in_grid>>
  disch_then $ irule_at Any>>
  simp[]
QED

(* ArrayMax: Y = max(Xs) *)
Definition cencode_array_max_def:
  cencode_array_max bnd Xs Y name =
  if NULL Xs
  then cfalse_constr
  else
    Append
      (flat_app (MAPi (λi X. cbimply_var bnd (arri name i) (mk_ge X Y)) Xs)) $
      Append
        (flat_app (MAPi (λi X. List $
          mk_annotate
            [mk_name name $ toString i ^ «le»]
            [mk_le X Y]) Xs)) $
        cat_least_one name «» $ GENLIST (λi. Pos $ arri name i) (LENGTH Xs)
End

Definition encode_array_max_def:
  encode_array_max bnd Xs Y name =
  abstr $ cencode_array_max bnd Xs Y name
End

Theorem encode_array_max_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Array (ArrayMax Xs Y)) ∧
  array_max_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_array_max bnd Xs Y name)
Proof
  Cases_on ‘NULL Xs’>>
  rw[cencode_array_max_def,encode_array_max_def,array_max_sem_def]>>
  gvs[NULL_EQ]>>
  rw[EVERY_FLAT,Once EVERY_MEM]>>
  gvs[MEM_FLAT,MEM_MAPi]
  >-(
    simp[reify_avar_def,reify_flag_def]>>
    intLib.ARITH_TAC)
  >-(
    gs[EVERY_MEM,MEM_MAP,SF DNF_ss]>>
    drule EL_MEM>>
    strip_tac>>
    first_x_assum drule>>
    intLib.ARITH_TAC)>>
  gs[MEM_EL,SF DNF_ss,MEM_MAP]>>
  rename1 ‘n < LENGTH _’>>
  qexists ‘n’>>
  simp[reify_avar_def,reify_flag_def,EL_MAP]>>
  intLib.ARITH_TAC
QED

Theorem encode_array_max_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_array_max bnd Xs Y name) ⇒
  array_max_sem Xs Y wi
Proof
  simp[encode_array_max_def,cencode_array_max_def,array_max_sem_def]>>
  Cases_on ‘NULL Xs’>>
  gs[NULL_EQ]
  >- simp[cfalse_constr_def]>>
  simp[EVERY_FLAT]>>
  qmatch_goalsub_abbrev_tac ‘EVERY P (MAPi _ _)’>>
  rw[EVERY_MEM,MEM_MAPi,SF DNF_ss]>>
  unabbrev_all_tac>>
  gs[MEM_EL]
  >-(
    first_assum $ irule_at Any>>
    first_x_assum $ drule_then assume_tac>>
    first_x_assum $ drule_then assume_tac>>
    gvs[EL_MAP]>>
    intLib.ARITH_TAC)>>
  gs[EL_MAP]>>
  first_x_assum $ drule_then assume_tac>>
  intLib.ARITH_TAC
QED

Theorem cencode_array_max_sem:
  enc_rel wi (cencode_array_max bnd Xs Y name) (encode_array_max bnd Xs Y name) ec ec
Proof
  simp[encode_array_max_def]
QED

(* ArrayMin: Y = min(Xs) *)
Definition cencode_array_min_def:
  cencode_array_min bnd Xs Y name =
  if NULL Xs
  then cfalse_constr
  else
    Append
      (flat_app (MAPi (λi X. cbimply_var bnd (arri name i) (mk_le X Y)) Xs)) $
      Append
        (flat_app (MAPi (λi X. List $
          mk_annotate
            [mk_name name $ toString i ^ «ge»]
            [mk_ge X Y]) Xs)) $
        cat_least_one name «» $ GENLIST (λi. Pos $ arri name i) (LENGTH Xs)
End

Definition encode_array_min_def:
  encode_array_min bnd Xs Y name =
  abstr $ cencode_array_min bnd Xs Y name
End

Theorem encode_array_min_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Array (ArrayMin Xs Y)) ∧
  array_min_sem Xs Y wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_array_min bnd Xs Y name)
Proof
  Cases_on ‘NULL Xs’>>
  rw[cencode_array_min_def,encode_array_min_def,array_min_sem_def]>>
  gvs[NULL_EQ]>>
  rw[EVERY_FLAT,Once EVERY_MEM]>>
  gvs[MEM_FLAT,MEM_MAPi]
  >-(
    simp[reify_avar_def,reify_flag_def]>>
    intLib.ARITH_TAC)
  >-(
    gs[EVERY_MEM,MEM_MAP,SF DNF_ss]>>
    drule EL_MEM>>
    strip_tac>>
    first_x_assum drule>>
    intLib.ARITH_TAC)>>
  gs[MEM_EL,SF DNF_ss,MEM_MAP]>>
  rename1 ‘n < LENGTH _’>>
  qexists ‘n’>>
  simp[reify_avar_def,reify_flag_def,EL_MAP]>>
  intLib.ARITH_TAC
QED

Theorem encode_array_min_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_array_min bnd Xs Y name) ⇒
  array_min_sem Xs Y wi
Proof
  simp[encode_array_min_def,cencode_array_min_def,array_min_sem_def]>>
  Cases_on ‘NULL Xs’>>
  gs[NULL_EQ]
  >- simp[cfalse_constr_def]>>
  simp[EVERY_FLAT]>>
  qmatch_goalsub_abbrev_tac ‘EVERY P (MAPi _ _)’>>
  rw[EVERY_MEM,MEM_MAPi,SF DNF_ss]>>
  unabbrev_all_tac>>
  gs[MEM_EL]
  >-(
    first_assum $ irule_at Any>>
    first_x_assum $ drule_then assume_tac>>
    first_x_assum $ drule_then assume_tac>>
    gvs[EL_MAP]>>
    intLib.ARITH_TAC)>>
  gs[EL_MAP]>>
  first_x_assum $ drule_then assume_tac>>
  intLib.ARITH_TAC
QED

Theorem cencode_array_min_sem:
  enc_rel wi (cencode_array_min bnd Xs Y name) (encode_array_min bnd Xs Y name) ec ec
Proof
  simp[encode_array_min_def]
QED

Definition encode_array_constr_def:
  encode_array_constr bnd c name =
  case c of
    Element Xs Yi Z => encode_element bnd Xs Yi Z name
  | Element2D Xss Y1i Y2i Z => encode_element2d bnd Xss Y1i Y2i Z name
  | ArrayMax Xs Y => encode_array_max bnd Xs Y name
  | ArrayMin Xs Y => encode_array_min bnd Xs Y name
End

Theorem encode_array_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Array c) ∧
  array_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_array_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_array_constr_def,array_constr_sem_def]
  >- metis_tac[encode_element_sem_1]
  >- metis_tac[encode_element2d_sem_1]
  >- metis_tac[encode_array_max_sem_1]
  >- metis_tac[encode_array_min_sem_1]
QED

Theorem encode_array_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_array_constr bnd c name) ⇒
  array_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_array_constr_def,array_constr_sem_def]
  >- metis_tac[encode_element_sem_2]
  >- metis_tac[encode_element2d_sem_2]
  >- metis_tac[encode_array_max_sem_2]
  >- metis_tac[encode_array_min_sem_2]
QED

(* Concrete encodings *)
Definition cencode_array_constr_def:
  cencode_array_constr bnd c name ec =
  case c of
    Element Xs Yi Z => cencode_element bnd Xs Yi Z name ec
  | Element2D Xss Y1i Y2i Z => cencode_element2d bnd Xss Y1i Y2i Z name ec
  | ArrayMax Xs Y => (cencode_array_max bnd Xs Y name,ec)
  | ArrayMin Xs Y => (cencode_array_min bnd Xs Y name,ec)
End

Theorem cencode_array_constr_sem:
  valid_assignment bnd wi ∧
  cencode_array_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_array_constr bnd c name) ec ec'
Proof
  Cases_on‘c’>>
  rw[cencode_array_constr_def,encode_array_constr_def]
  >- metis_tac[cencode_element_sem]
  >- metis_tac[cencode_element2d_sem]
  >- metis_tac[cencode_array_max_sem]
  >- metis_tac[cencode_array_min_sem]
QED
