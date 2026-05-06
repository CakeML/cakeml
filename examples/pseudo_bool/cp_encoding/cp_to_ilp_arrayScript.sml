(*
  Formalization of the CP to ILP phase (array constraints)
*)
Theory cp_to_ilp_array
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* Element: Xs[Y - offset] = Z *)
Definition encode_proper_index_def:
  encode_proper_index bnd Yi n =
  let
    (Y,offset) = Yi;
    (lb,ub) =
    case Y of
      INL vY => bnd vY
    | INR cY => (cY,cY);
    lbc =
    if lb < offset
    then [mk_constraint_one_ge 1 Y offset]
    else [];
    ubc =
    if ub > offset + n - 1
    then [mk_constraint_one_ge (-1) Y (1 - n - offset)]
    else []
  in
    lbc ++ ubc
End

Theorem encode_proper_index_lem[local]:
  valid_assignment bnd wi ∧
  0 ≤ varc wi Y − offset ∧
  Num (varc wi Y − offset) < n ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_proper_index bnd (Y,offset) &n)
Proof
  rw[encode_proper_index_def]>>
  every_case_tac>>
  pairarg_tac>>
  rw[]>>
  intLib.ARITH_TAC
QED

Definition cencode_proper_index_def:
  cencode_proper_index bnd Yi n name =
  let
    (Y,offset) = Yi;
    (lb,ub) =
      case Y of
        INL vY => bnd vY
      | INR cY => (cY,cY);
    lbann =
      if lb < offset
      then [mk_name name $ strlit"lb"]
      else [];
    ubann =
      if ub > offset + n - 1
      then [mk_name name $ strlit"ub"]
      else []
  in
    List $ mk_annotate
      (lbann ++ ubann)
      (encode_proper_index bnd Yi n)
End

Definition encode_element_aux_def:
  encode_element_aux bnd Xs Yi Z =
  let
    (Y,offset) = Yi
  in
    FLAT $ MAPi
      (λi X.
        [
          bits_imply bnd [Pos $ INL (Eq Y $ offset + &i)] (mk_ge X Z);
          bits_imply bnd [Pos $ INL (Eq Y $ offset + &i)] (mk_le X Z)
        ])
      Xs
End

Definition cencode_element_aux_def:
  cencode_element_aux bnd Xs Yi Z name =
  List $ mk_annotate
    (FLAT $ MAPi
      (λi X.
        [
          mk_name name (int_to_string #"-" (&i) ^ strlit"ge");
          mk_name name (int_to_string #"-" (&i) ^ strlit"le")
        ])
      Xs)
    (encode_element_aux bnd Xs Yi Z)
End

Definition cencode_element_def:
  cencode_element bnd Xs Yi Z name ec =
  let
    len = LENGTH Xs;
    (Y,offset) = Yi;
    (lb,ub) =
      case Y of
        INL vY => bnd vY
      | INR cY => (cY,cY);
    (xs,ec') =
      fold_cenc
        (λi ec. cencode_full_eq bnd Y (offset + &i) ec)
        (COUNT_LIST len)
        ec
  in
    (Append
      xs
      (Append
        (cencode_proper_index bnd Yi (&len) name)
        (cencode_element_aux bnd Xs Yi Z name)),
    ec')
End

Definition encode_element_def:
  encode_element bnd Xs Yi Z =
  let
    len = LENGTH Xs;
    (Y,offset) = Yi;
    (lb,ub) =
      case Y of
        INL vY => bnd vY
      | INR cY => (cY,cY)
  in
    (FLAT $ GENLIST (λi. encode_full_eq bnd Y (offset + &i)) len) ++
    (encode_proper_index bnd Yi (&len)) ++
    (encode_element_aux bnd Xs Yi Z)
End

Theorem encode_full_eq_lem[local]:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (FLAT (GENLIST
      (λi. encode_full_eq bnd Y (offset + &i))
      (LENGTH Xs)))
Proof
  rw[EVERY_FLAT,Once EVERY_MEM,MEM_GENLIST]>>
  simp[encode_full_eq_sem,reify_avar_def,reify_reif_def]
QED

Theorem encode_element_sem_1:
  valid_assignment bnd wi ∧
  element_sem Xs Yi Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_element bnd Xs Yi Z)
Proof
  PairCases_on ‘Yi’>>
  rename1 ‘(Y,offset)’>>
  Cases_on ‘Xs = []’>>
  rw[element_sem_def,mk_array_ind_def,
    encode_element_def,encode_proper_index_lem,encode_element_aux_def,
    encode_full_eq_lem]>>
  rw[EVERY_FLAT,Once EVERY_MEM,MEM_MAPi]>>
    simp[EVERY_MEM,reify_avar_def,reify_reif_def,varc_def]>>
    intLib.ARITH_TAC
QED

Theorem encode_element_sem_2_aux:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_proper_index bnd (Y,offset) (&len)) ⇒
  0 ≤ varc wi Y − offset ∧ Num (varc wi Y − offset) < len
Proof
  Cases_on ‘Y’>>
  strip_tac
  >-(
    rename1 ‘INL vY’>>
    Cases_on ‘bnd vY’>>
    fs[valid_assignment_def]>>
    last_x_assum $ drule_then assume_tac>>
    gs[encode_proper_index_def,varc_def]>>
    every_case_tac>>
    fs[varc_def]>>
    intLib.ARITH_TAC)
  >-(
    gs[encode_proper_index_def,varc_def]>>
    every_case_tac>>
    fs[varc_def]>>
    intLib.ARITH_TAC)
QED

Theorem encode_element_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_element bnd Xs Yi Z) ⇒
  element_sem Xs Yi Z wi
Proof
  PairCases_on ‘Yi’>>
  rename1 ‘element_sem _ (Y,offset) _ _’>>
  strip_tac>>
  gs[EVERY_FLAT,element_sem_def,mk_array_ind_def,encode_element_def,
    MEM_FLAT,SF DNF_ss,EVERY_GENLIST]>>
  simp[CONJ_ASSOC]>>
  CONJ_ASM1_TAC
  >-metis_tac[encode_element_sem_2_aux]>>
  fs[encode_element_aux_def,EVERY_FLAT,SF DNF_ss]>>
  gvs[MEM_MAPi,SF DNF_ss,EVERY_MEM]>>
  rpt (last_x_assum $ drule_then assume_tac)>>
  intLib.ARITH_TAC
QED

Theorem cencode_element_sem:
  valid_assignment bnd wi ∧
  cencode_element bnd Xs Yi Z name ec = (es,ec') ⇒
  enc_rel wi es (encode_element bnd Xs Yi Z) ec ec'
Proof
  PairCases_on ‘Yi’>>
  rename1 ‘(Y,offset)’>>
  rw[cencode_element_def,encode_element_def,UNCURRY_EQ]>>
  pure_rewrite_tac[GSYM APPEND_ASSOC]>>
  irule enc_rel_Append>>
  drule_at Any enc_rel_fold_cenc>>
  gs[SYM MAP_COUNT_LIST]>>
  disch_then $ irule_at Any>>
  simp[enc_rel_encode_full_eq]>>
  irule enc_rel_Append>>
  simp[cencode_proper_index_def,cencode_element_aux_def]>>
  Cases_on ‘Y’
  >~[‘INL vY’]
  >-(
    Cases_on ‘bnd vY’>>
    rw[]>>
    metis_tac[enc_rel_List_mk_annotate])
  >-(
    rw[]>>
    metis_tac[enc_rel_List_mk_annotate])
QED

(* Element2D: Xss[Y1 - offset1][Y2 - offset2] = Z *)
Definition encode_element2d_aux_def:
  encode_element2d_aux bnd Xss Y1i Y2i Z =
  let
    (Y1,offset1) = Y1i;
    (Y2,offset2) = Y2i
  in
    FLAT $ MAPi
      (λi Xs. FLAT $ MAPi
        (λj X.
          [
            bits_imply
              bnd
              [Pos $ INL (Eq Y1 $ offset1 + &i); Pos $ INL (Eq Y2 $ offset2 + &j)]
              (mk_ge X Z);
            bits_imply
              bnd
              [Pos $ INL (Eq Y1 $ offset1 + &i); Pos $ INL (Eq Y2 $ offset2 + &j)]
              (mk_le X Z)
          ])
        Xs)
      Xss
End

Definition cencode_element2d_aux_def:
  cencode_element2d_aux bnd Xss Y1i Y2i Z name =
  let
    (Y1,offset1) = Y1i;
    (Y2,offset2) = Y2i
  in
    List $ mk_annotate
      (FLAT $ MAPi
        (λi Xs. FLAT $ MAPi
          (λj X.
            [
              mk_name
                name
                (int_to_string #"-" (&i) ^ strlit"," ^
                  int_to_string #"-" (&j) ^ strlit"ge");
              mk_name
                name
                (int_to_string #"-" (&i) ^ strlit"," ^
                  int_to_string #"-" (&j) ^ strlit"le")
            ])
          Xs)
        Xss)
      (encode_element2d_aux bnd Xss Y1i Y2i Z)
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
        (lb1,ub1) =
          case Y1 of
            INL vY1 => bnd vY1
          | INR cY1 => (cY1,cY1);
        (lb2,ub2) =
          case Y2 of
            INL vY2 => bnd vY2
          | INR cY2 => (cY2,cY2);
        (xs',ec') =
          fold_cenc
            (λi ec. cencode_full_eq bnd Y1 (offset1 + &i) ec)
            (COUNT_LIST len1)
            ec;
        (xs'',ec'') =
          fold_cenc
            (λj ec. cencode_full_eq bnd Y2 (offset2 + &j) ec)
            (COUNT_LIST len2)
            ec'
        in
          (Append
            (Append xs' xs'')
            (Append
              (Append
                (cencode_proper_index bnd Y1i (&len1) name)
                (cencode_proper_index bnd Y2i (&len2) name))
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
  encode_element2d bnd Xss Y1i Y2i Z =
  if 0 < LENGTH Xss ∧ ∃l. EVERY (λXs. LENGTH Xs = l) Xss
  then
    let
      len1 = LENGTH Xss;
      len2 = LENGTH $ HD Xss;
      (Y1,offset1) = Y1i;
      (Y2,offset2) = Y2i;
      (lb1,ub1) =
        case Y1 of
          INL vY1 => bnd vY1
        | INR cY1 => (cY1,cY1);
      (lb2,ub2) =
        case Y2 of
          INL vY2 => bnd vY2
        | INR cY2 => (cY2,cY2)
    in
      (FLAT $ GENLIST (λi. encode_full_eq bnd Y1 (offset1 + &i)) len1) ++
      (FLAT $ GENLIST (λj. encode_full_eq bnd Y2 (offset2 + &j)) len2) ++
      (encode_proper_index bnd Y1i (&len1)) ++
      (encode_proper_index bnd Y2i (&len2)) ++
      (encode_element2d_aux bnd Xss Y1i Y2i Z)
  else [false_constr]
End

Theorem encode_element2d_sem_1:
  valid_assignment bnd wi ∧
  element2d_sem Xss Y1i Y2i Z wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_element2d bnd Xss Y1i Y2i Z)
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
  rw[encode_element2d_def,encode_element2d_aux_def,
    encode_full_eq_lem,encode_proper_index_lem]
  >-(
    ntac 2 (rw[EVERY_FLAT,Once EVERY_MEM,MEM_MAPi])>>
    simp[EVERY_MEM,reify_avar_def,reify_reif_def,varc_def]>>
    intLib.ARITH_TAC)
  >-metis_tac[NOT_EVERY]
QED

Theorem encode_element2d_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_element2d bnd Xss Y1i Y2i Z) ⇒
  element2d_sem Xss Y1i Y2i Z wi
Proof
  PairCases_on ‘Y1i’>>
  PairCases_on ‘Y2i’>>
  rename1 ‘element2d_sem _ (Y1,offset1) _ _ _’>>
  rw[encode_element2d_def,element2d_sem_def,mk_array_ind_def,
    EVERY_FLAT,MEM_FLAT,EVERY_GENLIST,SF DNF_ss]>>
  ‘EVERY (λXs. LENGTH Xs = LENGTH (HD Xss)) Xss’ by (
    Cases_on ‘Xss’>>
    fs[])>>
  qexists ‘LENGTH (HD Xss)’>>
  simp[CONJ_ASSOC]>>
  CONJ_ASM1_TAC
  >-(
    gs[]>>
    simp[Once $ GSYM CONJ_ASSOC]>>
    CONJ_TAC>>
    metis_tac[encode_element_sem_2_aux])>>
  fs[encode_element2d_aux_def,EVERY_FLAT]>>
  qmatch_asmsub_abbrev_tac ‘EVERY P (MAPi _ _)’>>
  fs[MEM_MAPi,SF DNF_ss,EVERY_MEM]>>
  first_x_assum $ drule_then assume_tac>>
  fs[Abbr‘P’,EVERY_FLAT]>>
  qmatch_asmsub_abbrev_tac ‘EVERY P (MAPi _ _)’>>
  fs[EVERY_MEM,MEM_MAPi,SF DNF_ss]>>
  ‘LENGTH (EL (Num (varc wi Y1 − offset1)) Xss) =
    LENGTH (HD Xss)’ by simp[EL_MEM]>>
  fs[]>>
  rpt (first_x_assum $ drule_then assume_tac)>>
  unabbrev_all_tac>>
  gs[]>>
  intLib.ARITH_TAC
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
  enc_rel wi es (encode_element2d bnd Xss Y1i Y2i Z) ec ec'
Proof
  PairCases_on ‘Y1i’>>
  PairCases_on ‘Y2i’>>
  simp[cencode_element2d_def,encode_element2d_def,cencode_element2d_len_lem]>>
  rw[UNCURRY_EQ,SYM MAP_COUNT_LIST]>>
  gvs[]>>
  pure_rewrite_tac[METIS_PROVE[APPEND_ASSOC]
    “a ++ b ++ c ++ d ++ e = a ++ b ++ (c ++ d ++ e)”]>>
  rpt (irule_at Any enc_rel_Append)>>
  drule_at Any enc_rel_fold_cenc>>
  disch_then $ irule_at Any>>
  rev_drule_at Any enc_rel_fold_cenc>>
  disch_then $ irule_at Any>>
  simp[enc_rel_encode_full_eq,cencode_proper_index_def]>>
  ntac 2 (qexists ‘ec'’)>>
  every_case_tac>>
  rpt (pairarg_tac>>fs[])>>
  rpt IF_CASES_TAC>>
  simp[enc_rel_List_mk_annotate,cencode_element2d_aux_def]
QED

(* ArrayMax: Y = max(Xs) *)
Definition cencode_array_max_def:
  cencode_array_max bnd Xs Y name =
  if NULL Xs
  then cfalse_constr
  else
    Append
      (flat_app (MAPi (λi X. cvar_imply bnd (arri name i) (mk_ge X Y)) Xs)) $
      Append
        (flat_app (MAPi (λi X. List $
          mk_annotate
            [mk_name name $ int_to_string #"-" (&i) ^ strlit"le"]
            [mk_le X Y]) Xs)) $
        cat_least_one name $ GENLIST (λi. Pos $ arri name i) (LENGTH Xs)
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
  >-simp[cfalse_constr_def]>>
  simp[EVERY_FLAT]>>
  qmatch_goalsub_abbrev_tac ‘EVERY P (MAPi _ _)’>>
  rw[EVERY_MEM,MEM_MAPi,SF DNF_ss]>>
  unabbrev_all_tac>>
  gs[MEM_EL]
  >-(
    rename1 ‘n < LENGTH Xs’>>
    qexists ‘n’>>
    ntac 3 (first_x_assum $ drule_then assume_tac)>>
    simp[EL_MAP]>>
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
      (flat_app (MAPi (λi X. cvar_imply bnd (arri name i) (mk_le X Y)) Xs)) $
      Append
        (flat_app (MAPi (λi X. List $
          mk_annotate
            [mk_name name $ int_to_string #"-" (&i) ^ strlit"ge"]
            [mk_ge X Y]) Xs)) $
        cat_least_one name $ GENLIST (λi. Pos $ arri name i) (LENGTH Xs)
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
  >-simp[cfalse_constr_def]>>
  simp[EVERY_FLAT]>>
  qmatch_goalsub_abbrev_tac ‘EVERY P (MAPi _ _)’>>
  rw[EVERY_MEM,MEM_MAPi,SF DNF_ss]>>
  unabbrev_all_tac>>
  gs[MEM_EL]
  >-(
    rename1 ‘n < LENGTH Xs’>>
    qexists ‘n’>>
    ntac 3 (first_x_assum $ drule_then assume_tac)>>
    simp[EL_MAP]>>
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
    Element Xs Yi Z => encode_element bnd Xs Yi Z
  | Element2D Xss Y1i Y2i Z => encode_element2d bnd Xss Y1i Y2i Z
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
