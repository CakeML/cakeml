(*
  Formalization of the CP to ILP phase (channeling constraints)
*)
Theory cp_to_ilp_channeling
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* Inverse:
   With Xsi = (Xs,offx) and Ysi = (Ys,offy) and LENGTH Xs = LENGTH Ys = n,

   1. both Xs and Ys are permutations of 0,...,n - 1 (plus offset), and
   2. they are inverse to each other (minus offset), i.e.,
      for all indices i and j (each with offset):
        Xs[i - offx] = j ⇔ Ys[j - offy] = i
*)

Definition mk_bounds_def:
  mk_bounds X a b =
  [
    mk_constraint_one_ge 1 X a;
    mk_constraint_one_ge (-1) X (-b)
  ]
End

Theorem mk_bounds_sem[simp]:
  EVERY (λx. iconstraint_sem x (wi,wb)) (mk_bounds X a b) ⇔
  varc wi X ≥ a ∧ varc wi X ≤ b
Proof
  simp[mk_bounds_def]>>
  intLib.ARITH_TAC
QED

Definition encode_inverse_aux_def:
  encode_inverse_aux Xs offx Ys offy n =
  FLAT (
    MAP (λX. mk_bounds X offy (offy + &n - 1)) Xs ++
    MAP (λY. mk_bounds Y offx (offx + &n - 1)) Ys ++
    FLAT (GENLIST
      (λi. GENLIST
        (λj. encode_bvar_eq
          (INL (Eq (EL i Xs) (offy + &j)))
          (INL (Eq (EL j Ys) (offx + &i))))
        n)
      n))
End

Definition encode_inverse_def:
  encode_inverse bnd Xsi Ysi =
  let (Xs,offx) = Xsi in
  let (Ys,offy) = Ysi in
  let n = LENGTH Xs in
  if n ≠ LENGTH Ys then
    [false_constr]
  else
    FLAT (FLAT $ GENLIST
      (λi.
        (MAP (λX. encode_full_eq bnd X (offy + &i)) Xs) ++
        (MAP (λY. encode_full_eq bnd Y (offx + &i)) Ys))
      n) ++
    encode_inverse_aux Xs offx Ys offy n
End

Theorem encode_inverse_sem_1:
  valid_assignment bnd wi ∧
  inverse_sem Xsi Ysi wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_inverse bnd Xsi Ysi)
Proof
  simp[encode_inverse_def,encode_inverse_aux_def]>>
  rpt (pairarg_tac>>fs[inverse_sem_def])>>
  rw[]
  >~[‘encode_full_eq _ _ _’]
  >-(
    simp[EVERY_FLAT,EVERY_GENLIST,EVERY_MAP,reify_avar_def]>>
    simp[EVERY_MEM,reify_reif_def])
  >~[‘encode_bvar_eq _ _’]
  >-(
    rw[EVERY_FLAT,EVERY_GENLIST,reify_avar_def,reify_reif_def]>>
    ntac 2 (pop_assum mp_tac)>>
    rename1‘i < _ ⇒ j < _ ⇒ _’>>
    pop_assum $ qspecl_then[‘&i + offx’,‘&j + offy’] mp_tac>>
    simp[]>>
    qmatch_goalsub_abbrev_tac
    ‘(P ⇒ (varc _ (EL a _) = c ⇔ varc _ (EL b _) = d)) ⇒
      Q ⇒ R ⇒ (_ = e ⇔ _ = f)’>>
    ‘(P ⇔ (Q ∧ R)) ∧ a = i ∧ b = j ∧
      c = e ∧ d = f’ suffices_by metis_tac[]>>
    unabbrev_all_tac>>
    intLib.ARITH_TAC)>>
  simp[mk_bounds_def,EVERY_FLAT]>>
  qmatch_goalsub_abbrev_tac‘EVERY P (MAP _ _)’>>
  rw[EVERY_MAP,EVERY_MEM,Abbr‘P’]>>
  fs[EVERY_MEM,mk_array_ind_def]>>
  last_x_assum $ drule_then mp_tac>>
  intLib.ARITH_TAC
QED

Theorem encode_inverse_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_inverse bnd Xsi Ysi) ⇒
  inverse_sem Xsi Ysi wi
Proof
  simp[encode_inverse_def,encode_inverse_aux_def]>>
  rpt (pairarg_tac>>fs[inverse_sem_def])>>
  IF_CASES_TAC>>
  rw[EVERY_FLAT,EVERY_GENLIST,EVERY_MAP]>>
  gvs[EVERY_MEM]
  >~[‘varc _ _ = _ ⇔ _’]
  >-(
    rename1‘_ = j ⇔ _ = i’>>
    rename1‘LENGTH Xs = LENGTH Ys’>>
    last_assum $ qspec_then‘Num (i - offx)’ assume_tac>>
    ‘Num (i - offx) < LENGTH Ys’ by intLib.ARITH_TAC>>
    fs[]>>
    last_assum $ qspec_then‘Num (j - offy)’ assume_tac>>
    ‘Num (j - offy) < LENGTH Ys’ by intLib.ARITH_TAC>>
    fs[]>>
    gs[EL_MEM]>>
    pop_assum mp_tac>>
    first_x_assum $ drule_then mp_tac>>
    rw[]>>
    first_x_assum $ drule_then mp_tac>>
    qmatch_goalsub_abbrev_tac‘(_ = a ⇔ _ = b) ⇒ _’>>
    ‘a = j ∧ b = i’ suffices_by metis_tac[]>>
    unabbrev_all_tac>>
    intLib.ARITH_TAC
  )>>
  rw[mk_array_ind_def]>>
  last_x_assum $ drule_then mp_tac>>
  intLib.ARITH_TAC
QED

Definition cencode_inverse_def:
  cencode_inverse bnd Xsi Ysi name ec =
  let (Xs,offx) = Xsi in
  let (Ys,offy) = Ysi in
  let n = LENGTH Xs in
  if n ≠ LENGTH Ys then
    (cfalse_constr,ec)
  else
    let
      (xs,ec') =
        fold_cenc
          (λi ec'.
            let
              (xs1,ec'') =
                fold_cenc (λX ec. cencode_full_eq bnd X (&i+offy) ec) Xs ec';
              (xs2,ec) =
                fold_cenc (λY ec. cencode_full_eq bnd Y (&i+offx) ec) Ys ec''
            in
              (Append xs1 xs2,ec))
          (COUNT_LIST n)
          ec
    in
      (Append xs
        (List $ mk_annotate
          (FLAT
            (GENLIST
              (λi.
                [
                  mk_name name
                    (strlit"X," ^ int_to_string #"-" (&i+1) ^ strlit",lb");
                  mk_name name
                    (strlit"X," ^ int_to_string #"-" (&i+1) ^ strlit",ub");
                ])
              n ++
            GENLIST
              (λi.
                [
                  mk_name name
                    (strlit"Y," ^ int_to_string #"-" (&i+1) ^ strlit",lb");
                  mk_name name
                    (strlit"Y," ^ int_to_string #"-" (&i+1) ^ strlit",ub");
                ])
              n ++
            FLAT (GENLIST
              (λi. GENLIST
                (λj.
                  [
                    mk_name name
                      (int_to_string #"-" (&i+1) ^ strlit"," ^
                        int_to_string #"-" (&j+1) ^ strlit"ge");
                    mk_name name
                      (int_to_string #"-" (&i+1) ^ strlit"," ^
                        int_to_string #"-" (&j+1) ^ strlit"le")
                  ])
                n)
              n)))
          (encode_inverse_aux Xs offx Ys offy n)),
      ec')
End

Theorem FLAT_FLAT_MAP:
  FLAT $ FLAT (MAP f ls) = FLAT $ MAP (λi. FLAT (f i)) ls
Proof
  Induct_on‘ls’>>
  simp[]
QED

Theorem cencode_inverse_sem:
  valid_assignment bnd wi ∧
  cencode_inverse bnd Xsi Ysi name ec = (es, ec') ⇒
  enc_rel wi es (encode_inverse bnd Xsi Ysi) ec ec'
Proof
  simp[cencode_inverse_def,encode_inverse_def]>>
  rpt (pairarg_tac>>fs[])>>
  IF_CASES_TAC>>
  rw[]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_List_mk_annotate>>
  simp[GSYM MAP_COUNT_LIST]>>
  rename1‘MAP _ ls’>>
  qmatch_goalsub_abbrev_tac‘FLAT (MAP f _)’>>
  simp[FLAT_FLAT_MAP]>>
  irule enc_rel_fold_cenc>>
  simp[Abbr‘f’]>>
  last_x_assum (fn thm => irule_at Any thm)>>
  rw[]>>
  gvs[UNCURRY_EQ]>>
  irule enc_rel_Append>>
  rpt (irule_at Any enc_rel_fold_cenc)>>
  ntac 2 (pop_assum (fn thm => irule_at Any thm)>>simp[])>>
  rw[]>>
  irule_at Any enc_rel_encode_full_eq>>
  simp[]>>
  qmatch_asmsub_abbrev_tac‘cencode_full_eq _ _ a _’>>
  qmatch_goalsub_abbrev_tac‘cencode_full_eq _ _ b _’>>
  ‘a = b’suffices_by metis_tac[]>>
  unabbrev_all_tac>>
  intLib.ARITH_TAC
QED

Definition encode_channeling_constr_def:
  encode_channeling_constr bnd c name =
  case c of Inverse Xsi Ysi =>
    encode_inverse bnd Xsi Ysi
End

Theorem encode_channeling_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Channeling c) ∧
  channeling_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_channeling_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_channeling_constr_def,channeling_constr_sem_def]>>
  metis_tac[encode_inverse_sem_1]
QED

Theorem encode_channeling_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_channeling_constr bnd c name) ⇒
  channeling_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_channeling_constr_def,channeling_constr_sem_def]>>
  metis_tac[encode_inverse_sem_2]
QED

(* Concrete encodings - TODO *)
Definition cencode_channeling_constr_def:
  cencode_channeling_constr bnd c name ec =
  case c of Inverse Xsi Ysi =>
    cencode_inverse bnd Xsi Ysi name ec
End

Theorem cencode_channeling_constr_sem:
  valid_assignment bnd wi ∧
  cencode_channeling_constr bnd c name ec = (es, ec') ⇒
  enc_rel wi es (encode_channeling_constr bnd c name) ec ec'
Proof
  Cases_on‘c’>>
  rw[cencode_channeling_constr_def,encode_channeling_constr_def]
  >- metis_tac[cencode_inverse_sem]
QED
