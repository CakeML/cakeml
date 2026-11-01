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

(* the channel rows: Xs[i] = offy+j ⇔ Ys[j] = offx+i *)
Definition cencode_inverse_pairs_def:
  cencode_inverse_pairs name Xs offx Ys offy =
  flat_app (MAPi (λi X. flat_app (MAPi (λj Y.
    List (mk_annotate
      [mk_name name (toString (i+1) ^ «_» ^ toString (j+1) ^ «ge»);
       mk_name name (toString (i+1) ^ «_» ^ toString (j+1) ^ «le»)]
      (encode_bvar_eq (INL (Eq X (offy + &j))) (INL (Eq Y (offx + &i))))))
    Ys)) Xs)
End

(* the range rows of Xs and Ys, then the channel rows *)
Definition cencode_inverse_rows_def:
  cencode_inverse_rows bnd name Xs offx Ys offy =
  let n = LENGTH Xs in
  Append (cmk_bounds_all bnd name «X_» Xs offy (offy + &n - 1))
    (Append (cmk_bounds_all bnd name «Y_» Ys offx (offx + &n - 1))
      (cencode_inverse_pairs name Xs offx Ys offy))
End

Theorem abstr_cencode_inverse_pairs:
  abstr (cencode_inverse_pairs name Xs offx Ys offy) =
  FLAT (FLAT (MAPi (λi X. MAPi (λj Y.
    encode_bvar_eq (INL (Eq X (offy + &j))) (INL (Eq Y (offx + &i)))) Ys) Xs))
Proof
  simp[cencode_inverse_pairs_def,indexedListsTheory.MAP_MAPi,o_DEF,
       abstrl_mk_annotate,rich_listTheory.FLAT_FLAT]
QED

Definition encode_inverse_def:
  encode_inverse bnd Xsi Ysi name =
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
    abstr (cencode_inverse_rows bnd name Xs offx Ys offy)
End

Theorem encode_inverse_sem_1:
  valid_assignment bnd wi ∧
  inverse_sem Xsi Ysi wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_inverse bnd Xsi Ysi name)
Proof
  simp[encode_inverse_def,cencode_inverse_rows_def,append_thm,
       abstr_cencode_inverse_pairs]>>
  rpt (pairarg_tac>>fs[inverse_sem_def])>>
  rw[cmk_bounds_all_sem]
  >~[‘encode_full_eq _ _ _’]
  >-(
    simp[EVERY_FLAT,EVERY_GENLIST,EVERY_MAP,reify_avar_def]>>
    simp[EVERY_MEM,reify_reif_def])
  >~[‘encode_bvar_eq _ _’]
  >-(
    ntac 2 (rw[EVERY_FLAT,Once EVERY_MEM,MEM_MAPi])>>
    simp[reify_avar_def,reify_reif_def]>>
    rename1‘j < LENGTH Ys’>>

    ntac 2 (pop_assum mp_tac)>>
    pop_assum $ qspecl_then[‘&i + offx’,‘&j + offy’] mp_tac>>
    simp[]>>
    qmatch_goalsub_abbrev_tac
    ‘(P ⇒ (varc _ (EL a _) = c ⇔ varc _ (EL b _) = d)) ⇒
      Q ⇒ R ⇒ (_ = e ⇔ _ = f)’>>
    ‘(P ⇔ (Q ∧ R)) ∧ a = i ∧ b = j ∧
      c = e ∧ d = f’ suffices_by metis_tac[]>>
    unabbrev_all_tac>>
    intLib.ARITH_TAC)>>
  fs[EVERY_MEM,mk_array_ind_def]>>
  last_x_assum $ drule_then mp_tac>>
  intLib.ARITH_TAC
QED

Theorem encode_inverse_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_inverse bnd Xsi Ysi name) ⇒
  inverse_sem Xsi Ysi wi
Proof
  simp[encode_inverse_def,cencode_inverse_rows_def,append_thm,
       abstr_cencode_inverse_pairs]>>
  rpt (pairarg_tac>>fs[])>>
  rename1‘inverse_sem (Xs,offx) (Ys,offy) _’>>
  simp[inverse_sem_def]>>
  IF_CASES_TAC
  >- rw[]>>
  strip_tac>>
  fs[EVERY_APPEND]>>
  qpat_x_assum`EVERY _ (abstr (cmk_bounds_all _ _ «X_» _ _ _))`mp_tac>>
  qpat_x_assum`EVERY _ (abstr (cmk_bounds_all _ _ «Y_» _ _ _))`mp_tac>>
  simp[cmk_bounds_all_sem]>>
  rpt strip_tac
  >- (
    rw[EVERY_MEM,mk_array_ind_def]>>
    qpat_x_assum`∀X. MEM X Xs ⇒ _`drule>>intLib.ARITH_TAC)
  >- (
    rw[EVERY_MEM,mk_array_ind_def]>>
    qpat_x_assum`∀X. MEM X Ys ⇒ _`drule>>intLib.ARITH_TAC)>>
  `Num (i − offx) < LENGTH Ys ∧ Num (j − offy) < LENGTH Ys ∧
   offx + &Num (i − offx) = i ∧ offy + &Num (j − offy) = j` by intLib.ARITH_TAC>>
  qabbrev_tac`a = Num (i − offx)`>>
  qabbrev_tac`b = Num (j − offy)`>>
  sg`wb (INL (Eq (EL a Xs) (offy + &b))) ⇔ wb (INL (Eq (EL b Ys) (offx + &a)))`
  >- (
    qpat_x_assum`EVERY _ (FLAT (FLAT (MAPi _ _)))`mp_tac>>
    simp[EVERY_FLAT]>>
    simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS]>>
    simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS]>>
    disch_then (qspec_then`a`mp_tac)>>simp[]>>
    disch_then (qspec_then`b`mp_tac)>>simp[])>>
  qpat_x_assum`EVERY _ (FLAT (FLAT (GENLIST _ _)))`mp_tac>>
  simp[EVERY_FLAT,EVERY_GENLIST,EVERY_MAP,EVERY_MEM]>>
  strip_tac>>
  `wb (INL (Eq (EL a Xs) j)) ⇔ varc wi (EL a Xs) = j` by (
    first_x_assum (qspec_then`b`mp_tac)>>simp[EL_MEM])>>
  `wb (INL (Eq (EL b Ys) i)) ⇔ varc wi (EL b Ys) = i` by (
    first_x_assum (qspec_then`a`mp_tac)>>simp[EL_MEM])>>
  qpat_x_assum`wb _ ⇔ wb _`mp_tac>>
  ntac 2 (qpat_x_assum`_ + _ = _`(SUBST_ALL_TAC o SYM))>>
  simp[]
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
      (Append xs (cencode_inverse_rows bnd name Xs offx Ys offy), ec')
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
  enc_rel wi es (encode_inverse bnd Xsi Ysi name) ec ec'
Proof
  simp[cencode_inverse_def,encode_inverse_def]>>
  rpt (pairarg_tac>>fs[])>>
  IF_CASES_TAC>>
  rw[]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_abstr>>
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
    encode_inverse bnd Xsi Ysi name
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
