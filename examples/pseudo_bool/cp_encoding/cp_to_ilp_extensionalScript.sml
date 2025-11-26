(*
  Formalization of the CP to ILP phase (extensional constraints)
*)
Theory cp_to_ilp_extensional
Libs
  preamble
Ancestors
  pbc cp ilp cp_to_ilp

(* Keep only the positions that we need to match *)
Definition filter_match_def:
  (filter_match [] = []) ∧
  (filter_match ((x,topt)::xs) =
    case topt of
      NONE => filter_match xs
    | SOME t => (x,t)::filter_match xs)
End

(* encodes ftable_i ⇔ X = Ti, provided that LENGTH X = LENGTH Ti *)
Definition encode_tuple_eq_def:
  encode_tuple_eq bnd Xts =
    bimply_bits bnd [Pos (INR (Tb Xts))]
      ([], MAP (λ(X,t). (1i, Pos (INL (Eq X t)))) Xts, &LENGTH Xts)
End

(* The reifications needed for tuple eq on a given row *)
Definition reify_tuple_eq_def:
  reify_tuple_eq bnd Xts =
  let
    eqs = FLAT $ MAP (λ(X,t). encode_full_eq bnd X t) Xts;
  in
    eqs ++ encode_tuple_eq bnd Xts
End

Theorem encode_tuple_eq_sem:
  valid_assignment bnd wi ∧
  EVERY (λ(X,t). wb (INL (Eq X t)) ⇔ varc wi X = t) Xts
  ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_tuple_eq bnd Xts) ⇔
  (wb (INR (Tb Xts)) ⇔ EVERY (λ(X,t). varc wi X = t) Xts))
Proof
  rw[encode_tuple_eq_def,iconstraint_sem_def]>>
  simp[eval_lin_term_def]>>
  qho_match_abbrev_tac ‘((P ⇔ R) ⇔ (R ⇔ Q))’>>
  qsuff_tac ‘P ⇔ Q’
  >- metis_tac[]>>
  unabbrev_all_tac>>
  pop_assum mp_tac>>
  last_x_assum kall_tac>>
  Induct_on`Xts`>>rw[iSUM_def]>>
  pairarg_tac>>gvs[]>>
  rw[oneline b2i_def]>>gvs[]
  >- (
    last_x_assum sym_sub_tac>>
    intLib.ARITH_TAC) >>
  simp[MAP_MAP_o,o_DEF,iterateTheory.LAMBDA_PAIR]>>
  qho_match_abbrev_tac`¬ (iSUM (MAP (λx. b2i (f x)) ls) ≥ _)`>>
  `iSUM (MAP (λx. b2i (f x)) ls) ≤ &LENGTH ls` by
    metis_tac[iSUM_MAP_b2i_bound]>>
  intLib.ARITH_TAC
QED

Definition table_ge_def[simp]:
  table_ge Xtss =
    (([], MAP (λXts. (1i, Pos (INR (Tb Xts)))) Xtss, 1):'a aiconstraint)
End

Definition encode_table_def:
  encode_table bnd tss Xs =
  let n = LENGTH Xs in
    if EVERY (λYs. LENGTH Ys = n) tss
    then
      let Xtss = MAP (λts. filter_match (ZIP (Xs,ts))) tss in
      (FLAT $ MAP (λXts. reify_tuple_eq bnd Xts) Xtss) ++
      [table_ge Xtss]
    else
      [false_constr]
End

Theorem match_row_filter_match:
  ∀Xs ts.
  LENGTH ts = LENGTH Xs ⇒
  (match_row ts (MAP wi Xs) ⇔
  EVERY (λ(X,t). wi X = t) (filter_match (ZIP (Xs,ts))))
Proof
  Induct>>rw[]>>
  fs[filter_match_def,match_row_def,LENGTH_CONS]>>
  TOP_CASE_TAC>>gvs[]>>
  metis_tac[]
QED

Theorem encode_tuple_eq_sem_reify:
  valid_assignment bnd wi  ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar wi)) (encode_tuple_eq bnd Xts)
Proof
  rw[encode_tuple_eq_def,reify_avar_def,reify_flag_def]>>
  simp[iconstraint_sem_def,MAP_MAP_o,o_DEF,eval_lin_term_def,iterateTheory.LAMBDA_PAIR,
    reify_avar_def,reify_reif_def,EVERY_MEM]
QED

Theorem reify_tuple_eq_sem_reify:
  valid_assignment bnd wi  ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar wi)) (reify_tuple_eq bnd Xts)
Proof
  rw[reify_tuple_eq_def]>>
  simp[EVERY_FLAT]
  >- simp[Once EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD,reify_avar_def,reify_reif_def]>>
  metis_tac[encode_tuple_eq_sem_reify]
QED

Theorem encode_table_sem_1:
  valid_assignment bnd wi ∧
  table_sem tss Xs wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar wi)) (encode_table bnd tss Xs)
Proof
  simp[encode_table_def,table_sem_def]>>
  strip_tac>>
  CONJ_TAC >-
    simp[EVERY_FLAT,EVERY_MAP,EVERY_FLAT,Once EVERY_MEM,reify_tuple_eq_sem_reify]>>
  fs[EVERY_MEM]>>first_x_assum drule>>
  strip_tac>> gs[match_row_filter_match]>>
  simp[iconstraint_sem_def,MAP_MAP_o,o_DEF,eval_lin_term_def,reify_avar_def,reify_flag_def]>>
  metis_tac[]
QED

Theorem reify_tuple_eq_sem:
  valid_assignment bnd wi ∧
  wb (INR (Tb Xts)) ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (reify_tuple_eq bnd Xts) ⇒
  EVERY (λ(X,t). varc wi X = t) Xts
Proof
  rw[reify_tuple_eq_def]>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[encode_tuple_eq_sem]>>
  rw[EVERY_MEM]>>
  qpat_x_assum`EVERY _ (FLAT _)` mp_tac>>
  simp[EVERY_FLAT,MAP_MAP_o,o_DEF,EVERY_MAP]>>
  simp[Once EVERY_MEM]>>
  disch_then drule>>
  pairarg_tac>>gvs[]
QED

Theorem encode_table_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_table bnd tss Xs) ⇒
  table_sem tss Xs wi
Proof
  simp[encode_table_def,table_sem_def]>>
  IF_CASES_TAC>>fs[]>>
  rw[]>>
  pop_assum mp_tac>>
  simp[iconstraint_sem_def,MAP_MAP_o,o_DEF,eval_lin_term_def,reify_avar_def,reify_flag_def]>>
  strip_tac>>
  first_assum $ irule_at Any>>
  DEP_REWRITE_TAC [match_row_filter_match]>>
  CONJ_ASM1_TAC
  >- fs[EVERY_MEM]>>
  qpat_x_assum`EVERY _ (FLAT _)` mp_tac>>
  simp[EVERY_FLAT,MAP_MAP_o,o_DEF,EVERY_MAP]>>
  simp[Once EVERY_MEM]>>
  disch_then drule>>
  metis_tac[reify_tuple_eq_sem]
QED

Definition encode_extensional_constr_def:
  encode_extensional_constr bnd c =
  case c of Table tss Xs =>
  encode_table bnd tss Xs
End

Theorem encode_extensional_constr_sem_1:
  valid_assignment bnd wi ∧
  extensional_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar wi))
    (encode_extensional_constr bnd c)
Proof
  Cases_on`c`>>
  rw[encode_extensional_constr_def,extensional_constr_sem_def]>>
  metis_tac[encode_table_sem_1]
QED

Theorem encode_extensional_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_extensional_constr bnd c) ⇒
  extensional_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_extensional_constr_def,extensional_constr_sem_def]>>
  metis_tac[encode_table_sem_2]
QED

(* The reifications needed for tuple eq on a given row *)
Definition cencode_full_eqs_def:
  (cencode_full_eqs bnd [] ec = (Nil,ec)) ∧
  (cencode_full_eqs bnd ((X,t)::Xts) ec =
    let (ys,ec') = cencode_full_eq bnd X t ec in
    let (yss,ec'') = cencode_full_eqs bnd Xts ec' in
    (Append ys yss, ec''))
End

Definition creify_tuple_eq_def:
  creify_tuple_eq bnd Xts pref ec =
  let
    (eqs,ec') = cencode_full_eqs bnd Xts ec;
    tup =
      List (
      mk_annotate [
        (strlit "BIG TODO");
        (strlit "BIG TODO2");
      ]
      (encode_tuple_eq bnd Xts))
  in
    (Append eqs tup, ec')
End

Definition creify_tuple_eqs_def:
  (creify_tuple_eqs bnd [] pref ec = (Nil,ec)) ∧
  (creify_tuple_eqs bnd (x::xs) pref ec =
  let
    (y,ec') = creify_tuple_eq bnd x pref ec;
    (ys,ec'') = creify_tuple_eqs bnd xs pref ec'
  in
    (Append y ys, ec''))
End

Definition cencode_table_def:
  cencode_table bnd tss Xs pref ec =
  let n = LENGTH Xs in
    if EVERY (λYs. LENGTH Ys = n) tss
    then
      let Xtss = MAP (λts. filter_match (ZIP (Xs,ts))) tss in
      let (ys,ec') = creify_tuple_eqs bnd Xtss pref ec in
      (Append ys
        (List
          [(SOME (strlit"BIG TODO 3"), table_ge Xtss)]), ec')
    else
      (List [cfalse_constr],ec)
End

Definition cencode_extensional_constr_def:
  cencode_extensional_constr bnd c pref ec =
  case c of Table tss Xs =>
  cencode_table bnd tss Xs pref ec
End

Theorem cencode_extensional_constr_sem:
  valid_assignment bnd wi ∧
  cencode_extensional_constr bnd c pref ec = (es,ec') ⇒
  enc_rel wi es (encode_extensional_constr bnd c) ec ec'
Proof
  rw[cencode_extensional_constr_def,encode_extensional_constr_def]>>
  gvs[CaseEq"extensional_constr"]>>
  fs[encode_table_def,cencode_table_def]>>
  rw[]>>
  gvs[UNCURRY_EQ]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_List_refl_1>>
  cheat
QED

