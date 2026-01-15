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
Definition cencode_tuple_eq_def:
  cencode_tuple_eq bnd Xts name n =
    cbimply_var bnd (INR (Index name n))
      ([],
      MAP (λ(X,t). (1i, Pos (INL (Eq X t)))) Xts,
      &LENGTH Xts)
End

Theorem encode_tuple_eq_sem:
  valid_assignment bnd wi ∧
  EVERY (λ(X,t). wb (INL (Eq X t)) ⇔ varc wi X = t) Xts
  ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (cencode_tuple_eq bnd Xts name n)) ⇔
  (wb (INR (Index name n)) ⇔ EVERY (λ(X,t). varc wi X = t) Xts))
Proof
  rw[cencode_tuple_eq_def,iconstraint_sem_def]>>
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

(* The reifications needed for tuple eq on a given row *)
Definition reify_tuple_eq_def:
  reify_tuple_eq bnd Xts name n =
  let
    eqs = FLAT $ MAP (λ(X,t). encode_full_eq bnd X t) Xts;
  in
    eqs ++ abstr (cencode_tuple_eq bnd Xts name n)
End

Definition ctable_al1_def[simp]:
  ctable_al1 Xtss name =
     cat_least_one name
      (MAPi (λn Xts. (Pos (INR (Index name n)))) Xtss)
End

Definition encode_table_def:
  encode_table bnd tss Xs name =
  let n = LENGTH Xs in
    if EVERY (λYs. LENGTH Ys = n) tss
    then
      let Xtss = MAP (λts. filter_match (ZIP (Xs,ts))) tss in
      (FLAT $ MAPi (λn Xts. reify_tuple_eq bnd Xts name n) Xtss) ++
      abstr (ctable_al1 Xtss name)
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
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Extensional (Table tss Xs)) ∧
  n < LENGTH tss ∧
  LENGTH (EL n tss) = LENGTH Xs ∧
  Xts = filter_match (ZIP (Xs,EL n tss)) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi)) (abstr (cencode_tuple_eq bnd Xts name n))
Proof
  rw[cencode_tuple_eq_def,reify_avar_def,reify_flag_def]>>
  simp[iconstraint_sem_def,eval_lin_term_def,iterateTheory.LAMBDA_PAIR,
    reify_avar_def,reify_reif_def,MAP_MAP_o,o_DEF,
    match_row_filter_match,EVERY_MEM]
QED

Theorem reify_tuple_eq_sem_reify:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Extensional (Table tss Xs)) ∧
  n < LENGTH tss ∧
  LENGTH (EL n tss) = LENGTH Xs ∧
  Xts = filter_match (ZIP (Xs,EL n tss))
  ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (reify_tuple_eq bnd Xts name n)
Proof
  rw[reify_tuple_eq_def]>>
  simp[EVERY_FLAT]
  >-
    simp[Once EVERY_MEM,MEM_MAP,PULL_EXISTS,iterateTheory.LAMBDA_PAIR,reify_avar_def,reify_reif_def]>>
  irule encode_tuple_eq_sem_reify>>
  simp[]
QED

Theorem encode_table_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Extensional (Table tss Xs)) ∧
  table_sem tss Xs wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_table bnd tss Xs name)
Proof
  simp[encode_table_def,table_sem_def]>>
  strip_tac>>
  CONJ_TAC >- (
    simp[EVERY_FLAT,Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,EL_MAP]>>
    rw[]>>
    irule reify_tuple_eq_sem_reify>>simp[]>>
    fs[EVERY_MEM]>>metis_tac[MEM_EL])>>
  fs[EVERY_MEM]>>first_x_assum drule>>
  strip_tac>>
  simp[MEM_MAPi,PULL_EXISTS,reify_avar_def,reify_flag_def]>>
  qpat_x_assum`MEM _ _` mp_tac>>
  simp[Once MEM_EL]>>rw[]>>
  qexists_tac`n`>>
  simp[MEM_enumerate]
QED

Theorem reify_tuple_eq_sem:
  valid_assignment bnd wi ∧
  wb (INR (Index name n)) ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (reify_tuple_eq bnd Xts name n) ⇒
  EVERY (λ(X,t). varc wi X = t) Xts
Proof
  rw[reify_tuple_eq_def]>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[encode_tuple_eq_sem]>>
  rw[EVERY_MEM]>>
  qpat_x_assum`EVERY _ (FLAT _)` mp_tac>>
  simp[EVERY_FLAT,Once EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
  simp[iterateTheory.LAMBDA_PAIR]>>
  metis_tac[MEM_EL]
QED

Theorem MEM_enumerate_IMP':
  ∀ls k.
  MEM (i,e) (enumerate k ls) ⇒
  MEM e ls ∧ k ≤ i ∧ i < k + LENGTH ls
Proof
  Induct>>
  rw[miscTheory.enumerate_def]>>
  fs[ADD1]>>
  first_x_assum drule>>
  simp[]
QED

Theorem MEM_enumerate_0:
  MEM (i,e) (enumerate 0 ls) ⇒
  EL i ls = e ∧ i < LENGTH ls
Proof
  rw[]>>
  drule MEM_enumerate_IMP'>>
  simp[]>>
  metis_tac[MEM_enumerate]
QED

Theorem encode_table_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_table bnd tss Xs name) ⇒
  table_sem tss Xs wi
Proof
  simp[encode_table_def,table_sem_def]>>
  IF_CASES_TAC>>fs[]>>
  rw[]>>
  gvs[MEM_MAPi]>>
  qexists_tac`EL n tss`>>
  simp[MEM_EL,PULL_EXISTS]>>
  first_assum $ irule_at Any>>
  DEP_REWRITE_TAC [match_row_filter_match]>>
  CONJ_ASM1_TAC
  >- (
    fs[EVERY_MEM]>>
    metis_tac[MEM_EL])>>
  drule_at (Pos (el 2)) reify_tuple_eq_sem>>
  disch_then (drule_then irule)>>
  qpat_x_assum`EVERY _ (FLAT _)` mp_tac>>
  simp[EVERY_FLAT,Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,EL_MAP]
QED

Definition encode_extensional_constr_def:
  encode_extensional_constr bnd c name =
  case c of Table tss Xs =>
  encode_table bnd tss Xs name
End

Theorem encode_extensional_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Extensional c) ∧
  extensional_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_extensional_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_extensional_constr_def,extensional_constr_sem_def]>>
  metis_tac[encode_table_sem_1]
QED

Theorem encode_extensional_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_extensional_constr bnd c name) ⇒
  extensional_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_extensional_constr_def,extensional_constr_sem_def]>>
  metis_tac[encode_table_sem_2]
QED

(* The reifications needed for tuple eq on a given row *)
Definition cencode_full_eqs_def:
  cencode_full_eqs bnd xs ec =
    fold_cenc
      (λXt ec. cencode_full_eq bnd (FST Xt) (SND Xt) ec) xs ec
End

Definition creify_tuple_eq_def:
  creify_tuple_eq bnd Xts name n ec =
  let
    (eqs,ec') = cencode_full_eqs bnd Xts ec;
  in
    (Append eqs
      (cencode_tuple_eq bnd Xts name n), ec')
End

Definition creify_tuple_eqs_def:
  creify_tuple_eqs bnd name nXtss ec =
  fold_cenc
    (λ(n,Xts) ec. creify_tuple_eq bnd Xts name n ec) nXtss ec
End

Definition cencode_table_def:
  cencode_table bnd tss Xs name ec =
  let n = LENGTH Xs in
    if EVERY (λYs. LENGTH Ys = n) tss
    then
      let Xtss = MAP (λts. filter_match (ZIP (Xs,ts))) tss in
      let nXtss = enumerate 0 Xtss in
      let (ys,ec') = creify_tuple_eqs bnd name nXtss ec in
      (Append ys (ctable_al1 Xtss name), ec')
    else
      (cfalse_constr, ec)
End

Definition cencode_extensional_constr_def:
  cencode_extensional_constr bnd c name ec =
  case c of Table tss Xs =>
  cencode_table bnd tss Xs name ec
End

Theorem cencode_extensional_constr_sem:
  valid_assignment bnd wi ∧
  cencode_extensional_constr bnd c name ec = (es,ec') ⇒
  enc_rel wi es (encode_extensional_constr bnd c name) ec ec'
Proof
  rw[cencode_extensional_constr_def,encode_extensional_constr_def]>>
  gvs[CaseEq"extensional_constr"]>>
  fs[encode_table_def,cencode_table_def]>>
  rw[]>>gvs[UNCURRY_EQ]>>
  irule enc_rel_Append>>
  irule_at (Pos (el 2)) enc_rel_abstr_cong>>
  simp[MAPi_enumerate_MAP]>>
  irule_at Any enc_rel_fold_cenc>>
  fs[creify_tuple_eqs_def]>>
  first_x_assum (irule_at Any)>>
  rw[]>>
  pairarg_tac>>
  gvs[creify_tuple_eq_def,reify_tuple_eq_def]>>
  pairarg_tac>>gvs[]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_abstr>>
  irule_at Any enc_rel_fold_cenc>>
  fs[cencode_full_eqs_def]>>
  first_x_assum (irule_at Any)>>
  rw[]>>
  pairarg_tac>>
  gvs[enc_rel_encode_full_eq]
QED

(*
EVAL``append o FST $ cencode_extensional_constr
  (\x. (-5,5))
  (Table [[SOME 1i;SOME 2i];[NONE;NONE];[SOME 1i;NONE];] [INL (strlit "x");INL (strlit "y")]) (strlit"t1") init_ec``
*)


