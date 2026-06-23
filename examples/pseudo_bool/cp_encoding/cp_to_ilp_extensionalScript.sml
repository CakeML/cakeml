(*
  Formalization of the CP to ILP phase (extensional constraints)
*)
Theory cp_to_ilp_extensional
Libs
  preamble
Ancestors
  pbc pbc_encode cp ilp cp_to_ilp

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
     cat_least_one name «»
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

(* regular (unrolled NFA) *)

(* state-indicator flag: NFA is in state q at position idx *)
Definition reg_state_def[simp]:
  reg_state name idx q = INR (name, Indices [idx; q] (SOME «st»))
End

(* \sum_q st_idx_q = 1 *)
Definition state_idx_row:
  state_idx_row name idx nstates =
  let ls = GENLIST (λq. Pos (reg_state name idx q)) nstates in
  Append
    (cat_least_one name («pos» ^ toString idx) ls)
    (cat_most_one name («pos» ^ toString idx) ls)
End

(* \and_idx \sum_q st_idx_q = 1 *)
Definition state_idx_def:
  state_idx name n nstates =
  flat_app
    (GENLIST (λidx.
      state_idx_row name idx nstates) (n+1))
End

Definition start_state_def:
  init_state name =
  List [
    (SOME (mk_name name «st0»),
      ([],[(1,Pos (reg_state name 0 0))],1))]
End

Definition accept_state_def:
  accept_state name n nstates finals =
  cat_least_one name («st» ^ toString n)
    (MAP (λf. Pos (reg_state name n f))
         (FILTER (λf. f < nstates) finals))
End

(* start, accept, state_idx *)
Definition reg_frame_def:
  reg_frame name nstates n finals =
  Append
    (state_idx name n nstates)
  (Append
    (accept_state name n nstates finals)
    (init_state name))
End

(* successor states of q on reading value v (only valid states < nstates) *)
Definition reg_targets_def:
  reg_targets (nstates:num) trans q v =
  MAP SND (FILTER (λvt. FST vt = v ∧ SND vt < nstates) (nfa_edges trans q))
End

(* transition / forbidding clauses
  For each X (idx) in Xs,
    For each v (vi) in X's values,
      For each state q in nstates,
        state_idx_is_q and X=v ⇒
          al1 ( state_{idx + 1} is q' for q' in transitions q,v ) *)
Definition reg_trans_def:
  reg_trans bnd name nstates trans Xs =
  List (FLAT (MAPi (λidx X.
    FLAT (MAPi (λvi v.
      GENLIST (λq.
        (SOME (mk_name name
          (toString idx ^ «_» ^ toString q ^ «_» ^ toString vi ^ «t»)),
         bits_imply bnd
           [Pos (reg_state name idx q); Pos (INL (Eq X v))]
           (at_least_one
             (MAP (λt. Pos (reg_state name (idx+1) t))
                  (reg_targets nstates trans q v))))
      ) nstates
    ) (domlist bnd X))
  ) Xs))
End

(* the (var,value) pairs over which Eq atoms are reified *)
Definition reg_eq_pairs_def:
  reg_eq_pairs bnd Xs =
  FLAT (MAP (λX. MAP (λv. (X, v)) (domlist bnd X)) Xs)
End

Definition encode_regular_def:
  encode_regular bnd Xs nstates trans finals name =
  let n = LENGTH Xs in
    FLAT (MAP (λ(X,v). encode_full_eq bnd X v) (reg_eq_pairs bnd Xs)) ++
    abstr (reg_frame name nstates n finals) ++
    abstr (reg_trans bnd name nstates trans Xs)
End

Definition cencode_regular_def:
  cencode_regular bnd Xs nstates trans finals name ec =
  let n = LENGTH Xs in
  let (eqs,ec') =
    fold_cenc (λ(X,v) ec. cencode_full_eq bnd X v ec)
      (reg_eq_pairs bnd Xs) ec in
    (Append eqs
      (Append (reg_frame name nstates n finals)
              (reg_trans bnd name nstates trans Xs)), ec')
End

(* --- NFA run theory (crux of regular completeness) --- *)

(* at most one element of a list satisfies P ⇒ the satisfying index is unique *)
Theorem FILTER_LENGTH_le_1_unique:
  ∀ls P i j.
  LENGTH (FILTER P ls) ≤ 1 ∧
  i < LENGTH ls ∧ j < LENGTH ls ∧ P (EL i ls) ∧ P (EL j ls) ⇒ i = j
Proof
  Induct>>rw[]>>
  gvs[FILTER]>>
  Cases_on`P h`>>gvs[]
  >~ [`¬P h`] >- (Cases_on`i`>>Cases_on`j`>>gvs[]>>metis_tac[])>>
  `LENGTH (FILTER P ls) = 0` by (qpat_x_assum`SUC _ ≤ 1` mp_tac>>DECIDE_TAC)>>
  gvs[LENGTH_NIL,FILTER_EQ_NIL,EVERY_EL]>>
  Cases_on`i`>>Cases_on`j`>>gvs[]
QED

Theorem nfa_accepts_lt:
  nfa_accepts trans finals nstates q vs ⇒ q < nstates
Proof
  Cases_on`vs`>>rw[nfa_accepts_def]
QED

(* a witnessing state run implies acceptance (the direction we need) *)
Theorem run_imp_nfa_accepts:
  ∀vs run q.
    LENGTH run = LENGTH vs + 1 ∧ EL 0 run = q ∧
    (∀i. i ≤ LENGTH vs ⇒ EL i run < nstates) ∧
    (∀i. i < LENGTH vs ⇒
       MEM (EL i vs, EL (i+1) run) (nfa_edges trans (EL i run))) ∧
    MEM (EL (LENGTH vs) run) finals ⇒
    nfa_accepts trans finals nstates q vs
Proof
  Induct>>rw[]
  >- (
    gvs[nfa_accepts_def]>>
    qpat_x_assum`∀i. i ≤ _ ⇒ _`(qspec_then`0` mp_tac)>>
    simp[])>>
  simp[nfa_accepts_def]>>
  conj_asm1_tac
  >- (qpat_x_assum`∀i. i ≤ _ ⇒ _`(qspec_then`0` mp_tac)>>simp[])>>
  qexists_tac`EL 1 run`>>
  conj_tac
  >- (qpat_x_assum`∀i. i < _ ⇒ MEM _ _`(qspec_then`0` mp_tac)>>simp[GSYM ADD1])>>
  last_x_assum irule>>
  qexists_tac`DROP 1 run`>>
  `1 ≤ LENGTH run` by simp[]>>
  rw[EL_DROP,LENGTH_DROP]
  >~ [`MEM (_,_) _`]
  >- (
    qpat_x_assum`∀i. i < _ ⇒ MEM _ _`(qspec_then`i+1` mp_tac)>>impl_tac
    >- simp[]>>
    `EL (i+1) (h::vs) = EL i vs` by simp[GSYM ADD1,EL]>>
    `i + 1 + 1 = i + 2` by simp[]>>
    simp[])>>
  qpat_x_assum`MEM _ finals`mp_tac>>simp[ADD1]
QED

Theorem regular_sem_imp_nfa:
  regular_sem Xs nstates trans finals w ⇒
  nfa_accepts trans finals nstates 0 (MAP (varc w) Xs)
Proof
  rw[regular_sem_def]
QED

(* the canonical run stays accepting (the key invariant) *)
Theorem nfa_run_invariant:
  nfa_accepts trans finals nstates 0 as ⇒
  ∀i. i ≤ LENGTH as ⇒
    nfa_run trans finals nstates as i < nstates ∧
    nfa_accepts trans finals nstates
      (nfa_run trans finals nstates as i)
      (DROP i as)
Proof
  strip_tac>>
  Induct>>rw[]
  >- (simp[nfa_run_def]>>metis_tac[nfa_accepts_lt])
  >- simp[nfa_run_def]
  >- (
    `i < LENGTH as` by gvs[]>>
    fs[]>>
    `DROP i as = EL i as :: DROP (SUC i) as` by
      (irule DROP_CONS_EL>>simp[])>>
    fs[Once nfa_accepts_def]>>
    simp[nfa_run_def]>>
    SELECT_ELIM_TAC>>rw[]
    >- metis_tac[]>>
    metis_tac[nfa_accepts_lt])
  >- (
    `i < LENGTH as` by gvs[]>>
    fs[]>>
    `DROP i as = EL i as :: DROP (SUC i) as` by
      (irule DROP_CONS_EL>>simp[])>>
    fs[Once nfa_accepts_def]>>
    simp[nfa_run_def]>>
    SELECT_ELIM_TAC>>rw[]>>
    metis_tac[])
QED

Theorem nfa_run_accepts:
  nfa_accepts trans finals nstates 0 as ⇒
  nfa_run trans finals nstates as 0 = 0 ∧
  (∀i. i ≤ LENGTH as ⇒ nfa_run trans finals nstates as i < nstates) ∧
  (∀i. i < LENGTH as ⇒
    MEM (EL i as, nfa_run trans finals nstates as (i+1))
        (nfa_edges trans (nfa_run trans finals nstates as i))) ∧
  MEM (nfa_run trans finals nstates as (LENGTH as)) finals
Proof
  strip_tac>>
  drule nfa_run_invariant>>strip_tac>>
  rw[]
  >- simp[nfa_run_def]
  >- (
    `i ≤ LENGTH as` by gvs[]>>
    first_x_assum drule>>strip_tac>>
    `DROP i as = EL i as :: DROP (SUC i) as` by
      (irule DROP_CONS_EL>>simp[])>>
    fs[Once nfa_accepts_def]>>
    simp[GSYM ADD1,nfa_run_def]>>
    SELECT_ELIM_TAC>>rw[]>>
    metis_tac[])
  >- (
    `LENGTH as ≤ LENGTH as` by simp[]>>
    first_x_assum drule>>strip_tac>>
    `DROP (LENGTH as) as = []` by
      simp[DROP_LENGTH_TOO_LONG]>>
    gvs[Once nfa_accepts_def])
QED

(* exactly the run-state column is true ⇒ at most one is *)
Theorem iSUM_GENLIST_b2i_eq:
  ∀n c. iSUM (GENLIST (λq. b2i (c = q)) n) = if c < n then 1 else 0
Proof
  Induct>>
  gvs[GENLIST,SNOC_APPEND,iSUM_APPEND,iSUM_def]>>
  rw[oneline b2i_def]>>gvs[]>>
  intLib.ARITH_TAC
QED

(* --- semantics of the transition clauses --- *)
Theorem reg_trans_sem:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (reg_trans bnd name nstates trans Xs)) ⇔
  ∀idx q v.
    idx < LENGTH Xs ∧ q < nstates ∧ MEM v (domlist bnd (EL idx Xs)) ⇒
    (wb (reg_state name idx q) ∧ wb (INL (Eq (EL idx Xs) v)) ⇒
     ∃t. MEM t (reg_targets nstates trans q v) ∧ wb (reg_state name (idx+1) t)))
Proof
  strip_tac>>
  simp[reg_trans_def,append_thm,EVERY_MAP,EVERY_MEM,MEM_FLAT,
    MEM_MAPi,MEM_GENLIST,PULL_EXISTS]>>
  simp[bits_imply_sem,at_least_one_sem,MEM_MAP,PULL_EXISTS]>>
  eq_tac>>rw[]>>
  gvs[MEM_EL]>>
  metis_tac[MEM_EL]
QED

Theorem encode_full_eq_reify:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi)) (encode_full_eq bnd X v)
Proof
  rw[]>>
  DEP_REWRITE_TAC[encode_full_eq_sem]>>
  simp[reify_avar_def,reify_reif_def]
QED

Theorem MEM_reg_targets:
  MEM t (reg_targets nstates trans q v) ⇔ MEM (v,t) (nfa_edges trans q) ∧ t < nstates
Proof
  rw[reg_targets_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]>>
  metis_tac[]
QED

Theorem encode_full_eqs_reify:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (FLAT (MAP (λ(X,v). encode_full_eq bnd X v) l))
Proof
  strip_tac>>Induct_on`l`>>rw[]>>
  PairCases_on`h`>>gvs[]>>
  simp[reify_avar_def,reify_reif_def]
QED

(* --- semantics of the frame (one-hot + start + accept) --- *)
Theorem reg_frame_sem:
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstr (reg_frame name nstates n finals)) ⇔
  (∀idx. idx ≤ n ⇒
     (∃q. q < nstates ∧ wb (reg_state name idx q)) ∧
     iSUM (MAP (b2i o lit wb)
       (GENLIST (λq. Pos (reg_state name idx q)) nstates)) ≤ 1) ∧
  wb (reg_state name 0 0) ∧
  (∃f. MEM f finals ∧ f < nstates ∧ wb (reg_state name n f))
Proof
  simp[reg_frame_def,state_idx_def,state_idx_row,accept_state_def,
    start_state_def,append_thm,EVERY_APPEND,EVERY_FLAT,EVERY_GENLIST,
    MAP_GENLIST,PULL_EXISTS]>>
  simp[MEM_GENLIST,MEM_MAP,MEM_FILTER,lit_def,arithmeticTheory.LE_LT1,
    PULL_EXISTS]>>
  simp[iconstraint_sem_def,eval_lin_term_def,iSUM_def,b2i_def]>>
  `∀x. b2i x ≥ 1 ⇔ x` by (Cases>>simp[b2i_def])>>simp[]>>
  metis_tac[]
QED

Theorem encode_regular_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Extensional (Regular Xs nstates trans finals)) ∧
  regular_sem Xs nstates trans finals wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_regular bnd Xs nstates trans finals name)
Proof
  rw[encode_regular_def,EVERY_APPEND]
  >- (irule encode_full_eqs_reify>>simp[])
  >- (
    gvs[regular_sem_def]>>
    drule nfa_run_accepts>>strip_tac>>
    simp[reg_frame_sem,reify_avar_def,reify_flag_def]>>
    rw[]>>
    simp[MAP_GENLIST,combinTheory.o_DEF]>>
    gvs[reify_avar_def,reify_flag_def]>>
    simp[iSUM_GENLIST_b2i_eq])
  >- (
    gvs[regular_sem_def]>>
    drule nfa_run_accepts>>strip_tac>>
    simp[reg_trans_sem,reify_avar_def,reify_flag_def]>>
    rw[]>>
    gvs[reify_reif_def]>>
    simp[MEM_reg_targets]>>
    first_x_assum drule>>gvs[EL_MAP])
QED

Theorem MEM_reg_eq_pairs:
  idx < LENGTH Xs ∧ MEM v (domlist bnd (EL idx Xs)) ⇒
  MEM (EL idx Xs, v) (reg_eq_pairs bnd Xs)
Proof
  rw[reg_eq_pairs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]>>
  metis_tac[EL_MEM]
QED

Theorem encode_full_eqs_sem_2:
  ∀l.
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (FLAT (MAP (λ(X,v). encode_full_eq bnd X v) l)) ⇒
  ∀X v. MEM (X,v) l ⇒ (wb (INL (Eq X v)) ⇔ varc wi X = v)
Proof
  Induct>>rw[]>>gvs[]
QED

Theorem reg_onehot_unique:
  iSUM (MAP (b2i o lit wb)
    (GENLIST (λq. Pos (reg_state name idx q)) nstates)) ≤ 1 ∧
  q1 < nstates ∧ q2 < nstates ∧
  wb (reg_state name idx q1) ∧ wb (reg_state name idx q2) ⇒ q1 = q2
Proof
  rw[]>>
  `LENGTH (FILTER (lit wb)
    (GENLIST (λq. Pos (reg_state name idx q)) nstates)) ≤ 1` by
    (gvs[iSUM_FILTER])>>
  drule FILTER_LENGTH_le_1_unique>>
  disch_then (qspecl_then[`q1`,`q2`] mp_tac)>>
  simp[EL_GENLIST]
QED

Theorem encode_regular_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_regular bnd Xs nstates trans finals name) ⇒
  regular_sem Xs nstates trans finals wi
Proof
  rw[encode_regular_def,EVERY_APPEND]>>
  qpat_x_assum`EVERY _ (abstr (reg_frame _ _ _ _))` mp_tac>>
  simp[reg_frame_sem]>>strip_tac>>
  qpat_x_assum`EVERY _ (abstr (reg_trans _ _ _ _ _))` mp_tac>>
  simp[reg_trans_sem]>>strip_tac>>
  `∀X v. MEM (X,v) (reg_eq_pairs bnd Xs) ⇒
     (wb (INL (Eq X v)) ⇔ varc wi X = v)` by
    metis_tac[encode_full_eqs_sem_2]>>
  (* the canonical chosen state per row *)
  qabbrev_tac`run = λidx. @q. q < nstates ∧ wb (reg_state name idx q)`>>
  `∀idx. idx ≤ LENGTH Xs ⇒
     run idx < nstates ∧ wb (reg_state name idx (run idx))` by (
    rw[Abbr`run`]>>
    SELECT_ELIM_TAC>>
    metis_tac[])>>
  `∀idx q. idx ≤ LENGTH Xs ∧ q < nstates ∧ wb (reg_state name idx q) ⇒
     q = run idx` by (
    rw[]>>
    `run idx < nstates ∧ wb (reg_state name idx (run idx))` by
      (first_x_assum irule>>gvs[])>>
    `iSUM (MAP (b2i o lit wb)
       (GENLIST (λq. Pos (reg_state name idx q)) nstates)) ≤ 1` by
      (last_x_assum drule>>simp[])>>
    metis_tac[reg_onehot_unique, reg_state_def])>>
  `0 < nstates` by (
    `run 0 < nstates ∧ wb (reg_state name 0 (run 0))` by (first_x_assum irule>>simp[])>>
    intLib.ARITH_TAC)>>
  simp[regular_sem_def]>>
  irule run_imp_nfa_accepts>>
  qexists_tac`GENLIST run (LENGTH Xs + 1)`>>
  rw[EL_GENLIST]
  >- (
    `MEM (EL i Xs, varc wi (EL i Xs)) (reg_eq_pairs bnd Xs)` by
      (irule MEM_reg_eq_pairs>>simp[MEM_domlist])>>
    `wb (INL (Eq (EL i Xs) (varc wi (EL i Xs))))` by metis_tac[]>>
    `MEM (varc wi (EL i Xs)) (domlist bnd (EL i Xs))` by simp[MEM_domlist]>>
    `run i < nstates` by (first_x_assum drule>>simp[])>>
    last_x_assum (qspecl_then[`i`,`run i`,`varc wi (EL i Xs)`] mp_tac)>>
    impl_tac >- gvs[]>>
    strip_tac>>
    gvs[MEM_reg_targets,EL_MAP]>>
    `t = run (i + 1)` by (first_x_assum irule>>gvs[ADD1])>>
    gvs[])
  >- (
    `f = run (LENGTH Xs)` by (first_x_assum irule>>gvs[])>>
    gvs[])
QED

Theorem cencode_regular_sem:
  valid_assignment bnd wi ∧
  cencode_regular bnd Xs nstates trans finals name ec = (es,ec') ⇒
  enc_rel wi es (encode_regular bnd Xs nstates trans finals name) ec ec'
Proof
  rw[cencode_regular_def,encode_regular_def]>>
  gvs[UNCURRY_EQ]>>
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_Append>>
  irule_at Any enc_rel_abstr>>
  irule_at Any enc_rel_abstr>>
  irule_at Any enc_rel_fold_cenc>>
  first_x_assum (irule_at Any)>>
  rw[]>>
  PairCases_on‘h’>>gvs[enc_rel_encode_full_eq]
QED

Definition encode_extensional_constr_def:
  encode_extensional_constr bnd c name =
  case c of
    Table tss Xs => encode_table bnd tss Xs name
  | Regular Xs nstates trans finals =>
      encode_regular bnd Xs nstates trans finals name
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
  metis_tac[encode_table_sem_1,encode_regular_sem_1]
QED

Theorem encode_extensional_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_extensional_constr bnd c name) ⇒
  extensional_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_extensional_constr_def,extensional_constr_sem_def]>>
  metis_tac[encode_table_sem_2,encode_regular_sem_2]
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
  case c of
    Table tss Xs => cencode_table bnd tss Xs name ec
  | Regular Xs nstates trans finals =>
      cencode_regular bnd Xs nstates trans finals name ec
End

Theorem cencode_extensional_constr_sem:
  valid_assignment bnd wi ∧
  cencode_extensional_constr bnd c name ec = (es,ec') ⇒
  enc_rel wi es (encode_extensional_constr bnd c name) ec ec'
Proof
  rw[cencode_extensional_constr_def,encode_extensional_constr_def]>>
  gvs[CaseEq"extensional_constr"]
  >- (
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
    gvs[enc_rel_encode_full_eq])>>
  metis_tac[cencode_regular_sem]
QED

(*
EVAL``append o FST $ cencode_extensional_constr
  (\x. (-5,5))
  (Table [[SOME 1i;SOME 2i];[NONE;NONE];[SOME 1i;NONE];] [INL («x»);INL («y»)]) («t1») init_ec``
*)


