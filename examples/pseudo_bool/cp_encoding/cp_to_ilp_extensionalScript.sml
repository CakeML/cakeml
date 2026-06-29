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

(* NegativeTable: dual of Table. For each forbidden tuple, one forbidding
   clause Σ [X_i ≠ t_i] ≥ 1 over the concrete positions; no selector. *)

(* one forbidden tuple: define the Eq atoms, then the forbidding clause *)
Definition encode_neg_tuple_def:
  encode_neg_tuple bnd Xts name n =
    (FLAT $ MAP (λ(X,t). encode_full_eq bnd X t) Xts) ++
    abstr (cat_least_one name (toString n)
      (MAP (λ(X,t). Neg (INL (Eq X t))) Xts))
End

Definition encode_negative_table_def:
  encode_negative_table bnd tss Xs name =
  let n = LENGTH Xs in
    if EVERY (λYs. LENGTH Ys = n) tss
    then
      let Xtss = MAP (λts. filter_match (ZIP (Xs,ts))) tss in
      FLAT $ MAPi (λn Xts. encode_neg_tuple bnd Xts name n) Xtss
    else
      [false_constr]
End

(* one forbidden tuple holds (under reify) iff it is NOT matched *)
Theorem encode_neg_tuple_reify:
  valid_assignment bnd wi ∧
  ¬ EVERY (λ(X,t). varc wi X = t) Xts ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_neg_tuple bnd Xts name n)
Proof
  rw[encode_neg_tuple_def,EVERY_APPEND]
  >- (irule encode_full_eqs_reify>>simp[])>>
  simp[abstr_cat_least_one,at_least_one_sem,MEM_MAP,PULL_EXISTS]>>
  fs[NOT_EVERY,EXISTS_MEM,EXISTS_PROD]>>
  first_x_assum $ irule_at Any>>
  simp[reify_avar_def,reify_reif_def,lit_def]
QED

Theorem encode_negative_table_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Extensional (NegativeTable tss Xs)) ∧
  negative_table_sem tss Xs wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_negative_table bnd tss Xs name)
Proof
  simp[encode_negative_table_def,negative_table_sem_def]>>
  strip_tac>>
  simp[EVERY_FLAT,Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,EL_MAP]>>
  rw[]>>
  `LENGTH (EL n tss) = LENGTH Xs` by (fs[EVERY_MEM]>>metis_tac[MEM_EL])>>
  `¬EVERY (λ(X,t). varc wi X = t) (filter_match (ZIP (Xs, EL n tss)))` by (
    DEP_REWRITE_TAC[GSYM match_row_filter_match]>>simp[]>>metis_tac[MEM_EL])>>
  irule encode_neg_tuple_reify>>
  simp[]>>fs[]
QED

(* one forbidden tuple's clauses force it to be NOT matched *)
Theorem encode_neg_tuple_sem:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_neg_tuple bnd Xts name n) ⇒
  ¬ EVERY (λ(X,t). varc wi X = t) Xts
Proof
  simp[encode_neg_tuple_def,EVERY_APPEND]>>strip_tac>>
  `∀X t. MEM (X,t) Xts ⇒ (wb (INL (Eq X t)) ⇔ varc wi X = t)` by
    metis_tac[encode_full_eqs_sem_2]>>
  gvs[MEM_MAP]>>pairarg_tac>>gvs[lit_def]>>
  simp[EXISTS_MEM,EXISTS_PROD]>>metis_tac[]
QED

Theorem encode_negative_table_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_negative_table bnd tss Xs name) ⇒
  negative_table_sem tss Xs wi
Proof
  simp[encode_negative_table_def,negative_table_sem_def]>>IF_CASES_TAC>>simp[]>>
  strip_tac>>rw[]>>
  `LENGTH ts = LENGTH Xs` by fs[EVERY_MEM]>>
  DEP_REWRITE_TAC[match_row_filter_match]>>simp[]>>
  gvs[MEM_EL]>>
  qpat_x_assum`EVERY _ (FLAT _)` mp_tac>>
  simp[EVERY_FLAT,Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,EL_MAP]>>
  strip_tac>>
  first_x_assum drule>>strip_tac>>
  drule_all encode_neg_tuple_sem>>simp[]
QED

(* SmartTable: per row a selector flag, ⇔ all entries hold; at_least_one row.
   Entry indicator: var-vs-const reuses reif_gen (shared Eq/Ge atoms, no flag);
   var-vs-var uses fresh flags sgt/slt (orderings) (+ seq for =/≠); a set entry
   uses a membership flag sset. *)

(* the "this entry holds" indicator literal for entry j of row k *)
Definition smart_entry_lit_def:
  smart_entry_lit name k j e =
  case e of
    SCmp v1 cmp v2 =>
      (case v2 of
        INR c => reif_gen (v1,cmp,c)
      | INL _ =>
        (case cmp of
          GreaterThan  => Pos (INR (name, Indices [k;j] (SOME «sgt»)))
        | LessEqual    => Neg (INR (name, Indices [k;j] (SOME «sgt»)))
        | LessThan     => Pos (INR (name, Indices [k;j] (SOME «slt»)))
        | GreaterEqual => Neg (INR (name, Indices [k;j] (SOME «slt»)))
        | Equal        => Pos (INR (name, Indices [k;j] (SOME «seq»)))
        | NotEqual     => Neg (INR (name, Indices [k;j] (SOME «seq»)))))
  | SSet v b vs =>
      if b then Pos (INR (name, Indices [k;j] (SOME «sset»)))
      else      Neg (INR (name, Indices [k;j] (SOME «sset»)))
End

(* defining constraints for entry j of row k *)
Definition encode_smart_entry_def:
  encode_smart_entry bnd name k j e =
  case e of
    SCmp v1 cmp v2 =>
      (case v2 of
        INR c => encode_reif_gen bnd (v1,cmp,c)
      | INL _ =>
        let
          fgt = INR (name, Indices [k;j] (SOME «sgt»));
          flt = INR (name, Indices [k;j] (SOME «slt»));
          feq = INR (name, Indices [k;j] (SOME «seq»))
        in
        (case cmp of
          GreaterThan  => abstr (cbimply_var bnd fgt (mk_gt v1 v2))
        | LessEqual    => abstr (cbimply_var bnd fgt (mk_gt v1 v2))
        | LessThan     => abstr (cbimply_var bnd flt (mk_lt v1 v2))
        | GreaterEqual => abstr (cbimply_var bnd flt (mk_lt v1 v2))
        | Equal =>
            abstr (cbimply_var bnd fgt (mk_gt v1 v2)) ++
            abstr (cbimply_var bnd flt (mk_lt v1 v2)) ++
            abstr (cbimply_var bnd feq ([],[(1,Neg fgt);(1,Neg flt)],2))
        | NotEqual =>
            abstr (cbimply_var bnd fgt (mk_gt v1 v2)) ++
            abstr (cbimply_var bnd flt (mk_lt v1 v2)) ++
            abstr (cbimply_var bnd feq ([],[(1,Neg fgt);(1,Neg flt)],2))))
  | SSet v b vs =>
      let fset = INR (name, Indices [k;j] (SOME «sset»)) in
      FLAT (MAP (λc. encode_full_eq bnd v c) vs) ++
      abstr (cbimply_var bnd fset
        (at_least_one (MAP (λc. Pos (INL (Eq v c))) vs)))
End

(* one row: entry defs, then selector ⇔ (all indicators hold) *)
Definition encode_smart_row_def:
  encode_smart_row bnd name k es =
  let lits = MAPi (λj e. smart_entry_lit name k j e) es in
  FLAT (MAPi (λj e. encode_smart_entry bnd name k j e) es) ++
  abstr (cbimply_var bnd (INR (Index name k))
    ([], MAP (λl. (1,l)) lits, &LENGTH es))
End

Definition encode_smart_table_def:
  encode_smart_table bnd rows name =
  FLAT (MAPi (λk es. encode_smart_row bnd name k es) rows) ++
  abstr (cat_least_one name «»
    (MAPi (λk es. Pos (INR (Index name k))) rows))
End

(* one entry's indicator reflects whether the entry holds *)
Theorem smart_entry_lit_sem:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_smart_entry bnd name k j e) ⇒
  (lit wb (smart_entry_lit name k j e) ⇔ smart_entry_holds e wi)
Proof
  strip_tac>>
  Cases_on`e`
  >- (
    simp[encode_smart_entry_def,smart_entry_lit_def,smart_entry_holds_def]>>
    Cases_on`s0`>>simp[]
    >- (
      Cases_on`c`>>
      gvs[encode_smart_entry_def,abstr_cbimply_var,EVERY_REVERSE,EVERY_APPEND,
          lit_def,cmpop_val_def]>>
      rpt strip_tac>>
      rpt(qpat_x_assum`_ ⇔ wb _`(assume_tac o GSYM))>>
      gvs[]>>
      intLib.ARITH_TAC)>>
    fs[encode_smart_entry_def]>>gvs[encode_reif_gen_sem,varc_def])
  >- (
    simp[smart_entry_lit_def,smart_entry_holds_def]>>
    fs[encode_smart_entry_def,EVERY_APPEND,abstr_cbimply_var,EVERY_REVERSE]>>
    gvs[EVERY_FLAT,EVERY_MAP]>>
    qpat_x_assum`_ ⇔ wb _`(assume_tac o GSYM)>>
    Cases_on`b`>>
    gvs[lit_def,MEM_MAP,PULL_EXISTS]>>
    fs[EVERY_MEM]>>metis_tac[])
QED

(* the entry defs hold under the proof-only reified assignment *)
Theorem encode_reif_gen_reify:
  valid_assignment bnd wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_reif_gen bnd (Z,cmp,v))
Proof
  rw[]>>
  DEP_REWRITE_TAC[encode_reif_gen_sem]>>
  simp[lit_reify_avar_reif_gen,reify_avar_def,reify_reif_def]
QED

(* The reify-direction proofs need from the constraint store only that the
   flags read back as reify_smart_flag of the rows.  Abstract that as a hook. *)
Definition smart_reify_def:
  smart_reify cs wi name rows ⇔
    ∀ids ann. reify_flag cs wi (name, Indices ids ann) =
              reify_smart_flag rows wi ids ann
End

Theorem smart_reify_SmartTable[local]:
  ALOOKUP cs name = SOME (Extensional (SmartTable rows)) ⇒
  smart_reify cs wi name rows
Proof
  rw[smart_reify_def,reify_flag_def]
QED

Theorem smart_entry_reify:
  valid_assignment bnd wi ∧
  smart_reify cs wi name rows ∧
  k < LENGTH rows ∧ j < LENGTH (EL k rows) ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_smart_entry bnd name k j (EL j (EL k rows)))
Proof
  strip_tac>>
  Cases_on`EL j (EL k rows)`
  >- (
    simp[encode_smart_entry_def]>>
    Cases_on`s0`
    >- (
      simp[]>>Cases_on`c`>>
      gs[EVERY_REVERSE,EVERY_APPEND]>>
      gs[smart_reify_def,reify_avar_def,reify_smart_flag_def]>>
      intLib.ARITH_TAC)>>
    simp[]>>irule encode_reif_gen_reify>>simp[])
  >- (
    simp[encode_smart_entry_def,EVERY_APPEND]>>
    conj_tac >- simp[EVERY_FLAT,EVERY_MAP,encode_full_eq_reify]>>
    simp[abstr_cbimply_var,EVERY_REVERSE,at_least_one_sem,MEM_MAP,PULL_EXISTS,lit_def]>>
    gs[smart_reify_def,reify_avar_def,reify_smart_flag_def,reify_reif_def])
QED

(* Σ indicators ≥ len ⇔ all indicators hold *)
Theorem iconstraint_all_lits[local]:
  iconstraint_sem ([], MAP (λl. (1i,l)) ls, &LENGTH ls) (wi,wb) ⇔
  EVERY (lit wb) ls
Proof
  simp[iconstraint_sem_def,eval_ilin_term_def,eval_lin_term_def,iSUM_def,
       MAP_MAP_o,o_DEF,EVERY_MEM]
QED

(* Σ_j [g j holds] ≥ len ⇔ every indexed indicator holds *)
Theorem eval_lin_term_MAPi_ge_LENGTH[local]:
  eval_lin_term wb (MAPi (λj e. (1i, g j e)) es) ≥ &LENGTH es ⇔
  (∀j. j < LENGTH es ⇒ lit wb (g j (EL j es)))
Proof
  simp[eval_lin_term_def,eval_term_def,eval_lit_def,MAPi_enumerate_MAP,
       MAP_MAP_o,o_DEF,integerTheory.INT_MUL_LID]>>
  `&LENGTH es = &LENGTH (enumerate 0 es)` by simp[LENGTH_enumerate]>>
  pop_assum SUBST1_TAC>>
  simp[pairTheory.ELIM_UNCURRY,iSUM_MAP_b2i_ge_LENGTH,MEM_enumerate,
       PULL_EXISTS,FORALL_PROD]>>
  metis_tac[MEM_enumerate,MEM_enumerate_0]
QED

(* selector ⇔ all entries of the row hold *)
Theorem encode_smart_row_sem:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_smart_row bnd name k es) ⇒
  (wb (INR (Index name k)) ⇔ EVERY (λe. smart_entry_holds e wi) es)
Proof
  simp[encode_smart_row_def,EVERY_APPEND,abstr_cbimply_var,EVERY_REVERSE]>>
  strip_tac>>
  qpat_x_assum`EVERY _ (bimply_bit _ _ _)` mp_tac>>simp[o_DEF]>>strip_tac>>
  `∀j. j < LENGTH es ⇒
     (lit wb (smart_entry_lit name k j (EL j es)) ⇔ smart_entry_holds (EL j es) wi)` by
    (rw[]>>irule smart_entry_lit_sem>>first_assum (irule_at Any)>>
     qpat_x_assum`EVERY _ (FLAT _)` mp_tac>>
     simp[EVERY_FLAT,Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,EL_MAP])>>
  qpat_x_assum`_ ⇔ wb (INR (Index name k))` mp_tac>>
  simp[eval_lin_term_MAPi_ge_LENGTH,EVERY_EL]
QED

(* the row's defs hold under the proof-only reified assignment *)
Theorem encode_smart_row_reify:
  valid_assignment bnd wi ∧
  smart_reify cs wi name rows ∧
  k < LENGTH rows ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_smart_row bnd name k (EL k rows))
Proof
  strip_tac>>
  `∀j. j < LENGTH (EL k rows) ⇒
     EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
       (encode_smart_entry bnd name k j (EL j (EL k rows)))` by
    (rw[]>>irule smart_entry_reify>>rpt(first_assum (irule_at Any))>>simp[])>>
  `∀j. j < LENGTH (EL k rows) ⇒
     (lit (reify_avar cs wi) (smart_entry_lit name k j (EL j (EL k rows))) ⇔
      smart_entry_holds (EL j (EL k rows)) wi)` by
    (rw[]>>irule smart_entry_lit_sem>>first_assum (irule_at Any)>>simp[])>>
  simp[encode_smart_row_def,EVERY_APPEND]>>
  conj_tac
  >- simp[EVERY_FLAT,Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,EL_MAP]
  >- (
    simp[abstr_cbimply_var,EVERY_REVERSE]>>
    DEP_REWRITE_TAC[bimply_bit_sem]>>simp[lit_def]>>
    gs[smart_reify_def,eval_lin_term_MAPi_ge_LENGTH,reify_avar_def,
       reify_smart_flag_def,EVERY_EL,o_DEF])
QED

Theorem encode_smart_table_sem_1:
  valid_assignment bnd wi ∧
  smart_reify cs wi name rows ∧
  smart_table_sem rows wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_smart_table bnd rows name)
Proof
  strip_tac>>
  simp[encode_smart_table_def,EVERY_APPEND]>>
  conj_tac
  >- (
    simp[EVERY_FLAT,Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,EL_MAP]>>
    rw[]>>irule encode_smart_row_reify>>simp[])
  >- (
    simp[abstr_cat_least_one,at_least_one_sem,MEM_MAPi,PULL_EXISTS]>>
    gvs[smart_table_sem_def,MEM_EL]>>
    qexists_tac`n`>>
    gs[smart_reify_def,lit_def,reify_avar_def,reify_smart_flag_def])
QED

Theorem encode_smart_table_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_smart_table bnd rows name) ⇒
  smart_table_sem rows wi
Proof
  strip_tac>>
  fs[encode_smart_table_def,EVERY_APPEND]>>
  `∀k. k < LENGTH rows ⇒
     (wb (INR (Index name k)) ⇔ EVERY (λe. smart_entry_holds e wi) (EL k rows))` by
    (rw[]>>irule encode_smart_row_sem>>first_assum (irule_at Any)>>
     qpat_x_assum`EVERY _ (FLAT _)` mp_tac>>
     simp[EVERY_FLAT,Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,EL_MAP])>>
  gvs[MEM_MAPi,lit_def]>>
  simp[smart_table_sem_def,MEM_EL]>>
  metis_tac[]
QED

(* bridges: the desugared rows reproduce the variant's existing predicate. *)

Theorem lex_rows_aux_sem[local]:
  ∀zs acc.
    EXISTS (λrow. EVERY (λe. smart_entry_holds e wi) row) (lex_rows_aux acc zs) ⇔
    EVERY (λe. smart_entry_holds e wi) acc ∧
    row_gt (MAP (λp. varc wi (FST p)) zs) (MAP (λp. varc wi (SND p)) zs)
Proof
  Induct
  >- rw[lex_rows_aux_def,row_gt_def]>>
  Cases>>
  gs[lex_rows_aux_def,EVERY_APPEND,smart_entry_holds_def,cmpop_val_def,row_gt_def]>>
  metis_tac[]
QED

Theorem amo_rows_aux_sem[local]:
  ∀Xs pre.
    EXISTS (λrow. EVERY (λe. smart_entry_holds e wi) row) (amo_rows_aux pre Xs v) ⇔
    EVERY (λe. smart_entry_holds e wi) pre ∧ Xs ≠ [] ∧
    LENGTH (FILTER (λX. varc wi X = v) Xs) ≤ 1
Proof
  Induct
  >- rw[amo_rows_aux_def]>>
  rpt gen_tac>>
  gs[amo_rows_aux_def,EVERY_APPEND,EVERY_MAP,combinTheory.o_DEF]>>
  qmatch_goalsub_abbrev_tac`EVERY PR pre`>>
  gs[smart_entry_holds_def,cmpop_val_def,varc_INR]>>
  `EVERY (λX. varc wi X ≠ v) Xs ⇔ FILTER (λX. varc wi X = v) Xs = []` by
    simp[FILTER_EQ_NIL]>>
  `FILTER (λX. varc wi X = v) Xs ≠ [] ⇒ Xs ≠ []` by (Cases_on`Xs`>>simp[])>>
  Cases_on`varc wi h = v`>>
  Cases_on`FILTER (λX. varc wi X = v) Xs`>>
  gvs[FILTER_EQ_NIL,EVERY_MEM,EXISTS_MEM]>>
  qpat_x_assum`Abbrev _`kall_tac>>
  metis_tac[]
QED

Theorem row_gt_TAKE[local]:
  ∀xs ys.
    row_gt xs ys ⇔
    row_gt (TAKE (MIN (LENGTH xs) (LENGTH ys)) xs)
           (TAKE (MIN (LENGTH xs) (LENGTH ys)) ys) ∨
    LENGTH ys < LENGTH xs ∧
    TAKE (MIN (LENGTH xs) (LENGTH ys)) xs =
    TAKE (MIN (LENGTH xs) (LENGTH ys)) ys
Proof
  ho_match_mp_tac row_gt_ind>>
  rw[row_gt_def]>>
  `MIN (SUC (LENGTH xs)) (SUC (LENGTH ys)) − 1 = MIN (LENGTH xs) (LENGTH ys)`
    by simp[MIN_DEF]>>
  gvs[]>>
  metis_tac[]
QED

Theorem lex_smart_table_bridge:
  smart_table_sem (lex_smart_rows Xs Ys) wi ⇔ lex_sem NONE GreaterThan Xs Ys wi
Proof
  simp[smart_table_sem_def,GSYM EXISTS_MEM,lex_smart_rows_def,EXISTS_APPEND,
       lex_rows_aux_sem,lex_sem_def,reify_sem_def]>>
  qabbrev_tac`m = MIN (LENGTH Xs) (LENGTH Ys)`>>
  `LENGTH (TAKE m Xs) = LENGTH (TAKE m Ys)` by simp[LENGTH_TAKE_EQ,Abbr`m`,MIN_DEF]>>
  `(λp:'a varc # 'a varc. varc wi (FST p)) = varc wi ∘ FST ∧
   (λp:'a varc # 'a varc. varc wi (SND p)) = varc wi ∘ SND`
    by simp[combinTheory.o_DEF,FUN_EQ_THM]>>
  gs[MAP_ZIP,MAP_TAKE]>>
  `row_gt (MAP (varc wi) Xs) (MAP (varc wi) Ys) ⇔
   row_gt (TAKE m (MAP (varc wi) Xs)) (TAKE m (MAP (varc wi) Ys)) ∨
   LENGTH Ys < LENGTH Xs ∧
   TAKE m (MAP (varc wi) Xs) = TAKE m (MAP (varc wi) Ys)` by (
    qspecl_then [`MAP (varc wi) Xs`,`MAP (varc wi) Ys`] mp_tac row_gt_TAKE>>
    simp[Abbr`m`,LENGTH_MAP])>>
  gs[]>>
  `EXISTS (λrow. EVERY (λe. smart_entry_holds e wi) row)
     (if LENGTH Xs > LENGTH Ys then
        [MAP (λ(x,y). SCmp x Equal y) (ZIP (TAKE m Xs,TAKE m Ys))] else []) ⇔
   LENGTH Ys < LENGTH Xs ∧
   TAKE m (MAP (varc wi) Xs) = TAKE m (MAP (varc wi) Ys)` by (
    IF_CASES_TAC>>
    simp[GSYM MAP_TAKE,MAP_EQ_EVERY2,LIST_REL_EVERY_ZIP,EVERY_MAP,
         smart_entry_holds_def,cmpop_val_def,pairTheory.ELIM_UNCURRY])>>
  fs[]
QED

Theorem amo_smart_table_bridge:
  smart_table_sem (amo_smart_rows Xs v) wi ⇔ at_most_one_sem Xs (INR v) wi
Proof
  `iSUM (MAP (λX. b2i (varc wi X = v)) Xs) =
   &LENGTH (FILTER (λX. varc wi X = v) Xs)` by
    (rewrite_tac[GSYM iSUM_FILTER]>>simp[combinTheory.o_DEF])>>
  simp[smart_table_sem_def,GSYM EXISTS_MEM,amo_smart_rows_def,
       at_most_one_sem_def,varc_INR]>>
  reverse IF_CASES_TAC
  >- (
    simp[amo_rows_aux_sem]>>
    `Xs ≠ []` by (Cases_on`Xs`>>gs[])>>
    simp[]>>
    intLib.ARITH_TAC)>>
  `LENGTH (FILTER (λX. varc wi X = v) Xs) ≤ 1` by
    (irule LESS_EQ_TRANS>>irule_at Any LENGTH_FILTER_LEQ>>simp[])>>
  simp[]>>
  intLib.ARITH_TAC
QED

Definition encode_extensional_constr_def:
  encode_extensional_constr bnd c name =
  case c of
    Table tss Xs => encode_table bnd tss Xs name
  | Regular Xs nstates trans finals =>
      encode_regular bnd Xs nstates trans finals name
  | NegativeTable tss Xs => encode_negative_table bnd tss Xs name
  | SmartTable rows => encode_smart_table bnd rows name
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
  metis_tac[encode_table_sem_1,encode_regular_sem_1,encode_negative_table_sem_1,
            encode_smart_table_sem_1,smart_reify_SmartTable]
QED

Theorem encode_extensional_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb)) (encode_extensional_constr bnd c name) ⇒
  extensional_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_extensional_constr_def,extensional_constr_sem_def]>>
  metis_tac[encode_table_sem_2,encode_regular_sem_2,encode_negative_table_sem_2,
            encode_smart_table_sem_2]
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

Definition cencode_neg_tuple_def:
  cencode_neg_tuple bnd Xts name n ec =
    let (eqs,ec') = cencode_full_eqs bnd Xts ec in
    (Append eqs
      (cat_least_one name (toString n)
        (MAP (λ(X,t). Neg (INL (Eq X t))) Xts)), ec')
End

Definition cencode_negative_table_def:
  cencode_negative_table bnd tss Xs name ec =
  let n = LENGTH Xs in
    if EVERY (λYs. LENGTH Ys = n) tss
    then
      let Xtss = MAP (λts. filter_match (ZIP (Xs,ts))) tss in
      let nXtss = enumerate 0 Xtss in
      fold_cenc (λ(n,Xts) ec. cencode_neg_tuple bnd Xts name n ec) nXtss ec
    else
      (cfalse_constr, ec)
End

Theorem cencode_negative_table_sem:
  valid_assignment bnd wi ∧
  cencode_negative_table bnd tss Xs name ec = (es,ec') ⇒
  enc_rel wi es (encode_negative_table bnd tss Xs name) ec ec'
Proof
  rw[cencode_negative_table_def,encode_negative_table_def]>>
  simp[MAPi_enumerate_MAP]>>
  irule enc_rel_fold_cenc>>
  first_x_assum (irule_at Any)>>
  rw[]>>pairarg_tac>>gvs[cencode_neg_tuple_def,encode_neg_tuple_def]>>
  pairarg_tac>>gvs[]>>
  irule enc_rel_Append>>
  simp[cat_least_one_def]>>
  qexists_tac`ec'`>>reverse conj_tac
  >- irule enc_rel_List_refl_1>>
  fs[cencode_full_eqs_def]>>
  irule enc_rel_fold_cenc>>
  first_x_assum (irule_at Any)>>
  rw[]>>pairarg_tac>>gvs[enc_rel_encode_full_eq]
QED

(* concrete SmartTable encoder: mirrors encode_smart_* but threads ec for the
   shared Eq/Ge atoms (reif_gen / full_eq); fresh sgt/slt/seq/sset flags and
   the selector cbimply carry no ec. *)
Definition cencode_smart_entry_def:
  cencode_smart_entry bnd name k j e ec =
  case e of
    SCmp v1 cmp v2 =>
      (case v2 of
        INR c => cencode_reif_gen bnd (v1,cmp,c) ec
      | INL _ =>
        let
          fgt = INR (name, Indices [k;j] (SOME «sgt»));
          flt = INR (name, Indices [k;j] (SOME «slt»));
          feq = INR (name, Indices [k;j] (SOME «seq»))
        in
        (case cmp of
          GreaterThan  => (cbimply_var bnd fgt (mk_gt v1 v2), ec)
        | LessEqual    => (cbimply_var bnd fgt (mk_gt v1 v2), ec)
        | LessThan     => (cbimply_var bnd flt (mk_lt v1 v2), ec)
        | GreaterEqual => (cbimply_var bnd flt (mk_lt v1 v2), ec)
        | Equal =>
            (Append (cbimply_var bnd fgt (mk_gt v1 v2))
              (Append (cbimply_var bnd flt (mk_lt v1 v2))
                (cbimply_var bnd feq ([],[(1,Neg fgt);(1,Neg flt)],2))), ec)
        | NotEqual =>
            (Append (cbimply_var bnd fgt (mk_gt v1 v2))
              (Append (cbimply_var bnd flt (mk_lt v1 v2))
                (cbimply_var bnd feq ([],[(1,Neg fgt);(1,Neg flt)],2))), ec)))
  | SSet v b vs =>
      let fset = INR (name, Indices [k;j] (SOME «sset»)) in
      let (eqs,ec') = fold_cenc (λc ec. cencode_full_eq bnd v c ec) vs ec in
      (Append eqs
        (cbimply_var bnd fset
          (at_least_one (MAP (λc. Pos (INL (Eq v c))) vs))), ec')
End

Definition cencode_smart_row_def:
  cencode_smart_row bnd name k es ec =
  let (eqs,ec') =
    fold_cenc (λ(j,e) ec. cencode_smart_entry bnd name k j e ec)
      (enumerate 0 es) ec in
  (Append eqs
    (cbimply_var bnd (INR (Index name k))
      ([], MAP (λl. (1,l)) (MAPi (λj e. smart_entry_lit name k j e) es),
       &LENGTH es)), ec')
End

Definition cencode_smart_table_def:
  cencode_smart_table bnd rows name ec =
  let (eqs,ec') =
    fold_cenc (λ(k,es) ec. cencode_smart_row bnd name k es ec)
      (enumerate 0 rows) ec in
  (Append eqs
    (cat_least_one name «» (MAPi (λk es. Pos (INR (Index name k))) rows)), ec')
End

(* abstr (cbimply_var ..) is [simp]-rewritten to REVERSE (bimply_bit ..), so
   the spec side never shows abstr; relate any ec-preserving block to it by
   discharging the (simp-provable) abstr equation. *)
Theorem enc_rel_abstr'[local]:
  es' = abstr es ⇒ enc_rel wi es es' ec ec
Proof
  rw[]>>irule enc_rel_abstr
QED

Theorem enc_rel_cbimply_var[local]:
  enc_rel wi (cbimply_var bnd x cc) (REVERSE (bimply_bit bnd (Pos x) cc)) ec ec
Proof
  irule enc_rel_abstr'>>simp[]
QED

Theorem cencode_smart_entry_sem:
  valid_assignment bnd wi ∧
  cencode_smart_entry bnd name k j e ec = (es,ec') ⇒
  enc_rel wi es (encode_smart_entry bnd name k j e) ec ec'
Proof
  strip_tac>>
  Cases_on`e`>>
  gvs[cencode_smart_entry_def,encode_smart_entry_def]
  >- (
    Cases_on`s0`>>gvs[]
    >- (Cases_on`c`>>gvs[]>>irule enc_rel_abstr'>>simp[])>>
    metis_tac[enc_rel_encode_reif_gen])
  >- (
    pairarg_tac>>gvs[]>>
    irule enc_rel_Append>>
    irule_at Any enc_rel_cbimply_var>>
    irule enc_rel_fold_cenc>>
    first_x_assum (irule_at Any)>>
    rw[]>>gvs[enc_rel_encode_full_eq])
QED

Theorem cencode_smart_row_sem:
  valid_assignment bnd wi ∧
  cencode_smart_row bnd name k es ec = (xs,ec') ⇒
  enc_rel wi xs (encode_smart_row bnd name k es) ec ec'
Proof
  rw[cencode_smart_row_def,encode_smart_row_def]>>
  pairarg_tac>>gvs[]>>
  irule enc_rel_Append>>
  irule_at Any enc_rel_cbimply_var>>
  simp[MAPi_enumerate_MAP]>>
  irule enc_rel_fold_cenc>>
  first_x_assum (irule_at Any)>>
  rw[]>>pairarg_tac>>gvs[]>>
  metis_tac[cencode_smart_entry_sem]
QED

Theorem cencode_smart_table_sem:
  valid_assignment bnd wi ∧
  cencode_smart_table bnd rows name ec = (es,ec') ⇒
  enc_rel wi es (encode_smart_table bnd rows name) ec ec'
Proof
  rw[cencode_smart_table_def,encode_smart_table_def]>>
  pairarg_tac>>gvs[]>>
  simp[MAPi_enumerate_MAP]>>
  irule enc_rel_Append>>
  qexists_tac`ec'`>>reverse conj_tac
  >- (simp[cat_least_one_def]>>irule enc_rel_List_refl_1)>>
  irule enc_rel_fold_cenc>>
  first_x_assum (irule_at Any)>>
  rw[]>>pairarg_tac>>gvs[]>>
  metis_tac[cencode_smart_row_sem]
QED

Definition cencode_extensional_constr_def:
  cencode_extensional_constr bnd c name ec =
  case c of
    Table tss Xs => cencode_table bnd tss Xs name ec
  | Regular Xs nstates trans finals =>
      cencode_regular bnd Xs nstates trans finals name ec
  | NegativeTable tss Xs => cencode_negative_table bnd tss Xs name ec
  | SmartTable rows => cencode_smart_table bnd rows name ec
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
    gvs[enc_rel_encode_full_eq])
  >- metis_tac[cencode_regular_sem]
  >- metis_tac[cencode_negative_table_sem]
  >- metis_tac[cencode_smart_table_sem]
QED

(*
EVAL``append o FST $ cencode_extensional_constr
  (\x. (-5,5))
  (Table [[SOME 1i;SOME 2i];[NONE;NONE];[SOME 1i;NONE];] [INL («x»);INL («y»)]) («t1») init_ec``
*)


