(*
  WCNF into pbc, written in a tutorial style
*)
Theory wcnf_to_pb
Ancestors
  pbc pbc_normalise satSem lpr cnf_to_pb
Libs
  preamble

(*** STEP 1: Formalise the semantics of MAX-SAT ***)

(* lprTheory already provides a concrete syntax for clauses
  based on the DIMACS integer representation, which we will reuse *)

(* Weighted (soft) clauses are clauses paired with a weight n
  In this representation, the clause is hard
  if n = 0 and soft (with weight n) otherwise. *)
Type wcclause = ``:num # cclause``;

(* Weighted CNFs are a list of weighted soft clauses *)
Type wccnf = ``:wcclause list``;

(* A cleaner definition of satisfaction *)
Definition sat_lit_def:
  sat_lit w l ⇔
  l ≠ 0 ∧
  let v = Num (ABS l) in
  if l > 0 then w v else ¬ w v
End

Definition sat_clause_def:
  sat_clause w C ⇔
  ∃l. l ∈ set C ∧ sat_lit w l
End

Definition sat_hard_def:
  sat_hard w wfml ⇔
  ∀C. (0:num,C) ∈ set wfml ⇒ sat_clause w C
End

(* The weight of a clause with respect to an assignment
  (0 if satisfied, w otherwise) *)
Definition weight_clause_def:
  weight_clause w ((n,C):wcclause) =
  if sat_clause w C then 0 else n
End

Definition cost_def:
  cost w wfml = SUM (MAP (weight_clause w) wfml)
End

Definition opt_cost_def:
  opt_cost wfml =
  if ¬∃w. sat_hard w wfml then NONE
  else SOME (MIN_SET {cost w wfml | w | sat_hard w wfml})
End

(* Some alternative definitions *)
Theorem sat_lit_alt:
  sat_lit w l ⇔
  l ≠ 0 ∧ satisfies_literal w (interp_lit l)
Proof
  EVAL_TAC>>rw[]
QED

Theorem sat_clause_alt:
  sat_clause w C ⇔
  satisfies_clause w (interp_cclause C)
Proof
  rw[sat_clause_def,lprTheory.interp_cclause_def,satSemTheory.satisfies_clause_def,PULL_EXISTS]>>
  metis_tac[sat_lit_alt]
QED

(*** STEP 2: Formalise an encoding into PB ***)

(* A simple encoding trick is to use meaningful variable
  names to help partition the variable space *)

(* Here, we let variable names be either
  INL n --> representing the original variable n in CNF
  INR m --> an auxiliary (blocking) variable *)
Type enc_var = ``:num + num``

(* Turns a literal into its PB representation *)
Definition enc_lit_def:
  enc_lit l =
  if l > 0 then
    Pos (INL (Num (ABS l)) : enc_var)
  else
    Neg (INL (Num (ABS l)) : enc_var)
End

Definition enc_clause_def:
  enc_clause C =
  MAP (λl. (1:int ,enc_lit l)) C
End

(* Each weighted clause turns into
  ≤ 1 PB constraints and ≤ 1 terms in the objective *)
Definition wclause_to_pbc_def:
  wclause_to_pbc (i,n,C) =
  let C = nub (FILTER (λl. l ≠ 0) C) in
  if n = 0 then (* hard clauses *)
    ([(GreaterEqual,enc_clause C,1:int)],[])
  else (* soft clauses *)
  if LENGTH C = 1 then
    ([],[((&n:int), negate (enc_lit (HD C)))])
  else
    ([(GreaterEqual,(1,Neg (INR i)) :: enc_clause C,1)],
     [((&n:int),Neg (INR i))])
End

(* Encoding a weighted formula *)
Definition wfml_to_pbf_def:
  wfml_to_pbf wfml =
  let ls = MAP wclause_to_pbc (enumerate 1 wfml) in
  let pbf = FLAT (MAP FST ls) in
  let obj = FLAT (MAP SND ls) in
  (SOME (obj,0:int), pbf)
End

(* Map abstract variables into string names *)
Definition enc_string_def:
  (enc_string (INL n) = concat [strlit"x";toString n]) ∧
  (enc_string (INR n) = concat [strlit"_b";toString n])
End

(* The end-to-end encoder using string names *)
Definition full_encode_def:
  full_encode wfml =
  let (obj,pbf) = wfml_to_pbf wfml in
  (map_obj enc_string obj,
  MAP (map_pbc enc_string) pbf)
End

Definition nn_int_def:
  nn_int i = if i < 0 then 0:num else Num i
End

(* Convert a VeriPB conclusion into a MIN UNSAT conclusion *)
Definition conv_concl_def:
  (conv_concl NoConcl = SOME NONE) ∧
  (conv_concl (OBounds lbi ubi) =
  let lbg =
    case lbi of
      NONE => NONE
    | SOME lb => SOME (nn_int lb) in
  let ubg =
    case ubi of
      NONE => NONE
    | SOME ub =>
      SOME (nn_int ub) in
    SOME (SOME (lbg,ubg))) ∧
  (conv_concl _ = NONE)
End

(* Convert a VeriPB output into a MAX SAT output
  NOTE: this currently requires that no solutions are logged
*)
Definition conv_output_def:
  (conv_output _ NoOutput = SOME F) ∧
  (conv_output
    (bopt: int option) Equioptimal =
    if bopt = NONE
    then SOME T
    else NONE) ∧
  (conv_output _ _ = NONE)
End

(*** STEP 3: Prove correctness of the encoding ***)

Theorem satisfies_pbc_satisfies_clause:
  wf_clause C ∧
  satisfies_pbc w (GreaterEqual,enc_clause C,1) ⇒
  satisfies_clause (w o INL) (interp_cclause C)
Proof
  Induct_on`C`>>rw[satisfies_clause_def,satisfies_pbc_def]
  >-
    EVAL_TAC>>
  fs[satisfies_pbc_def,Once interp_cclause_cons,enc_clause_def]>>
  fs[eval_lin_term_def,iSUM_def,wf_clause_def]>>
  Cases_on`satisfies_literal (w o INL) (interp_lit h)`
  >-
    (qexists_tac`interp_lit h`>>simp[interp_cclause_def])>>
  `eval_lit w (enc_lit h) = 0` by
    (rw[enc_lit_def]>>fs[interp_lit_def,satisfies_literal_def])>>
  fs[]>>
  metis_tac[satisfies_clause_def]
QED

Theorem eval_lin_term_enc_clause_ge0:
  eval_lin_term w (enc_clause C) ≥ 0
Proof
  simp[eval_lin_term_def,enc_clause_def]>>
  match_mp_tac iSUM_one_coeff>>
  simp[MEM_MAP,PULL_EXISTS]
QED

Theorem satisfies_clause_satisfies_pbc:
  wf_clause C ∧
  (∀v. w' (INL v) = w v) ∧
  satisfies_clause w (interp_cclause C) ⇒
  satisfies_pbc w' (GreaterEqual,enc_clause C,1)
Proof
  Induct_on`C`
  >-
    fs[satisfies_clause_def]>>
  rw[]>>
  gvs[interp_cclause_def,wf_clause_def]>>
  Cases_on`satisfies_literal w (interp_lit h)`>>
  fs[satisfies_clause_INSERT]
  >- (
    simp[satisfies_pbc_def,enc_clause_def,eval_lin_term_def,iSUM_def]>>
    `eval_lit w' (enc_lit h) = 1` by
      (rw[enc_lit_def]>>gvs[interp_lit_def,satisfies_literal_def])>>
    simp[GSYM eval_lin_term_def,GSYM enc_clause_def]>>
    qsuff_tac`eval_lin_term w' (enc_clause C') ≥ 0`
    >- intLib.ARITH_TAC>>
    metis_tac[eval_lin_term_enc_clause_ge0])>>
  fs[satisfies_pbc_def,enc_clause_def,eval_lin_term_def,iSUM_def]>>
  `eval_lit w' (enc_lit h) = 0` by
    (rw[enc_lit_def]>>gvs[interp_lit_def,satisfies_literal_def])>>
  fs[]
QED

Theorem interp_cclause_FILTER:
  interp_cclause C =
  interp_cclause (FILTER (λl. l ≠ 0) C)
Proof
  rw[interp_cclause_def]>>
  simp[EXTENSION,MEM_FILTER]>>
  metis_tac[]
QED

Theorem EVERY_FILTER:
  EVERY P (FILTER P ls)
Proof
  Induct_on`ls`>>rw[]
QED

Theorem satisfies_pbc_cons:
  satisfies_pbc w (op,cl::xs,n) =
  satisfies_pbc w (op,xs,n - eval_term w cl)
Proof
  rw[satisfies_pbc_def,eval_lin_term_def,iSUM_def]>>
  Cases_on`op`>>simp[]>>
  intLib.ARITH_TAC
QED

Theorem weight_clause_FILTER:
  weight_clause w (n,C) =
  weight_clause w (n, FILTER (λl. l ≠ 0) C)
Proof
  rw[weight_clause_def,sat_clause_alt]>>
  metis_tac[interp_cclause_FILTER]
QED

Theorem weight_clause_nub:
  weight_clause f (q,nub C) =
  weight_clause f (q,C)
Proof
  rw[weight_clause_def,interp_cclause_def,sat_clause_alt]
QED

Theorem interp_cclause_nub:
  interp_cclause (nub C) = interp_cclause C
Proof
  rw[interp_cclause_def]
QED

(* The sum of weights for unsatisfied clauses is
  upper bounded by the (negated) obj *)
Theorem weight_clause_obj_upper:
  wfml_to_pbf wfml = (obj,pbf) ∧
  satisfies w (set pbf) ⇒
  &(SUM (MAP (weight_clause (w o INL)) wfml)) ≤
  eval_obj obj w
Proof
  rw[wfml_to_pbf_def,eval_obj_def]>>
  simp[eval_lin_term_def,MAP_FLAT,MAP_MAP_o,o_DEF]>>
  rename1`enumerate k wfml`>>
  pop_assum mp_tac>>
  qid_spec_tac`k`>>
  Induct_on`wfml`>>rw[]
  >-
    EVAL_TAC>>
  gvs[miscTheory.enumerate_def]>>
  last_x_assum drule>>strip_tac>>
  Cases_on`h`>>
  simp[miscTheory.enumerate_def,wclause_to_pbc_def]>>
  qmatch_goalsub_abbrev_tac`LENGTH C = 1`>>
  `wf_clause C` by
    fs[Abbr`C`,wf_clause_def,MEM_FILTER]>>
  `weight_clause (λx. w (INL x)) (q,r) =
   weight_clause (λx. w (INL x)) (q,C)` by
    metis_tac[Abbr`C`,weight_clause_FILTER,weight_clause_nub]>>
  rw[]>>simp[weight_clause_def,iSUM_def,sat_clause_alt]
  >- (
    Cases_on`C`>>fs[]>>
    IF_CASES_TAC>>
    gvs[interp_cclause_def,satisfies_clause_def,wf_clause_def]>>
    rw[enc_lit_def]>>fs[interp_lit_def,satisfies_literal_def]>>
    intLib.ARITH_TAC)>>
  fs[wclause_to_pbc_def,satisfies_pbc_cons]>>
  Cases_on`w (INR k)`>>fs[]
  >- (
    rw[]>>
    metis_tac[satisfies_pbc_satisfies_clause]
    )>>
  rw[]>>
  intLib.ARITH_TAC
QED

(* Prove correctness of the encoding:
  From PBF to CNF, we simply project out the original variables
  In this case, the PBF objective is an upper bound on the
  sum of weights of unsatisfied clauses
  (because our encoding doesn't enforce the other bound
  on auxiliary variables) *)
Theorem encode_correct_pbf_cnf:
  wfml_to_pbf wfml = (obj,pbf) ∧
  satisfies w (set pbf) ⇒
  sat_hard (w o INL) wfml ∧
  &(SUM (MAP (weight_clause (w o INL)) wfml)) ≤
  eval_obj obj w
Proof
  rw[]
  >- (
    (* All hard constraints are satisfied *)
    gvs[wfml_to_pbf_def]>>
    fs[pbcTheory.satisfies_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]>>
    rw[sat_hard_def,sat_clause_alt]>>
    fs[MEM_EL]>>rw[]>>fs[LENGTH_enumerate,PULL_EXISTS]>>
    first_x_assum drule>>
    DEP_REWRITE_TAC[EL_enumerate]>>
    Cases_on`EL n wfml`>>
    fs[wclause_to_pbc_def]>>
    strip_tac>>simp[Once interp_cclause_FILTER]>>
    PURE_ONCE_REWRITE_TAC[GSYM interp_cclause_nub]>>
    match_mp_tac satisfies_pbc_satisfies_clause>>
    simp[wf_clause_def,MEM_FILTER])>>
  drule_all weight_clause_obj_upper>>
  simp[]
QED

Theorem MEM_enumerate_index:
  MEM (i,e) (enumerate k ls) ⇒
  i ≥ k
Proof
  simp[MEM_EL]>>rw[]>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[EL_enumerate]>>fs[LENGTH_enumerate]
QED

(* Prove correctness of the encoding:
  From CNF to PBF, we construct an assignment which sets the
  auxiliaries as required.
  In this case, the PBF objective is exactly equal to
  the sum of weights of unsatisfied clauses *)
Theorem encode_correct_cnf_pbf:
  wfml_to_pbf wfml = (obj,pbf) ∧
  sat_hard w wfml ⇒
  ∃w'.
    satisfies w' (set pbf) ∧
    eval_obj obj w' = &(SUM (MAP (weight_clause w) wfml))
Proof
  rw[]>>gvs[wfml_to_pbf_def]>>
  rename1`enumerate k wfml`>>
  qexists_tac`λv.
    case v of
      INL x => w x
    | INR y =>
      satisfies_clause w (interp_cclause (SND (EL (y - k) wfml)))`>>
  CONJ_TAC >- (
    fs[sat_hard_def,sat_clause_alt,pbcTheory.satisfies_def]>>
    rw[MEM_FLAT,MEM_MAP]>>
    fs[MEM_EL]>>rw[]>>fs[LENGTH_enumerate,PULL_EXISTS]>>
    pop_assum mp_tac>>
    DEP_REWRITE_TAC[EL_enumerate]>>simp[]>>
    Cases_on`EL n wfml`>>
    fs[wclause_to_pbc_def]>>
    rw[]
    >- (
      match_mp_tac satisfies_clause_satisfies_pbc>>
      simp[interp_cclause_nub,GSYM interp_cclause_FILTER]>>
      first_x_assum drule>>
      simp[wf_clause_def,MEM_FILTER])>>
    (* For the non-hard clauses *)
    Cases_on`satisfies_clause w (interp_cclause r)`>>
    simp[satisfies_pbc_def,eval_lin_term_def,iSUM_def]>>
    simp[GSYM eval_lin_term_def]
    >- (
      fs[Once interp_cclause_FILTER,Once (GSYM interp_cclause_nub)]>>
      drule_at Any satisfies_clause_satisfies_pbc>>
      simp[satisfies_pbc_def]>>
      disch_then match_mp_tac>>
      simp[wf_clause_def,MEM_FILTER])>>
    rename1`eval_lin_term w' (enc_clause C')`>>
    qsuff_tac`eval_lin_term w' (enc_clause C') ≥ 0`
    >- intLib.ARITH_TAC>>
    metis_tac[eval_lin_term_enc_clause_ge0])>>
  simp[eval_obj_def,eval_lin_term_def]>>
  pop_assum kall_tac>>
  qid_spec_tac`k`>>
  Induct_on`wfml`
  >-
    simp[miscTheory.enumerate_def,iSUM_def]>>
  rw[]>>
  simp[miscTheory.enumerate_def,iSUM_APPEND]>>
  qmatch_goalsub_abbrev_tac`A + B = &(C + D)`>>
  qsuff_tac`A = &D ∧ B = &C`
  >- (
    rpt(pop_assum kall_tac)>>
    intLib.ARITH_TAC)>>
  unabbrev_all_tac>>CONJ_TAC
  >- (
    Cases_on`h`>>
    simp[wclause_to_pbc_def,weight_clause_def,iSUM_def,sat_clause_alt]>>
    qmatch_goalsub_abbrev_tac`LENGTH C = 1`>>
    `wf_clause C` by
      fs[Abbr`C`,wf_clause_def,MEM_FILTER]>>
    rw[]>>fs[iSUM_def]>>
    `satisfies_clause w (interp_cclause r) =
    satisfies_clause w (interp_cclause C)` by
      metis_tac[Abbr`C`,interp_cclause_nub,interp_cclause_FILTER]>>
    gvs[]>>
    (
    Cases_on`C`>>fs[]>>
    gvs[interp_cclause_def,wf_clause_def,interp_lit_def,enc_lit_def]>>
    rw[]>>fs[satisfies_clause_def,satisfies_literal_def]))>>
  pop_assum (qspec_then`k+1` sym_sub_tac)>>
  AP_TERM_TAC>>
  rw[MAP_EQ_f,MEM_FLAT,MEM_MAP,PULL_EXISTS]>>
  rename1`MEM rr (enumerate _ _)`>>
  PairCases_on`rr`>>fs[wclause_to_pbc_def]>>
  every_case_tac>>gvs[]
  >- rw[enc_lit_def]>>
  `rr0 - k > 0` by
    (drule MEM_enumerate_index>>simp[])>>
  simp[EL_CONS,PRE_SUB1]
QED

(* Prove injectivity of abstract -> concrete variable map *)
Theorem enc_string_INJ:
  INJ enc_string UNIV UNIV
Proof
  rw[INJ_DEF]
  \\ Cases_on`x` \\ Cases_on`y`
  \\ fs[enc_string_def]
  \\ fs [mlstringTheory.concat_def]
  \\ every_case_tac \\ gvs []
  \\ metis_tac[mlintTheory.num_to_str_11]
QED

(* Putting things together,
  the final theorem gives us verified lower and upper bounds
  on the MAX-SAT objective *)
Theorem full_encode_sem_concl:
  full_encode wfml = (obj,pbf) ∧
  sem_concl (set pbf) obj concl ∧
  conv_concl concl = SOME (SOME (lbg, ubg)) ⇒
  (case lbg of
    NONE => ¬∃w. sat_hard w wfml
  | SOME lb => (∀w. sat_hard w wfml ⇒ lb ≤ cost w wfml)) ∧
  (case ubg of
    NONE => T
  | SOME ub =>
    ∃w. sat_hard w wfml ∧ cost w wfml ≤ ub)
Proof
  strip_tac>>
  gvs[full_encode_def]>>
  pairarg_tac>>gvs[]>>
  qpat_x_assum`sem_concl _ _ _` mp_tac>>
  simp[LIST_TO_SET_MAP]>>
  DEP_REWRITE_TAC[GSYM concl_INJ_iff]>>
  CONJ_TAC >- (
    assume_tac enc_string_INJ>>
    drule INJ_SUBSET>>
    disch_then match_mp_tac>>
    simp[])>>
  Cases_on`concl`>>fs[conv_concl_def]>>
  rename1`OBounds lbi ubi`>>
  simp[sem_concl_def]>>
  rw[]
  >- ( (* Lower bound from PB optimization *)
    pop_assum kall_tac>>
    drule encode_correct_cnf_pbf>>rw[]>>
    Cases_on`lbi`>>fs[]
    >- (
      (* If the lower bound is NONE, then UNSAT *)
      rw[]>>
      CCONTR_TAC>>
      fs[pbcTheory.unsatisfiable_def,pbcTheory.satisfiable_def]>>
      metis_tac[LESS_EQ_REFL])>>
    rw[]>>
    first_x_assum drule>>rw[]>>
    first_x_assum drule>>rw[]>>
    simp[cost_def]>>rw[nn_int_def]>>
    intLib.ARITH_TAC)>>
  (* Upper bound from PB optimization *)
  qpat_x_assum`_ lbi _ _` kall_tac>>
  every_case_tac>>fs[]>>
  drule_all encode_correct_pbf_cnf>>rw[]>>
  first_x_assum (irule_at Any)>>
  rw[nn_int_def,cost_def]>>
  intLib.ARITH_TAC
QED

Theorem FINITE_max_sat:
  FINITE {cost w wfml| w | sat_hard w wfml}
Proof
  `FINITE (count (SUM (MAP FST wfml) + 1))` by fs[]>>
  drule_then match_mp_tac SUBSET_FINITE>>
  simp[IMAGE_DEF,SUBSET_DEF]>>rw[]>>
  simp[cost_def] >>
  simp[GSYM LE_LT1]>>
  match_mp_tac SUM_MAP_same_LE >>
  rw[EVERY_MEM,FORALL_PROD,weight_clause_def]>>
  rw[]
QED

Theorem MIN_SET_eq_intro:
  s ≠ {} ∧
  (∀x. x ∈ s ⇒ n ≤ x) ∧
  n ∈ s ⇒
  MIN_SET s = n
Proof
  rw[]>>
  DEEP_INTRO_TAC MIN_SET_ELIM>>
  simp[]>>
  rw[]>>
  fs[]>>
  res_tac>>fs[]
QED

(* Special case *)
Theorem full_encode_sem_concl_opt_cost:
  full_encode wfml = (obj,pbf) ∧
  sem_concl (set pbf) obj concl ∧
  conv_concl concl = SOME (SOME (lbg, ubg)) ⇒
  (lbg = NONE ⇒ opt_cost wfml = NONE) ∧
  (lbg = ubg ⇒ opt_cost wfml = lbg)
Proof
  strip_tac>>
  drule_all full_encode_sem_concl>>
  Cases_on`lbg`>>fs[opt_cost_def]>>
  rw[]>>gvs[]>>
  match_mp_tac MIN_SET_eq_intro>>
  rw[]
  >-
    (simp[EXTENSION]>>metis_tac[])
  >- metis_tac[]
  >- (
    first_assum (irule_at Any)>>
    first_x_assum drule>>
    rw[])
QED

Theorem full_encode_sem_output:
  full_encode wfml = (obj,pbf) ∧
  full_encode wfml' = (obj',pbf') ∧
  pbc$sem_output
    (set pbf) obj {} bound
    (set pbf') obj' {} output ∧
  conv_output bound output = SOME T ⇒
  ∀v.
    ((∃w. sat_hard w wfml ∧ cost w wfml ≤ v) ⇔
    (∃w'. sat_hard w' wfml' ∧ cost w' wfml' ≤ v))
Proof
  strip_tac>>
  gvs[full_encode_def]>>
  pairarg_tac>>gvs[]>>
  pairarg_tac>>gvs[]>>
  qpat_x_assum`sem_output _ _ _ _ _ _ _ _ ` mp_tac>>
  simp[LIST_TO_SET_MAP]>>
  `{} = IMAGE enc_string {}` by
    simp[]>>
  pop_assum SUBST_ALL_TAC>>
  DEP_REWRITE_TAC[GSYM output_INJ_iff]>>
  CONJ_TAC >- (
    assume_tac enc_string_INJ>>
    rw[]>>
    drule INJ_SUBSET>>
    disch_then match_mp_tac>>
    simp[])>>
  Cases_on`output`>>fs[conv_output_def]>>
  simp[sem_output_def]>>
  simp[EQ_IMP_THM]>>rw[]>>
  gvs[FORALL_AND_THM,PULL_EXISTS,AllCaseEqs()]
  >- (
    drule_all encode_correct_cnf_pbf>>rw[]>>
    first_x_assum drule>>
    disch_then(qspec_then`eval_obj obj' w'` mp_tac)>>simp[]>>
    rw[]>>
    qpat_x_assum`_ wfml = _` kall_tac>>
    drule_all encode_correct_pbf_cnf>>
    rw[]>>
    first_x_assum(irule_at Any)>>
    fs[cost_def]>>
    intLib.ARITH_TAC)
  >- (
    drule_all encode_correct_cnf_pbf>>rw[]>>
    first_x_assum drule>>
    disch_then(qspec_then`eval_obj obj'' w''` mp_tac)>>simp[]>>
    rw[]>>
    qpat_x_assum`_ wfml' = _` kall_tac>>
    drule_all encode_correct_pbf_cnf>>
    rw[]>>
    first_x_assum(irule_at Any)>>
    fs[cost_def]>>
    intLib.ARITH_TAC)
QED

(* rephrasing *)
Theorem full_encode_sem_output_opt_cost:
  full_encode wfml = (obj,pbf) ∧
  full_encode wfml' = (obj',pbf') ∧
  pbc$sem_output (set pbf) obj {} bound
    (set pbf') obj' {} output ∧
  conv_output bound output = SOME T ⇒
  opt_cost wfml = opt_cost wfml'
Proof
  rw[]>>
  drule_all full_encode_sem_output>>
  rw[opt_cost_def]>>
  fs[]
  >- metis_tac[LESS_EQ_REFL]
  >- metis_tac[LESS_EQ_REFL]>>
  `{cost w wfml | w | sat_hard w wfml} ≠ {} ∧
  {cost w wfml' | w | sat_hard w wfml'} ≠ {}` by
    (rw[EXTENSION]>>metis_tac[])>>
  match_mp_tac MIN_SET_eq_intro>>
  simp[]>>
  rw[]
  >- (
    gvs[FORALL_AND_THM,PULL_EXISTS,AllCaseEqs(),EQ_IMP_THM]>>
    last_x_assum drule>>
    disch_then(qspec_then`cost w'' wfml` mp_tac)>>
    simp[]>>rw[]>>
    (drule_at_then Any match_mp_tac LESS_EQ_TRANS)>>
    drule MIN_SET_LEM >>
    rw[]>>gvs[PULL_EXISTS])>>
  drule MIN_SET_LEM>>rw[]>>
  gvs[PULL_EXISTS,FORALL_AND_THM,PULL_EXISTS,AllCaseEqs(),EQ_IMP_THM]>>
  first_x_assum(qspecl_then[`cost w'' wfml'`,`w''`] mp_tac)>>
  simp[]>>rw[]>>
  first_assum (irule_at Any)>>
  rename1`cost ww wfml`>>
  first_x_assum(qspecl_then[`cost ww wfml`,`ww`] mp_tac)>>
  simp[]>>rw[]>>
  first_x_assum drule>>
  simp[]
QED

(*** STEP 4: Build a parser for the command line interface ***)

(* Parse a list of integers terminated by 0 *)
Definition parse_wclause_aux_def:
  (parse_wclause_aux [] (acc:cclause) = NONE) ∧
  (parse_wclause_aux [c] acc =
    if c = INR 0i then SOME acc else NONE) ∧
  (parse_wclause_aux (x::xs) acc =
    case x of
      INR l =>
      if l = 0 then NONE
      else parse_wclause_aux xs (l::acc)
    | INL (_:mlstring) => NONE)
End

Definition parse_wclause_def:
  parse_wclause ls =
  case ls of [] => NONE
  | c::rs =>
    (case parse_wclause_aux rs [] of NONE => NONE
    | SOME cl =>
      let cl = REVERSE cl in
      (case c of
        INL s => if s = strlit"h" then SOME (0,cl) else NONE
      | INR n => if n > 0 then SOME (Num n,cl) else NONE))
End

Definition wnocomment_line_def:
  (wnocomment_line (INL c::cs) ⇔
  (if strlen c > 0 then strsub c 0 ≠ #"c" else T)) ∧
  (wnocomment_line _ ⇔ T)
End

Definition parse_wcnf_toks_def:
  (parse_wcnf_toks [] acc = SOME (REVERSE acc)) ∧
  (parse_wcnf_toks (s::ss) acc =
    if wnocomment_line s then
      case parse_wclause s of NONE => NONE
      | SOME l => parse_wcnf_toks ss (l::acc)
    else parse_wcnf_toks ss acc)
End

Definition parse_wcnf_def:
  parse_wcnf strs =
  let tokss = MAP toks strs in
  parse_wcnf_toks tokss []
End

(*
  val wcnf =
  EVAL ``parse_wcnf
  [strlit"c This is a comment";
  strlit"cExample 1...another comment";
  strlit"h 1 2 3 4 0";
  strlit"1 -3 -5 6 7 0";
  strlit"6 -1 -2 0";
  strlit"4 1 6 -7 6 -7 0";]``

  val enc = EVAL`` full_encode (THE ^(rconc wcnf))``
*)

