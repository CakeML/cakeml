(*
  Multi-objective MaxSAT (MCNF) into pbc, written in a tutorial style
*)
Theory mcnf_to_pb
Ancestors
  pbc pbc_normalise pbc_mo cnf syntax_helper cnf_to_pb wcnf_to_pb
  mlmap comparison
Libs
  preamble

val _ = numLib.temp_prefer_num();

(*** STEP 1: Formalise the semantics of multi-objective MaxSAT ***)

(* A clause tagged with an objective index and a weight.
  Index 0 marks a hard clause; index i > 0 marks a soft clause
  contributing weight n to objective i when it is falsified. *)
Type mcclause = ``:num # num # num clause``;

Type mccnf = ``:mcclause list``;

Definition msat_hard_def:
  msat_hard w (mfml:mccnf) ⇔
  ∀n C. MEM (0:num,n,C) mfml ⇒ satisfies_clause w C
End

(* The number of objectives is the largest index occurring *)
Definition num_objs_def:
  num_objs (mfml:mccnf) = FOLDR (λ(i,n,C) a. MAX i a) (0:num) mfml
End

Definition weight_mclause_def:
  weight_mclause k w ((i,n,C):mcclause) =
  if i = k ∧ ¬satisfies_clause w C then n else 0
End

Definition cost_obj_def:
  cost_obj k w (mfml:mccnf) = SUM (MAP (weight_mclause k w) mfml)
End

(* The cost vector of an assignment, one component per objective *)
Definition cost_vec_def:
  cost_vec w (mfml:mccnf) =
  MAP (λk. &(cost_obj k w mfml):int) (GENLIST SUC (num_objs mfml))
End

(* The non-dominated set of cost vectors under an objective ordering *)
Definition nondom_costs_def:
  nondom_costs ord (mfml:mccnf) =
  min_set (ord_le ord) {cost_vec w mfml | w | msat_hard w mfml}
End

(*** STEP 2: Formalise an encoding into PB ***)

(* Variables of the encoding: INL v is the input variable v and INR C is
  the blocking variable of the non-unit soft clause C, so equal soft
  clauses share their blocking variable *)
Type menc_var = ``:num + num clause``;

Definition menc_lit_def:
  (menc_lit (cnf$Pos v) = pbc$Pos (INL v : menc_var)) ∧
  (menc_lit (cnf$Neg v) = pbc$Neg (INL v : menc_var))
End

Definition menc_clause_def:
  menc_clause C = MAP (λl. (1:int, menc_lit l)) C
End

(* The constraints contributed by one tagged clause.
  A soft clause of length ≠ 1 is relaxed by its positive blocking variable *)
Definition mclause_cs_def:
  mclause_cs ((i,n,C):mcclause) =
  if i = 0 then [(PGe,menc_clause (canon_clause C),1:int)]
  else if LENGTH C = 1 then []
  else [(PGe,(1,pbc$Pos (INR C)) :: menc_clause (canon_clause C),1:int)]
End

(* The terms contributed by one tagged clause to objective k *)
Definition mclause_obj_def:
  mclause_obj (k:num) ((i,n,C):mcclause) =
  if i ≠ k then []
  else if LENGTH C = 1 then [((&n:int), negate (menc_lit (HD C)))]
  else [((&n:int),pbc$Pos (INR C))]
End

Definition mfml_to_pbf_def:
  mfml_to_pbf (mfml:mccnf) =
  let pbf = FLAT (MAP mclause_cs mfml) in
  let objs =
    MAP (λk. (FLAT (MAP (mclause_obj k) mfml),0:int))
      (GENLIST SUC (num_objs mfml)) in
  (objs,pbf)
End

(* The largest variable of the instance *)
Definition mcnf_max_var_def:
  mcnf_max_var (mfml:mccnf) =
    max_list 0 (MAP var_lit (FLAT (MAP (λ(i,n,C). C) mfml)))
End

(* Clauses as balanced-map keys: literals as numbers, compared
  lexicographically *)
Definition lit_num_def:
  (lit_num (cnf$Pos v) = 2 * v) ∧
  (lit_num (cnf$Neg v) = 2 * v + 1)
End

Definition clause_key_def:
  clause_key (C:num clause) = MAP lit_num C
End

Definition blk_cmp_def:
  blk_cmp = list_cmp num_cmp
End

(* Blocking variables are numbered from nxt upwards in order of first
  occurrence of their clause *)
Definition alloc_blk_def:
  (alloc_blk (nxt:num) t ([]:mccnf) = t) ∧
  (alloc_blk nxt t ((i,n,C)::rest) =
    if i ≠ 0 ∧ LENGTH C ≠ 1 ∧ mlmap$lookup t (clause_key C) = NONE
    then alloc_blk (nxt+1) (mlmap$insert t (clause_key C) nxt) rest
    else alloc_blk nxt t rest)
End

Definition blk_map_def:
  blk_map mfml = alloc_blk (mcnf_max_var mfml + 1) (mlmap$empty blk_cmp) mfml
End

Definition blk_num_def:
  (blk_num t (INL v) = v) ∧
  (blk_num t (INR C) =
    case mlmap$lookup t (clause_key C) of NONE => 0 | SOME m => m)
End

(* Every variable is named x<num>, blocking variables above the input ones *)
Definition mcnf_enc_string_def:
  mcnf_enc_string t v = concat [«x»; toString (blk_num t v)]
End

(* The end-to-end encoder using string names *)
Definition full_encode_mcnf_def:
  full_encode_mcnf (mfml:mccnf) =
  let (objs,pbf) = mfml_to_pbf mfml in
  let f = mcnf_enc_string (blk_map mfml) in
  (map_objs f objs, MAP (map_pbc f) pbf)
End

(*** STEP 3: Prove correctness of the encoding ***)

Theorem lit_menc_lit[simp]:
  lit w (menc_lit l) ⇔ satisfies_lit (w o INL) l
Proof
  Cases_on`l`>>rw[menc_lit_def,satisfies_lit_def]
QED

Theorem eval_term_menc_lit[simp]:
  eval_term w (1:int,menc_lit l) = 1 ⇔ satisfies_lit (w o INL) l
Proof
  `∀b:bool. b2i b = 1 ⇔ b` by (Cases>>simp[])>>
  simp[]
QED

(* A clause's encoding is satisfied exactly when the clause is *)
Theorem eval_lin_term_menc_clause:
  eval_lin_term w (menc_clause C) ≥ 1 ⇔
  satisfies_clause (w o INL) C
Proof
  simp[menc_clause_def]>>
  DEP_REWRITE_TAC[eval_lin_term_coeff_1]>>
  rw[MEM_MAP,satisfies_clause_def,PULL_EXISTS]
QED

Theorem eval_lin_term_menc_clause_ge0:
  eval_lin_term w (menc_clause C) ≥ 0
Proof
  simp[eval_lin_term_def,menc_clause_def]>>
  match_mp_tac iSUM_one_coeff>>
  simp[MEM_MAP,PULL_EXISTS]
QED

Theorem satisfies_clause_menc_clause:
  (∀v. w' (INL v) = w v) ∧
  satisfies_clause w C ⇒
  eval_lin_term w' (menc_clause C) ≥ 1
Proof
  rw[eval_lin_term_menc_clause]>>
  `w' o INL = w` by simp[FUN_EQ_THM]>>
  gvs[]
QED

Theorem lit_var_menc_lit[simp]:
  lit_var (menc_lit l) = INL (var_lit l)
Proof
  Cases_on`l`>>rw[menc_lit_def]
QED

Theorem cost_obj_obj_upper:
  ∀mfml.
  0 < k ∧
  satisfies w (set (FLAT (MAP mclause_cs mfml))) ⇒
  &(cost_obj k (λx. w (INL x)) mfml) ≤
  eval_lin_term w (FLAT (MAP (mclause_obj k) mfml))
Proof
  Induct>>rw[cost_obj_def]>>
  first_x_assum drule>>simp[cost_obj_def]>>strip_tac>>
  PairCases_on`h`>>
  qsuff_tac`&(weight_mclause k (λx. w (INL x)) (h0,h1,h2)) ≤
    eval_lin_term w (mclause_obj k (h0,h1,h2))`
  >- intLib.ARITH_TAC>>
  simp[mclause_obj_def,weight_mclause_def]>>
  Cases_on`h0 = k`>>simp[]>>gvs[]>>
  gvs[mclause_cs_def]>>
  Cases_on`LENGTH h2 = 1`>>
  gvs[pbcTheory.satisfies_simp,pbcTheory.satisfies_pbc_plain]
  >- (
    (* a unit soft clause is charged through its negated literal *)
    `∃l. h2 = [l]` by (Cases_on`h2`>>gvs[LENGTH_EQ_NUM_compute])>>
    gvs[satisfies_clause_def,o_DEF]>>
    IF_CASES_TAC>>simp[])>>
  (* every other soft clause is charged through its blocking variable *)
  IF_CASES_TAC
  >- (
    `w (INR h2)` by (
      CCONTR_TAC>>gvs[]>>
      `eval_lin_term w (menc_clause (canon_clause h2)) ≥ 1` by
        intLib.ARITH_TAC>>
      gvs[eval_lin_term_menc_clause,o_DEF])>>
    simp[])>>
  Cases_on`w (INR h2)`>>simp[]
QED

Theorem mencode_correct_pbf_cnf:
  mfml_to_pbf mfml = (objs,pbf) ∧
  satisfies w (set pbf) ⇒
  msat_hard (w o INL) mfml ∧
  vec_le (cost_vec (w o INL) mfml) (obj_vecs objs w)
Proof
  rw[]>>gvs[mfml_to_pbf_def]
  >~ [‘msat_hard’] >- (
    rw[msat_hard_def]>>
    gvs[pbcTheory.satisfies_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]>>
    first_x_assum(qspecl_then[
      `(PGe,menc_clause (canon_clause C),1i)`,`(0,n,C)`] mp_tac)>>
    simp[mclause_cs_def,pbcTheory.satisfies_pbc_plain,
      eval_lin_term_menc_clause])>>
  simp[cost_vec_def,obj_vecs_def,MAP_MAP_o,o_DEF,vec_le_MAP,EVERY_MEM,
    MEM_GENLIST,PULL_EXISTS,pbcTheory.eval_obj_def]>>
  rw[]>>irule cost_obj_obj_upper>>simp[]
QED

Theorem cost_obj_obj_eq:
  ∀mfml.
  (∀x. ww (INL x) = w x) ∧
  (∀C. ww (INR C) ⇔ ¬satisfies_clause w C) ⇒
  eval_lin_term ww (FLAT (MAP (mclause_obj k) mfml)) =
  &(cost_obj k w mfml)
Proof
  Induct>>rw[cost_obj_def]>>
  PairCases_on`h`>>
  qsuff_tac`eval_lin_term ww (mclause_obj k (h0,h1,h2)) =
    &(weight_mclause k w (h0,h1,h2))`
  >- intLib.ARITH_TAC>>
  simp[mclause_obj_def,weight_mclause_def]>>
  Cases_on`h0 = k`>>simp[]>>gvs[]>>
  Cases_on`LENGTH h2 = 1`>>gvs[]
  >- (
    `∃l. h2 = [l]` by (Cases_on`h2`>>gvs[LENGTH_EQ_NUM_compute])>>
    `ww o INL = w` by simp[FUN_EQ_THM]>>
    gvs[satisfies_clause_def]>>
    IF_CASES_TAC>>simp[])>>
  IF_CASES_TAC>>gvs[]
QED

Theorem mencode_correct_cnf_pbf:
  mfml_to_pbf mfml = (objs,pbf) ∧
  msat_hard w mfml ⇒
  ∃w'.
    satisfies w' (set pbf) ∧
    obj_vecs objs w' = cost_vec w mfml
Proof
  rw[]>>gvs[mfml_to_pbf_def]>>
  (* a blocking variable is set exactly when its clause is falsified *)
  qexists_tac`λv. case v of INL x => w x | INR C => ¬satisfies_clause w C`>>
  CONJ_TAC >- (
    rw[pbcTheory.satisfies_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]>>
    PairCases_on`y`>>
    gvs[mclause_cs_def]>>
    qmatch_goalsub_abbrev_tac`satisfies_pbc ww _`>>
    `∀x. ww (INL x) ⇔ w x` by simp[Abbr`ww`]>>
    `∀C. ww (INR C) ⇔ ¬satisfies_clause w C` by simp[Abbr`ww`]>>
    `∀C. eval_lin_term ww (menc_clause C) ≥ 1 ⇔ satisfies_clause w C` by (
      `ww o INL = w` by simp[FUN_EQ_THM]>>
      simp[eval_lin_term_menc_clause])>>
    Cases_on`y0 = 0`>>gvs[pbcTheory.satisfies_pbc_plain]
    >- (
      simp[]>>
      metis_tac[msat_hard_def])>>
    Cases_on`LENGTH y2 = 1`>>gvs[pbcTheory.satisfies_pbc_plain]>>
    `eval_lin_term ww (menc_clause (canon_clause y2)) ≥ 0` by
      metis_tac[eval_lin_term_menc_clause_ge0]>>
    Cases_on`satisfies_clause w y2`>>gvs[]>>
    intLib.ARITH_TAC)>>
  simp[obj_vecs_def,cost_vec_def,MAP_MAP_o,o_DEF,MAP_EQ_f,MEM_GENLIST,
    PULL_EXISTS,pbcTheory.eval_obj_def]>>
  rw[]>>
  irule cost_obj_obj_eq>>
  simp[]
QED


Theorem mfml_to_pbf_nondom:
  mfml_to_pbf mfml = (objs,pbf) ⇒
  set_equiv ord (nondom_set ord (set pbf) objs) (nondom_costs ord mfml)
Proof
  rw[nondom_set_def,nondom_costs_def]>>
  irule min_set_dom_ord>>
  rw[in_obj_img]
  >~ [‘ord_le _ _ (cost_vec _ _)’] >- (
    drule_all mencode_correct_cnf_pbf>>
    rw[]>>
    qexists_tac`cost_vec w mfml`>>
    simp[]>>
    metis_tac[])>>
  drule_all mencode_correct_pbf_cnf>>
  rw[]>>
  qexists_tac`cost_vec (w o INL) mfml`>>
  simp[]>>
  metis_tac[vec_le_ord_le]
QED

(* The string renaming is injective on the variables of the encoding *)

Theorem TotOrd_blk_cmp:
  TotOrd blk_cmp
Proof
  rw[blk_cmp_def]>>
  irule comparisonTheory.TotOrd_list_cmp>>
  simp[miscTheory.TotOrd_num_cmp]
QED

Theorem lit_num_11[simp]:
  lit_num l = lit_num l' ⇔ l = l'
Proof
  Cases_on`l`>>Cases_on`l'`>>simp[lit_num_def]>>
  intLib.ARITH_TAC
QED

Theorem clause_key_11:
  clause_key C = clause_key C' ⇔ C = C'
Proof
  rw[clause_key_def]>>
  irule INJ_MAP_EQ_IFF>>
  simp[INJ_DEF]
QED

Theorem alloc_blk_map_ok:
  ∀mfml nxt t.
  map_ok t ⇒ map_ok (alloc_blk nxt t mfml)
Proof
  Induct>>rw[alloc_blk_def]>>
  PairCases_on`h`>>rw[alloc_blk_def]>>
  first_x_assum irule>>
  simp[mlmapTheory.insert_thm]
QED

Theorem alloc_blk_FLOOKUP_SOME:
  ∀mfml nxt t.
  map_ok t ∧ FLOOKUP (to_fmap t) k = SOME m ⇒
  FLOOKUP (to_fmap (alloc_blk nxt t mfml)) k = SOME m
Proof
  Induct>>rw[alloc_blk_def]>>
  PairCases_on`h`>>rw[alloc_blk_def]>>
  first_x_assum irule>>
  simp[mlmapTheory.insert_thm,FLOOKUP_UPDATE]>>
  rw[]>>gvs[mlmapTheory.lookup_thm]
QED

Theorem alloc_blk_dom:
  ∀mfml nxt t.
  map_ok t ∧ MEM (i,n,C) mfml ∧ i ≠ 0 ∧ LENGTH C ≠ 1 ⇒
  ∃m. FLOOKUP (to_fmap (alloc_blk nxt t mfml)) (clause_key C) = SOME m
Proof
  Induct >- simp[] >>
  rpt gen_tac>>
  PairCases_on`h`>>rw[alloc_blk_def]
  >- (
    (* the clause is the head and is allocated here *)
    irule_at Any alloc_blk_FLOOKUP_SOME>>
    simp[mlmapTheory.insert_thm,FLOOKUP_UPDATE])
  >- (
    first_x_assum irule>>
    simp[mlmapTheory.insert_thm])
  >- (
    (* the clause is the head and was allocated earlier *)
    gvs[]>>
    Cases_on`lookup t (clause_key C)`>>gvs[]>>
    irule_at Any alloc_blk_FLOOKUP_SOME>>
    gvs[mlmapTheory.lookup_thm])>>
  first_x_assum irule>>
  simp[]
QED

(* The allocated numbers lie in [lo,nxt) and are pairwise distinct *)
Theorem alloc_blk_inv:
  ∀mfml nxt t.
  map_ok t ∧ lo ≤ nxt ∧
  (∀k m. FLOOKUP (to_fmap t) k = SOME m ⇒ lo ≤ m ∧ m < nxt) ∧
  (∀k k' m. FLOOKUP (to_fmap t) k = SOME m ∧ FLOOKUP (to_fmap t) k' = SOME m ⇒
    k = k') ⇒
  (∀k m. FLOOKUP (to_fmap (alloc_blk nxt t mfml)) k = SOME m ⇒ lo ≤ m) ∧
  (∀k k' m.
    FLOOKUP (to_fmap (alloc_blk nxt t mfml)) k = SOME m ∧
    FLOOKUP (to_fmap (alloc_blk nxt t mfml)) k' = SOME m ⇒ k = k')
Proof
  Induct>>rpt gen_tac>>disch_then strip_assume_tac
  >- (simp[alloc_blk_def]>>metis_tac[])>>
  PairCases_on`h`>>simp[alloc_blk_def]>>
  IF_CASES_TAC>>simp[]
  >- (
    first_x_assum (qspecl_then [`nxt+1`,`insert t (clause_key h2) nxt`] mp_tac)>>
    impl_tac >- (
      simp[mlmapTheory.insert_thm,FLOOKUP_UPDATE]>>
      rw[]>>
      qpat_x_assum`∀k m. FLOOKUP _ _ = SOME _ ⇒ _` drule>>
      simp[])>>
    simp[])>>
  first_x_assum (qspecl_then [`nxt`,`t`] mp_tac)>>
  impl_tac >- metis_tac[]>>
  simp[]
QED

Theorem blk_map_map_ok:
  map_ok (blk_map mfml)
Proof
  rw[blk_map_def]>>
  irule alloc_blk_map_ok>>
  simp[mlmapTheory.empty_thm,TotOrd_blk_cmp]
QED

Theorem blk_map_dom:
  MEM (i,n,C) mfml ∧ i ≠ 0 ∧ LENGTH C ≠ 1 ⇒
  ∃m. lookup (blk_map mfml) (clause_key C) = SOME m
Proof
  rw[]>>
  `map_ok (blk_map mfml)` by simp[blk_map_map_ok]>>
  simp[mlmapTheory.lookup_thm,blk_map_def]>>
  irule alloc_blk_dom>>
  simp[mlmapTheory.empty_thm,TotOrd_blk_cmp]>>
  metis_tac[]
QED

Theorem blk_map_lower:
  lookup (blk_map mfml) (clause_key C) = SOME m ⇒
  mcnf_max_var mfml < m
Proof
  rw[]>>
  `map_ok (blk_map mfml)` by simp[blk_map_map_ok]>>
  gvs[mlmapTheory.lookup_thm,blk_map_def]>>
  qspecl_then [`mfml`,`mcnf_max_var mfml + 1`,`empty blk_cmp`] mp_tac
    (alloc_blk_inv |> Q.GEN `lo` |> Q.SPEC `mcnf_max_var mfml + 1`)>>
  simp[mlmapTheory.empty_thm,TotOrd_blk_cmp]>>
  strip_tac>>
  qpat_x_assum`∀k m. FLOOKUP _ _ = SOME _ ⇒ _` drule>>
  simp[]
QED

Theorem blk_map_inj:
  lookup (blk_map mfml) (clause_key C) = SOME m ∧
  lookup (blk_map mfml) (clause_key C') = SOME m ⇒
  C = C'
Proof
  rw[]>>
  `map_ok (blk_map mfml)` by simp[blk_map_map_ok]>>
  gvs[mlmapTheory.lookup_thm,blk_map_def]>>
  qspecl_then [`mfml`,`mcnf_max_var mfml + 1`,`empty blk_cmp`] mp_tac
    (alloc_blk_inv |> Q.GEN `lo` |> Q.SPEC `mcnf_max_var mfml + 1`)>>
  simp[mlmapTheory.empty_thm,TotOrd_blk_cmp]>>
  strip_tac>>
  metis_tac[clause_key_11]
QED

Theorem mcnf_max_var_bound:
  MEM (i,n,C) mfml ∧ MEM l C ⇒
  var_lit l ≤ mcnf_max_var mfml
Proof
  rw[mcnf_max_var_def]>>
  irule le_max_list>>
  qexists_tac`var_lit l`>>
  simp[MEM_MAP,MEM_FLAT,PULL_EXISTS,EXISTS_PROD]>>
  metis_tac[]
QED

(* The variables that can occur in the encoding of mfml *)
Definition menc_vars_def:
  menc_vars (mfml:mccnf) =
    {INL v | v ≤ mcnf_max_var mfml} ∪
    {INR C | ∃i n. MEM (i,n,C) mfml ∧ i ≠ 0 ∧ LENGTH C ≠ 1}
End

Theorem mfml_to_pbf_vars:
  mfml_to_pbf mfml = (objs,pbf) ⇒
  pbf_vars (set pbf) ∪ objs_vars objs ⊆ menc_vars mfml
Proof
  rw[mfml_to_pbf_def,pbf_vars_def,objs_vars_def,obj_vars_def,SUBSET_DEF,
    PULL_EXISTS,MEM_FLAT,MEM_MAP,MEM_GENLIST,menc_vars_def]
  >- (
    (* variables of the constraints *)
    gvs[MEM_FLAT,MEM_MAP]>>
    PairCases_on`y`>>
    gvs[mclause_cs_def]>>
    Cases_on`y0 = 0`>>gvs[]>>
    Cases_on`LENGTH y2 = 1`>>
    gvs[pbcTheory.pbc_vars_def,pbcTheory.pbhd_vars_def,menc_clause_def,
      MEM_MAP]>>
    metis_tac[mcnf_max_var_bound])>>
  (* variables of the objectives *)
  gvs[MEM_MAP,MEM_GENLIST,obj_vars_def,MEM_FLAT]>>
  PairCases_on`y`>>
  PairCases_on`y'`>>
  gvs[mclause_obj_def]>>
  Cases_on`y'0 = SUC m`>>gvs[]>>
  Cases_on`LENGTH y'2 = 1`>>gvs[pbc_normaliseTheory.lit_var_negate]
  >- (
    `∃l. y'2 = [l]` by (Cases_on`y'2`>>gvs[LENGTH_EQ_NUM_compute])>>
    gvs[]>>
    metis_tac[mcnf_max_var_bound,MEM])>>
  metis_tac[numTheory.NOT_SUC]
QED

(* Every blocking variable of the instance is numbered above its input
  variables *)
Theorem blk_num_INR:
  MEM (i,n,C) mfml ∧ i ≠ 0 ∧ LENGTH C ≠ 1 ⇒
  lookup (blk_map mfml) (clause_key C) = SOME (blk_num (blk_map mfml) (INR C)) ∧
  mcnf_max_var mfml < blk_num (blk_map mfml) (INR C)
Proof
  rw[]>>
  drule_all blk_map_dom>>
  rw[blk_num_def]>>
  drule blk_map_lower>>
  simp[]
QED

Theorem blk_num_INJ:
  INJ (blk_num (blk_map mfml)) (menc_vars mfml) UNIV
Proof
  rw[INJ_DEF,menc_vars_def]>>
  gvs[CONJUNCT1 blk_num_def]
  >- (
    drule_all blk_num_INR>>
    strip_tac>>intLib.ARITH_TAC)
  >- (
    drule_all blk_num_INR>>
    strip_tac>>intLib.ARITH_TAC)>>
  metis_tac[blk_num_INR,blk_map_inj]
QED

Theorem mcnf_enc_string_INJ:
  INJ (mcnf_enc_string (blk_map mfml)) (menc_vars mfml) UNIV
Proof
  rw[INJ_DEF]>>
  gvs[mcnf_enc_string_def,mlstringTheory.concat_def]>>
  `blk_num (blk_map mfml) x = blk_num (blk_map mfml) y` by (
    every_case_tac>>gvs[]>>
    metis_tac[mlintTheory.num_to_str_11])>>
  metis_tac[blk_num_INJ,INJ_DEF]
QED

Theorem full_encode_mcnf_nondom:
  full_encode_mcnf mfml = (objs,pbf) ⇒
  set_equiv ord (nondom_set ord (set pbf) objs) (nondom_costs ord mfml)
Proof
  rw[full_encode_mcnf_def]>>pairarg_tac>>gvs[LIST_TO_SET_MAP]>>
  DEP_REWRITE_TAC[GSYM nondom_set_INJ]>>simp[]>>
  drule mfml_to_pbf_nondom>>simp[]>>strip_tac>>
  irule INJ_SUBSET>>simp[]>>
  irule_at Any mcnf_enc_string_INJ>>
  drule mfml_to_pbf_vars>>
  simp[]
QED

(*** STEP 4: Build a parser for the command line interface ***)

Definition parse_mclause_def:
  parse_mclause ls =
  case ls of
    [] => NONE
  | INR _::_ => NONE
  | INL s::rs =>
    if s = «h» then
      (case parse_until_zero rs of
        SOME (cl,[]) => SOME (0,0,MAP mk_lit cl)
      | _ => NONE)
    else if s = «o» then
      (case rs of
        INR i::INR n::rs' =>
          if i > 0 ∧ n > 0 then
            (case parse_until_zero rs' of
              SOME (cl,[]) => SOME (Num i,Num n,MAP mk_lit cl)
            | _ => NONE)
          else NONE
      | _ => NONE)
    else NONE
End

Definition parse_mcnf_toks_def:
  (parse_mcnf_toks [] acc = SOME (REVERSE acc)) ∧
  (parse_mcnf_toks (s::ss) acc =
    if wnocomment_line s then
      case parse_mclause s of NONE => NONE
      | SOME l => parse_mcnf_toks ss (l::acc)
    else parse_mcnf_toks ss acc)
End

Definition parse_mcnf_def:
  parse_mcnf strs =
  let tokss = MAP syntax_helper$toks strs in
  parse_mcnf_toks tokss []
End

(*
  val mcnf =
  EVAL ``parse_mcnf
  [«c This is a comment»;
  «h 1 2 0»;
  «o 2 10 -3 4 5 0»;
  «o 1 3 -1 0»]``

  val enc = EVAL``full_encode_mcnf (THE ^(rconc mcnf))``
*)
