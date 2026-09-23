(*
  Multi-objective MaxSAT (MCNF) into pbc, written in a tutorial style
*)
Theory mcnf_to_pb
Ancestors
  pbc pbc_normalise pbc_mo cnf syntax_helper cnf_to_pb wcnf_to_pb
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

(* The constraints contributed by one tagged clause.
  Soft clauses of length > 1 get a blocking variable keyed by the
  global line index, which keeps the blocking namespace injective. *)
Definition mclause_cs_def:
  mclause_cs ((idx:num),((i,n,C):mcclause)) =
  let C = canon_clause C in
  if i = 0 then [(PGe,enc_clause C,1:int)]
  else if LENGTH C = 1 then []
  else [(PGe,(1,pbc$Neg (INR idx)) :: enc_clause C,1:int)]
End

(* The terms contributed by one tagged clause to objective k *)
Definition mclause_obj_def:
  mclause_obj (k:num) ((idx:num),((i,n,C):mcclause)) =
  if i ≠ k then []
  else
    let C = canon_clause C in
    if LENGTH C = 1 then [((&n:int), negate (enc_lit (HD C)))]
    else [((&n:int),pbc$Neg (INR idx))]
End

Definition mfml_to_pbf_def:
  mfml_to_pbf (mfml:mccnf) =
  let ls = enumerate 1 mfml in
  let pbf = FLAT (MAP mclause_cs ls) in
  let objs =
    MAP (λk. (FLAT (MAP (mclause_obj k) ls),0:int))
      (GENLIST SUC (num_objs mfml)) in
  (objs,pbf)
End

(* The end-to-end encoder using string names *)
Definition full_encode_mcnf_def:
  full_encode_mcnf (mfml:mccnf) =
  let (objs,pbf) = mfml_to_pbf mfml in
  (map_objs enc_string objs,
   MAP (map_pbc enc_string) pbf)
End

(*** STEP 3: Prove correctness of the encoding ***)

Theorem cost_obj_obj_upper:
  ∀mfml j.
  0 < k ∧
  satisfies w (set (FLAT (MAP mclause_cs (enumerate j mfml)))) ⇒
  &(cost_obj k (λx. w (INL x)) mfml) ≤
  eval_lin_term w (FLAT (MAP (mclause_obj k) (enumerate j mfml)))
Proof
  (Induct>>rw[cost_obj_def]
  >- EVAL_TAC)>>
  gvs[miscTheory.enumerate_def,pbcTheory.satisfies_simp]>>
  first_x_assum drule>>simp[cost_obj_def]>>strip_tac>>
  PairCases_on`h`>>
  qsuff_tac`&(weight_mclause k (λx. w (INL x)) (h0,h1,h2)) ≤
    eval_lin_term w (mclause_obj k (j,h0,h1,h2))`
  >- intLib.ARITH_TAC>>
  simp[mclause_obj_def,weight_mclause_def]>>
  Cases_on`h0 = k`>>simp[]>>gvs[]>>
  qmatch_goalsub_abbrev_tac`LENGTH C = 1`>>
  `satisfies_clause (λx. w (INL x)) h2 ⇔
   satisfies_clause (λx. w (INL x)) C` by simp[Abbr`C`]>>
  gvs[mclause_cs_def]>>
  Cases_on`LENGTH C = 1`>>
  gvs[pbcTheory.satisfies_simp,pbcTheory.satisfies_pbc_plain]
  >- (
    (* a unit soft clause is charged through its negated literal *)
    `∃l. C = [l]` by (Cases_on`C`>>gvs[LENGTH_EQ_NUM_compute])>>
    gvs[satisfies_clause_def,o_DEF]>>
    IF_CASES_TAC>>simp[])>>
  (* every other soft clause is charged through its blocking variable *)
  IF_CASES_TAC
  >- (
    `¬ w (INR j)` by (
      CCONTR_TAC>>gvs[]>>
      `eval_lin_term w (enc_clause C) ≥ 1` by intLib.ARITH_TAC>>
      drule satisfies_pbc_satisfies_clause>>
      gvs[o_DEF])>>
    simp[])>>
  Cases_on`w (INR j)`>>simp[]
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
    gvs[MEM_EL]>>
    first_x_assum(qspecl_then[
      `(PGe,enc_clause (canon_clause C),1i)`,
      `(n'+1,0,n,C)`] mp_tac)>>
    impl_tac >- (
      simp[mclause_cs_def,MEM_EL,LENGTH_enumerate]>>
      qexists_tac`n'`>>
      DEP_REWRITE_TAC[EL_enumerate]>>simp[])>>
    simp[pbcTheory.satisfies_pbc_plain]>>strip_tac>>
    drule satisfies_pbc_satisfies_clause>>
    simp[o_DEF])>>
  simp[cost_vec_def,obj_vecs_def,MAP_MAP_o,o_DEF,vec_le_MAP,EVERY_MEM,
    MEM_GENLIST,PULL_EXISTS,pbcTheory.eval_obj_def]>>
  rw[]>>irule cost_obj_obj_upper>>simp[]
QED

Theorem cost_obj_obj_eq:
  ∀mfml j.
  (∀x. ww (INL x) = w x) ∧
  (∀y. y ≥ j ⇒ (ww (INR y) ⇔ satisfies_clause w (SND (SND (EL (y - j) mfml))))) ⇒
  eval_lin_term ww (FLAT (MAP (mclause_obj k) (enumerate j mfml))) =
  &(cost_obj k w mfml)
Proof
  (Induct>>rw[cost_obj_def]
  >- EVAL_TAC)>>
  gvs[miscTheory.enumerate_def]>>
  last_x_assum(qspec_then`j+1` mp_tac)>>
  (impl_tac >- (
    rw[]>>
    first_x_assum(qspec_then`y` mp_tac)>>
    simp[]>>
    `y - j = SUC (y - (j+1))` by simp[]>>
    simp[]))>>
  simp[cost_obj_def]>>strip_tac>>
  PairCases_on`h`>>
  (qsuff_tac`eval_lin_term ww (mclause_obj k (j,h0,h1,h2)) =
    &(weight_mclause k w (h0,h1,h2))`
  >- intLib.ARITH_TAC)>>
  `ww (INR j) ⇔ satisfies_clause w h2` by (
    first_x_assum(qspec_then`j` mp_tac)>>simp[])>>
  simp[mclause_obj_def,weight_mclause_def]>>
  Cases_on`h0 = k`>>simp[]>>gvs[]>>
  qmatch_goalsub_abbrev_tac`LENGTH C = 1`>>
  `satisfies_clause w h2 ⇔ satisfies_clause w C` by simp[Abbr`C`]>>
  (Cases_on`LENGTH C = 1`>>gvs[]
  >- (
    `∃l. C = [l]` by (Cases_on`C`>>gvs[LENGTH_EQ_NUM_compute])>>
    `ww o INL = w` by simp[FUN_EQ_THM]>>
    gvs[satisfies_clause_def]>>
    IF_CASES_TAC>>simp[]))>>
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
  qexists_tac`λv.
    case v of
      INL x => w x
    | INR y => satisfies_clause w (SND (SND (EL (y - 1) mfml)))`>>
  `∀i e. MEM (i,e) (enumerate 1 mfml) ⇒ EL (i-1) mfml = e` by (
    rw[MEM_EL,LENGTH_enumerate]>>
    gvs[EL_enumerate])>>
  CONJ_TAC >- (
    qmatch_goalsub_abbrev_tac`satisfies ww _`>>
    `∀x. ww (INL x) ⇔ w x` by simp[Abbr`ww`]>>
    `∀y. ww (INR y) ⇔ satisfies_clause w (SND (SND (EL (y-1) mfml)))` by
      simp[Abbr`ww`]>>
    rw[pbcTheory.satisfies_def,MEM_FLAT,MEM_MAP,PULL_EXISTS]>>
    PairCases_on`y`>>
    `MEM (y1,y2,y3) mfml` by metis_tac[MEM_enumerate_IMP]>>
    first_x_assum drule>>strip_tac>>
    simp[]>>
    qabbrev_tac`C = canon_clause y3`>>
    `satisfies_clause w y3 ⇔ satisfies_clause w C` by simp[Abbr`C`]>>
    `satisfies_clause w C ⇒ eval_lin_term ww (enc_clause C) ≥ 1` by (
      strip_tac>>
      irule satisfies_clause_satisfies_pbc>>
      simp[]>>qexists_tac`w`>>
      gvs[])>>
    gvs[mclause_cs_def]>>
    (Cases_on`y1 = 0`>>gvs[]
    >- (
      `satisfies_clause w y3` by metis_tac[msat_hard_def]>>
      gvs[pbcTheory.satisfies_pbc_plain]))>>
    Cases_on`LENGTH C = 1`>>gvs[]>>
    simp[pbcTheory.satisfies_pbc_plain]>>
    `eval_lin_term ww (enc_clause C) ≥ 0` by
      metis_tac[eval_lin_term_enc_clause_ge0]>>
    Cases_on`satisfies_clause w C`>>gvs[]>>
    intLib.ARITH_TAC)>>
  simp[obj_vecs_def,cost_vec_def,MAP_MAP_o,o_DEF,MAP_EQ_f,MEM_GENLIST,
    PULL_EXISTS,pbcTheory.eval_obj_def]>>
  rw[]>>
  irule cost_obj_obj_eq>>
  rw[]>>
  `y - 1 = y - 1` by simp[]>>
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

Theorem full_encode_mcnf_nondom:
  full_encode_mcnf mfml = (objs,pbf) ⇒
  set_equiv ord (nondom_set ord (set pbf) objs) (nondom_costs ord mfml)
Proof
  rw[full_encode_mcnf_def]>>pairarg_tac>>gvs[LIST_TO_SET_MAP]>>
  DEP_REWRITE_TAC[GSYM nondom_set_INJ]>>simp[]>>
  drule mfml_to_pbf_nondom>>simp[]>>strip_tac>>
  irule INJ_SUBSET>>simp[]>>
  irule_at Any enc_string_INJ>>
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
