(*
   Specification of an LSR checker for CNF: proof steps, the check of one
   step, its soundness, and the parser for the binary LSR format.
*)
Theory lsr
Ancestors
  cnf ccnf syntax_helper dimacs mlstring mlvector sr
Libs
  preamble

(***
  The binary LSR proof format
 ***)

(* Both steps carry the raw variable-byte encoded bytes of the record they
  were read from, so that neither the deleted ids nor the hints are ever
  materialised *)
Datatype:
  lsr =
  | Delvb mlstring num
    (* Delvb s i : delete the clause ids encoded in s from offset i *)
  | Lsrvb num vcclause ((num # (bool + int)) list) mlstring
    (* Lsrvb n C w h : add C at id n with the witness w, the entries of
       the substitution in the order written; later entries win. h holds
       the global hints, then the groups, each a header -D followed by
       D's hints. *)
End

(* The witness substitution of an addition *)
Definition mk_subst_def:
  mk_subst (w:(num # (bool + int)) list) : subst = FEMPTY |++ w
End

(* The offset just after the first group header -j in h at or after
  offset i; NONE if there is none before the end of the record *)
Definition group_offset_def:
  group_offset h i len (j:num) =
  let (m,i') = parse_vb_int h i len in
  if m = 0 then NONE
  else if m = -&j then SOME i'
  else group_offset h i' len j
Termination
  WF_REL_TAC `measure (λ(h,i,len,j). len - i)` >>
  rw[] >>
  drule_then strip_assume_tac parse_vb_int_i >>
  gvs[]
End

(* The round for a clause D with id j and reduct D', on top of the map dm
  of the line: assume ¬D' and propagate with D's group, which must
  conflict, unless assuming ¬D' already contradicts dm *)
Definition check_red_def:
  check_red fml dm h i len j D' =
  case assume_neg dm D' of
    NONE => T
  | SOME dm' =>
    case group_offset h i len j of
      NONE => F
    | SOME k =>
      case unit_prop_vb_vec fml dm' h k len of
        SOME (NONE,_) => T
      | _ => F
End

(* A clause of the formula: satisfied or unmoved by σ, or its reduct is
  refuted by its round *)
Definition check_sr_def:
  check_sr fml dm σ h i len (j,D) =
  case classify σ (toList D) of
    Sat => T
  | Id => T
  | Red D' => check_red fml dm h i len j D'
End

(* The candidate itself: satisfied by σ, or its reduct is refuted by its
  round, also when σ leaves it unmoved *)
Definition check_cand_def:
  check_cand fml dm σ h i len n C ⇔
  EXISTS (λl. sub_lit σ l = INL T) (toList C) ∨
  check_red fml dm h i len n (reduct σ (toList C))
End

Definition check_lsr_def:
  check_lsr lsr fml =
  case lsr of
    Delvb s i =>
    SOME (delete_ids_vb fml s i (strlen s))
  | Lsrvb n C w h =>
    if n ∈ FDOM fml then NONE
    else
    let len = strlen h in
    case unit_prop_vb_vec fml (init_lit_map_vec (length C) C FEMPTY) h 0 len of
      NONE => NONE
    | SOME (NONE,_) => SOME (insert_vcc fml n C)
    | SOME (SOME i,dm) =>
      let σ = mk_subst w in
      if EVERY (check_sr fml dm σ h i len) (fmap_to_alist fml) ∧
         check_cand fml dm σ h i len n C
      then SOME (insert_vcc fml n C)
      else NONE
End

Definition check_lsrs_def:
  (check_lsrs [] fml = SOME fml) ∧
  (check_lsrs (x::xs) fml =
  case check_lsr x fml of
    NONE => NONE
  | SOME fml' => check_lsrs xs fml')
End

(***
  Soundness: every step preserves satisfiability
 ***)

(* No clause of the formula contains the literal 0 *)
Definition nz_vcfml_def:
  nz_vcfml fml ⇔ ∀C. C ∈ fml ⇒ ¬MEM 0 (toList C)
End

(* A witness entry maps a variable other than 0, and never to the
  literal 0 *)
Definition wf_entry_def:
  wf_entry ((v:num),(x:bool + int)) ⇔ v ≠ 0 ∧ x ≠ INR 0
End

(* The literals of a step are non-zero; the parser only produces such
  steps *)
Definition wf_lsr_def:
  (wf_lsr (Delvb s i) ⇔ T) ∧
  (wf_lsr (Lsrvb n C w h) ⇔
    ¬MEM 0 (toList C) ∧ EVERY wf_entry w)
End

Theorem mk_subst_wf:
  EVERY wf_entry w ⇒ wf_subst (mk_subst w)
Proof
  `∀w σ. wf_subst σ ∧ EVERY wf_entry w ⇒ wf_subst (σ |++ w)` by (
    Induct>>
    simp[FUPDATE_LIST_THM,FORALL_PROD,wf_entry_def]>>
    rw[]>>
    first_x_assum irule>>
    simp[]>>
    irule wf_subst_FUPDATE>>
    simp[])>>
  rw[mk_subst_def]>>
  first_x_assum irule>>
  simp[wf_subst_def]
QED

(* A round that passes refutes ¬D' on top of a map falsifying d *)
Theorem check_red_sound:
  check_red fml dm h i len j D' ∧
  lit_map d dm ∧ ¬satisfies_cclause w d ∧ ¬MEM 0 D' ∧
  satisfies_vcfml w (FRANGE fml) ⇒
  satisfies_cclause w D'
Proof
  rw[check_red_def]>>
  gvs[AllCasePreds()]
  >- metis_tac[assume_neg_NONE]>>
  drule_all assume_neg_SOME>>
  strip_tac>>
  drule_all unit_prop_vb_vec_conflict>>
  gvs[satisfies_cclause_def]>>
  metis_tac[]
QED

Theorem check_sr_sound:
  check_sr fml dm σ h i len (j,D) ∧
  wf_subst σ ∧ ¬MEM 0 (toList D) ∧ satisfies_cclause w (toList D) ∧
  lit_map d dm ∧ ¬satisfies_cclause w d ∧
  satisfies_vcfml w (FRANGE fml) ⇒
  EXISTS (λl. sub_lit σ l = INL T) (toList D) ∨
  satisfies_cclause w (reduct σ (toList D))
Proof
  rw[check_sr_def]>>
  gvs[AllCasePreds()]
  >- gvs[classify_Sat]
  >- (drule classify_Id>>simp[])>>
  drule classify_Red>>
  rw[]>>
  metis_tac[check_red_sound,reduct_nz]
QED

Theorem check_cand_sound:
  check_cand fml dm σ h i len n C ∧
  wf_subst σ ∧ ¬MEM 0 (toList C) ∧
  lit_map d dm ∧ ¬satisfies_cclause w d ∧
  satisfies_vcfml w (FRANGE fml) ⇒
  EXISTS (λl. sub_lit σ l = INL T) (toList C) ∨
  satisfies_cclause w (reduct σ (toList C))
Proof
  rw[check_cand_def]>>
  metis_tac[check_red_sound,reduct_nz]
QED

Theorem check_lsr_nz_vcfml:
  check_lsr lsr fml = SOME fml' ∧
  wf_lsr lsr ∧ nz_vcfml (FRANGE fml) ⇒
  nz_vcfml (FRANGE fml')
Proof
  rw[check_lsr_def]>>
  gvs[AllCaseEqs(),nz_vcfml_def,insert_vcc_def,wf_lsr_def]>>
  metis_tac[FRANGE_delete_ids_vb_SUBSET,FRANGE_DOMSUB_SUBSET,SUBSET_DEF]
QED

(* The map of a line's first step: every literal of the clause false *)
Theorem lit_map_init_lit_map_vec:
  ∀v. lit_map (toList v) (init_lit_map_vec (length v) v FEMPTY)
Proof
  Cases>>
  rename1`Vector ds`>>
  simp[length_def,toList_thm]>>
  qspecl_then [`LENGTH ds`,`Vector ds`,`FEMPTY`,`ds`] mp_tac init_lit_map_vec>>
  simp[]>>
  disch_then kall_tac>>
  `lit_map [] FEMPTY` by rw[lit_map_def]>>
  drule init_lit_map_lit_map>>
  disch_then (qspec_then`REVERSE ds` mp_tac)>>
  simp[]
QED

Theorem check_lsr_sound:
  check_lsr lsr fml = SOME fml' ∧
  wf_lsr lsr ∧ nz_vcfml (FRANGE fml) ∧
  satisfies_vcfml w (FRANGE fml) ⇒
  ∃w'. satisfies_vcfml w' (FRANGE fml')
Proof
  rw[check_lsr_def]>>
  gvs[AllCaseEqs(),insert_vcc_def]
  >- (
    qexists_tac`w`>>
    gvs[satisfies_vcfml_def,satisfies_fml_gen_delete_ids_vb])
  >- (
    rename1`wf_lsr (Lsrvb n vc wit h)`>>
    qexists_tac`w`>>
    `is_rup_vb fml vc h` by simp[is_rup_vb_def]>>
    drule_all is_rup_vb_sound>>
    gvs[satisfies_vcfml_def,satisfies_fml_gen_def]>>
    metis_tac[FRANGE_DOMSUB_SUBSET,SUBSET_DEF])>>
  rename1`wf_lsr (Lsrvb n vc wit h)`>>
  gvs[DOMSUB_NOT_IN_DOM]>>
  Cases_on`satisfies_vcclause w vc`
  >- (
    qexists_tac`w`>>
    gvs[satisfies_vcfml_def,satisfies_fml_gen_def]>>
    metis_tac[])>>
  `∃ds. vc = Vector ds` by (Cases_on`vc`>>simp[])>>
  gvs[wf_lsr_def,toList_thm,satisfies_vcclause_def,length_def]>>
  assume_tac (Q.SPEC`Vector ds` lit_map_init_lit_map_vec)>>
  gvs[toList_thm,length_def]>>
  drule_all unit_prop_vb_vec_no_conflict>>
  strip_tac>>
  qabbrev_tac`σ = mk_subst wit`>>
  `wf_subst σ` by simp[Abbr`σ`,mk_subst_wf]>>
  qexists_tac`apply_subst σ w`>>
  simp[satisfies_vcfml_eq]>>
  irule satisfies_cfml_apply_subst>>
  simp[PULL_EXISTS,toList_thm]>>
  rw[]
  >- simp[]
  >- gvs[nz_vcfml_def]
  >- (
    drule check_cand_sound>>
    simp[toList_thm]>>
    metis_tac[])>>
  gvs[FRANGE_FLOOKUP,EVERY_MEM,FORALL_PROD,MEM_pair_fmap_to_alist_FLOOKUP]>>
  first_x_assum drule>>
  strip_tac>>
  drule check_sr_sound>>
  gvs[satisfies_vcfml_def,satisfies_fml_gen_def,nz_vcfml_def,
      satisfies_vcclause_def,FRANGE_FLOOKUP,PULL_EXISTS]>>
  metis_tac[]
QED

Theorem check_lsrs_sound:
  ∀ls fml fml' w.
  check_lsrs ls fml = SOME fml' ∧
  EVERY wf_lsr ls ∧ nz_vcfml (FRANGE fml) ∧
  satisfies_vcfml w (FRANGE fml) ⇒
  ∃w'. satisfies_vcfml w' (FRANGE fml')
Proof
  Induct
  >- (simp[check_lsrs_def]>>metis_tac[])>>
  rw[check_lsrs_def]>>
  gvs[AllCaseEqs()]>>
  drule_all check_lsr_sound>>
  strip_tac>>
  drule_all check_lsr_nz_vcfml>>
  strip_tac>>
  first_x_assum drule_all>>
  simp[]
QED

Definition check_lsrs_unsat_def:
  check_lsrs_unsat ls fml =
  (case check_lsrs ls fml of
    NONE => F
  | SOME fml' => contains_emp fml')
End

Theorem check_lsrs_unsat_sound:
  check_lsrs_unsat ls (build_cfml cid cfml) ∧
  EVERY wf_lsr ls ∧ nz_vcfml (set cfml) ⇒
  ¬ ∃w.
    satisfies_vcfml w (set cfml)
Proof
  rw[check_lsrs_unsat_def]>>
  CCONTR_TAC>>
  gvs[AllCasePreds()]>>
  drule check_lsrs_sound>>
  simp[range_build_cfml]>>
  metis_tac[contains_emp_unsat]
QED

Theorem nz_vcfml_conv_cfml:
  EVERY (EVERY nz_lit) cfml ⇒ nz_vcfml (set (conv_cfml cfml))
Proof
  strip_tac>>
  gvs[nz_vcfml_def,conv_cfml_def,MEM_MAP,PULL_EXISTS,EVERY_MEM,
      toList_thm,to_cclause_def]>>
  metis_tac[to_ilit_NEQ_0]
QED

(* The checker's guarantee, phrased on the parsed formula rather than on
  the checker's internal representation *)
Theorem check_lsrs_unsat_conv_sound:
  EVERY (EVERY nz_lit) cfml ∧
  EVERY wf_lsr lsrs ∧
  check_lsrs_unsat lsrs (build_cfml cid (conv_cfml cfml)) ⇒
  unsatisfiable_cnf (set cfml)
Proof
  strip_tac>>
  drule_then assume_tac nz_vcfml_conv_cfml>>
  drule_all check_lsrs_unsat_sound>>
  simp[unsatisfiable_cnf_def,satisfiable_cnf_def]>>
  metis_tac[conv_cfml_sound]
QED

(***
  Parser for the binary LSR format.

  Records are variable-byte encoded and terminated by a zero byte. A
  deletion is one record, an addition two:

    4 <line id> <ids> 0      (dsr-trim)
    d <ids> 0                (CaDiCaL)
    3 <id> <clause> <witness> 0    <hints> <groups> 0      (dsr-trim)
    a <id> <clause> <witness> 0    <hints> <groups> 0      (CaDiCaL)

  The first record of an addition holds the clause and the witness: the
  clause runs up to the second occurrence of its first literal (the
  pivot), the literals mapped to ⊤ up to the third, and the pairs (v,l),
  mapping v to l, after it. The pivot is always mapped to ⊤.
 ***)

(* Reads the clause with pivot p: literals up to the next p, or up to the
  end of the record, which then has an empty witness. The result is in
  reverse order and ends with the pivot when acc = [p]. *)
Definition parse_vb_cl_def:
  parse_vb_cl (s:mlstring) (i:num) (len:num) (p:int) (acc:int list) =
  let (v,j) = parse_vb_int s i len in
  if v = 0 then (acc,len)
  else if v = p then (acc,j)
  else parse_vb_cl s j len p (v::acc)
Termination
  WF_REL_TAC` measure (λ(s,i,len,p,acc). len-i)`>>
  rw[]>>
  drule_then strip_assume_tac parse_vb_int_i>>
  gvs[]
End

(* The entry mapping the literal l to ⊤ *)
Definition top_entry_def:
  top_entry (l:int) = (Num (ABS l), (INL (l > 0) : bool + int))
End

(* The entries of the pairs (v,l), each mapping the literal v to l *)
Definition lsr_pairs_def:
  (lsr_pairs [] = SOME []) ∧
  (lsr_pairs [x] = NONE) ∧
  (lsr_pairs (v::l::rest) =
    case lsr_pairs rest of
      NONE => NONE
    | SOME ps => SOME ((Num (ABS v), INR (if v > 0 then l else -l)) :: ps))
End

(* The entries after the pivot's: the ⊤-literals up to the next pivot,
  then the pairs *)
Definition split_witness_def:
  split_witness (p:int) ls =
  let (tl,rest) = SPLITP (λl. l = p) ls in
  case rest of
    [] => SOME (MAP top_entry tl)
  | _::rest =>
    case lsr_pairs rest of
      NONE => NONE
    | SOME ps => SOME (MAP top_entry tl ++ ps)
End

Definition parse_lsr_chunk_def:
  parse_lsr_chunk s =
  if strlen s = 0 then NONE
  else
  let c = strsub_unsafe s 0 in
  let len = strlen s in
  if c = #"d"
  then SOME (INL (Delvb s 1))
  else if c = CHR 4
  then
    (* skip the line id *)
    let (m,i) = parse_vb_num s 1 len in
    SOME (INL (Delvb s i))
  else if c = #"a" ∨ c = CHR 3
  then
    let (m,i) = parse_vb_num s 1 len in
    if m = 0 ∨ m MOD 2 ≠ 0
    then NONE
    else
      let (p,i) = parse_vb_int s i len in
      if p = 0 then SOME (INR (m DIV 2, Vector [], []))
      else
        let (cl,i) = parse_vb_cl s i len p [p] in
        case split_witness p (parse_vb_ilits_fwd s i len) of
          NONE => NONE
        | SOME w => SOME (INR (m DIV 2, Vector cl, top_entry p :: w))
  else NONE
End

(* One step's worth of lines: NONE on a parse failure, SOME NONE at end
  of file, and otherwise the step together with the unread lines *)
Definition parse_lsr_one_def:
  parse_lsr_one lines =
  case lines of
    [] => SOME NONE
  | l::ls =>
    (case parse_lsr_chunk l of
      NONE => NONE
    | SOME (INL step) => SOME (SOME (step, ls))
    | SOME (INR (id,cl,w)) =>
      (case ls of
        [] => NONE
      | h::rest => SOME (SOME (Lsrvb id cl w h, rest))))
End

Theorem parse_lsr_one_LENGTH:
  parse_lsr_one lines = SOME (SOME (step,rest)) ⇒
  LENGTH rest < LENGTH lines
Proof
  rw[parse_lsr_one_def]>>
  gvs[AllCaseEqs()]
QED

Definition parse_lsrs_def:
  parse_lsrs lines =
  case parse_lsr_one lines of
    NONE => NONE
  | SOME NONE => SOME []
  | SOME (SOME (step,rest)) =>
    (case parse_lsrs rest of
      NONE => NONE
    | SOME ss => SOME (step :: ss))
Termination
  WF_REL_TAC` measure LENGTH`>>
  rw[]>>
  drule parse_lsr_one_LENGTH>>
  simp[]
End

(***
  Tests. Variable-byte numbers below 64 are one byte: 2v for v ≥ 0 and
  2|v|+1 for v < 0.
 ***)

(* A check over all clauses of a formula, one update at a time *)
Theorem EVERY_fmap_to_alist_FUPDATE:
  EVERY P (fmap_to_alist (fm |+ (k,v))) ⇔
  P (k,v) ∧ EVERY P (fmap_to_alist (fm \\ k))
Proof
  rw[EVERY_MEM,FORALL_PROD,MEM_pair_fmap_to_alist_FLOOKUP,
     FLOOKUP_UPDATE,DOMSUB_FLOOKUP_THM]>>
  rw[EQ_IMP_THM]>>
  gvs[AllCaseEqs()]>>
  metis_tac[]
QED

(* Evaluate check_lsrs on a concrete formula, after rewriting away the
  clause enumeration and the empty-clause test *)
val check_lsrs_tac =
  simp[check_lsrs_unsat_def,check_lsrs_def,build_cfml_def,build_fml_def]>>
  simp[check_lsr_def,insert_vcc_def,EVERY_fmap_to_alist_FUPDATE,
       DOMSUB_FUPDATE_THM,fmap_to_alist_FEMPTY,contains_emp_FRANGE,
       FRANGE_FUPDATE_DOMSUB]>>
  EVAL_TAC>>
  simp[FRANGE_FUPDATE_DOMSUB,DOMSUB_FUPDATE_THM];

val unsat4 = ``build_cfml 1
  [Vector [1;2]; Vector [-1;2]; Vector [1;-2]; Vector [-1;-2]]``;

(* A RAT step adding 2: clause 3 is satisfied by the map after the global
  hint 1, and clause 4 is refuted by its group [2]; then ⊥ by RUP *)
Theorem check_lsrs_test_rat[local]:
  check_lsrs_unsat
    [Lsrvb 5 (Vector [2]) [(2,INL T)] (implode [CHR 2; CHR 9; CHR 4]);
     Lsrvb 6 (Vector []) [] (implode [CHR 10; CHR 6; CHR 8])] ^unsat4
Proof
  check_lsrs_tac
QED

(* A RAT step with no group for the clauses it reduces is rejected,
  whatever the hints say *)
Theorem check_lsrs_test_no_groups[local]:
  check_lsrs [Lsrvb 3 (Vector [1]) [(1,INL T)] (implode [])]
    (build_cfml 1 [Vector [-1;2]; Vector [-1;-2]]) = NONE
Proof
  check_lsrs_tac
QED

(* A candidate left unmoved by the witness is refuted by its own round:
  without a group it is rejected, and with the group [1;2] accepted *)
Theorem check_lsrs_test_unmoved[local]:
  check_lsrs [Lsrvb 3 (Vector [1]) [] (implode [])]
    (build_cfml 1 [Vector [-1;2]; Vector [-1;-2]]) = NONE ∧
  check_lsrs [Lsrvb 5 (Vector [2]) [] (implode [CHR 11; CHR 2; CHR 4])]
    ^unsat4 ≠ NONE
Proof
  check_lsrs_tac
QED

(* A hint may not name the clause being added *)
Theorem check_lsrs_test_own_id[local]:
  check_lsrs [Lsrvb 2 (Vector [1]) [(1,INL T)] (implode [CHR 4])]
    (build_cfml 1 [Vector [1;2]]) = NONE
Proof
  check_lsrs_tac
QED

Theorem split_witness_test[local]:
  split_witness 1 [3;1;-2;5] = SOME [(3,INL T); (2,INR (-5))] ∧
  split_witness 1 [3] = SOME [(3,INL T)] ∧
  split_witness 1 [] = SOME [] ∧
  split_witness 1 [3;1;2] = NONE
Proof
  EVAL_TAC
QED

Theorem parse_lsr_chunk_test[local]:
  parse_lsr_chunk (implode [CHR 3; CHR 10; CHR 4]) =
    SOME (INR (5, Vector [2], [(2,INL T)])) ∧
  parse_lsr_chunk (implode [CHR 3; CHR 10; CHR 3]) =
    SOME (INR (5, Vector [-1], [(1,INL F)])) ∧
  parse_lsr_chunk (implode [CHR 3; CHR 12]) =
    SOME (INR (6, Vector [], [])) ∧
  parse_lsr_chunk
    (implode [#"a"; CHR 10; CHR 2; CHR 4; CHR 2; CHR 6; CHR 2; CHR 5; CHR 10]) =
    SOME (INR (5, Vector [2;1], [(1,INL T); (3,INL T); (2,INR (-5))])) ∧
  parse_lsr_chunk (implode [#"a"; CHR 10; CHR 2; CHR 2; CHR 2; CHR 4]) =
    NONE ∧
  parse_lsr_chunk (implode [CHR 4; CHR 14; CHR 2; CHR 4]) =
    SOME (INL (Delvb (implode [CHR 4; CHR 14; CHR 2; CHR 4]) 2)) ∧
  parse_lsr_chunk (implode [#"d"; CHR 2]) =
    SOME (INL (Delvb (implode [#"d"; CHR 2]) 1))
Proof
  EVAL_TAC
QED

Theorem parse_vb_cl_nz:
  ∀s i len p acc.
  ¬MEM 0 acc ⇒ ¬MEM 0 (FST (parse_vb_cl s i len p acc))
Proof
  ho_match_mp_tac parse_vb_cl_ind>>
  rw[]>>
  simp[Once parse_vb_cl_def]>>
  pairarg_tac>>
  rw[]
QED

Theorem top_entry_wf:
  l ≠ 0 ⇒ wf_entry (top_entry l)
Proof
  rw[top_entry_def,wf_entry_def]>>
  intLib.ARITH_TAC
QED

Theorem lsr_pairs_wf:
  ∀ls w. lsr_pairs ls = SOME w ∧ ¬MEM 0 ls ⇒ EVERY wf_entry w
Proof
  ho_match_mp_tac lsr_pairs_ind>>
  rw[lsr_pairs_def]>>
  gvs[AllCaseEqs(),wf_entry_def]
QED

Theorem split_witness_wf:
  split_witness p ls = SOME w ∧ ¬MEM 0 ls ⇒ EVERY wf_entry w
Proof
  rw[split_witness_def]>>
  pairarg_tac>>gvs[]>>
  imp_res_tac SPLITP_JOIN>>
  gvs[AllCaseEqs(),EVERY_MAP]>>
  gvs[EVERY_MEM]>>
  metis_tac[top_entry_wf,lsr_pairs_wf,EVERY_MEM]
QED

Theorem parse_lsr_one_wf_lsr:
  parse_lsr_one lines = SOME (SOME (step,rest)) ⇒ wf_lsr step
Proof
  rw[parse_lsr_one_def,AllCaseEqs()]>>
  gvs[parse_lsr_chunk_def,AllCaseEqs(),wf_lsr_def]>>
  rpt (pairarg_tac>>gvs[AllCaseEqs(),wf_lsr_def])>>
  rw[toList_thm,top_entry_wf]>>
  metis_tac[parse_vb_cl_nz,FST,MEM,split_witness_wf,parse_vb_ilits_fwd_nz]
QED

Theorem parse_lsrs_wf_lsr:
  ∀lines ss.
  parse_lsrs lines = SOME ss ⇒ EVERY wf_lsr ss
Proof
  ho_match_mp_tac parse_lsrs_ind>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once parse_lsrs_def]>>
  rw[AllCaseEqs()]>>
  simp[]>>
  metis_tac[parse_lsr_one_wf_lsr]
QED
