(*
  Substitution redundancy (SR) for CNF clauses.

  A clause C is substitution-redundant w.r.t. a formula F if some
  substitution σ has F ∧ ¬C ⊢₁ (F ∧ C)|σ. Then every model w of F that
  falsifies C gives the model w ∘ σ of F ∧ C, so adding C preserves
  satisfiability (but not models).
*)
Theory sr
Ancestors
  cnf ccnf mlvector
Libs
  preamble

(* A substitution maps a variable to a truth value (INL) or to a literal
  (INR); variables outside its domain are left alone *)
Type subst = ``:num |-> bool + int``;

(* A substitution read from a witness of non-zero literals: it never
  maps variable 0 and never maps to the literal 0 *)
Definition wf_subst_def:
  wf_subst (σ:subst) ⇔
    0 ∉ FDOM σ ∧ ∀v m. FLOOKUP σ v = SOME (INR m) ⇒ m ≠ 0
End

Theorem wf_subst_FUPDATE:
  wf_subst σ ∧ v ≠ 0 ∧ (∀m. x = INR m ⇒ m ≠ 0) ⇒
  wf_subst (σ |+ (v,x))
Proof
  rw[wf_subst_def,FLOOKUP_UPDATE]>>
  rw[]>>
  metis_tac[]
QED

(* The image of a literal: σ(¬x) = ¬σ(x) *)
Definition sub_lit_def:
  sub_lit (σ:subst) (l:int) : bool + int =
  case FLOOKUP σ (Num (ABS l)) of
    NONE => INR l
  | SOME (INL b) => INL (if l < 0 then ¬b else b)
  | SOME (INR m) => INR (if l < 0 then -m else m)
End

(* w ∘ σ *)
Definition apply_subst_def:
  apply_subst (σ:subst) (w:num -> bool) n =
  case FLOOKUP σ n of
    NONE => w n
  | SOME (INL b) => b
  | SOME (INR m) => satisfies_ilit w m
End

(* D|σ: the images of D's literals that are literals; a literal mapped
  to ⊥ drops out *)
Definition reduct_def:
  reduct σ D = MAP OUTR (FILTER ISR (MAP (sub_lit σ) D))
End

Theorem satisfies_ilit_apply_subst:
  wf_subst σ ∧ l ≠ 0 ⇒
  (satisfies_ilit (apply_subst σ w) l ⇔
    case sub_lit σ l of
      INL b => b
    | INR m => satisfies_ilit w m)
Proof
  rw[wf_subst_def]>>
  `l < 0 ⇔ ¬(l > 0)` by intLib.ARITH_TAC>>
  simp[Once satisfies_ilit_ABS,apply_subst_def,sub_lit_def]>>
  Cases_on`FLOOKUP σ (Num (ABS l))`>>simp[]
  >- simp[satisfies_ilit_ABS]>>
  rename1`SOME x`>>Cases_on`x`>>simp[]
  >- rw[]>>
  rename1`INR m`>>
  `m ≠ 0` by (strip_tac>>gvs[])>>
  rw[satisfies_ilit_neg]
QED

Theorem reduct_CONS:
  reduct σ (l::D) =
  case sub_lit σ l of
    INL _ => reduct σ D
  | INR m => m :: reduct σ D
Proof
  simp[reduct_def]>>
  Cases_on`sub_lit σ l`>>simp[]
QED

Theorem reduct_nz:
  wf_subst σ ∧ ¬MEM 0 D ⇒ ¬MEM 0 (reduct σ D)
Proof
  rw[wf_subst_def]>>
  Induct_on`D`
  >- simp[reduct_def]>>
  rw[reduct_CONS]>>
  Cases_on`sub_lit σ h`>>simp[]>>
  gvs[sub_lit_def,AllCaseEqs()]>>
  rw[]>>
  strip_tac>>gvs[]
QED

(* w ∘ σ satisfies D iff σ maps some literal of D to ⊤ or w satisfies D|σ *)
Theorem satisfies_cclause_apply_subst:
  wf_subst σ ∧ ¬MEM 0 D ⇒
  (satisfies_cclause (apply_subst σ w) D ⇔
    EXISTS (λl. sub_lit σ l = INL T) D ∨
    satisfies_cclause w (reduct σ D))
Proof
  Induct_on`D`
  >- simp[reduct_def,satisfies_cclause_def]>>
  gvs[satisfies_cclause_CONS]>>
  rw[]>>
  drule_all satisfies_ilit_apply_subst>>
  disch_then (qspec_then`w` SUBST1_TAC)>>
  Cases_on`sub_lit σ h`>>
  simp[reduct_CONS,satisfies_cclause_CONS]>>
  metis_tac[]
QED

(* How a clause fares under σ: satisfied (some literal maps to ⊤),
  unmoved (every literal maps to itself), or reduced to D|σ *)
Datatype:
  sr_class = Sat | Id | Red (int list)
End

Definition classify_def:
  classify σ D =
  if EXISTS (λl. sub_lit σ l = INL T) D then Sat
  else if EVERY (λl. sub_lit σ l = INR l) D then Id
  else Red (reduct σ D)
End

Theorem classify_Sat:
  classify σ D = Sat ⇔ EXISTS (λl. sub_lit σ l = INL T) D
Proof
  rw[classify_def]
QED

Theorem classify_Red:
  classify σ D = Red D' ⇒ D' = reduct σ D
Proof
  rw[classify_def]
QED

Theorem classify_Id:
  classify σ D = Id ⇒ reduct σ D = D
Proof
  rw[classify_def]>>
  qpat_x_assum`EVERY _ _`mp_tac>>
  rpt (pop_assum kall_tac)>>
  Induct_on`D`
  >- simp[reduct_def]>>
  simp[reduct_CONS]
QED

(* l is true under an assignment map dm. As in the core, dm maps a
  variable to T when its positive literal is assigned false *)
Definition lit_true_def:
  lit_true dm (l:int) ⇔ FLOOKUP dm (Num (ABS l)) = SOME (l < 0)
End

(* Assume ¬D on top of dm. NONE when that is contradictory without any
  propagation: some literal of D is already true under dm, or D contains
  a literal and its negation. The result does not depend on the order of
  D's literals. *)
Definition assume_neg_def:
  assume_neg dm (D:int list) =
  if EXISTS (lit_true dm) D ∨ EXISTS (λl. MEM (-l) D) D
  then NONE
  else SOME (init_lit_map D dm)
End

Theorem assume_neg_NONE:
  assume_neg dm D = NONE ∧
  lit_map d dm ∧ ¬satisfies_cclause w d ∧
  ¬MEM 0 D ⇒
  satisfies_cclause w D
Proof
  rw[assume_neg_def,EXISTS_MEM]>>
  gvs[satisfies_cclause_def,EVERY_MEM]
  >- (
    rename1`lit_true dm l`>>
    `l ≠ 0` by (strip_tac>>gvs[])>>
    `MEM (-l) d` by (
      gvs[lit_map_def,lit_true_def]>>
      first_x_assum drule>>
      Cases_on`l < 0`>>simp[]
      >- (`&Num (ABS l) = -l` by intLib.ARITH_TAC>>simp[])>>
      `-&Num (ABS l) = -l` by intLib.ARITH_TAC>>simp[])>>
    metis_tac[satisfies_ilit_neg])>>
  rename1`MEM (-l) D`>>
  `l ≠ 0` by (strip_tac>>gvs[])>>
  metis_tac[satisfies_ilit_neg]
QED

Theorem assume_neg_SOME:
  assume_neg dm D = SOME dm' ∧
  lit_map d dm ⇒
  lit_map (d ++ D) dm'
Proof
  rw[assume_neg_def]>>
  metis_tac[init_lit_map_lit_map]
QED

Theorem Num_ABS_11:
  Num (ABS a) = Num (ABS b) ⇔ a = b ∨ a = -b
Proof
  intLib.ARITH_TAC
QED

(* Without a complementary pair, assuming ¬D maps each variable of D to
  whether a positive literal of it occurs, and leaves the others alone *)
Theorem FLOOKUP_init_lit_map:
  ∀D dm n.
  ¬EXISTS (λl. MEM (-l) D) D ⇒
  FLOOKUP (init_lit_map D dm) n =
  if ∃d. MEM d D ∧ Num (ABS d) = n
  then SOME (∃d. MEM d D ∧ Num (ABS d) = n ∧ d > 0)
  else FLOOKUP dm n
Proof
  Induct
  >- simp[init_lit_map_def]>>
  rpt strip_tac>>
  `¬EXISTS (λl. MEM (-l) D) D` by (gvs[EXISTS_MEM,EVERY_MEM]>>metis_tac[])>>
  simp[init_lit_map_def]>>
  first_x_assum drule>>
  disch_then (qspecl_then [`dm |+ (Num (ABS h),h > 0)`,`n`] SUBST1_TAC)>>
  Cases_on`∃d. MEM d D ∧ Num (ABS d) = n`>>
  asm_simp_tac std_ss [FLOOKUP_UPDATE]
  >- (
    `Num (ABS h) = n ⇒ MEM h D` by (
      rw[]>>
      gvs[Num_ABS_11])>>
    reverse IF_CASES_TAC
    >- metis_tac[]>>
    simp[]>>
    metis_tac[])>>
  rw[]>>
  metis_tac[]
QED

Theorem assume_neg_PERM:
  PERM D1 D2 ⇒ assume_neg dm D1 = assume_neg dm D2
Proof
  strip_tac>>
  `∀l. MEM l D1 ⇔ MEM l D2` by metis_tac[MEM_PERM]>>
  `∀P. EXISTS P D1 ⇔ EXISTS P D2` by metis_tac[EXISTS_MEM]>>
  simp[assume_neg_def]>>
  rw[fmap_eq_flookup]>>
  DEP_REWRITE_TAC[FLOOKUP_init_lit_map]>>
  gvs[EVERY_MEM]
QED

(* Assuming ¬D one literal at a time: a true literal ends it, a false one
  changes nothing, and an unassigned one is assigned false *)
Theorem assume_neg_CONS_true:
  lit_true dm m ⇒ assume_neg dm (m::R) = NONE
Proof
  rw[assume_neg_def]
QED

Theorem assume_neg_CONS_false:
  m ≠ 0 ∧ FLOOKUP dm (Num (ABS m)) = SOME (m > 0) ⇒
  assume_neg dm (m::R) = assume_neg dm R
Proof
  strip_tac>>
  `Num (ABS (-m)) = Num (ABS m)` by intLib.ARITH_TAC>>
  `¬lit_true dm m ∧ lit_true dm (-m)` by (
    simp[lit_true_def]>>
    intLib.ARITH_TAC)>>
  `dm |+ (Num (ABS m), m > 0) = dm` by (
    irule FUPDATE_ELIM>>
    gvs[FLOOKUP_DEF])>>
  `-m ≠ m` by intLib.ARITH_TAC>>
  rw[assume_neg_def,init_lit_map_def]>>
  gvs[EXISTS_MEM,EVERY_MEM]
QED

(* Assigning the unassigned m false makes exactly ¬m true in addition *)
Theorem lit_true_assume:
  m ≠ 0 ∧ FLOOKUP dm (Num (ABS m)) = NONE ⇒
  (lit_true (dm |+ (Num (ABS m), m > 0)) l ⇔ lit_true dm l ∨ l = -m)
Proof
  rw[lit_true_def,FLOOKUP_UPDATE]
  >- (gvs[Num_ABS_11]>>intLib.ARITH_TAC)>>
  Cases_on`l = -m`>>gvs[]
QED

Theorem assume_neg_CONS_unassigned:
  m ≠ 0 ∧ FLOOKUP dm (Num (ABS m)) = NONE ⇒
  assume_neg dm (m::R) = assume_neg (dm |+ (Num (ABS m), m > 0)) R
Proof
  strip_tac>>
  `∀l. lit_true (dm |+ (Num (ABS m), m > 0)) l ⇔ lit_true dm l ∨ l = -m`
    by simp[lit_true_assume]>>
  `¬lit_true dm m` by simp[lit_true_def]>>
  `-m ≠ m` by intLib.ARITH_TAC>>
  rw[assume_neg_def,init_lit_map_def]>>
  gvs[EXISTS_MEM,EVERY_MEM]>>
  metis_tac[integerTheory.INT_NEG_NEG]
QED

(* Unit propagation over vb-encoded hints, read as a statement about the
  clause d falsified by the map *)
Theorem unit_prop_vb_vec_conflict:
  unit_prop_vb_vec fml dm s i len = SOME (NONE,dm') ∧
  lit_map d dm ∧
  satisfies_vcfml w (FRANGE fml) ⇒
  satisfies_cclause w d
Proof
  strip_tac>>
  drule unit_prop_vb_vec>>
  strip_tac>>
  `satisfies_vcclause w (Vector d)` by (
    irule $ INST_TYPE[alpha |-> numSyntax.num] unit_prop_vec_SOME_T>>
    gvs[toList_thm]>>
    metis_tac[])>>
  gvs[satisfies_vcclause_def,toList_thm]
QED

Theorem unit_prop_vb_vec_no_conflict:
  unit_prop_vb_vec fml dm s i len = SOME (SOME j,dm') ∧
  lit_map d dm ∧ ¬satisfies_cclause w d ∧
  satisfies_vcfml w (FRANGE fml) ⇒
  ∃d'. lit_map d' dm' ∧ ¬satisfies_cclause w d'
Proof
  strip_tac>>
  drule unit_prop_vb_vec>>
  strip_tac>>
  gvs[]>>
  drule_at (Pos (el 2)) $ INST_TYPE[alpha |-> numSyntax.num] unit_prop_vec_SOME_F>>
  disch_then (qspecl_then [`w`,`Vector d`] mp_tac)>>
  simp[toList_thm,satisfies_vcclause_def]>>
  metis_tac[]
QED

(* The SR argument: if w satisfies the reduct of every clause of a
  formula that σ does not satisfy, then w ∘ σ satisfies the formula. The
  SR check establishes the premise for F ∧ C under every model of F that
  falsifies C. *)
Theorem satisfies_cfml_apply_subst:
  wf_subst σ ∧
  (∀D. D ∈ fml ⇒ ¬MEM 0 D) ∧
  (∀D. D ∈ fml ⇒
    EXISTS (λl. sub_lit σ l = INL T) D ∨
    satisfies_cclause w (reduct σ D)) ⇒
  satisfies_cfml (apply_subst σ w) fml
Proof
  rw[satisfies_cfml_def,satisfies_fml_gen_def]>>
  metis_tac[satisfies_cclause_apply_subst]
QED
