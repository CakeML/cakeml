(*
  Formalisation of a flexible surface syntax and semantics for
  pseudo-boolean constraint (un-normalised) with 'a var type
*)
open preamble mlintTheory;

val _ = new_theory "pbc";

val _ = numLib.temp_prefer_num();

Datatype:
  lit = Pos 'a | Neg 'a
End

(*
  Pseudo-boolean constraints have the form:
  c_i l_i ≥ n
  c_i l_i = n
  c_i l_i > n
  c_i l_i ≤ n
  c_i l_i < n
  where coefficients c_i and n are arbitrary integers and l_i are literals

  All of these will be normalized to ≥ constraints
*)

(* A linear term over variables *)
Type lin_term = ``:(int # 'a lit) list``;

Datatype:
  pbop = Equal | GreaterEqual | Greater | LessEqual | Less
End

Type pbc = ``:(pbop # 'a lin_term # int)``

(* 0-1 integer-valued semantics *)
Definition b2i_def[simp]:
  b2i T = 1i ∧
  b2i F = 0i
End

Definition eval_lit_def[simp]:
  eval_lit w (Pos v) =     b2i (w v) ∧
  eval_lit w (Neg v) = 1 - b2i (w v)
End

Definition negate_def[simp]:
  negate (Pos n) = Neg n ∧
  negate (Neg n) = Pos n
End

Definition eval_term_def[simp]:
  eval_term w (c,l) = c * eval_lit w l
End

Definition iSUM_def:
  (iSUM [] = 0:int) ∧
  (iSUM (x::xs) = x + iSUM xs)
End

Definition eval_lin_term_def:
  eval_lin_term w (xs:'a lin_term) = iSUM (MAP (eval_term w) xs)
End

Definition do_op_def[simp]:
  (do_op Equal (l:int) (r:int) ⇔ l = r) ∧
  (do_op GreaterEqual l r ⇔ l ≥ r) ∧
  (do_op Greater l r ⇔ l > r) ∧
  (do_op LessEqual l r ⇔ l ≤ r) ∧
  (do_op Less l r ⇔ l < r)
End

(* satisfaction of a pseudo-boolean constraint *)
Definition satisfies_pbc_def:
  (satisfies_pbc w (pbop,xs,n) ⇔
    do_op pbop (eval_lin_term w xs) n)
End

(* satisfaction of a set of constraints *)
Definition satisfies_def:
  satisfies w pbf ⇔
  ∀c. c ∈ pbf ⇒ satisfies_pbc w c
End

Definition satisfiable_def:
  satisfiable pbf ⇔
  ∃w. satisfies w pbf
End

Definition unsatisfiable_def:
  unsatisfiable pbf ⇔ ¬satisfiable pbf
End

(* Optimality of an assignment wrt an affine term *)
Definition optimal_def:
  optimal w pbf f ⇔
    satisfies w pbf ∧
    ∀w'.
      satisfies w' pbf ⇒ eval_lin_term w f ≤ eval_lin_term w' f
End

Definition optimal_val_def:
  optimal_val pbf (f,c) =
    if satisfiable pbf then
      SOME (eval_lin_term (@w. optimal w pbf f) f + c)
    else
      NONE
End

Theorem NUM_LE:
  0 ≤ x ∧ 0 ≤ y ⇒
  (Num x ≤ Num y ⇔ x ≤ y)
Proof
  intLib.ARITH_TAC
QED

Theorem optimal_exists:
  satisfies w pbf ⇒
  ∃w'.
    optimal w' pbf f
Proof
  rw[]>>
  qabbrev_tac`solns = {w | satisfies w pbf}`>>
  qabbrev_tac`(mv:int) =
    iSUM (MAP (λ(c,l). if c < 0 then c else 0) f)`>>
  qabbrev_tac`objs = IMAGE (λw. Num (eval_lin_term w f - mv)) solns`>>
  qabbrev_tac`opt = MIN_SET objs`>>

  `objs ≠ {}` by (
    unabbrev_all_tac>>
    fs[EXTENSION]>>
    metis_tac[])>>
  drule MIN_SET_LEM>>
  rw[]>>
  unabbrev_all_tac>>fs[]>>
  qexists_tac`w'`>>
  fs[optimal_def,PULL_EXISTS]>>rw[]>>
  first_x_assum drule>>
  rw[]>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC [NUM_LE]>>
  simp[]>>
  `∀w f. 0 ≤
   eval_lin_term w f -
   iSUM (MAP (λ(c,l). if c < 0 then c else 0) f)` by
    (rpt(pop_assum kall_tac)>>
    strip_tac>>Induct>>
    fs[eval_lin_term_def]>>rw[iSUM_def]>>
    Cases_on`h`>>rw[]>>
    Cases_on`r`>>fs[]>>
    Cases_on`w a`>>fs[]>>
    intLib.ARITH_TAC)>>
  simp[]>>
  pop_assum kall_tac>>
  intLib.ARITH_TAC
QED

Theorem optimal_obj_eq:
  optimal w pbf f ∧
  optimal w' pbf f ⇒
  eval_lin_term w f =
  eval_lin_term w' f
Proof
  rw[optimal_def]>>
  last_x_assum drule>>
  qpat_x_assum`_ w' _` kall_tac>>
  first_x_assum drule>>
  intLib.ARITH_TAC
QED

Theorem optimal_optimal_val:
  optimal w pbf f ⇒
  optimal_val pbf (f,c) = SOME (eval_lin_term w f + c)
Proof
  rw[]>>
  drule optimal_obj_eq>>
  rw[optimal_val_def]
  >- (
    fs[satisfiable_def,optimal_def]>>
    metis_tac[])>>
  `optimal (@w. optimal w pbf f) pbf f` by
    metis_tac[SELECT_AX]>>
  metis_tac[]
QED

Theorem optimal_witness:
  satisfies w pbf ∧
  unsatisfiable (
    (Less,f,(eval_lin_term w f)) INSERT pbf) ⇒
  optimal_val pbf (f,c) = SOME (eval_lin_term w f + c)
Proof
  rw[]>>
  match_mp_tac optimal_optimal_val>>
  rw[optimal_def]>>
  fs[unsatisfiable_def,satisfiable_def,satisfies_def,PULL_EXISTS]>>
  first_x_assum (qspec_then `w'` assume_tac)>>
  reverse (rw[])
  >-
    metis_tac[]>>
  fs[satisfies_pbc_def]>>
  intLib.ARITH_TAC
QED

Theorem satisfies_simp[simp]:
  satisfies w EMPTY = T ∧
  satisfies w (c INSERT f) = (satisfies_pbc w c ∧ satisfies w f) ∧
  satisfies w (f ∪ h) = (satisfies w f ∧ satisfies w h)
Proof
  fs [satisfies_def] \\
  metis_tac []
QED

Definition lit_var_def[simp]:
  (lit_var (Pos v) = v) ∧
  (lit_var (Neg v) = v)
End

Definition pbc_vars_def:
  (pbc_vars (pbop,xs,n) = set (MAP (lit_var o SND) xs))
End

Definition pbf_vars_def:
  pbf_vars pbf =
  BIGUNION (IMAGE pbc_vars pbf)
End

Definition map_lit_def:
  (map_lit f (Pos v) = Pos (f v)) ∧
  (map_lit f (Neg v) = Neg (f v))
End

Definition map_pbc_def:
  map_pbc f (pbop,xs,n) =
    (pbop,MAP (λ(a,b). (a, map_lit f b)) xs,n)
End

Theorem eval_lin_term_MAP:
  eval_lin_term w (MAP (λ(a,b). (a, map_lit f b)) xs) =
  eval_lin_term (w o f) xs
Proof
  simp[eval_lin_term_def]>>
  AP_TERM_TAC>>
  match_mp_tac LIST_EQ>>simp[EL_MAP]>>
  rw[]>>
  Cases_on`EL x xs`>>fs[]>>
  Cases_on`r`>>simp[map_lit_def]
QED

Theorem satisfies_map_pbc:
  satisfies_pbc w (map_pbc f pbc) ⇒
  satisfies_pbc (w o f) pbc
Proof
  PairCases_on`pbc`>>
  simp[satisfies_pbc_def,map_pbc_def,MAP_MAP_o,o_DEF,pbc_vars_def]>>
  qmatch_goalsub_abbrev_tac`do_op _ A _ ⇒ do_op _ B _`>>
  qsuff_tac`A=B` >- fs[]>>
  metis_tac[eval_lin_term_MAP]
QED

Theorem satisfies_map_pbf:
  satisfies w (IMAGE (map_pbc f) pbf) ⇒
  satisfies (w o f) pbf
Proof
  fs[satisfies_def,PULL_EXISTS]>>
  metis_tac[satisfies_map_pbc]
QED

Theorem map_pbc_o:
  map_pbc f (map_pbc g pbc) = map_pbc (f o g) pbc
Proof
  PairCases_on`pbc`>>
  EVAL_TAC>>simp[o_DEF,MAP_MAP_o]>>
  match_mp_tac LIST_EQ>>simp[EL_MAP]>>rw[]>>
  Cases_on`EL x pbc1`>>fs[]>>
  Cases_on`r`>>fs[map_lit_def]
QED

Theorem map_pbc_I:
  (∀x. x ∈ pbc_vars pbc ⇒ f x = x) ⇒
  map_pbc f pbc = pbc
Proof
  PairCases_on`pbc`>>EVAL_TAC>>rw[MEM_MAP]>>
  rw[MAP_EQ_ID]>>
  Cases_on`x`>>fs[]>>
  Cases_on`r`>>fs[map_lit_def]>>
  first_x_assum match_mp_tac>>simp[]>>
  metis_tac[lit_var_def,SND]
QED

Theorem lit_var_map_lit:
  !x. lit_var (map_lit f x) = f (lit_var x)
Proof
  Cases>>EVAL_TAC
QED

Theorem pbc_vars_map_pbc:
  pbc_vars (map_pbc f pbc) =
  IMAGE f (pbc_vars pbc)
Proof
  PairCases_on`pbc`>>
  simp[pbc_vars_def,map_pbc_def,o_DEF,MAP_MAP_o,LAMBDA_PROD,LIST_TO_SET_MAP,IMAGE_IMAGE,lit_var_map_lit]
QED

Theorem pbf_vars_IMAGE:
  pbf_vars (IMAGE (map_pbc f) pbf) =
  IMAGE f (pbf_vars pbf)
Proof
  rw[pbf_vars_def,IMAGE_BIGUNION,IMAGE_IMAGE,o_DEF]>>
  simp[pbc_vars_map_pbc]
QED

Theorem satisfies_INJ:
  INJ f s UNIV ∧
  pbf_vars pbf ⊆ s ∧
  satisfies w pbf ⇒
  satisfies (w o LINV f s) (IMAGE (map_pbc f) pbf)
Proof
  rw[]>>
  match_mp_tac (GEN_ALL satisfies_map_pbf)>>
  simp[IMAGE_IMAGE,o_DEF]>>
  simp[map_pbc_o,o_DEF]>>
  drule LINV_DEF>>strip_tac>>
  qmatch_goalsub_abbrev_tac`satisfies w A`>>
  qsuff_tac`A = pbf`>>fs[]>>
  unabbrev_all_tac>>rw[EXTENSION,EQ_IMP_THM]
  >- (
    DEP_REWRITE_TAC [map_pbc_I]>>simp[]>>
    fs[pbf_vars_def,PULL_EXISTS,SUBSET_DEF]>>
    metis_tac[])>>
  qexists_tac`x`>>simp[]>>
  match_mp_tac (GSYM map_pbc_I)>>
  fs[pbf_vars_def,PULL_EXISTS,SUBSET_DEF]>>
  metis_tac[]
QED

Theorem satisfies_pbc_vars:
  (∀x. x ∈ pbc_vars c ⇒ w x = w' x) ⇒
  satisfies_pbc w c ⇒
  satisfies_pbc w' c
Proof
  PairCases_on`c`>>rw[satisfies_pbc_def]>>
  fs[pbc_vars_def,eval_lin_term_def]>>
  qmatch_asmsub_abbrev_tac`iSUM ls `>>
  qmatch_goalsub_abbrev_tac`iSUM ls'`>>
  qsuff_tac `ls = ls'`>>rw[]>>fs[]>>
  unabbrev_all_tac>>
  fs[MAP_EQ_f,MEM_MAP,PULL_EXISTS,FORALL_PROD]>>
  rw[]>>
  first_x_assum drule>>
  Cases_on`p_2`>>simp[]
QED

Theorem satisfies_pbf_vars:
  (∀x. x ∈ pbf_vars f ⇒ w x = w' x) ⇒
  satisfies w f ⇒
  satisfies w' f
Proof
  rw[satisfies_def,pbf_vars_def]>>
  metis_tac[satisfies_pbc_vars]
QED

Theorem satisfies_INJ_2:
  INJ f (pbf_vars pbf) UNIV ∧
  satisfies (w o f) pbf ⇒
  satisfies w (IMAGE (map_pbc f) pbf)
Proof
  rw[]>>
  drule satisfies_INJ>>
  disch_then (drule_at Any)>>
  simp[]>>
  match_mp_tac satisfies_pbf_vars>>
  fs[]>>
  drule LINV_DEF>>
  simp[pbf_vars_IMAGE]>>
  rw[]>>
  first_x_assum drule>>
  metis_tac[]
QED

Theorem satisfiable_INJ_iff:
  INJ f (pbf_vars pbf) UNIV ⇒
  (satisfiable (IMAGE (map_pbc f) pbf) ⇔
  satisfiable pbf)
Proof
  rw[satisfiable_def,EQ_IMP_THM]
  >-
    metis_tac[satisfies_map_pbf]>>
  drule satisfies_INJ>>
  disch_then (drule_at Any)>>
  simp[]>>
  metis_tac[]
QED

Definition eval_obj_def:
  eval_obj fopt w =
    case fopt of NONE => 0
    | SOME (f,c:int) =>
      eval_lin_term w f + c
End

(* Conclusions about a pseudoboolean formula and
  optional objective *)
Datatype:
  concl =
  | NoConcl
  | DSat
  | DUnsat
  | OBounds (int option) (int option)
End

(* Semantics of a conclusion
  Note: lbi, ubi are optional values where
    NONE represents (positive) infinity

  if lbi = NONE (infinity), then the formula is unsat
  else, lbi = SOME lb where lb is a lower bound on the objective

  if ubi = NONE (infinity), no conclusion
  else, ubi = SOME ub where ub is attained by some assignment
*)
Definition sem_concl_def:
  (sem_concl pbf obj NoConcl = T) ∧
  (sem_concl pbf obj DSat = satisfiable pbf) ∧
  (sem_concl pbf obj DUnsat = unsatisfiable pbf) ∧
  (sem_concl pbf obj (OBounds lbi ubi) =
    ((case lbi of
      NONE => unsatisfiable pbf
    | SOME lb =>
      (∀w. satisfies w pbf ⇒ lb ≤ eval_obj obj w)) ∧
    (case ubi of
      NONE => T
    | SOME ub =>
      (∃w. satisfies w pbf ∧ eval_obj obj w ≤ ub))))
End

Theorem eval_lin_term_cong:
  (∀x. MEM x xs ⇒ eval_term f x = eval_term g x) ⇒
  eval_lin_term f xs = eval_lin_term g xs
Proof
  Induct_on`xs`>>rw[]>>
  fs[eval_lin_term_def,iSUM_def]
QED

Theorem eval_lin_term_INJ:
  INJ f s UNIV ∧
  set (MAP (lit_var o SND) xs) ⊆ s ⇒
  eval_lin_term w xs =
  eval_lin_term (w o LINV f s) (MAP (λ(a,b). (a, map_lit f b)) xs)
Proof
  rw[]>>
  simp[eval_lin_term_MAP]>>
  match_mp_tac eval_lin_term_cong>>
  fs[FORALL_PROD,SUBSET_DEF,MEM_MAP,PULL_EXISTS]>>
  rw[]>>
  first_x_assum drule>>rw[]>>
  rename1`lit_var l`>>
  Cases_on`l`>>fs[]>>
  DEP_REWRITE_TAC[LINV_DEF]>>
  metis_tac[]
QED

Definition obj_vars_def:
  (obj_vars NONE = {}) ∧
  (obj_vars (SOME (xs,c)) =
    set (MAP (lit_var o SND) xs))
End

Definition map_obj_def:
  (map_obj f NONE = NONE) ∧
  (map_obj f (SOME (xs,c)) =
    SOME(MAP (λ(a,b). (a, map_lit f b)) xs,c))
End

Theorem eval_obj_map_obj:
  eval_obj (map_obj f obj) w =
  eval_obj obj (w o f)
Proof
  Cases_on`obj`>>rw[map_obj_def,eval_obj_def]>>
  Cases_on`x`>>simp[map_obj_def,eval_lin_term_MAP]
QED

Theorem eval_obj_cong:
  (∀x. x ∈ obj_vars obj ⇒ f x = g x) ⇒
  eval_obj obj f = eval_obj obj g
Proof
  Cases_on`obj`>>rw[eval_obj_def]>>
  TOP_CASE_TAC>>fs[obj_vars_def,MEM_MAP]>>
  match_mp_tac eval_lin_term_cong>>
  fs[PULL_EXISTS,FORALL_PROD]>>rw[]>>first_x_assum drule>>
  Cases_on`p_2`>>fs[]
QED

Theorem concl_INJ_iff:
  INJ f (pbf_vars pbf ∪ obj_vars obj) UNIV
  ⇒
  sem_concl pbf obj concl =
  sem_concl (IMAGE (map_pbc f) pbf) (map_obj f obj) concl
Proof
  Cases_on`concl`>>rw[sem_concl_def]
  >- (
    match_mp_tac (GSYM satisfiable_INJ_iff)>>
    match_mp_tac INJ_SUBSET>>
    asm_exists_tac>>simp[])
  >- (
    simp[unsatisfiable_def]>>
    match_mp_tac (GSYM satisfiable_INJ_iff)>>
    match_mp_tac INJ_SUBSET>>
    asm_exists_tac>>simp[])
  >- (
    simp[eval_obj_map_obj]>>
    match_mp_tac
      (METIS_PROVE [] ``(A ⇔ C) ∧ (B ⇔ D) ⇒ ((A ∧ B) ⇔ (C ∧ D))``)>>
    CONJ_TAC
    >- (
      every_case_tac>>fs[]
      >- (
        simp[unsatisfiable_def]>>
        match_mp_tac (GSYM satisfiable_INJ_iff)>>
        match_mp_tac INJ_SUBSET>>
        asm_exists_tac>>simp[])>>
      rw[EQ_IMP_THM]
      >- (
        first_x_assum match_mp_tac>>
        metis_tac[satisfies_map_pbf])>>
      (drule_at Any) satisfies_INJ>>
      disch_then drule>>simp[]>>
      rw[]>>
      first_x_assum drule>>
      qmatch_goalsub_abbrev_tac`_ ≤ A ⇒ _ ≤ B`>>
      qsuff_tac`A=B`
      >-
        rw[]>>
      unabbrev_all_tac>>
      match_mp_tac eval_obj_cong>>rw[]>>
      DEP_REWRITE_TAC[LINV_DEF]>>
      fs[]>>metis_tac[])>>
    every_case_tac>>fs[]>>
    rw[EQ_IMP_THM]
    >- (
      (drule_at Any) satisfies_INJ>>
      disch_then drule>>simp[]>>
      rw[]>>
      asm_exists_tac>>simp[]>>
      qpat_x_assum`_ ≤ _` mp_tac>>
      qmatch_goalsub_abbrev_tac`A ≤ _ ⇒ B ≤ _`>>
      qsuff_tac`A=B`
      >-
        rw[]>>
      unabbrev_all_tac>>
      match_mp_tac eval_obj_cong>>rw[]>>
      DEP_REWRITE_TAC[LINV_DEF]>>
      fs[]>>metis_tac[])>>
    metis_tac[satisfies_map_pbf])
QED

(* Output section for a pseudoboolean formula *)
Datatype:
  output =
  | NoOutput
  | Derivable
  | Equisatisfiable
  | Equioptimal
End

(* Semantics of an output section wrt a derived bound *)
Definition sem_output_def:
  (sem_output pbf obj bound pbf' obj' NoOutput = T) ∧
  (sem_output pbf obj bound pbf' obj' Derivable =
    (satisfiable pbf ⇒ satisfiable pbf')) ∧
  (sem_output pbf obj bound pbf' obj' Equisatisfiable =
    (satisfiable pbf ⇔ satisfiable pbf')) ∧
  (sem_output pbf obj bound pbf' obj' Equioptimal =
    ∀v.
    (case bound of NONE => T | SOME b => v < b) ⇒
    (
      (∃w. satisfies w pbf ∧ eval_obj obj w ≤ v) ⇔
      (∃w'. satisfies w' pbf' ∧ eval_obj obj' w' ≤ v)
    )
  )
End

Theorem output_INJ_iff:
  INJ f (pbf_vars pbf ∪ obj_vars obj) UNIV ∧
  INJ g (pbf_vars pbf' ∪ obj_vars obj') UNIV
  ⇒
  sem_output pbf obj bound pbf' obj' output =
  sem_output
    (IMAGE (map_pbc f) pbf) (map_obj f obj)
    bound
    (IMAGE (map_pbc g) pbf') (map_obj g obj')
    output
Proof
  Cases_on`output`>>rw[sem_output_def]
  >- (
    rw[]>>
    DEP_REWRITE_TAC [satisfiable_INJ_iff]>>
    rw[]>>
    match_mp_tac INJ_SUBSET>>
    asm_exists_tac>>simp[])
  >- (
    rw[]>>
    DEP_REWRITE_TAC [satisfiable_INJ_iff]>>
    rw[]>>
    match_mp_tac INJ_SUBSET>>
    asm_exists_tac>>simp[])
  >- (
    simp[eval_obj_map_obj]>>
    ho_match_mp_tac (METIS_PROVE []
    ``(∀v. P v ⇒ (X v ⇔ Y v)) ⇒
      ((∀v. P v ⇒ X v) ⇔ (∀v. P v ⇒ Y v))``)>>
    rw[EQ_IMP_THM]>>
    fs[PULL_EXISTS]
    >- (
      (* Undo mapping g in concl *)
      (irule_at Any) satisfies_INJ>>
      first_assum (irule_at Any)>>
      simp[]>>
      (* Undo mapping f in assms *)
      drule satisfies_map_pbf>> strip_tac>>
      (* implies *)
      first_x_assum drule_all>>rw[]>>
      (* Solve *)
      first_x_assum (irule_at Any)>>
      pop_assum mp_tac>>
      qmatch_goalsub_abbrev_tac`A ≤ _ ⇒ B ≤ _`>>
      qsuff_tac`A=B`
      >-
        rw[]>>
      unabbrev_all_tac>>
      match_mp_tac eval_obj_cong>>rw[]>>
      DEP_REWRITE_TAC[LINV_DEF]>>
      fs[]>>metis_tac[])
    >- (
      (* Undo mapping f in concl *)
      (irule_at Any) satisfies_INJ>>
      first_assum (irule_at Any)>>
      simp[]>>
      (* Undo mapping g in assms *)
      drule satisfies_map_pbf>> strip_tac>>
      (* implies *)
      first_x_assum drule_all>>rw[]>>
      (* Solve *)
      first_x_assum (irule_at Any)>>
      pop_assum mp_tac>>
      qmatch_goalsub_abbrev_tac`A ≤ _ ⇒ B ≤ _`>>
      qsuff_tac`A=B`
      >-
        rw[]>>
      unabbrev_all_tac>>
      match_mp_tac eval_obj_cong>>rw[]>>
      DEP_REWRITE_TAC[LINV_DEF]>>
      fs[]>>metis_tac[])
    >- (
      (* map f in assums *)
      (drule_at Any) satisfies_INJ>>
      disch_then drule>>simp[]>>
      strip_tac>>
      (* implies *)
      first_x_assum drule>>
      impl_tac>- (
        qpat_x_assum`_ ≤ v` mp_tac>>
        qmatch_goalsub_abbrev_tac`A ≤ _ ⇒ B ≤ _`>>
        qsuff_tac`A=B`
        >-
          rw[]>>
        unabbrev_all_tac>>
        match_mp_tac eval_obj_cong>>rw[]>>
        DEP_REWRITE_TAC[LINV_DEF]>>
        fs[]>>metis_tac[])>>
      rw[]>>
      metis_tac[satisfies_map_pbf])
    >- (
      (* map g in assums *)
      (drule_at Any) (INST_TYPE [beta |-> delta] satisfies_INJ)>>
      disch_then drule>>simp[]>>
      strip_tac>>
      (* implies *)
      first_x_assum drule>>
      impl_tac>- (
        qpat_x_assum`_ ≤ v` mp_tac>>
        qmatch_goalsub_abbrev_tac`A ≤ _ ⇒ B ≤ _`>>
        qsuff_tac`A=B`
        >-
          rw[]>>
        unabbrev_all_tac>>
        match_mp_tac eval_obj_cong>>rw[]>>
        DEP_REWRITE_TAC[LINV_DEF]>>
        fs[]>>metis_tac[])>>
      rw[]>>
      metis_tac[satisfies_map_pbf]))
QED

val _ = export_theory();
