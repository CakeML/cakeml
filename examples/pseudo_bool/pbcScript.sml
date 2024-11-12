(*
  Formalisation of a flexible surface syntax and semantics for
  pseudo-boolean problems with 'a var type
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

(* NOTE: NONE case is a dummy, we never use it *)
Definition eval_obj_def:
  eval_obj fopt w =
    case fopt of NONE => 0
    | SOME (f,c:int) =>
      eval_lin_term w f + c
End

(* Conclusions about a pseudoboolean formula and objective.
  TODO: support for enumeration of solutions on preserved variable set *)
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

(* More convenient input representation as lists *)
Definition pres_set_list_def:
  pres_set_list pres =
    case pres of NONE => {} | SOME pres => set pres
End

(* projecting set ws of solutions onto preserved set *)
Definition proj_pres_def:
  proj_pres pres ws =
    IMAGE (λw. pres ∩ w) ws
End

(* Output section for a pseudoboolean formula *)
Datatype:
  output =
  | NoOutput
  | Derivable
  | Equisatisfiable
  | Equioptimal
  | Equisolvable
End

(* Semantics of an output section wrt a derived bound.
  TODO: BIJ f uniform or non-uniform in v for Equisolvable?
  TODO: support partial enumeration *)
Definition sem_output_def:
  (sem_output pbf obj pres bound pbf' obj' pres' NoOutput = T) ∧
  (sem_output pbf obj pres bound pbf' obj' pres' Derivable =
    (satisfiable pbf ⇒ satisfiable pbf')) ∧
  (sem_output pbf obj pres bound pbf' obj' pres' Equisatisfiable =
    (satisfiable pbf ⇔ satisfiable pbf')) ∧
  (sem_output pbf obj pres bound pbf' obj' pres' Equioptimal =
    ∀v.
    (case bound of NONE => T | SOME b => v < b) ⇒
    (
      (∃w. satisfies w pbf ∧ eval_obj obj w ≤ v) ⇔
      (∃w'. satisfies w' pbf' ∧ eval_obj obj' w' ≤ v)
    )
  ) ∧
  (sem_output pbf obj pres bound pbf' obj' pres' Equisolvable =
    ∀v.
    (case bound of NONE => T | SOME b => v < b) ⇒
    ∃f.
    (
        BIJ f
        (proj_pres pres {w | satisfies w pbf ∧ eval_obj obj w ≤ v})
        (proj_pres pres' {w' | satisfies w' pbf' ∧ eval_obj obj' w' ≤ v})
    )
  )
End

Theorem sem_output_equioptimal_NONE_imp_equisatisfiable:
  sem_output pbf obj pres NONE pbf' obj' pres' Equioptimal ⇒
  sem_output pbf obj pres NONE pbf' obj' pres' Equisatisfiable
Proof
  rw[sem_output_def,satisfiable_def]>>
  metis_tac[integerTheory.INT_LE_TOTAL]
QED

Theorem sem_output_equioptimal_NONE_optimal_val:
  sem_output pbf (SOME obj) pres NONE pbf' (SOME obj') pres' Equioptimal ⇒
  optimal_val pbf obj = optimal_val pbf' obj'
Proof
  strip_tac>>drule sem_output_equioptimal_NONE_imp_equisatisfiable>>
  gvs[sem_output_def]>>
  Cases_on`obj`>>Cases_on`obj'`>>
  rename1`optimal_val _ (f,c) = _ _ (f',c')`>>
  reverse (Cases_on`satisfiable pbf`)
  >-
    rw[optimal_val_def]>>
  rw[]>>
  gvs[satisfiable_def]>>
  imp_res_tac optimal_exists >>
  pop_assum (qspec_then`f` mp_tac)>>
  pop_assum (qspec_then`f'` mp_tac)>>
  rw[]>>
  drule optimal_optimal_val>>
  disch_then(qspec_then`c` mp_tac)>>
  pop_assum mp_tac>>
  drule optimal_optimal_val>>
  disch_then(qspec_then`c'` mp_tac)>>
  rw[]>>gvs[eval_obj_def,optimal_def]>>
  gvs[EQ_IMP_THM,FORALL_AND_THM,PULL_EXISTS]>>
  last_x_assum drule>>
  last_x_assum drule>>
  rename1`eval_lin_term ww _ + _ = eval_lin_term ww' _ + _`>>
  disch_then(qspec_then`eval_lin_term ww' f' + c'` assume_tac)>>
  disch_then(qspec_then`eval_lin_term ww f + c` assume_tac)>>
  gvs[]>>
  last_x_assum drule>>
  last_x_assum drule>>
  intLib.ARITH_TAC
QED

Theorem sem_output_equisolvable_imp_equioptimal:
  sem_output pbf obj pres bound pbf' obj' pres' Equisolvable ⇒
  sem_output pbf obj pres bound pbf' obj' pres' Equioptimal
Proof
  rw[sem_output_def,satisfiable_def]>>
  first_x_assum drule>>rw[]>>
  gvs[BIJ_DEF,proj_pres_def,SURJ_DEF]>>
  metis_tac[]
QED

Theorem eval_term_bounded:
  eval_term w h ≤ ABS (FST h)
Proof
  Cases_on`h`>>rw[]>>
  Cases_on`r`>>rw[]>>
  Cases_on`w a`>>fs[]>>
  intLib.ARITH_TAC
QED

Theorem eval_lin_term_bounded:
  ∀w. eval_lin_term w lin ≤ iSUM (MAP (ABS o FST) lin)
Proof
  simp[eval_lin_term_def]>>
  Induct_on`lin`>>rw[iSUM_def]>>
  rw[]>>
  assume_tac eval_term_bounded>>
  last_x_assum (qspec_then`w` assume_tac)>>
  intLib.ARITH_TAC
QED

(* Can give a more precise bound ... *)
Theorem eval_obj_bounded:
  ∃v. ∀w. eval_obj obj w ≤ v
Proof
  rw[eval_obj_def]>>every_case_tac>>gvs[]
  >- intLib.ARITH_TAC>>
  qexists_tac`iSUM(MAP(ABS o FST) q) + r`>>
  simp[]>>
  metis_tac[eval_lin_term_bounded]
QED

(* The unbounded version, i.e., all solutions are preserved.
  This should be the main case where we will use this... *)
Theorem sem_output_equisolvable_NONE:
  sem_output pbf obj pres NONE pbf' obj' pres' Equisolvable ⇒
  ∃f.
    BIJ f
      (proj_pres pres {w | satisfies w pbf})
      (proj_pres pres' {w' | satisfies w' pbf'})
Proof
  rw[sem_output_def,EQ_IMP_THM]>>
  `∃v.
    (∀w. eval_obj obj w ≤ v) ∧
    (∀w. eval_obj obj' w ≤ v) ` by
      metis_tac[eval_obj_bounded,integerTheory.INT_LE_TRANS,integerTheory.INT_LE_TOTAL]>>
  rw[]>>
  first_x_assum(qspec_then`v` mp_tac)>>
  rw[]
QED

Theorem optimal_val_iff:
  optimal_val pbf (ob,c) = SOME v ⇒
  (optimal w pbf ob
  ⇔
  satisfies w pbf ∧ eval_obj (SOME (ob,c)) w ≤ v)
Proof
  strip_tac>>
  eq_tac
  >- (
    strip_tac>>
    drule optimal_optimal_val>>
    disch_then(qspec_then`c` assume_tac)>>
    gvs[optimal_val_def,eval_obj_def,optimal_def])>>
  rw[]>>
  drule optimal_exists>>
  disch_then(qspec_then`ob` assume_tac)>>
  gvs[]>>
  drule optimal_optimal_val>>
  disch_then(qspec_then`c` assume_tac)>>
  gvs[]>>
  gvs[optimal_def]>>
  rw[]>>
  gvs[eval_obj_def]>>
  first_x_assum drule>>
  intLib.ARITH_TAC
QED

(* In particular, there is a bijection on projections of the optimal solutions *)
Theorem sem_output_equisolvable_NONE_2:
  sem_output pbf (SOME (ob,c)) pres NONE pbf' (SOME (ob',c')) pres' Equisolvable ⇒
  ∃f.
    BIJ f
      (proj_pres pres {w | optimal w pbf ob})
      (proj_pres pres' {w' | optimal w' pbf' ob'})
Proof
  rw[]>>
  reverse (Cases_on`satisfiable pbf`)
  >- (
    drule sem_output_equisolvable_NONE>>
    rw[]>>qexists_tac`f`>>
    gvs[satisfiable_def,proj_pres_def,optimal_def,EXTENSION])>>
  drule sem_output_equisolvable_imp_equioptimal>>
  strip_tac>>
  drule sem_output_equioptimal_NONE_optimal_val>>
  pop_assum kall_tac>>
  strip_tac>>
  `∃v. optimal_val pbf (ob,c) = SOME v` by
    gvs[optimal_val_def]>>
  gvs[sem_output_def]>>
  first_x_assum(qspec_then`v` mp_tac)>>
  rw[]>>
  qexists_tac`f`>>
  qmatch_asmsub_abbrev_tac`BIJ f (_ _ A) (_ _ B)`>>
  qmatch_goalsub_abbrev_tac`BIJ f (_ _ A') (_ _ B')`>>
  `A = A' ∧ B = B'` by (
    unabbrev_all_tac>>
    rw[EXTENSION]>>
    metis_tac[optimal_val_iff])>>
  rw[]
QED

(* take x, y, z -> bool
  f x, f y, f z -> bool *)
Theorem image_sol_set:
  INJ f (pbf_vars pbf ∪ obj_vars obj ∪ pres) UNIV ∧
  (∀x y. x ∈ pres ∧ f x = f y ⇒ x = y) ⇒
  IMAGE (λpfw. pfw o f)
  (proj_pres (IMAGE f pres)
    {fw | satisfies fw (IMAGE (map_pbc f) pbf) ∧
           eval_obj (map_obj f obj) fw ≤ v}) =
  proj_pres pres
    {w | satisfies w pbf ∧ eval_obj obj w ≤ v}
Proof
  rw[proj_pres_def,Once EXTENSION,EQ_IMP_THM]
  >- (
    rename1`eval_obj _ fw`>>
    gvs[eval_obj_map_obj,FORALL_AND_THM,IMP_CONJ_THM]>>
    drule satisfies_map_pbf>>
    strip_tac>>
    first_x_assum (irule_at Any)>>simp[]>>
    simp[o_DEF,EXTENSION]>>
    rw[EQ_IMP_THM]>>gvs[IN_DEF]>>
    metis_tac[])
  >- (
    drule satisfies_INJ>>
    disch_then (drule_at Any)>>
    simp[SUBSET_DEF]>>
    disch_then (irule_at Any)>>
    simp[eval_obj_map_obj]>>
    CONJ_TAC >- (
      simp[o_DEF,EXTENSION]>>
      rw[EQ_IMP_THM]
      >- metis_tac[]
      >- (
        DEP_REWRITE_TAC[LINV_DEF]>>
        gvs[IN_DEF]>>
        metis_tac[])
      >- metis_tac[]
      >- (
        pop_assum mp_tac>>
        simp[]>>
        DEP_REWRITE_TAC[LINV_DEF]>>
        gvs[IN_DEF]>>
        metis_tac[]))>>
    pop_assum mp_tac>>
    qmatch_goalsub_abbrev_tac`A ≤ _ ⇒ B ≤ _`>>
    qsuff_tac`A=B`
    >-
      rw[]>>
    unabbrev_all_tac>>
    match_mp_tac eval_obj_cong>>rw[]>>
    DEP_REWRITE_TAC[LINV_DEF]>>
    fs[]>>metis_tac[])
QED

Theorem BIJ_IMAGE_proj_pres:
  BIJ (λpfw. pfw o f)
  (proj_pres (IMAGE f pres) ws)
  (IMAGE (λpfw. pfw o f)
  (proj_pres (IMAGE f pres) ws))
Proof
  match_mp_tac INJ_IMAGE_BIJ>>
  qexists_tac`UNIV`>>
  simp[INJ_DEF,proj_pres_def,PULL_EXISTS]>>rw[EXTENSION]>>
  gvs[o_DEF,PULL_EXISTS]>>
  metis_tac[]
QED

(* Applying an injection on variables for input/output problems preserves their semantic output relation *)
Theorem output_INJ_iff:
  INJ f (pbf_vars pbf ∪ obj_vars obj ∪ pres) UNIV ∧
  INJ g (pbf_vars pbf' ∪ obj_vars obj' ∪ pres') UNIV ∧
  (∀x y. x ∈ pres ∧ f x = f y ⇒ x = y) ∧
  (∀x y. x ∈ pres' ∧ g x = g y ⇒ x = y)
  ⇒
  sem_output pbf obj pres bound pbf' obj' pres' output =
  sem_output
    (IMAGE (map_pbc f) pbf) (map_obj f obj) (IMAGE f pres)
    bound
    (IMAGE (map_pbc g) pbf') (map_obj g obj') (IMAGE g pres')
    output
Proof
  Cases_on`output`>>rw[sem_output_def]
  >- (
    rw[]>>
    DEP_REWRITE_TAC [satisfiable_INJ_iff]>>
    rw[]>>
    match_mp_tac INJ_SUBSET>>
    asm_exists_tac>>simp[SUBSET_DEF])
  >- (
    rw[]>>
    DEP_REWRITE_TAC [satisfiable_INJ_iff]>>
    rw[]>>
    match_mp_tac INJ_SUBSET>>
    asm_exists_tac>>simp[SUBSET_DEF])
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
      simp[SUBSET_DEF]>>
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
      simp[SUBSET_DEF]>>
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
      disch_then drule>>simp[SUBSET_DEF]>>
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
      disch_then drule>>simp[SUBSET_DEF]>>
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
  >- (
    qmatch_asmsub_abbrev_tac`INJ f fd _`>>
    qmatch_asmsub_abbrev_tac`INJ g gd _`>>
    ho_match_mp_tac (METIS_PROVE []
    ``(∀v. P v ⇒ (X v ⇔ Y v)) ⇒
      ((∀v. P v ⇒ X v) ⇔ (∀v. P v ⇒ Y v))``)>>
    rw[EQ_IMP_THM]
    (* We're chase the following diagram (all lines are BIJ)
        ww  --AA--  ww'
        |            |
        BB          CC
        |            |
        fww --DD-- gww *)
    >- (
      qmatch_asmsub_abbrev_tac `BIJ AA ww ww'`>>
      qmatch_goalsub_abbrev_tac `BIJ _ fww fww'`>>
      `∃BB. BIJ BB ww fww` by (
        unabbrev_all_tac>>
        DEP_ONCE_REWRITE_TAC[GSYM image_sol_set]>>
        simp[Once BIJ_SYM]>>
        metis_tac[BIJ_IMAGE_proj_pres])>>
      `∃CC. BIJ CC ww' fww'` by (
        unabbrev_all_tac>>
        DEP_ONCE_REWRITE_TAC[GSYM image_sol_set |> Q.GEN`f` |> Q.SPEC`g` |> INST_TYPE [beta |-> delta]]>>
        simp[Once BIJ_SYM]>>
        metis_tac[BIJ_IMAGE_proj_pres]) >>
      metis_tac[BIJ_SYM,BIJ_TRANS])
    >- (
      qmatch_asmsub_abbrev_tac `BIJ DD fww fww'`>>
      qmatch_goalsub_abbrev_tac `BIJ _ ww ww'`>>
      `∃BB. BIJ BB ww fww` by (
        unabbrev_all_tac>>
        DEP_ONCE_REWRITE_TAC[GSYM image_sol_set]>>
        simp[Once BIJ_SYM]>>
        metis_tac[BIJ_IMAGE_proj_pres])>>
      `∃CC. BIJ CC ww' fww'` by (
        unabbrev_all_tac>>
        DEP_ONCE_REWRITE_TAC[GSYM image_sol_set |> Q.GEN`f` |> Q.SPEC`g` |> INST_TYPE [beta |-> delta]]>>
        simp[Once BIJ_SYM]>>
        metis_tac[BIJ_IMAGE_proj_pres]) >>
      metis_tac[BIJ_SYM,BIJ_TRANS]))
QED

val _ = export_theory();
