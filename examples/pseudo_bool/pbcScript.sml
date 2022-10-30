(*
  Formalisation of a flexible surface syntax and semantics for
  pseudo-boolean constraint (un-normalised) with 'a var type
*)
open preamble mlintTheory;

val _ = new_theory "pbc";

val _ = numLib.prefer_num();

Datatype:
  lit = Pos 'a | Neg 'a
End

(*
  Un-normalised pseudo-boolean constraints have the form:
  c_i l_i ≥ n OR
  c_i l_i = n OR
  where coefficients c_i and n are arbitrary integers and l_i are literals

  TODO: the surface format could also support other comparators
    like <, ≤ if needed
*)

(* A linear term over variables *)
Type lin_term = ``:(int # 'a lit) list``;

Datatype:
  pbc =
    Equal ('a lin_term) int
  | GreaterEqual ('a lin_term) int
End

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

(* satisfaction of a pseudo-boolean constraint *)
Definition satisfies_pbc_def:
  (satisfies_pbc w (Equal xs n) ⇔ eval_lin_term w xs = n) ∧
  (satisfies_pbc w (GreaterEqual xs n) ⇔ eval_lin_term w xs ≥ n)
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

(* Optimality of an assignment *)
Definition optimal_def:
  optimal w pbf f ⇔
    satisfies w pbf ∧
    ∀w'.
      satisfies w' pbf ⇒ eval_lin_term w f ≤ eval_lin_term w' f
End

Definition optimal_val_def:
  optimal_val pbf f =
    if satisfiable pbf then
      SOME (eval_lin_term (@w. optimal w pbf f) f)
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
  optimal_val pbf f = SOME (eval_lin_term w f)
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

Theorem eval_lin_term_MAP_negate_coeff:
  ∀f.
  eval_lin_term w (MAP (λ(c,l). (-c,l)) f) =
  -eval_lin_term w f
Proof
  Induct>>fs[eval_lin_term_def,iSUM_def]>>
  Cases_on`h`>>rw[]>>
  Cases_on`r`>>rw[]>>Cases_on`w a`>>rw[]>>
  intLib.ARITH_TAC
QED

Theorem optimal_witness:
  satisfies w pbf ∧
  unsatisfiable (
    GreaterEqual (MAP (λ(c,l). (-c,l)) f)
    (-(eval_lin_term w f) +1) INSERT pbf) ⇒
  optimal_val pbf f = SOME (eval_lin_term w f)
Proof
  rw[]>>
  match_mp_tac optimal_optimal_val>>
  rw[optimal_def]>>
  fs[unsatisfiable_def,satisfiable_def,satisfies_def,PULL_EXISTS]>>
  first_x_assum (qspec_then `w'` assume_tac)>>
  reverse (rw[])
  >-
    metis_tac[]>>
  fs[satisfies_pbc_def,eval_lin_term_MAP_negate_coeff]>>
  fs[]>>
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
  (pbc_vars (Equal xs n) = set (MAP (lit_var o SND) xs)) ∧
  (pbc_vars (GreaterEqual xs n) = set (MAP (lit_var o SND) xs))
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
  (map_pbc f (Equal xs n) = Equal (MAP (λ(a,b). (a, map_lit f b)) xs) n) ∧
  (map_pbc f (GreaterEqual xs n) = GreaterEqual (MAP (λ(a,b). (a, map_lit f b)) xs) n)
End

Theorem satisfiable_map_pbc:
  satisfies_pbc w (map_pbc f pbc) ⇒
  satisfies_pbc (w o f) pbc
Proof
  Cases_on`pbc`>>simp[satisfies_pbc_def,map_pbc_def,MAP_MAP_o,o_DEF,pbc_vars_def]>>
  rw[eval_lin_term_def]
  >- (
    AP_TERM_TAC>>
    match_mp_tac LIST_EQ>>simp[EL_MAP]>>
    rw[]>>
    Cases_on`EL x l`>>fs[]>>
    Cases_on`r`>>simp[map_lit_def])>>
  qmatch_asmsub_abbrev_tac`a ≥ _` >>
  qmatch_goalsub_abbrev_tac`b ≥ _` >>
  qsuff_tac`a=b` >-
    intLib.ARITH_TAC>>
  unabbrev_all_tac>>
  AP_TERM_TAC>>
  match_mp_tac LIST_EQ>>simp[EL_MAP]>>
  rw[]>>
  Cases_on`EL x l`>>fs[]>>
  Cases_on`r`>>simp[map_lit_def]
QED

Theorem satisfiable_map_pbf:
  satisfiable (IMAGE (map_pbc f) pbf) ⇒
  satisfiable pbf
Proof
  rw[satisfiable_def]>>
  qexists_tac`w o f`>>fs[satisfies_def,PULL_EXISTS]>>
  metis_tac[satisfiable_map_pbc]
QED

Theorem map_pbc_o:
  map_pbc f (map_pbc g x) = map_pbc (f o g) x
Proof
  Cases_on`x`>>EVAL_TAC>>simp[o_DEF,MAP_MAP_o]>>
  match_mp_tac LIST_EQ>>simp[EL_MAP]>>rw[]>>
  Cases_on`EL x l`>>fs[]>>
  Cases_on`r`>>fs[map_lit_def]
QED

Theorem map_pbc_I:
  (∀x. x ∈ pbc_vars pbc ⇒ f x = x) ⇒
  map_pbc f pbc = pbc
Proof
  Cases_on`pbc`>>EVAL_TAC>>rw[MEM_MAP]>>
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
  ∀x.
  pbc_vars (map_pbc f x) =
  IMAGE f (pbc_vars x)
Proof
  Cases>>
  simp[pbc_vars_def,map_pbc_def,o_DEF,MAP_MAP_o,LAMBDA_PROD,LIST_TO_SET_MAP,IMAGE_IMAGE,lit_var_map_lit]
QED

Theorem pbf_vars_IMAGE:
  pbf_vars (IMAGE (map_pbc f) pbf) =
  IMAGE f (pbf_vars pbf)
Proof
  rw[pbf_vars_def,IMAGE_BIGUNION,IMAGE_IMAGE,o_DEF]>>
  simp[pbc_vars_map_pbc]
QED

Theorem satisfiable_INJ:
  INJ f (pbf_vars pbf) UNIV ∧
  satisfiable pbf ⇒
  satisfiable (IMAGE (map_pbc f) pbf)
Proof
  rw[]>>
  match_mp_tac (GEN_ALL satisfiable_map_pbf)>>
  simp[IMAGE_IMAGE,o_DEF]>>
  qexists_tac`LINV f (pbf_vars pbf)`>>
  simp[map_pbc_o,o_DEF]>>
  drule LINV_DEF>>strip_tac>>
  qmatch_goalsub_abbrev_tac`satisfiable A`>>
  qsuff_tac`A = pbf`>>fs[]>>
  unabbrev_all_tac>>rw[EXTENSION,EQ_IMP_THM]
  >- (
    DEP_REWRITE_TAC [map_pbc_I]>>simp[]>>
    fs[pbf_vars_def,PULL_EXISTS]>>
    metis_tac[])>>
  qexists_tac`x`>>simp[]>>
  match_mp_tac (GSYM map_pbc_I)>>
  fs[pbf_vars_def,PULL_EXISTS]>>
  metis_tac[]
QED

Theorem satisfiable_INJ_iff:
  INJ f (pbf_vars pbf) UNIV ⇒
  (satisfiable (IMAGE (map_pbc f) pbf) ⇔ satisfiable pbf)
Proof
  metis_tac[satisfiable_INJ,satisfiable_map_pbf]
QED

val _ = export_theory();
