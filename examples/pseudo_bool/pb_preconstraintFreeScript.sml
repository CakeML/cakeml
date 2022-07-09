(*
  Formalisation of (un-normalised) pseudo-boolean constraints with 'a type
*)

open preamble;

val _ = new_theory "pb_preconstraintFree";

val _ = numLib.prefer_num();

Datatype:
  lit = Pos 'a | Neg 'a
End

(*
  Un-normalised pseudo-boolean constraints have the form:
  c_i l_i ≥ n OR
  c_i l_i = n OR
  where coefficients c_i and n are arbitrary integers and l_i are literals
*)
Datatype:
  pbc =
    Equal ((int # 'a lit) list) int
  | GreaterEqual ((int # 'a lit) list) int
End

(* integer-valued semantics *)

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

Definition eval_lhs_def[simp]:
  eval_lhs w xs = iSUM (MAP (eval_term w) xs)
End

(* satisfaction of a pseudoboolean constraint *)
Definition satisfies_pbc_def:
  (satisfies_pbc w (Equal xs n) ⇔ eval_lhs w xs = n) ∧
  (satisfies_pbc w (GreaterEqual xs n) ⇔ eval_lhs w xs ≥ n)
End

(* satisfaction of a set of pseudoboolean constraints *)
Definition satisfies_def:
  satisfies w pbf ⇔
  ∀c. c ∈ pbf ⇒ satisfies_pbc w c
End

Definition satisfiable_def:
  satisfiable pbf ⇔
  ∃w. satisfies w pbf
End

Theorem satisfies_simp[simp]:
  satisfies w EMPTY = T ∧
  satisfies w (c INSERT f) = (satisfies_pbc w c ∧ satisfies w f) ∧
  satisfies w (f ∪ h) = (satisfies w f ∧ satisfies w h)
Proof
  fs [satisfies_def] \\
  metis_tac []
QED

(* Convert a list of pbc to one with ≥ constraints only *)
Definition pbc_ge_def:
  (pbc_ge (GreaterEqual xs n) = [GreaterEqual xs n]) ∧
  (pbc_ge (Equal xs n) =
    let xs' = MAP (λ(c:int,l). (-c,l)) xs in
      [GreaterEqual xs n; GreaterEqual xs' (-n)])
End

Theorem eq_disj:
  (∀x. x = a ∨ x = b ⇒ P x) ⇔ P a ∧ P b
Proof
  metis_tac[]
QED

Theorem eval_term_negate:
  ∀ls.
  (MAP (eval_term w) (MAP (λ(c,l). (-c,l)) ls)) =
  (MAP (\i. -i) (MAP (eval_term w) ls))
Proof
  Induct>>simp[]>>
  Cases>>rw[eval_term_def]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_negate:
  ∀ls. iSUM (MAP (\i. -i) ls) = -iSUM ls
Proof
  Induct>>simp[iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem pbc_ge_thm:
  ∀c.
  satisfies w (set (pbc_ge c)) ⇔
  satisfies_pbc w c
Proof
  Cases>>
  simp[pbc_ge_def,satisfies_def]>>
  rw[EQ_IMP_THM]
  >- (
    fs[satisfies_pbc_def,eq_disj,eval_term_negate,iSUM_negate]>>
    intLib.ARITH_TAC) >>
  fs[satisfies_pbc_def,eval_term_negate,iSUM_negate]>>
  intLib.ARITH_TAC
QED

Definition satisfiable_def:
  satisfiable pbf ⇔
  ∃w. satisfies w pbf
End

Definition lit_var_def:
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
  rw[]
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
  (satisfiable (IMAGE (map_pbc f) pbf) ⇔
  satisfiable pbf)
Proof
  metis_tac[satisfiable_INJ,satisfiable_map_pbf]
QED

val _ = export_theory();
