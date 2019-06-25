(*
  Lemmas used in proof of clos_known
*)
open HolKernel Parse boolLib bossLib;

open preamble
open closPropsTheory clos_knownTheory

val _ = new_theory "clos_knownProps";

val va_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of ``:val_approx``,
                      nchotomy = TypeBase.nchotomy_of ``:val_approx``}

Theorem merge_Other[simp]:
   merge Other a = Other ∧ merge a Other = Other
Proof
  Cases_on `a` >> simp[]
QED

Theorem merge_Impossible[simp]:
   merge a Impossible = a
Proof
  Cases_on `a` >> simp[]
QED

(* See merge as a join operation on a semi-lattice: it's a join because it's
   a little akin to a union: as merge is used, more and more values might
   inhabit the approximation, with Other at the top corresponding to
   anything at all. *)
Theorem merge_comm:
   ∀a1 a2. merge a1 a2 = merge a2 a1
Proof
  ho_match_mp_tac merge_ind >> rpt strip_tac >> simp_tac(srw_ss()) [] >>
  COND_CASES_TAC >> simp[] >>
  simp[MAP2_MAP, MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_ZIP] >>
  metis_tac[MEM_EL]
QED

Theorem merge_assoc:
   ∀a1 a2 a3. merge a1 (merge a2 a3) = merge (merge a1 a2) a3
Proof
  ho_match_mp_tac merge_ind >> rpt strip_tac >> Cases_on `a3` >>
  simp[] >> rw[LENGTH_MAP2]
  >- (simp[MAP2_MAP, MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >>
      metis_tac[MEM_EL]) >>
  rw[]
QED

Theorem merge_idem[simp]:
   merge a a = a
Proof
  completeInduct_on `val_approx_size a` >> Cases_on `a` >>
  simp[val_approx_size_def] >> strip_tac >> fs[PULL_FORALL] >>
  simp[MAP2_MAP, MAP_EQ_ID] >> rpt strip_tac >> first_x_assum match_mp_tac >>
  rw[] >> Induct_on `l` >> dsimp[val_approx_size_def] >> rpt strip_tac >>
  res_tac >> simp[]
QED

val subapprox_def = Define`
  subapprox a1 a2 ⇔ merge a1 a2 = a2
`;

val _ = set_fixity "◁" (Infix(NONASSOC,450))
val _ = overload_on ("◁", ``subapprox``)

Theorem subapprox_refl[simp]:
   a ◁ a
Proof
  simp[subapprox_def]
QED

Theorem subapprox_trans:
   a1 ◁ a2 ∧ a2 ◁ a3 ⇒ a1 ◁ a3
Proof
  simp[subapprox_def] >> metis_tac[merge_assoc]
QED

Theorem subapprox_antisym:
   a1 ◁ a2 ∧ a2 ◁ a1 ⇒ a1 = a2
Proof
  simp[subapprox_def] >> metis_tac[merge_comm]
QED

Theorem subapprox_merge[simp]:
   a ◁ merge a b ∧ a ◁ merge b a
Proof
  simp[subapprox_def] >>
  metis_tac[merge_assoc, merge_comm, merge_idem]
QED

Theorem subapprox_Other[simp]:
   (Other ◁ a ⇔ (a = Other)) ∧ a ◁ Other
Proof
  simp[subapprox_def] >> metis_tac[]
QED

Theorem subapprox_Int[simp]:
   (a ◁ Int i ⇔ a = Int i ∨ a = Impossible) ∧
   (Int i ◁ a ⇔ a = Int i ∨ a = Other)
Proof
  simp[subapprox_def] >> Cases_on `a` >> simp[] >> rw[]
QED


Theorem subapprox_ClosNoInline[simp]:
   (a ◁ ClosNoInline m n ⇔ a = ClosNoInline m n ∨ a = Impossible) ∧
   (ClosNoInline m n ◁ a ⇔ a = ClosNoInline m n ∨ a = Other)
Proof
  simp[subapprox_def] >> Cases_on `a` >> simp[] >> rw[] >>
  fs [DE_MORGAN_THM]
QED

Theorem subapprox_Clos[simp]:
   (a ◁ Clos m n e s ⇔ a = Clos m n e s ∨ a = Impossible) ∧
   (Clos m n e s ◁ a ⇔ a = Clos m n e s ∨ a = Other)
Proof
  simp[subapprox_def] >> Cases_on `a` >> simp[] >> rw[] >>
  fs [DE_MORGAN_THM]
QED

Theorem subapprox_Impossible[simp]:
   (a ◁ Impossible ⇔ a = Impossible) ∧ Impossible ◁ a
Proof
  simp[subapprox_def]
QED

Theorem subapprox_Tuple[simp]:
   Tuple tg1 as1 ◁ Tuple tg2 as2 ⇔ tg1 = tg2 ∧ LIST_REL subapprox as1 as2
Proof
  simp[subapprox_def, MAP2_MAP, LIST_REL_EL_EQN, bool_case_eq] >>
  Cases_on `LENGTH as1 = LENGTH as2` >> Cases_on `tg1 = tg2` >>
  simp[LIST_EQ_REWRITE, EL_MAP, EL_ZIP] >> metis_tac[]
QED

val better_definedg_def = Define`
  better_definedg g1 g2 ⇔
    ∀k. k ∈ domain g1 ⇒ k ∈ domain g2 ∧ THE (lookup k g1) ◁ THE (lookup k g2)
`;

Theorem better_definedg_refl[simp]:
   better_definedg g g
Proof
  simp[better_definedg_def]
QED

Theorem better_definedg_trans:
   better_definedg g1 g2 ∧ better_definedg g2 g3 ⇒ better_definedg g1 g3
Proof
  simp[better_definedg_def] >> metis_tac[subapprox_trans]
QED

Theorem known_op_better_definedg:
   known_op opn apxs g0 = (a,g) ⇒ better_definedg g0 g
Proof
  Cases_on `opn` >>
  simp[known_op_def, pair_case_eq, closSemTheory.case_eq_thms, va_case_eq, bool_case_eq] >> rw[] >>
  rw[better_definedg_def, lookup_insert] >>
  rw[] >> fs[lookup_NONE_domain]
QED

Theorem known_better_definedg:
   ∀c es apxs g0 alist g.
     known c es apxs g0 = (alist, g) ⇒ better_definedg g0 g
Proof
  ho_match_mp_tac known_ind >> simp[known_def] >>
  reverse (rpt strip_tac) >> rpt (pairarg_tac >> fs[]) >> rw[]
  >- (EVERY_CASE_TAC >> rpt (pairarg_tac >> fs[]) >> fs [] >>
      metis_tac[better_definedg_trans, known_op_better_definedg]) >>
  metis_tac[better_definedg_trans, known_op_better_definedg]
QED

Theorem mk_Ticks_alt:
   (!t tc e. mk_Ticks t tc 0 e = e) /\
   (!t tc n e. mk_Ticks t tc (SUC n) e = mk_Ticks t (tc + 1) n (Tick (t§tc) e))
Proof
  conj_tac \\ simp [Once mk_Ticks_def]
QED

val _ = export_theory();
