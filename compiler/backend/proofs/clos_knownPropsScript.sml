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

Theorem merge_Other[simp]
  `merge Other a = Other ∧ merge a Other = Other`
  (Cases_on `a` >> simp[]);

Theorem merge_Impossible[simp]
  `merge a Impossible = a`
  (Cases_on `a` >> simp[]);

(* See merge as a join operation on a semi-lattice: it's a join because it's
   a little akin to a union: as merge is used, more and more values might
   inhabit the approximation, with Other at the top corresponding to
   anything at all. *)
Theorem merge_comm
  `∀a1 a2. merge a1 a2 = merge a2 a1`
  (ho_match_mp_tac merge_ind >> rpt strip_tac >> simp_tac(srw_ss()) [] >>
  COND_CASES_TAC >> simp[] >>
  simp[MAP2_MAP, MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_ZIP] >>
  metis_tac[MEM_EL]);

Theorem merge_assoc
  `∀a1 a2 a3. merge a1 (merge a2 a3) = merge (merge a1 a2) a3`
  (ho_match_mp_tac merge_ind >> rpt strip_tac >> Cases_on `a3` >>
  simp[] >> rw[LENGTH_MAP2]
  >- (simp[MAP2_MAP, MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >>
      metis_tac[MEM_EL]) >>
  rw[])

Theorem merge_idem[simp]
  `merge a a = a`
  (completeInduct_on `val_approx_size a` >> Cases_on `a` >>
  simp[val_approx_size_def] >> strip_tac >> fs[PULL_FORALL] >>
  simp[MAP2_MAP, MAP_EQ_ID] >> rpt strip_tac >> first_x_assum match_mp_tac >>
  rw[] >> Induct_on `l` >> dsimp[val_approx_size_def] >> rpt strip_tac >>
  res_tac >> simp[]);

val subapprox_def = Define`
  subapprox a1 a2 ⇔ merge a1 a2 = a2
`;

val _ = set_fixity "◁" (Infix(NONASSOC,450))
val _ = overload_on ("◁", ``subapprox``)

Theorem subapprox_refl[simp]
  `a ◁ a`
  (simp[subapprox_def]);

Theorem subapprox_trans
  `a1 ◁ a2 ∧ a2 ◁ a3 ⇒ a1 ◁ a3`
  (simp[subapprox_def] >> metis_tac[merge_assoc]);

Theorem subapprox_antisym
  `a1 ◁ a2 ∧ a2 ◁ a1 ⇒ a1 = a2`
  (simp[subapprox_def] >> metis_tac[merge_comm]);

Theorem subapprox_merge[simp]
  `a ◁ merge a b ∧ a ◁ merge b a`
  (simp[subapprox_def] >>
  metis_tac[merge_assoc, merge_comm, merge_idem]);

Theorem subapprox_Other[simp]
  `(Other ◁ a ⇔ (a = Other)) ∧ a ◁ Other`
  (simp[subapprox_def] >> metis_tac[]);

Theorem subapprox_Int[simp]
  `(a ◁ Int i ⇔ a = Int i ∨ a = Impossible) ∧
   (Int i ◁ a ⇔ a = Int i ∨ a = Other)`
  (simp[subapprox_def] >> Cases_on `a` >> simp[] >> rw[]);


Theorem subapprox_ClosNoInline[simp]
  `(a ◁ ClosNoInline m n ⇔ a = ClosNoInline m n ∨ a = Impossible) ∧
   (ClosNoInline m n ◁ a ⇔ a = ClosNoInline m n ∨ a = Other)`
  (simp[subapprox_def] >> Cases_on `a` >> simp[] >> rw[] >>
  fs [DE_MORGAN_THM]);

Theorem subapprox_Clos[simp]
  `(a ◁ Clos m n e s ⇔ a = Clos m n e s ∨ a = Impossible) ∧
   (Clos m n e s ◁ a ⇔ a = Clos m n e s ∨ a = Other)`
  (simp[subapprox_def] >> Cases_on `a` >> simp[] >> rw[] >>
  fs [DE_MORGAN_THM]);

Theorem subapprox_Impossible[simp]
  `(a ◁ Impossible ⇔ a = Impossible) ∧ Impossible ◁ a`
  (simp[subapprox_def]);

Theorem subapprox_Tuple[simp]
  `Tuple tg1 as1 ◁ Tuple tg2 as2 ⇔ tg1 = tg2 ∧ LIST_REL subapprox as1 as2`
  (simp[subapprox_def, MAP2_MAP, LIST_REL_EL_EQN, bool_case_eq] >>
  Cases_on `LENGTH as1 = LENGTH as2` >> Cases_on `tg1 = tg2` >>
  simp[LIST_EQ_REWRITE, EL_MAP, EL_ZIP] >> metis_tac[]);

val better_definedg_def = Define`
  better_definedg g1 g2 ⇔
    ∀k. k ∈ domain g1 ⇒ k ∈ domain g2 ∧ THE (lookup k g1) ◁ THE (lookup k g2)
`;

Theorem better_definedg_refl[simp]
  `better_definedg g g`
  (simp[better_definedg_def]);

Theorem better_definedg_trans
  `better_definedg g1 g2 ∧ better_definedg g2 g3 ⇒ better_definedg g1 g3`
  (simp[better_definedg_def] >> metis_tac[subapprox_trans])

Theorem known_op_better_definedg
  `known_op opn apxs g0 = (a,g) ⇒ better_definedg g0 g`
  (Cases_on `opn` >>
  simp[known_op_def, pair_case_eq, closSemTheory.case_eq_thms, va_case_eq, bool_case_eq] >> rw[] >>
  rw[better_definedg_def, lookup_insert] >>
  rw[] >> fs[lookup_NONE_domain])

Theorem known_better_definedg
  `∀c es apxs g0 alist g.
     known c es apxs g0 = (alist, g) ⇒ better_definedg g0 g`
  (ho_match_mp_tac known_ind >> simp[known_def] >>
  reverse (rpt strip_tac) >> rpt (pairarg_tac >> fs[]) >> rw[]
  >- (EVERY_CASE_TAC >> rpt (pairarg_tac >> fs[]) >> fs [] >>
      metis_tac[better_definedg_trans, known_op_better_definedg]) >>
  metis_tac[better_definedg_trans, known_op_better_definedg]);

Theorem mk_Ticks_alt
  `(!t tc e. mk_Ticks t tc 0 e = e) /\
   (!t tc n e. mk_Ticks t tc (SUC n) e = mk_Ticks t (tc + 1) n (Tick (t§tc) e))`
  (conj_tac \\ simp [Once mk_Ticks_def]);

val _ = export_theory();
