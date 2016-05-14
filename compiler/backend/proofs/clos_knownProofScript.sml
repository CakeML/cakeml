open HolKernel Parse boolLib bossLib;

open preamble
open closPropsTheory clos_knownTheory

val _ = new_theory "clos_knownProof";

val bool_case_eq = Q.prove(
  `COND b t f = v ⇔ b /\ v = t ∨ ¬b ∧ v = f`,
  srw_tac[][] >> metis_tac[]);

val pair_case_eq = Q.prove (
`pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v`,
 Cases_on `x` >>
 srw_tac[][]);

val known_LENGTH = Q.store_thm(
  "known_LENGTH",
  `∀es vs g. LENGTH (FST (known es vs g)) = LENGTH es`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]))

val known_sing = Q.store_thm(
  "known_sing",
  `∀e vs g. ∃e' a g'. known [e] vs g = ([(e',a)], g')`,
  rpt strip_tac >> Cases_on `known [e] vs g` >>
  qcase_tac `known [e] vs g = (res,g')` >>
  qspecl_then [`[e]`, `vs`, `g`] mp_tac known_LENGTH >> simp[] >>
  Cases_on `res` >> simp[LENGTH_NIL] >> metis_tac[pair_CASES])

val _ = export_rewrites ["closLang.exp_size_def"]

val merge_Impossible = Q.store_thm(
  "merge_Impossible[simp]",
  `merge a Impossible = a`,
  Cases_on `a` >> simp[]);

(* merge defines a meet-semilattice *)
val merge_comm = Q.store_thm(
  "merge_comm",
  `∀a1 a2. merge a1 a2 = merge a2 a1`,
  ho_match_mp_tac merge_ind >> rpt strip_tac >> simp_tac(srw_ss()) [] >>
  COND_CASES_TAC >> simp[] >>
  simp[MAP2_MAP, MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_ZIP] >>
  metis_tac[MEM_EL]);

val merge_assoc = Q.store_thm(
  "merge_assoc",
  `∀a1 a2 a3. merge a1 (merge a2 a3) = merge (merge a1 a2) a3`,
  ho_match_mp_tac merge_ind >> rpt strip_tac >> Cases_on `a3` >>
  simp[] >> rw[LENGTH_MAP2]
  >- (simp[MAP2_MAP, MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >>
      metis_tac[MEM_EL]) >>
  rw[])

val merge_idem = Q.store_thm(
  "merge_idem[simp]",
  `merge a a = a`,
  completeInduct_on `val_approx_size a` >> Cases_on `a` >>
  simp[val_approx_size_def] >> strip_tac >> fs[PULL_FORALL] >>
  simp[MAP2_MAP, MAP_EQ_ID] >> rpt strip_tac >> first_x_assum match_mp_tac >>
  rw[] >> Induct_on `l` >> dsimp[val_approx_size_def] >> rpt strip_tac >>
  res_tac >> simp[]);

val better_defined_approx_def = Define`
  better_defined_approx a1 a2 ⇔ merge a1 a2 = a1
`;

val better_defined_approx_refl = Q.store_thm(
  "better_defined_approx_refl[simp]",
  `better_defined_approx a a`,
  simp[better_defined_approx_def]);

val better_definedg_def = Define`
  better_definedg g1 g2 ⇔
    ∀k. k ∈ domain g1 ⇒
        k ∈ domain g2 ∧
        better_defined_approx (THE (lookup k g1)) (THE (lookup k g2))
`;

val better_definedg_refl = Q.store_thm(
  "better_definedg_refl[simp]",
  `better_definedg g g`,
  simp[better_definedg_def]);

val va_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of ``:val_approx``,
                      nchotomy = TypeBase.nchotomy_of ``:val_approx``}
val result_ty = ``:(α,β)semanticPrimitives$result``
val result_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of result_ty,
                      nchotomy = TypeBase.nchotomy_of result_ty}
val error_ty = ``:α semanticPrimitives$error_result``
val error_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of error_ty,
                      nchotomy = TypeBase.nchotomy_of error_ty}


val val_approx_val_def = tDefine "val_approx_val" `
  (val_approx_val (Clos n m) v ⇔ ∃e1 e2 b. v = Closure (SOME n) e1 e2 m b) ∧
  (val_approx_val (Tuple vas) v ⇔
    ∃n vs. v = Block n vs ∧ LIST_REL (λv va. val_approx_val v va) vas vs) ∧
  (val_approx_val Impossible v ⇔ F) ∧
  (val_approx_val (Int i) v ⇔ v = Number i) ∧
  (val_approx_val Other v ⇔ T)
` (WF_REL_TAC `measure (val_approx_size o FST)` >> simp[] >> Induct >>
   dsimp[val_approx_size_def] >> rpt strip_tac >> res_tac >> simp[])

val val_approx_val_def = save_thm(
  "val_approx_val_def[simp]",
  val_approx_val_def |> SIMP_RULE (srw_ss() ++ ETA_ss) []);

val any_el_ALT = Q.store_thm(
  "any_el_ALT",
  `∀l n d. any_el n l d = if n < LENGTH l then EL n l else d`,
  Induct_on `l` >> simp[any_el_def] >> Cases_on `n` >> simp[] >> rw[] >>
  fs[]);

val merge_Other = Q.store_thm(
  "merge_Other[simp]",
  `merge Other a = Other ∧ merge a Other = Other`,
  Cases_on `a` >> simp[]);

val val_approx_val_merge_I = Q.store_thm(
  "val_approx_val_merge_I",
  `∀a1 v a2.
     val_approx_val a1 v ∨ val_approx_val a2 v ⇒
     val_approx_val (merge a1 a2) v`,
  ho_match_mp_tac (theorem "val_approx_val_ind") >>
  simp[] >> rpt strip_tac >> Cases_on `a2` >> simp[] >> fs[] >> rw[] >>
  fs[LIST_REL_EL_EQN, LENGTH_MAP2, MAP2_MAP, EL_MAP, EL_ZIP] >>
  metis_tac[MEM_EL])

val evaluate_list_members_individually = Q.store_thm(
  "evaluate_list_members_individually",
  `∀es env (s0:'a closSem$state) vs s.
     closSem$evaluate (es, env, s0) = (Rval vs, s) ⇒
     ∀n. n < LENGTH es ⇒
         ∃(s0':'a closSem$state) s'.
           evaluate([EL n es], env, s0') = (Rval [EL n vs], s')`,
  Induct >> simp[] >> Cases_on `es` >> fs[]
  >- (rpt strip_tac >> qcase_tac `evaluate ([exp], env, _)` >>
      `∃v. vs = [v]` by metis_tac[evaluate_SING] >> rw[] >> metis_tac[]) >>
  dsimp[closSemTheory.evaluate_def, pair_case_eq, result_case_eq] >>
  rpt strip_tac >> reverse (Cases_on `n` >> fs[]) >- metis_tac[] >>
  imp_res_tac evaluate_SING >> rw[] >> metis_tac[]);

val known_correct_approx = Q.store_thm(
  "known_correct_approx",
  `∀es as g0 all g.
     known es as g0 = (all,g) ⇒
     ∀e a vs s0 s v.
        MEM (e,a) all ∧ LIST_REL val_approx_val as vs ∧
        evaluate([e], vs, s0) = (Rval [v], s) ⇒
        val_approx_val a v`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac
  >- (qcase_tac `known [exp1] as g0` >>
      `∃exp1' a1 g1. known [exp1] as g0 = ([(exp1',a1)], g1)`
         by metis_tac[known_sing] >> fs[] >>
      qcase_tac `known (exp2::erest) as g1` >>
      `∃arest g2. known (exp2::erest) as g1 = (arest, g2)`
         by metis_tac[pair_CASES] >> fs[] >> rw[] >> fs[] >> metis_tac[])
  >- (fs[any_el_ALT, closSemTheory.evaluate_def, bool_case_eq] >>
      fs[LIST_REL_EL_EQN])
  >- (qcase_tac `known [ge] as g0` >>
      `∃ge' a1 g1. known [ge] as g0 = ([(ge',a1)], g1)`
         by metis_tac[known_sing] >> fs[] >>
      qcase_tac `known [tb] as g1` >>
      `∃tb' a2 g2. known [tb] as g1 = ([(tb',a2)], g2)`
         by metis_tac[known_sing] >> fs[] >>
      qcase_tac `known [eb] as g2` >>
      `∃eb' a3 g3. known [eb] as g2 = ([(eb',a3)], g3)`
         by metis_tac[known_sing] >> fs[] >> rw[] >> fs[] >> rw[] >>
      fs[closSemTheory.evaluate_def, pair_case_eq, result_case_eq,
         bool_case_eq] >> metis_tac[val_approx_val_merge_I])
  >- ((* let *) qcase_tac `known binds as g0` >>
      `∃al1 g1. known binds as g0 = (al1,g1)` by metis_tac[pair_CASES] >>
      fs[] >>
      qcase_tac `known [bod] (MAP SND al1 ++ as) g1` >>
      `∃bod' ba g2. known [bod] (MAP SND al1 ++ as) g1 = ([(bod',ba)], g2)`
        by metis_tac [known_sing] >> fs[] >> rw[] >> fs[] >> rw[] >>
      fs[closSemTheory.evaluate_def, pair_case_eq, result_case_eq] >> rw[] >>
      qcase_tac `evaluate (MAP FST al1,vs,s0) = (Rval res1, s1)` >>
      `LENGTH res1 = LENGTH al1`
        by (Q.ISPECL_THEN [`MAP FST al1`, `vs`, `s0`] mp_tac
                          (evaluate_LENGTH |> CONJUNCT1) >> simp[]) >>
      first_x_assum (qspecl_then [`res1 ++ vs`, `s1`, `s`, `v`] mp_tac) >>
      impl_tac >> simp[] >> irule EVERY2_APPEND_suff >> simp[] >>
      simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >> first_x_assum irule >>
      simp[] >>
      qspecl_then [`MAP FST al1`, `vs`, `s0`, `res1`, `s1`] mp_tac
        evaluate_list_members_individually >> simp[] >>
      disch_then (qspec_then `n` mp_tac) >> simp[EL_MAP] >>
      metis_tac[PAIR, MEM_EL])
  >- ((* raise *) qcase_tac `known [exp1] as g0` >>
      `∃exp' ea g1. known [exp1] as g0 = ([(exp',ea)], g1)`
        by metis_tac [known_sing] >> fs[] >> rw[] >> fs[] >> rw[] >>
      fs[closSemTheory.evaluate_def, pair_case_eq, result_case_eq])
  >- ((* tick *) qcase_tac `known [exp1] as g0` >>
      `∃exp' ea g1. known [exp1] as g0 = ([(exp',ea)], g1)`
        by metis_tac [known_sing] >> fs[] >> rw[] >> fs[] >> rw[] >>
      fs[closSemTheory.evaluate_def, pair_case_eq, result_case_eq,
         bool_case_eq] >> metis_tac[])
  >- ((* handle *) qcase_tac `known [exp1] as g0` >>
      `∃exp1' ea1 g1. known [exp1] as g0 = ([(exp1',ea1)], g1)`
        by metis_tac [known_sing] >> fs[] >> rw[] >>
      qcase_tac `known [exp2] (Other::as) g1` >>
      `∃exp2' ea2 g2. known [exp2] (Other::as) g1 = ([(exp2',ea2)], g2)`
        by metis_tac [known_sing] >> fs[] >> rw[] >> fs[] >> rw[] >>
      fs[closSemTheory.evaluate_def, pair_case_eq, result_case_eq,
         error_case_eq] >> rw[] >- metis_tac[val_approx_val_merge_I] >>
      irule val_approx_val_merge_I >> disj2_tac >> first_x_assum irule >>
      dsimp[] >> metis_tac[])
  >- ((* call *) qcase_tac `known exps as g0` >>
      `∃al1 g1. known exps as g0 = (al1, g1)` by metis_tac[pair_CASES] >>
      fs[] >> rw[] >> fs[])
  >> cheat )





val _ = export_theory();
