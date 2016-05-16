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

val merge_Other = Q.store_thm(
  "merge_Other[simp]",
  `merge Other a = Other ∧ merge a Other = Other`,
  Cases_on `a` >> simp[]);

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

(* See merge as a join operation on a semi-lattice: it's a join because it's
   a little akin to a union: as merge is used, more and more values might
   inhabit the approximation, with Other at the top corresponding to
   anything at all. *)
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

val subapprox_def = Define`
  subapprox a1 a2 ⇔ merge a1 a2 = a2
`;

val _ = set_mapped_fixity { fixity = Infix(NONASSOC, 450),
                            term_name = "subapprox",
                            tok = "<:" }

val subapprox_refl = Q.store_thm(
  "subapprox_refl[simp]",
  `a <: a`,
  simp[subapprox_def]);

val subapprox_trans = Q.store_thm(
  "subapprox_trans",
  `a1 <: a2 ∧ a2 <: a3 ⇒ a1 <: a3`,
  simp[subapprox_def] >> metis_tac[merge_assoc]);

val subapprox_antisym = Q.store_thm(
  "subapprox_antisym",
  `a1 <: a2 ∧ a2 <: a1 ⇒ a1 = a2`,
  simp[subapprox_def] >> metis_tac[merge_comm]);

val subapprox_merge = Q.store_thm(
  "subapprox_merge[simp]",
  `a <: merge a b ∧ a <: merge b a`,
  simp[subapprox_def] >>
  metis_tac[merge_assoc, merge_comm, merge_idem]);

val subapprox_Other = Q.store_thm(
  "subapprox_Other[simp]",
  `(Other <: a ⇔ (a = Other)) ∧ a <: Other`,
  simp[subapprox_def] >> metis_tac[]);

val subapprox_Int = Q.store_thm(
  "subapprox_Int[simp]",
  `(a <: Int i ⇔ a = Int i ∨ a = Impossible) ∧
   (Int i <: a ⇔ a = Int i ∨ a = Other)`,
  simp[subapprox_def] >> Cases_on `a` >> simp[] >> rw[]);

val subapprox_Clos = Q.store_thm(
  "subapprox_Clos[simp]",
  `(a <: Clos m n ⇔ a = Clos m n ∨ a = Impossible) ∧
   (Clos m n <: a ⇔ a = Clos m n ∨ a = Other)`,
  simp[subapprox_def] >> Cases_on `a` >> simp[] >> rw[]);

val subapprox_Impossible = Q.store_thm(
  "subapprox_Impossible[simp]",
  `(a <: Impossible ⇔ a = Impossible) ∧ Impossible <: a`,
  simp[subapprox_def]);

val subapprox_Tuple = Q.store_thm(
  "subapprox_Tuple[simp]",
  `Tuple as1 <: Tuple as2 ⇔ LIST_REL subapprox as1 as2`,
  simp[subapprox_def, MAP2_MAP, LIST_REL_EL_EQN] >>
  Cases_on `LENGTH as1 = LENGTH as2` >> simp[LIST_EQ_REWRITE, EL_MAP, EL_ZIP]);

(* "better" is arguable; g2 has more entries, but where they differ, g2's
   entries say less about the value *)
val better_definedg_def = Define`
  better_definedg g1 g2 ⇔
    ∀k. k ∈ domain g1 ⇒ k ∈ domain g2 ∧ THE (lookup k g1) <: THE (lookup k g2)
`;

val better_definedg_refl = Q.store_thm(
  "better_definedg_refl[simp]",
  `better_definedg g g`,
  simp[better_definedg_def]);

val better_definedg_trans = Q.store_thm(
  "better_definedg_trans",
  `better_definedg g1 g2 ∧ better_definedg g2 g3 ⇒ better_definedg g1 g3`,
  simp[better_definedg_def] >> metis_tac[subapprox_trans]);

val known_op_better_definedg = Q.store_thm(
  "known_op_better_definedg",
  `known_op opn apxs g0 = (a,g) ⇒ better_definedg g0 g`,
  Cases_on `opn` >> simp[known_op_def, pair_case_eq, eqs, va_case_eq,
                         bool_case_eq] >> rw[] >> rw[]
  >- (rw[better_definedg_def, lookup_insert] >> rw[] >>
      fs[lookup_NONE_domain])
  >- (rw[better_definedg_def, lookup_insert] >> rw[] >>
      simp[subapprox_def]));

val known_better_definedg = Q.store_thm(
  "known_better_definedg",
  `∀es apxs g0 alist g.
     known es apxs g0 = (alist, g) ⇒ better_definedg g0 g`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rw[] >>
  metis_tac[better_definedg_trans, known_op_better_definedg]);

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

val val_approx_better_approx = Q.store_thm(
  "val_approx_better_approx",
  `∀a1 v a2.
     a1 <: a2 ∧ val_approx_val a1 v ⇒ val_approx_val a2 v`,
  ho_match_mp_tac (theorem "val_approx_val_ind") >> dsimp[] >> rpt gen_tac >>
  qcase_tac `Tuple a2s <: apx2` >>
  Cases_on `apx2` >> dsimp[] >> simp[LIST_REL_EL_EQN] >> metis_tac[MEM_EL]);

val state_globals_approx_def = Define`
  state_globals_approx s g ⇔
    ∀k v a.
      lookup k g = SOME a ∧ get_global k s.globals = SOME (SOME v) ⇒
      val_approx_val a v
`;

(*
val state_approx_better_definedg = Q.store_thm(
  "state_approx_better_definedg",
  `better_definedg g1 g2 ∧ state_globals_approx s g1 ⇒
   state_globals_approx s g2`,
  simp[better_definedg_def, state_globals_approx_def] >> rpt strip_tac >>
  qcase_tac `lookup k g1 = SOME a` >>
  `k ∈ domain g1` by metis_tac[domain_lookup] >>
  `∃a'. lookup k g2 = SOME a' ∧ a <: a'` by metis_tac[domain_lookup, THE_DEF] >>



val eval_approx_def = Define`
  eval_approx g0 EA (:'ffi) es as ⇔
    ∀s0 env vs (s:'ffi closSem$state).
       evaluate(es, env, s0) = (Rval vs, s) ∧ state_globals_approx s0 g0 ∧
       LIST_REL val_approx_val EA env ⇒
       LIST_REL val_approx_val as vs
`;

val eval_approx_nil = Q.store_thm(
  "eval_approx_nil[simp]",
  `eval_approx g as (:'a) [] []`,
  simp[eval_approx_def, closSemTheory.evaluate_def]);

val evaluate_eq_nil = Q.store_thm(
  "evaluate_eq_nil[simp]",
  `closSem$evaluate(es,env,s0) = (Rval [], s) ⇔ s0 = s ∧ es = []`,
  Cases_on `es` >> simp[closSemTheory.evaluate_def] >>
  strip_tac >> qcase_tac `evaluate(h::t, env, s0)` >>
  Q.ISPECL_THEN [`h::t`, `env`, `s0`] mp_tac (CONJUNCT1 evaluate_LENGTH) >>
  simp[]);

val eval_approx_better_definedg = Q.store_thm(
  "eval_approx_better_definedg",
  `eval_approx g0 EA (:'a) exps apxs ∧ better_definedg g0 g ⇒
   eval_approx


val known_op_correct_approx = Q.store_thm(
  "known_op_correct_approx",
  `∀opn es apxs g0 a g EA.
      known_op opn apxs g0 = (a, g) ∧
      eval_approx g0 EA (:'a) es (REVERSE apxs) ⇒
      eval_approx g EA (:'a) [Op opn es] [a]`,
  Cases >> simp[eval_approx_def] >>
  dsimp[closSemTheory.evaluate_def, result_case_eq, pair_case_eq,
        closSemTheory.do_app_def, eqs, known_op_def]
  >- (simp[state_globals_approx_def, closSemTheory.get_global_def] >>
      rw[] >> metis_tac[])
  >- metis_tac[EVERY2_REVERSE1]
  >- (dsimp[va_case_eq, eqs, bool_case_eq] >> rpt strip_tac >>
      qcase_tac `closSem$evaluate (exps, ENV, S0) = (Rval vals, S1)` >>
      first_x_assum (qspecl_then [`S0`, `ENV`, `vals`, `S1`] mp_tac) >>
      simp[] >> strip_tac >> fs[] >> rw[] >> fs[LIST_REL_EL_EQN]))


val known_correct_approx = Q.store_thm(
  "known_correct_approx",
  `∀es as g0 all g.
     known es as g0 = (all,g) ⇒
     eval_approx g0 as (:'a) es (MAP SND all) ∧
     eval_approx g as (:'a) es (MAP SND all)`,
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
  >- ((* op *) qcase_tac `known exps as g0` >>
      `∃al1 g1. known exps as g0 = (al1, g1)` by metis_tac[pair_CASES] >>
      fs[] >> rw[] >> fs[]
  >> cheat )



*)

val _ = export_theory();
