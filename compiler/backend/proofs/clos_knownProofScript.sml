open HolKernel Parse boolLib bossLib;

open preamble
open closPropsTheory clos_knownTheory closSemTheory
open clos_knownPropsTheory
open bagTheory

val _ = new_theory "clos_knownProof";

val bool_case_eq = Q.prove(
  `COND b t f = v ⇔ b /\ v = t ∨ ¬b ∧ v = f`,
  srw_tac[][] >> metis_tac[]);

val pair_case_eq = Q.prove (
`pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v`,
 Cases_on `x` >>
 srw_tac[][]);

val value_CASES = TypeBase.nchotomy_of ``:closSem$v``
val v_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of ``:closSem$v``,
                      nchotomy = value_CASES}

val ref_CASES = TypeBase.nchotomy_of ``:α closSem$ref``

val va_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of ``:val_approx``,
                      nchotomy = TypeBase.nchotomy_of ``:val_approx``}
val result_ty = ``:(α,β)semanticPrimitives$result``
val result_CASES = TypeBase.nchotomy_of result_ty
val result_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of result_ty,
                      nchotomy = result_CASES}
val error_ty = ``:α semanticPrimitives$error_result``
val error_CASES = TypeBase.nchotomy_of error_ty
val error_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of error_ty,
                      nchotomy = error_CASES}

(* MOVE candidates *)
fun nailIHx k = let
  fun hdt t = (t |> lhs |> strip_comb |> #1)
              handle HOL_ERR _ => t |> strip_comb |> #1
  fun sameish t1 t2 = aconv t1 t2 orelse same_const t1 t2
  fun samehd t1 th2 = sameish (hdt t1) (hdt (concl th2))
  fun findcs [] a k = raise Fail "strip_conj gave empty list"
    | findcs [c] a k =
      first_assum
        (fn th => k (LIST_CONJ (List.rev (assert (samehd c) th :: a))))
    | findcs (c::cs) a k =
      first_assum (fn th => findcs cs (assert (samehd c) th :: a) k)
in
  first_x_assum
    (fn th0 =>
        let val body = th0 |> concl |> strip_forall |> #2
            val hyp = #1 (dest_imp body)
            val cs = strip_conj hyp
        in
          findcs cs [] (k o MATCH_MP th0)
        end)
end

fun avSPEC_ALL avds th =
  let
    fun recurse avds acc th =
      case Lib.total dest_forall (concl th) of
          SOME (v,bod) =>
          let
            val v' = variant avds v
          in
            recurse (v'::avds) (v'::acc) (SPEC v' th)
          end
        | NONE => (List.rev acc, th)
  in
    recurse avds [] th
  end

fun PART_MATCH' f th t =
  let
    val (vs, _) = strip_forall (concl th)
    val hypfvs_set = hyp_frees th
    val hypfvs = HOLset.listItems hypfvs_set
    val tfvs = free_vars t
    val dontspec = union tfvs hypfvs
    val (vs, speccedth) = avSPEC_ALL dontspec th
    val ((tmsig,_),_) = raw_match [] hypfvs_set (f (concl speccedth)) t ([],[])
    val dontgen = union (map #redex tmsig) dontspec
  in
    GENL (set_diff vs dontgen) (INST tmsig speccedth)
  end

fun asmPART_MATCH' f th t =
    PART_MATCH' (f o strip_conj o #1 o dest_imp) th t

fun sel_ihpc f =
    first_assum (fn asm => first_x_assum (fn ih =>
      mp_tac (asmPART_MATCH' f ih (concl asm))))

fun resolve_selected f th =
  first_assum (mp_tac o asmPART_MATCH' f th o concl)

fun patresolve p f th =
  qpat_assum p (fn cth => mp_tac (asmPART_MATCH' f th (concl cth)) >>
                          assume_tac cth)

val _ = export_rewrites ["closLang.exp_size_def"]

val any_el_ALT = Q.store_thm(
  "any_el_ALT",
  `∀l n d. any_el n l d = if n < LENGTH l then EL n l else d`,
  Induct_on `l` >> simp[any_el_def] >> Cases_on `n` >> simp[] >> rw[] >>
  fs[]);

val exp_size_MEM = Q.store_thm(
  "exp_size_MEM",
  `(∀e elist. MEM e elist ⇒ exp_size e < exp3_size elist) ∧
   (∀x e ealist. MEM (x,e) ealist ⇒ exp_size e < exp1_size ealist)`,
  conj_tac >| [Induct_on `elist`, Induct_on `ealist`] >> dsimp[] >>
  rpt strip_tac >> res_tac >> simp[]);

val evaluate_eq_nil = Q.store_thm(
  "evaluate_eq_nil[simp]",
  `closSem$evaluate(es,env,s0) = (Rval [], s) ⇔ s0 = s ∧ es = []`,
  Cases_on `es` >> simp[evaluate_def] >>
  strip_tac >> qcase_tac `evaluate(h::t, env, s0)` >>
  Q.ISPECL_THEN [`h::t`, `env`, `s0`] mp_tac (CONJUNCT1 evaluate_LENGTH) >>
  simp[]);

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
  dsimp[evaluate_def, pair_case_eq, result_case_eq] >>
  rpt strip_tac >> reverse (Cases_on `n` >> fs[]) >- metis_tac[] >>
  imp_res_tac evaluate_SING >> rw[] >> metis_tac[]);

(* MOVE-HOL candidate *)
val union_idem = Q.store_thm(
  "union_idem[simp]",
  `∀spt. union spt spt = spt`,
  Induct >> simp[union_def]);

val _ = temp_overload_on ("⊌", ``union``)


(* simple properties of constants from clos_known: i.e., merge and known *)
val opn_fresh_def = Define`
  (opn_fresh (SetGlobal n) g ⇔ n ∉ domain g) ∧
  (opn_fresh _ g ⇔ T)
`;

val gidem_op_def = Define`
  gidem_op apxs opn ⇔
    ∀g0 apx0 g. known_op opn apxs g0 = (apx0,g) ⇒
                ∃apx. known_op opn apxs g = (apx,g)
`;

val non_SetGlobal_gidem_op = Q.store_thm(
  "non_SetGlobal_gidem_op",
  `(∀n. opn ≠ SetGlobal n) ⇒ gidem_op apxs opn`,
  Cases_on `opn` >>
  simp[gidem_op_def, known_op_def, eqs, va_case_eq, bool_case_eq] >> dsimp[]);

val safe_op_def = Define`
  safe_op opn apxs g0 ⇔
    ∀n a0. opn = SetGlobal n ∧ lookup n g0 = SOME a0 ⇒ apxs = [a0]
`;

val no_top_getGlobal_def = tDefine "no_top_getGlobal" `
  (no_top_getGlobal (Var _) = T) ∧
  (no_top_getGlobal (If e1 e2 e3) ⇔
    no_top_getGlobal e1 ∧ no_top_getGlobal e2 ∧ no_top_getGlobal e3) ∧
  (no_top_getGlobal (Let bs e) ⇔
    (∀b. MEM b bs ⇒ no_top_getGlobal b) ∧ no_top_getGlobal e) ∧
  (no_top_getGlobal (Raise e) ⇔ no_top_getGlobal e) ∧
  (no_top_getGlobal (Handle e1 e2) ⇔
    no_top_getGlobal e1 ∧ no_top_getGlobal e2) ∧
  (no_top_getGlobal (Tick e) ⇔ no_top_getGlobal e) ∧
  (no_top_getGlobal (Call _ es) ⇔ ∀e. MEM e es ⇒ no_top_getGlobal e) ∧
  (no_top_getGlobal (App _ f args) ⇔
    no_top_getGlobal f ∧ ∀a. MEM a args ⇒ no_top_getGlobal a) ∧
  (no_top_getGlobal (Fn _ _ _ _) ⇔ T) ∧
  (no_top_getGlobal (Letrec _ _ _ b) = no_top_getGlobal b) ∧
  (no_top_getGlobal (Op opn args) ⇔
    (∀n. opn ≠ Global n) ∧ ∀a. MEM a args ⇒ no_top_getGlobal a)
` (WF_REL_TAC `measure exp_size` >> simp[] >> rpt strip_tac >>
   imp_res_tac exp_size_MEM >> simp[])

(* val no_top_getGlobal_g_varies = Q.store_thm(
  "no_top_getGlobal_g_varies",
  `∀es as g0 alist g.
    known es as g0 = (alist,g) ∧ (∀e. MEM e es ⇒ no_top_getGlobal e) ⇒
    ∀g0'. ∃g'. known es as g0' = (alist,g')`,
  ho_match_mp_tac known_ind >> simp[known_def, no_top_getGlobal_def] >>
  rpt strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt (pairarg_tac >> fs[]) >> rveq >> imp_res_tac known_sing_EQ_E >> rveq >>
  fs[] >> rveq >>
  TRY (qcase_tac `known_op opn` >> Cases_on `opn` >>
       fs[known_op_def, eqs, va_case_eq, bool_case_eq] >>
       rveq >> simp[] >> metis_tac[PAIR_EQ, REVERSE, MAP, NOT_CONS_NIL])
  >- metis_tac[PAIR_EQ, CONS_11]
  >- metis_tac[PAIR_EQ, CONS_11]
  >- metis_tac[PAIR_EQ, CONS_11]
  >- metis_tac[PAIR_EQ, CONS_11]
  >- metis_tac[PAIR_EQ, CONS_11]
  >- metis_tac[PAIR_EQ, CONS_11] *)

val safe_opsetg_def = Define`
  safe_opsetg opn args =
    (∀n. opn = SetGlobal n ⇒
         ∃a. args = [a] ∧ no_top_getGlobal a)
`;

val op_gbag_def = Define`
  op_gbag (SetGlobal n) = BAG_INSERT n {||} ∧
  op_gbag _ = {||}
`;

val set_globals_def = tDefine "set_globals" `
  (set_globals (Var _) = {||}) ∧
  (set_globals (If e1 e2 e3) =
    set_globals e1 ⊎ set_globals e2 ⊎ set_globals e3) ∧
  (set_globals (Let binds e) =
    FOLDR $BAG_UNION (set_globals e) (MAP set_globals binds)) ∧
  (set_globals (Raise e) = set_globals e) ∧
  (set_globals (Handle e1 e2) = set_globals e1 ⊎ set_globals e2) ∧
  (set_globals (Tick e) = set_globals e) ∧
  (set_globals (Call _ args) = FOLDR $BAG_UNION {||} (MAP set_globals args)) ∧
  (set_globals (App _ f args) =
    FOLDR $BAG_UNION (set_globals f) (MAP set_globals args)) ∧
  (set_globals (Fn _ _ _ bod) = set_globals bod) ∧
  (set_globals (Letrec _ _ fbinds bod) =
    FOLDR (λne s. set_globals (SND ne) ⊎ s) (set_globals bod) fbinds) ∧
  (set_globals (Op opn args) =
    FOLDR $BAG_UNION (op_gbag opn) (MAP set_globals args))
`
  (WF_REL_TAC `measure exp_size` >> simp[] >> rpt strip_tac >>
   imp_res_tac exp_size_MEM >> simp[])

val elist_globals_def = Define`
  elist_globals es = FOLDR BAG_UNION {||} (MAP set_globals es)
`;
val elist_globals_thm = Q.store_thm(
  "elist_globals_thm[simp]",
  `elist_globals [] = {||} ∧
   elist_globals (exp::rest) = set_globals exp ⊎ elist_globals rest`,
  simp[elist_globals_def]);

val FOLDR_BAG_UNION_extract_acc = Q.store_thm(
  "FOLDR_BAG_UNION_extract_acc",
  `∀l a b. a ⊎ FOLDR (BAG_UNION o f) b l = FOLDR (BAG_UNION o f) (a ⊎ b) l`,
  Induct_on `l` >> simp[] >> metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION])
val foldr_bu =
    FOLDR_BAG_UNION_extract_acc |> SPEC_ALL
                                |> INST_TYPE [alpha |-> ``:β bag``]
                                |> Q.INST [`b` |-> `{||}`, `f` |-> `I`]
                                |> SIMP_RULE (srw_ss()) []
                                |> GSYM

val foldr_bu' =
    FOLDR_BAG_UNION_extract_acc |> SPEC_ALL
                                |> Q.INST [`b` |-> `{||}`, `f` |-> `λa. g a`]
                                |> SIMP_RULE (srw_ss()) [o_ABS_R]
                                |> GSYM


val set_globals_def = save_thm("set_globals_def[simp]",
  set_globals_def |> ONCE_REWRITE_RULE [foldr_bu]
                  |> SIMP_RULE (srw_ss() ++ ETA_ss) [GSYM elist_globals_def])
val set_globals_ind = theorem "set_globals_ind"

val known_op_changed_globals = Q.store_thm(
  "known_op_changed_globals",
  `∀opn as g0 a g.
     known_op opn as g0 = (a,g) ⇒
     ∀i. i ∈ domain g ∧ (i ∈ domain g0 ⇒ lookup i g ≠ lookup i g0) ⇒
         i ∈ SET_OF_BAG (op_gbag opn)`,
  rpt gen_tac >> Cases_on `opn` >>
  simp[known_op_def, eqs, op_gbag_def, pair_case_eq, va_case_eq,
       bool_case_eq] >> rw[] >>
  fs[bool_case_eq, lookup_insert]);

val known_changed_globals = Q.store_thm(
  "known_changed_globals",
  `∀es as g0 alist g.
     known es as g0 = (alist, g) ⇒
     ∀i. i ∈ domain g ∧ (i ∈ domain g0 ⇒ lookup i g ≠ lookup i g0) ⇒
         i ∈ SET_OF_BAG (elist_globals es)`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rveq >> fs[]
  >- (map_every qcase_tac [`known [exp1] as g0 = (al,g')`,`i ∈ domain g`] >>
      Cases_on `i ∈ domain g'` >> fs[] >>
      Cases_on `i ∈ domain g0` >> fs[] >>
      Cases_on `lookup i g' = lookup i g0` >> fs[])
  >- (map_every qcase_tac [
        `known [exp1] as g0 = (al1,g1)`,
        `known [exp2] as g1 = (al2,g2)`,
        `known [exp3] as g2 = (al3,g3)`] >>
      Cases_on `i ∈ domain g2` >> fs[] >>
      Cases_on `i ∈ domain g1` >> fs[] >>
      Cases_on `i ∈ domain g0` >> fs[] >>
      Cases_on `lookup i g1 = lookup i g0` >> fs[] >>
      Cases_on `lookup i g2 = lookup i g1` >> fs[])
  >- (qcase_tac `known exps as g0 = (al1,g1)` >>
      Cases_on `i ∈ domain g1` >> fs[] >>
      Cases_on `i ∈ domain g0` >> fs[] >>
      Cases_on `lookup i g1 = lookup i g0` >> fs[])
  >- (qcase_tac `known _ _  g0 = (al1,g1)` >>
      Cases_on `i ∈ domain g1` >> fs[] >>
      Cases_on `i ∈ domain g0` >> fs[] >>
      Cases_on `lookup i g1 = lookup i g0` >> fs[])
  >- (qcase_tac `known _ _  g0 = (_,g1)` >>
      qcase_tac `known_op opn` >>
      Cases_on `i ∈ domain g1` >> fs[]
      >- (Cases_on `i ∈ domain g0` >> fs[] >>
          Cases_on `lookup i g1 = lookup i g0` >> fs[] >>
          resolve_selected hd known_op_changed_globals >> simp[]) >>
      resolve_selected hd known_op_changed_globals >> simp[])
  >- (qcase_tac `known _ _ g0 = (_, g1)` >>
      Cases_on `i ∈ domain g1` >> fs[] >>
      Cases_on `lookup i g1 = lookup i g0` >> fs[] >>
      Cases_on `lookup i g = lookup i g1` >> fs[])
  >- simp[Once foldr_bu'])

val subspt_def = Define`
  subspt sp1 sp2 ⇔
    ∀k. k ∈ domain sp1 ⇒ k ∈ domain sp2 ∧ lookup k sp2 = lookup k sp1
`;

val subspt_refl = Q.store_thm(
  "subspt_refl[simp]",
  `subspt sp sp`,
  simp[subspt_def])

val subspt_trans = Q.store_thm(
  "subspt_trans",
  `subspt sp1 sp2 ∧ subspt sp2 sp3 ⇒ subspt sp1 sp3`,
  metis_tac[subspt_def]);

val subspt_better_definedg = Q.store_thm(
  "subspt_better_definedg",
  `subspt sp1 sp3 ∧ better_definedg sp1 sp2 ∧ better_definedg sp2 sp3 ⇒
   subspt sp1 sp2`,
  simp[subspt_def, better_definedg_def] >> rpt strip_tac >>
  spose_not_then assume_tac >>
  `k ∈ domain sp2 ∧ k ∈ domain sp3` by metis_tac [] >>
  `∃v1 v2 v3. lookup k sp1 = SOME v1 ∧ lookup k sp2 = SOME v2 ∧
              lookup k sp3 = SOME v3` by metis_tac[domain_lookup] >>
  `v3 = v1` by metis_tac[SOME_11] >> rveq >>
  `v1 ◁ v2 ∧ v2 ◁ v1` by metis_tac[THE_DEF] >>
  metis_tac[subapprox_antisym])

val subspt_known_elist_globals = Q.store_thm(
  "subspt_known_elist_globals",
  `∀es1 as1 g0 al1 g1 es2 as2 al2 g2.
     known es1 as1 g0 = (al1, g1) ∧ known es2 as2 g1 = (al2, g2) ∧
     subspt g0 g2 ∧ BAG_DISJOINT (elist_globals es1) (elist_globals es2) ⇒
     subspt g0 g1 ∧ subspt g1 g2`,
  rpt gen_tac >> strip_tac >>
  `subspt g0 g1` by metis_tac[known_better_definedg, subspt_better_definedg] >>
  simp[] >> fs[subspt_def] >>
  rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
  `better_definedg g1 g2` by metis_tac[known_better_definedg] >>
  `k ∈ domain g2` by fs[better_definedg_def] >> simp[] >>
  spose_not_then strip_assume_tac >>
  `k ∈ SET_OF_BAG (elist_globals es2)` by metis_tac[known_changed_globals] >>
  Cases_on `k ∈ domain g0` >- metis_tac[] >>
  `k ∈ SET_OF_BAG (elist_globals es1)` by metis_tac[known_changed_globals] >>
  fs[BAG_DISJOINT, DISJOINT_DEF, EXTENSION] >> metis_tac[])

val subspt_known_op_elist_globals = Q.store_thm(
  "subspt_known_op_elist_globals",
  `∀es as1 g0 al1 g1 opn as2 g2 a.
      known es as1 g0 = (al1,g1) ∧ known_op opn as2 g1 = (a,g2) ∧ subspt g0 g2 ∧
      BAG_DISJOINT (op_gbag opn) (elist_globals es) ⇒
      subspt g0 g1 ∧ subspt g1 g2`,
  rpt gen_tac >> strip_tac >>
  `subspt g0 g1`
    by metis_tac[known_better_definedg, subspt_better_definedg,
                 known_op_better_definedg] >> simp[] >>
  fs[subspt_def] >> rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
  `better_definedg g1 g2` by metis_tac[known_op_better_definedg] >>
  `k ∈ domain g2` by fs[better_definedg_def] >> simp[] >>
  spose_not_then strip_assume_tac >>
  `k ∈ SET_OF_BAG (op_gbag opn)` by metis_tac[known_op_changed_globals] >>
  Cases_on `k ∈ domain g0` >- metis_tac[] >>
  `k ∈ SET_OF_BAG (elist_globals es)` by metis_tac[known_changed_globals] >>
  fs[BAG_DISJOINT, DISJOINT_DEF, EXTENSION] >> metis_tac[])

(*
val safe_setglobals_known_fixed_union = Q.store_thm(
  "safe_setglobals_known_fixed_union",
  `∀es as g0 alist g.
      known es as g0 = (alist,g) ∧
      (∀e. MEM e es ⇒ safe_setglobals e)
     ⇒
      ∃Δ. g = Δ ⊌ g0 ∧
          ∀g0'. ∃alist'. known es as g0' = (alist',Δ ⊌ g0')`,
  ho_match_mp_tac known_ind >> simp[known_def, safe_setglobals_def] >>
  rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
  imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq
  >- (qexists_tac `LN` >> simp[])
  >- (full_simp_tac (srw_ss() ++ DNF_ss) [] >>
      qcase_tac `g = union Δ₁ (union Δ₂ g0)` >>
      qexists_tac `union Δ₁ Δ₂` >> simp[union_assoc] >> qx_gen_tac `g0'` >>
      map_every qcase_tac [
        `known [exp1] as g0 = _`,
        `known (exp2::exps) as _ = _`
      ] >>
      `∃alist0. known [exp1] as g0' = (alist0,union Δ₂ g0')` by metis_tac[] >>
      simp[] >>
      `∃alist1.
        known (exp2::exps) as (union Δ₂ g0') = (alist1,union Δ₁ (union Δ₂ g0'))`
          by metis_tac[] >> simp[union_assoc])
  >- (qexists_tac `LN` >> simp[])
  >- (qcase_tac `union d3 (union d2 (union d1 g0)) = union _ g0` >>
      qexists_tac `union d3 (union d2 d1)` >> simp[union_assoc] >>
      qx_gen_tac `g0'` >> qcase_tac `known [exp1] as g0'` >>
      `∃a1. known [exp1] as g0' = (a1,union d1 g0')` by metis_tac[] >> simp[] >>
      qcase_tac `known [exp2] as (union d1 g0')` >>
      `∃a2. known [exp2] as (union d1 g0') = (a2,union d2 (union d1 g0'))`
        by metis_tac[] >> simp[] >>
      qcase_tac `known [exp3] as (d2 ⊌ (d1 ⊌ g0'))` >>
      `∃a3. known [exp3] as (d2 ⊌ (d1 ⊌ g0')) = (a3, d3 ⊌ (d2 ⊌ (d1 ⊌ g0')))`
        by metis_tac[] >> simp[] >>
      imp_res_tac known_sing_EQ_E >> fs[] >> rveq >> simp[union_assoc])
  >- (qcase_tac `d2 ⊌ (d1 ⊌ g0) = _ ⊌ g0` >> qexists_tac `d2 ⊌ d1` >>
      simp[union_assoc] >> qx_gen_tac


val safe_setglobals_known_subspt = Q.store_thm(
  "safe_setglobals_known_subspt",
  `∀es as g0 alist g g1.
      known es as g0 = (alist,g) ∧ subspt g0 g1 ∧ subspt g0 g ∧
      (∀e. MEM e es ⇒ safe_setglobals e)
     ⇒
      ∃alist' g'. known es as g1 = (alist',g') ∧
                  MAP FST alist' = MAP FST alist`,
  ho_match_mp_tac known_ind >> simp[known_def, safe_setglobals_def] >>
  rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
  imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq
  >- (full_simp_tac (srw_ss() ++ DNF_ss) [] >>
      map_every qcase_tac [
        `subspt g0 g1`, `known [exp0] as g0 = ([(exp1,apx1)], g01)`,
        `known [exp0] as g1 = ([(exp2,apx2)], g02)`] >>
      `subspt g0 g01`
        by metis_tac[subspt_better_definedg, known_better_definedg] >>
      first_x_assum
        (fn th => qspec_then `g1` mp_tac th >> simp[] >>
                  disch_then (assume_tac o assert (not o is_imp o concl))) >>
      rveq

*)

val opn_fresh_gbag = Q.store_thm(
  "opn_fresh_gbag",
  `opn_fresh opn g ⇔ DISJOINT (SET_OF_BAG (op_gbag opn)) (domain g)`,
  Cases_on `opn` >> simp[opn_fresh_def, op_gbag_def] >>
  simp[DISJOINT_DEF, SET_OF_BAG_INSERT, EXTENSION]);

val known_op_adds_gbag = Q.store_thm(
  "known_op_adds_gbag",
  `known_op opn apxs g0 = (apx,g) ⇒
   domain g ⊆ domain g0 ∪ SET_OF_BAG (op_gbag opn)`,
  Cases_on `opn` >> dsimp[known_op_def, op_gbag_def, eqs, va_case_eq] >> rw[] >>
  simp[domain_insert]);



val FINITE_BAG_FOLDR = Q.store_thm(
  "FINITE_BAG_FOLDR",
  `∀l f a.
     FINITE_BAG a ∧ (∀e a. FINITE_BAG a ∧ MEM e l ⇒ FINITE_BAG (f e a)) ⇒
     FINITE_BAG (FOLDR f a l)`,
  Induct >> simp[]);

val FINITE_set_globals = Q.store_thm(
  "FINITE_set_globals[simp]",
  `∀e. FINITE_BAG (set_globals e)`,
  ho_match_mp_tac set_globals_ind >> simp[elist_globals_def] >> rpt strip_tac >>
  TRY (irule FINITE_BAG_FOLDR >> dsimp[MEM_MAP] >> NO_TAC) >>
  qcase_tac `op_gbag opn` >> Cases_on `opn` >> simp[op_gbag_def]);

val FINITE_BAG_elist_globals = Q.store_thm(
  "FINITE_BAG_elist_globals[simp]",
  `FINITE_BAG (elist_globals es)`,
  Induct_on `es` >> fs[]);

val unchanging_gapx_def = Define`
  unchanging_gapx es g0 g ⇔
    ∀i. i ∈ SET_OF_BAG (elist_globals es) ∧ i ∈ domain g0 ⇒
        lookup i g0 = lookup i g
`;

val unchanging_gapx_CONS = Q.store_thm(
  "unchanging_gapx_CONS",
  `unchanging_gapx (e::es) g0 g ⇔
     (∀i. i <: set_globals e ∧ i ∈ domain g0 ⇒ lookup i g0 = lookup i g) ∧
     unchanging_gapx es g0 g`,
  dsimp[unchanging_gapx_def])

val unchanging_gapx_NIL = Q.store_thm(
  "unchanging_gapx_NIL[simp]",
  `unchanging_gapx [] g0 g ⇔ T`,
  simp[unchanging_gapx_def]);

val unchanging_gapx_LN = Q.store_thm(
  "unchanging_gapx_LN[simp]",
  `unchanging_gapx es LN g ⇔ T`,
  simp[unchanging_gapx_def]);

val unchanging_gapx_SING = Q.store_thm(
  "unchanging_gapx_SING",
  `unchanging_gapx [e] g0 g ⇔
     (∀i. i <: set_globals e ∧ i ∈ domain g0 ⇒ lookup i g0 = lookup i g)`,
  simp[unchanging_gapx_CONS]);

val unchanging_gapx_CONS2 = Q.store_thm(
  "unchanging_gapx_CONS2",
  `unchanging_gapx (e1::e2::es) g0 g ⇔
     unchanging_gapx [e1] g0 g ∧ unchanging_gapx (e2::es) g0 g`,
  simp[unchanging_gapx_CONS]);

val state_globals_approx_def = Define`
  state_globals_approx s g ⇔
    ∀k v.
      get_global k s.globals = SOME (SOME v) ⇒
      ∃a. lookup k g = SOME a ∧ val_approx_val a v
`;

val state_approx_better_definedg = Q.store_thm(
  "state_approx_better_definedg",
  `better_definedg g1 g2 ∧ state_globals_approx s g1 ⇒
   state_globals_approx s g2`,
  csimp[better_definedg_def, state_globals_approx_def, domain_lookup,
        PULL_EXISTS] >>
  metis_tac[val_approx_better_approx]);

val known_preserves_gwf = Q.store_thm(
  "known_preserves_gwf",
  `∀exps apxs g0 alist g. known exps apxs g0 = (alist,g) ∧ wf g0 ⇒ wf g`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rw[] >> qcase_tac `known_op opn` >>
  Cases_on `opn` >> fs[known_op_def, eqs, va_case_eq, bool_case_eq] >>
  rw[wf_insert]);

val mapped_globals_def = Define`
  mapped_globals (s:'a closSem$state) =
    { i | ∃v. get_global i s.globals = SOME (SOME v) }
`;

val mapped_globals_refupdate = Q.store_thm(
  "mapped_globals_refupdate[simp]",
  `mapped_globals (s with refs updated_by f) = mapped_globals s`,
  simp[mapped_globals_def]);

val mapped_globals_ffiupdate = Q.store_thm(
  "mapped_globals_ffiupdate[simp]",
  `mapped_globals (s with ffi updated_by v) = mapped_globals s`,
  simp[mapped_globals_def]);

val mapped_globals_clockupdate = Q.store_thm(
  "mapped_globals_clockupdate[simp]",
  `mapped_globals (s with clock updated_by f) = mapped_globals s`,
  simp[mapped_globals_def]);

val mapped_globals_dec_clock = Q.store_thm(
  "mapped_globals_dec_clock[simp]",
  `mapped_globals (dec_clock n s) = mapped_globals s`,
  simp[mapped_globals_def, dec_clock_def])

val evaluate_t = ``closSem$evaluate``
val fixeqs = let
  fun c t =
    let
      val r = rhs t
      val (f, _) = strip_comb r
    in
      if same_const evaluate_t f then REWR_CONV EQ_SYM_EQ
      else NO_CONV
    end t
in
  RULE_ASSUM_TAC (CONV_RULE (TRY_CONV c))
end

val state_globals_approx_clock_fupd = Q.store_thm(
  "state_globals_approx_clock_fupd[simp]",
  `state_globals_approx (s with clock updated_by f) g ⇔
   state_globals_approx s g`,
  simp[state_globals_approx_def]);

val state_globals_approx_dec_clock = Q.store_thm(
  "state_globals_approx_dec_clock[simp]",
  `state_globals_approx (dec_clock n s) g ⇔ state_globals_approx s g`,
  simp[dec_clock_def]);

val state_globals_approx_refsfupd = Q.store_thm(
  "state_globals_approx_refsfupd[simp]",
  `state_globals_approx (s with refs updated_by f) g ⇔
   state_globals_approx s g`,
  simp[state_globals_approx_def]);

val state_globals_approx_ffifupd = Q.store_thm(
  "state_globals_approx_ffifupd[simp]",
  `state_globals_approx (s with ffi updated_by f) g ⇔
   state_globals_approx s g`,
  simp[state_globals_approx_def]);

val v_size_lemma = prove(
  ``MEM (v:closSem$v) vl ⇒ v_size v < v1_size vl``,
  Induct_on `vl` >> dsimp[v_size_def] >> rpt strip_tac >>
  res_tac >> simp[]);

(* value is setglobal-closure free *)
val vsgc_free_def = tDefine "vsgc_free" `
  (vsgc_free (Closure _ VL1 VL2 _ body) ⇔
     set_globals body = {||} ∧
     EVERY vsgc_free VL1 ∧ EVERY vsgc_free VL2) ∧
  (vsgc_free (Recclosure _ VL1 VL2 bods _) ⇔
     elist_globals (MAP SND bods) = {||} ∧
     EVERY vsgc_free VL1 ∧ EVERY vsgc_free VL2) ∧
  (vsgc_free (Block _ VL) ⇔ EVERY vsgc_free VL) ∧
  (vsgc_free _ ⇔ T)
` (WF_REL_TAC `measure closSem$v_size` >> simp[v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[])

val vsgc_free_def = save_thm(
  "vsgc_free_def[simp]",
  SIMP_RULE (bool_ss ++ ETA_ss) [] vsgc_free_def)

val vsgc_free_Unit = Q.store_thm(
  "vsgc_free_Unit[simp]",
  `vsgc_free Unit`,
  simp[Unit_def]);

val vsgc_free_Boolv = Q.store_thm(
  "vsgc_free_Boolv[simp]",
  `vsgc_free (Boolv b)`,
  simp[Boolv_def]);

(* result is setglobal-closure free *)
val rsgc_free_def = Define`
  (rsgc_free (Rval vs) ⇔ EVERY vsgc_free vs) ∧
  (rsgc_free (Rerr (Rabort _)) ⇔ T) ∧
  (rsgc_free (Rerr (Rraise v)) ⇔ vsgc_free v)
`;
val _ = export_rewrites ["rsgc_free_def"]

(* state is setglobal-closure free *)
val ssgc_free_def = Define`
  ssgc_free (s:'a closSem$state) ⇔
    (∀n m e. FLOOKUP s.code n = SOME (m,e) ⇒ set_globals e = {||}) ∧
    (∀n vl. FLOOKUP s.refs n = SOME (ValueArray vl) ⇒ EVERY vsgc_free vl) ∧
    (∀v. MEM (SOME v) s.globals ⇒ vsgc_free v)
`;

val ssgc_free_clockupd = Q.store_thm(
  "ssgc_free_clockupd[simp]",
  `ssgc_free (s with clock updated_by f) = ssgc_free s`,
  simp[ssgc_free_def])

val ssgc_free_dec_clock = Q.store_thm(
  "ssgc_free_dec_clock[simp]",
  `ssgc_free (dec_clock n s) ⇔ ssgc_free s`,
  simp[dec_clock_def])

val esgc_free_def = tDefine "esgc_free" `
  (esgc_free (Var _) ⇔ T) ∧
  (esgc_free (If e1 e2 e3) ⇔ esgc_free e1 ∧ esgc_free e2 ∧ esgc_free e3) ∧
  (esgc_free (Let binds e) ⇔ EVERY esgc_free binds ∧ esgc_free e) ∧
  (esgc_free (Raise e) ⇔ esgc_free e) ∧
  (esgc_free (Handle e1 e2) ⇔ esgc_free e1 ∧ esgc_free e2) ∧
  (esgc_free (Tick e) ⇔ esgc_free e) ∧
  (esgc_free (Call _ args) ⇔ EVERY esgc_free args) ∧
  (esgc_free (App _ e args) ⇔ esgc_free e ∧ EVERY esgc_free args) ∧
  (esgc_free (Fn _ _ _ b) ⇔ set_globals b = {||}) ∧
  (esgc_free (Letrec _ _ binds bod) ⇔
    elist_globals (MAP SND binds) = {||} ∧ esgc_free bod) ∧
  (esgc_free (Op _ args) ⇔ EVERY esgc_free args)
` (WF_REL_TAC `measure exp_size` >> simp[] >> rpt strip_tac >>
   imp_res_tac exp_size_MEM >> simp[])
val esgc_free_def = save_thm("esgc_free_def[simp]",
  SIMP_RULE (bool_ss ++ ETA_ss) [] esgc_free_def)

val value_ind =
  TypeBase.induction_of ``:closSem$v``
   |> Q.SPECL [`P`, `EVERY P`]
   |> SIMP_RULE (srw_ss()) []
   |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> Q.GEN `P`


val mglobals_extend_def = Define`
  mglobals_extend s1 mgs s2 ⇔
     mapped_globals s2 ⊆ mapped_globals s1 ∪ mgs ∧
     ∀k v. get_global k s2.globals = SOME (SOME v) ∧ k ∉ mgs ⇒
           get_global k s1.globals = SOME (SOME v)`

val mglobals_extend_refl = Q.store_thm(
  "mglobals_extend_refl[simp]",
  `mglobals_extend s gs s`,
  simp[mglobals_extend_def]);

val mglobals_extend_trans = Q.store_thm(
  "mglobals_extend_trans",
  `mglobals_extend s0 g1 s1 ∧ mglobals_extend s1 g2 s2 ⇒
   mglobals_extend s0 (g1 ∪ g2) s2`,
  simp[mglobals_extend_def, SUBSET_DEF] >> metis_tac[]);

val mglobals_extend_SUBSET = Q.store_thm(
  "mglobals_extend_SUBSET",
  `mglobals_extend s0 g1 s ∧ g1 ⊆ g2 ⇒ mglobals_extend s0 g2 s`,
  simp[mglobals_extend_def, SUBSET_DEF] >> metis_tac[]);

val mglobals_extend_refupdate = Q.store_thm(
  "mglobals_extend_refupdate[simp]",
  `(mglobals_extend s0 gs (s with refs updated_by f) ⇔
      mglobals_extend s0 gs s) ∧
   (mglobals_extend (s0 with refs updated_by f) gs s ⇔
      mglobals_extend s0 gs s)`,
  simp[mglobals_extend_def]);

val mglobals_extend_ffiupdate = Q.store_thm(
  "mglobals_extend_ffiupdate[simp]",
  `(mglobals_extend s0 gs (s with ffi updated_by f) ⇔
      mglobals_extend s0 gs s) ∧
   (mglobals_extend (s0 with ffi updated_by f) gs s  ⇔
      mglobals_extend s0 gs s)`,
  simp[mglobals_extend_def]);

val mglobals_extend_clockupdate = Q.store_thm(
  "mglobals_extend_clockupdate[simp]",
  `(mglobals_extend s0 gs (s with clock updated_by f) ⇔
      mglobals_extend s0 gs s) ∧
   (mglobals_extend (s0 with clock updated_by f) gs s ⇔
      mglobals_extend s0 gs s)`,
  simp[mglobals_extend_def]);

val mglobals_extend_decclock = Q.store_thm(
  "mglobals_extend_decclock[simp]",
  `(mglobals_extend (dec_clock n s0) gs s ⇔ mglobals_extend s0 gs s) ∧
   (mglobals_extend s0 gs (dec_clock n s) ⇔ mglobals_extend s0 gs s)`,
  simp[dec_clock_def]);

val do_app_ssgc = Q.store_thm(
  "do_app_ssgc",
  `∀opn args s0 res.
     do_app opn args s0 = res ⇒
     EVERY vsgc_free args ∧ ssgc_free s0 ⇒
     (∀v s. res = Rval(v,s) ⇒
            vsgc_free v ∧ ssgc_free s ∧
            mglobals_extend s0 (SET_OF_BAG (op_gbag opn)) s) ∧
     (∀v. res = Rerr (Rraise v) ⇒ vsgc_free v)`,
  Cases_on `opn` >>
  simp[do_app_def, eqs, op_gbag_def, PULL_EXISTS, bool_case_eq,
       pair_case_eq]
  >- ((* GetGlobal *)
      simp[get_global_def, ssgc_free_def] >> metis_tac[MEM_EL])
  >- ((* SetGlobal *)
      simp[ssgc_free_def, mglobals_extend_def, mapped_globals_def] >>
      rpt strip_tac
      >- metis_tac[]
      >- metis_tac[]
      >- (fs[MEM_LUPDATE] >> metis_tac[MEM_EL])
      >- (dsimp[SUBSET_DEF, get_global_def,
                EL_LUPDATE, bool_case_eq] >> metis_tac[])
      >- (fs[get_global_def, EL_LUPDATE]))
  >- (dsimp[ssgc_free_def, mglobals_extend_def, mapped_globals_def, SUBSET_DEF,
            get_global_def, EL_APPEND_EQN, bool_case_eq] >>
      reverse (rpt strip_tac)
      >- (qcase_tac `ii < LENGTH (ss:α closSem$state).globals` >>
          Cases_on `ii < LENGTH ss.globals` >> simp[] >>
          Cases_on `ii - LENGTH ss.globals = 0`
          >- (pop_assum SUBST_ALL_TAC >> simp[]) >> simp[])
      >- (qcase_tac `nn < LENGTH (ss:α closSem$state).globals` >>
          Cases_on `nn < LENGTH ss.globals` >> simp[] >>
          Cases_on `nn < LENGTH ss.globals + 1` >> simp[] >>
          `nn - LENGTH ss.globals = 0` by simp[] >> simp[]) >>
      metis_tac[])
  >- dsimp[]
  >- (simp[PULL_FORALL] >> metis_tac[EVERY_MEM, MEM_EL])
  >- (simp[ssgc_free_def] >>
      rpt (disch_then strip_assume_tac ORELSE gen_tac) >> rpt conj_tac
      >- first_assum MATCH_ACCEPT_TAC >> fs[] >>
      simp[FLOOKUP_UPDATE, bool_case_eq] >> metis_tac[])
  >- (simp[ssgc_free_def] >>
      rpt (disch_then strip_assume_tac ORELSE gen_tac) >> rpt conj_tac
      >- first_assum MATCH_ACCEPT_TAC >> fs[] >>
      dsimp[FLOOKUP_UPDATE, bool_case_eq, EVERY_REPLICATE] >> metis_tac[])
  >- (simp[ssgc_free_def] >>
      rpt (disch_then strip_assume_tac ORELSE gen_tac) >> rpt conj_tac
      >- first_assum MATCH_ACCEPT_TAC >> fs[] >>
      dsimp[FLOOKUP_UPDATE, bool_case_eq, EVERY_REPLICATE] >> metis_tac[])
  >- (simp[PULL_FORALL] >> rpt gen_tac >> qcase_tac `v_to_list v = SOME vs` >>
      map_every qid_spec_tac [`vs`, `v`] >> ho_match_mp_tac value_ind >>
      simp[v_to_list_def] >> Cases >>
      simp[v_to_list_def] >>
      qcase_tac `closSem$Block _ (v1::vs)` >> Cases_on `vs` >>
      simp[v_to_list_def] >>
      qcase_tac `closSem$Block _ (v1::v2::vs)` >> Cases_on `vs` >>
      simp[v_to_list_def, eqs, PULL_EXISTS, PULL_FORALL])
  >- (simp[PULL_FORALL] >> rpt gen_tac >> qcase_tac `EVERY vsgc_free vs` >>
      Induct_on `vs` >> simp[list_to_v_def])
  >- (dsimp[ssgc_free_def, FLOOKUP_UPDATE, bool_case_eq] >> metis_tac[])
  >- (dsimp[ssgc_free_def] >>
      metis_tac[MEM_EL, EVERY_MEM, integerTheory.INT_INJ,
                integerTheory.INT_OF_NUM, integerTheory.INT_LT])
  >- (dsimp[ssgc_free_def, FLOOKUP_UPDATE, bool_case_eq] >>
      rpt strip_tac
      >- metis_tac[]
      >- (irule IMP_EVERY_LUPDATE >> simp[] >> metis_tac[])
      >- metis_tac[])
  >- (dsimp[ssgc_free_def, FLOOKUP_UPDATE, bool_case_eq] >> metis_tac[])
  >- dsimp[]
  >- dsimp[])

val EVERY_lookup_vars = Q.store_thm(
  "EVERY_lookup_vars",
  `∀vs env env'. EVERY P env ∧ lookup_vars vs env = SOME env' ⇒ EVERY P env'`,
  Induct >> simp[lookup_vars_def, eqs, PULL_EXISTS] >>
  metis_tac[MEM_EL, EVERY_MEM]);

val FOLDR_BU_EQ_EMPTY = Q.store_thm(
  "FOLDR_BU_EQ_EMPTY",
  `FOLDR (λx. BAG_UNION (f x)) a l = {||} ⇔
     a = {||} ∧ ∀e. MEM e l ⇒ f e = {||}`,
  Induct_on `l` >> dsimp[] >> metis_tac[])

val elglobals_EQ_EMPTY = Q.store_thm(
  "elglobals_EQ_EMPTY",
  `elist_globals l = {||} ⇔ ∀e. MEM e l ⇒ set_globals e = {||}`,
  Induct_on `l` >> dsimp[]);

val set_globals_empty_esgc_free = Q.store_thm(
  "set_globals_empty_esgc_free",
  `set_globals e = {||} ⇒ esgc_free e`,
  completeInduct_on `exp_size e` >> fs[PULL_FORALL] >> Cases >>
  simp[] >> strip_tac >> rveq >> fs[AND_IMP_INTRO] >>
  simp[EVERY_MEM, elglobals_EQ_EMPTY, FOLDR_BU_EQ_EMPTY, MEM_MAP] >>
  rw[] >> rw[] >>
  first_x_assum irule >> simp[] >> imp_res_tac exp_size_MEM >> simp[])

val lem = Q.prove(
  `(∀a es env (s0:α closSem$state) res s.
      a = (es,env,s0) ∧ evaluate(es,env,s0) = (res,s) ⇒
      mapped_globals s0 ⊆ mapped_globals s) ∧
   (∀lopt f args (s0:α closSem$state) res s.
      evaluate_app lopt f args s0 = (res, s) ⇒
      mapped_globals s0 ⊆ mapped_globals s)`,
  ho_match_mp_tac evaluate_ind >> rw[evaluate_def]
  >- fs[evaluate_def]
  >- (fs[pair_case_eq, result_case_eq] >> rveq >> fs[] >>
      metis_tac[SUBSET_TRANS])
  >- fs[evaluate_def, bool_case_eq]
  >- (fs[pair_case_eq, result_case_eq, bool_case_eq] >> rveq >> fixeqs >>
      fs[] >> metis_tac[SUBSET_TRANS])
  >- (fs[pair_case_eq, result_case_eq] >> rveq >> fs[] >>
      metis_tac[SUBSET_TRANS])
  >- fs[result_case_eq, pair_case_eq]
  >- (fs[result_case_eq, pair_case_eq, error_case_eq] >> rveq >> fs[] >>
      metis_tac[SUBSET_TRANS])
  >- (fs[pair_case_eq, result_case_eq] >> rveq >> fs[] >>
      qcase_tac `closSem$do_app opn` >> Cases_on `opn` >>
      fs[do_app_def, eqs, bool_case_eq, pair_case_eq] >> rw[] >>
      fs[]
      >- (qcase_tac `closSem$evaluate(_,_,s0) = (_, s1)` >>
          irule SUBSET_TRANS >> qexists_tac `mapped_globals s1` >> simp[] >>
          simp[mapped_globals_def] >>
          fs[SUBSET_DEF, PULL_EXISTS, get_global_def,
             EL_LUPDATE, bool_case_eq] >> metis_tac[])
      >- (simp[mapped_globals_def, SUBSET_DEF, get_global_def,
               EL_APPEND_EQN, bool_case_eq] >> rpt strip_tac >>
          simp[]))
  >- fs[evaluate_def, bool_case_eq, eqs]
  >- (fs[eqs, PULL_EXISTS] >> rveq >> fs[])
  >- (fs[pair_case_eq, result_case_eq] >> rveq >> fs[] >>
      metis_tac[SUBSET_TRANS])
  >- (fs[pair_case_eq, result_case_eq, eqs, bool_case_eq] >> rveq >> fixeqs >>
      fs[] >> metis_tac[SUBSET_TRANS])
  >- (fs[eqs, bool_case_eq, pair_case_eq] >> rveq >> fs[] >>
      metis_tac[SUBSET_TRANS]))

val mapped_globals_grow = save_thm(
  "mapped_globals_grow",
  lem |> CONJUNCT1 |> SIMP_RULE bool_ss [])

fun say0 pfx s g = (print (pfx ^ ": " ^ s ^ "\n"); ALL_TAC g)
val say = say0 "ssgc_evaluate0"

val ssgc_evaluate0 = Q.prove(
  `(∀a es env (s0:α closSem$state) res s.
      ssgc_free s0 ∧ EVERY vsgc_free env ∧
      EVERY esgc_free es ∧ a = (es,env,s0) ∧
      evaluate a = (res,s) ⇒
      ssgc_free s ∧ rsgc_free res ∧
      mglobals_extend s0 (SET_OF_BAG (elist_globals es)) s) ∧
   (∀lopt f args (s0:α closSem$state) res s.
      ssgc_free s0 ∧ vsgc_free f ∧ EVERY vsgc_free args ∧
      evaluate_app lopt f args s0 = (res, s) ⇒
      ssgc_free s ∧ rsgc_free res ∧ mglobals_extend s0 ∅ s)`,
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> simp[]
  >- (* nil *) simp[evaluate_def]
  >- ((* cons *) say "cons" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           PULL_EXISTS] >>
      qcase_tac `evaluate([e1], env, s0)` >>
      rpt gen_tac >> strip_tac >> rveq >> fs[]
      >- (imp_res_tac evaluate_SING >> rveq >> fs[SET_OF_BAG_UNION] >>
          metis_tac[mglobals_extend_trans])
      >- (fs[SET_OF_BAG_UNION] >> metis_tac[mglobals_extend_trans])
      >- (fs[SET_OF_BAG_UNION] >>
          metis_tac[mglobals_extend_SUBSET, SUBSET_UNION]))
  >- ((* var *) say "var" >> simp[evaluate_def] >> rw[] >> rw[] >>
      metis_tac[EVERY_MEM, MEM_EL])
  >- ((* If *) say "if" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           bool_case_eq] >>
      rpt gen_tac >> reverse strip_tac >> rveq >> fixeqs >>
      fs[SET_OF_BAG_UNION]
      >- metis_tac[mglobals_extend_SUBSET, SUBSET_UNION, UNION_ASSOC,
                   UNION_COMM]
      >- metis_tac[mglobals_extend_SUBSET, SUBSET_UNION, UNION_ASSOC,
                   UNION_COMM] >>
      qcase_tac `evaluate ([gd], env, s0) = (Rval vs, s1)` >>
      qcase_tac `mglobals_extend s0 set1 s1` >>
      qcase_tac `mglobals_extend s1 set2 s` >>
      `mglobals_extend s0 (set1 ∪ set2) s` by metis_tac[mglobals_extend_trans]>>
      metis_tac[mglobals_extend_SUBSET, SUBSET_UNION, UNION_ASSOC, UNION_COMM])
  >- ((* let *) say "let" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq] >>
      rpt gen_tac >> strip_tac >> rveq >> fs[SUBSET_DEF, SET_OF_BAG_UNION] >>
      metis_tac[mglobals_extend_trans, UNION_COMM, SUBSET_UNION,
                mglobals_extend_SUBSET])
  >- ((* raise *) say "raise" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq] >>
      rpt gen_tac >> strip_tac >> rveq >> fs[SUBSET_DEF, SET_OF_BAG_UNION] >>
      metis_tac[evaluate_SING, HD, EVERY_DEF])
  >- ((* handle *) say "handle" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           error_case_eq] >>
      rpt gen_tac >> strip_tac >> rveq >> fs[SUBSET_DEF, SET_OF_BAG_UNION] >>
      metis_tac[mglobals_extend_SUBSET, SUBSET_UNION, mglobals_extend_trans])
  >- ((* op *) say "op" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq] >>
      rpt gen_tac >> strip_tac >> rveq >> fs[]
      >- (IMP_RES_THEN mp_tac do_app_ssgc >> simp[EVERY_REVERSE] >>
          fs[SET_OF_BAG_UNION] >>
          metis_tac[mglobals_extend_trans, UNION_COMM])
      >- (IMP_RES_THEN mp_tac do_app_ssgc >> simp[EVERY_REVERSE] >>
          qcase_tac `Rerr err` >> Cases_on `err` >> simp[] >>
          fs[SET_OF_BAG_UNION] >>
          metis_tac[SUBSET_UNION, mglobals_extend_SUBSET])
      >- (fs[SET_OF_BAG_UNION] >>
          metis_tac[SUBSET_UNION, mglobals_extend_SUBSET]))
  >- ((* Fn *) say "fn" >>
      simp[evaluate_def, eqs, bool_case_eq] >> rpt gen_tac >>
      strip_tac >> rveq >> fs[] >> metis_tac[EVERY_lookup_vars])
  >- ((* Letrec *) say "letrec" >>
      simp[Once foldr_bu', SET_OF_BAG_UNION] >>
      simp[evaluate_def, bool_case_eq, eqs] >>
      rpt (gen_tac ORELSE disch_then strip_assume_tac) >> rveq >>
      fs[EVERY_GENLIST]
      >- (metis_tac[mglobals_extend_SUBSET, SUBSET_UNION])
      >- (imp_res_tac EVERY_lookup_vars >> fs[] >>
          metis_tac[mglobals_extend_SUBSET, SUBSET_UNION]))
  >- ((* App *) say "app" >>
      rpt gen_tac >> strip_tac >>
      simp[evaluate_def, bool_case_eq, pair_case_eq,
           result_case_eq] >>
      rpt (gen_tac ORELSE disch_then strip_assume_tac) >> rveq >> fs[]
      >- (imp_res_tac evaluate_SING >> rveq >>
          fs[SET_OF_BAG_UNION] >>
          metis_tac[mglobals_extend_trans, UNION_COMM, UNION_EMPTY])
      >- (fs[SET_OF_BAG_UNION] >> metis_tac[mglobals_extend_trans, UNION_COMM])
      >- (fs[SET_OF_BAG_UNION] >>
          metis_tac[mglobals_extend_SUBSET, SUBSET_UNION]))
  >- ((* Tick *)
      say "tick" >> simp[evaluate_def, bool_case_eq] >>
      rpt (gen_tac ORELSE disch_then strip_assume_tac) >> rveq >> fixeqs >>
      fs[])
  >- ((* Call *)
      say "call" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq, eqs,
           bool_case_eq] >>
      rpt (gen_tac ORELSE disch_then strip_assume_tac) >> rveq >> fixeqs >>
      fs[] >> fs[find_code_def, eqs, pair_case_eq] >> rveq >>
      qcase_tac `FLOOKUP _.code _ = SOME (_, fbody)` >>
      `set_globals fbody = {||}` suffices_by
        (strip_tac >> fs[] >> imp_res_tac set_globals_empty_esgc_free >>
         fs[] >> metis_tac[mglobals_extend_trans, UNION_EMPTY]) >>
      fs[ssgc_free_def] >> metis_tac[])
  >- ((* evaluate_app *)
      say "evaluate_app" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, eqs, bool_case_eq, pair_case_eq] >>
      rpt (gen_tac ORELSE disch_then strip_assume_tac) >> rveq >> fixeqs >>
      fs[]
      >- (fs[dest_closure_def, eqs, bool_case_eq] >> rveq >>
          fs[] >> pairarg_tac >> fs[bool_case_eq])
      >- (fs[dest_closure_def, eqs, bool_case_eq] >> rveq >>
          fs[EVERY_REVERSE, EVERY_DROP, EVERY_TAKE]
          >- (imp_res_tac set_globals_empty_esgc_free >> fs[] >>
              metis_tac[mglobals_extend_trans, UNION_EMPTY]) >>
          pairarg_tac >>
          fs[elglobals_EQ_EMPTY, bool_case_eq] >> rveq >>
          fs[EVERY_DROP, EVERY_TAKE, EVERY_REVERSE, EVERY_GENLIST,
             elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS] >>
          qcase_tac `EL ii fns = (_, fbody)` >>
          `ii < LENGTH fns` by simp[] >>
          `set_globals fbody = {||}` by metis_tac[MEM_EL,SND] >>
          imp_res_tac set_globals_empty_esgc_free >> fs[] >>
          metis_tac[mglobals_extend_trans, UNION_EMPTY])
      >- (fs[dest_closure_def, eqs, bool_case_eq] >> rveq >>
          fs[EVERY_TAKE, EVERY_REVERSE, EVERY_DROP]
          >- (imp_res_tac set_globals_empty_esgc_free >> fs[]) >>
          pairarg_tac >>
          fs[elglobals_EQ_EMPTY, bool_case_eq] >> rveq >>
          fs[EVERY_DROP, EVERY_TAKE, EVERY_REVERSE, EVERY_GENLIST,
             elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS] >>
          qcase_tac `EL ii fns = (_, fbody)` >>
          `ii < LENGTH fns` by simp[] >>
          `set_globals fbody = {||}` by metis_tac[MEM_EL,SND] >>
          imp_res_tac set_globals_empty_esgc_free >> fs[])
      >- (fs[dest_closure_def, eqs, bool_case_eq] >> rveq >>
          fs[EVERY_TAKE, EVERY_REVERSE, EVERY_DROP]
          >- (imp_res_tac set_globals_empty_esgc_free >> fs[]) >>
          pairarg_tac >>
          fs[elglobals_EQ_EMPTY, bool_case_eq] >> rveq >>
          fs[EVERY_DROP, EVERY_TAKE, EVERY_REVERSE, EVERY_GENLIST,
             elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS] >>
          qcase_tac `EL ii fns = (_, fbody)` >>
          `ii < LENGTH fns` by simp[] >>
          `set_globals fbody = {||}` by metis_tac[MEM_EL,SND] >>
          imp_res_tac set_globals_empty_esgc_free >> fs[])))

val ssgc_evaluate = save_thm(
  "ssgc_evaluate",
  ssgc_evaluate0 |> CONJUNCT1 |> SIMP_RULE bool_ss []);

val known_preserves_setGlobals = Q.store_thm(
  "known_preserves_setGlobals",
  `∀es as g0 all g.
      known es as g0 = (all,g) ⇒
      elist_globals (MAP FST all) = elist_globals es`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rw[] >> fs[] >> imp_res_tac known_sing_EQ_E >>
  rw[] >> fs[] >> rw[] >> simp[FOLDR_MAP] >>
  irule FOLDR_CONG >> simp[] >> rpt strip_tac >> pairarg_tac >>
  simp[]>> rw[] >>
  qmatch_abbrev_tac `set_globals (FST (HD (FST (known [X] ENV G0)))) =
                     set_globals X` >>
  qcase_tac `MEM (nn,X) fns` >> res_tac >> rfs[] >>
  `∃X' APX g'. known [X] ENV G0 = ([(X',APX)], g')` by metis_tac[known_sing] >>
  fs[])

val mglobals_extend_EMPTY_state_globals_approx = Q.store_thm(
  "mglobals_extend_EMPTY_state_globals_approx",
  `mglobals_extend s1 ∅ s2 ∧ mapped_globals s1 ⊆ mapped_globals s2 ⇒
   (state_globals_approx s1 g ⇔ state_globals_approx s2 g)`,
  simp[mglobals_extend_def, state_globals_approx_def, EXTENSION, SUBSET_DEF,
       mapped_globals_def] >>
  metis_tac[]);

val known_preserves_esgc_free = Q.store_thm(
  "known_preserves_esgc_free",
  `∀es as g0 all g.
     known es as g0 = (all,g) ∧ EVERY esgc_free es ⇒
     EVERY (esgc_free o FST) all`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rw[] >> fs[] >> imp_res_tac known_sing_EQ_E >>
  rw[] >> fs[] >> rw[ALL_EL_MAP]
  >- (imp_res_tac known_preserves_setGlobals >> fs[elist_globals_def])
  >- (fs[elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
      pairarg_tac >> rw[] >> fs[FORALL_PROD] >>
      qmatch_abbrev_tac
        `set_globals (FST (HD (FST (known [X] ENV g00)))) = _` >>
      qcase_tac `MEM (nn, X) fns` >>
      rpt (first_x_assum (qspecl_then [`nn`, `X`] mp_tac)) >> simp[] >>
      `∃X' APX gg. known [X] ENV g00 = ([(X',APX)], gg)`
        by metis_tac[known_sing] >> simp[] >>
      imp_res_tac known_preserves_setGlobals >> fs[elist_globals_def]))

val ssgc_free_preserved_SING = Q.store_thm(
  "ssgc_free_preserved_SING",
  `known [e1] as g0 = ([(e1',a)], g) ∧ esgc_free e1 ∧ ssgc_free s0 ∧
   EVERY vsgc_free env ∧ evaluate([e1'],env,s0) = (res,s) ⇒ ssgc_free s`,
  rpt strip_tac >>
  `EVERY esgc_free [e1]` by simp[] >>
  `EVERY (esgc_free o FST) [(e1',a)]`
     by metis_tac[known_preserves_esgc_free] >>
  `EVERY esgc_free [e1']` by fs[] >>
  metis_tac[ssgc_evaluate]);


val known_op_correct_approx = Q.store_thm(
  "known_op_correct_approx",
  `known_op opn args g0 = (a,g) ∧ LIST_REL val_approx_val args vs ∧
   subspt g g' ∧
   state_globals_approx s0 g' ∧
   do_app opn vs s0 = Rval (v, s) ⇒
   state_globals_approx s g' ∧ val_approx_val a v`,
  Cases_on `opn` >>
  simp[known_op_def, do_app_def, eqs, va_case_eq, bool_case_eq,
       pair_case_eq] >>
  rpt strip_tac >> rveq >> fs[]
  >- (fs[state_globals_approx_def] >> res_tac >>
      fs[subspt_def] >> metis_tac[SOME_11, domain_lookup])
  >- (fs[state_globals_approx_def, get_global_def, EL_LUPDATE,
         lookup_insert, bool_case_eq] >> rw[] >> simp[] >>
      fs[subspt_def])
  >- (fs[state_globals_approx_def, get_global_def, EL_LUPDATE,
         bool_case_eq, lookup_insert] >> rw[] >> fs[subspt_def] >>
      metis_tac[val_approx_val_merge_I])
  >- (fs[state_globals_approx_def, get_global_def, EL_APPEND_EQN,
         bool_case_eq] >> rw[]
      >- metis_tac[]
      >- (qcase_tac `nn - LENGTH (ss:'a closSem$state).globals` >>
          `nn - LENGTH ss.globals = 0` by simp[] >>
          pop_assum (fn th => fs[th])))
  >- (rveq >> fs[LIST_REL_EL_EQN]));

val known_CONS = Q.store_thm(
  "known_CONS",
  `known (e::es) as g0 =
    let (al1,g') = known [e] as g0 in
    let (all,g) = known es as g'
    in
       (al1 ++ all, g)`,
  Cases_on `es` >> simp[known_def] >> pairarg_tac >> simp[]);

val say = say0 "known_correct_approx"
val known_correct_approx = Q.store_thm(
  "known_correct_approx",
  `∀es as g0 all g env s0 s result g'.
     known es as g0 = (all,g) ∧ BAG_ALL_DISTINCT (elist_globals es) ∧
     LIST_REL val_approx_val as env ∧ subspt g0 g ∧ subspt g g' ∧
     state_globals_approx s0 g' ∧ ssgc_free s0 ∧ EVERY vsgc_free env ∧
     EVERY esgc_free es ∧ evaluate(MAP FST all, env, s0) = (result, s)
    ⇒
     state_globals_approx s g' ∧
     ∀vs. result = Rval vs ⇒ LIST_REL val_approx_val (MAP SND all) vs`,
  ho_match_mp_tac known_ind >> simp[known_def] >>
  rpt conj_tac >> rpt (gen_tac ORELSE disch_then strip_assume_tac)
  >- (* nil *) (say "nil" >> fs[evaluate_def] >> rw[])
  >- (say "cons" >> rpt (pairarg_tac >> fs[]) >> rveq >>
      qcase_tac `known [exp1] as g0` >>
      `∃exp1' a1 g1. known [exp1] as g0 = ([(exp1',a1)], g1)`
         by metis_tac[known_sing] >> fs[] >> rveq >> fs[] >>
      qcase_tac `known [exp1] EA g0 = ([(exp1',a1)], g1)` >>
      qcase_tac `known (exp2::erest) EA g1 = (al2,g)` >>
      `LENGTH al2 = LENGTH (exp2::erest)` by metis_tac[known_LENGTH, FST] >>
      fs[] >>
      `∃exp2' a2 arest. al2 = (exp2',a2)::arest`
        by (Cases_on `al2` >> fs[] >> metis_tac[pair_CASES]) >> rveq >>
      qpat_assum `known [_] _ _ = _` (fn th =>
        mp_tac (asmPART_MATCH' hd subspt_known_elist_globals (concl th)) >>
        assume_tac th) >> simp[] >> disch_then (resolve_selected hd) >>
      fs[BAG_ALL_DISTINCT_BAG_UNION] >> strip_tac >>
      fs[evaluate_def, pair_case_eq, result_case_eq] >> rveq
      >- (qcase_tac `evaluate ([exp1'], env, s0) = (Rval v1, s1)` >>
          qpat_assum `closSem$evaluate([_],_,_) = _` (fn th =>
            first_x_assum (fn ith =>
              mp_tac (asmPART_MATCH' last ith (concl th))) >> assume_tac th) >>
          simp[] >>
          disch_then (resolve_selected last) >> simp[] >>
          impl_keep_tac >- metis_tac[subspt_trans] >> strip_tac >>
          simp[] >> rveq >> fs[] >> sel_ihpc last >> simp[] >>
          metis_tac[ssgc_free_preserved_SING])
      >- (simp[] >>
          qpat_assum `closSem$evaluate ([_],_,_) = _` (fn th =>
            first_x_assum (fn ith =>
              mp_tac (asmPART_MATCH' last ith (concl th))) >> assume_tac th) >>
          simp[] >>
          disch_then (resolve_selected last) >> simp[] >>
          impl_tac >- metis_tac[subspt_trans] >> rw[] >>
          sel_ihpc last >> simp[] >> disch_then irule >> simp[]>>
          metis_tac[ssgc_free_preserved_SING])
      >- (simp[] >> sel_ihpc last >> simp[] >> metis_tac[subspt_trans]))
  >- ((* Var *) say "var" >>
      fs[any_el_ALT, evaluate_def, bool_case_eq] >>
      fs[LIST_REL_EL_EQN])
  >- ((* If *) say "if" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[BAG_ALL_DISTINCT_BAG_UNION] >>
      qcase_tac `known [ge] as g0 = (_, g1)` >>
      `∃ge' apx1. known [ge] as g0 = ([(ge',apx1)], g1)`
         by metis_tac[known_sing, PAIR_EQ] >>
      qcase_tac `known [tb] as g1 = (_, g2)` >>
      `∃tb' apx2. known [tb] as g1 = ([(tb',apx2)], g2)`
         by metis_tac[known_sing, PAIR_EQ] >>
      qcase_tac `known [eb] as g2 = (_, g3)` >>
      `∃eb' apx3. known [eb] as g2 = ([(eb',apx3)], g3)`
         by metis_tac[known_sing, PAIR_EQ] >> fs[] >> rveq >> fs[] >> rveq >>
      `subspt g0 g1 ∧ subspt g1 g2 ∧ subspt g2 g3`
         by (`∃al01. known [ge;tb] as g0 = (al01,g2)` by simp[known_def] >>
             first_assum (fn th =>
               mp_tac (asmPART_MATCH' hd subspt_known_elist_globals
                                      (concl th))) >> simp[] >>
             disch_then (resolve_selected hd) >> simp[] >> strip_tac >>
             qpat_assum `known [_] _ g0 = (_,g1)` (fn th =>
               mp_tac (asmPART_MATCH' hd subspt_known_elist_globals
                                      (concl th)) >> assume_tac th) >>
             simp[] >> disch_then (resolve_selected hd) >> simp[]) >>
      reverse
        (fs[evaluate_def, pair_case_eq, result_case_eq,
            bool_case_eq]) >> rveq >> fixeqs >> simp[]
      >- (sel_ihpc last >> simp[] >> metis_tac[subspt_trans])
      >- (sel_ihpc last >> simp[] >> metis_tac[subspt_trans]) >>
      (* two cases from here on *)
      qcase_tac `evaluate ([ge'], env, s0) = (Rval gvs, s1)` >>
      qpat_assum `evaluate ([ge'], _, _) = _` (fn th =>
        first_x_assum (fn ith =>
          mp_tac (asmPART_MATCH' last ith (concl th))) >> assume_tac th) >>
      simp[] >> disch_then (resolve_selected last) >> simp[] >>
      (impl_keep_tac >- metis_tac[subspt_trans]) >>
      strip_tac >> rveq >> fs[] >> rveq >> sel_ihpc last >> simp[] >>
      disch_then (resolve_selected (el 2)) >> simp[] >>
      impl_tac
      >- metis_tac[ssgc_free_preserved_SING]
      >- metis_tac[val_approx_val_merge_I]
      >- (conj_tac >- metis_tac[subspt_trans] >>
          irule (GEN_ALL ssgc_free_preserved_SING) >> metis_tac[])
      >- metis_tac[val_approx_val_merge_I])
  >- ((* let *) say "let" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      fs[evaluate_def, eqs, pair_case_eq, result_case_eq] >>
      rveq >> sel_ihpc last >> simp[] >> disch_then (resolve_selected last) >>
      simp[] >> fs[BAG_ALL_DISTINCT_BAG_UNION] >>
      map_every qcase_tac [`known [bod] _ g1 = (_, g)`,
                           `known _ _ g0 = (_, g1)`] >>
      qpat_assum `known [_] _ _ = _` (fn th =>
        mp_tac (asmPART_MATCH' (el 2) subspt_known_elist_globals
                               (concl th)) >> assume_tac th) >> simp[] >>
      disch_then (resolve_selected hd) >> simp[] >>
      (impl_tac >- fs[BAG_DISJOINT, DISJOINT_SYM]) >> strip_tac >> simp[] >>
      (impl_tac >- metis_tac[subspt_trans]) >> strip_tac >> simp[] >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      sel_ihpc last >> simp[EVERY2_APPEND_suff] >>
      disch_then (resolve_selected (el 2)) >> simp[] >> reverse impl_tac
      >- rw[] >> resolve_selected hd ssgc_evaluate >> simp[] >>
      disch_then (resolve_selected last) >> simp[] >>
      imp_res_tac known_preserves_esgc_free >> simp[ALL_EL_MAP])
  >- ((* raise *) say "raise" >>
      pairarg_tac >> fs[] >> imp_res_tac known_sing_EQ_E >> fs[] >> rveq >>
      fs[evaluate_def, pair_case_eq, result_case_eq] >> rveq >>
      simp[] >> metis_tac[])
  >- ((* tick *) say "tick" >>
      pairarg_tac >> fs[] >> imp_res_tac known_sing_EQ_E >> fs[] >> rveq >>
      fs[evaluate_def, pair_case_eq, result_case_eq,
         bool_case_eq] >> rveq >> simp[] >>
      fixeqs >> first_x_assum irule >> simp[] >>
      metis_tac[state_globals_approx_dec_clock, ssgc_free_dec_clock])
  >- ((* handle *) say "handle" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      map_every qcase_tac [`known _ (_ :: _) g1 = (_, g)`,
                           `known _ _ g0 = (_, g1)`] >>
      qpat_assum `known _ (_ :: _) _ = _` (fn th =>
        mp_tac (asmPART_MATCH' (el 2) subspt_known_elist_globals
                               (concl th)) >> assume_tac th) >> simp[] >>
      disch_then (resolve_selected hd) >> simp[] >>
      fs[BAG_ALL_DISTINCT_BAG_UNION] >> strip_tac >>
      fs[evaluate_def, pair_case_eq, result_case_eq,
         error_case_eq] >> rveq >> fs[] >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq
      >- (sel_ihpc last >> simp[] >> disch_then (resolve_selected last) >>
          simp[] >> reverse impl_keep_tac
          >- metis_tac[val_approx_val_merge_I] >>
          metis_tac[subspt_trans])
      >- (qpat_assum `closSem$evaluate _ = (Rerr _, _)`
           (fn th => first_x_assum (fn ith =>
              mp_tac (asmPART_MATCH' last ith (concl th))) >> assume_tac th) >>
          simp[] >> disch_then (resolve_selected last) >> simp[] >>
          impl_keep_tac >- metis_tac[subspt_trans] >>
          strip_tac >> sel_ihpc last >> simp[PULL_EXISTS] >>
          disch_then (resolve_selected (el 2)) >> simp[] >> reverse impl_tac
          >- metis_tac[val_approx_val_merge_I] >>
          conj_tac >- metis_tac[ssgc_free_preserved_SING] >>
          resolve_selected hd ssgc_evaluate >>
          disch_then (resolve_selected last) >> simp[] >> reverse impl_tac
          >- simp[] >>
          imp_res_tac known_preserves_esgc_free >> fs[])
      >- (sel_ihpc last >> simp[] >> metis_tac[subspt_trans]))
  >- ((* call *) say "call" >> pairarg_tac >> fs[] >> rveq >> fs[] >>
      fs[evaluate_def, pair_case_eq, result_case_eq, eqs,
         bool_case_eq] >>
      rveq >> fs[] >> sel_ihpc last >> simp[] >> fixeqs >>
      disch_then (resolve_selected last) >> simp[] >>
      reverse (rpt strip_tac)
      >- (rveq >> imp_res_tac evaluate_SING >> simp[]) >>
      map_every qcase_tac [
        `evaluate([body],args,dec_clock 1 s1) = (result,s)`,
        `evaluate(MAP FST alist,env,s0) = (Rval vs, s1)`] >>
      `ssgc_free s1 ∧ EVERY vsgc_free vs`
         by (resolve_selected hd ssgc_evaluate >> simp[] >>
             disch_then (resolve_selected last) >> simp[] >>
             reverse impl_tac >- simp[] >>
             imp_res_tac known_preserves_esgc_free >> simp[ALL_EL_MAP]) >>
      `set_globals body = {||}`
         by (Q.UNDISCH_THEN `ssgc_free s1` mp_tac >>
             simp[ssgc_free_def] >> fs[find_code_def, eqs, pair_case_eq] >>
             metis_tac[])  >>
      `mapped_globals s1 ⊆ mapped_globals s`
         by metis_tac[mapped_globals_grow, mapped_globals_dec_clock] >>
      `mglobals_extend s1 {} s`
         by (qspecl_then [`[body]`, `args`, `dec_clock 1 s1`, `result`, `s`]
                         mp_tac ssgc_evaluate >> simp[] >>
             fs[find_code_def, eqs, pair_case_eq] >> rveq >>
             simp[set_globals_empty_esgc_free]) >>
      metis_tac[mglobals_extend_EMPTY_state_globals_approx])
  >- ((* op *) say "op" >> rpt (pairarg_tac >> fs[]) >> rveq >>
      fs[BAG_ALL_DISTINCT_BAG_UNION] >>
      resolve_selected hd subspt_known_op_elist_globals >> simp[] >>
      disch_then (resolve_selected hd) >> simp[] >> strip_tac >>
      fs[evaluate_def, pair_case_eq, result_case_eq] >> rveq >>
      fs[] >> sel_ihpc last >> simp[] >> disch_then (resolve_selected last) >>
      simp[] >> (impl_keep_tac >- metis_tac[subspt_trans]) >>
      simp[] >> strip_tac >>
      metis_tac[known_op_correct_approx, LIST_REL_REVERSE_EQ])
  >- (say "app" >> rpt (pairarg_tac >> fs[]) >> rveq >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      qpat_assum `known [_] _ _ = _` (fn th =>
        mp_tac (asmPART_MATCH' (el 2) subspt_known_elist_globals (concl th)) >>
        assume_tac th) >> simp[] >> fs[BAG_ALL_DISTINCT_BAG_UNION] >>
      disch_then (resolve_selected hd) >> simp[] >> impl_tac
      >- fs[BAG_DISJOINT, DISJOINT_SYM] >> strip_tac >>
      fs[evaluate_def, bool_case_eq, pair_case_eq,
         result_case_eq] >> rveq >> fs[]
      >- (qcase_tac `evaluate(MAP FST args, env, s0) = (Rval argvs, s1)` >>
          qcase_tac `known exps apxs g0 = (args, g1)` >>
          qcase_tac `state_globals_approx s0 g'` >>
          `subspt g1 g'` by metis_tac[subspt_trans] >>
          nailIHx strip_assume_tac >> fs[] >>
          sel_ihpc last >> simp[] >> disch_then (resolve_selected (el 2)) >>
          simp[] >> resolve_selected hd ssgc_evaluate >> simp[] >>
          disch_then (resolve_selected last) >> simp[] >>
          impl_keep_tac
          >- (imp_res_tac known_preserves_esgc_free >> fs[ALL_EL_MAP]) >>
          simp[] >> rpt (disch_then strip_assume_tac) >> rveq >> fs[] >>
          qcase_tac `evaluate_app _ fval argvs s2 = (result, s)` >>
          reverse conj_tac
          >- (Cases_on `result` >> simp[] >>
              imp_res_tac evaluate_app_length_imp >>
              qcase_tac `LENGTH aa = 1` >> Cases_on `aa` >> fs[LENGTH_NIL]) >>
          qcase_tac `evaluate([fexp],env,s1) = (Rval[fval],s2)` >>
          qspecl_then [`[fexp]`, `env`, `s1`, `Rval [fval]`, `s2`]
                      mp_tac ssgc_evaluate >> simp[] >>
          impl_tac
          >- (IMP_RES_THEN mp_tac known_preserves_esgc_free >> simp[]) >>
          strip_tac >>
          qpat_assum `evaluate_app _ _ _ _ = _`
             (fn th =>
                 (mp_tac o PART_MATCH (last o strip_conj o #1 o dest_imp)
                                      (CONJUNCT2 ssgc_evaluate0) o concl) th >>
                 assume_tac th) >> simp[] >>
          strip_tac >>
          `mapped_globals s2 ⊆ mapped_globals s` suffices_by
            metis_tac[mglobals_extend_EMPTY_state_globals_approx] >>
          metis_tac[lem])
      >- (qcase_tac `evaluate(MAP FST args, env, s0) = (Rval argvs, s1)` >>
          qcase_tac `known exps apxs g0 = (args, g1)` >>
          qcase_tac `state_globals_approx s0 g'` >>
          `subspt g1 g'` by metis_tac[subspt_trans] >>
          nailIHx strip_assume_tac >> fs[] >> sel_ihpc last >> simp[] >>
          disch_then irule >>
          qspecl_then [`MAP FST args`, `env`, `s0`, `Rval argvs`, `s1`]
                      mp_tac ssgc_evaluate >> simp[] >>
          impl_tac
          >- (simp[ALL_EL_MAP] >> metis_tac[known_preserves_esgc_free]) >>
          simp[])
      >- (sel_ihpc last >> simp[] >> metis_tac[subspt_trans]))
  >- (say "fn" >> rpt (pairarg_tac >> fs[]) >> rveq >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      fs[evaluate_def, bool_case_eq, eqs] >> rveq >> fs[] >> every_case_tac >>
      simp[])
  >- (say "letrec" >> rpt (pairarg_tac >> fs[]) >> imp_res_tac known_sing_EQ_E>>
      rveq >> fs[] >> rveq >>
      fs[evaluate_def, bool_case_eq]
      >- (fixeqs >>
          qmatch_assum_abbrev_tac
            `closSem$evaluate([_], GENLIST (_ (MAP ff _)) _ ++ _, _) = _` >>
          qcase_tac
            `closSem$evaluate([body'],
                              GENLIST (Recclosure lopt [] env (MAP ff fns))
                                      (LENGTH fns) ++ env,
                              s0) = (result, s)` >>
          first_x_assum (qspecl_then [
            `GENLIST (Recclosure lopt [] env (MAP ff fns)) (LENGTH fns) ++ env`,
            `s0`] mp_tac) >> simp[] >>
          fs[Once foldr_bu', BAG_ALL_DISTINCT_BAG_UNION] >>
          imp_res_tac LIST_REL_LENGTH >>
          simp[LIST_REL_EL_EQN, EL_GENLIST, EL_APPEND_EQN, EVERY_MEM,
               MEM_GENLIST, PULL_EXISTS] >>
          disch_then (resolve_selected (el 3)) >>
          impl_tac
          >- (rpt conj_tac >> simp[]
              >- (qx_gen_tac `i` >> reverse (Cases_on `i < LENGTH fns`) >>
                  simp[] >- fs[LIST_REL_EL_EQN] >>
                  Cases_on `lopt` >> simp[] >>
                  simp[Abbr`ff`, EL_MAP] >> pairarg_tac >> simp[])
              >- (fs[elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
                  simp[Abbr`ff`] >> rpt strip_tac >>
                  qmatch_abbrev_tac `
                    set_globals (FST (HD (FST (known [_] ENV g0)))) = {||}` >>
                  qcase_tac `MEM (nargs, fbody) fns` >>
                  `set_globals fbody = {||}` by metis_tac[] >>
                  Cases_on `known [fbody] ENV g0` >> simp[] >>
                  imp_res_tac known_sing_EQ_E >> fs[] >> rveq >>
                  first_x_assum (mp_tac o MATCH_MP known_preserves_setGlobals)>>
                  simp[])) >>
          metis_tac[])))

val kca_sing_sga =
    known_correct_approx
      |> Q.SPECL [`[e]`, `as`, `g0`, `[(e',a)]`, `g`]
      |> SIMP_RULE (srw_ss()) [PULL_FORALL]
      |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL

val ssgc_free_preserved_SING' = Q.store_thm(
  "ssgc_free_preserved_SING'",
  `esgc_free e1 ∧ ssgc_free s0 ∧
   EVERY vsgc_free env ∧ evaluate([e1],env,s0) = (res,s) ⇒ ssgc_free s`,
  rpt strip_tac >>
  `EVERY esgc_free [e1]` by simp[] >>
  metis_tac[ssgc_evaluate]);

val say = say0 "known_correct";


val evaluate_app_NONE_SOME = Q.store_thm(
  "evaluate_app_NONE_SOME",
  `evaluate_app NONE fval argvs s0 = (res, s) ∧
   res ≠ Rerr (Rabort Rtype_error) ∧
   ((∃e2 b. fval = Closure (SOME mm) [] e2 (LENGTH argvs) b) ∨
    (∃base env fs j.
            fval = Recclosure (SOME base) [] env fs j ∧ mm = base + j ∧
            LENGTH argvs = FST (EL j fs))) ⇒
   evaluate_app (SOME mm) fval argvs s0 = (res, s)`,
  Cases_on `argvs = []` >>
  simp[evaluate_app_rw] >> Cases_on `fval` >>
  simp[eqs, result_case_eq, bool_case_eq, pair_case_eq] >>
  rpt strip_tac >> fs[dest_closure_def] >> rveq >> fs[] >>
  rpt (pairarg_tac >> fs[]) >> rveq >>
  fs[check_loc_def, revdroprev, revtakerev]);

val kerel_def = Define`
  kerel as g' e1 e2 ⇔
    ∃g0 g apx. subspt g g' ∧ known [e1] as g0 = ([(e2,apx)], g)
`;

val kvrel_def = tDefine "kvrel" `
  (kvrel g (Number i) v ⇔ v = Number i) ∧
  (kvrel g (Word64 w) v ⇔ v = Word64 w) ∧
  (kvrel g (Block n vs) v ⇔
     ∃vs'. v = Block n vs' ∧ LIST_REL (kvrel g) vs vs') ∧
  (kvrel g (RefPtr n) v ⇔ v = RefPtr n) ∧
  (kvrel g (Closure lopt vs1 env1 n bod1) v ⇔
     ∃vs2 env2 bod2 eapx.
       LIST_REL (kvrel g) vs1 vs2 ∧ LIST_REL (kvrel g) env1 env2 ∧
       LIST_REL val_approx_val eapx env2 ∧
       kerel (REPLICATE n Other ++ eapx) g bod1 bod2 ∧
       v = Closure lopt vs2 env2 n bod2) ∧
  (kvrel g (Recclosure lopt vs1 env1 fns1 i) v ⇔
     let gfn = case lopt of
                 | NONE => K Other
                 | SOME n => (λi. Clos (n + i) (FST (EL i fns1))) in
     let clos = GENLIST gfn (LENGTH fns1)
     in
       ∃vs2 env2 fns2 eapx.
         LIST_REL (kvrel g) vs1 vs2 ∧ LIST_REL (kvrel g) env1 env2 ∧
         LIST_REL val_approx_val eapx env2 ∧
         LIST_REL (λ(n1,e1) (n2,e2).
                     n1 = n2 ∧
                     kerel (REPLICATE n1 Other ++ clos ++ eapx) g e1 e2)
                  fns1 fns2 ∧
         v = Recclosure lopt vs2 env2 fns2 i)
` (WF_REL_TAC `measure (v_size o FST o SND)` >> simp[v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[])
val kvrel_ind = theorem "kvrel_ind"
val kvrel_def = save_thm(
  "kvrel_def[simp]",
  SIMP_RULE (bool_ss ++ ETA_ss) [] kvrel_def)

(* necessary kvrel *)
val kvrel_vsgc_free = Q.store_thm(
  "kvrel_vsgc_free",
  `∀g v1 v2. kvrel g v1 v2 ⇒ (vsgc_free v1 ⇔ vsgc_free v2)`,
  ho_match_mp_tac kvrel_ind >> simp[] >> rpt strip_tac
  >- (fs[EVERY_MEM, LIST_REL_EL_EQN] >> metis_tac[MEM_EL])
  >- (fs[EVERY_MEM, LIST_REL_EL_EQN] >>
      fs[kerel_def] >> imp_res_tac known_preserves_setGlobals >>
      fs[] >> metis_tac[MEM_EL])
  >- (fs[EVERY_MEM, LIST_REL_EL_EQN, elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS,
         FORALL_PROD]>>
      EQ_TAC >> rpt strip_tac
      >- (imp_res_tac (MEM_EL |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GSYM) >>
          qcase_tac `m < LENGTH fns2` >>
          Cases_on `EL m fns1` >> fs[] >>
          first_x_assum (qspec_then `m` mp_tac) >> simp[] >>
          rw[kerel_def] >>
          imp_res_tac known_preserves_setGlobals >> fs[] >>
          metis_tac[MEM_EL])
      >- metis_tac[MEM_EL]
      >- metis_tac[MEM_EL]
      >- (imp_res_tac (MEM_EL |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GSYM) >>
          qcase_tac `m < LENGTH fns1` >>
          Cases_on `EL m fns2` >> fs[] >>
          first_x_assum (qspec_then `m` mp_tac) >> simp[] >>
          rw[kerel_def] >>
          imp_res_tac known_preserves_setGlobals >> fs[] >>
          metis_tac[MEM_EL])
      >- metis_tac[MEM_EL]
      >- metis_tac[MEM_EL]))

val kvrel_Boolv = Q.store_thm(
  "kvrel_Boolv[simp]",
  `(kvrel g (Boolv b) v ⇔ v = Boolv b) ∧
   (kvrel g v (Boolv b) ⇔ v = Boolv b)`,
  simp[closSemTheory.Boolv_def] >> Cases_on `v` >> simp[] >> metis_tac[]);

val kvrel_Unit = Q.store_thm(
  "kvrel_Unit[simp]",
  `(kvrel g Unit v ⇔ v = Unit) ∧ (kvrel g v Unit ⇔ v = Unit)`,
  simp[Unit_def] >> Cases_on `v` >> simp[] >> metis_tac[])

val kvrel_EVERY_vsgc_free = Q.store_thm(
  "kvrel_EVERY_vsgc_free",
  `∀vs1 vs2.
     LIST_REL (kvrel g) vs1 vs2 ⇒
     (EVERY vsgc_free vs1 ⇔ EVERY vsgc_free vs2)`,
  Induct_on `LIST_REL` >> simp[] >> metis_tac[kvrel_vsgc_free]);

(* necessary kvrel *)
val kvrel_val_approx = Q.store_thm(
  "kvrel_val_approx",
  `∀g v1 v2.
     kvrel g v1 v2 ⇒ ∀a. val_approx_val a v1 ⇔ val_approx_val a v2`,
  ho_match_mp_tac kvrel_ind >> rw[]
  >- (Cases_on `a` >> simp[] >> fs[LIST_REL_EL_EQN] >> metis_tac[MEM_EL])
  >- (Cases_on `a` >> simp[] >> fs[LIST_REL_EL_EQN] >> metis_tac[LENGTH_NIL])
  >- (Cases_on `a` >> fs[LIST_REL_EL_EQN] >> qcase_tac `lopt = SOME _` >>
      Cases_on `lopt` >> simp[] >> qcase_tac `EL j` >>
      qcase_tac `j < LENGTH fns2` >> Cases_on `j < LENGTH fns2` >> simp[] >>
      qcase_tac `vvs = []` >> reverse (Cases_on `vvs`)
      >- (simp[] >> qcase_tac `vvs' = []` >> Cases_on `vvs'` >> fs[]) >>
      fs[LENGTH_NIL, LENGTH_NIL_SYM] >> rfs[] >> res_tac >>
      fs[UNCURRY]))

val kvrel_LIST_REL_val_approx = Q.store_thm(
  "kvrel_LIST_REL_val_approx",
  `∀vs1 vs2.
      LIST_REL (kvrel g) vs1 vs2 ⇒
      ∀as. LIST_REL val_approx_val as vs1 ⇔ LIST_REL val_approx_val as vs2`,
  Induct_on `LIST_REL` >> simp[] >> metis_tac[kvrel_val_approx]);

val ksrel_def = Define`
  ksrel g (s1:'a closSem$state) (s2:'a closSem$state) ⇔
     s2.clock = s1.clock ∧ s2.ffi = s1.ffi ∧
     LIST_REL (OPTREL (kvrel g)) s1.globals s2.globals ∧
     fmap_rel (ref_rel (kvrel g)) s1.refs s2.refs ∧
     s1.code = FEMPTY ∧ s2.code = FEMPTY
`;

(* ksrel necessary *)
val ksrel_sga = Q.store_thm(
  "ksrel_sga",
  `ksrel g0 s1 s2 ⇒ (state_globals_approx s1 g ⇔ state_globals_approx s2 g)`,
  simp[ksrel_def, state_globals_approx_def, get_global_def, LIST_REL_EL_EQN] >>
  csimp[] >> rpt strip_tac >> eq_tac >> rpt strip_tac >>
  qcase_tac `EL kk (ss:α closSem$state).globals = SOME vv` >>
  qcase_tac `lookup kk gg` >>
  qpat_assum `kk < LENGTH ss.globals`
    (fn th => first_x_assum (mp_tac o C MATCH_MP th) >> assume_tac th) >>
  simp[optionTheory.OPTREL_def] >>
  metis_tac [kvrel_val_approx])

(* ksrel necessary *)
val ksrel_ssgc_free = Q.store_thm(
  "ksrel_ssgc_free",
  `ksrel g s1 s2 ⇒ (ssgc_free s1 ⇔ ssgc_free s2)`,
  simp[ksrel_def, ssgc_free_def] >> rpt strip_tac >> eq_tac >> rpt strip_tac >>
  fs[fmap_rel_OPTREL_FLOOKUP]
  >- (qcase_tac `FLOOKUP s2.refs kk = SOME (ValueArray vvl)` >>
      `OPTREL (ref_rel (kvrel g)) (FLOOKUP s1.refs kk) (FLOOKUP s2.refs kk)`
         by simp[] >> pop_assum mp_tac >>
      simp_tac(srw_ss()) [OPTREL_def] >> simp[PULL_EXISTS] >> Cases >>
      simp[] >> metis_tac[kvrel_EVERY_vsgc_free])
  >- (fs[LIST_REL_EL_EQN] >>
      imp_res_tac (MEM_EL |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GSYM) >>
      qcase_tac `EL kk s2.globals` >>
      `OPTREL (kvrel g) (EL kk s1.globals) (EL kk s2.globals)` by simp[] >>
      pop_assum mp_tac >> simp_tac(srw_ss()) [OPTREL_def] >> simp[] >>
      metis_tac[kvrel_vsgc_free, MEM_EL])
  >- (qcase_tac `FLOOKUP s1.refs kk = SOME (ValueArray vvl)` >>
      `OPTREL (ref_rel (kvrel g)) (FLOOKUP s1.refs kk) (FLOOKUP s2.refs kk)`
         by simp[] >> pop_assum mp_tac >>
      simp_tac(srw_ss()) [OPTREL_def] >> simp[PULL_EXISTS] >>
      metis_tac[kvrel_EVERY_vsgc_free])
  >- (fs[LIST_REL_EL_EQN] >>
      imp_res_tac (MEM_EL |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GSYM) >>
      qcase_tac `EL kk s1.globals` >>
      `OPTREL (kvrel g) (EL kk s1.globals) (EL kk s2.globals)` by simp[] >>
      pop_assum mp_tac >> simp_tac(srw_ss()) [OPTREL_def] >> simp[] >>
      metis_tac[kvrel_vsgc_free, MEM_EL]))

val krrel_def = Define`
  (krrel g (Rval vs1, s1) r ⇔
      ∃s2 vs2. r = (Rval vs2,s2) ∧ LIST_REL (kvrel g) vs1 vs2 ∧ ksrel g s1 s2) ∧
  (krrel g (Rerr (Rabort Rtype_error), _) _ ⇔ T) ∧
  (krrel g (Rerr (Rabort Rtimeout_error), s1) (Rerr e, s2) ⇔
     e = Rabort Rtimeout_error ∧ ksrel g s1 s2) ∧
  (krrel g (Rerr (Rraise v1), s1) (Rerr (Rraise v2), s2) ⇔
     kvrel g v1 v2 ∧ ksrel g s1 s2) ∧
  (krrel _ _ _ ⇔ F)
`;
val _ = export_rewrites ["krrel_def"]

val krrel_errval = Q.store_thm(
  "krrel_errval[simp]",
  `(krrel g (Rerr e, s1) (Rval vs, s2) ⇔ e = Rabort Rtype_error)`,
  Cases_on `e` >> simp[] >> qcase_tac `Rabort a` >> Cases_on `a` >> simp[]);

val krrel_err_rw = Q.store_thm(
  "krrel_err_rw",
  `krrel g (Rerr e, s1) r ⇔
      e = Rabort Rtype_error ∨
      (∃s2. e = Rabort Rtimeout_error ∧ r = (Rerr (Rabort Rtimeout_error), s2) ∧
            ksrel g s1 s2) ∨
      (∃v1 v2 s2.
            e = Rraise v1 ∧ r = (Rerr (Rraise v2),s2) ∧ kvrel g v1 v2 ∧
            ksrel g s1 s2)`,
  Cases_on `e` >> simp[] >> Cases_on `r` >> simp[]
  >- (qcase_tac `krrel _ _ (r2, s2)` >> Cases_on `r2` >> simp[] >>
      qcase_tac `krrel _ _ (Rerr e,_)` >> Cases_on `e` >> simp[])
  >- (qcase_tac `Rabort abt` >> Cases_on `abt` >> simp[] >>
      qcase_tac `krrel _ _ (r2,s2)` >> Cases_on `r2` >> simp[]));

(* necesssary kvrel *)
val kvrel_v_to_list = Q.store_thm(
  "kvrel_v_to_list",
  `∀g v1 v2 l1.
     kvrel g v1 v2 ∧ v_to_list v1 = SOME l1 ⇒
     ∃l2. v_to_list v2 = SOME l2 ∧ LIST_REL (kvrel g) l1 l2`,
  ho_match_mp_tac kvrel_ind >> simp[v_to_list_def, PULL_EXISTS] >>
  rpt strip_tac >> qcase_tac `v_to_list (closSem$Block _ vs2)` >>
  Cases_on `vs2` >> fs[v_to_list_def] >> rw[] >> fs[v_to_list_def] >>
  qcase_tac `v_to_list (closSem$Block _ (_ :: vs2'))` >>
  Cases_on `vs2'` >> fs[v_to_list_def] >> rw[] >> fs[v_to_list_def] >>
  qcase_tac `v_to_list (closSem$Block _ (_ :: _ :: vs2''))` >>
  Cases_on `vs2''` >> fs[v_to_list_def] >> rw[] >> fs[v_to_list_def] >>
  fs[eqs] >> rveq >> simp[PULL_EXISTS] >> metis_tac[MEM]);

val kvrel_list_to_v = Q.store_thm(
  "kvrel_list_to_v",
  `∀vs1 vs2. LIST_REL (kvrel g) vs1 vs2 ⇒
             kvrel g (list_to_v vs1) (list_to_v vs2)`,
  Induct_on `LIST_REL` >> simp[list_to_v_def])

val kvrel_do_eq0 = Q.prove(
  `(∀u1 v1 u2 v2 b g.
      kvrel g u1 u2 ∧ kvrel g v1 v2 ∧ do_eq u1 v1 = Eq_val b ⇒
      do_eq u2 v2 = Eq_val b) ∧
   (∀us1 vs1 us2 vs2 b g.
      LIST_REL (kvrel g) us1 us2 ∧ LIST_REL (kvrel g) vs1 vs2 ∧
      do_eq_list us1 vs1 = Eq_val b ⇒
      do_eq_list us2 vs2 = Eq_val b)`,
  ho_match_mp_tac do_eq_ind >> rpt conj_tac
  >- (Cases >> Cases >> strip_tac >>
      simp[SimpL ``$==>``, do_eq_def, v_case_eq, bool_case_eq, PULL_EXISTS] >>
      fs[] >> simp[do_eq_def] >> rw[] >> fs[LIST_REL_EL_EQN] >> metis_tac[])
  >- simp[]
  >- (simp[PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      ONCE_REWRITE_TAC [do_eq_def] >> qcase_tac `do_eq uu1 vv1` >>
      Cases_on `do_eq uu1 vv1` >> fs[] >> simp[bool_case_eq] >> dsimp[] >>
      qcase_tac `do_eq uu1 vv1 = Eq_val b` >> Cases_on `b` >> simp[] >>
      rpt strip_tac >> nailIHx strip_assume_tac >> simp[] >> metis_tac[])
  >- (simp[PULL_EXISTS] >> ONCE_REWRITE_TAC[do_eq_def] >> simp[])
  >- (simp[PULL_EXISTS] >> ONCE_REWRITE_TAC[do_eq_def] >> simp[]));

val kvrel_do_eq = save_thm("kvrel_do_eq", kvrel_do_eq0 |> CONJUNCT1)

(* necessary(!) *)
val kvrel_op_correct_Rval = Q.store_thm(
  "kvrel_op_correct_Rval",
  `LIST_REL (kvrel g) vs1 vs2 ∧ do_app opn vs1 s01 = Rval(v1,s1) ∧
   ksrel g s01 s02 ⇒
   ∃v2 s2. do_app opn vs2 s02 = Rval(v2,s2) ∧ ksrel g s1 s2 ∧
           kvrel g v1 v2`,
  Cases_on `opn` >> simp[do_app_def, eqs, bool_case_eq, PULL_EXISTS] >>
  TRY (rw[] >> fs[LIST_REL_EL_EQN] >> NO_TAC)
  >- (csimp[get_global_def] >> simp[ksrel_def] >>
      simp[LIST_REL_EL_EQN, OPTREL_def] >> rpt strip_tac >> rveq >>
      res_tac >> fs[] >> rveq >> simp[])
  >- (csimp[get_global_def, PULL_EXISTS] >> simp[ksrel_def] >> rw[] >>
      fs[LIST_REL_EL_EQN] >> rfs[] >> res_tac >> fs[OPTREL_def] >> fs[] >>
      simp[EL_LUPDATE, bool_case_eq] >> metis_tac[])
  >- (rw[] >> fs[] >> fs[ksrel_def, OPTREL_def])
  >- (rw[] >> fs[] >> fs[ksrel_def, fmap_rel_OPTREL_FLOOKUP] >>
      qcase_tac `FLOOKUP _ PTR` >>
      rpt (first_x_assum (qspec_then `PTR` mp_tac)) >>
      simp[OPTREL_def] >> rw[] >> fs[LIST_REL_EL_EQN])
  >- (rw[] >> fs[] >> fs[ksrel_def, fmap_rel_OPTREL_FLOOKUP] >>
      qcase_tac `FLOOKUP _ PTR` >>
      rpt (first_x_assum (qspec_then `PTR` mp_tac)) >>
      simp[OPTREL_def] >> rw[] >> fs[LIST_REL_EL_EQN])
  >- (rw[] >> fs[] >> fs[ksrel_def] >>
      `FDOM s02.refs = FDOM s01.refs` by fs[fmap_rel_def] >> simp[] >>
      irule fmap_rel_FUPDATE_same >> simp[])
  >- (rw[] >> fs[] >> fs[ksrel_def] >>
      `FDOM s02.refs = FDOM s01.refs` by fs[fmap_rel_def] >> simp[] >>
      irule fmap_rel_FUPDATE_same >> simp[LIST_REL_REPLICATE_same])
  >- (rw[] >> fs[] >> fs[ksrel_def] >>
      qcase_tac `FLOOKUP _ PTR = SOME (ByteArray barray)` >>
      qexists_tac `barray` >> simp[] >> fs[fmap_rel_OPTREL_FLOOKUP] >>
      rpt (first_x_assum (qspec_then `PTR` mp_tac)) >>
      simp[OPTREL_def])
  >- (rw[] >> fs[] >>
      qcase_tac `FLOOKUP _ PTR = SOME (ByteArray barray)` >>
      qexists_tac `barray` >> simp[] >> fs[ksrel_def] >>
      reverse conj_tac >- simp[fmap_rel_FUPDATE_same] >>
      fs[fmap_rel_OPTREL_FLOOKUP] >>
      rpt (first_x_assum (qspec_then `PTR` mp_tac)) >>
      simp[OPTREL_def])
  >- (rw[] >> fs[] >> metis_tac[kvrel_v_to_list])
  >- (rw[] >> fs[] >> simp[kvrel_list_to_v])
  >- (rw[] >> fs[] >> fs[ksrel_def] >>
      `FDOM s02.refs = FDOM s01.refs` by fs[fmap_rel_def] >>
      simp[fmap_rel_FUPDATE_same])
  >- (rw[] >> fs[] >> fs[ksrel_def] >>
      qcase_tac `FLOOKUP _ PTR = SOME (ValueArray vas)` >>
      fs[fmap_rel_OPTREL_FLOOKUP] >>
      rpt (first_x_assum (qspec_then `PTR` mp_tac)) >>
      simp[OPTREL_def, PULL_EXISTS] >> simp[LIST_REL_EL_EQN] >> rw[] >>
      metis_tac[MEM_EL, EVERY_MEM, integerTheory.INT_INJ,
                integerTheory.INT_OF_NUM, integerTheory.INT_LT])
  >- (rw[] >> fs[] >> fs[ksrel_def] >>
      qcase_tac `FLOOKUP _ PTR = SOME (ValueArray vas)` >>
      fs[fmap_rel_OPTREL_FLOOKUP] >> rveq >>
      simp[OPTREL_def, FLOOKUP_UPDATE, bool_case_eq] >>
      `OPTREL (ref_rel (kvrel g))
              (FLOOKUP s01.refs PTR) (FLOOKUP s02.refs PTR)`
         by simp[] >> pop_assum mp_tac >>
      simp_tac (srw_ss()) [OPTREL_def] >> simp[PULL_EXISTS] >>
      rw[LIST_REL_EL_EQN] >- fs[] >> qcase_tac `PTR = kk` >>
      Cases_on `PTR = kk` >> simp[]
      >- (irule EVERY2_LUPDATE_same >> simp[LIST_REL_EL_EQN]) >>
      rpt (first_x_assum (qspec_then `kk` mp_tac)) >>
      simp[OPTREL_def, PULL_EXISTS] >> rw[] >> rw[])
  >- (rw[ksrel_def, pair_case_eq] >> simp[] >> fs[] >>
      simp[PULL_EXISTS] >> qcase_tac `FLOOKUP _ PTR = SOME (ByteArray bytes)` >>
      `FLOOKUP s02.refs PTR = SOME (ByteArray bytes)`
         by (fs[fmap_rel_OPTREL_FLOOKUP] >>
             rpt (first_x_assum (qspec_then `PTR` mp_tac)) >>
             simp[OPTREL_def]) >> simp[] >>
      simp[fmap_rel_FUPDATE_same])
  >- (rw[] >> fs[] >> rw[] >> metis_tac[kvrel_do_eq])
  >- (rw[] >> fs[pair_case_eq] >> rveq >> simp[]))

val do_app_EQ_Rerr = Q.store_thm(
  "do_app_EQ_Rerr",
  `closSem$do_app opn vs s0 = Rerr e ⇒ e = Rabort Rtype_error`,
  Cases_on `opn` >> simp[do_app_def, eqs, bool_case_eq, pair_case_eq] >> rw[]);

val kvrel_lookup_vars = Q.store_thm(
  "kvrel_lookup_vars",
  `∀env01 env02 vars env1.
     LIST_REL (kvrel g) env01 env02 ∧ lookup_vars vars env01 = SOME env1 ⇒
     ∃env2. lookup_vars vars env02 = SOME env2 ∧
            LIST_REL (kvrel g) env1 env2`,
  Induct_on `vars` >> simp[lookup_vars_def, eqs, PULL_EXISTS] >>
  fs[LIST_REL_EL_EQN] >> metis_tac[]);

val loptrel_def = Define`
  loptrel fv numargs lopt1 lopt2 ⇔
     lopt2 = lopt1 ∨
     lopt1 = NONE ∧
     case (fv,lopt2) of
       | (Closure (SOME loc1) ae _ n bod, SOME loc2) =>
            loc1 = loc2 ∧ n = numargs ∧ ae = []
       | (Recclosure (SOME loc1) ae _ fns i, SOME loc2) =>
         i < LENGTH fns ∧ loc2 = loc1 + i ∧ numargs = FST (EL i fns) ∧
         ae = []
       | _ => F
`;

val ksrel_find_code = Q.store_thm(
  "ksrel_find_code",
  `ksrel g s1 s2 ⇒ find_code l (vs1:closSem$v list) s1.code = NONE`,
  simp[ksrel_def, find_code_def, eqs, pair_case_eq]);

val kvrel_dest_closure_SOME_Partial = Q.store_thm(
  "kvrel_dest_closure_SOME_Partial",
  `dest_closure lopt1 f1 vs1 = SOME (Partial_app v1) ∧ kvrel g f1 f2 ∧
   LIST_REL (kvrel g) vs1 vs2 ∧ loptrel f2 n lopt1 lopt2 ∧ LENGTH vs2 = n ⇒
   ∃v2. dest_closure lopt2 f2 vs2 = SOME (Partial_app v2) ∧
        kvrel g v1 v2`,
  simp[dest_closure_def, eqs, v_case_eq] >> rpt strip_tac >> rveq >> fs[] >>
  rpt strip_tac >> fs[eqs, bool_case_eq] >> rveq >> fs[loptrel_def] >> rveq
  >- (simp[EVERY2_APPEND_suff] >> fs[LIST_REL_EL_EQN] >> metis_tac[])
  >- (Cases_on `lopt2` >> simp[EVERY2_APPEND_suff] >> fs[LIST_REL_EL_EQN] >>
      qcase_tac `option_CASE lll` >> Cases_on `lll` >> fs[LIST_REL_EL_EQN])
  >- (rpt (pairarg_tac >> fs[]) >> fs[bool_case_eq] >>
      simp[EVERY2_APPEND_suff] >>
      qcase_tac `LIST_REL val_approx_val envapx env2` >> simp[PULL_EXISTS] >>
      qexists_tac `envapx` >>
      fs[LIST_REL_EL_EQN] >> qcase_tac `EL ii` >>
      qpat_assum `∀n. _ ⇒ UNCURRY f x y` mp_tac >>
      disch_then (qspec_then `ii` mp_tac) >> simp[] >> rw[] >> simp[])
  >- (rpt (pairarg_tac >> fs[]) >> fs[bool_case_eq] >>
      Cases_on `lopt2` >> fs[] >> qcase_tac `option_CASE lll` >>
      Cases_on `lll` >> fs[] >> rveq >>
      qpat_assum `LIST_REL (UNCURRY _) _ _` mp_tac >>
      CONV_TAC (LAND_CONV (REWRITE_CONV [LIST_REL_EL_EQN])) >>
      qcase_tac `EL ii` >>
      disch_then (CONJUNCTS_THEN2 assume_tac (qspec_then `ii` mp_tac)) >>
      strip_tac >> rfs[] >> fs[LIST_REL_EL_EQN]))

val kvrel_dest_closure_SOME_Full = Q.store_thm(
  "kvrel_dest_closure_SOME_Full",
  `dest_closure lopt1 f1 vs1 = SOME (Full_app e1 env1 args1) ∧
   kvrel g f1 f2 ∧
   LIST_REL (kvrel g) vs1 vs2 ∧ loptrel f2 n lopt1 lopt2 ∧ LENGTH vs2 = n ⇒
   ∃eapx e2 env2 args2.
      dest_closure lopt2 f2 vs2 = SOME (Full_app e2 env2 args2) ∧
      LIST_REL val_approx_val eapx env2 ∧
      LIST_REL (kvrel g) env1 env2 ∧ LIST_REL (kvrel g) args1 args2 ∧
      kerel eapx g e1 e2`,
  simp[dest_closure_def, eqs, bool_case_eq] >>
  csimp[revtakerev, revdroprev] >> dsimp[] >> rpt strip_tac >> rveq >>
  fs[] >> rveq >> fs[]
  >- (imp_res_tac LIST_REL_LENGTH >> simp[] >> fs[] >>
      simp[EVERY2_APPEND_suff, EVERY2_DROP, EVERY2_TAKE] >>
      fs[loptrel_def] >>
      qexists_tac `REPLICATE num_args Other ++ eapx` >> simp[] >>
      rpt conj_tac >>
      TRY (irule EVERY2_APPEND_suff >> simp[] >>
           simp[LIST_REL_EL_EQN, LENGTH_REPLICATE, EL_REPLICATE]) >>
      Cases_on `lopt2` >> fs[] >>
      qcase_tac `option_CASE lll` >> Cases_on `lll` >> fs[] >> rveq >>
      fs[check_loc_def])
  >- (rpt (pairarg_tac >> fs[]) >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
      fs[bool_case_eq] >> rveq >>
      qpat_assum `LIST_REL (UNCURRY _) _ _`
        (fn th => (mp_tac o SIMP_RULE (srw_ss()) [LIST_REL_EL_EQN]) th >>
                  assume_tac th) >>
      qcase_tac `EL ii` >> simp[] >>
      disch_then (qspec_then `ii` mp_tac) >> simp[] >> strip_tac >> rveq >>
      simp[EVERY2_TAKE] >> qcase_tac `REPLICATE nargs Other` >>
      qcase_tac `GENLIST (option_CASE locc _ _)` >>
      qcase_tac `LIST_REL (UNCURRY _) fns1 fns2` >>
      qcase_tac `LIST_REL val_approx_val envapx _` >>
      qexists_tac `REPLICATE nargs Other ++
                   GENLIST (case locc of
                              | NONE => K Other
                              | SOME n => (λi. Clos (i + n) (FST (EL i fns1))))
                           (LENGTH fns2) ++ envapx` >> simp[] >>
      conj_tac
      >- (fs[loptrel_def] >> Cases_on `lopt2` >> fs[] >>
          qcase_tac `option_CASE lll` >> Cases_on `lll` >> fs[] >>
          fs[check_loc_def]) >>
      conj_tac >> rpt (irule EVERY2_APPEND_suff) >> simp[EVERY2_DROP]
      >- simp[LIST_REL_EL_EQN, EL_REPLICATE, LENGTH_REPLICATE]
      >- (simp[LIST_REL_GENLIST] >> Cases_on `locc` >> simp[] >>
          fs[LIST_REL_EL_EQN, UNCURRY])
      >- (simp[LIST_REL_GENLIST] >> rpt strip_tac >>
          qexists_tac `envapx` >> simp[])))

val kvrel_subspt = Q.store_thm(
  "kvrel_subspt",
  `∀g v1 v2 g'. kvrel g v1 v2 ∧ subspt g g' ⇒ kvrel g' v1 v2`,
  ho_match_mp_tac kvrel_ind >> simp[PULL_EXISTS] >> rpt strip_tac
  >- (irule EVERY2_MEM_MONO >> imp_res_tac LIST_REL_LENGTH >>
      simp[FORALL_PROD, MEM_ZIP, PULL_EXISTS] >> qexists_tac `kvrel g` >>
      simp[] >> metis_tac[MEM_EL])
  >- (qcase_tac `LIST_REL val_approx_val envapx _` >> qexists_tac `envapx` >>
      simp[] >> rpt conj_tac >>
      TRY (irule EVERY2_MEM_MONO >> imp_res_tac LIST_REL_LENGTH >>
           simp[FORALL_PROD, MEM_ZIP, PULL_EXISTS] >>
           qexists_tac `kvrel g` >> simp[] >> metis_tac[MEM_EL]) >>
      fs[kerel_def] >> metis_tac[subspt_trans])
  >- (qcase_tac `LIST_REL val_approx_val envapx _` >> qexists_tac `envapx` >>
      simp[] >> rpt conj_tac >>
      TRY (irule EVERY2_MEM_MONO >> imp_res_tac LIST_REL_LENGTH >>
           simp[FORALL_PROD, MEM_ZIP, PULL_EXISTS] >>
           qexists_tac `kvrel g` >> simp[] >> metis_tac[MEM_EL]) >>
      qpat_assum `LIST_REL (UNCURRY _) _ _` mp_tac >> simp[LIST_REL_EL_EQN] >>
      rpt strip_tac >> fs[] >> rfs[] >> rpt (pairarg_tac >> fs[]) >>
      qcase_tac `nn < LENGTH _` >> first_x_assum (qspec_then `nn` mp_tac) >>
      simp[] >> simp[kerel_def] >> metis_tac[subspt_trans]))

val kvrel_LIST_REL_subspt = Q.store_thm(
  "kvrel_LIST_REL_subspt",
  `∀vs1 vs2. LIST_REL (kvrel g) vs1 vs2 ⇒
             ∀g'. subspt g g' ⇒ LIST_REL (kvrel g') vs1 vs2`,
  Induct_on `LIST_REL` >> simp[] >> metis_tac[kvrel_subspt]);

val ksrel_subspt = Q.store_thm(
  "ksrel_subspt",
  `ksrel g s1 s2 ∧ subspt g g' ⇒ ksrel g' s1 s2`,
  simp[ksrel_def] >> rpt strip_tac
  >- (irule EVERY2_mono >>
      qexists_tac `OPTREL (kvrel g)` >> simp[] >> rpt strip_tac >>
      irule OPTREL_MONO >> qexists_tac `kvrel g` >>
      metis_tac[kvrel_subspt])
  >- (irule fmap_rel_mono >> qexists_tac `ref_rel (kvrel g)` >> simp[] >>
      Cases >> simp[PULL_EXISTS] >> metis_tac[kvrel_LIST_REL_subspt]));

val krrel_better_subspt = Q.store_thm(
  "krrel_better_subspt",
  `krrel g (res1,s1) (res2,s2) ∧ subspt g g' ⇒ krrel g' (res1,s1) (res2,s2)`,
  Cases_on `res1` >> simp[krrel_err_rw] >>
  metis_tac[kvrel_LIST_REL_subspt, ksrel_subspt, kvrel_subspt]);

(*
val known_correct0 = Q.prove(
  `(∀a es env1 env2 (s01:α closSem$state) s02 res1 s1 g0 g g' as ealist.
      a = (es,env1,s01) ∧ evaluate (es, env1, s01) = (res1, s1) ∧
      EVERY esgc_free es ∧ subspt g0 g ∧ subspt g g' ∧
      LIST_REL val_approx_val as env1 ∧ EVERY vsgc_free env1 ∧
      LIST_REL (kvrel g') env1 env2 ∧ ksrel g' s01 s02 ∧
      state_globals_approx s01 g' ∧ BAG_ALL_DISTINCT (elist_globals es) ∧
      ssgc_free s01 ∧ known es as g0 = (ealist, g) ⇒
      ∃res2 s2.
        evaluate(MAP FST ealist, env2, s02) = (res2, s2) ∧
        krrel g' (res1,s1) (res2,s2)) ∧
   (∀lopt1 f1 args1 (s01:α closSem$state) res1 s1 lopt2 f2 args2 s02 g.
      evaluate_app lopt1 f1 args1 s01 = (res1,s1) ∧ ssgc_free s01 ∧
      kvrel g f1 f2 ∧ LIST_REL (kvrel g) args1 args2 ∧
      ksrel g s01 s02 ∧ state_globals_approx s01 g ∧
      EVERY vsgc_free args1 ∧ loptrel f2 (LENGTH args1) lopt1 lopt2 ⇒
      ∃res2 s2.
        evaluate_app lopt2 f2 args2 s02 = (res2,s2) ∧
        krrel g (res1,s1) (res2,s2))`,
  ho_match_mp_tac evaluate_ind >> rpt conj_tac
  >- (say "nil" >> simp[evaluate_def, known_def])
  >- (say "cons" >>
      simp[evaluate_def, known_def, pair_case_eq, result_case_eq,
           BAG_ALL_DISTINCT_BAG_UNION] >>
      rpt strip_tac >> rveq >> rpt (pairarg_tac >> fs[]) >> rveq >> simp[] >>
      first_x_assum (patresolve `known [_] _ _ = _` last) >>
      disch_then (resolve_selected (el 4)) >> simp[] >>
      patresolve `known [_] _ _ = _` hd subspt_known_elist_globals >> simp[] >>
      disch_then (resolve_selected hd) >> simp[] >> strip_tac >>
      disch_then (resolve_selected last) >> simp[] >>
      (impl_keep_tac >- metis_tac[subspt_trans]) >>
      rw[]
      >- (imp_res_tac known_sing_EQ_E >> rveq >> fs[] >>
          sel_ihpc last >> simp[] >> disch_then (resolve_selected (el 3)) >>
          simp[] >> disch_then (resolve_selected hd) >> simp[] >> impl_tac
          >- (conj_tac
              >- (resolve_selected hd (GEN_ALL kca_sing_sga) >> simp[] >>
                  disch_then (resolve_selected last) >> simp[] >>
                  metis_tac[kvrel_LIST_REL_val_approx, kvrel_EVERY_vsgc_free,
                            ksrel_sga, ksrel_ssgc_free]) >>
              metis_tac[ssgc_free_preserved_SING']) >> rw[] >>
          simp[Once evaluate_CONS] >> imp_res_tac evaluate_SING >> rveq >>
          fs[])
      >- (imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> sel_ihpc last >>
          simp[] >> disch_then (resolve_selected (el 3)) >> simp[] >>
          disch_then (resolve_selected hd) >> simp[] >> impl_tac
          >- (conj_tac
              >- (resolve_selected hd (GEN_ALL kca_sing_sga) >> simp[] >>
                  disch_then (resolve_selected last) >> simp[] >>
                  metis_tac[kvrel_LIST_REL_val_approx, kvrel_EVERY_vsgc_free,
                            ksrel_sga, ksrel_ssgc_free]) >>
              metis_tac[ssgc_free_preserved_SING']) >> rw[] >>
          simp[Once evaluate_CONS, result_case_eq] >> fs[krrel_err_rw] >>
          dsimp[] >> metis_tac[result_CASES])
      >- (imp_res_tac known_sing_EQ_E >> rveq >> fs[] >>
          simp[Once evaluate_CONS, result_case_eq, pair_case_eq] >>
          dsimp[] >> fs[krrel_err_rw] >> metis_tac[pair_CASES, result_CASES]))
  >- (say "var" >>
      simp[evaluate_def, bool_case_eq, known_def] >>
      rpt strip_tac >> fs[LIST_REL_EL_EQN])
  >- (say "if" >>
      simp[evaluate_def, pair_case_eq, bool_case_eq, BAG_ALL_DISTINCT_BAG_UNION,
           result_case_eq, known_def] >> rpt strip_tac >> rveq >> fs[] >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >> fixeqs >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      map_every qcase_tac [`ksrel g' s01 s02`, `subspt g g'`,
                           `known [eb] as g2 = ([(eb',eapx)], g)`,
                           `known [tb] as g1 = ([(tb',tapx)], g2)`,
                           `known [gd] as g0 = ([(gd',gapx)], g1)`] >>
      `known [gd;tb] as g0 = ([(gd',gapx); (tb',tapx)], g2)`
        by simp[known_def] >>
      resolve_selected hd (subspt_known_elist_globals)>> simp[] >>
      disch_then (resolve_selected hd) >> simp[] >> strip_tac >>
      patresolve `known [gd] _ _ = _` hd subspt_known_elist_globals >> simp[] >>
      disch_then (resolve_selected hd) >> simp[] >> strip_tac
      >- (first_x_assum (patresolve `state_globals_approx _ _` (el 6)) >>
          rpt (disch_then (resolve_selected last) >> simp[]) >>
          impl_keep_tac >- metis_tac[subspt_trans] >> rw[] >>
          simp[evaluate_def] >> imp_res_tac evaluate_SING >> fs[] >> rveq >>
          fs[] >> rveq >> sel_ihpc last >> simp[] >> disch_then irule >>
          simp[]
          >- metis_tac[ssgc_free_preserved_SING']
          >- (patresolve `known [gd] _ _ = _` hd (GEN_ALL kca_sing_sga) >>
              simp[] >> disch_then (resolve_selected last) >> simp[] >>
              metis_tac[ksrel_sga, kvrel_LIST_REL_val_approx,
                        kvrel_EVERY_vsgc_free, ksrel_ssgc_free])
          >- metis_tac[subspt_trans])
      >- (first_x_assum (patresolve `state_globals_approx _ _` (el 6)) >>
          rpt (disch_then (resolve_selected last) >> simp[]) >>
          impl_keep_tac >- metis_tac[subspt_trans] >> rw[] >>
          simp[evaluate_def] >> imp_res_tac evaluate_SING >> fs[] >> rveq >>
          fs[] >> rveq >> sel_ihpc last >> simp[] >> disch_then irule >>
          simp[]
          >- metis_tac[ssgc_free_preserved_SING']
          >- (patresolve `known [exp1] _ _ = _` hd (GEN_ALL kca_sing_sga) >>
              simp[] >> disch_then (resolve_selected last) >> simp[] >>
              metis_tac[ksrel_sga, kvrel_LIST_REL_val_approx,
                        kvrel_EVERY_vsgc_free, ksrel_ssgc_free,
                        state_approx_better_definedg, known_better_definedg]))
      >- ((* guard doesn't evaluate to T or F *) sel_ihpc (el 6) >> simp[] >>
          rpt (disch_then (resolve_selected last) >> simp[]) >>
          impl_keep_tac >- metis_tac[subspt_trans] >> rw[] >>
          simp[evaluate_def] >> imp_res_tac evaluate_SING >> fs[] >> rveq >>
          fs[] >> rveq >> dsimp[bool_case_eq] >> rpt disj2_tac >>
          rpt strip_tac >> rveq >> fs[])
      >- ((* guard errors *) sel_ihpc (el 6) >> simp[] >>
          rpt (disch_then (resolve_selected last) >> simp[]) >>
          impl_keep_tac >- metis_tac[subspt_trans] >> rw[] >>
          dsimp[evaluate_def, result_case_eq, bool_case_eq] >>
          fs[krrel_err_rw] >> metis_tac[pair_CASES, result_CASES]))
  >- (say "let" >>
      simp[evaluate_def, pair_case_eq, result_case_eq] >>
      rpt strip_tac >> rveq >> fs[known_def] >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[BAG_ALL_DISTINCT_BAG_UNION] >>
      map_every qcase_tac [`known [bod] _ g1 = (_, g)`,
                           `known _ _ g0 = (_, g1)`,
                           `subspt g gg`] >>
      patresolve `known _ _ g0 = _` hd subspt_known_elist_globals >> simp[] >>
      disch_then (resolve_selected hd) >> simp[] >>
      (impl_tac >- fs[BAG_DISJOINT, DISJOINT_SYM]) >> strip_tac >>
      first_x_assum (patresolve `known _ _ g0 = _` last) >> simp[] >>
      rpt (disch_then (resolve_selected last) >> simp[]) >>
      (impl_keep_tac >- metis_tac[subspt_trans]) >> rw[] >>
      simp[evaluate_def, result_case_eq]
      >- (imp_res_tac known_sing_EQ_E >> rveq >> fs[] >>
          rveq >> sel_ihpc last >> simp[] >> disch_then irule >> simp[]
          >- metis_tac[ssgc_evaluate]
          >- metis_tac[ssgc_evaluate,rsgc_free_def]
          >- (resolve_selected last known_correct_approx >> simp[] >>
              rpt (disch_then (resolve_selected hd) >> simp[]) >>
              metis_tac[ksrel_sga, kvrel_EVERY_vsgc_free,
                        kvrel_LIST_REL_val_approx, ksrel_ssgc_free])
          >- simp[EVERY2_APPEND_suff]
          >- (irule EVERY2_APPEND_suff >> simp[] >>
              resolve_selected last known_correct_approx >> simp[] >>
              rpt (disch_then (resolve_selected hd) >> simp[]) >>
              metis_tac[ksrel_sga, kvrel_EVERY_vsgc_free,
                        kvrel_LIST_REL_val_approx, ksrel_ssgc_free]))
      >- (fs[krrel_err_rw, result_case_eq] >> dsimp[] >>
          metis_tac[pair_CASES, result_CASES]))
  >- (say "raise" >>
      simp[evaluate_def, pair_case_eq, result_case_eq] >>
      rpt strip_tac >> rveq >> fs[known_def] >> pairarg_tac >> fs[] >>
      imp_res_tac known_sing_EQ_E >> fs[] >> rveq >> fs[] >>
      simp[evaluate_def, pair_case_eq, result_case_eq] >>
      nailIHx strip_assume_tac >> simp[] >> fs[]
      >- (imp_res_tac evaluate_SING >> fs[])
      >- (dsimp[] >> fs[krrel_err_rw] >> metis_tac[result_CASES]))
  >- (say "handle" >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           BAG_ALL_DISTINCT_BAG_UNION, error_case_eq, known_def] >>
      rpt strip_tac >> rveq >> fs[] >>
      rpt (pairarg_tac >> fs[]) >> rveq >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      map_every qcase_tac [`known _ (_ :: _) g1 = (_, g)`,
                           `known _ _ g0 = (_, g1)`,
                           `subspt g gg`] >>
      patresolve `known _ _ g0 = _` hd subspt_known_elist_globals >> simp[] >>
      rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
      first_x_assum (patresolve `state_globals_approx _ _`  (el 6)) >> simp[] >>
      rpt (disch_then (resolve_selected last) >> simp[]) >>
      (impl_keep_tac >- metis_tac[subspt_trans]) >> rw[] >>
      simp[evaluate_def, pair_case_eq, result_case_eq, error_case_eq]
      >- (dsimp[] >> fs[PULL_EXISTS] >> sel_ihpc last >> simp[] >>
          fs[krrel_err_rw] >> disch_then irule >> simp[]
          >- metis_tac[ssgc_free_preserved_SING']
          >- first_assum
               (fn th =>
                    mp_tac (asmPART_MATCH' last ssgc_evaluate (concl th)) >>
                    simp[] >> NO_TAC)
          >- (patresolve `known _ _ g0 = _` hd (GEN_ALL kca_sing_sga) >>
              simp[] >> disch_then (resolve_selected last) >> simp[] >>
              metis_tac[ksrel_ssgc_free,kvrel_EVERY_vsgc_free,ksrel_sga,
                        kvrel_LIST_REL_val_approx]))
      >- (fs[krrel_err_rw, result_case_eq, error_case_eq] >> dsimp[] >>
          metis_tac[pair_CASES, result_CASES, error_CASES]))
  >- (say "op" >>
      simp[evaluate_def, pair_case_eq, result_case_eq, known_def,
           BAG_ALL_DISTINCT_BAG_UNION] >>
      rpt strip_tac >> rveq >> fs[] >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      dsimp[evaluate_def, result_case_eq, pair_case_eq] >>
      sel_ihpc last >> simp[PULL_EXISTS] >>
      rpt (disch_then (resolve_selected last) >> simp[]) >>
      resolve_selected hd subspt_known_op_elist_globals >> simp[] >>
      rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
      (impl_keep_tac >- metis_tac[subspt_trans]) >> rw[] >> simp[]
      >- ((* args evaluate OK, do_app evaluates OK *)
          metis_tac[kvrel_op_correct_Rval, EVERY2_REVERSE])
      >- ((* args evaluate OK, do_app errors *)
          imp_res_tac do_app_EQ_Rerr >> rw[] >>
          metis_tac[result_CASES, pair_CASES])
      >- ((* args error *) fs[krrel_err_rw] >>
         metis_tac[result_CASES, pair_CASES]))
  >- (say "fn" >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           known_def, bool_case_eq, eqs] >> rpt strip_tac >> rveq >> fs[] >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      dsimp[evaluate_def, eqs] >> imp_res_tac known_sing_EQ_E >> rveq >> fs[] >>
      rveq
      >- (simp[kerel_def, PULL_EXISTS] >> metis_tac[kvrel_LIST_REL_val_approx])
      >- metis_tac[option_CASES]
      >- (resolve_selected last (GEN_ALL kvrel_lookup_vars) >> simp[] >>
          disch_then (resolve_selected hd) >> simp[] >> strip_tac
          simp[kerel_def] >> cheat))
          (* need to show that val_approx works on lookup_vars output *)
  >- (say "letrec" >> cheat)
  >- (say "app" >>
      rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           bool_case_eq, known_def] >> rpt strip_tac >> rveq >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      map_every imp_res_tac [known_sing_EQ_E, evaluate_SING] >> rveq >> fs[] >>
      rveq
      >- (qhdtm_assum `state_globals_approx` (fn th => first_x_assum(fn impth =>
            mp_tac (asmPART_MATCH' (el 5) impth (concl th)))) >> simp[] >>
          rpt (disch_then (fn impth => first_assum (fn th =>
                 mp_tac (asmPART_MATCH' last impth (concl th)))) >> simp[]) >>
          impl_keep_tac
          >- metis_tac[known_better_definedg, better_definedg_trans] >>
          rw[] >> simp[evaluate_def] >> imp_res_tac known_LENGTH_EQ_E >>
          fs[] >> simp[pair_case_eq, result_case_eq, PULL_EXISTS] >>
          sel_ihpc last >> simp[] >> strip_tac >> sel_ihpc (el 3) >> simp[] >>
          strip_tac >> sel_ihpc hd >> simp[PULL_EXISTS] >>
          map_every qcase_tac [
            `known [exp1] apxs g1 = ([(exp2,apx2)], g)`,
            `known exps1 apxs g0 = (alist2,g1)`,
            `evaluate ([exp1],env1,s11) = (Rval [v1],s21)`,
            `evaluate (MAP FST alist2,env2,s02) = (Rval vs2,s12)`,
            `evaluate (exps1,env1,s01) = (Rval vs1,s11)`
          ] >>
          qspecl_then [`exps1`, `apxs`, `g0`, `alist2`, `g1`]
             mp_tac known_correct_approx >> simp[] >>
          disch_then (qspecl_then [`env2`, `s02`, `s12`, `Rval vs2`]
                                  mp_tac) >> simp[] >>
          impl_tac
          >- metis_tac[kvrel_LIST_REL_val_approx, ksrel_sga,
                       ksrel_ssgc_free, kvrel_EVERY_vsgc_free] >>
          strip_tac >>
          qspecl_then [`exps1`, `env1`, `s01`, `Rval vs1`, `s11`]
            mp_tac ssgc_evaluate >> simp[] >>
          disch_then (CONJUNCTS_THEN2 assume_tac
                                      (CONJUNCTS_THEN2 assume_tac kall_tac)) >>
          impl_tac >- metis_tac[ksrel_sga] >>
          strip_tac >>
          qcase_tac `evaluate([exp2],env2,s12) = (Rval [v2],s22)` >> simp[] >>
          qcase_tac `evaluate_app loption1 v1 vs1 s21` >>
          `ssgc_free s21`
             by metis_tac[ksrel_ssgc_free, ssgc_free_preserved_SING'] >> fs[] >>
          reverse (Cases_on `loption1`) >> simp[]
          >- (first_x_assum irule >> simp[loptrel_def]) >>
          Cases_on `dest_Clos apx2` >> simp[]
          >- (first_x_assum irule >> simp[loptrel_def]) >>
          qcase_tac `dest_Clos apx2 = SOME closapxvalue` >>
          `∃clloc clarity. closapxvalue = (clloc, clarity)`
            by metis_tac[pair_CASES] >> pop_assum SUBST_ALL_TAC >>
          simp[] >> reverse (Cases_on `clarity = LENGTH exps1`) >> simp[]
          >- (first_x_assum irule >> simp[loptrel_def]) >>
          first_x_assum irule >> simp[loptrel_def] >>
          qspecl_then [`[exp1]`, `apxs`, `g1`, `[(exp2,apx2)]`, `g`]
             mp_tac known_correct_approx >> simp[] >>
          disch_then (qspecl_then [`env2`, `s12`, `s22`, `Rval [v2]`] mp_tac) >>
          simp[] >> impl_tac
          >- metis_tac[kvrel_LIST_REL_val_approx, ksrel_ssgc_free,
                       kvrel_EVERY_vsgc_free] >>
          fs[dest_Clos_eq_SOME] >> rveq >> rw[] >> simp[] >>
          metis_tac[evaluate_length_imp])
      >- (qhdtm_assum `state_globals_approx` (fn th => first_x_assum(fn impth =>
            mp_tac (asmPART_MATCH' (el 5) impth (concl th)))) >> simp[] >>
          rpt (disch_then (fn impth => first_assum (fn th =>
                 mp_tac (asmPART_MATCH' last impth (concl th)))) >> simp[]) >>
          impl_keep_tac
          >- metis_tac[known_better_definedg, better_definedg_trans] >>
          rw[] >> simp[evaluate_def] >> imp_res_tac known_LENGTH_EQ_E >>
          fs[] >> simp[pair_case_eq, result_case_eq, PULL_EXISTS] >>
          sel_ihpc last >> simp[] >> strip_tac >> sel_ihpc (el 3) >> simp[] >>
          strip_tac >> sel_ihpc hd >> simp[PULL_EXISTS] >>
          reverse impl_tac
          >- (rw[] >> simp[] >> fs[krrel_err_rw] >> dsimp[] >>
              metis_tac[pair_CASES, result_CASES]) >>
          map_every qcase_tac [
             `state_globals_approx s01 g0`,
             `evaluate(args1,env1,s01) = (Rval vs1, s11)`,
             `evaluate([exp1],env1,s11) = (Rerr err1, s21)`,
             `evaluate(MAP FST alist,env2,s02) = (Rval vs2,s12)`,
             `known [exp1] apxs g1 = ([(exp2,apx)], g)`] >>
          qspecl_then [`args1`, `apxs`, `g0`, `alist`, `g1`] mp_tac
                      known_correct_approx >> simp[] >>
          disch_then
            (qspecl_then [`env2`, `s02`, `s12`, `Rval vs2`] mp_tac) >>
          simp[] >> impl_tac
          >- metis_tac[kvrel_EVERY_vsgc_free, kvrel_LIST_REL_val_approx,
                       ksrel_ssgc_free, ksrel_sga] >>
          metis_tac[ksrel_sga, ssgc_evaluate,
                    known_better_definedg,
                    kvrel_LIST_REL_better_definedg])
      >- (qhdtm_assum `state_globals_approx` (fn th => first_x_assum(fn impth =>
            mp_tac (asmPART_MATCH' (el 5) impth (concl th)))) >> simp[] >>
          rpt (disch_then (fn impth => first_assum (fn th =>
                 mp_tac (asmPART_MATCH' last impth (concl th)))) >> simp[]) >>
          impl_keep_tac
          >- metis_tac[known_better_definedg, better_definedg_trans] >> rw[] >>
          simp[evaluate_def, bool_case_eq, result_case_eq, pair_case_eq] >>
          imp_res_tac known_LENGTH_EQ_E >> rveq >> fs[] >>
          fs[krrel_err_rw] >> dsimp[] >>
          metis_tac[result_CASES,pair_CASES])
      >- (map_every imp_res_tac [evaluate_IMP_LENGTH, known_LENGTH_EQ_E] >>
          fs[] >> rw[] >> simp[evaluate_def]))
  >- (say "tick" >> simp[dec_clock_def] >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, bool_case_eq, known_def] >>
      qcase_tac `(s0:α closSem$state).clock = 0` >> Cases_on `s0.clock = 0` >>
      fs[] >> rpt strip_tac >> rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      simp[evaluate_def] >- (fs[ksrel_def] >> (* easy *) cheat) >>
      fs[dec_clock_def] >> fixeqs >> imp_res_tac known_sing_EQ_E >> rveq >>
      fs[] >> rveq >>
      map_every qcase_tac [
        `known [exp1] apxs g0 = ([(exp2,apx)],g)`,
        `evaluate([exp1],env1,s01 with clock := s01.clock - 1) = (res1,s1)`,
        `ksrel g0 s01 s02`] >>
      sel_ihpc last >> simp[] >>
      disch_then
        (qspecl_then [`env2`, `s02 with clock := s02.clock - 1`] mp_tac) >>
      simp[] >> impl_keep_tac >- fs[ksrel_def] >>
      `s02.clock = s01.clock` by fs[ksrel_def] >> simp[])
  >- (say "call" >>
      simp[evaluate_def, pair_case_eq, result_case_eq, eqs, bool_case_eq,
           known_def] >> rw[]
      >- (simp[] >> metis_tac[pair_CASES])
      >- (rpt (pairarg_tac >> fs[]) >> rveq >> nailIHx strip_assume_tac >>
          simp[evaluate_def] >> rw[] >>
          imp_res_tac ksrel_find_code >> fs[])
      >- (fixeqs >> rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
          nailIHx strip_assume_tac >>
          imp_res_tac ksrel_find_code >> fs[])
      >- (rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
          nailIHx strip_assume_tac >> simp[evaluate_def] >>
          fs[krrel_err_rw] >>
          dsimp[result_case_eq, eqs, pair_case_eq, bool_case_eq] >>
          metis_tac[option_CASES, pair_CASES, result_CASES]))
  >- (say "evaluate_app(nil)" >> simp[evaluate_def])
  >- (say "evaluate_app(cons)" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, eqs, bool_case_eq, pair_case_eq, result_case_eq] >>
      rpt strip_tac >> rveq >> fs[]
      >- metis_tac[pair_CASES]
      >- (simp[evaluate_def, eqs, bool_case_eq] >>
          first_assum
            (mp_tac o
             asmPART_MATCH' hd (GEN_ALL kvrel_dest_closure_SOME_Partial) o
             concl) >> simp[PULL_EXISTS] >> strip_tac >>
          sel_ihpc hd >> simp[] >> strip_tac >> sel_ihpc hd >> simp[] >>
          strip_tac >> sel_ihpc hd >> imp_res_tac LIST_REL_LENGTH >>
          strip_tac >> fs[] >> nailIHx strip_assume_tac >> simp[] >>
          fs[ksrel_def])
      >- (simp[evaluate_def, eqs, bool_case_eq] >>
          first_assum
            (mp_tac o
             asmPART_MATCH' hd (GEN_ALL kvrel_dest_closure_SOME_Partial) o
             concl) >> simp[PULL_EXISTS] >> strip_tac >>
          sel_ihpc (el 3) >> simp[] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          strip_tac >> nailIHx strip_assume_tac >> simp[] >>
          fs[ksrel_def, dec_clock_def])
      >- (simp[evaluate_def, eqs, bool_case_eq] >>
          first_assum
            (mp_tac o
             asmPART_MATCH' hd (GEN_ALL kvrel_dest_closure_SOME_Full) o
             concl) >> simp[PULL_EXISTS] >> strip_tac >>
          sel_ihpc (el 3) >> simp[] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          strip_tac >> nailIHx strip_assume_tac >> simp[] >>
          `s02.clock = s01.clock` by fs[ksrel_def] >>
          imp_res_tac LIST_REL_LENGTH >> fs[] >>
          fs[ksrel_def])
      >- (simp[evaluate_def, eqs, bool_case_eq, pair_case_eq] >>
          first_assum
            (mp_tac o
             asmPART_MATCH' hd (GEN_ALL kvrel_dest_closure_SOME_Full) o
             concl) >> simp[PULL_EXISTS] >> strip_tac >>
          sel_ihpc (el 3) >> simp[] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          strip_tac >> nailIHx strip_assume_tac >> simp[] >>
          `s02.clock = s01.clock` by fs[ksrel_def] >>
          imp_res_tac LIST_REL_LENGTH >> fs[] >> simp[PULL_EXISTS] >>
          dsimp[] >> fs[PULL_EXISTS] >>
          map_every qcase_tac [
            `evaluate([exp1],env1,dec_clock _ s01) = (Rval [v1], s11)`,
            `kerel envapx gg exp1 exp2`] >> fs[kerel_def] >>
          rpt disj1_tac >> sel_ihpc last >> simp[] >>


cheat)
      >- (imp_res_tac evaluate_SING >> fs[])
      >- cheat))

val known_correct = save_thm(
  "known_correct",
  known_correct0 |> SIMP_RULE (srw_ss()) []);
*)
val _ = export_theory();
