open preamble backendPropsTheory
open closPropsTheory clos_knownTheory clos_knownPropsTheory closSemTheory
open bagTheory
open mp_then
open closLangTheory

val _ = new_theory "clos_knownProof";

fun patresolve p f th = Q.PAT_ASSUM p (mp_then (Pos f) mp_tac th)
fun say0 pfx s g = (print (pfx ^ ": " ^ s ^ "\n"); ALL_TAC g)

(* repeated resolution, requiring that all preconditions get removed *)
fun nailIHx k =
  first_x_assum
    (REPEAT_GTCL
       (fn ttcl => fn th => first_assum (mp_then (Pos hd) ttcl th))
       (k o assert (not o is_imp o #2 o strip_forall o concl)) o
     assert (is_imp o #2 o strip_forall o concl))

(* fixeqs flips any equations in the assumption that have evaluate on the rhs *)
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


val va_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of ``:val_approx``,
                      nchotomy = TypeBase.nchotomy_of ``:val_approx``}

val inlD_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of ``:inliningDecision``,
                      nchotomy = TypeBase.nchotomy_of ``:inliningDecision``}

val result_ty = ``:(α,β)semanticPrimitives$result``
val result_CASES = TypeBase.nchotomy_of result_ty
val result_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of result_ty,
                      nchotomy = result_CASES}

(*
val error_ty = ``:α semanticPrimitives$error_result``
val error_CASES = TypeBase.nchotomy_of error_ty
val error_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of error_ty,
                      nchotomy = error_CASES}
*)

(* simple properties of constants from clos_known: i.e., merge and known *)

val known_op_changed_globals = Q.store_thm(
  "known_op_changed_globals",
  `!opn aenv g0 a g.
     known_op opn aenv g0 = (a, g) ==>
     !i. i ∈ domain g /\ (i ∈ domain g0 ==> lookup i g <> lookup i g0) ==>
         i ∈ SET_OF_BAG (op_gbag opn)`,
  rpt gen_tac \\ Cases_on `opn`
  \\ simp [known_op_def, case_eq_thms, op_gbag_def,
           pair_case_eq, bool_case_eq, va_case_eq]
  \\ rw []
  \\ fs [lookup_insert, bool_case_eq])

val known_changed_globals = Q.store_thm(
  "known_changed_globals",
  `!c xs aenv g0 alist g.
     known c xs aenv g0 = (alist, g) ==>
     !i. i ∈ domain g ∧ (i ∈ domain g0 ==> lookup i g <> lookup i g0) ==>
         i ∈ SET_OF_BAG (elist_globals xs)`,
  ho_match_mp_tac known_ind \\ simp [known_def] \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  THEN1 metis_tac []
  THEN1 metis_tac []
  THEN1 metis_tac []
  THEN1 metis_tac []
  THEN1
   (rename1 `known _ xs aenv g0 = (ee1, g1)`
    \\ imp_res_tac known_op_changed_globals
    \\ Cases_on `i ∈ domain g1` \\ fs[]
    \\ Cases_on `i ∈ domain g0` \\ fs[]
    \\ Cases_on `lookup i g1 = lookup i g0` \\ fs[])
  \\ fs [inlD_case_eq, bool_case_eq]
  \\ rpt (pairarg_tac  \\ fs []) \\ rveq
  \\ metis_tac []);

val known_unchanged_globals = Q.store_thm(
  "known_unchanged_globals",
  `!c xs aenv g0 eas1 g1.
     known c xs aenv g0 = (eas1, g1) /\
     elist_globals xs = {||} ==> g0 = g1`,
  ho_match_mp_tac known_ind
  \\ simp [known_def]
  \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  THEN1 (Cases_on `op`
         \\ fs [known_op_def, bool_case_eq,
                case_eq_thms, va_case_eq, op_gbag_def])
  THEN1 (fs [inlD_case_eq, bool_case_eq]
         \\ rpt (pairarg_tac \\ fs [])));

(* Take first n expressions returned by the compile oracle. *)
val first_n_exps_def = Define `
  first_n_exps co n = GENLIST (FST o SND o co) n`;

val first_n_exps_shift_seq = Q.store_thm("first_n_exps_shift_seq",
  `!co n k. first_n_exps co (n + k) = first_n_exps co k ++ first_n_exps (shift_seq k co) n`,
  Induct_on `n`
  \\ rpt strip_tac
  \\ fs [first_n_exps_def]
  \\ REWRITE_TAC [Q.prove (`k + SUC n = SUC (k + n)`, decide_tac)]
  \\ fs [GENLIST]
  \\ fs [shift_seq_def])

(* All globals set in the program and in code returned by
   the compile oracle are unique. *)
val unique_set_globals_def = Define `
  unique_set_globals es co <=>
    !n. BAG_ALL_DISTINCT (elist_globals (es ++ first_n_exps co n))`;

val unique_set_globals_shift_seq = Q.store_thm(
  "unique_set_globals_shift_seq",
  `!es co k. unique_set_globals es co ==> unique_set_globals es (shift_seq k co)`,
  fs [unique_set_globals_def]
  \\ rpt strip_tac
  \\ pop_assum (qspec_then `n + k` assume_tac)
  \\ fs [first_n_exps_shift_seq]
  \\ fs [elist_globals_append]
  \\ fs [BAG_ALL_DISTINCT_BAG_UNION]);

val unique_set_globals_evaluate = Q.store_thm(
  "unique_set_globals_evaluate",
  `!es xs env s1 s2 res. unique_set_globals xs s1.compile_oracle /\
   evaluate (es,env,s1) = (res, s2) ==> unique_set_globals xs s2.compile_oracle`,
  rpt strip_tac \\ imp_res_tac evaluate_code \\ fs []
  \\ simp [unique_set_globals_shift_seq]);

(* Compile oracle globals are disjoint from given map. *)
val co_disjoint_globals_def = Define `
  co_disjoint_globals g co =
    !n. DISJOINT (domain g) (SET_OF_BAG (set_globals (FST (SND (co n)))))`;

val co_disjoint_globals_shift_seq = Q.store_thm(
  "co_disjoint_globals_shift_seq",
  `co_disjoint_globals g co ==>
   co_disjoint_globals g (shift_seq k co)`,
  fs [co_disjoint_globals_def, shift_seq_def]);

val co_disjoint_globals_evaluate = Q.store_thm(
  "co_disjoint_globals_evaluate",
  `!g s0 es env res s1.
     co_disjoint_globals g s0.compile_oracle /\
     evaluate (es, env, s0) = (res, s1) ==>
     co_disjoint_globals g s1.compile_oracle`,
  rw [] \\ imp_res_tac evaluate_code \\ simp [co_disjoint_globals_shift_seq]);

val co_disjoint_globals_first_n_exps = Q.store_thm(
  "co_disjoint_globals_first_n_exps",
  `!g co. co_disjoint_globals g co ==>
     !n. DISJOINT (domain g) (SET_OF_BAG (elist_globals (first_n_exps co n)))`,
  rpt gen_tac
  \\ simp [first_n_exps_def, co_disjoint_globals_def]
  \\ strip_tac
  \\ Induct \\ simp []
  \\ simp [GENLIST, SNOC_APPEND, elist_globals_append,
           SET_OF_BAG_UNION]
  \\ simp [DISJOINT_SYM]);

val direct_subexp_def = Define `
  (direct_subexp es [] <=> es = []) /\
  (direct_subexp es (x1::x2::xs) <=> es = [x1] \/ es = (x2::xs)) /\
  (direct_subexp es [Var t n] <=> F) /\
  (direct_subexp es [If t x1 x2 x3] <=> es = [x1] \/ es = [x2] \/ es = [x3]) /\
  (direct_subexp es [Let t xs x1] <=> es = xs \/ es = [x1]) /\
  (direct_subexp es [Raise t x1] <=> es = [x1]) /\
  (direct_subexp es [Handle t x1 x2] <=> es = [x1] \/ es = [x2]) /\
  (direct_subexp es [Op t opn xs] <=> es = xs) /\
  (direct_subexp es [Fn t loc_opt vsopt num_args x1] <=> es = [x1]) /\
  (direct_subexp es [Letrec t loc_opt vsopt fns x1] <=> es = (MAP SND fns) \/ es = [x1]) /\
  (direct_subexp es [App t loc_opt x1 xs] <=> es = [x1] \/ es = xs) /\
  (direct_subexp es [Tick t x1] <=> es = [x1]) /\
  (direct_subexp es [Call t ticks dest xs] <=> es = xs)`;

val direct_subexp_def = save_thm(
  "direct_subexp_def[simp]",
  direct_subexp_def |> SIMP_RULE (srw_ss()) []);

val BAG_DISJOINT_SYM = Q.prove(
  `!b1 b2. BAG_DISJOINT b1 b2 <=> BAG_DISJOINT b2 b1`,
  simp [BAG_DISJOINT, DISJOINT_SYM]);

val unique_set_globals_subexps = Q.store_thm("unique_set_globals_subexps",
 `(unique_set_globals (x1::x2::xs) co ==>
     unique_set_globals [x1] co /\ unique_set_globals (x2::xs) co) /\
  (unique_set_globals [If t x1 x2 x3] co ==>
     unique_set_globals [x1] co /\ unique_set_globals [x2] co /\ unique_set_globals [x3] co) /\
  (unique_set_globals [Let t xs x2] co ==>
     unique_set_globals xs co /\ unique_set_globals [x2] co) /\
  (unique_set_globals [Raise t x1] co ==>
     unique_set_globals [x1] co) /\
  (unique_set_globals [Handle t x1 x2] co ==>
     unique_set_globals [x1] co /\ unique_set_globals [x2] co) /\
  (unique_set_globals [Op t opn xs] co ==>
     unique_set_globals xs co) /\
  (unique_set_globals [Fn t loc_opt vsopt num_args x1] co ==>
     unique_set_globals [x1] co) /\
  (unique_set_globals [Letrec t loc_opt vsopt fns x1] co ==>
     unique_set_globals [x1] co /\ unique_set_globals (MAP SND fns) co) /\
  (unique_set_globals [App t loc_opt x1 xs] co ==>
     unique_set_globals [x1] co /\ unique_set_globals xs co) /\
  (unique_set_globals [Tick t x1] co ==>
     unique_set_globals [x1] co) /\
  (unique_set_globals [Call t ticks dest xs] co ==>
     unique_set_globals xs co)`,
  rpt strip_tac
  \\ fs [unique_set_globals_def]
  \\ fs [elist_globals_append]
  \\ fs [BAG_ALL_DISTINCT_BAG_UNION]);

val unique_set_globals_subexps = GEN_ALL unique_set_globals_subexps;

val unique_set_globals_IMP_es_distinct_elist_globals = Q.store_thm(
  "unique_set_globals_IMP_es_distinct_elist_globals",
  `!es co. unique_set_globals es co ==> BAG_ALL_DISTINCT (elist_globals es)`,
  simp [unique_set_globals_def, elist_globals_append, BAG_ALL_DISTINCT_BAG_UNION]);

(* State globals agree with the approximated globals. *)
val state_globals_approx_def = Define `
  state_globals_approx s g ⇔
    ∀k v.
      get_global k s.globals = SOME (SOME v) ⇒
      !a. lookup k g = SOME a ==> val_approx_val a v`;

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

val state_globals_approx_codeupd = Q.store_thm(
  "state_globals_approx_codeupd[simp]",
  `state_globals_approx (s with code updated_by f) g ⇔
   state_globals_approx s g`,
  simp[state_globals_approx_def]);

val state_globals_approx_coupd = Q.store_thm(
  "state_globals_approx_coupd[simp]",
  `state_globals_approx (s with compile_oracle updated_by f) g ⇔
   state_globals_approx s g`,
  simp[state_globals_approx_def]);


(* Mapped globals *)

val mapped_globals_def = Define`
  mapped_globals (s:('c,'ffi) closSem$state) =
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
  simp[mapped_globals_def, dec_clock_def]);

val mapped_globals_codeupdate = Q.store_thm(
  "mapped_globals_codeupdate[simp]",
  `mapped_globals (s with code updated_by f) g = mapped_globals s g`,
  simp[mapped_globals_def]);

val mapped_globals_coupdate = Q.store_thm(
  "mapped_globals_coupdate[simp]",
  `mapped_globals (s with compile_oracle updated_by f) g = mapped_globals s g`,
  simp[mapped_globals_def]);

(* Extending mapped globals *)

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
  `!s0 s1 s2 g1 g2. mglobals_extend s0 g1 s1 ∧ mglobals_extend s1 g2 s2 ⇒
   mglobals_extend s0 (g1 ∪ g2) s2`,
  simp[mglobals_extend_def, SUBSET_DEF] >> metis_tac[]);

val mglobals_extend_SUBSET = Q.store_thm(
  "mglobals_extend_SUBSET",
  `!s0 s g1 g2. mglobals_extend s0 g1 s ∧ g1 ⊆ g2 ⇒ mglobals_extend s0 g2 s`,
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

val mapped_globals_codeupdate = Q.store_thm(
  "mglobals_extend_codeupdate[simp]",
  `(mglobals_extend s0 gs (s with code updated_by f) ⇔
      mglobals_extend s0 gs s) /\
   (mglobals_extend (s0 with code updated_by f) gs s ⇔
      mglobals_extend s0 gs s)`,
  simp[mglobals_extend_def,mapped_globals_def]);

val mglobals_extend_co_update = Q.store_thm(
  "mglobals_extend_co_update[simp]",
  `(mglobals_extend s0 gs (s with compile_oracle updated_by f) ⇔
      mglobals_extend s0 gs s) /\
   (mglobals_extend (s0 with compile_oracle updated_by f) gs s ⇔
      mglobals_extend s0 gs s)`,
  simp[mglobals_extend_def,mapped_globals_def]);


val subspt_better_definedg = Q.store_thm(
  "subspt_better_definedg",
  `!sp1 sp2 sp3. subspt sp1 sp3 ∧ better_definedg sp1 sp2 ∧ better_definedg sp2 sp3 ⇒
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
  `∀c es1 as1 g0 al1 g1 es2 as2 al2 g2.
     known c es1 as1 g0 = (al1, g1) ∧ known c es2 as2 g1 = (al2, g2) ∧
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
  `∀c es as1 g0 al1 g1 opn as2 g2 a.
      known c es as1 g0 = (al1,g1) ∧ known_op opn as2 g1 = (a,g2) ∧ subspt g0 g2 ∧
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

val known_op_correct_approx = Q.store_thm("known_op_correct_approx",
  `!opn args g0 a g vs s0 g' v s.
   known_op opn args g0 = (a,g) ∧ LIST_REL val_approx_val args vs ∧
   state_globals_approx s0 g' ∧ subspt g g' /\
   do_app opn vs s0 = Rval (v, s) ⇒
   state_globals_approx s g' ∧ val_approx_val a v`,
  rpt gen_tac
  \\ `?this_is_case. this_is_case opn` by (qexists_tac `K T` \\ fs [])
  \\ Cases_on `opn`
  \\ simp [known_op_def, do_app_def, case_eq_thms, va_case_eq, bool_case_eq,
           pair_case_eq]
  \\ rpt strip_tac \\ rveq \\ fs[]
  THEN1
   (fs [state_globals_approx_def] \\ res_tac
    \\ metis_tac [SOME_11, subspt_lookup])
  THEN1
   (fs [subspt_lookup, lookup_insert]
    \\ fs [state_globals_approx_def] \\ rw []
    \\ fs [get_global_def, EL_LUPDATE, bool_case_eq] \\ rveq \\ fs []
    THEN1 (first_x_assum (qspecl_then [`k`, `a'`] assume_tac) \\ fs [])
    THEN1 metis_tac [])
  THEN1
   (fs [subspt_lookup, lookup_insert]
    \\ fs [state_globals_approx_def] \\ rw []
    \\ fs [get_global_def, EL_LUPDATE, bool_case_eq] \\ rveq \\ fs []
    THEN1 (first_x_assum (qspecl_then [`k`, `merge other a'`] assume_tac)
           \\ fs [] \\ metis_tac [val_approx_val_merge_I])
    THEN1 metis_tac [])
  THEN1
   (fs [state_globals_approx_def, get_global_def,
        EL_APPEND_EQN, bool_case_eq]
    \\ rw [] THEN1 (metis_tac [])
    \\ rename1 `nn - LENGTH (ss:('a,'b) closSem$state).globals`
    \\ `nn = LENGTH ss.globals` by simp [] \\ fs [])
  THEN1
   (rveq \\ fs [LIST_REL_EL_EQN]));

val ssgc_free_co_shift_seq = Q.store_thm(
  "ssgc_free_co_shift_seq",
  `ssgc_free s ==> ssgc_free (s with compile_oracle := shift_seq k s.compile_oracle)`,
  simp [ssgc_free_def] \\ strip_tac \\ rpt conj_tac \\ fs []
  \\ rpt gen_tac \\ strip_tac \\ fs [shift_seq_def] \\ res_tac \\ simp []);

val shift_seq_zero = Q.store_thm(
  "shift_seq_zero[simp]",
  `!co. shift_seq 0 co = co`,
  simp [shift_seq_def, ETA_THM]);

val shift_seq_add = Q.store_thm(
  "shift_seq_add[simp]",
  `!co k1 k2. shift_seq k2 (shift_seq k1 co) = shift_seq (k1 + k2) co`,
  simp [shift_seq_def]);

val ssgc_free_do_install = Q.store_thm(
  "ssgc_free_do_install",
  `!s. ssgc_free s ==>
   ssgc_free (s with <|compile_oracle := shift_seq 1 (s.compile_oracle);
                       code := s.code |++ SND (SND (s.compile_oracle 0))|>)`,
  gen_tac \\ simp [ssgc_free_def] \\ strip_tac \\ rpt conj_tac
  THEN1 (`?exp aux. SND (s.compile_oracle 0) = (exp, aux)`
           by (Cases_on `SND (s.compile_oracle 0)` \\ simp [])
         \\ res_tac \\ simp []
         \\ rpt strip_tac
         \\ fs [flookup_fupdate_list]
         \\ fs [case_eq_thms] THEN1 res_tac
         \\ imp_res_tac ALOOKUP_MEM
         \\ fs [MEM_REVERSE]
         \\ fs [MEM_SPLIT]
         \\ rveq
         \\ fs [MAP_APPEND, elist_globals_append])
  THEN1 (rw [] \\ res_tac)
  THEN1 (simp [shift_seq_def] \\ rw [] \\ res_tac));

val do_install_ssgc = Q.store_thm(
  "do_install_ssgc",
  `!vs s0 e s1. do_install vs s0 = (Rval e, s1) /\ ssgc_free s0 ==>
   ssgc_free s1 /\ esgc_free e /\
   s1.compile_oracle = shift_seq 1 s0.compile_oracle /\
   first_n_exps s0.compile_oracle 1 = [e] /\
   mglobals_extend s0 (SET_OF_BAG (set_globals e)) s1`,
   rpt gen_tac \\ strip_tac
   \\ fs [do_install_def, case_eq_thms]
   \\ pairarg_tac \\ fs []
   \\ fs [case_eq_thms, bool_case_eq, pair_case_eq]
   \\ rveq
   \\ simp [first_n_exps_def]
   \\ imp_res_tac ssgc_free_do_install \\ rfs []
   \\ pop_assum kall_tac
   \\ fs [ssgc_free_def]
   \\ Cases_on `SND (s0.compile_oracle 0)`
   \\ res_tac \\ rfs []);

val value_ind =
  TypeBase.induction_of ``:closSem$v``
   |> Q.SPECL [`P`, `EVERY P`]
   |> SIMP_RULE (srw_ss()) []
   |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> Q.GEN `P`

(* TODO closProps? *)
val list_to_v_EVERY_APPEND = Q.store_thm("list_to_v_EVERY_APPEND",
  `!(x: closSem$v) y xs ys.
     v_to_list x = SOME xs /\
     v_to_list y = SOME ys /\
     (!t l. P (Block t l) <=> EVERY P l) /\
     P x /\ P y ==>
       P (list_to_v (xs ++ ys))`,
  ho_match_mp_tac v_to_list_ind \\ rw [v_to_list_def, case_eq_thms] \\ fs []
  >-
   (qpat_x_assum `v_to_list _ = _` mp_tac
    \\ pop_assum mp_tac
    \\ ConseqConv.SPEC_ALL_TAC
    \\ ho_match_mp_tac v_to_list_ind
    \\ rw [v_to_list_def, case_eq_thms]
    \\ fs [list_to_v_def])
  \\ rfs []
  \\ res_tac
  \\ fs [list_to_v_def])

val do_app_ssgc = Q.store_thm(
  "do_app_ssgc",
  `!opn args s0 res.
     do_app opn args s0 = res /\
     EVERY vsgc_free args /\ ssgc_free s0 ==>
     (!v s. res = Rval (v, s) ==>
            vsgc_free v /\ ssgc_free s /\
            s.compile_oracle = s0.compile_oracle /\
            mglobals_extend s0 (SET_OF_BAG (op_gbag opn)) s) /\
     (!v. res = Rerr (Rraise v) ==> vsgc_free v)`,
  gen_tac >>
  `?this_is_case. this_is_case = opn` by metis_tac [] >>
  Cases_on `opn` >>
  simp[do_app_def, case_eq_thms, op_gbag_def, PULL_EXISTS, bool_case_eq,
       pair_case_eq]
  >- ((* GetGlobal *)
      simp[get_global_def, ssgc_free_def] >> metis_tac[MEM_EL])
  >- ((* SetGlobal *)
      simp[ssgc_free_def, mglobals_extend_def, mapped_globals_def] >>
      rpt strip_tac
      >- metis_tac[]
      >- metis_tac[]
      >- (fs[MEM_LUPDATE] >> metis_tac[MEM_EL])
      >- metis_tac[]
      >- metis_tac[]
      >- (dsimp[SUBSET_DEF, get_global_def,
                EL_LUPDATE, bool_case_eq] >> metis_tac[])
      >- (fs[get_global_def, EL_LUPDATE]))
  >- ((* AllocGlobal *)
      dsimp[ssgc_free_def, mglobals_extend_def, mapped_globals_def, SUBSET_DEF,
            get_global_def, EL_APPEND_EQN, bool_case_eq] >>
      reverse (rpt strip_tac)
      >- (rename1 `ii < LENGTH (ss:('a,'b) closSem$state).globals` >>
          Cases_on `ii < LENGTH ss.globals` >> simp[] >>
          Cases_on `ii - LENGTH ss.globals = 0`
          >- (pop_assum SUBST_ALL_TAC >> simp[]) >> simp[])
      >- (rename1 `nn < LENGTH (ss:('a,'b) closSem$state).globals` >>
          Cases_on `nn < LENGTH ss.globals` >> simp[] >>
          Cases_on `nn < LENGTH ss.globals + 1` >> simp[] >>
          `nn - LENGTH ss.globals = 0` by simp[] >> simp[]) >>
      metis_tac[])
  >- (
    dsimp [] >>
    rw [] >>
    irule EVERY_TAKE >>
    simp []
    >- intLib.ARITH_TAC >>
    irule EVERY_DROP >>
    simp []
    >- intLib.ARITH_TAC)
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
  >- (dsimp[ssgc_free_def,FLOOKUP_UPDATE,bool_case_eq] \\ rw[] \\ metis_tac[])
  >- ((* ListAppend *)
      rw [] \\ fs []
      \\ match_mp_tac list_to_v_EVERY_APPEND
      \\ simp [vsgc_free_def]
      \\ asm_exists_tac \\ fs []
      \\ asm_exists_tac \\ fs [])
  >- ((* FromList *)
      simp[PULL_FORALL] >> rpt gen_tac >> rename1 `v_to_list v = SOME vs` >>
      map_every qid_spec_tac [`vs`, `v`] >> ho_match_mp_tac value_ind >>
      simp[v_to_list_def] >> Cases >>
      simp[v_to_list_def] >>
      rename1 `closSem$Block _ (v1::vs)` >> Cases_on `vs` >>
      simp[v_to_list_def] >>
      rename1 `closSem$Block _ (v1::v2::vs)` >> Cases_on `vs` >>
      simp[v_to_list_def, case_eq_thms, PULL_EXISTS, PULL_FORALL])
  >- (dsimp[ssgc_free_def, FLOOKUP_UPDATE, bool_case_eq] >> metis_tac[])
  >- (dsimp[ssgc_free_def] >>
      metis_tac[MEM_EL, EVERY_MEM, integerTheory.INT_INJ,
                integerTheory.INT_OF_NUM, integerTheory.INT_LT])
  >- (dsimp[ssgc_free_def, FLOOKUP_UPDATE, bool_case_eq] >>
      rpt strip_tac
      >- metis_tac[]
      >- (irule IMP_EVERY_LUPDATE >> simp[] >> metis_tac[])
      >- metis_tac[]
      >- metis_tac[]
      >- metis_tac[])
  >- (dsimp[ssgc_free_def, FLOOKUP_UPDATE, bool_case_eq] >> metis_tac[])
  >> dsimp[]);

val EVERY_lookup_vars = Q.store_thm(
  "EVERY_lookup_vars",
  `∀vs env env'. EVERY P env ∧ lookup_vars vs env = SOME env' ⇒ EVERY P env'`,
  Induct >> simp[lookup_vars_def, case_eq_thms, PULL_EXISTS] >>
  metis_tac[MEM_EL, EVERY_MEM]);


val dest_closure_Full_sgc_free = Q.store_thm(
  "dest_closure_Full_sgc_free",
  `dest_closure max_app loc_opt f (arg1::args) =
     SOME (Full_app fbody env rest_args) /\
   vsgc_free f /\ vsgc_free arg1 /\ EVERY vsgc_free args ==>
   set_globals fbody = {||} /\ EVERY vsgc_free env /\ EVERY vsgc_free rest_args`,
   rpt gen_tac \\ strip_tac
   \\ imp_res_tac dest_closure_is_closure
   \\ imp_res_tac dest_closure_full_length
   \\ rename [`is_closure f`]
   \\ Cases_on `f` \\ fs [is_closure_def]
   \\ fs [dest_closure_def]
   THEN1 (rveq
          \\ simp [EVERY_REVERSE]
          \\ conj_tac
          THEN1 (irule EVERY_TAKE \\ simp [EVERY_REVERSE])
          THEN1 (irule EVERY_DROP \\ simp [EVERY_REVERSE]))
   \\ rpt (pairarg_tac \\ fs [])
   \\ rveq
   \\ rename [`EL n funs = _`]
   \\ qmatch_assum_abbrev_tac `EL n funs = funn`
   \\ `MEM funn funs` by (simp [MEM_EL] \\ qexists_tac `n` \\ simp [])
   \\ unabbrev_all_tac
   \\ fs [MEM_SPLIT] \\ fs [elist_globals_append]
   \\ simp [EVERY_REVERSE, EVERY_GENLIST, elist_globals_append]
   \\ conj_tac
   THEN1 (irule EVERY_TAKE \\ simp [EVERY_REVERSE])
   THEN1 (irule EVERY_DROP \\ simp [EVERY_REVERSE]));

val say = say0 "evaluate_changed_globals_0";

(* Evaluate  *)
val evaluate_changed_globals_0 = Q.prove(
  `(!es env (s0:('c,'ffi) closSem$state) res s.
      evaluate (es, env, s0) = (res, s) /\
      ssgc_free s0 /\ EVERY esgc_free es /\
      EVERY vsgc_free env ==>
        ssgc_free s /\ rsgc_free res /\
        ?n.
          s.compile_oracle = shift_seq n s0.compile_oracle /\
          mglobals_extend s0
            (SET_OF_BAG (elist_globals es) ∪
             SET_OF_BAG (elist_globals (first_n_exps s0.compile_oracle n))) s) /\
   (!loc_opt f args (s0:('c,'ffi) closSem$state) res s.
      evaluate_app loc_opt f args s0 = (res, s) /\
      ssgc_free s0 /\ vsgc_free f /\ EVERY vsgc_free args ==>
        ssgc_free s /\ rsgc_free res /\
        ?n.
          s.compile_oracle = shift_seq n s0.compile_oracle /\
          mglobals_extend s0
            (SET_OF_BAG (elist_globals (first_n_exps s0.compile_oracle n))) s)`,
  ho_match_mp_tac (evaluate_ind |> Q.SPEC `\(x1,x2,x3). P0 x1 x2 x3`
                   |> Q.GEN `P0` |> SIMP_RULE std_ss [FORALL_PROD])
  \\ rpt conj_tac \\ rpt (gen_tac ORELSE disch_then strip_assume_tac)
  THEN1
   (say "NIL"
    \\ fs [evaluate_def] \\ rveq \\ simp []
    \\ qexists_tac `0` \\ simp [])
  THEN1
   (say "CONS"
    \\ fs [evaluate_def, pair_case_eq]
    \\ reverse (fs [result_case_eq]) \\ rveq \\ fs []
    THEN1 (qexists_tac `n` \\ fs [SET_OF_BAG_UNION]
           \\ match_mp_tac mglobals_extend_SUBSET
           \\ goal_assum drule
           \\ simp [GSYM UNION_ASSOC])
    \\ reverse (fs [pair_case_eq, result_case_eq]) \\ rveq \\ fs []
    \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
    \\ qexists_tac `n' + n` \\ simp [first_n_exps_shift_seq]
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0 g1 s1`
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1 g2 s`
    \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0 g3 s`
    \\ `g3 = g1 ∪ g2` suffices_by metis_tac [mglobals_extend_trans]
    \\ fs [elist_globals_append, SET_OF_BAG_UNION]
    \\ unabbrev_all_tac \\ rpt (pop_assum kall_tac)
    \\ metis_tac [UNION_ASSOC, UNION_COMM])
  THEN1
   (say "Var"
    \\ fs [evaluate_def, bool_case_eq, EVERY_EL]
    \\ qexists_tac `0` \\ simp [])
  THEN1
   (say "If"
    \\ reverse (fs [evaluate_def, pair_case_eq, case_eq_thms])
    \\ rveq \\ fs []
    THEN1 (qexists_tac `n` \\ simp [SET_OF_BAG_UNION]
           \\ match_mp_tac mglobals_extend_SUBSET
           \\ goal_assum drule
           \\ metis_tac [UNION_ASSOC, UNION_COMM, SUBSET_UNION])
    \\ rename1 `Rval vs`
    \\ reverse (Cases_on `Boolv T = HD vs \/ (Boolv T <> HD vs /\ Boolv F = HD vs)`)
    THEN1 (fs [] \\ fs [] \\ rveq \\ fs []
           \\ qexists_tac `n` \\ simp [SET_OF_BAG_UNION]
           \\ match_mp_tac mglobals_extend_SUBSET
           \\ goal_assum drule
           \\ metis_tac [UNION_ASSOC, UNION_COMM, SUBSET_UNION])
    \\ fs [] \\ fs []
    \\ qexists_tac `n' + n`
    \\ simp [first_n_exps_shift_seq]
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0 g1 s1`
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1 g2 s`
    \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0 g3 s`
    \\ `g1 ∪ g2 ⊆ g3` suffices_by metis_tac [mglobals_extend_trans, mglobals_extend_SUBSET]
    \\ fs [elist_globals_append, SET_OF_BAG_UNION]
    \\ unabbrev_all_tac \\ rpt (pop_assum kall_tac)
    \\ metis_tac [UNION_ASSOC, UNION_COMM, SUBSET_UNION])
  THEN1
   (say "Let"
    \\ fs [evaluate_def, pair_case_eq, case_eq_thms]
    \\ rveq \\ fs []
    THEN1 (qexists_tac `n + n'` \\ simp [first_n_exps_shift_seq]
           \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0 g1 s1`
           \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1 g2 s`
           \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0 g3 s`
           \\ `g3 = g1 ∪ g2` suffices_by metis_tac [mglobals_extend_trans]
           \\ unabbrev_all_tac
           \\ simp [elist_globals_append, SET_OF_BAG_UNION]
           \\ metis_tac [UNION_ASSOC, UNION_COMM])
    THEN1 (qexists_tac `n` \\ simp [SET_OF_BAG_UNION]
           \\ match_mp_tac mglobals_extend_SUBSET
           \\ goal_assum drule
           \\ metis_tac [UNION_ASSOC, UNION_COMM, SUBSET_UNION]))
  THEN1
   (say "Raise"
    \\ fs [evaluate_def, pair_case_eq, case_eq_thms]
    \\ rveq \\ imp_res_tac evaluate_SING \\ fs [])
  THEN1
   (say "Handle"
    \\ fs [evaluate_def, pair_case_eq, case_eq_thms]
    \\ rveq \\ fs []
    \\ fs [SET_OF_BAG_UNION]
    THEN1 (qexists_tac `n` \\ simp []
           \\ match_mp_tac mglobals_extend_SUBSET
           \\ goal_assum drule
           \\ metis_tac [UNION_ASSOC, UNION_COMM, SUBSET_UNION])
    THEN1 (qexists_tac `n + n'` \\ simp [first_n_exps_shift_seq]
           \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0 g1 s1`
           \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1 g2 s`
           \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0 g3 s`
           \\ `g3 = g1 ∪ g2` suffices_by metis_tac [mglobals_extend_trans]
           \\ fs [elist_globals_append, SET_OF_BAG_UNION]
           \\ unabbrev_all_tac \\ rpt (pop_assum kall_tac)
           \\ metis_tac [UNION_ASSOC, UNION_COMM])
    THEN1 (qexists_tac `n` \\ simp []
           \\ match_mp_tac mglobals_extend_SUBSET
           \\ goal_assum drule
           \\ metis_tac [UNION_ASSOC, UNION_COMM, SUBSET_UNION]))
  THEN1
   (say "Op"
    \\ fs [evaluate_def]
    \\ reverse (fs [pair_case_eq, result_case_eq]) \\ rveq \\ fs []
    THEN1 (qexists_tac `n` \\ fs [SET_OF_BAG_UNION]
           \\ metis_tac [mglobals_extend_SUBSET, UNION_ASSOC, SUBSET_UNION])
    \\ rename1 `evaluate (_, _, s0) = (_, s1)`
    \\ Cases_on `op = Install` \\ fs []
    THEN1
     (reverse (fs [pair_case_eq, result_case_eq]) \\ rveq \\ fs []
      THEN1
       (fs [do_install_def, case_eq_thms, bool_case_eq] \\ rveq \\ fs []
        \\ TRY (qexists_tac `n` \\ fs [SET_OF_BAG_UNION]
                \\ metis_tac [mglobals_extend_SUBSET, UNION_ASSOC, SUBSET_UNION])
        \\ pairarg_tac \\ fs []
        \\ fs [case_eq_thms, bool_case_eq, pair_case_eq] \\ rveq \\ fs []
        \\ TRY (qexists_tac `n` \\ fs [SET_OF_BAG_UNION]
                \\ metis_tac [mglobals_extend_SUBSET, UNION_ASSOC, SUBSET_UNION])
        \\ conj_tac THEN1 (imp_res_tac ssgc_free_do_install \\ rfs [])
        \\ TRY (qexists_tac `n + 1`
                \\ fs [first_n_exps_def, GSYM ADD1, GENLIST,
                       SNOC_APPEND, elist_globals_append]
                \\ fs [SET_OF_BAG_UNION]
                \\ metis_tac [mglobals_extend_SUBSET, UNION_ASSOC, SUBSET_UNION]))
      \\ drule do_install_ssgc
      \\ disch_then drule
      \\ strip_tac \\ fs []
      \\ qexists_tac `n' + (1 + n)`
      \\ simp [first_n_exps_shift_seq]
      \\ rename1 `do_install _ _ = (_, s2)`
      \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0 g1 s1`
      \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1 g2 s2`
      \\ qmatch_asmsub_abbrev_tac `mglobals_extend s2 g3 s`
      \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0 g4 s`
      \\ rfs []
      \\ `g1 ∪ g2 ∪ g3 ⊆ g4` suffices_by metis_tac [mglobals_extend_trans, mglobals_extend_SUBSET]
      \\ unabbrev_all_tac
      \\ rpt (pop_assum kall_tac)
      \\ fs [elist_globals_append, SET_OF_BAG_UNION]
      \\ metis_tac [UNION_ASSOC, UNION_COMM, SUBSET_UNION])
    \\ reverse (fs [result_case_eq, pair_case_eq]) \\ rveq \\ fs []
    \\ drule do_app_ssgc \\ fs [EVERY_REVERSE]
    \\ strip_tac \\ rveq \\ fs []
    THEN1 (rename1 `do_app _ _ _ = Rerr err`
           \\ Cases_on `err` \\ simp []
           \\ qexists_tac `n` \\ fs [SET_OF_BAG_UNION]
           \\ metis_tac [mglobals_extend_SUBSET, UNION_ASSOC, SUBSET_UNION])
    \\ qexists_tac `n` \\ simp []
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0 g1 s1`
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1 g2 s`
    \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0 g3 s`
    \\ `g3 = g1 ∪ g2` suffices_by metis_tac [mglobals_extend_trans]
    \\ unabbrev_all_tac \\ rpt (pop_assum kall_tac)
    \\ simp [elist_globals_append, SET_OF_BAG_UNION]
    \\ metis_tac [UNION_ASSOC, UNION_COMM])
  THEN1
   (say "Fn"
    \\ fs [evaluate_def, bool_case_eq, case_eq_thms]
    \\ rveq \\ fs []
    \\ imp_res_tac lookup_vars_MEM
    \\ imp_res_tac lookup_vars_SOME
    \\ fs [EVERY_EL]
    \\ qexists_tac `0` \\ simp [])
  THEN1
   (say "Letrec"
    \\ reverse (fs [evaluate_def, bool_case_eq])
    THEN1 (qexists_tac `0` \\ simp [])
    \\ fs [Once case_eq_thms] \\ rveq \\ fs []
    THEN1 (qexists_tac `0` \\ simp [])
    \\ `EVERY vsgc_free ed`
       by (fs [case_eq_thms] \\ rveq
           \\ fs [EVERY_GENLIST]
           \\ metis_tac [EVERY_lookup_vars])
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ qexists_tac `n` \\ simp [])
  THEN1
   (say "App"
    \\ reverse (fs [evaluate_def, bool_case_eq]) \\ rveq \\ fs []
    THEN1 (qexists_tac `0` \\ simp [])
    \\ reverse (fs [pair_case_eq, Once case_eq_thms]) \\ rveq \\ fs []
    THEN1 (qexists_tac `n` \\ simp [SET_OF_BAG_UNION]
           \\ match_mp_tac mglobals_extend_SUBSET
           \\ goal_assum drule
           \\ metis_tac [UNION_ASSOC, UNION_COMM, SUBSET_UNION])
    \\ reverse (fs [pair_case_eq, case_eq_thms]) \\ rveq \\ fs []
    THEN1 (qexists_tac `n + n'` \\ simp [first_n_exps_shift_seq]
           \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0 g1 s1`
           \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1 g2 s`
           \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0 g3 s`
           \\ `g3 = g1 ∪ g2` suffices_by metis_tac [mglobals_extend_trans]
           \\ unabbrev_all_tac
           \\ simp [elist_globals_append, SET_OF_BAG_UNION]
           \\ metis_tac [UNION_ASSOC, UNION_COMM])
    \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
    \\ qexists_tac `(n'' + n) + n'` \\ simp [first_n_exps_shift_seq]
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0 g1 s1`
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1 g2 s2`
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s2 g3 s`
    \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0 g4 s`
    \\ `g1 ∪ g2 ∪ g3 ⊆ g4` suffices_by metis_tac [mglobals_extend_trans, mglobals_extend_SUBSET]
    \\ fs [elist_globals_append, SET_OF_BAG_UNION]
    \\ unabbrev_all_tac
    \\ rpt (pop_assum kall_tac)
    \\ metis_tac [UNION_ASSOC, UNION_COMM, SUBSET_UNION])
  THEN1
   (say "Tick"
    \\ fs [evaluate_def, bool_case_eq] \\ rveq \\ fs []
    THEN1 (qexists_tac `0` \\ simp [])
    \\ qpat_x_assum `_ = evaluate _` (assume_tac o GSYM)
    \\ fs [dec_clock_def]
    \\ qexists_tac `n` \\ simp [])
  THEN1
   (say "Call"
    \\ fs [evaluate_def, pair_case_eq, case_eq_thms, bool_case_eq]
    \\ rveq \\ fs []
    \\ qpat_x_assum `_ = evaluate _` (assume_tac o GSYM)
    \\ fs [dec_clock_def]
    \\ rename [`find_code _ _ s1.code = SOME (args, code)`]
    \\ fs [find_code_def, case_eq_thms, pair_case_eq, bool_case_eq]
    \\ rveq \\ fs []
    \\ `set_globals code = {||}` by metis_tac [ssgc_free_def]
    \\ fs [set_globals_empty_esgc_free]
    \\ qexists_tac `n' + n` \\ simp [first_n_exps_shift_seq]
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0 g1 s1`
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1 g2 s`
    \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0 g3 s`
    \\ `g3 = g1 ∪ g2` suffices_by metis_tac [mglobals_extend_trans]
    \\ fs [elist_globals_append, SET_OF_BAG_UNION]
    \\ metis_tac [UNION_ASSOC, UNION_COMM])
  THEN1
   (say "evaluate_app NIL"
    \\ fs [] \\ rveq \\ simp []
    \\ qexists_tac `0` \\ simp [])
  THEN1
   (say "evaluate_app CONS"
    \\ fs [evaluate_def]
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    THEN1 (qexists_tac `0` \\ simp [])
    THEN1 (fs [bool_case_eq] \\ rveq \\ fs []
           THEN1 (qexists_tac `0` \\ simp [])
           \\ fs [dest_closure_def, case_eq_thms]
           \\ rpt (pairarg_tac \\ fs [])
           \\ fs [bool_case_eq]
           \\ rveq \\ fs [dec_clock_def]
           \\ qexists_tac `0` \\ simp [])
    \\ fs [bool_case_eq] \\ rveq \\ fs []
    THEN1 (qexists_tac `0` \\ simp [])
    \\ fs [pair_case_eq] \\ fs []
    \\ drule dest_closure_Full_sgc_free \\ simp [] \\ strip_tac
    \\ fs [set_globals_empty_esgc_free, dec_clock_def]
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    THEN1 (qexists_tac `n' + n` \\ simp [first_n_exps_shift_seq]
           \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0 g1 s1`
           \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1 g2 s`
           \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0 g3 s`
           \\ `g3 = g1 ∪ g2` suffices_by metis_tac [mglobals_extend_trans]
           \\ fs [elist_globals_append, SET_OF_BAG_UNION]
           \\ metis_tac [UNION_ASSOC, UNION_COMM])
    \\ qexists_tac `n` \\ fs []));

val evaluate_changed_globals = save_thm(
   "evaluate_changed_globals",
   CONJUNCT1 evaluate_changed_globals_0);

val evaluate_app_changed_globals = save_thm(
   "evaluate_app_changed_globals",
   CONJUNCT2 evaluate_changed_globals_0);


val mk_Ticks_set_globals = Q.store_thm(
  "mk_Ticks_set_globals[simp]",
  `!t tc n exp. set_globals (mk_Ticks t tc n exp) = set_globals exp`,
  Induct_on `n` \\ simp [mk_Ticks_alt]);


val mglobals_extend_DISJOINT_state_globals_approx = Q.store_thm(
  "mglobals_extend_DISJOINT_state_globals_approx",
  `!s1 gd s2 g. mglobals_extend s1 gd s2 /\ state_globals_approx s1 g /\ DISJOINT (domain g) gd ==>
   state_globals_approx s2 g`,
  rpt strip_tac
  \\ simp [state_globals_approx_def]
  \\ rpt gen_tac \\ strip_tac
  \\ fs [mglobals_extend_def]
  \\ first_x_assum drule
  \\ reverse (Cases_on `k ∈ gd`)
  \\ fs []
  THEN1 (fs [state_globals_approx_def] \\ metis_tac [])
  THEN1 (`k ∉ domain g` by fs [Once DISJOINT_SYM, DISJOINT_ALT]
         \\ fs [domain_lookup]));


val known_op_install_correct_approx = Q.store_thm("known_op_install_correct_approx",
  `!args g0 a g vs (s0:('c, 'ffi) closSem$state) g' e s1 res s.
   known_op Install args g0 = (a,g) /\
   do_install vs s0 = (Rval e, s1) /\
   LIST_REL val_approx_val args vs /\
   co_disjoint_globals g' s0.compile_oracle /\
   state_globals_approx s0 g' /\
   ssgc_free s0 /\
   evaluate ([e], [], s1) = (res, s) ⇒
   state_globals_approx s g'`,
  rpt gen_tac \\ disch_then strip_assume_tac
  \\ drule evaluate_changed_globals
  \\ imp_res_tac do_install_ssgc \\ simp []
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1 gd s`
  \\ `gd = SET_OF_BAG (elist_globals (first_n_exps s0.compile_oracle (n + 1)))`
     by simp [first_n_exps_shift_seq, SET_OF_BAG_UNION]
  \\ `DISJOINT (domain g') gd`
     by simp [co_disjoint_globals_first_n_exps]
  \\ `state_globals_approx s1 g'`
     by (fs [do_install_def, case_eq_thms] \\ rveq \\ fs []
         \\ pairarg_tac \\ fs []
         \\ fs [bool_case_eq, pair_case_eq, case_eq_thms])
  \\ metis_tac [mglobals_extend_DISJOINT_state_globals_approx]);

val mk_Ticks_esgc_free = Q.store_thm(
  "mk_Ticks_esgc_free[simp]",
  `!t tc n exp. esgc_free (mk_Ticks t tc n exp) <=> esgc_free exp`,
  Induct_on `n` \\ fs [mk_Ticks_alt]);


val val_approx_sgc_free_def = tDefine "val_approx_gc_free" `
  (val_approx_sgc_free (ClosNoInline m n) <=> T) /\
  (val_approx_sgc_free (Clos m n e s) <=> set_globals e = {||}) /\
  (val_approx_sgc_free (Tuple tag vas) <=> EVERY val_approx_sgc_free vas) /\
  (val_approx_sgc_free _ <=> T)
` (WF_REL_TAC `measure val_approx_size`
   \\ Induct_on `vas` \\ simp []
   \\ rw [] THEN1 simp [val_approx_size_def]
   \\ first_x_assum drule
   \\ disch_then (qspec_then `tag` assume_tac)
   \\ fs [val_approx_size_def]);

val val_approx_sgc_free_def = save_thm(
  "val_approx_sgc_free_def[simp]",
  val_approx_sgc_free_def |> SIMP_RULE (srw_ss() ++ ETA_ss) []);

val val_approx_sgc_free_merge = Q.store_thm(
  "val_approx_sgc_free_merge",
  `!a1 a2. val_approx_sgc_free a1 /\ val_approx_sgc_free a2 ==>
   val_approx_sgc_free (merge a1 a2)`,
  ho_match_mp_tac merge_ind \\ simp []
  \\ rpt strip_tac
  \\ IF_CASES_TAC \\ fs [] \\ rveq
  \\ fs [EVERY_MEM]
  \\ simp [MAP2_MAP, MEM_MAP, PULL_EXISTS]
  \\ simp [MEM_ZIP, PULL_EXISTS]
  \\ fs [MEM_EL]
  \\ metis_tac []);

val globals_approx_sgc_free_def = Define `
  globals_approx_sgc_free g <=>
  !n a. lookup n g = SOME a ==> val_approx_sgc_free a`;

val known_op_preserves_esgc_free = Q.store_thm(
  "known_op_preserves_esgc_free",
  `!opn args g0 a g.
     known_op opn args g0 = (a, g) /\
     EVERY val_approx_sgc_free args /\
     globals_approx_sgc_free g0 ==>
     val_approx_sgc_free a /\ globals_approx_sgc_free g
`,
  rpt gen_tac \\ strip_tac
  \\ Cases_on `opn`
  \\ fs [known_op_def] \\ rveq \\ fs []
  THEN1 (fs [bool_case_eq, case_eq_thms] \\ rveq \\ fs []
         \\ metis_tac [globals_approx_sgc_free_def])
  THEN1 (fs [case_eq_thms] \\ rveq \\ fs []
         \\ fs [globals_approx_sgc_free_def]
         \\ rw [] \\ fs [lookup_insert, bool_case_eq]
         \\ metis_tac [val_approx_sgc_free_merge])
  THEN1 (fs [case_eq_thms, va_case_eq, bool_case_eq] \\ rveq \\ fs []
         \\ imp_res_tac integerTheory.NUM_POSINT_EXISTS \\ fs []
         \\ fs [EVERY_EL]));

val elist_globals_empty = Q.store_thm(
  "elist_globals_empty",
  `!es. elist_globals es = {||} <=>
        !e. MEM e es ==> set_globals e = {||}`,
  Induct \\ fs [] \\ rw [] \\ eq_tac \\ rw [] \\ fs []);

val clos_gen_noinline_val_approx_sgc_free = Q.store_thm(
  "clos_gen_noinline_val_approx_sgc_free",
  `!n i fns. elist_globals (MAP SND fns) = {||} ==>
               EVERY val_approx_sgc_free (clos_gen_noinline n i fns)`,
  ho_match_mp_tac clos_gen_noinline_ind
  \\ rw [] \\ fs [clos_gen_noinline_def, clos_approx_def]);

val decide_inline_LetInline_IMP_Clos = Q.store_thm(
  "decide_inline_LetInline_IMP_Clos",
  `!c fapx lopt arity body.
     decide_inline c fapx lopt arity = inlD_LetInline body ==> ?m s. fapx = Clos m arity body s`,
  rpt strip_tac
  \\ Cases_on `fapx` \\ fs [decide_inline_def, bool_case_eq]);

val known_preserves_esgc_free_0 = Q.store_thm(
  "known_preserves_esgc_free_0",
  `!c es aenv g0 eas1 g.
     known c es aenv g0 = (eas1, g) /\
     EVERY esgc_free es /\
     EVERY val_approx_sgc_free aenv /\
     globals_approx_sgc_free g0 ==>
     elist_globals (MAP FST eas1) ≤ elist_globals es /\
     EVERY esgc_free (MAP FST eas1) /\
     EVERY val_approx_sgc_free (MAP SND eas1) /\
     globals_approx_sgc_free g`,
  ho_match_mp_tac known_ind
  \\ rpt conj_tac \\ rpt (gen_tac ORELSE disch_then strip_assume_tac)
  \\ fs [known_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq \\ fs []
  \\ simp [val_approx_sgc_free_merge, SUB_BAG_UNION]
  THEN1 (simp [any_el_ALT] \\ IF_CASES_TAC \\ fs [EVERY_EL])
  THEN1 (drule known_op_preserves_esgc_free
         \\ simp [EVERY_REVERSE]
         \\ strip_tac
         \\ every_case_tac \\ simp []
         \\ rename [`isGlobal opn`] \\ Cases_on `opn` \\ fs [isGlobal_def]
         \\ fs [known_op_def, op_gbag_def])
  THEN1 (fs [inlD_case_eq, bool_case_eq, SUB_BAG_UNION]
         \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
         \\ imp_res_tac decide_inline_LetInline_IMP_Clos
         \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
         \\ imp_res_tac set_globals_empty_esgc_free \\ fs []
         \\ fs [SNOC_APPEND, elist_globals_append, SUB_BAG_UNION])
  THEN1 (fs [EVERY_REPLICATE]
         \\ imp_res_tac set_globals_empty_esgc_free \\ fs []
         \\ TOP_CASE_TAC \\ simp [clos_approx_def]
         \\ TOP_CASE_TAC \\ simp [])
  THEN1 (Cases_on `loc_opt` \\ fs []
         \\ imp_res_tac clos_gen_noinline_val_approx_sgc_free \\ fs [] \\ pop_assum kall_tac
         \\ fs [EVERY_REPLICATE]
         \\ conj_asm2_tac \\ simp []
         \\ fs [elist_globals_empty]
         \\ simp [MAP_MAP_o, o_DEF, LAMBDA_PROD]
         \\ simp [MEM_MAP] \\ rw []
         \\ qmatch_assum_rename_tac `MEM fff fns`
         \\ `MEM (SND fff) (MAP SND fns)` by metis_tac [MEM_MAP]
         \\ PairCases_on `fff` \\ fs []
         \\ first_x_assum drule \\ strip_tac
         \\ imp_res_tac set_globals_empty_esgc_free
         \\ qmatch_goalsub_abbrev_tac `known c k1 k2 k3`
         \\ Cases_on `known c k1 k2 k3`
         \\ unabbrev_all_tac
         \\ imp_res_tac known_sing_EQ_E
         \\ fs [] \\ rveq
         \\ first_x_assum drule \\ fs []));

val known_preserves_esgc_free = Q.store_thm(
  "known_preserves_esgc_free",
  `!c es aenv g0 eas1 g.
     known c es aenv g0 = (eas1, g) /\
     EVERY esgc_free es /\
     EVERY val_approx_sgc_free aenv /\
     globals_approx_sgc_free g0 ==>
     EVERY esgc_free (MAP FST eas1) /\
     EVERY val_approx_sgc_free (MAP SND eas1) /\
     globals_approx_sgc_free g`,
  rpt gen_tac \\ rpt (disch_then strip_assume_tac)
  \\ metis_tac [known_preserves_esgc_free_0]);

val known_elglobals_dont_grow = Q.store_thm(
  "known_elglobals_dont_grow",
  `!c es aenv g0 eas1 g.
     known c es aenv g0 = (eas1, g) /\
     EVERY esgc_free es /\
     EVERY val_approx_sgc_free aenv /\
     globals_approx_sgc_free g0 ==>
     elist_globals (MAP FST eas1) ≤ elist_globals es`,
  rpt gen_tac \\ rpt (disch_then strip_assume_tac)
  \\ metis_tac [known_preserves_esgc_free_0]);

val known_preserves_pure = Q.store_thm(
  "known_preserves_pure",
  `!c es aenv g0 eas1 g.
     known c es aenv g0 = (eas1, g) /\
     EVERY pure es ==>
     EVERY pure (MAP FST eas1)`,
  ho_match_mp_tac known_ind
  \\ simp [known_def]
  \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ imp_res_tac known_sing_EQ_E
  \\ fs [] \\ rveq
  \\ fs [closLangTheory.pure_def]
  \\ every_case_tac
  \\ fs [closLangTheory.pure_def, closLangTheory.pure_op_def, ETA_THM]);

val evaluate_mk_Ticks_rw = Q.store_thm(
  "evaluate_mk_Ticks_rw",
  `!t tc n exp env (s:('c,'ffi) closSem$state).
     evaluate ([mk_Ticks t tc n exp], env, s) =
     if s.clock < n then (Rerr (Rabort Rtimeout_error), s with clock := 0)
     else evaluate ([exp], env, dec_clock n s)`,
  Induct_on `n`
  THEN1 simp [mk_Ticks_alt, dec_clock_def]
  \\ rw []
  \\ fs [mk_Ticks_alt, evaluate_def, dec_clock_def, ADD1]
  \\ IF_CASES_TAC \\ simp [state_component_equality])

val evaluate_mk_Ticks_IMP = Q.store_thm(
  "evaluate_mk_Ticks_IMP",
  `!t tc n exp env (s0:('c,'ffi) closSem$state) res s.
     evaluate ([mk_Ticks t tc n exp], env, s0) = (res, s) ==>
     (res = Rerr (Rabort Rtimeout_error) /\ s = s0 with clock := 0) \/
     (evaluate ([exp], env, dec_clock n s0) = (res, s))`,
  Induct_on `n` \\ rpt strip_tac
  THEN1 (fs [mk_Ticks_alt, dec_clock_def])
  \\ fs [mk_Ticks_alt] \\ res_tac
  \\ fs [evaluate_def] 
  \\ fs [bool_case_eq, dec_clock_def, ADD1, state_component_equality]);

val clos_gen_noinline_eq = Q.prove(`
  !n c fns.
  clos_gen_noinline n c fns =
  GENLIST (λi. ClosNoInline (2 * (i+c) + n) (FST (EL i fns))) (LENGTH fns)`,
  Induct_on`fns`>>fs[FORALL_PROD,clos_gen_noinline_def,GENLIST_CONS]>>rw[]>>
  simp[o_DEF,ADD1])

val letrec_case_eq = Q.prove(`
  !limit loc fns.
  (case loc of
    NONE => REPLICATE (LENGTH fns) Other
  | SOME n => clos_gen_noinline n 0 fns) =
  GENLIST (case loc of NONE => K Other |
                       SOME n => λi. ClosNoInline (n + 2*i) (FST (EL i fns))) (LENGTH fns)`,
  Cases_on`loc`>>fs[clos_gen_noinline_eq,REPLICATE_GENLIST])


val say = say0 "known_correct_approx";

val known_correct_approx = Q.store_thm(
  "known_correct_approx",
  `!limit es aenv g1 eas g g' env (s1:('c, 'ffi) closSem$state) res s.
   known limit es aenv g1 = (eas,g) /\
   evaluate (MAP FST eas, env, s1) = (res, s) /\
   unique_set_globals es s1.compile_oracle /\
   LIST_REL val_approx_val aenv env /\
   state_globals_approx s1 g' /\
   subspt g1 g /\ subspt g g' /\
   co_disjoint_globals g' s1.compile_oracle /\
   ssgc_free s1 /\ EVERY vsgc_free env /\ EVERY esgc_free es /\
   EVERY val_approx_sgc_free aenv /\ globals_approx_sgc_free g1 ==>
     state_globals_approx s g' /\
     !vs. res = Rval vs ==> LIST_REL val_approx_val (MAP SND eas) vs`,
  (**)
  ho_match_mp_tac known_ind \\ simp [known_def]
  \\ rpt conj_tac \\ rpt (gen_tac ORELSE disch_then strip_assume_tac)
  THEN1
   (say "NIL" \\ fs [evaluate_def] \\ rveq \\ fs [])
  THEN1
   (say "CONS"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_LENGTH_EQ_E
    \\ fs [LENGTH_EQ_NUM, LENGTH_EQ_NUM_compute]
    \\ rveq \\ fs []
    \\ rename1 `known limit [exp1] aenv g1 = ([ea1], g2)`
    \\ `?exp1' a1. ea1 = (exp1', a1)` by (Cases_on `ea1` \\ simp []) \\ rveq
    \\ rename1 `known limit (exp2::exps) aenv g2 = (ea2::eas, g)`
    \\ `?exp2' a2. ea2 = (exp2', a2)` by (Cases_on `ea2` \\ simp []) \\ rveq
    \\ fs []
    \\ fs [evaluate_def]
    \\ `?res1 s2. evaluate ([exp1'],env,s1) = (res1, s2)` by fs [pair_case_eq]
    \\ `?res2 s3. evaluate (exp2'::MAP FST eas,env,s2) = (res2, s3)`
         by (Cases_on `evaluate (exp2'::MAP FST eas,env,s2)` \\ fs [])
    \\ imp_res_tac unique_set_globals_subexps
    \\ `unique_set_globals (exp2::exps) s2.compile_oracle`
         by (imp_res_tac evaluate_code \\ metis_tac [unique_set_globals_shift_seq])
    \\ `subspt g1 g2 /\ subspt g2 g`
       by (match_mp_tac subspt_known_elist_globals
           \\ asm_exists_tac \\ simp []
           \\ goal_assum drule
           \\ fs [unique_set_globals_def,elist_globals_append]
           \\ fs [BAG_ALL_DISTINCT_BAG_UNION])
    \\ `subspt g2 g'` by metis_tac [subspt_trans]
    \\ patresolve `known _ [_] _ _ = _` (el 1) known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ `ssgc_free s2`
       by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
           \\ rpt (disch_then drule \\ simp []))
    \\ drule co_disjoint_globals_evaluate \\ disch_then drule \\ strip_tac
    \\ REPEAT (first_x_assum drule
               \\ rpt (disch_then drule)
               \\ fs [] \\ strip_tac)
    \\ Cases_on `res1` \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `res2` \\ fs [] \\ rveq \\ fs [])
  THEN1
   (say "Var"
    \\ fs [evaluate_def, bool_case_eq] \\ rveq
    \\ fs [any_el_ALT] \\ fs [LIST_REL_EL_EQN])
  THEN1
   (say "If"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ rename1 `known limit [x1] aenv g1 = ([(e1,a1)], g2)`
    \\ rename1 `known limit [x2] aenv g2 = ([(e2,a2)], g3)`
    \\ rename1 `known limit [x3] aenv g3 = ([(e3,a3)], g4)`
    \\ imp_res_tac unique_set_globals_subexps
    \\ fs [evaluate_def]
    \\ fs [pair_case_eq]
    \\ `subspt g1 g2 /\ subspt g2 g3 /\ subspt g3 g4`
       by (`?unused. known limit [x1;x2] aenv g1 = (unused, g3)` by simp [known_def]
           \\ drule subspt_known_elist_globals
           \\ rpt (disch_then drule)
           \\ impl_tac THEN1 fs [unique_set_globals_def,BAG_ALL_DISTINCT_BAG_UNION]
           \\ strip_tac \\ simp []
           \\ match_mp_tac subspt_known_elist_globals
           \\ asm_exists_tac \\ simp []
           \\ goal_assum drule
           \\ fs [unique_set_globals_def,BAG_ALL_DISTINCT_BAG_UNION])
    \\ `subspt g2 g' /\ subspt g3 g'` by metis_tac [subspt_trans]
    \\ first_x_assum drule
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ rename1 `evaluate ([e1],env,s1) = (res1, s2)`
    \\ Cases_on `res1` \\ fs [] \\ rveq \\ fs []
    \\ rename1 `evaluate ([e1],env,s1) = (Rval [vcond],s2)`
    \\ Cases_on `Boolv T = vcond \/ Boolv F = vcond`
    \\ fs [] \\ rveq \\ fs []
    \\ rename1 `evaluate ([e_taken_branch],env,s2) = (res, s)`
    \\ rename1 `known limit [x_taken_branch] aenv _ = ([e_taken_branch,_],_)`
    \\ `unique_set_globals [x_taken_branch] s2.compile_oracle`
         by metis_tac [unique_set_globals_evaluate]
    \\ rpt (qpat_x_assum `unique_set_globals _ s1.compile_oracle` kall_tac)
    \\ drule co_disjoint_globals_evaluate \\ disch_then drule \\ strip_tac
    \\ patresolve `known _ _ _ g1 = _` (el 1) known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ patresolve `known _ _ _ g2 = _` (el 1) known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ `ssgc_free s2`
       by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
           \\ rpt (disch_then drule \\ simp []))
    \\ first_x_assum drule
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ Cases_on `res` \\ fs [] \\ rveq
    \\ fs [val_approx_val_merge_I])
  THEN1
   (say "Let"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ rename1 `known limit xs aenv g1 = (ea1, g2)`
    \\ rename1 `known limit [x2] _ g2 = ([(e2,a2)], g3)`
    \\ imp_res_tac unique_set_globals_subexps
    \\ fs [evaluate_def, pair_case_eq]
    \\ `subspt g1 g2 /\ subspt g2 g3`
       by (match_mp_tac subspt_known_elist_globals
           \\ rpt (asm_exists_tac \\ simp [])
           \\ fs [unique_set_globals_def,
                  BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
    \\ `subspt g2 g'` by metis_tac [subspt_trans]
    \\ first_x_assum drule
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ rename1 `evaluate (MAP FST ea1,env,s1) = (Rval vs, s2)`
    \\ `unique_set_globals [x2] s2.compile_oracle`
         by metis_tac [unique_set_globals_evaluate]
    \\ drule co_disjoint_globals_evaluate \\ disch_then drule \\ strip_tac
    \\ patresolve `known _ _ _ g1 = _` (el 1) known_preserves_esgc_free
    \\ simp [] \\ strip_tac \\ fs []
    \\ `ssgc_free s2 /\ EVERY vsgc_free vs`
       by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
           \\ rpt (disch_then drule \\ simp []))
    \\ first_x_assum irule \\ simp []
    \\ qexists_tac `vs ++ env`
    \\ qexists_tac `s2` \\ fs []
    \\ irule EVERY2_APPEND_suff \\ fs [])
  THEN1
   (say "Raise"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ rename1 `known limit [x1] aenv g1 = ([(e1,a1)], g2)`
    \\ imp_res_tac unique_set_globals_subexps
    \\ fs [evaluate_def, pair_case_eq]
    \\ first_x_assum drule
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ fs [case_eq_thms] \\ rveq
    \\ simp [])
  THEN1
   (say "Tick"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ imp_res_tac unique_set_globals_subexps
    \\ fs [evaluate_def, pair_case_eq]
    \\ Cases_on `s1.clock = 0` \\ fs [] \\ rveq \\ fs []
    \\ first_x_assum (qpat_assum `evaluate _ = _` o mp_then Any match_mp_tac)
    \\ fs [dec_clock_def])
  THEN1
   (say "Handle"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ rename1 `known limit [x1] _ g1 = ([(e1,a1)], g2)`
    \\ rename1 `known limit [x2] _ g2 = ([(e2,a2)], g3)`
    \\ imp_res_tac unique_set_globals_subexps
    \\ fs [evaluate_def, pair_case_eq]
    \\ `subspt g1 g2 /\ subspt g2 g3`
       by (match_mp_tac subspt_known_elist_globals
           \\ rpt (asm_exists_tac \\ simp [])
           \\ fs [unique_set_globals_def,
                  BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
    \\ `subspt g2 g'` by metis_tac [subspt_trans]
    \\ first_x_assum drule
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    THEN1 (fs [val_approx_val_merge_I])
    \\ rename1 `evaluate (_,_,s1) = (Rerr (Rraise v), s2)`
    \\ `unique_set_globals [x2] s2.compile_oracle`
         by metis_tac [unique_set_globals_evaluate]
    \\ drule co_disjoint_globals_evaluate \\ disch_then drule \\ strip_tac
    \\ patresolve `known _ _ _ g1 = _` (el 1) known_preserves_esgc_free
    \\ simp [] \\ strip_tac \\ fs []
    \\ `ssgc_free s2 /\ vsgc_free v`
       by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
           \\ rpt (disch_then drule \\ simp []))
    \\ first_x_assum (qpat_assum `evaluate (_,_,s2) = _` o mp_then Any mp_tac)
    \\ simp []
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ Cases_on `res`
    \\ fs [val_approx_val_merge_I])
  THEN1
   (say "Call"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, pair_case_eq]
    \\ imp_res_tac unique_set_globals_subexps
    \\ first_x_assum drule
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ patresolve `known _ _ _ g1 = _` (el 1) known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ fs [pair_case_eq] \\ rveq
    \\ rename1 `evaluate (_,_,s1) = (Rval vs, s2)`
    \\ Cases_on `s2.clock < ticks + 1`
    \\ fs [] \\ rveq \\ fs []
    \\ `ssgc_free s2 /\ EVERY vsgc_free vs`
       by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
           \\ rpt (disch_then drule \\ simp []))
    \\ rename1 `find_code _ _ _ = SOME (args, exp)`
    \\ `set_globals exp = {||} /\ EVERY vsgc_free args`
       by (fs [find_code_def, case_eq_thms, pair_case_eq]
           \\ metis_tac [ssgc_free_def])
    \\ patresolve `evaluate ([exp],_,_) = _` (el 1) evaluate_changed_globals
    \\ simp [dec_clock_def, set_globals_empty_esgc_free]
    \\ strip_tac
    \\ drule mglobals_extend_DISJOINT_state_globals_approx
    \\ disch_then drule
    \\ impl_tac
    THEN1 metis_tac [co_disjoint_globals_first_n_exps, co_disjoint_globals_evaluate]
    \\ metis_tac [evaluate_SING])
  THEN1
   (say "Op"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ rename1 `known limit xs aenv g1 = (ea1, g2)`
    \\ rename1 `[Op _ opn _]`
    \\ imp_res_tac unique_set_globals_subexps
    \\ `subspt g1 g2 /\ subspt g2 g`
       by (match_mp_tac subspt_known_op_elist_globals
           \\ rpt (goal_assum drule)
           \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION])
    \\ `subspt g2 g'` by metis_tac [subspt_trans]
    \\ Cases_on `opn = Install`
    THEN1
     (rveq \\ fs [isGlobal_def]
      \\ reverse conj_tac
      THEN1 (Cases_on `res` \\ fs [known_op_def]
             \\ imp_res_tac evaluate_SING
             \\ rveq \\ simp [])
      \\ fs [evaluate_def]
      \\ fs [pair_case_eq]
      \\ first_x_assum drule
      \\ rpt (disch_then drule)
      \\ strip_tac
      \\ reverse (fs [case_eq_thms, pair_case_eq]) \\ rveq \\ fs []
      THEN1 (fs [do_install_def, case_eq_thms] \\ rveq \\ fs []
             \\ pairarg_tac \\ fs []
             \\ fs [bool_case_eq, pair_case_eq, case_eq_thms] \\ rveq \\ fs [])
      \\ rename1 `do_install _ s2 = (_, s3)`
      \\ `ssgc_free s2`
         by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
             \\ rpt (disch_then drule)
             \\ drule known_preserves_esgc_free \\ simp [])
      \\ imp_res_tac EVERY2_REVERSE \\ simp []
      \\ match_mp_tac known_op_install_correct_approx
      \\ rpt (goal_assum drule \\ simp [])
      \\ metis_tac [co_disjoint_globals_evaluate])
    \\ Cases_on `isGlobal opn` \\ fs []
    THENL
     [Cases_on `opn` \\ fs [isGlobal_def]
      \\ rename1 `gO_destApx apx`
      \\ Cases_on `gO_destApx apx` \\ fs []
      \\ fs [evaluate_def]
      THEN1 (fs [do_app_def] \\ rveq
             \\ Cases_on `apx` \\ fs [gO_destApx_def, bool_case_eq])
      THEN1 (fs [do_app_def] \\ rveq
             \\ Cases_on `apx` \\ fs [gO_destApx_def, bool_case_eq, NULL_EQ]),
      fs [evaluate_def]]
    \\ fs [pair_case_eq]
    \\ first_x_assum drule
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ fs [case_eq_thms, pair_case_eq] \\ rveq \\ fs []
    \\ irule known_op_correct_approx
    \\ rpt (goal_assum drule \\ simp [])
    \\ irule EVERY2_REVERSE \\ simp [])
  THEN1
   (say "App"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ rename1 `known _ [_] _ g2 = (_, g3)`
    \\ reverse (fs [inlD_case_eq])
    THEN1 (* inlD_LetInline *)
     (fs [bool_case_eq]
      \\ rpt (pairarg_tac \\ fs []) \\ rveq
      \\ rename1 `known limit [_] _ g2 = (_, g)`
      \\ fs [evaluate_def, pair_case_eq]
      \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
      THEN1 (* pure *)
       (imp_res_tac unique_set_globals_subexps
        \\ `subspt g1 g2 /\ subspt g2 g`
           by (match_mp_tac subspt_known_elist_globals
               \\ rpt (goal_assum drule)
               \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
        \\ `subspt g2 g'` by metis_tac [subspt_trans]
        \\ first_x_assum drule
        \\ rpt (disch_then drule)
        \\ strip_tac
        \\ fs [result_case_eq] \\ rveq \\ fs []
        \\ imp_res_tac evaluate_mk_Ticks_IMP \\ fs []
        \\ last_x_assum (pop_assum o mp_then Any match_mp_tac)
        \\ simp [dec_clock_def]
        \\ simp [EVERY2_APPEND_suff]
        \\ rename1 `evaluate (MAP FST ea2, env, s1) = (Rval args, s2)`
        \\ drule co_disjoint_globals_evaluate \\ disch_then drule
        \\ simp [] \\ disch_then kall_tac
        \\ patresolve  `known _ _ _ g1 = _` hd known_preserves_esgc_free
        \\ simp [] \\ strip_tac
        \\ patresolve  `known _ _ _ g2 = _` hd known_preserves_esgc_free
        \\ simp [] \\ strip_tac
        \\ imp_res_tac decide_inline_LetInline_IMP_Clos \\ rveq \\ fs []
        \\ imp_res_tac set_globals_empty_esgc_free \\ simp []
        \\ simp [ALL_EL_MAP]
        \\ patresolve `evaluate (_,_,s1) = _` hd evaluate_changed_globals
        \\ simp [ALL_EL_MAP] \\ disch_then kall_tac
        \\ rename1 `known _ [xbody] _ g = (_, gdead)`
        \\ `unique_set_globals [xbody] s2.compile_oracle`
           by (match_mp_tac unique_set_globals_evaluate
               \\ goal_assum (first_assum o mp_then (Pos (el 2)) mp_tac)
               \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION])
        \\ simp []
        \\ `g = gdead`
           by (match_mp_tac known_unchanged_globals
               \\ goal_assum drule \\ simp [])
        \\ fs [])
      THEN1 (* not pure *)
       (fs [evaluate_append, pair_case_eq]
        \\ rename1 `evaluate (_, _, s1) = (res1, s2)`
        \\ imp_res_tac unique_set_globals_subexps
        \\ `subspt g1 g2 /\ subspt g2 g`
           by (match_mp_tac subspt_known_elist_globals
               \\ rpt (goal_assum drule)
               \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
        \\ `subspt g2 g'` by metis_tac [subspt_trans]
        \\ first_x_assum drule
        \\ rpt (disch_then drule)
        \\ strip_tac
        \\ Cases_on `res1`
        \\ fs [] \\ rveq \\ fs [] \\ rveq \\ fs []
        \\ rename1 `evaluate (_, _, s1) = (Rval args, _)`
        \\ fs [pair_case_eq]
        \\ rename1 `evaluate (_, _, s2) = (res2, s3)`
        \\ patresolve  `known _ _ _ g1 = _` hd known_preserves_esgc_free
        \\ simp [] \\ strip_tac
        \\ patresolve `ssgc_free _` (el 2) evaluate_changed_globals
        \\ rpt (disch_then drule \\ simp []) \\ strip_tac
        \\ drule co_disjoint_globals_evaluate \\ disch_then drule \\ strip_tac
        \\ `unique_set_globals [x] s2.compile_oracle`
           by metis_tac [unique_set_globals_evaluate]
        \\ first_x_assum drule
        \\ rpt (disch_then drule)
        \\ strip_tac
        \\ Cases_on `res2`
        \\ fs [] \\ rveq \\ fs [] \\ rveq \\ fs []
        \\ patresolve  `known _ _ _ g2 = _` hd known_preserves_esgc_free
        \\ simp [] \\ strip_tac
        \\ imp_res_tac decide_inline_LetInline_IMP_Clos \\ rveq \\ fs []
        \\ imp_res_tac set_globals_empty_esgc_free \\ simp []
        \\ patresolve `ssgc_free _` (el 2) evaluate_changed_globals
        \\ rpt (disch_then drule \\ simp []) \\ strip_tac
        \\ imp_res_tac evaluate_mk_Ticks_IMP \\ fs []
        \\ last_x_assum (pop_assum o mp_then Any match_mp_tac)
        \\ simp [dec_clock_def, SNOC_APPEND, EVERY2_APPEND_suff]
        \\ simp [co_disjoint_globals_shift_seq]
        \\ fs [case_eq_thms, pair_case_eq, bool_case_eq] \\ rveq
        \\ rename1 `known _ [xbody] _ g = (_, gdead)`
        \\ `unique_set_globals [xbody] s1.compile_oracle`
           by fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION]
        \\ simp [unique_set_globals_shift_seq]
        \\ `g = gdead` by (match_mp_tac known_unchanged_globals \\ goal_assum drule \\ simp [])
        \\ fs []))
    (* This next part solves both inlD_Nothing and inlD_Annotate *)
    THEN 
     (rveq \\ fs [evaluate_def, bool_case_eq, pair_case_eq]
      \\ imp_res_tac unique_set_globals_subexps
      \\ `subspt g1 g2 /\ subspt g2 g`
         by (match_mp_tac subspt_known_elist_globals
             \\ rpt (goal_assum drule)
             \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
      \\ `subspt g2 g'` by metis_tac [subspt_trans]
      \\ first_x_assum drule
      \\ rpt (disch_then drule)
      \\ strip_tac
      \\ fs [result_case_eq] \\ rveq \\ fs []    
      \\ rename1 `evaluate (MAP FST ea2, env, s1) = (Rval args, s2)`
      \\ `unique_set_globals [x] s2.compile_oracle`
         by metis_tac [unique_set_globals_evaluate]
      \\ drule co_disjoint_globals_evaluate \\ disch_then drule \\ strip_tac
      \\ patresolve `known _ _ _ g1 = _` (el 1) known_preserves_esgc_free
      \\ simp [] \\ strip_tac
      \\ `ssgc_free s2 /\ EVERY vsgc_free args`
         by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
             \\ rpt (disch_then drule \\ simp []))
      \\ fs [pair_case_eq]
      \\ first_x_assum drule
      \\ rpt (disch_then drule)
      \\ strip_tac
      \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq \\ fs []
      \\ reverse conj_tac
      THEN1 (Cases_on `res` \\ imp_res_tac evaluate_app_IMP_LENGTH
             \\ fs [LENGTH_EQ_NUM_compute])
      \\ rename1 `evaluate ([_], _, s2) = (Rval [fval], s3)`
      \\ patresolve `known _ _ _ g2 = _` (el 1) known_preserves_esgc_free
      \\ simp [] \\ strip_tac
      \\ `ssgc_free s3 /\ vsgc_free fval`
         by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
             \\ rpt (disch_then drule \\ simp []))
      \\ drule evaluate_app_changed_globals \\ simp [] \\ strip_tac
      \\ drule co_disjoint_globals_evaluate \\ disch_then drule \\ strip_tac
      \\ qmatch_asmsub_abbrev_tac `mglobals_extend _ gd _`
      \\ `DISJOINT (domain g') gd` by metis_tac [co_disjoint_globals_first_n_exps]
      \\ metis_tac [mglobals_extend_DISJOINT_state_globals_approx]))
  THEN1
   (say "Fn" \\ cheat
    (* \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def]
    \\ fs [bool_case_eq] \\ rveq
    \\ Cases_on `loc_opt` \\ simp []
    \\ simp [clos_approx_def]
    \\ IF_CASES_TAC \\ simp [] *))
  THEN1
   (say "Letrec"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ imp_res_tac unique_set_globals_subexps
    \\ fs [evaluate_def, bool_case_eq, clos_gen_noinline_eq]
    \\ fixeqs
    \\ qmatch_assum_abbrev_tac `closSem$evaluate([_], GENLIST (_ (MAP ff _)) _ ++ _, _) = _`
    \\ rename1 `closSem$evaluate ([body'],
                                  GENLIST (Recclosure lopt [] env (MAP ff fns))
                                  (LENGTH fns) ++ env,
                                  s0) = (result, s)`
    \\ first_x_assum (qpat_assum `evaluate ([_],_,_) = _` o mp_then Any match_mp_tac)
    \\ simp []
    \\ Cases_on `lopt` \\ fs []
    THEN1
     (fs [REPLICATE_GENLIST]
      \\ conj_tac
      THEN1 (irule EVERY2_APPEND_suff \\ simp []
             \\ fs [LIST_REL_GENLIST])
      \\ reverse conj_tac
      THEN1 fs [EVERY_GENLIST]
      \\ fs [EVERY_GENLIST]
      \\ fs [elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS, FORALL_PROD]
      \\ simp [Abbr `ff`] \\ rpt strip_tac
      \\ qmatch_abbrev_tac `set_globals (FST (HD (FST (known _ [_] ENV g1)))) = {||}`
      \\ rename1 `MEM (num_args, fbody) fns`
      \\ `set_globals fbody = {||}` by metis_tac[]
      \\ Cases_on `known limit [fbody] ENV g1` \\ simp []
      \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
      \\ patresolve `known _ [fbody] _ _ = _` (el 1) known_elglobals_dont_grow
      \\ fs [set_globals_empty_esgc_free]
      \\ simp [Abbr `ENV`, EVERY_GENLIST])
    THEN1
     (conj_tac
      THEN1 (irule EVERY2_APPEND_suff \\ simp []
             \\ fs [LIST_REL_GENLIST, EL_MAP]
             \\ rpt strip_tac
             \\ simp [Abbr `ff`]
             \\ pairarg_tac \\ simp [])
      \\ reverse conj_tac
      THEN1 fs [EVERY_GENLIST]
      \\ fs [EVERY_GENLIST]
      \\ fs [elglobals_EQ_EMPTY]
      \\ simp [MEM_MAP, PULL_EXISTS, FORALL_PROD]
      \\ simp [Abbr `ff`] \\ rpt strip_tac
      \\ qmatch_abbrev_tac `set_globals (FST (HD (FST (known _ [_] ENV g1)))) = {||}`
      \\ rename1 `MEM (num_args, fbody) fns`
      \\ `set_globals fbody = {||}`
         by (fs [MEM_MAP, PULL_EXISTS, FORALL_PROD] \\ metis_tac [])
      \\ Cases_on `known limit [fbody] ENV g1` \\ simp []
      \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
      \\ patresolve `known _ [fbody] _ _ = _` (el 1) known_elglobals_dont_grow
      \\ fs [set_globals_empty_esgc_free]
      \\ disch_then match_mp_tac
      \\ simp [Abbr `ENV`]
      \\ simp [EVERY_REPLICATE, EVERY_GENLIST])));


(* code relation *)

val exp_rel_def = Define `
  exp_rel limit aenv g' e1 e2 <=>
    ?g0 g apx.
      subspt g g' /\
      EVERY val_approx_sgc_free aenv /\
      globals_approx_sgc_free g0 /\
      known limit [e1] aenv g0 = ([(e2, apx)], g)`;

(* value relation *)

val f_rel_def = Define `
  f_rel limit aenv g (a1, e1) (a2, e2) <=>
     a1 = a2 /\ exp_rel limit (REPLICATE a1 Other ++ aenv) g e1 e2`;

val (v_rel_rules, v_rel_ind, v_rel_cases) = Hol_reln `
  (!i. v_rel l g (Number i) (Number i)) /\
  (!w. v_rel l g (Word64 w) (Word64 w)) /\
  (!w. v_rel l g (ByteVector w) (ByteVector w)) /\
  (!n. v_rel l g (RefPtr n) (RefPtr n)) /\
  (!tag xs ys.
     LIST_REL (v_rel l g) xs ys ==>
       v_rel l g (Block tag xs) (Block tag ys)) /\
  (!loc args1 args2 env1 env2 num_args e1 e2 aenv.
     LIST_REL (v_rel l g) env1 env2 /\
     LIST_REL (v_rel l g) args1 args2 /\
     LIST_REL val_approx_val aenv env2 /\
     exp_rel l (REPLICATE num_args Other ++ aenv) g e1 e2 ==>
       v_rel l g (Closure loc args1 env1 num_args e1) (Closure loc args2 env2 num_args e2)) /\
  (!loc_opt funs1 funs2 args1 args2 env1 env2 k aenv.
     LIST_REL (v_rel l g) env1 env2 /\
     LIST_REL (v_rel l g) args1 args2 /\
     (clos = case loc_opt of
               | NONE => REPLICATE (LENGTH funs1) Other
               | SOME loc => clos_gen_noinline loc 0 funs1) /\
     LIST_REL (f_rel l (clos ++ aenv) g) funs1 funs2 ==>
       v_rel l g (Recclosure loc_opt args1 env1 funs1 k) (Recclosure loc_opt args2 env2 funs2 k))`;


val v_rel_simps = save_thm("v_rel_simps[simp]",LIST_CONJ [
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel l g (Number n) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel l g (Block n p) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel l g (Word64 p) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel l g (ByteVector p) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel l g (RefPtr p) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel l g (Closure x1 x2 x3 x4 x5) x``,
  SIMP_CONV (srw_ss()) [v_rel_cases] ``v_rel l g (Recclosure y1 y2 y3 y4 y5) x``,
  prove(``v_rel l g (Boolv b) x <=> x = Boolv b``,
        Cases_on `b` \\ fs [Boolv_def,Once v_rel_cases]),
  prove(``v_rel l g Unit x <=> x = Unit``,
        fs [closSemTheory.Unit_def,Once v_rel_cases])])

val v_rel_vsgc_free = Q.store_thm(
  "v_rel_vsgc_free",
  `!l g v1 v2. v_rel l g v1 v2 ==> (vsgc_free v1 ==> vsgc_free v2)`,
  cheat);

val v_rel_Boolv = Q.store_thm(
  "v_rel_Boolv[simp]",
  `(v_rel l g (Boolv b) v ⇔ v = Boolv b) ∧
   (v_rel l g v (Boolv b) ⇔ v = Boolv b)`,
  simp [closSemTheory.Boolv_def] >> Cases_on `v` >> simp[] >> metis_tac[]);

val v_rel_Unit = Q.store_thm(
  "v_rel_Unit[simp]",
  `(v_rel l g Unit v ⇔ v = Unit) ∧ (v_rel l g v Unit ⇔ v = Unit)`,
  simp[Unit_def] >> Cases_on `v` >> simp[] >> metis_tac[])

val v_rel_EVERY_vsgc_free = Q.store_thm(
  "v_rel_EVERY_vsgc_free",
  `!vs1 vs2.
     LIST_REL (v_rel l g) vs1 vs2 ==>
     (EVERY vsgc_free vs1 ==> EVERY vsgc_free vs2)`,
  Induct_on `LIST_REL` >> simp[] >> metis_tac [v_rel_vsgc_free]);

(* state relation *)

val (ref_rel_rules, ref_rel_ind, ref_rel_cases) = Hol_reln `
  (!b bs. ref_rel l g (ByteArray b bs) (ByteArray b bs)) /\
  (!xs ys.
    LIST_REL (v_rel l g) xs ys ==>
    ref_rel l g (ValueArray xs) (ValueArray ys))`;

val ref_rel_simps = save_thm("ref_rel_simps[simp]",LIST_CONJ [
  SIMP_CONV (srw_ss()) [ref_rel_cases] ``ref_rel l g (ValueArray vs) x``,
  SIMP_CONV (srw_ss()) [ref_rel_cases] ``ref_rel l g (ByteArray b bs) x``])

val compile_inc_def = Define `
  compile_inc l g (e,xs) =
    let (ea, g') = known l [e] [] g in (g', FST (HD ea), xs)`;

val state_rel_def = Define `
  state_rel l g (s:(val_approx num_map#'c,'ffi) closSem$state) (t:('c,'ffi) closSem$state) <=>
    (!n. SND (SND (s.compile_oracle n)) = []) /\
    s.code = FEMPTY /\ t.code = FEMPTY /\
    s.clock = t.clock /\ s.ffi = t.ffi /\ s.max_app = t.max_app /\
    LIST_REL (OPTREL (v_rel l g)) s.globals t.globals /\
    fmap_rel (ref_rel l g) s.refs t.refs /\
    s.compile = state_cc (compile_inc l) t.compile  /\
    t.compile_oracle = state_co (compile_inc l) s.compile_oracle`;

val oracle_state_sgc_free_def = Define `
  oracle_state_sgc_free co = !n. globals_approx_sgc_free (FST (FST (co n)))`;

val oracle_state_sgc_free_shift_seq =
  Q.store_thm("oracle_state_sgc_free_shift_seq",
  `!co n. oracle_state_sgc_free co ==> oracle_state_sgc_free (shift_seq n co)`,
  rpt strip_tac \\ fs [oracle_state_sgc_free_def, shift_seq_def])

val state_rel_ssgc_free = Q.store_thm(
  "state_rel_ssgc_free",
  `!l g s1 s2. state_rel l g s1 s2 /\ oracle_state_sgc_free s1.compile_oracle  /\ ssgc_free s1 ==> ssgc_free s2`,
  simp [state_rel_def, ssgc_free_def]
  \\ rpt strip_tac
  \\ fs [fmap_rel_OPTREL_FLOOKUP]
  THEN1
   (rename1 `FLOOKUP s2.refs kk = SOME (ValueArray vvl)`
    \\ `OPTREL (ref_rel l g) (FLOOKUP s1.refs kk) (FLOOKUP s2.refs kk)` by simp[]
    \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [OPTREL_def]
    \\ simp [PULL_EXISTS]
    \\ Cases \\ simp[]
    \\ metis_tac [v_rel_EVERY_vsgc_free])
  THEN1
   (fs [LIST_REL_EL_EQN]
    \\ imp_res_tac (MEM_EL |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GSYM)
    \\ rename1 `EL kk s2.globals`
    \\ `OPTREL (v_rel l g) (EL kk s1.globals) (EL kk s2.globals)` by simp[]
    \\ pop_assum mp_tac \\ simp_tac(srw_ss()) [OPTREL_def] \\ simp[]
    \\ metis_tac [v_rel_vsgc_free, MEM_EL])
  THEN1
   (fs [state_co_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ rename1 `s1.compile_oracle nn = _`
    \\ Cases_on `SND (s1.compile_oracle nn)`
    \\ res_tac
    \\ rfs [] \\ rveq \\ fs []
    \\ fs [compile_inc_def]
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ rveq \\ fs []
    \\ drule known_preserves_esgc_free \\ fs []
    \\ fs [oracle_state_sgc_free_def]
    \\ rename1 `known _ _ _ ss`
    \\ `ss = FST (FST (s1.compile_oracle nn))` by simp []
    \\ metis_tac [])
  THEN1
   (fs [state_co_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ rename1 `compile_inc _ _ progs`
    \\ PairCases_on `progs` \\ fs [compile_inc_def]
    \\ pairarg_tac \\ fs [] \\ rveq
    \\ rename1 `s1.compile_oracle nn = _`
    \\ qpat_x_assum `!n. _ = []` (qspec_then `nn` mp_tac)
    \\ simp []))

val loptrel_def = Define`
  loptrel fv numargs lopt1 lopt2 ⇔
     lopt2 = lopt1 ∨
     lopt1 = NONE ∧
     case (fv,lopt2) of
       | (Closure (SOME loc1) ae _ n bod, SOME loc2) =>
            loc1 = loc2 ∧ n = numargs ∧ ae = []
       | (Recclosure (SOME loc1) ae _ fns i, SOME loc2) =>
         i < LENGTH fns ∧ loc2 = loc1 + 2 * i ∧ numargs = FST (EL i fns) ∧
         ae = []
       | _ => F
`;

val evaluate_changed_globals_inst = INST_TYPE [``:'c`` |-> ``:val_approx num_map#'c``] evaluate_changed_globals
val known_correct_approx_inst = INST_TYPE [``:'c`` |-> ``:val_approx num_map#'c``] known_correct_approx

val co_every_Fn_vs_NONE_def = Define `
  co_every_Fn_vs_NONE co =
    !n exp aux. SND (co n) = (exp, aux) ==>
      every_Fn_vs_NONE [exp] /\
      every_Fn_vs_NONE (MAP (SND o SND) aux)`

val co_every_Fn_vs_NONE_shift_seq =
  Q.store_thm("co_every_Fn_vs_NONE_shift_seq",
  `!co n. co_every_Fn_vs_NONE co ==> co_every_Fn_vs_NONE (shift_seq n co)`,
  rpt strip_tac \\ fs [co_every_Fn_vs_NONE_def, shift_seq_def] \\ metis_tac [])

val state_rel_co_set_globals = Q.store_thm("state_rel_co_set_globals",
  `state_rel l g s t /\ ssgc_free s /\ oracle_state_sgc_free s.compile_oracle ==>
     set_globals (FST (SND (t.compile_oracle n))) <= set_globals (FST (SND (s.compile_oracle n)))`,
  strip_tac \\ fs [state_rel_def]
  \\ fs [state_co_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rename1 `compile_inc _ _ p1 = (_, p2)`
  \\ PairCases_on `p1`
  \\ fs [compile_inc_def]
  \\ pairarg_tac \\ fs [] \\ rveq
  \\ imp_res_tac known_sing_EQ_E \\ rveq \\ fs []
  \\ drule known_elglobals_dont_grow \\ fs []
  \\ impl_tac \\ simp []
  \\ rename1 `s.compile_oracle nn = _`
  \\ fs [oracle_state_sgc_free_def]
  \\ qpat_x_assum `!n. globals_approx_sgc_free _` (qspec_then `nn` mp_tac) \\ simp []
  \\ fs [ssgc_free_def]
  \\ qpat_x_assum `!n e a. _` (qspec_then `nn` mp_tac) \\ simp []);

val state_rel_first_n_exps = Q.store_thm("state_rel_first_n_exps",
  `state_rel l g s t /\ ssgc_free s /\ oracle_state_sgc_free s.compile_oracle ==>
     elist_globals (first_n_exps t.compile_oracle n) <= elist_globals (first_n_exps s.compile_oracle n)`,
  strip_tac
  \\ imp_res_tac state_rel_co_set_globals
  \\ fs [first_n_exps_def] \\ Induct_on `n`
  \\ fs [GENLIST]
  \\ simp [SNOC_APPEND, elist_globals_append]
  \\ simp [SUB_BAG_UNION]);

val state_rel_unique_set_globals = Q.store_thm("state_rel_unique_set_globals",
  `!xs. state_rel l g s t /\ ssgc_free s /\ oracle_state_sgc_free s.compile_oracle /\
   unique_set_globals xs s.compile_oracle ==> unique_set_globals xs t.compile_oracle`,
  rpt strip_tac
  \\ imp_res_tac state_rel_first_n_exps
  \\ fs [unique_set_globals_def]
  \\ fs [elist_globals_append, BAG_ALL_DISTINCT_BAG_UNION]
  \\ gen_tac
  \\ rpt (qpat_x_assum `!n. _` (qspec_then `n` assume_tac))
  \\ fs []
  \\ imp_res_tac SUB_BAG_DIFF_EQ \\ pop_assum (fn th => fs [Once th])
  \\ fs [BAG_ALL_DISTINCT_BAG_UNION])

val state_rel_co_disjoint_globals = Q.store_thm("state_rel_co_disjoint_globals",
  `!g : val_approx num_map. state_rel l g0 s t /\ ssgc_free s /\ oracle_state_sgc_free s.compile_oracle /\
   co_disjoint_globals g s.compile_oracle ==> co_disjoint_globals g t.compile_oracle`,
  rpt strip_tac
  \\ imp_res_tac state_rel_co_set_globals
  \\ fs [co_disjoint_globals_def]
  \\ assume_tac (BAG_DISJOINT |> GSYM |> ISPEC ``BAG_OF_SET (domain (g : val_approx num_map))``)
  \\ fs [] \\ pop_assum kall_tac
  \\ gen_tac
  \\ rpt (qpat_x_assum `!n. _` (qspec_then `n` assume_tac))
  \\ imp_res_tac SUB_BAG_DIFF_EQ \\ pop_assum (fn th => fs [Once th]));

val state_rel_get_global_IMP = Q.store_thm("state_rel_get_global_IMP",
  `!l g s t n v1. state_rel l g s t /\ get_global n s.globals = SOME (SOME v1) ==>
   ?v2. get_global n t.globals = SOME (SOME v2) /\ v_rel l g v1 v2`,
  rw [state_rel_def, get_global_def, LIST_REL_EL_EQN]
  \\ metis_tac [OPTREL_SOME]);

val do_app_lemma = Q.prove(
  `!l g s t xs ys opp. state_rel l g s t /\ LIST_REL (v_rel l g) xs ys ==>
    case do_app opp xs s of
      | Rerr err1 => ?err2. do_app opp ys t = Rerr err2 /\
                            exc_rel (v_rel l g) err1 err2
      | Rval (x, s1) => ?y t1. v_rel l g x y /\ state_rel l g s1 t1 /\
                               do_app opp ys t = Rval (y, t1)`,
  rpt gen_tac
  \\ match_mp_tac simple_val_rel_do_app
  \\ conj_tac THEN1 (fs [simple_val_rel_def] \\ rw [] \\ fs [v_rel_cases])
  \\ fs [simple_state_rel_def, state_rel_def]
  \\ rw [] \\ fs [fmap_rel_def, FLOOKUP_DEF]
  \\ rfs []
  \\ TRY (first_x_assum drule \\ fs [ref_rel_cases])
  \\ fs [FAPPLY_FUPDATE_THM]
  \\ rw [] \\ fs [ref_rel_cases]);

(*
val evaluate_app_lemma = Q.store_thm(
  "evaluate_app_lemma",
  `evaluate_app app_lopt
     (Closure clos_lopt clos_args env arity body)
     args s0 = (res, s) /\ res <> Rerr (Rabort Rtype_error) ==>
     app_lopt = clos_lopt`,
  Cases_on `args` \\ simp [evaluate_def]
  \\ strip_tac

val v_caseT = v_case_eq |> INST_TYPE [alpha |-> bool] |> Q.INST [`v` |-> `T`]
                        |> REWRITE_RULE []
val optcaset = ``option$option_CASE``
val opt_caseT = case_eq_thms |> CONJUNCTS
                    |> List.find (fn th => th |> concl |> lhs |> lhs
                                              |> strip_comb
                                              |> #1 |> same_const optcaset)
                    |> valOf
                    |> INST_TYPE [beta |-> bool]
                    |> Q.INST [`v'` |-> `T`]
                    |> SIMP_RULE (srw_ss()) []


val loptrel_arg1_SOME = save_thm(
  "loptrel_arg1_SOME",
  loptrel_def |> SPEC_ALL |> Q.INST [`lopt1` |-> `SOME loc1`]
              |> SIMP_RULE (srw_ss()) [opt_caseT, v_caseT])

val loptrel_arg1_NONE = save_thm(
  "loptrel_arg1_NONE",
  loptrel_def |> SPEC_ALL |> Q.INST [`lopt1` |-> `NONE`]
              |> SIMP_RULE (srw_ss()) [opt_caseT, v_caseT])
*)

(*

WIP, probably missing some preconditions

val inline_lemma = Q.store_thm("inline_lemma",
  `!loc arity body f env. val_approx_val (Clos loc arity (SOME body)) f /\
   loptrel f arity lopt (SOME loc) /\
   evaluate_app lopt f args s0 = (res, s1) /\
   arity = LENGTH args /\
   1 <= arity ==>
   evaluate ([mk_Ticks tr trc arity body], args ++ env, s0) = (res, s1)`,

   \\ rw []
   \\ Cases_on `args` \\ fs [evaluate_def]
   \\ fs [loptrel_def] \\ rveq
   \\ fs [dest_closure_def, check_loc_def]
   \\ simp [evaluate_mk_Ticks_EQ]

   THEN1 (fs [bool_case_eq]
          \\ fs [pair_case_eq, result_case_eq]
          \\ imp_res_tac evaluate_SING \\ fs []
          \\ rveq \\ fs []

*)

val say = say0 "known_correct0";

val known_correct0 = Q.prove(
  `(!xs env1 (s0:(val_approx num_map#'c,'ffi) closSem$state) res1 s env2 t0 limit g0 g g' aenv eas.
      evaluate (xs, env1, s0) = (res1, s) /\
      known limit xs aenv g0 = (eas, g) /\
      LIST_REL (v_rel limit g') env1 env2 /\
      state_rel limit g' s0 t0 /\
      every_Fn_vs_NONE xs /\
      co_every_Fn_vs_NONE s0.compile_oracle /\
      EVERY esgc_free xs /\ ssgc_free s0 /\
      EVERY vsgc_free env1 /\
      subspt g0 g /\ subspt g g' /\
      LIST_REL val_approx_val aenv env2 /\
      oracle_state_sgc_free s0.compile_oracle /\
      globals_approx_sgc_free g0 /\
      state_globals_approx t0 g' /\
      EVERY val_approx_sgc_free aenv /\
      unique_set_globals xs s0.compile_oracle /\
      co_disjoint_globals g' s0.compile_oracle /\
      res1 <> Rerr (Rabort Rtype_error) ==>
      ?res2 t.
        evaluate (MAP FST eas, env2, t0) = (res2, t) /\
        result_rel (LIST_REL (v_rel limit g')) (v_rel limit g') res1 res2 /\
        state_rel limit g' s t) /\
   (!lopt1 f1 args1 (s0:(val_approx num_map#'c,'ffi) closSem$state) res1 s lopt2 f2 args2 t0 limit g.
      evaluate_app lopt1 f1 args1 s0 = (res1, s) /\
      ssgc_free s0 /\
      v_rel limit g f1 f2 /\ LIST_REL (v_rel limit g) args1 args2 /\
      state_rel limit g s0 t0 /\ state_globals_approx s0 g /\
      vsgc_free f1 /\ oracle_state_sgc_free s0.compile_oracle /\
      loptrel f2 (LENGTH args1) lopt1 lopt2 ==>
      ?res2 t.
        evaluate_app lopt2 f2 args2 t0 = (res2, t) /\
        result_rel (LIST_REL (v_rel limit g)) (v_rel limit g) res1 res2 /\
        state_rel limit g s t)`,

  ho_match_mp_tac (evaluate_ind |> Q.SPEC `\(x1,x2,x3). P0 x1 x2 x3`
                   |> Q.GEN `P0` |> SIMP_RULE std_ss [FORALL_PROD])
  \\ rpt strip_tac
  THEN1
   (say "NIL"
    \\ fs [known_def, evaluate_def] \\ rveq
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ simp [])
  THEN1
   (say "CONS"
    \\ fs [known_def, evaluate_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac unique_set_globals_subexps \\ fs []
    \\ fs [pair_case_eq]
    \\ patresolve `subspt g0 g` (el 3) subspt_known_elist_globals
    \\ rpt (disch_then drule)
    \\ impl_tac THEN1 (imp_res_tac unique_set_globals_IMP_es_distinct_elist_globals
                       \\ fs [BAG_ALL_DISTINCT_BAG_UNION])
    \\ strip_tac
    \\ rename1 `known _ [_] _ g0 = (_, g1)`
    \\ `subspt g1 g'` by metis_tac [subspt_trans]
    \\ first_x_assum drule
    \\ rpt (disch_then drule \\ simp [])
    \\ fs [result_case_eq] \\ rveq \\ fs []
    \\ strip_tac \\ simp [evaluate_append]
    \\ fs [pair_case_eq] \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ rpt (disch_then drule \\ simp [])
    \\ patresolve `evaluate ([_], _, _) = _` hd evaluate_changed_globals_inst
    \\ simp [] \\ strip_tac \\ fs []
    \\ fs [co_disjoint_globals_shift_seq,
           unique_set_globals_shift_seq,
           co_every_Fn_vs_NONE_shift_seq,
           oracle_state_sgc_free_shift_seq]
    \\ patresolve `known _ [_] _ _ = _` hd known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ patresolve `known _ [_] _ _ = _` hd known_correct_approx
    \\ disch_then drule \\ simp []
    \\ imp_res_tac known_sing_EQ_E \\ rveq \\ fs []
    \\ rename1 `known _ [_] _ g0 = ([(e1,a1)],g1)`
    \\ simp []
    \\ patresolve `LIST_REL _ env1 env2` hd v_rel_EVERY_vsgc_free
    \\ simp [] \\ strip_tac
    \\ qpat_x_assum `state_rel _ _ s0 _` assume_tac
    \\ drule state_rel_ssgc_free \\ simp []
    \\ strip_tac \\ fs []
    \\ disch_then (qpat_assum `state_globals_approx _ _` o mp_then Any mp_tac)
    \\ simp []
    \\ drule state_rel_unique_set_globals \\ simp []
    \\ disch_then kall_tac
    \\ drule state_rel_co_disjoint_globals \\ simp []
    \\ disch_then kall_tac
    \\ strip_tac \\ rveq \\ fs []
    \\ qpat_x_assum `state_rel _ _ s1 _` assume_tac
    \\ fs [result_case_eq] \\ rveq \\ fs []
    \\ strip_tac \\ simp [])
  THEN1
   (say "Var"
    \\ fs [known_def] \\ rveq \\ fs []
    \\ fs [evaluate_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs []
    \\ fs [bool_case_eq] \\ rveq
    \\ metis_tac [LIST_REL_EL_EQN])
  THEN1
   (say "If"
    \\ cheat)
  THEN1
   (say "Let"
    \\ cheat)
  THEN1
   (say "Raise"
    \\ fs [known_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, pair_case_eq, result_case_eq]
    \\ rveq \\ fs []
    \\ imp_res_tac unique_set_globals_subexps
    \\ first_x_assum drule
    \\ rpt (disch_then drule \\ simp [])
    \\ strip_tac
    \\ imp_res_tac known_sing_EQ_E \\ rveq \\ fs [] \\ rveq
    \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
    \\ imp_res_tac evaluate_SING \\ rveq \\ fs [])
  THEN1
   (say "Handle"
    \\ cheat)
  THEN1
   (say "Op"
    \\ fs [known_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ rename1 `known _ _ _ g0 = (_, g1)`
    \\ imp_res_tac unique_set_globals_subexps
    \\ drule subspt_known_op_elist_globals
    \\ rpt (disch_then drule)
    \\ impl_tac THEN1 (imp_res_tac unique_set_globals_IMP_es_distinct_elist_globals
                       \\ fs [BAG_ALL_DISTINCT_BAG_UNION])
    \\ strip_tac
    \\ `subspt g1 g'` by metis_tac [subspt_trans]
    \\ rename [`isGlobal opn`, `gO_destApx apx`]
    \\ fs [evaluate_def, pair_case_eq]
    \\ first_x_assum drule
    \\ rpt (disch_then drule \\ simp [])
    \\ reverse (fs [result_case_eq]) \\ rveq \\ fs []
    THEN1 (strip_tac \\ rveq \\ fs []
           \\ Cases_on `opn` \\ simp [isGlobal_def, evaluate_def]
           \\ Cases_on `apx` \\ simp [gO_destApx_def] \\ rveq
           \\ fs [known_op_def, NULL_EQ, bool_case_eq] \\ rveq
           \\ fs [evaluate_def])
    \\ strip_tac
    \\ Cases_on `opn = Install` \\ fs []
    THEN1 cheat
    \\ Cases_on `isGlobal opn /\ gO_destApx apx <> gO_None`
    THEN1
     (fs []
      \\ Cases_on `opn` \\ fs [isGlobal_def]
      \\ Cases_on `apx` \\ fs[gO_destApx_def] \\ rveq
      \\ fs [known_op_def, NULL_EQ, bool_case_eq] \\ rveq
      \\ imp_res_tac known_LENGTH_EQ_E \\ fs [LENGTH_NIL_SYM] \\ rveq
      \\ fs [evaluate_def, do_app_def] \\ rveq \\ fs []
      \\ fs [case_eq_thms, pair_case_eq] \\ rveq \\ fs [] \\ rveq
      \\ rename1 `lookup nn gg`
      \\ Cases_on `lookup nn gg` \\ fs [] \\ rveq
      \\ fs [state_globals_approx_def, subspt_def]
      \\ qmatch_asmsub_abbrev_tac `lookup nn gg = SOME apx`
      \\ `lookup nn g' = SOME apx` by metis_tac [domain_lookup]
      \\ drule state_rel_get_global_IMP
      \\ disch_then drule \\ strip_tac
      \\ res_tac
      \\ unabbrev_all_tac
      \\ fs [val_approx_val_def])
    THEN1
     (rename1 `Op tr opn (MAP FST ea1)`
      \\ qmatch_goalsub_abbrev_tac `evaluate ([opexp],_,_)`
      \\ `opexp = Op tr opn (MAP FST ea1)`
         by (Cases_on `isGlobal opn` \\ fs [] \\ rfs [])
      \\ pop_assum SUBST_ALL_TAC
      \\ qpat_x_assum `~(_ /\  _)` kall_tac
      \\ simp [evaluate_def]
      \\ qmatch_asmsub_abbrev_tac `do_app _ vvs _`
      \\ qmatch_goalsub_abbrev_tac `do_app _ wws _`
      \\ drule do_app_lemma
      \\ disch_then (qspecl_then [`vvs`, `wws`, `opn`] mp_tac)
      \\ impl_tac THEN1 metis_tac [EVERY2_REVERSE]
      \\ fs [case_eq_thms, pair_case_eq]
      \\ rveq \\ fs []
      \\ strip_tac \\ fs []))
  THEN1
   (say "Fn"
    \\ fs [known_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, bool_case_eq] \\ rveq
    \\ dsimp []
    \\ qexists_tac `aenv`
    \\ goal_assum (qpat_assum `LIST_REL val_approx_val _ _` o mp_then Any mp_tac)
    \\ conj_tac
    THEN1 fs [state_rel_def]
    THEN1 (simp [exp_rel_def, EVERY_REPLICATE]
           \\ imp_res_tac known_sing_EQ_E \\ rveq \\ fs [] \\ rveq
           \\ rpt (goal_assum drule)))
  THEN1
   (say "Letrec"
    \\ cheat)
  THEN1
   (say "App" \\ cheat)

(*
    \\ fs [known_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac unique_set_globals_subexps
    \\ imp_res_tac known_LENGTH_EQ_E
    \\ rename1 `known _ _ _ g0 = (_, g1)`
    \\ rename1 `known _ _ _ g1 = (_, g2)`
    \\ `g2 = g` by (fs [bool_case_eq, case_eq_thms]
                    \\ rpt (pairarg_tac \\ fs []))
    \\ rveq
    \\ patresolve `subspt g0 g` (el 3) subspt_known_elist_globals
    \\ rpt (disch_then drule)
    \\ impl_tac THEN1 (imp_res_tac unique_set_globals_IMP_es_distinct_elist_globals
                       \\ fs [BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
    \\ strip_tac
    \\ `subspt g1 g'` by metis_tac [subspt_trans]
    
    
    (* Cases split on annotate or inline *)
    \\ Cases_on `SND limit = 0 \/ body_opt = NONE`
    THEN1
     (rename1 `App tr new_loc_opt e1 (MAP FST ea2)`
      \\ `eas = [(App tr new_loc_opt e1 (MAP FST ea2),Other)]` by (fs [] \\ fs [])
      \\ qpat_x_assum `_ \/ _` kall_tac
      \\ qpat_x_assum `(if SND limit = 0 then _ else _) = _` kall_tac
      \\ rveq
      \\ fs [evaluate_def, bool_case_eq, pair_case_eq]
      \\ first_x_assum drule
      \\ rpt (disch_then drule \\ simp [])
      \\ fs [result_case_eq] \\ rveq \\ fs []
      \\ strip_tac \\ fs [] \\ rveq
      \\ fs [pair_case_eq]
      \\ first_x_assum drule
      \\ rpt (disch_then drule \\ simp [])
      \\ patresolve `evaluate (_, _, s0) = _` hd evaluate_changed_globals
      \\ simp [] \\ strip_tac \\ fs []
      \\ fs [co_disjoint_globals_shift_seq,
             unique_set_globals_shift_seq,
             co_every_Fn_vs_NONE_shift_seq,
             oracle_state_sgc_free_shift_seq]
      \\ patresolve `known _ _ _ g0 = _` hd known_preserves_esgc_free
      \\ simp [] \\ strip_tac
      \\ patresolve `known _ _ _ g0 = _` hd known_correct_approx
      \\ disch_then drule \\ simp []
      \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
      \\ patresolve `LIST_REL _ env1 env2` hd v_rel_EVERY_vsgc_free
      \\ simp [] \\ strip_tac
      \\ qpat_x_assum `state_rel _ _ s0 _` assume_tac
      \\ drule state_rel_ssgc_free \\ simp []
      \\ strip_tac
      \\ disch_then (qpat_assum `state_globals_approx _ _` o mp_then Any mp_tac)
      \\ simp []
      \\ drule state_rel_unique_set_globals \\ simp []
      \\ disch_then kall_tac
      \\ drule state_rel_co_disjoint_globals \\ simp []
      \\ disch_then kall_tac
      \\ strip_tac \\ rveq \\ fs []
      \\ qpat_x_assum `state_rel _ _ s1 _` assume_tac
      \\ cheat
      (* \\ drule state_rel_state_globals_approx \\ strip_tac \\ fs []
      \\ fs [result_case_eq] \\ fs [] \\ rveq
      \\ strip_tac \\ rveq \\ fs []
      \\ imp_res_tac evaluate_SING
      \\ rveq \\ fs []
      \\ patresolve `evaluate (_, _, s1) = _` hd evaluate_changed_globals_inst
      \\ simp [] \\ strip_tac \\ fs []
      \\ first_x_assum match_mp_tac \\ fs []
      \\ `oracle_state_sgc_free s2.compile_oracle` by fs [oracle_state_sgc_free_shift_seq]
      \\ rfs []
      \\ patresolve `known _ _ _ g1 = _` hd known_correct_approx
      \\ simp []
      \\ disch_then drule \\ simp []
      \\ disch_then (qspec_then `g'` mp_tac) \\ simp []
      \\ qpat_x_assum `state_rel _ _ s1 _` assume_tac
      \\ drule state_rel_ssgc_free
      \\ simp [oracle_state_sgc_free_shift_seq]
      \\ strip_tac
      \\ `oracle_state_sgc_free s1.compile_oracle` by fs [oracle_state_sgc_free_shift_seq]
      \\ `unique_set_globals [x1] s1.compile_oracle` by fs [unique_set_globals_shift_seq]
      \\ `co_disjoint_globals g' s1.compile_oracle` by fs [co_disjoint_globals_shift_seq]
      \\ rfs []
      \\ drule state_rel_unique_set_globals \\ simp []
      \\ disch_then kall_tac
      \\ drule state_rel_co_disjoint_globals \\ simp []
      \\ disch_then kall_tac
      \\ strip_tac
      \\ qpat_x_assum `state_rel _ _ s2 _` assume_tac
      \\ drule state_rel_state_globals_approx
      \\ strip_tac \\ simp []
      \\ rename1 `dest_Clos fapx`
      \\ Cases_on `dest_Clos fapx` \\ fs []
      THEN1 fs [loptrel_def] \\ rveq \\ fs []
      \\ Cases_on `lopt1` \\ fs []
      THEN1 (simp [loptrel_def]
             \\ rename1 `dest_Clos fapx = SOME clos_apx`
             \\ `?clos_loc clos_arity clos_body. clos_apx = (clos_loc, clos_arity, clos_body)`
                by (Cases_on `fapx` \\ fs [] \\ metis_tac [])
             \\ fs [bool_case_eq] \\ metis_tac [evaluate_IMP_LENGTH])
      \\ simp [loptrel_def]
      \\ fs [pair_case_eq, bool_case_eq]*))
    
    (* Inlining *)
    \\ cheat
    (*
    \\ fs []
    \\ `?body. body_opt = SOME body` by (Cases_on `body_opt` \\ fs [])
    \\ rveq \\ fs []
    \\ fs [evaluate_def]
    \\ Cases_on `LENGTH xs > 0` \\ fs []
    \\ fs [pair_case_eq]
    \\ Cases_on `dest_Clos a1` \\ fs []

    \\ reverse (Cases_on `pure x1`) \\ fs []
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ simp [evaluate_def]


    THEN1

      \\ simp [evaluate_append]

      \\ first_x_assum drule
      \\ rpt (disch_then drule \\ simp [])
      \\ fs [result_case_eq] \\ rveq \\ fs []
      \\ strip_tac \\ fs [] \\ rveq
      \\ fs [pair_case_eq] \\ rveq


      \\ simp [PULL_EXISTS]


      \\ simp [evaluate_mk_Ticks_EQ]


      \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq


      \\ first_x_assum drule
      \\ rpt (disch_then drule \\ simp [])

      \\ patresolve `evaluate (_, _, s0) = _` hd evaluate_changed_globals_inst
      \\ simp [] \\ strip_tac \\ fs []
      \\ fs [co_disjoint_globals_shift_seq,
             unique_set_globals_shift_seq,
             co_every_Fn_vs_NONE_shift_seq,
             oracle_state_sgc_free_shift_seq]
      \\ patresolve `known _ _ _ g0 = _` hd known_preserves_esgc_free
      \\ simp [] \\ strip_tac
      \\ patresolve `known _ _ _ g0 = _` hd known_correct_approx
      \\ disch_then drule \\ simp []
      \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
      \\ patresolve `LIST_REL _ env1 env2` hd v_rel_EVERY_vsgc_free
      \\ simp [] \\ strip_tac
      \\ patresolve `LIST_REL _ env1 env2` hd v_rel_LIST_REL_val_approx
      \\ strip_tac \\ fs []
      \\ qpat_x_assum `state_rel _ _ s0 _` assume_tac
      \\ drule state_rel_ssgc_free \\ simp []
      \\ strip_tac
      \\ drule state_rel_state_globals_approx
      \\ strip_tac \\ fs []
      \\ disch_then (qpat_assum `state_globals_approx _ _` o mp_then Any mp_tac)
      \\ simp []
      \\ drule state_rel_unique_set_globals \\ simp []
      \\ disch_then kall_tac
      \\ drule state_rel_co_disjoint_globals \\ simp []
      \\ disch_then kall_tac
      \\ strip_tac \\ rveq \\ fs []

      \\ qpat_x_assum `state_rel _ _ s1 _` assume_tac
      \\ drule state_rel_state_globals_approx \\ strip_tac \\ fs []
      \\ fs [result_case_eq] \\ fs [] \\ rveq
      \\ strip_tac \\ rveq \\ fs []
      \\ imp_res_tac evaluate_SING
      \\ rveq \\ fs []


      \\ patresolve `known _ _ _ g1 = _` hd known_preserves_esgc_free
      \\ simp [] \\ strip_tac

      \\ patresolve `known _ _ _ g1 = _` hd known_correct_approx
      \\ simp []
      \\ disch_then drule \\ simp []
      \\ disch_then (qspec_then `g'` mp_tac) \\ simp []


      \\ qpat_x_assum `state_rel _ _ s1 _` assume_tac
      \\ drule state_rel_ssgc_free \\ simp []
      \\ simp [oracle_state_sgc_free_shift_seq]
      \\ strip_tac
      \\ `oracle_state_sgc_free s1.compile_oracle` by simp [oracle_state_sgc_free_shift_seq]
      \\ `unique_set_globals [x1] s1.compile_oracle` by simp [unique_set_globals_shift_seq]
      \\ `co_disjoint_globals g' s1.compile_oracle` by simp [co_disjoint_globals_shift_seq]
      \\ rfs []
      \\ drule state_rel_unique_set_globals \\ simp []
      \\ disch_then kall_tac
      \\ drule state_rel_co_disjoint_globals \\ simp []
      \\ disch_then kall_tac
      \\ strip_tac


      \\ patresolve `evaluate (_, _, s1) = _` hd evaluate_changed_globals_inst
      \\ simp [] \\ strip_tac


      \\ first_x_assum drule
      \\ rpt (disch_then drule \\ simp [])


      \\ Cases_on `a1` \\ fs [] \\ rveq \\ fs []


      \\ known_preserves_ssgc_free
      \\ imp_res_tac unique_set_globals_shift_seq


    *)
*)


  THEN1
   (say "Tick"
    \\ fs [known_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, pair_case_eq]
    \\ `t0.clock = s0.clock` by fs [state_rel_def]
    \\ fs [bool_case_eq] \\ fixeqs
    \\ first_x_assum drule
    \\ rpt (disch_then drule \\ simp [])
    \\ disch_then (qspec_then `dec_clock 1 t0` mp_tac)
    \\ fs [dec_clock_def]
    \\ imp_res_tac unique_set_globals_subexps \\ simp []
    \\ impl_tac THEN1 fs [state_rel_def]
    \\ strip_tac
    \\ imp_res_tac known_sing_EQ_E
    \\ rveq \\ fs [] \\ rveq \\ fs [])

  THEN1
   (say "Call"
    \\ fs [known_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, pair_case_eq]
    \\ imp_res_tac unique_set_globals_subexps
    \\ first_x_assum drule
    \\ rpt (disch_then drule \\ simp [])
    \\ cheat
    (*
    \\ strip_tac \\ fs []
    \\ rename1 `state_rel _ _ sss t`
    \\ `sss.code = FEMPTY /\ t.code = FEMPTY` by fs [state_rel_def]
    \\ fs [find_code_def]
    \\ fs [result_case_eq]
    \\ rveq \\ fs []*))
  THEN1
   (say "evaluate_app NIL"
    \\ fs [evaluate_def] \\ rveq \\ fs [])
  THEN1
   (say "evaluate_app CONS"
    \\ cheat));



(*
  `(∀a es env1 env2 (s01:('a,'b) closSem$state) s02 res1 s1 g0 g g' as ealist.




       ⇒
      ∃res2 s2.
        evaluate(MAP FST ealist, env2, s02) = (res2, s2) ∧
        krrel g' (res1,s1) (res2,s2)) ∧
   (∀lopt1 f1 args1 (s01:('a,'b) closSem$state) res1 s1 lopt2 f2 args2 s02 g.
      evaluate_app lopt1 f1 args1 s01 = (res1,s1) ∧ ssgc_free s01 ∧
      kvrel g f1 f2 ∧ LIST_REL (kvrel g) args1 args2 ∧
      ksrel g s01 s02 ∧ state_globals_approx s01 g ∧ vsgc_free f1 ∧
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
      map_every rename1 [`ksrel g' s01 s02`, `subspt g g'`,
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
          >- (patresolve `known [gd] _ _ = _` hd (GEN_ALL kca_sing_sga) >>
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
      map_every rename1 [`known [bod] _ g1 = (_, g)`,
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
      map_every rename1 [`known _ (_ :: _) g1 = (_, g)`,
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
               (mp_then (Pos last) (mp_tac >~ (simp[] >> NO_TAC)) ssgc_evaluate)
          >- (patresolve `known _ _ g0 = _` hd (GEN_ALL kca_sing_sga) >>
              simp[] >> disch_then (resolve_selected last) >> simp[] >>
              metis_tac[ksrel_ssgc_free,kvrel_EVERY_vsgc_free,ksrel_sga,
                        kvrel_LIST_REL_val_approx]))
      >- (fs[krrel_err_rw, result_case_eq, error_case_eq] >> dsimp[] >>
          metis_tac[pair_CASES, result_CASES, error_CASES]))
  >- (say "op" >>
      simp[evaluate_def, pair_case_eq, result_case_eq, known_def,
           BAG_ALL_DISTINCT_BAG_UNION] >>
      rpt gen_tac >> strip_tac >> rpt gen_tac >>
      Cases_on `op = Install` >- cheat >>
      rpt (pairarg_tac >> fs[]) >>
      rename[`isGlobal opn`, `gO_destApx apx`] >>
      cheat (*
      Cases_on `isGlobal opn ∧ gO_destApx apx ≠ gO_None`
      >- (pop_assum strip_assume_tac >> simp[] >>
          Cases_on `opn` >> fs[isGlobal_def] >>
          Cases_on `apx` >> fs[gO_destApx_def] >> rveq >>
          fs[known_op_def, NULL_EQ, bool_case_eq, case_eq_thms] >> rveq >>
          imp_res_tac known_LENGTH_EQ_E >> fs[LENGTH_NIL_SYM] >> rveq >>
          simp[evaluate_def] >>
          rpt strip_tac >> rveq >> fs[evaluate_def, do_app_def, case_eq_thms] >>
          fs[state_globals_approx_def, subspt_def] >> rveq >> simp[] >>
          fs[known_def] >> rveq
          >- (rename[`lookup n g0 = SOME (Tuple tg [])`,
                     `kvrel g1 v (Block tg [])`] >>
              `lookup n g1 = SOME (Tuple tg [])` by metis_tac[domain_lookup] >>
              res_tac >> fs[] >> rveq >> fs[val_approx_val_def]) >>
          (* TODO: clos_known$ is only necessary because of HOL issue #430 *)
          rename[`lookup n g0 = SOME (clos_known$Int i)`, `kvrel g1 v (Number i)`] >>
          `lookup n g1 = SOME (Int i)` by metis_tac[domain_lookup] >>
          metis_tac[val_rel_def, val_approx_val_def, SOME_11]) >>
      rename[`closLang$Op tr opn (MAP FST es)`,
             `closSem$evaluate(MAP FST ealist,_,_)`] >>
      rpt strip_tac >>
      `ealist = [(Op tr opn (MAP FST es), apx)]`
         by (Cases_on `isGlobal opn` >> fs[] >>
             Cases_on `apx` >> fs[gO_destApx_def] >> every_case_tac >> fs[]) >>
      pop_assum SUBST_ALL_TAC >> rveq >>
      qpat_x_assum `¬(_ ∧ _)` kall_tac >> fs[] >>
      dsimp[evaluate_def, result_case_eq, pair_case_eq] >>
      sel_ihpc last >> simp[PULL_EXISTS] >>
      rpt (disch_then (resolve_selected last) >> simp[]) >>
      resolve_selected hd subspt_known_op_elist_globals >> simp[] >>
      rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
      (impl_keep_tac >- metis_tac[subspt_trans])
      >- ((* args evaluate OK, do_app evaluates OK *)
          metis_tac[kvrel_op_correct_Rval, EVERY2_REVERSE])
      >- ((* args evaluate OK, do_app errors *)
          rw[] >> imp_res_tac do_app_EQ_Rerr >> rw[] >>
          metis_tac[result_CASES, pair_CASES])
      >- ((* args error *) rw[] >> fs[krrel_err_rw] >>
         metis_tac[result_CASES, pair_CASES]) *))
  >- (say "fn" >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           known_def, bool_case_eq, case_eq_thms] >> rpt strip_tac >> rveq >> fs[] >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac state_rel_max_app >> fs[] >>
      dsimp[evaluate_def, case_eq_thms] >> imp_res_tac known_sing_EQ_E >> rveq >> fs[] >>
      rveq >>
      simp[exp_rel_def, PULL_EXISTS] >> metis_tac[kvrel_LIST_REL_val_approx])
  >- (say "letrec" >>
      simp[evaluate_def, pair_case_eq, result_case_eq, known_def, bool_case_eq,
           case_eq_thms] >> rpt strip_tac >> rveq >> fs[letrec_case_eq] >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      fs[BAG_ALL_DISTINCT_BAG_UNION] >>
      imp_res_tac state_rel_max_app >> fs[] >>
      simp[evaluate_def, case_eq_thms, bool_case_eq] >> dsimp[] >>
      simp[EVERY_MAP, EXISTS_MAP]
      >- (disj1_tac >> simp[EVERY_MEM, FORALL_PROD] >>
          imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
          sel_ihpc last >> simp[EVERY_GENLIST] >>
          rpt (disch_then (resolve_selected last) >> simp[]) >>
          rename1 `BAG_ALL_DISTINCT (elist_globals (MAP SND fns1))` >>
          `∀n e. MEM (n,e) fns1 ⇒ n ≤ s02.max_app ∧ n ≠ 0`
            by fs[EVERY_MEM, FORALL_PROD] >> simp[] >> strip_tac >>
          simp[GSYM PULL_EXISTS] >> simp[Once EQ_SYM_EQ] >>
          imp_res_tac LIST_REL_LENGTH >> fs[] >>
          first_x_assum irule
          >- (simp[LIST_REL_EL_EQN, EL_APPEND_EQN] >> qx_gen_tac `mm` >>
              strip_tac >> rw[]
              >- (fs[Once every_Fn_vs_NONE_EVERY] >>
                  fs[EVERY_MAP] >> fs[EVERY_MEM, FORALL_PROD] >>
                  metis_tac[])
              >- (rename1 `LIST_REL val_approx_val apxs env1` >>
                  qexists_tac `apxs` >> conj_tac
                  >- metis_tac[kvrel_LIST_REL_val_approx] >>
                  simp[LIST_REL_EL_EQN, EL_MAP] >>
                  qx_gen_tac `nn` >> strip_tac >> pairarg_tac >>
                  simp[] >> simp[exp_rel_def] >>
                  map_every rename1 [`ksrel gg ss1 ss2`, `subspt g gg`,
                                       `subspt g0 g`] >>
                  ntac 2 (qexists_tac `g0`) >> simp[] >>
                  rename1 `known [e1] env g0` >>
                  Cases_on `known [e1] env g0` >>
                  imp_res_tac known_sing_EQ_E >> fs[] >> rveq >>
                  conj_tac >- metis_tac[subspt_trans] >>
                  rename1 `known [subexp] env g0 = _` >>
                  `elist_globals [subexp] = {||}`
                    suffices_by metis_tac[known_emptySetGlobals_unchanged_g] >>
                  fs[elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
                  metis_tac[MEM_EL])
              >- fs[LIST_REL_EL_EQN])
          >- (irule EVERY2_APPEND_suff >> simp[] >>
              simp[LIST_REL_GENLIST] >> qx_gen_tac `ii` >> strip_tac >>
              rename1 `option_CASE lloc` >> Cases_on `lloc` >> simp[])) >>
      disj2_tac >> fs[EXISTS_MEM, EXISTS_PROD] >> metis_tac[])
  >- (say "app" >>
      rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           bool_case_eq, known_def, BAG_ALL_DISTINCT_BAG_UNION] >>
      rpt strip_tac >> rveq >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      map_every imp_res_tac [known_sing_EQ_E, evaluate_SING] >> rveq >> fs[] >>
      rveq
      >- (map_every rename1 [
            `known [fexp] apxs g1 = ([(fexp',fapx)], g)`,
            `known args apxs g0 = (alist, g1)`,
            `subspt g gg`] >>
          patresolve `known [_] _ _ = _` (el 2) subspt_known_elist_globals >>
          simp[] >> disch_then (resolve_selected (el 1)) >> simp[] >>
          impl_tac >- fs[BAG_DISJOINT, DISJOINT_SYM] >> strip_tac >>
          first_x_assum (patresolve `known args _ _ = _` last) >> simp[] >>
          `subspt g1 gg` by metis_tac[subspt_trans] >>
          rpt (disch_then (resolve_selected last) >> simp[]) >> rw[] >>
          simp[evaluate_def] >> imp_res_tac known_LENGTH_EQ_E >> fs[] >>
          first_x_assum (patresolve `known [_] _ _ = _` last) >> simp[] >>
          disch_then (resolve_selected (el 2)) >> simp[] >>
          disch_then (resolve_selected hd) >> simp[] >>
          resolve_selected hd ssgc_evaluate >> simp[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          impl_keep_tac
          >- (patresolve `closSem$evaluate (MAP FST _, _, _) = _` last
                         known_correct_approx >>
              simp[] >> disch_then (resolve_selected hd) >> simp[] >>
              metis_tac[ksrel_ssgc_free,kvrel_EVERY_vsgc_free,ksrel_sga,
                        kvrel_LIST_REL_val_approx]) >>
          rw[] >> simp[] >>
          rename1 `evaluate_app loption1 v1 vs1 s21 = (result,ss1)` >>
          `ssgc_free s21`
            by metis_tac[ksrel_ssgc_free, ssgc_free_preserved_SING'] >> fs[] >>
          first_x_assum (resolve_selected hd) >> simp[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          `state_globals_approx s21 gg`
            by (patresolve `known [_] _ _ = _` hd known_correct_approx >>
                simp[] >> disch_then (resolve_selected last) >> simp[] >>
                metis_tac[ksrel_ssgc_free,kvrel_EVERY_vsgc_free,ksrel_sga,
                          kvrel_LIST_REL_val_approx]) >> fs[] >>
          `vsgc_free v1`
            by (patresolve `closSem$evaluate ([_],_,_) = (Rval [v1],_)` last
                           ssgc_evaluate >> simp[]) >> fs[] >>
          reverse (Cases_on `loption1`) >> simp[]
          >- (first_x_assum irule >> simp[loptrel_def]) >>
          rename1 `dest_Clos fapprox` >> Cases_on `dest_Clos fapprox` >>
          simp[]
          >- (first_x_assum irule >> simp[loptrel_def]) >>
          rename1 `dest_Clos fapprox = SOME closapxvalue` >>
          `∃clloc clarity. closapxvalue = (clloc, clarity)`
            by metis_tac[pair_CASES] >> pop_assum SUBST_ALL_TAC >>
          simp[] >> rename1 `LENGTH args > 0` >>
          reverse (Cases_on `clarity = LENGTH args`) >> simp[]
          >- (first_x_assum irule >> simp[loptrel_def]) >>
          first_x_assum irule >> simp[loptrel_def] >>
          qspecl_then [`[fexp]`, `apxs`, `g1`, `[(fexp',fapprox)]`, `g`]
             mp_tac known_correct_approx >> simp[] >>
          disch_then (resolve_selected last) >> simp[] >>
          disch_then (qspec_then `gg` mp_tac) >> impl_tac
          >- metis_tac[kvrel_LIST_REL_val_approx, ksrel_ssgc_free,
                       kvrel_EVERY_vsgc_free, ksrel_sga] >>
          fs[dest_Clos_eq_SOME] >> rveq >> rw[] >> simp[] >>
          metis_tac[evaluate_length_imp])
      >- (map_every rename1 [
            `known [fexp] apxs g1 = ([(fexp',fapx)], g)`,
            `known args apxs g0 = (alist, g1)`,
            `subspt g gg`] >>
          patresolve `known [_] _ _ = _` (el 2) subspt_known_elist_globals >>
          simp[] >> disch_then (resolve_selected (el 1)) >> simp[] >>
          impl_tac >- fs[BAG_DISJOINT, DISJOINT_SYM] >> strip_tac >>
          first_x_assum (patresolve `known args _ _ = _` last) >> simp[] >>
          `subspt g1 gg` by metis_tac[subspt_trans] >>
          rpt (disch_then (resolve_selected last) >> simp[]) >> rw[] >>
          simp[evaluate_def] >> imp_res_tac known_LENGTH_EQ_E >> fs[] >>
          sel_ihpc last >> simp[] >>
          disch_then (resolve_selected (el 2)) >> simp[] >>
          disch_then (resolve_selected hd) >> simp[] >> reverse impl_tac
          >- (rw[] >> simp[] >> fs[krrel_err_rw] >>
              dsimp[result_case_eq] >> metis_tac[pair_CASES, result_CASES]) >>
          conj_tac
          >- (patresolve `closSem$evaluate (MAP FST _, _, _) = _` last
                         known_correct_approx >>
              simp[] >> disch_then (resolve_selected hd) >> simp[] >>
              metis_tac[ksrel_ssgc_free,kvrel_EVERY_vsgc_free,ksrel_sga,
                        kvrel_LIST_REL_val_approx]) >>
          metis_tac [ssgc_evaluate])
      >- (map_every rename1 [
            `known [fexp] apxs g1 = ([(fexp',fapx)], g)`,
            `known args apxs g0 = (alist, g1)`,
            `subspt g gg`] >>
          patresolve `known [_] _ _ = _` (el 2) subspt_known_elist_globals >>
          simp[] >> disch_then (resolve_selected (el 1)) >> simp[] >>
          impl_tac >- fs[BAG_DISJOINT, DISJOINT_SYM] >> strip_tac >>
          first_x_assum (patresolve `known args _ _ = _` last) >> simp[] >>
          `subspt g1 gg` by metis_tac[subspt_trans] >> strip_tac >>
          nailIHx strip_assume_tac >>
          simp[evaluate_def, bool_case_eq, result_case_eq, pair_case_eq] >>
          imp_res_tac known_LENGTH_EQ_E >> rveq >> fs[] >>
          fs[krrel_err_rw] >> dsimp[] >>
          metis_tac[result_CASES,pair_CASES])
      >- (map_every imp_res_tac [evaluate_IMP_LENGTH, known_LENGTH_EQ_E] >>
          fs[] >> rw[] >> simp[evaluate_def]))
  >- (say "tick" >> simp[dec_clock_def] >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, bool_case_eq, known_def] >>
      rename1 `(s0:('a,'b) closSem$state).clock = 0` >> Cases_on `s0.clock = 0` >>
      fs[] >> rpt strip_tac >> rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      simp[evaluate_def] >- fs[ksrel_def] >>
      fs[dec_clock_def] >> fixeqs >> imp_res_tac known_sing_EQ_E >> rveq >>
      fs[] >> rveq >>
      map_every rename1 [
        `known [exp1] apxs g0 = ([(exp2,apx)],g)`,
        `evaluate([exp1],env1,s01 with clock := s01.clock - 1) = (res1,s1)`,
        `ksrel gg s01 s02`] >>
      sel_ihpc last >> simp[] >>
      disch_then
        (qspecl_then [`env2`, `s02 with clock := s02.clock - 1`, `gg`]
                     mp_tac) >>
      simp[] >> impl_keep_tac >- fs[ksrel_def] >>
      `s02.clock = s01.clock` by fs[ksrel_def] >> simp[])
  >- (say "call" >>
      simp[evaluate_def, pair_case_eq, result_case_eq, case_eq_thms, bool_case_eq,
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
          dsimp[result_case_eq, case_eq_thms, pair_case_eq, bool_case_eq] >>
          metis_tac[option_CASES, pair_CASES, result_CASES]))
  >- (say "evaluate_app(nil)" >> simp[evaluate_def])
  >- (say "evaluate_app(cons)" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq, result_case_eq] >>
      rpt strip_tac >> rveq >> fs[]
      >- metis_tac[pair_CASES]
      >- (simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq] >>
          resolve_selected hd (GEN_ALL kvrel_dest_closure_SOME_Partial) >>
          simp[PULL_EXISTS] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >>
          strip_tac >> simp[] >> fs[ksrel_def])
      >- (simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq] >>
          resolve_selected hd (GEN_ALL kvrel_dest_closure_SOME_Partial) >>
          simp[PULL_EXISTS] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          simp[] >> fs[ksrel_def, dec_clock_def])
      >- (simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq] >>
          resolve_selected hd (GEN_ALL kvrel_dest_closure_SOME_Full) >>
          simp[PULL_EXISTS] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          simp[] >> imp_res_tac LIST_REL_LENGTH >> fs[ksrel_def])
      >- (simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq] >>
          resolve_selected hd (GEN_ALL kvrel_dest_closure_SOME_Full) >>
          simp[PULL_EXISTS] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          simp[] >> rename1 `ksrel g s01 s02` >>
          `s02.clock = s01.clock` by fs[ksrel_def] >>
          `s02.max_app = s01.max_app` by fs[ksrel_def] >>
          imp_res_tac LIST_REL_LENGTH >> fs[] >> simp[PULL_EXISTS] >>
          dsimp[] >> fs[PULL_EXISTS] >>
          map_every rename1 [
            `dest_closure _ lopt1 f1 (iarg1 :: iargs) =
               SOME (Full_app exp1 env1 args1)`,
            `evaluate([exp1],env1,dec_clock _ s01) = (Rval [v1], s11)`,
            `kerel envapx gg exp1 exp2`] >> fs[exp_rel_def] >>
          rpt disj1_tac >>
          first_x_assum (patresolve `known [exp1] _ _ = _` last) >> simp[] >>
          map_every rename1 [
            `evaluate([exp1],env1,
                      dec_clock (SUC (LENGTH iargs1) - LENGTH args2) s01)`,
            `LIST_REL (kvrel gg) env1 env2`] >>
          disch_then (qspecl_then [
             `env2`,
             `dec_clock (SUC (LENGTH iargs1) - LENGTH args2) s02`,
             `gg`] mp_tac) >> simp[] >>
          `set_globals exp1 = {||} ∧ EVERY vsgc_free env1 ∧
           EVERY vsgc_free args1 ∧ esgc_free exp1`
            by metis_tac[vsgc_free_Full_app_set_globals, EVERY_DEF,
                         set_globals_empty_esgc_free] >> simp[] >>
          qspec_then `[exp1]` mp_tac known_emptySetGlobals_unchanged_g >>
          disch_then (resolve_selected hd) >> simp[] >>
          disch_then SUBST_ALL_TAC >>
          rename1 `LIST_REL val_approx_val envapx env1` >>
          `LIST_REL val_approx_val envapx env1`
            by metis_tac[kvrel_LIST_REL_val_approx] >>
          `every_Fn_vs_NONE [exp1]`
            by metis_tac[kvrel_dest_closure_every_Fn_vs_NONE] >>
          impl_tac >- (simp[] >> fs[ksrel_def, dec_clock_def]) >> rw[] >>
          simp[] >>
          rename1 `loptrel f2 _ lopt1 lopt2` >>
          reverse (Cases_on `lopt1`)
          >- (fs[loptrel_arg1_SOME] >> rveq >>
              imp_res_tac dest_closure_SOME_Full_app_args_nil >> fs[] >>
              rveq >> simp[]) >>
          qpat_x_assum `loptrel _ _ _ _` mp_tac >>
          simp[loptrel_arg1_NONE] >> reverse strip_tac >> rveq
          >- (imp_res_tac dest_closure_SOME_Full_app_args_nil >> fs[] >>
              rveq >> simp[])
          >- (imp_res_tac dest_closure_SOME_Full_app_args_nil >> fs[] >>
              rveq >> simp[]) >>
          first_x_assum irule >> simp[]
          >- metis_tac[ssgc_free_preserved_SING', ssgc_free_dec_clock]
          >- (patresolve `evaluate([exp1],_,_) = _` last ssgc_evaluate >>
              simp[])
          >- (patresolve `known [exp1] _ _ = _` hd known_correct_approx >>
              simp[] >> disch_then (resolve_selected last) >> simp[] >>
              metis_tac[ksrel_sga, ksrel_ssgc_free, kvrel_EVERY_vsgc_free])
          >- simp[loptrel_def])
      >- (imp_res_tac evaluate_SING >> fs[])
      >- (simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq] >>
          resolve_selected hd (GEN_ALL kvrel_dest_closure_SOME_Full) >>
          simp[PULL_EXISTS] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          simp[] >> rename1 `ksrel g s01 s02` >>
          `s02.clock = s01.clock` by fs[ksrel_def] >>
          imp_res_tac LIST_REL_LENGTH >> fs[] >> simp[PULL_EXISTS] >>
          dsimp[] >>
          map_every rename1 [
            `dest_closure _ lopt1 f1 (iarg1 :: iargs) =
               SOME (Full_app exp1 env1 args1)`,
            `evaluate([exp1],env1,dec_clock _ s01) = (Rerr err1, s1)`,
            `kerel envapx gg exp1 exp2`] >> fs[exp_rel_def] >>
          first_x_assum (patresolve `known [exp1] _ _ = _` last) >> simp[] >>             map_every rename1 [
            `evaluate([exp1],env1,
                      dec_clock (SUC (LENGTH iargs1) - LENGTH args2) s01)`,
            `LIST_REL (kvrel gg) env1 env2`] >>
          disch_then (qspecl_then [
             `env2`,
             `dec_clock (SUC (LENGTH iargs1) - LENGTH args2) s02`,
             `gg`] mp_tac) >> simp[] >>
          `set_globals exp1 = {||} ∧ EVERY vsgc_free env1 ∧
           EVERY vsgc_free args1 ∧ esgc_free exp1`
            by metis_tac[vsgc_free_Full_app_set_globals, EVERY_DEF,
                         set_globals_empty_esgc_free] >> simp[] >>
          qspec_then `[exp1]` mp_tac known_emptySetGlobals_unchanged_g >>
          disch_then (resolve_selected hd) >> simp[] >>
          disch_then SUBST_ALL_TAC >>
          rename1 `LIST_REL val_approx_val envapx env1` >>
          `LIST_REL val_approx_val envapx env1`
            by metis_tac[kvrel_LIST_REL_val_approx] >>
          `every_Fn_vs_NONE [exp1]`
            by metis_tac[kvrel_dest_closure_every_Fn_vs_NONE] >>
          impl_tac >- (simp[] >> fs[ksrel_def, dec_clock_def]) >> rw[] >>
          imp_res_tac state_rel_max_app >>
          simp[] >> fs[krrel_err_rw] >>
          rename1 `evaluate([exp2],_,_) = (res2,_)` >>
          Cases_on `res2`
          >- (imp_res_tac evaluate_SING >> simp[] >> metis_tac[pair_CASES]) >>
          simp[])))





(*******************************************************)


(* TODO: MOVE candidates *)
fun sel_ihpc f = first_x_assum (first_assum o mp_then (Pos f) mp_tac)
fun resolve_selected f th = first_assum (mp_then (Pos f) mp_tac th)

fun patresolve p f th = Q.PAT_ASSUM p (mp_then (Pos f) mp_tac th)

(* repeated resolution, requiring that all preconditions get removed *)
fun nailIHx k =
  first_x_assum
    (REPEAT_GTCL
       (fn ttcl => fn th => first_assum (mp_then (Pos hd) ttcl th))
       (k o assert (not o is_imp o #2 o strip_forall o concl)) o
     assert (is_imp o #2 o strip_forall o concl))

infix >~
fun (f >~ g) th = f th >> g

(* TODO: MOVE-HOL candidate; unused here *)
val union_idem = Q.store_thm(
  "union_idem[simp]",
  `∀spt. union spt spt = spt`,
  Induct >> simp[union_def]);

val FINITE_BAG_FOLDR = Q.store_thm(
  "FINITE_BAG_FOLDR",
  `∀l f a.
     FINITE_BAG a ∧ (∀e a. FINITE_BAG a ∧ MEM e l ⇒ FINITE_BAG (f e a)) ⇒
     FINITE_BAG (FOLDR f a l)`,
  Induct >> simp[]);

val FINITE_set_globals = Q.store_thm(
  "FINITE_set_globals[simp]",
  `(∀e. FINITE_BAG (set_globals e)) ∧ ∀es. FINITE_BAG (elist_globals es)`,
  ho_match_mp_tac set_globals_ind >> simp[] >> rpt strip_tac >>
  rename1 `op_gbag opn` >> Cases_on `opn` >> simp[op_gbag_def]);

val state_approx_better_definedg = Q.store_thm(
  "state_approx_better_definedg",
  `better_definedg g1 g2 ∧ state_globals_approx s g1 ⇒
   state_globals_approx s g2`,
  csimp[better_definedg_def, state_globals_approx_def, domain_lookup,
        PULL_EXISTS] >>
  metis_tac[val_approx_better_approx]);

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




val lem = Q.prove(
  `(∀a es env (s0:('a,'b) closSem$state) res s.
      a = (es,env,s0) ∧ evaluate(es,env,s0) = (res,s) ⇒
      mapped_globals s0 ⊆ mapped_globals s) ∧
   (∀lopt f args (s0:('a,'b) closSem$state) res s.
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
      rename1 `closSem$do_app opn` >>
      Cases_on `opn = Install` THEN1
       (rveq \\ fs []
        \\ reverse (Cases_on `do_install (REVERSE vs) s''`) \\ fs []
        \\ reverse (Cases_on `q`) \\ fs []
        THEN1 (Cases_on `e` \\ rveq \\ fs []
               \\ imp_res_tac do_install_not_Rraise \\ fs []
               \\ fs [do_install_def]
               \\ fs [case_eq_thms] \\ rveq \\ fs []
               \\ pairarg_tac \\ fs []
               \\ fs [case_eq_thms,bool_case_eq,pair_case_eq]
               \\ fs [case_eq_thms] \\ rveq \\ fs []
               \\ fs [mapped_globals_def])
        \\ pop_assum mp_tac
        \\ fs [do_install_def]
        \\ fs [case_eq_thms]
        \\ strip_tac \\ pairarg_tac \\ fs []
        \\ fs [case_eq_thms,bool_case_eq,pair_case_eq]
        \\ rveq \\ fs []
        \\ fs [mapped_globals_def]
        \\ match_mp_tac SUBSET_TRANS \\ asm_exists_tac \\ fs []) >>
      Cases_on `opn` >>
      fs[do_app_def, case_eq_thms, bool_case_eq, pair_case_eq] >> rw[] >>
      fs[]
      >- (rename1 `closSem$evaluate(_,_,s0) = (_, s1)` >>
          irule SUBSET_TRANS >> qexists_tac `mapped_globals s1` >> simp[] >>
          simp[mapped_globals_def] >>
          fs[SUBSET_DEF, PULL_EXISTS, get_global_def,
             EL_LUPDATE, bool_case_eq] >> metis_tac[])
      >- (simp[mapped_globals_def, SUBSET_DEF, get_global_def,
               EL_APPEND_EQN, bool_case_eq] >> rpt strip_tac >>
          simp[]))
  >- fs[evaluate_def, bool_case_eq, case_eq_thms]
  >- (fs[case_eq_thms, PULL_EXISTS] >> rveq >> fs[])
  >- (fs[pair_case_eq, result_case_eq] >> rveq >> fs[] >>
      metis_tac[SUBSET_TRANS])
  >- (fs[pair_case_eq, result_case_eq, case_eq_thms, bool_case_eq] >> rveq >> fixeqs >>
      fs[] >> metis_tac[SUBSET_TRANS])
  >- (fs[case_eq_thms, bool_case_eq, pair_case_eq] >> rveq >> fs[] >>
      metis_tac[SUBSET_TRANS]));

val mapped_globals_grow = save_thm(
  "mapped_globals_grow",
  lem |> CONJUNCT1 |> SIMP_RULE bool_ss [])

fun say0 pfx s g = (print (pfx ^ ": " ^ s ^ "\n"); ALL_TAC g)
val say = say0 "ssgc_evaluate0"

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

val LENGTH_clos_gen = Q.prove(`
  ∀ls x c.
  LENGTH (clos_gen x c ls) = LENGTH ls`,
  Induct>>fs[FORALL_PROD,clos_gen_def])

val clos_gen_eq = Q.prove(`
  ∀n c fns.
  clos_gen n c fns =
  GENLIST (λi. Clos (2* (i+c) +n ) (FST (EL i fns))) (LENGTH fns)`,
  Induct_on`fns`>>fs[FORALL_PROD,clos_gen_def,GENLIST_CONS]>>rw[]>>
  simp[o_DEF,ADD1])

val letrec_case_eq = Q.prove(`
  (case loc of
    NONE => REPLICATE (LENGTH fns) Other
  | SOME n => clos_gen n 0 fns) =
  GENLIST (case loc of NONE => K Other | SOME n => λi. Clos (n+ 2*i) (FST (EL i fns))) (LENGTH fns)`,
  Cases_on`loc`>>fs[clos_gen_eq,REPLICATE_GENLIST])

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

val exp_rel_def = Define`
  exp_rel as g' e1 e2 ⇔
    ∃g0 g apx. subspt g g' ∧ known [e1] as g0 = ([(e2,apx)], g)
`;
val _ = temp_overload_on ("kerel", ``clos_knownProof$exp_rel``)

val val_rel_def = tDefine "val_rel" `
  (val_rel g (Number i) v ⇔ v = Number i) ∧
  (val_rel g (Word64 w) v ⇔ v = Word64 w) ∧
  (val_rel g (Block n vs) v ⇔
     ∃vs'. v = Block n vs' ∧ LIST_REL (val_rel g) vs vs') ∧
  (val_rel g (ByteVector ws) v ⇔ v = ByteVector ws) ∧
  (val_rel g (RefPtr n) v ⇔ v = RefPtr n) ∧
  (val_rel g (Closure lopt vs1 env1 n bod1) v ⇔
     every_Fn_vs_NONE [bod1] ∧
     ∃vs2 env2 bod2 eapx.
       LIST_REL (val_rel g) vs1 vs2 ∧ LIST_REL (val_rel g) env1 env2 ∧
       LIST_REL val_approx_val eapx env2 ∧
       kerel (REPLICATE n Other ++ eapx) g bod1 bod2 ∧
       v = Closure lopt vs2 env2 n bod2) ∧
  (val_rel g (Recclosure lopt vs1 env1 fns1 i) v ⇔
     EVERY (λ(n,e). every_Fn_vs_NONE [e]) fns1 ∧
     let gfn = case lopt of
                 | NONE => K Other
                 | SOME n => (λi. Clos (n + 2*i) (FST (EL i fns1))) in
     let clos = GENLIST gfn (LENGTH fns1)
     in
       ∃vs2 env2 fns2 eapx.
         LIST_REL (val_rel g) vs1 vs2 ∧ LIST_REL (val_rel g) env1 env2 ∧
         LIST_REL val_approx_val eapx env2 ∧
         LIST_REL (λ(n1,e1) (n2,e2).
                     n1 = n2 ∧
                     kerel (REPLICATE n1 Other ++ clos ++ eapx) g e1 e2)
                  fns1 fns2 ∧
         v = Recclosure lopt vs2 env2 fns2 i)
` (WF_REL_TAC `measure (v_size o FST o SND)` >> simp[v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[])
val val_rel_ind = theorem "val_rel_ind"
val val_rel_def = save_thm(
  "val_rel_def[simp]",
  SIMP_RULE (bool_ss ++ ETA_ss) [] val_rel_def)

val _ = temp_overload_on ("kvrel", ``clos_knownProof$val_rel``)

(* necessary kvrel *)
val kvrel_vsgc_free = Q.store_thm(
  "kvrel_vsgc_free",
  `∀g v1 v2. kvrel g v1 v2 ⇒ (vsgc_free v1 ⇔ vsgc_free v2)`,
  ho_match_mp_tac val_rel_ind >> simp[] >> rpt strip_tac
  >- (fs[EVERY_MEM, LIST_REL_EL_EQN] >> metis_tac[MEM_EL])
  >- (fs[EVERY_MEM, LIST_REL_EL_EQN] >>
      fs[exp_rel_def] >> imp_res_tac known_preserves_setGlobals >>
      fs[] >> metis_tac[MEM_EL])
  >- (fs[EVERY_MEM, LIST_REL_EL_EQN, elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS,
         FORALL_PROD]>>
      EQ_TAC >> rpt strip_tac
      >- (imp_res_tac (MEM_EL |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GSYM) >>
          rename1 `m < LENGTH fns2` >>
          Cases_on `EL m fns1` >> fs[] >>
          first_x_assum (qspec_then `m` mp_tac) >> simp[] >>
          rw[exp_rel_def] >>
          imp_res_tac known_preserves_setGlobals >> fs[] >>
          metis_tac[MEM_EL])
      >- metis_tac[MEM_EL]
      >- metis_tac[MEM_EL]
      >- (imp_res_tac (MEM_EL |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GSYM) >>
          rename1 `m < LENGTH fns1` >>
          Cases_on `EL m fns2` >> fs[] >>
          first_x_assum (qspec_then `m` mp_tac) >> simp[] >>
          rw[exp_rel_def] >>
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
  ho_match_mp_tac val_rel_ind >> rw[]
  >- (Cases_on `a` >> simp[] >> fs[LIST_REL_EL_EQN] >> metis_tac[MEM_EL])
  >- (Cases_on `a` >> simp[] >> fs[LIST_REL_EL_EQN] >> metis_tac[LENGTH_NIL])
  >- (Cases_on `a` >> fs[LIST_REL_EL_EQN] >> rename1 `lopt = SOME _` >>
      Cases_on `lopt` >> simp[] >> rename1 `EL j` >>
      rename1 `j < LENGTH fns2` >> Cases_on `j < LENGTH fns2` >> simp[] >>
      rename1 `vvs = []` >> reverse (Cases_on `vvs`)
      >- (simp[] >> rename1 `vvs' = []` >> Cases_on `vvs'` >> fs[]) >>
      fs[LENGTH_NIL, LENGTH_NIL_SYM] >> rfs[] >> res_tac >>
      fs[UNCURRY]))

val kvrel_LIST_REL_val_approx = Q.store_thm(
  "kvrel_LIST_REL_val_approx",
  `∀vs1 vs2.
      LIST_REL (kvrel g) vs1 vs2 ⇒
      ∀as. LIST_REL val_approx_val as vs1 ⇔ LIST_REL val_approx_val as vs2`,
  Induct_on `LIST_REL` >> simp[] >> metis_tac[kvrel_val_approx]);

val state_rel_def = Define`
  state_rel g (s1:('a,'b) closSem$state) (s2:('a,'b) closSem$state) ⇔
     s2.clock = s1.clock ∧ s2.ffi = s1.ffi ∧ s2.max_app = s1.max_app ∧
     LIST_REL (OPTREL (kvrel g)) s1.globals s2.globals ∧
     fmap_rel (ref_rel (kvrel g)) s1.refs s2.refs ∧
     s1.code = FEMPTY ∧ s2.code = FEMPTY
`;
val _ = temp_overload_on ("ksrel", ``clos_knownProof$state_rel``)
val ksrel_def = state_rel_def

val state_rel_max_app = Q.store_thm("state_rel_max_app",
  `state_rel g s1 s2 ⇒ s1.max_app = s2.max_app`,
  rw[state_rel_def]);

val ksrel_flookup_refs = Q.store_thm("ksrel_flookup_refs",
  `ksrel g s1 s2 ∧ FLOOKUP s1.refs k = SOME v ⇒
   ∃v'. FLOOKUP s2.refs k = SOME v' ∧ ref_rel (kvrel g) v v'`,
  rw[ksrel_def,fmap_rel_OPTREL_FLOOKUP,OPTREL_def]
  \\  first_x_assum(qspec_then`k`mp_tac) \\ rw[]);

(* ksrel necessary *)
val ksrel_sga = Q.store_thm(
  "ksrel_sga",
  `ksrel g0 s1 s2 ⇒ (state_globals_approx s1 g ⇔ state_globals_approx s2 g)`,
  simp[ksrel_def, state_globals_approx_def, get_global_def, LIST_REL_EL_EQN] >>
  csimp[] >> rpt strip_tac >> eq_tac >> rpt strip_tac >>
  rename1 `EL kk (ss:('a,'b) closSem$state).globals = SOME vv` >>
  rename1 `lookup kk gg` >>
  nailIHx mp_tac >>
  simp[optionTheory.OPTREL_def] >>
  metis_tac [kvrel_val_approx])

(* ksrel necessary *)
val ksrel_ssgc_free = Q.store_thm(
  "ksrel_ssgc_free",
  `ksrel g s1 s2 ⇒ (ssgc_free s1 ⇔ ssgc_free s2)`,
  simp[ksrel_def, ssgc_free_def] >> rpt strip_tac >> eq_tac >> rpt strip_tac >>
  fs[fmap_rel_OPTREL_FLOOKUP]
  >- (rename1 `FLOOKUP s2.refs kk = SOME (ValueArray vvl)` >>
      `OPTREL (ref_rel (kvrel g)) (FLOOKUP s1.refs kk) (FLOOKUP s2.refs kk)`
         by simp[] >> pop_assum mp_tac >>
      simp_tac(srw_ss()) [OPTREL_def] >> simp[PULL_EXISTS] >> Cases >>
      simp[] >> metis_tac[kvrel_EVERY_vsgc_free])
  >- (fs[LIST_REL_EL_EQN] >>
      imp_res_tac (MEM_EL |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GSYM) >>
      rename1 `EL kk s2.globals` >>
      `OPTREL (kvrel g) (EL kk s1.globals) (EL kk s2.globals)` by simp[] >>
      pop_assum mp_tac >> simp_tac(srw_ss()) [OPTREL_def] >> simp[] >>
      metis_tac[kvrel_vsgc_free, MEM_EL])
  >- (rename1 `FLOOKUP s1.refs kk = SOME (ValueArray vvl)` >>
      `OPTREL (ref_rel (kvrel g)) (FLOOKUP s1.refs kk) (FLOOKUP s2.refs kk)`
         by simp[] >> pop_assum mp_tac >>
      simp_tac(srw_ss()) [OPTREL_def] >> simp[PULL_EXISTS] >>
      metis_tac[kvrel_EVERY_vsgc_free])
  >- (fs[LIST_REL_EL_EQN] >>
      imp_res_tac (MEM_EL |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GSYM) >>
      rename1 `EL kk s1.globals` >>
      `OPTREL (kvrel g) (EL kk s1.globals) (EL kk s2.globals)` by simp[] >>
      pop_assum mp_tac >> simp_tac(srw_ss()) [OPTREL_def] >> simp[] >>
      metis_tac[kvrel_vsgc_free, MEM_EL]))

val res_rel_def = Define`
  (res_rel g (Rval vs1, s1) r ⇔
      ∃s2 vs2. r = (Rval vs2,s2) ∧ LIST_REL (kvrel g) vs1 vs2 ∧ ksrel g s1 s2) ∧
  (res_rel g (Rerr (Rabort Rtype_error), _) _ ⇔ T) ∧
  (res_rel g (Rerr (Rabort Rtimeout_error), s1) (Rerr e, s2) ⇔
     e = Rabort Rtimeout_error ∧ ksrel g s1 s2) ∧
  (res_rel g (Rerr (Rraise v1), s1) (Rerr (Rraise v2), s2) ⇔
     kvrel g v1 v2 ∧ ksrel g s1 s2) ∧
  (res_rel _ _ _ ⇔ F)
`;
val _ = export_rewrites ["res_rel_def"]
val _ = temp_overload_on ("krrel", ``clos_knownProof$res_rel``)
val krrel_def = res_rel_def

val krrel_errval = Q.store_thm(
  "krrel_errval[simp]",
  `(krrel g (Rerr e, s1) (Rval vs, s2) ⇔ e = Rabort Rtype_error)`,
  Cases_on `e` >> simp[] >> rename1 `Rabort a` >> Cases_on `a` >> simp[]);

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
  >- (rename1 `krrel _ _ (r2, s2)` >> Cases_on `r2` >> simp[] >>
      rename1 `krrel _ _ (Rerr e,_)` >> Cases_on `e` >> simp[])
  >- (rename1 `Rabort abt` >> Cases_on `abt` >> simp[] >>
      rename1 `krrel _ _ (r2,s2)` >> Cases_on `r2` >> simp[]));

val krrel_ffi = Q.store_thm(
  "krrel_ffi",
  `krrel gmap (r1,s1) (r2,s2) ∧ r1 ≠ Rerr (Rabort Rtype_error) ⇒
   s2.ffi = s1.ffi`,
  Cases_on `r1` >> Cases_on`r2` >>
  simp[krrel_def, ksrel_def, krrel_err_rw, ksrel_def] >> rw[])

val krrel_arg2_typeerror = Q.store_thm(
  "krrel_arg2_typeerror[simp]",
  `krrel g (res1, s1) (Rerr (Rabort Rtype_error), s2) ⇔
    res1 = Rerr (Rabort Rtype_error)`,
  Cases_on `res1` >> simp[krrel_def, krrel_err_rw]);

(* necesssary kvrel *)
val kvrel_v_to_list = Q.store_thm(
  "kvrel_v_to_list",
  `∀g v1 v2 l1.
     kvrel g v1 v2 ∧ v_to_list v1 = SOME l1 ⇒
     ∃l2. v_to_list v2 = SOME l2 ∧ LIST_REL (kvrel g) l1 l2`,
  ho_match_mp_tac val_rel_ind >> simp[v_to_list_def, PULL_EXISTS] >>
  rpt strip_tac >> rename1 `v_to_list (closSem$Block _ vs2)` >>
  Cases_on `vs2` >> fs[v_to_list_def] >> rw[] >> fs[v_to_list_def] >>
  rename1 `v_to_list (closSem$Block _ (_ :: vs2'))` >>
  Cases_on `vs2'` >> fs[v_to_list_def] >> rw[] >> fs[v_to_list_def] >>
  rename1 `v_to_list (closSem$Block _ (_ :: _ :: vs2''))` >>
  Cases_on `vs2''` >> fs[v_to_list_def] >> rw[] >> fs[v_to_list_def] >>
  fs[case_eq_thms] >> rveq >> simp[PULL_EXISTS] >> metis_tac[MEM]);

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
      ONCE_REWRITE_TAC [do_eq_def] >>
      Cases_on `do_eq u1 v1` >> fs[] >> simp[bool_case_eq] >> dsimp[] >>
      rename1 `do_eq u1 v1 = Eq_val b` >> Cases_on `b` >> simp[] >>
      rpt strip_tac >> nailIHx strip_assume_tac >> simp[] >> metis_tac[])
  >- (simp[PULL_EXISTS] >> ONCE_REWRITE_TAC[do_eq_def] >> simp[])
  >- (simp[PULL_EXISTS] >> ONCE_REWRITE_TAC[do_eq_def] >> simp[]));

val kvrel_do_eq = save_thm("kvrel_do_eq", kvrel_do_eq0 |> CONJUNCT1);

val kvrel_list_to_v = Q.store_thm("kvrel_list_to_v",
  `!xs1 xs2 ys1 ys2.
     LIST_REL (kvrel g) xs1 xs2 /\
     LIST_REL (kvrel g) ys1 ys2 /\
     kvrel g (list_to_v xs1) (list_to_v xs2) /\
     kvrel g (list_to_v ys1) (list_to_v ys2) ==>
       kvrel g (list_to_v (xs1 ++ ys1)) (list_to_v (xs2 ++ ys2))`,
  Induct >- rw [list_to_v_def] \\ gen_tac
  \\ Induct \\ rw [list_to_v_def] \\ fs []);

val kvrel_v2l_l2v = Q.store_thm("kvrel_v2l_l2v",
  `!x y xs ys.
     kvrel g x y /\
     v_to_list x = SOME xs /\
     v_to_list y = SOME ys ==>
       kvrel g (list_to_v xs) (list_to_v ys)`,
  ho_match_mp_tac v_to_list_ind \\ rw [v_to_list_def]
  \\ fs [list_to_v_def] \\ rveq
  \\ fs [v_to_list_def] \\ rveq
  \\ fs [list_to_v_def, case_eq_thms] \\ rveq
  \\ fs [list_to_v_def]
  \\ res_tac);

(* necessary(!) *)
val kvrel_op_correct_Rval = Q.store_thm(
  "kvrel_op_correct_Rval",
  `LIST_REL (kvrel g) vs1 vs2 ∧ do_app opn vs1 s01 = Rval(v1,s1) ∧
   ksrel g s01 s02 ⇒
   ∃v2 s2. do_app opn vs2 s02 = Rval(v2,s2) ∧ ksrel g s1 s2 ∧
           kvrel g v1 v2`,
  Cases_on `opn` >> simp[do_app_def, case_eq_thms, bool_case_eq, PULL_EXISTS] >>
  TRY (rw[] >> fs[LIST_REL_EL_EQN] >> NO_TAC) \\
  TRY (rw[] >> fs[] >>
       imp_res_tac ksrel_flookup_refs \\ fs[ksrel_def] >>
       imp_res_tac fmap_rel_def \\ fs[] \\
       rveq \\ fs[LIST_REL_EL_EQN] \\
       TRY (CASE_TAC \\ fs[] \\ rveq \\ fs[]) \\
       TRY (match_mp_tac fmap_rel_FUPDATE_same) \\ fs[]
       \\ fs[LIST_REL_EL_EQN,OPTREL_def,LIST_REL_REPLICATE_same,EVERY2_LUPDATE_same]
       \\ first_x_assum match_mp_tac \\ rw[] \\ fs[] \\ intLib.COOPER_TAC)
  >- (csimp[get_global_def] >> simp[ksrel_def] >>
      simp[LIST_REL_EL_EQN, OPTREL_def] >> rpt strip_tac >> rveq >>
      res_tac >> fs[] >> rveq >> simp[])
  >- (csimp[get_global_def, PULL_EXISTS] >> simp[ksrel_def] >> rw[] >>
      fs[LIST_REL_EL_EQN] >> rfs[] >> res_tac >> fs[OPTREL_def] >> fs[] >>
      simp[EL_LUPDATE, bool_case_eq] >> metis_tac[])
  >- (
    rw [] >>
    fs [] >>
    rw [] >>
    imp_res_tac LIST_REL_LENGTH
    >- intLib.ARITH_TAC
    >- intLib.ARITH_TAC >>
    irule EVERY2_APPEND_suff >>
    simp [] >>
    irule EVERY2_TAKE >>
    irule EVERY2_DROP >>
    simp [])
  >- (rw[] >> fs[] >>
      imp_res_tac kvrel_v_to_list >> fs[ksrel_def] \\ rfs[] >>
      qpat_x_assum`_ = SOME wss`mp_tac >>
      DEEP_INTRO_TAC some_intro \\ fs[] \\ strip_tac \\
      DEEP_INTRO_TAC some_intro \\ fs[PULL_EXISTS] \\
      map_every qexists_tac[`wss`] \\
      reverse conj_asm2_tac >- (
        fs[LIST_EQ_REWRITE,EL_MAP,LIST_REL_EL_EQN,fmap_rel_def,FLOOKUP_DEF] \\
        rfs[EL_MAP] \\ rw[] \\ res_tac \\ res_tac \\ fs[] \\
        Cases_on`s02.refs ' (EL x ps)` \\ fs[] >>
        metis_tac[ref_rel_def,ref_11]) \\
      ntac 2 strip_tac >>
      imp_res_tac INJ_MAP_EQ \\ fs[INJ_DEF] \\
      imp_res_tac INJ_MAP_EQ \\ fs[INJ_DEF] )
  >-
   (rw [] \\ fs [] \\ rw []
    \\ imp_res_tac kvrel_v_to_list \\ fs [] \\ rfs [] \\ rw []
    \\ match_mp_tac kvrel_list_to_v \\ fs []
    \\ imp_res_tac kvrel_v2l_l2v \\ fs [])
  >- (rw[] >> fs[] >> metis_tac[kvrel_v_to_list])
  >- (
    rw[] \\ fs[] \\
    rpt(qpat_x_assum`$some _ = _`mp_tac) \\
    rpt(DEEP_INTRO_TAC some_intro) \\ rw[] \\
    spose_not_then strip_assume_tac \\
    imp_res_tac kvrel_v_to_list \\
    rfs[LIST_EQ_REWRITE,LIST_REL_EL_EQN,EL_MAP] \\ fs[EL_MAP] \\
    rfs[LIST_EQ_REWRITE,LIST_REL_EL_EQN,EL_MAP] \\
    fs[EVERY_MEM,EXISTS_MEM] \\
    metis_tac[v_11,integerTheory.INT_INJ,EL_MAP,o_THM,ORD_BOUND] )
  >- (rw[] >> fs[] >> rw[] >> metis_tac[kvrel_do_eq]));

val do_app_EQ_Rerr = Q.store_thm(
  "do_app_EQ_Rerr",
  `closSem$do_app opn vs s0 = Rerr e ⇒ e = Rabort Rtype_error`,
  Cases_on `opn` >> simp[do_app_def, case_eq_thms, bool_case_eq, pair_case_eq] >> rw[]);

val kvrel_lookup_vars = Q.store_thm(
  "kvrel_lookup_vars",
  `∀env01 env02 vars env1.
     LIST_REL (kvrel g) env01 env02 ∧ lookup_vars vars env01 = SOME env1 ⇒
     ∃env2. lookup_vars vars env02 = SOME env2 ∧
            LIST_REL (kvrel g) env1 env2`,
  Induct_on `vars` >> simp[lookup_vars_def, case_eq_thms, PULL_EXISTS] >>
  fs[LIST_REL_EL_EQN] >> metis_tac[]);

val loptrel_def = Define`
  loptrel fv numargs lopt1 lopt2 ⇔
     lopt2 = lopt1 ∨
     lopt1 = NONE ∧
     case (fv,lopt2) of
       | (Closure (SOME loc1) ae _ n bod, SOME loc2) =>
            loc1 = loc2 ∧ n = numargs ∧ ae = []
       | (Recclosure (SOME loc1) ae _ fns i, SOME loc2) =>
         i < LENGTH fns ∧ loc2 = loc1 + 2 * i ∧ numargs = FST (EL i fns) ∧
         ae = []
       | _ => F
`;

val ksrel_find_code = Q.store_thm(
  "ksrel_find_code",
  `ksrel g s1 s2 ⇒ find_code l (vs1:closSem$v list) s1.code = NONE`,
  simp[ksrel_def, find_code_def, case_eq_thms, pair_case_eq]);

val kvrel_dest_closure_SOME_Partial = Q.store_thm(
  "kvrel_dest_closure_SOME_Partial",
  `dest_closure max_app lopt1 f1 vs1 = SOME (Partial_app v1) ∧ kvrel g f1 f2 ∧
   LIST_REL (kvrel g) vs1 vs2 ∧ loptrel f2 n lopt1 lopt2 ∧ LENGTH vs2 = n ⇒
   ∃v2. dest_closure max_app lopt2 f2 vs2 = SOME (Partial_app v2) ∧
        kvrel g v1 v2`,
  simp[dest_closure_def, case_eq_thms, v_case_eq] >> rpt strip_tac >> rveq >> fs[] >>
  rpt strip_tac >> fs[case_eq_thms, bool_case_eq] >> rveq >> fs[loptrel_def] >> rveq
  >- (simp[EVERY2_APPEND_suff] >> fs[LIST_REL_EL_EQN] >> metis_tac[])
  >- (Cases_on `lopt2` >> simp[EVERY2_APPEND_suff] >> fs[LIST_REL_EL_EQN] >>
      rename1 `option_CASE lll` >> Cases_on `lll` >> fs[LIST_REL_EL_EQN])
  >- (rpt (pairarg_tac >> fs[]) >> fs[bool_case_eq] >>
      simp[EVERY2_APPEND_suff] >>
      rename1 `LIST_REL val_approx_val envapx env2` >> simp[PULL_EXISTS] >>
      qexists_tac `envapx` >>
      fs[LIST_REL_EL_EQN] >> rename1 `EL ii` >>
      qpat_x_assum `∀n. _ ⇒ UNCURRY f x y` mp_tac >>
      disch_then (qspec_then `ii` mp_tac) >> simp[] >> rw[] >> simp[])
  >- (rpt (pairarg_tac >> fs[]) >> fs[bool_case_eq] >>
      Cases_on `lopt2` >> fs[] >> rename1 `option_CASE lll` >>
      Cases_on `lll` >> fs[] >> rveq >>
      qpat_x_assum `LIST_REL (UNCURRY _) _ _` mp_tac >>
      CONV_TAC (LAND_CONV (REWRITE_CONV [LIST_REL_EL_EQN])) >>
      rename1 `EL ii` >>
      disch_then (CONJUNCTS_THEN2 assume_tac (qspec_then `ii` mp_tac)) >>
      strip_tac >> rfs[] >> fs[LIST_REL_EL_EQN]))

val kvrel_dest_closure_SOME_Full = Q.store_thm(
  "kvrel_dest_closure_SOME_Full",
  `dest_closure max_app lopt1 f1 vs1 = SOME (Full_app e1 env1 args1) ∧
   kvrel g f1 f2 ∧
   LIST_REL (kvrel g) vs1 vs2 ∧ loptrel f2 n lopt1 lopt2 ∧ LENGTH vs2 = n ⇒
   ∃eapx e2 env2 args2.
      dest_closure max_app lopt2 f2 vs2 = SOME (Full_app e2 env2 args2) ∧
      LIST_REL val_approx_val eapx env2 ∧
      LIST_REL (kvrel g) env1 env2 ∧ LIST_REL (kvrel g) args1 args2 ∧
      kerel eapx g e1 e2`,
  simp[dest_closure_def, case_eq_thms, bool_case_eq] >>
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
      rename1 `option_CASE lll` >> Cases_on `lll` >> fs[] >> rveq >>
      fs[check_loc_def])
  >- (rpt (pairarg_tac >> fs[]) >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
      fs[bool_case_eq] >> rveq >>
      qpat_x_assum `LIST_REL (UNCURRY _) _ _`
        (fn th => (mp_tac o SIMP_RULE (srw_ss()) [LIST_REL_EL_EQN]) th >>
                  assume_tac th) >>
      rename1 `EL ii` >> simp[] >>
      disch_then (qspec_then `ii` mp_tac) >> simp[] >> strip_tac >> rveq >>
      simp[EVERY2_TAKE] >> rename1 `REPLICATE nargs Other` >>
      rename1 `GENLIST (option_CASE locc _ _)` >>
      rename1 `LIST_REL (UNCURRY _) fns1 fns2` >>
      rename1 `LIST_REL val_approx_val envapx _` >>
      qexists_tac `REPLICATE nargs Other ++
                   GENLIST (case locc of
                              | NONE => K Other
                              | SOME n => (λi. Clos (2*i + n) (FST (EL i fns1))))
                           (LENGTH fns2) ++ envapx` >> simp[] >>
      conj_tac
      >- (fs[loptrel_def] >> Cases_on `lopt2` >> fs[] >>
          rename1 `option_CASE lll` >> Cases_on `lll` >> fs[] >>
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
  ho_match_mp_tac val_rel_ind >> simp[PULL_EXISTS] >> rpt strip_tac
  >- (irule EVERY2_MEM_MONO >> imp_res_tac LIST_REL_LENGTH >>
      simp[FORALL_PROD, MEM_ZIP, PULL_EXISTS] >> qexists_tac `kvrel g` >>
      simp[] >> metis_tac[MEM_EL])
  >- (rename1 `LIST_REL val_approx_val envapx _` >> qexists_tac `envapx` >>
      simp[] >> rpt conj_tac >>
      TRY (irule EVERY2_MEM_MONO >> imp_res_tac LIST_REL_LENGTH >>
           simp[FORALL_PROD, MEM_ZIP, PULL_EXISTS] >>
           qexists_tac `kvrel g` >> simp[] >> metis_tac[MEM_EL]) >>
      fs[exp_rel_def] >> metis_tac[subspt_trans])
  >- (rename1 `LIST_REL val_approx_val envapx _` >> qexists_tac `envapx` >>
      simp[] >> rpt conj_tac >>
      TRY (irule EVERY2_MEM_MONO >> imp_res_tac LIST_REL_LENGTH >>
           simp[FORALL_PROD, MEM_ZIP, PULL_EXISTS] >>
           qexists_tac `kvrel g` >> simp[] >> metis_tac[MEM_EL]) >>
      qpat_x_assum `LIST_REL (UNCURRY _) _ _` mp_tac >> simp[LIST_REL_EL_EQN] >>
      rpt strip_tac >> fs[] >> rfs[] >> rpt (pairarg_tac >> fs[]) >>
      rename1 `nn < LENGTH _` >> first_x_assum (qspec_then `nn` mp_tac) >>
      simp[] >> simp[exp_rel_def] >> metis_tac[subspt_trans]))

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

val dest_closure_SOME_Full_app_args_nil = Q.store_thm(
  "dest_closure_SOME_Full_app_args_nil",
  `dest_closure max_app (SOME loc) f args = SOME (Full_app exp1 env args1) ⇒
   args1 = []`,
  simp[dest_closure_def, case_eq_thms, bool_case_eq, revtakerev] >> strip_tac >> rveq
  >- (fs[check_loc_def] >> simp[DROP_LENGTH_NIL_rwt]) >>
  pairarg_tac >> fs[bool_case_eq] >> rveq >> fs[check_loc_def] >> rveq >>
  simp[DROP_LENGTH_NIL_rwt]);

val eqtI_thm = EQ_CLAUSES |> SPEC_ALL |> CONJUNCTS |> el 2 |> GSYM

val v_caseT = v_case_eq |> INST_TYPE [alpha |-> bool] |> Q.INST [`v` |-> `T`]
                        |> REWRITE_RULE []
val optcaset = ``option$option_CASE``
val opt_caseT = case_eq_thms |> CONJUNCTS
                    |> List.find (fn th => th |> concl |> lhs |> lhs
                                              |> strip_comb
                                              |> #1 |> same_const optcaset)
                    |> valOf
                    |> INST_TYPE [beta |-> bool]
                    |> Q.INST [`v'` |-> `T`]
                    |> SIMP_RULE (srw_ss()) []


val loptrel_arg1_SOME = save_thm(
  "loptrel_arg1_SOME",
  loptrel_def |> SPEC_ALL |> Q.INST [`lopt1` |-> `SOME loc1`]
              |> SIMP_RULE (srw_ss()) [opt_caseT, v_caseT])

val loptrel_arg1_NONE = save_thm(
  "loptrel_arg1_NONE",
  loptrel_def |> SPEC_ALL |> Q.INST [`lopt1` |-> `NONE`]
              |> SIMP_RULE (srw_ss()) [opt_caseT, v_caseT])

val kvrel_dest_closure_every_Fn_vs_NONE = Q.store_thm(
  "kvrel_dest_closure_every_Fn_vs_NONE",
  `kvrel g f1 f2 ∧ dest_closure max_app locopt f1 args0 = SOME (Full_app e env args) ⇒
   every_Fn_vs_NONE [e]`,
  simp[dest_closure_def, case_eq_thms, bool_case_eq] >> strip_tac >> rveq >> fs[] >>
  rveq >> simp[Once every_Fn_vs_NONE_EVERY] >> pairarg_tac >>
  fs[bool_case_eq] >> rveq >> fs[EVERY_MEM, FORALL_PROD, NOT_LESS_EQUAL] >>
  metis_tac[MEM_EL]);

val known_correct0 = Q.prove(
  `(∀a es env1 env2 (s01:('a,'b) closSem$state) s02 res1 s1 g0 g g' as ealist.
      a = (es,env1,s01) ∧ evaluate (es, env1, s01) = (res1, s1) ∧
      EVERY esgc_free es ∧ subspt g0 g ∧ subspt g g' ∧
      LIST_REL val_approx_val as env1 ∧ EVERY vsgc_free env1 ∧
      every_Fn_vs_NONE es ∧
      LIST_REL (kvrel g') env1 env2 ∧ ksrel g' s01 s02 ∧
      state_globals_approx s01 g' ∧ BAG_ALL_DISTINCT (elist_globals es) ∧
      ssgc_free s01 ∧ known es as g0 = (ealist, g) ⇒
      ∃res2 s2.
        evaluate(MAP FST ealist, env2, s02) = (res2, s2) ∧
        krrel g' (res1,s1) (res2,s2)) ∧
   (∀lopt1 f1 args1 (s01:('a,'b) closSem$state) res1 s1 lopt2 f2 args2 s02 g.
      evaluate_app lopt1 f1 args1 s01 = (res1,s1) ∧ ssgc_free s01 ∧
      kvrel g f1 f2 ∧ LIST_REL (kvrel g) args1 args2 ∧
      ksrel g s01 s02 ∧ state_globals_approx s01 g ∧ vsgc_free f1 ∧
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
      map_every rename1 [`ksrel g' s01 s02`, `subspt g g'`,
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
          >- (patresolve `known [gd] _ _ = _` hd (GEN_ALL kca_sing_sga) >>
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
      map_every rename1 [`known [bod] _ g1 = (_, g)`,
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
      map_every rename1 [`known _ (_ :: _) g1 = (_, g)`,
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
               (mp_then (Pos last) (mp_tac >~ (simp[] >> NO_TAC)) ssgc_evaluate)
          >- (patresolve `known _ _ g0 = _` hd (GEN_ALL kca_sing_sga) >>
              simp[] >> disch_then (resolve_selected last) >> simp[] >>
              metis_tac[ksrel_ssgc_free,kvrel_EVERY_vsgc_free,ksrel_sga,
                        kvrel_LIST_REL_val_approx]))
      >- (fs[krrel_err_rw, result_case_eq, error_case_eq] >> dsimp[] >>
          metis_tac[pair_CASES, result_CASES, error_CASES]))
  >- (say "op" >>
      simp[evaluate_def, pair_case_eq, result_case_eq, known_def,
           BAG_ALL_DISTINCT_BAG_UNION] >>
      rpt gen_tac >> strip_tac >> rpt gen_tac >>
      Cases_on `op = Install` >- cheat >>
      rpt (pairarg_tac >> fs[]) >>
      rename[`isGlobal opn`, `gO_destApx apx`] >>
      cheat (*
      Cases_on `isGlobal opn ∧ gO_destApx apx ≠ gO_None`
      >- (pop_assum strip_assume_tac >> simp[] >>
          Cases_on `opn` >> fs[isGlobal_def] >>
          Cases_on `apx` >> fs[gO_destApx_def] >> rveq >>
          fs[known_op_def, NULL_EQ, bool_case_eq, case_eq_thms] >> rveq >>
          imp_res_tac known_LENGTH_EQ_E >> fs[LENGTH_NIL_SYM] >> rveq >>
          simp[evaluate_def] >>
          rpt strip_tac >> rveq >> fs[evaluate_def, do_app_def, case_eq_thms] >>
          fs[state_globals_approx_def, subspt_def] >> rveq >> simp[] >>
          fs[known_def] >> rveq
          >- (rename[`lookup n g0 = SOME (Tuple tg [])`,
                     `kvrel g1 v (Block tg [])`] >>
              `lookup n g1 = SOME (Tuple tg [])` by metis_tac[domain_lookup] >>
              res_tac >> fs[] >> rveq >> fs[val_approx_val_def]) >>
          (* TODO: clos_known$ is only necessary because of HOL issue #430 *)
          rename[`lookup n g0 = SOME (clos_known$Int i)`, `kvrel g1 v (Number i)`] >>
          `lookup n g1 = SOME (Int i)` by metis_tac[domain_lookup] >>
          metis_tac[val_rel_def, val_approx_val_def, SOME_11]) >>
      rename[`closLang$Op tr opn (MAP FST es)`,
             `closSem$evaluate(MAP FST ealist,_,_)`] >>
      rpt strip_tac >>
      `ealist = [(Op tr opn (MAP FST es), apx)]`
         by (Cases_on `isGlobal opn` >> fs[] >>
             Cases_on `apx` >> fs[gO_destApx_def] >> every_case_tac >> fs[]) >>
      pop_assum SUBST_ALL_TAC >> rveq >>
      qpat_x_assum `¬(_ ∧ _)` kall_tac >> fs[] >>
      dsimp[evaluate_def, result_case_eq, pair_case_eq] >>
      sel_ihpc last >> simp[PULL_EXISTS] >>
      rpt (disch_then (resolve_selected last) >> simp[]) >>
      resolve_selected hd subspt_known_op_elist_globals >> simp[] >>
      rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
      (impl_keep_tac >- metis_tac[subspt_trans])
      >- ((* args evaluate OK, do_app evaluates OK *)
          metis_tac[kvrel_op_correct_Rval, EVERY2_REVERSE])
      >- ((* args evaluate OK, do_app errors *)
          rw[] >> imp_res_tac do_app_EQ_Rerr >> rw[] >>
          metis_tac[result_CASES, pair_CASES])
      >- ((* args error *) rw[] >> fs[krrel_err_rw] >>
         metis_tac[result_CASES, pair_CASES]) *))
  >- (say "fn" >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           known_def, bool_case_eq, case_eq_thms] >> rpt strip_tac >> rveq >> fs[] >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac state_rel_max_app >> fs[] >>
      dsimp[evaluate_def, case_eq_thms] >> imp_res_tac known_sing_EQ_E >> rveq >> fs[] >>
      rveq >>
      simp[exp_rel_def, PULL_EXISTS] >> metis_tac[kvrel_LIST_REL_val_approx])
  >- (say "letrec" >>
      simp[evaluate_def, pair_case_eq, result_case_eq, known_def, bool_case_eq,
           case_eq_thms] >> rpt strip_tac >> rveq >> fs[letrec_case_eq] >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      fs[BAG_ALL_DISTINCT_BAG_UNION] >>
      imp_res_tac state_rel_max_app >> fs[] >>
      simp[evaluate_def, case_eq_thms, bool_case_eq] >> dsimp[] >>
      simp[EVERY_MAP, EXISTS_MAP]
      >- (disj1_tac >> simp[EVERY_MEM, FORALL_PROD] >>
          imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
          sel_ihpc last >> simp[EVERY_GENLIST] >>
          rpt (disch_then (resolve_selected last) >> simp[]) >>
          rename1 `BAG_ALL_DISTINCT (elist_globals (MAP SND fns1))` >>
          `∀n e. MEM (n,e) fns1 ⇒ n ≤ s02.max_app ∧ n ≠ 0`
            by fs[EVERY_MEM, FORALL_PROD] >> simp[] >> strip_tac >>
          simp[GSYM PULL_EXISTS] >> simp[Once EQ_SYM_EQ] >>
          imp_res_tac LIST_REL_LENGTH >> fs[] >>
          first_x_assum irule
          >- (simp[LIST_REL_EL_EQN, EL_APPEND_EQN] >> qx_gen_tac `mm` >>
              strip_tac >> rw[]
              >- (fs[Once every_Fn_vs_NONE_EVERY] >>
                  fs[EVERY_MAP] >> fs[EVERY_MEM, FORALL_PROD] >>
                  metis_tac[])
              >- (rename1 `LIST_REL val_approx_val apxs env1` >>
                  qexists_tac `apxs` >> conj_tac
                  >- metis_tac[kvrel_LIST_REL_val_approx] >>
                  simp[LIST_REL_EL_EQN, EL_MAP] >>
                  qx_gen_tac `nn` >> strip_tac >> pairarg_tac >>
                  simp[] >> simp[exp_rel_def] >>
                  map_every rename1 [`ksrel gg ss1 ss2`, `subspt g gg`,
                                       `subspt g0 g`] >>
                  ntac 2 (qexists_tac `g0`) >> simp[] >>
                  rename1 `known [e1] env g0` >>
                  Cases_on `known [e1] env g0` >>
                  imp_res_tac known_sing_EQ_E >> fs[] >> rveq >>
                  conj_tac >- metis_tac[subspt_trans] >>
                  rename1 `known [subexp] env g0 = _` >>
                  `elist_globals [subexp] = {||}`
                    suffices_by metis_tac[known_emptySetGlobals_unchanged_g] >>
                  fs[elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
                  metis_tac[MEM_EL])
              >- fs[LIST_REL_EL_EQN])
          >- (irule EVERY2_APPEND_suff >> simp[] >>
              simp[LIST_REL_GENLIST] >> qx_gen_tac `ii` >> strip_tac >>
              rename1 `option_CASE lloc` >> Cases_on `lloc` >> simp[])) >>
      disj2_tac >> fs[EXISTS_MEM, EXISTS_PROD] >> metis_tac[])
  >- (say "app" >>
      rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           bool_case_eq, known_def, BAG_ALL_DISTINCT_BAG_UNION] >>
      rpt strip_tac >> rveq >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      map_every imp_res_tac [known_sing_EQ_E, evaluate_SING] >> rveq >> fs[] >>
      rveq
      >- (map_every rename1 [
            `known [fexp] apxs g1 = ([(fexp',fapx)], g)`,
            `known args apxs g0 = (alist, g1)`,
            `subspt g gg`] >>
          patresolve `known [_] _ _ = _` (el 2) subspt_known_elist_globals >>
          simp[] >> disch_then (resolve_selected (el 1)) >> simp[] >>
          impl_tac >- fs[BAG_DISJOINT, DISJOINT_SYM] >> strip_tac >>
          first_x_assum (patresolve `known args _ _ = _` last) >> simp[] >>
          `subspt g1 gg` by metis_tac[subspt_trans] >>
          rpt (disch_then (resolve_selected last) >> simp[]) >> rw[] >>
          simp[evaluate_def] >> imp_res_tac known_LENGTH_EQ_E >> fs[] >>
          first_x_assum (patresolve `known [_] _ _ = _` last) >> simp[] >>
          disch_then (resolve_selected (el 2)) >> simp[] >>
          disch_then (resolve_selected hd) >> simp[] >>
          resolve_selected hd ssgc_evaluate >> simp[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          impl_keep_tac
          >- (patresolve `closSem$evaluate (MAP FST _, _, _) = _` last
                         known_correct_approx >>
              simp[] >> disch_then (resolve_selected hd) >> simp[] >>
              metis_tac[ksrel_ssgc_free,kvrel_EVERY_vsgc_free,ksrel_sga,
                        kvrel_LIST_REL_val_approx]) >>
          rw[] >> simp[] >>
          rename1 `evaluate_app loption1 v1 vs1 s21 = (result,ss1)` >>
          `ssgc_free s21`
            by metis_tac[ksrel_ssgc_free, ssgc_free_preserved_SING'] >> fs[] >>
          first_x_assum (resolve_selected hd) >> simp[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          `state_globals_approx s21 gg`
            by (patresolve `known [_] _ _ = _` hd known_correct_approx >>
                simp[] >> disch_then (resolve_selected last) >> simp[] >>
                metis_tac[ksrel_ssgc_free,kvrel_EVERY_vsgc_free,ksrel_sga,
                          kvrel_LIST_REL_val_approx]) >> fs[] >>
          `vsgc_free v1`
            by (patresolve `closSem$evaluate ([_],_,_) = (Rval [v1],_)` last
                           ssgc_evaluate >> simp[]) >> fs[] >>
          reverse (Cases_on `loption1`) >> simp[]
          >- (first_x_assum irule >> simp[loptrel_def]) >>
          rename1 `dest_Clos fapprox` >> Cases_on `dest_Clos fapprox` >>
          simp[]
          >- (first_x_assum irule >> simp[loptrel_def]) >>
          rename1 `dest_Clos fapprox = SOME closapxvalue` >>
          `∃clloc clarity. closapxvalue = (clloc, clarity)`
            by metis_tac[pair_CASES] >> pop_assum SUBST_ALL_TAC >>
          simp[] >> rename1 `LENGTH args > 0` >>
          reverse (Cases_on `clarity = LENGTH args`) >> simp[]
          >- (first_x_assum irule >> simp[loptrel_def]) >>
          first_x_assum irule >> simp[loptrel_def] >>
          qspecl_then [`[fexp]`, `apxs`, `g1`, `[(fexp',fapprox)]`, `g`]
             mp_tac known_correct_approx >> simp[] >>
          disch_then (resolve_selected last) >> simp[] >>
          disch_then (qspec_then `gg` mp_tac) >> impl_tac
          >- metis_tac[kvrel_LIST_REL_val_approx, ksrel_ssgc_free,
                       kvrel_EVERY_vsgc_free, ksrel_sga] >>
          fs[dest_Clos_eq_SOME] >> rveq >> rw[] >> simp[] >>
          metis_tac[evaluate_length_imp])
      >- (map_every rename1 [
            `known [fexp] apxs g1 = ([(fexp',fapx)], g)`,
            `known args apxs g0 = (alist, g1)`,
            `subspt g gg`] >>
          patresolve `known [_] _ _ = _` (el 2) subspt_known_elist_globals >>
          simp[] >> disch_then (resolve_selected (el 1)) >> simp[] >>
          impl_tac >- fs[BAG_DISJOINT, DISJOINT_SYM] >> strip_tac >>
          first_x_assum (patresolve `known args _ _ = _` last) >> simp[] >>
          `subspt g1 gg` by metis_tac[subspt_trans] >>
          rpt (disch_then (resolve_selected last) >> simp[]) >> rw[] >>
          simp[evaluate_def] >> imp_res_tac known_LENGTH_EQ_E >> fs[] >>
          sel_ihpc last >> simp[] >>
          disch_then (resolve_selected (el 2)) >> simp[] >>
          disch_then (resolve_selected hd) >> simp[] >> reverse impl_tac
          >- (rw[] >> simp[] >> fs[krrel_err_rw] >>
              dsimp[result_case_eq] >> metis_tac[pair_CASES, result_CASES]) >>
          conj_tac
          >- (patresolve `closSem$evaluate (MAP FST _, _, _) = _` last
                         known_correct_approx >>
              simp[] >> disch_then (resolve_selected hd) >> simp[] >>
              metis_tac[ksrel_ssgc_free,kvrel_EVERY_vsgc_free,ksrel_sga,
                        kvrel_LIST_REL_val_approx]) >>
          metis_tac [ssgc_evaluate])
      >- (map_every rename1 [
            `known [fexp] apxs g1 = ([(fexp',fapx)], g)`,
            `known args apxs g0 = (alist, g1)`,
            `subspt g gg`] >>
          patresolve `known [_] _ _ = _` (el 2) subspt_known_elist_globals >>
          simp[] >> disch_then (resolve_selected (el 1)) >> simp[] >>
          impl_tac >- fs[BAG_DISJOINT, DISJOINT_SYM] >> strip_tac >>
          first_x_assum (patresolve `known args _ _ = _` last) >> simp[] >>
          `subspt g1 gg` by metis_tac[subspt_trans] >> strip_tac >>
          nailIHx strip_assume_tac >>
          simp[evaluate_def, bool_case_eq, result_case_eq, pair_case_eq] >>
          imp_res_tac known_LENGTH_EQ_E >> rveq >> fs[] >>
          fs[krrel_err_rw] >> dsimp[] >>
          metis_tac[result_CASES,pair_CASES])
      >- (map_every imp_res_tac [evaluate_IMP_LENGTH, known_LENGTH_EQ_E] >>
          fs[] >> rw[] >> simp[evaluate_def]))
  >- (say "tick" >> simp[dec_clock_def] >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, bool_case_eq, known_def] >>
      rename1 `(s0:('a,'b) closSem$state).clock = 0` >> Cases_on `s0.clock = 0` >>
      fs[] >> rpt strip_tac >> rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      simp[evaluate_def] >- fs[ksrel_def] >>
      fs[dec_clock_def] >> fixeqs >> imp_res_tac known_sing_EQ_E >> rveq >>
      fs[] >> rveq >>
      map_every rename1 [
        `known [exp1] apxs g0 = ([(exp2,apx)],g)`,
        `evaluate([exp1],env1,s01 with clock := s01.clock - 1) = (res1,s1)`,
        `ksrel gg s01 s02`] >>
      sel_ihpc last >> simp[] >>
      disch_then
        (qspecl_then [`env2`, `s02 with clock := s02.clock - 1`, `gg`]
                     mp_tac) >>
      simp[] >> impl_keep_tac >- fs[ksrel_def] >>
      `s02.clock = s01.clock` by fs[ksrel_def] >> simp[])
  >- (say "call" >>
      simp[evaluate_def, pair_case_eq, result_case_eq, case_eq_thms, bool_case_eq,
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
          dsimp[result_case_eq, case_eq_thms, pair_case_eq, bool_case_eq] >>
          metis_tac[option_CASES, pair_CASES, result_CASES]))
  >- (say "evaluate_app(nil)" >> simp[evaluate_def])
  >- (say "evaluate_app(cons)" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq, result_case_eq] >>
      rpt strip_tac >> rveq >> fs[]
      >- metis_tac[pair_CASES]
      >- (simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq] >>
          resolve_selected hd (GEN_ALL kvrel_dest_closure_SOME_Partial) >>
          simp[PULL_EXISTS] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >>
          strip_tac >> simp[] >> fs[ksrel_def])
      >- (simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq] >>
          resolve_selected hd (GEN_ALL kvrel_dest_closure_SOME_Partial) >>
          simp[PULL_EXISTS] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          simp[] >> fs[ksrel_def, dec_clock_def])
      >- (simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq] >>
          resolve_selected hd (GEN_ALL kvrel_dest_closure_SOME_Full) >>
          simp[PULL_EXISTS] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          simp[] >> imp_res_tac LIST_REL_LENGTH >> fs[ksrel_def])
      >- (simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq] >>
          resolve_selected hd (GEN_ALL kvrel_dest_closure_SOME_Full) >>
          simp[PULL_EXISTS] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          simp[] >> rename1 `ksrel g s01 s02` >>
          `s02.clock = s01.clock` by fs[ksrel_def] >>
          `s02.max_app = s01.max_app` by fs[ksrel_def] >>
          imp_res_tac LIST_REL_LENGTH >> fs[] >> simp[PULL_EXISTS] >>
          dsimp[] >> fs[PULL_EXISTS] >>
          map_every rename1 [
            `dest_closure _ lopt1 f1 (iarg1 :: iargs) =
               SOME (Full_app exp1 env1 args1)`,
            `evaluate([exp1],env1,dec_clock _ s01) = (Rval [v1], s11)`,
            `kerel envapx gg exp1 exp2`] >> fs[exp_rel_def] >>
          rpt disj1_tac >>
          first_x_assum (patresolve `known [exp1] _ _ = _` last) >> simp[] >>
          map_every rename1 [
            `evaluate([exp1],env1,
                      dec_clock (SUC (LENGTH iargs1) - LENGTH args2) s01)`,
            `LIST_REL (kvrel gg) env1 env2`] >>
          disch_then (qspecl_then [
             `env2`,
             `dec_clock (SUC (LENGTH iargs1) - LENGTH args2) s02`,
             `gg`] mp_tac) >> simp[] >>
          `set_globals exp1 = {||} ∧ EVERY vsgc_free env1 ∧
           EVERY vsgc_free args1 ∧ esgc_free exp1`
            by metis_tac[vsgc_free_Full_app_set_globals, EVERY_DEF,
                         set_globals_empty_esgc_free] >> simp[] >>
          qspec_then `[exp1]` mp_tac known_emptySetGlobals_unchanged_g >>
          disch_then (resolve_selected hd) >> simp[] >>
          disch_then SUBST_ALL_TAC >>
          rename1 `LIST_REL val_approx_val envapx env1` >>
          `LIST_REL val_approx_val envapx env1`
            by metis_tac[kvrel_LIST_REL_val_approx] >>
          `every_Fn_vs_NONE [exp1]`
            by metis_tac[kvrel_dest_closure_every_Fn_vs_NONE] >>
          impl_tac >- (simp[] >> fs[ksrel_def, dec_clock_def]) >> rw[] >>
          simp[] >>
          rename1 `loptrel f2 _ lopt1 lopt2` >>
          reverse (Cases_on `lopt1`)
          >- (fs[loptrel_arg1_SOME] >> rveq >>
              imp_res_tac dest_closure_SOME_Full_app_args_nil >> fs[] >>
              rveq >> simp[]) >>
          qpat_x_assum `loptrel _ _ _ _` mp_tac >>
          simp[loptrel_arg1_NONE] >> reverse strip_tac >> rveq
          >- (imp_res_tac dest_closure_SOME_Full_app_args_nil >> fs[] >>
              rveq >> simp[])
          >- (imp_res_tac dest_closure_SOME_Full_app_args_nil >> fs[] >>
              rveq >> simp[]) >>
          first_x_assum irule >> simp[]
          >- metis_tac[ssgc_free_preserved_SING', ssgc_free_dec_clock]
          >- (patresolve `evaluate([exp1],_,_) = _` last ssgc_evaluate >>
              simp[])
          >- (patresolve `known [exp1] _ _ = _` hd known_correct_approx >>
              simp[] >> disch_then (resolve_selected last) >> simp[] >>
              metis_tac[ksrel_sga, ksrel_ssgc_free, kvrel_EVERY_vsgc_free])
          >- simp[loptrel_def])
      >- (imp_res_tac evaluate_SING >> fs[])
      >- (simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq] >>
          resolve_selected hd (GEN_ALL kvrel_dest_closure_SOME_Full) >>
          simp[PULL_EXISTS] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          simp[] >> rename1 `ksrel g s01 s02` >>
          `s02.clock = s01.clock` by fs[ksrel_def] >>
          imp_res_tac LIST_REL_LENGTH >> fs[] >> simp[PULL_EXISTS] >>
          dsimp[] >>
          map_every rename1 [
            `dest_closure _ lopt1 f1 (iarg1 :: iargs) =
               SOME (Full_app exp1 env1 args1)`,
            `evaluate([exp1],env1,dec_clock _ s01) = (Rerr err1, s1)`,
            `kerel envapx gg exp1 exp2`] >> fs[exp_rel_def] >>
          first_x_assum (patresolve `known [exp1] _ _ = _` last) >> simp[] >>             map_every rename1 [
            `evaluate([exp1],env1,
                      dec_clock (SUC (LENGTH iargs1) - LENGTH args2) s01)`,
            `LIST_REL (kvrel gg) env1 env2`] >>
          disch_then (qspecl_then [
             `env2`,
             `dec_clock (SUC (LENGTH iargs1) - LENGTH args2) s02`,
             `gg`] mp_tac) >> simp[] >>
          `set_globals exp1 = {||} ∧ EVERY vsgc_free env1 ∧
           EVERY vsgc_free args1 ∧ esgc_free exp1`
            by metis_tac[vsgc_free_Full_app_set_globals, EVERY_DEF,
                         set_globals_empty_esgc_free] >> simp[] >>
          qspec_then `[exp1]` mp_tac known_emptySetGlobals_unchanged_g >>
          disch_then (resolve_selected hd) >> simp[] >>
          disch_then SUBST_ALL_TAC >>
          rename1 `LIST_REL val_approx_val envapx env1` >>
          `LIST_REL val_approx_val envapx env1`
            by metis_tac[kvrel_LIST_REL_val_approx] >>
          `every_Fn_vs_NONE [exp1]`
            by metis_tac[kvrel_dest_closure_every_Fn_vs_NONE] >>
          impl_tac >- (simp[] >> fs[ksrel_def, dec_clock_def]) >> rw[] >>
          imp_res_tac state_rel_max_app >>
          simp[] >> fs[krrel_err_rw] >>
          rename1 `evaluate([exp2],_,_) = (res2,_)` >>
          Cases_on `res2`
          >- (imp_res_tac evaluate_SING >> simp[] >> metis_tac[pair_CASES]) >>
          simp[])))

val known_correct = save_thm(
  "known_correct",
  known_correct0 |> SIMP_RULE (srw_ss()) []);

val known_preserves_every_Fn_NONE = Q.store_thm(
  "known_preserves_every_Fn_NONE",
  `∀es as g0 alist g.
     known es as g0 = (alist,g) ∧ every_Fn_vs_NONE es ⇒
     every_Fn_vs_NONE (MAP FST alist)`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
  imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq
  >- (simp[Once every_Fn_vs_NONE_EVERY] >> simp[GSYM every_Fn_vs_NONE_EVERY])
  >- (every_case_tac >> simp[Once every_Fn_vs_NONE_EVERY])
  >- (simp[Once every_Fn_vs_NONE_EVERY] >>
      simp[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rpt strip_tac >>
      sel_ihpc hd >> rename1 `known[bod] env g0` >>
      Cases_on `known[bod] env g0` >> simp[] >> imp_res_tac known_sing_EQ_E >>
      rveq >> fs[] >> rveq >> disch_then irule >>
      fs[Once every_Fn_vs_NONE_EVERY] >>
      fs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> metis_tac[]));

val known_preserves_every_Fn_SOME = Q.store_thm(
  "known_preserves_every_Fn_SOME",
  `∀es as g0 alist g.
     known es as g0 = (alist,g) ∧ every_Fn_SOME es ⇒
     every_Fn_SOME (MAP FST alist)`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
  imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq
  >- (simp[Once every_Fn_SOME_EVERY]>>simp[GSYM every_Fn_SOME_EVERY])
  >- (every_case_tac >> simp[Once every_Fn_SOME_EVERY])
  >- (simp[Once every_Fn_SOME_EVERY] >>
      simp[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rpt strip_tac >>
      sel_ihpc hd >> rename1 `known[bod] env g0` >>
      Cases_on `known[bod] env g0` >> simp[] >> imp_res_tac known_sing_EQ_E >>
      rveq >> fs[] >> rveq >> disch_then irule >>
      fs[Once every_Fn_SOME_EVERY] >>
      fs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> metis_tac[]));

fun abbrevify (asl,g) =
  let val (l,r) = dest_imp g
      fun abc t = if is_forall t then REWR_CONV (GSYM markerTheory.Abbrev_def) t
                  else ALL_CONV t
  in
    if is_forall r then
      CONV_TAC (LAND_CONV (EVERY_CONJ_CONV abc)) >> strip_tac
    else ALL_TAC
  end (asl,g)

val unabbrevify = RULE_ASSUM_TAC (REWRITE_RULE [markerTheory.Abbrev_def])

val say = say0 "known_idem"
val merge_subapprox_cong = Q.store_thm(
  "merge_subapprox_cong",
  `a1 ◁ a2 ∧ b1 ◁ b2 ⇒ merge a1 b1 ◁ merge a2 b2`,
  simp[subapprox_def] >>
  metis_tac[merge_comm, merge_assoc]);

val known_op_increases_subspt_info = Q.store_thm(
  "known_op_increases_subspt_info",
  `∀opn as1 g0 a1 a2 g1 g2 as2 g.
     known_op opn as1 g0 = (a1,g1) ∧ subspt g0 g1 ∧ subspt g1 g2 ∧
     LIST_REL $◁ as2 as1 ∧ known_op opn as2 g2 = (a2,g)
    ⇒
     a2 ◁ a1 ∧ subspt g2 g`,
  rpt gen_tac >> Cases_on `opn` >>
  simp[known_op_def, case_eq_thms, va_case_eq, bool_case_eq, NULL_EQ] >>
  disch_then strip_assume_tac >> rveq >> simp[] >> fs[]
  >- (fs[subspt_def] >> metis_tac[domain_lookup, NOT_SOME_NONE])
  >- (fs[subspt_def] >> metis_tac[domain_lookup, subapprox_refl, SOME_11])
  >- fs[subspt_def, DISJ_IMP_THM, lookup_insert]
  >- (fs[subspt_def, DISJ_IMP_THM, lookup_insert, FORALL_AND_THM] >> rveq >>
      rw[] >> fs[subapprox_def, merge_comm])
  >- fs[subspt_def, lookup_insert, DISJ_IMP_THM]
  >- (fs[subspt_def, lookup_insert, DISJ_IMP_THM, FORALL_AND_THM] >> rveq >>
      rw[] >> fs[subapprox_def] >> metis_tac[merge_comm, merge_assoc])
  >- (fs[LIST_REL_EL_EQN] >>
      metis_tac[integerTheory.INT_INJ, integerTheory.INT_OF_NUM,
                integerTheory.INT_LT])
  >- (fs[LIST_REL_EL_EQN] >> rfs[]))

val known_increases_subspt_info = Q.store_thm(
  "known_increases_subspt_info",
  `∀es as1 g0 alist1 g1 g2 as2 alist2 g.
      known es as1 g0 = (alist1,g1) ∧ BAG_ALL_DISTINCT (elist_globals es) ∧
      subspt g0 g1 ∧ subspt g1 g2 ∧ LIST_REL $◁ as2 as1 ∧
      known es as2 g2 = (alist2,g)
     ⇒
      subspt g2 g ∧
      LIST_REL $◁ (MAP SND alist2) (MAP SND alist1)`,
  ho_match_mp_tac known_ind >> rpt conj_tac >> rpt gen_tac >> abbrevify >>
  fs[known_def, BAG_ALL_DISTINCT_BAG_UNION] >>
  rpt (gen_tac ORELSE disch_then strip_assume_tac)
  >- (rveq >> simp[])
  >- (rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      map_every rename1 [`LIST_REL _ (MAP SND alist2) (MAP SND alist1)`,
                           `known (exp2::es) as1 g01 = (alist1, g1)`,
                           `known [exp1] as1 g0 = ([(_,apx1)], g01)`,
                           `known [exp1] as2 g2 = ([(_,apx2)], g21)`] >>
      patresolve `known [_] _ g0 = _` hd subspt_known_elist_globals >> simp[] >>
      rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >> fs[] >>
      unabbrevify >>
      `subspt g01 g2` by metis_tac[subspt_trans] >>
      first_x_assum (resolve_selected hd) >> simp[] >>
      rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
      `subspt g2 g21` by metis_tac[] >>
      `subspt g1 g21` by metis_tac[subspt_trans] >>
      `subspt g21 g` by metis_tac[] >> metis_tac[subspt_trans])
  >- (say "var" >> rveq >> simp[any_el_ALT] >> fs[LIST_REL_EL_EQN] >> rw[])
  >- (say "if" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac known_sing_EQ_E >> rveq >>
      fs[PULL_EXISTS, EXISTS_PROD] >> rveq >>
      map_every rename1 [
        `merge apx2' apx3' ◁ merge apx2 apx3`,
        `known [tb] as1 g01 = ([(_,apx2)], g02)`,
        `known [tb] as2 g11 = ([(_,apx2')], g12)`,
        `known [eb] as1 g02 = ([(_,apx3)], g1)`,
        `known [ge] as1 g0 = ([(_,apx1)], g01)`] >>
      `∃apxs. known [ge;tb] as1 g0 = (apxs, g02)` by simp[known_def] >>
      resolve_selected hd subspt_known_elist_globals >> simp[] >>
      rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
      patresolve `known [ge] as1 g0 = _` hd subspt_known_elist_globals >>
      simp[] >>
      rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >> fs[] >>
      unabbrevify >>
      `subspt g01 g2` by metis_tac[subspt_trans] >>
      first_x_assum (resolve_selected hd) >> simp[] >>
      disch_then (resolve_selected last) >> simp[] >> strip_tac >>
      first_x_assum (patresolve `known [tb] as2 _ = _` (el 3)) >> simp[] >>
      impl_keep_tac
      >- metis_tac[subspt_trans] >> strip_tac >>
      first_x_assum (patresolve `known [eb] as2 _ = _` (el 3)) >> simp[] >>
      impl_keep_tac
      >- metis_tac[subspt_trans] >> strip_tac >>
      conj_tac >- metis_tac[subspt_trans] >>
      metis_tac[merge_subapprox_cong])
  >- (say "let" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      map_every rename1 [`apx' ◁ apx`,
                           `known [bod] _ g01 = ([(_, apx)], g02)`,
                           `known [bod] _ g21 = ([(_, apx')], g22)`,
                           `known binds as1 g0 = (_, g01)`,
                           `known binds as2 g2 = (_, g21)`] >>
      patresolve `known binds as1 g0 = _` hd subspt_known_elist_globals >>
      simp[] >>
      rpt (disch_then (resolve_selected hd) >> simp[]) >> impl_tac
      >- fs[BAG_DISJOINT, DISJOINT_SYM] >> strip_tac >> fs[] >> unabbrevify >>
      first_x_assum (patresolve `known binds as2 _ = _` (el 3)) >> simp[] >>
      impl_keep_tac >- metis_tac [subspt_trans] >> strip_tac >>
      first_x_assum (patresolve `known [bod] _ g21 = _` (el 3)) >>
      simp[EVERY2_APPEND_suff] >> impl_keep_tac >- metis_tac[subspt_trans] >>
      metis_tac[subspt_trans])
  >- (say "raise" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >> unabbrevify >>
      metis_tac[])
  >- (say "tick" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >> unabbrevify >>
      fs[EXISTS_PROD] >> metis_tac[CONS_11, PAIR_EQ])
  >- (say "handle" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      map_every rename1 [
        `merge apx1' apx2' ◁ merge apx1 apx2`,
        `known [exp1] as1 g0 = ([(_,apx1)], g01)`,
        `known [exp1] as2 g2 = ([(_,apx1')], g21)`,
        `known [hndlr] (Other::as1) g01 = ([(_,apx2)], g1)`,
        `known [hndlr] (Other::as2) g21 = ([(_,apx2')], gg)`] >>
      patresolve `known [exp1] as1 g0 = _` hd subspt_known_elist_globals >>
      simp[] >> disch_then (resolve_selected hd) >> simp[] >> strip_tac >>
      fs[] >> unabbrevify >>
      first_x_assum (patresolve `known [exp1] _ g2 = _` last) >> simp[] >>
      impl_keep_tac >- metis_tac[subspt_trans] >> strip_tac >>
      fs[PULL_EXISTS, EXISTS_PROD] >>
      first_x_assum (patresolve `known [hndlr] _ g21 = _` last) >> simp[] >>
      impl_keep_tac >- metis_tac[subspt_trans] >>
      metis_tac[merge_subapprox_cong, subspt_trans])
  >- (say "call" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >> unabbrevify >> metis_tac[])
  >- (say "op" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      map_every rename1 [`apx' ◁ apx`,
                           `known_op opn _ g01 = (apx,g1)`,
                           `known_op opn _ g21 = (apx',gg)`] >>
      patresolve `known_op _ _ g01 = _` (el 2) subspt_known_op_elist_globals >>
      simp[] >> disch_then (resolve_selected hd) >> simp[] >> strip_tac >>
      fs[] >> unabbrevify >>
      first_x_assum (patresolve `known _ _ g2 = _` last) >> simp[] >>
      impl_keep_tac >- metis_tac[subspt_trans] >> strip_tac >>
      patresolve `known_op _ _ g01 = _` hd known_op_increases_subspt_info >>
      simp[] >>
      disch_then (patresolve `known_op _ _ g21 = _` last) >>
      simp[LIST_REL_REVERSE_EQ] >> metis_tac[subspt_trans])
  >- (say "app" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      map_every rename1 [`subspt g2 gg`, `subspt g1 g2`,
                           `known args as2 g2 = (_, g21)`,
                           `known [f] as1 g11 = (_, g1)`] >>
      patresolve `known _ _ _ = (_, g11)` hd subspt_known_elist_globals >>
      simp[] >>
      disch_then (resolve_selected hd) >> simp[] >> impl_keep_tac
      >- fs[BAG_DISJOINT, DISJOINT_SYM] >> strip_tac >> fs[] >> unabbrevify >>
      first_x_assum (patresolve `known _ _ g2 = _` last) >> simp[] >>
      impl_keep_tac >- metis_tac[subspt_trans] >> strip_tac >>
      first_x_assum (patresolve `known _ _ g21 = _` last) >> simp[] >>
      metis_tac[subspt_trans])
  >- (say "fn" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >> rveq >> unabbrevify >>
      rename1 `subspt gg2 gg` >>
      first_x_assum (patresolve `known _ _ gg2 = _` last) >>
      simp[] >> reverse impl_tac >- metis_tac[subspt_trans] >>
      simp[LIST_REL_REPLICATE_same, EVERY2_APPEND_suff])
  >- (say "letrec" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[letrec_case_eq] >> rveq >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      map_every rename1 [`apx1' ◁ apx1`,
                           `known [bod] _ g0 = ([(_,apx1)], g1)`,
                           `known [bod] _ g2 = ([(_,apx1')], g)`] >>
      unabbrevify >>
      first_x_assum (patresolve `subspt g1 _` hd) >> simp[] >>
      disch_then (first_assum o mp_then (Pos last) mp_tac) >> simp[] >>
      disch_then irule >> irule EVERY2_APPEND_suff >> simp[] >>
      simp[LIST_REL_GENLIST]))

val sga_subspt = Q.store_thm(
  "sga_subspt",
  `state_globals_approx s g0 ∧ subspt g0 g ⇒ state_globals_approx s g`,
  simp[state_globals_approx_def, subspt_def] >> rw[] >> fs[get_global_def] >>
  nailIHx strip_assume_tac >> metis_tac[domain_lookup]);

val state_globals_LN = Q.store_thm(
  "state_globals_LN",
  `state_globals_approx s LN ⇔ ∀n v. get_global n s.globals ≠ SOME (SOME v)`,
  simp[state_globals_approx_def] >> simp[lookup_def]);

(* Optionally applied state relation and result relation*)
val opt_state_rel_def = Define`
  opt_state_rel b g s1 s2 ⇔
  if b then state_rel g s1 s2
       else s1 = s2`

val opt_res_rel_def = Define`
  opt_res_rel b g r1 r2 ⇔
  if b then res_rel g r1 r2
        else r1 = r2`

(* Some assumptions can be removed if b = F *)
val compile_correct = Q.store_thm(
  "compile_correct",
  `compile b e0 = e ∧ evaluate ([e0], [], s01) = (res1, s1) ∧
   esgc_free e0 ∧ every_Fn_vs_NONE [e0] ∧
   opt_state_rel b LN s01 s02 ∧
   state_globals_approx s01 LN ∧ BAG_ALL_DISTINCT (set_globals e0) ∧
   ssgc_free s01
    ⇒
   ∃res2 s2 g.
     evaluate([e], [], s02) = (res2, s2) ∧
     opt_res_rel b g (res1,s1) (res2,s2)`,
  reverse (Cases_on`b`)>>
  simp[compile_def,opt_state_rel_def,opt_res_rel_def] >- metis_tac[]>>
  rpt (pairarg_tac >> simp[]) >>
  map_every rename1 [`known [e0] [] LN = (alist0, g1)`,
                       `known [e0] [] g1 = (alist, g)`] >>
  imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rw[] >>
  patresolve `known _ _ LN = _` hd known_increases_subspt_info >> simp[] >>
  disch_then (patresolve `known _ _ g1 = _` (el 2)) >> simp[] >> strip_tac >>
  patresolve `known _ _ g1 = _` last (CONJUNCT1 known_correct) >> simp[] >>
  disch_then (resolve_selected hd) >> simp[] >>
  `ksrel g s01 s02` by metis_tac[ksrel_subspt, subspt_LN] >>
  disch_then (resolve_selected (el 2)) >> simp[] >>
  metis_tac[sga_subspt, subspt_LN])

val known_code_locs = Q.store_thm("known_code_locs",
  `∀xs vs g.
   code_locs (MAP FST (FST (known xs vs g))) = code_locs xs`,
  ho_match_mp_tac known_ind
  \\ rw[known_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rw[code_locs_append]
  \\ fs[code_locs_def]
  \\ imp_res_tac known_sing_EQ_E \\ fs[]
  >- (every_case_tac >> simp[code_locs_def] >>
      rename[`isGlobal opn`, `gO_destApx apx`] >>
      Cases_on `opn` >> fs[isGlobal_def] >> Cases_on `apx` >>
      fs[gO_destApx_def, known_op_def, bool_case_eq, NULL_EQ, case_eq_thms] >> rveq >>
      imp_res_tac known_LENGTH_EQ_E >> fs[LENGTH_NIL_SYM, code_locs_def])
  \\ fs[code_locs_map]
  \\ AP_TERM_TAC
  \\ simp[MAP_MAP_o,MAP_EQ_f,FORALL_PROD]
  \\ rw[]
  \\ first_x_assum drule
  \\ qmatch_goalsub_abbrev_tac`FST p`
  \\ Cases_on`p` \\ fs[markerTheory.Abbrev_def]
  \\ pop_assum(assume_tac o SYM)
  \\ imp_res_tac known_sing_EQ_E \\ fs[]);

val compile_code_locs = Q.store_thm("compile_code_locs",
  `code_locs [compile b e] = code_locs [e]`,
  Cases_on`b` \\ rw[compile_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ pop_assum mp_tac
  \\ specl_args_of_then``known``known_code_locs mp_tac
  \\ rw[] \\ fs[]
  \\ pop_assum mp_tac
  \\ specl_args_of_then``known``known_code_locs mp_tac
  \\ rw[] \\ fs[]
  \\ imp_res_tac known_sing_EQ_E \\ fs[]);

(*
vsgc_free_def
ssgc_free_def
esgc_free_def
set_globals_def
compile_correct
state_globals_approx_def
clos_knownTheory.compile_def
val_rel_def
*)

*)

val _ = export_theory();
