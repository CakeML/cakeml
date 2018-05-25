open preamble backendPropsTheory
open closPropsTheory clos_knownTheory clos_knownPropsTheory closSemTheory
open bagTheory
open mp_then
open closLangTheory
open db_varsTheory

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
  \\ fs [inlD_case_eq]
  \\ rpt (pairarg_tac  \\ fs []) \\ rveq
  \\ fs [bool_case_eq]
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
  THEN1 (fs [inlD_case_eq]
         \\ rpt (pairarg_tac \\ fs [])
         \\ fs [bool_case_eq]));

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
  `!es co. unique_set_globals es co ==> !k. unique_set_globals es (shift_seq k co)`,
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
   !k. co_disjoint_globals g (shift_seq k co)`,
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

(* Value approximation is sgc free *)

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

(* alternative val_approx to value relation *)

val (val_approx_val_rules, val_approx_val_ind, val_approx_val_cases) = Hol_reln `
  (!v. val_approx_val Other v) /\
  (!i. val_approx_val (Int i) (Number i)) /\
  (!tg vas vs.
     LIST_REL val_approx_val vas vs ==>
     val_approx_val (Tuple tg vas) (Block tg vs)) /\
  (!m n env b. val_approx_val (ClosNoInline m n) (Closure (SOME m) [] env n b)) /\
  (!m n env base fs j.
     m = base + 2*j /\ j < LENGTH fs /\ n = FST (EL j fs) ==>
     val_approx_val (ClosNoInline m n) (Recclosure (SOME base) [] env fs j)) /\
  (!m n b s env. val_approx_val (Clos m n b s) (Closure (SOME m) [] env n b))`;

val val_approx_val_simps = save_thm("val_approx_val_simps[simp]",LIST_CONJ [
  SIMP_CONV (srw_ss()) [val_approx_val_cases] ``val_approx_val Other v``,
  SIMP_CONV (srw_ss()) [val_approx_val_cases] ``val_approx_val (Int i) v``,
  SIMP_CONV (srw_ss()) [val_approx_val_cases] ``val_approx_val (Tuple tg vas) v``,
  SIMP_CONV (srw_ss()) [val_approx_val_cases] ``val_approx_val (ClosNoInline m n) v``,
  SIMP_CONV (srw_ss()) [val_approx_val_cases] ``val_approx_val (Clos m n b1 s) v``,
  prove(``val_approx_val Impossible v <=> F``, simp [val_approx_val_cases])
]);

val val_approx_val_merge_I_lemma = Q.store_thm(
  "val_approx_val_merge_I_lemma",
  `!a1 v. val_approx_val a1 v ==> !a2. val_approx_val (merge a1 a2) v`,
  ho_match_mp_tac val_approx_val_ind
  \\ rw [] \\ Cases_on `a2` \\ fs []
  \\ TRY (IF_CASES_TAC \\ fs [] \\ rveq)
  THEN1 fs [LIST_REL_EL_EQN,  MAP2_MAP, EL_MAP, EL_ZIP]
  THEN1 (fs [LIST_REL_EL_EQN] \\ rfs [] \\ rw [] \\ res_tac
         \\ first_x_assum (qspec_then `Impossible` assume_tac) \\ fs []));

val val_approx_val_merge_I = Q.store_thm(
  "val_approx_val_merge_I",
  `!a1 v a2.
     val_approx_val a1 v \/ val_approx_val a2 v ==>
     val_approx_val (merge a1 a2) v`,
  metis_tac [val_approx_val_merge_I_lemma, merge_comm]);

val val_approx_better_approx_lemma = Q.store_thm(
  "val_approx_better_approx_lemma",
  `!a1 v. val_approx_val a1 v ==> !a2. a1 ◁ a2 ==> val_approx_val a2 v`,
  ho_match_mp_tac val_approx_val_ind
  \\ rw [] \\ simp []
  \\ rename1 `Tuple _ _ ◁ apx2`
  \\ Cases_on `apx2` \\ simp []
  \\ fs [LIST_REL_EL_EQN] \\ metis_tac [MEM_EL]);

val val_approx_better_approx = Q.store_thm(
  "val_approx_better_approx",
  `!a1 v a2. a1 ◁ a2 /\ val_approx_val a1 v ==> val_approx_val a2 v`,
  metis_tac [val_approx_better_approx_lemma]);

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

val known_op_correct_approx = Q.store_thm(
  "known_op_correct_approx",
  `!opn args g0 a g vs s0 g' v s.
   known_op opn args g0 = (a, g) /\ LIST_REL val_approx_val args vs /\
   state_globals_approx s0 g' /\ subspt g g' /\
   do_app opn vs s0 = Rval (v, s) ⇒
   state_globals_approx s g' /\ val_approx_val a v`,
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
  `ssgc_free s ==> !k. ssgc_free (s with compile_oracle := shift_seq k s.compile_oracle)`,
  simp [PULL_FORALL] \\ gen_tac
  \\ simp [ssgc_free_def] \\ strip_tac \\ rpt conj_tac \\ fs []
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
  `!s1 gd s2 g.
     mglobals_extend s1 gd s2 /\
     state_globals_approx s1 g /\
     DISJOINT (domain g) gd
     ==>
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

val known_op_preserves_esgc_free = Q.store_thm(
  "known_op_preserves_esgc_free",
  `!opn args g0 a g.
     known_op opn args g0 = (a, g) /\
     EVERY val_approx_sgc_free args /\
     globals_approx_sgc_free g0 ==>
     val_approx_sgc_free a /\ globals_approx_sgc_free g`,
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

val decide_inline_LetInline_IMP_Clos = Q.store_thm(
  "decide_inline_LetInline_IMP_Clos",
  `!c fapx lopt arity body.
     decide_inline c fapx lopt arity = inlD_LetInline body ==>
       ?m s. fapx = Clos m arity body s`,
  rpt strip_tac
  \\ Cases_on `fapx` \\ fs [decide_inline_def, bool_case_eq]);

val decide_inline_LetInline_IMP_Clos_lopt = Q.store_thm(
  "decide_inline_LetInline_IMP_Clos_lopt",
  `!c fapx lopt arity body.
     decide_inline c fapx lopt arity = inlD_LetInline body ==>
       ?m s. fapx = Clos m arity body s /\
             (lopt = NONE \/ lopt = SOME m)`,
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
  THEN1 (fs [inlD_case_eq]
         \\ rpt (pairarg_tac \\ fs []) \\ rveq
         \\ fs [bool_case_eq, SUB_BAG_UNION]
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

val every_var_def = Define `
  (every_var P Empty = T) /\
  (every_var P (Var v) <=> P v) /\
  (every_var P (Shift k d) <=> every_var (\v. k <= v ==> P (v - k)) d) /\
  (every_var P (Union d1 d2) <=> every_var P d1 /\ every_var P d2)
`;

val every_var_mk_Union = Q.store_thm("every_var_mk_Union[simp]",
  `every_var P (mk_Union d1 d2) <=> every_var P d1 /\ every_var P d2`,
  simp [mk_Union_def] \\ rpt (IF_CASES_TAC \\ simp [every_var_def]));

val fv_max_def = Define `fv_max n xs = !v. fv v xs ==> v < n`;

val fv_alt = Q.store_thm("fv_alt",
  `!n xs. fv n xs <=> has_var n (SND (free xs))`,
  ho_match_mp_tac fv_ind \\ rw []
  \\ simp [free_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ TRY (simp [Once fv1_def, fv_def] \\ NO_TAC)
  \\ eq_tac
  THEN1 (simp [Once fv1_def, fv_def]
         \\ strip_tac \\ simp [] \\ disj1_tac 
         \\ simp [EXISTS_MAP]
         \\ fs [EXISTS_MEM]
         \\ asm_exists_tac
         \\ rpt (pairarg_tac \\ fs [])
         \\ metis_tac [SND])
  THEN1 (simp [Once fv1_def, fv_def] \\ simp []
         \\ strip_tac \\ simp [] \\ disj1_tac
         \\ fs [EXISTS_MAP]
         \\ fs [EXISTS_MEM]
         \\ rpt (pairarg_tac \\ fs [])
         \\ asm_exists_tac \\ simp []));

val fv1_alt = Q.store_thm("fv1_alt",
  `fv1 n x = has_var n (SND (free [x]))`,
  once_rewrite_tac [fv1_def] \\ metis_tac [fv_alt]);

val fv_max_rw = Q.store_thm("fv_max_rw",
  `(fv_max n [] <=> T) /\
   (fv_max n (x::y::xs) <=> fv_max n [x] /\ fv_max n (y::xs)) /\
   (fv_max n [Var tr v] <=> v < n) /\
   (fv_max n [If tr x1 x2 x3] <=> fv_max n [x1] /\ fv_max n [x2] /\ fv_max n [x3]) /\
   (fv_max n [Let tr xs x1] <=> fv_max n xs /\ fv_max (n + LENGTH xs) [x1]) /\
   (fv_max n [Raise tr x1] <=> fv_max n [x1]) /\
   (fv_max n [Tick tr x1] <=> fv_max n [x1]) /\
   (fv_max n [Op tr opn xs] <=> fv_max n xs) /\
   (fv_max n [App tr lopt x1 xs] <=> fv_max n [x1] /\ fv_max n xs) /\
   (fv_max n [Fn tr loc vs num_args x1] <=> fv_max (n + num_args) [x1]) /\
   (fv_max n [Letrec tr loc vs fns x1] <=>
      EVERY (\(num_args, x). fv_max (n + num_args + LENGTH fns) [x]) fns /\
      fv_max (n + LENGTH fns) [x1]) /\
   (fv_max n [Handle tr x1 x2] <=> fv_max n [x1] /\ fv_max (n + 1) [x2]) /\
   (fv_max n [Call tr ticks dest xs] <=> fv_max n xs)`,
  rpt conj_tac \\ fs [fv_max_def]
  \\ dsimp [Once fv1_def, fv_def]
  THEN1
   (eq_tac \\ rw []
    THEN1 (first_x_assum (qspec_then `v - LENGTH xs` assume_tac)
           \\ Cases_on `v < LENGTH xs` \\ fs [])
    THEN1 (first_x_assum (qspec_then `v + LENGTH xs` assume_tac) \\ fs []))
  THEN1
   (eq_tac \\ rw []
    THEN1 (first_x_assum (qspec_then `v - num_args` assume_tac)
           \\ Cases_on `v < num_args` \\ fs [])
    THEN1 (first_x_assum (qspec_then `v + num_args` assume_tac) \\ fs []))
  THEN1
   (eq_tac \\ rw []
    THEN1 (fs [EVERY_MEM, EXISTS_MEM, PULL_EXISTS]
           \\ rw [] \\ res_tac
           \\ pairarg_tac \\ fs [] \\ rw []
           \\ first_x_assum (qspec_then `v - num_args - LENGTH fns` assume_tac)
           \\ Cases_on `v < num_args + LENGTH fns` \\ fs [])
    THEN1 (first_x_assum (qspec_then `v - LENGTH fns` assume_tac)
           \\ Cases_on `v < LENGTH fns` \\ fs [])
    THEN1 (fs [EVERY_MEM, EXISTS_MEM]
           \\ res_tac
           \\ pairarg_tac \\ fs []
           \\ first_x_assum (qspec_then `v + num_args + LENGTH fns` assume_tac)
           \\ rfs [])
    THEN1 (first_x_assum (qspec_then `v + LENGTH fns` assume_tac) \\ fs []))
  THEN1
   (eq_tac \\ rw []
    THEN1 (first_x_assum (qspec_then `v - 1` assume_tac)
           \\ Cases_on `v < 1` \\ fs [])
    THEN1 (first_x_assum (qspec_then `v + 1` assume_tac) \\ fs [])))

val fv_max_mk_Ticks = Q.store_thm(
  "fv_max_mk_Ticks[simp]",
  `!t trc i e. fv_max n [mk_Ticks t trc i e] <=> fv_max n [e]`,
  Induct_on `i` \\ simp [mk_Ticks_alt, fv_max_rw]);

val fv_max_cons = Q.store_thm(
  "fv_max_cons",
  `fv_max n (h::t) <=> fv_max n [h] /\ fv_max n t`,
  simp [fv_max_def] \\ eq_tac \\ rw [] \\ res_tac);

val fv_max_append = Q.store_thm(
  "fv_max_append[simp]",
  `!xs ys n. fv_max n (xs ++ ys) <=> fv_max n xs /\ fv_max n ys`,
  Induct \\ simp [fv_max_rw] \\ metis_tac [fv_max_cons]);

val decide_inline_LetInline_IMP_Clos_fv_max = Q.store_thm(
  "decide_inline_LetInline_IMP_Clos_fv_max",
  `!c fapx lopt arity body.
     decide_inline c fapx lopt arity = inlD_LetInline body ==>
       ?m s. fapx = Clos m arity body s /\
             fv_max arity [body]`,
  rpt strip_tac
  \\ Cases_on `fapx` \\ fs [decide_inline_def, bool_case_eq]
  \\ fs [fv_max_def, fv1_alt] \\ rpt strip_tac \\ rveq
  \\ fs [closed_def, free_def]
  \\ pairarg_tac \\ fs []
  \\ imp_res_tac (Q.prove(`isEmpty sp ==> !n. lookup n sp = NONE`, simp [lookup_def]))
  \\ fs [db_to_set_def, lookup_db_to_set_acc]
  \\ rename1 `v < arity`
  \\ Cases_on `v < arity` \\ simp []
  \\ first_x_assum (qspec_then `v - arity` mp_tac)
  \\ simp []);

val fv_max_less = Q.store_thm(
  "fv_max_less",
  `!m n xs. fv_max m xs /\ m <= n ==> fv_max n xs`,
  simp [fv_max_def] \\ rw [] \\ res_tac \\ fs [])

val known_preserves_fv_max = Q.store_thm(
  "known_preserves_fv_max",
  `!c es aenv g0 eas1 g n.
     known c es aenv g0 = (eas1, g) /\
     fv_max n es ==>
     fv_max n (MAP FST eas1)`,
  ho_match_mp_tac known_ind
  \\ simp [known_def, fv_max_rw]
  \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ imp_res_tac known_sing_EQ_E
  \\ imp_res_tac known_LENGTH_EQ_E
  \\ fs [] \\ rveq
  \\ fs [fv_max_rw]
  THEN1
   (fs [fv_max_def] \\ rw [] \\ res_tac)
  THEN1
   (every_case_tac \\ fs [fv_max_rw])
  THEN1
   (fs [inlD_case_eq] \\ rveq \\ fs [fv_max_rw]
    \\ rpt (pairarg_tac \\ fs [])
    \\ imp_res_tac known_sing_EQ_E
    \\ imp_res_tac decide_inline_LetInline_IMP_Clos_fv_max
    \\ fs [bool_case_eq, fv_max_rw] \\ rveq
    \\ res_tac
    \\ match_mp_tac fv_max_less
    \\ asm_exists_tac \\ simp [])
  THEN1
   (dsimp [EVERY_MEM, MEM_MAP] \\ rw []
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ qmatch_goalsub_abbrev_tac `HD (FST knownres)`
    \\ `?exp apx gdead. knownres = ([exp, apx], gdead)`
       by (unabbrev_all_tac \\ simp [known_sing])
    \\ rveq \\ fs []
    \\ first_x_assum drule \\ simp [] \\ strip_tac
    \\ fs [EVERY_MEM]
    \\ first_x_assum drule \\ simp []));

val known_extra = Q.store_thm(
  "known_extra",
  `!c xs aenv g0 extra1 extra2.
     fv_max (LENGTH aenv) xs ==>
     known c xs (aenv ++ extra1) g0 = known c xs (aenv) g0`,
  ho_match_mp_tac known_ind
  \\ rpt strip_tac
  \\ fs [known_def, fv_max_rw]
  \\ rpt (pairarg_tac \\ fs [])
  THEN1 (simp [any_el_ALT, EL_APPEND1])
  THEN1 (imp_res_tac known_LENGTH_EQ_E \\ fs [] \\ rfs [])
  THEN1 (fs [ADD1] \\ rfs [])
  THEN1 (fs [clos_gen_noinline_eq]
         \\ TOP_CASE_TAC \\ fs [] \\ rfs [] \\ fs []
         \\ simp [MAP_EQ_f, PULL_FORALL, FORALL_PROD]
         \\ rpt strip_tac \\ fs [EVERY_MEM]
         \\ res_tac \\ fs []));

val say = say0 "known_correct_approx";

val known_correct_approx = Q.store_thm(
  "known_correct_approx",
  `!c xs aenv g0 eas g g' env extra (s0:('c, 'ffi) closSem$state) res s.
   known c xs aenv g0 = (eas,g) /\
   evaluate (xs, env ++ extra, s0) = (res, s) /\
   fv_max (LENGTH env) xs /\
   unique_set_globals xs s0.compile_oracle /\
   LIST_REL val_approx_val aenv env /\
   state_globals_approx s0 g' /\
   subspt g0 g /\ subspt g g' /\
   co_disjoint_globals g' s0.compile_oracle /\
   ssgc_free s0 /\ EVERY vsgc_free (env ++ extra) /\ EVERY esgc_free xs /\
   EVERY val_approx_sgc_free aenv /\ globals_approx_sgc_free g0
   ==>
     state_globals_approx s g' /\
     !vs. res = Rval vs ==> LIST_REL val_approx_val (MAP SND eas) vs`,
  ho_match_mp_tac known_ind \\ simp [known_def]
  \\ rpt conj_tac \\ rpt (gen_tac ORELSE disch_then strip_assume_tac)
  \\ imp_res_tac evaluate_SING \\ rveq
  \\ imp_res_tac unique_set_globals_subexps
  THEN1
   (say "NIL" \\ fs [evaluate_def] \\ rveq \\ fs [])
  THEN1
   (say "CONS"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ rename1 `known _ _ _ g0 = (_, g1)`
    \\ fs [evaluate_def, pair_case_eq]
    \\ `subspt g0 g1 /\ subspt g1 g`
       by (match_mp_tac subspt_known_elist_globals
           \\ asm_exists_tac \\ simp []
           \\ goal_assum drule
           \\ fs [unique_set_globals_def, elist_globals_append]
           \\ fs [BAG_ALL_DISTINCT_BAG_UNION])
    \\ fs [fv_max_rw]
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ impl_tac THEN1 metis_tac [subspt_trans]
    \\ fs [result_case_eq] \\ rveq \\ fs [] \\ strip_tac
    \\ fs [pair_case_eq]
    \\ patresolve `unique_set_globals (_::_) _` hd unique_set_globals_evaluate
    \\ disch_then drule \\ simp [] \\ strip_tac
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ patresolve `known _ [_] _ _ = _` (el 1) known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ drule co_disjoint_globals_evaluate \\ disch_then drule
    \\ simp [] \\ disch_then kall_tac
    \\ rename1 `evaluate ([_], _, _) = (_, s1)`
    \\ `ssgc_free s1`
       by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
           \\ rpt (disch_then drule \\ simp []))
    \\ simp [] \\ strip_tac
    \\ imp_res_tac known_sing_EQ_E
    \\ fs [result_case_eq] \\ rveq \\ fs [])
  THEN1
   (say "Var"
    \\ fs [evaluate_def, bool_case_eq] \\ rveq
    \\ fs [any_el_ALT] \\ fs [fv_max_rw, EL_APPEND1, LIST_REL_EL_EQN])
  THEN1
   (say "If"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ rename1 `known limit [x1] aenv g0 = ([(e1,a1)], g1)`
    \\ rename1 `known limit [x2] aenv g1 = ([(e2,a2)], g2)`
    \\ rename1 `known limit [x3] aenv g2 = ([(e3,a3)], g)`
    \\ `subspt g0 g1 /\ subspt g1 g2 /\ subspt g2 g`
       by (`?unused. known limit [x1;x2] aenv g0 = (unused, g2)` by simp [known_def]
           \\ drule subspt_known_elist_globals
           \\ rpt (disch_then drule)
           \\ impl_tac THEN1 fs [unique_set_globals_def,BAG_ALL_DISTINCT_BAG_UNION]
           \\ strip_tac \\ simp []
           \\ match_mp_tac subspt_known_elist_globals
           \\ asm_exists_tac \\ simp []
           \\ goal_assum drule
           \\ fs [unique_set_globals_def,BAG_ALL_DISTINCT_BAG_UNION])
    \\ `subspt g1 g' /\ subspt g2 g'` by metis_tac [subspt_trans]
    \\ fs [evaluate_def, pair_case_eq]
    \\ fs [fv_max_rw]
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ fs [result_case_eq] \\ rveq \\ fs []
    \\ strip_tac \\ rveq
    \\ rename1 `evaluate (_, _, s0) = (_, s1)`
    \\ `ssgc_free s1`
       by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
           \\ rpt (disch_then drule \\ simp []))
    \\ patresolve `known _ _ _ g0 = _` (el 1) known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ patresolve `known _ _ _ g1 = _` (el 1) known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ drule co_disjoint_globals_evaluate
    \\ disch_then drule \\ simp [] \\ strip_tac
    \\ fs [bool_case_eq] \\ fixeqs
    \\ rename1 `evaluate ([x_taken_branch], _, s1) = (res, s)`
    \\ patresolve `unique_set_globals [x_taken_branch] _` hd unique_set_globals_evaluate
    \\ disch_then drule \\ simp [] \\ strip_tac
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ Cases_on `res` \\ fs [] \\ strip_tac \\ rveq \\ fs []
    \\ metis_tac [val_approx_val_merge_I])
  THEN1
   (say "Let"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ rename1 `known _ xs _ g0 = (ea1, g1)`
    \\ rename1 `known _ [x2] _ g1 = ([(e2,a2)], g)`
    \\ `subspt g0 g1 /\ subspt g1 g`
       by (match_mp_tac subspt_known_elist_globals
           \\ rpt (goal_assum drule \\ simp [])
           \\ fs [unique_set_globals_def,
                  BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
    \\ `subspt g1 g'` by metis_tac [subspt_trans]
    \\ fs [fv_max_rw]
    \\ fs [evaluate_def, pair_case_eq]
    \\ first_x_assum drule \\ rpt (disch_then drule)
    \\ fs [result_case_eq] \\ rveq \\ fs [] \\ strip_tac
    \\ patresolve `unique_set_globals [_] _` hd unique_set_globals_evaluate
    \\ disch_then drule \\ strip_tac
    \\ rename1 `evaluate (_, _, s0) = (Rval vs, s1)`
    \\ `ssgc_free s1 /\ EVERY vsgc_free vs`
       by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
           \\ rpt (disch_then drule \\ simp []))
    \\ first_x_assum drule
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ drule co_disjoint_globals_evaluate \\ disch_then drule \\ strip_tac
    \\ disch_then match_mp_tac \\ simp []
    \\ patresolve `known _ _ _ g0 = _` (el 1) known_preserves_esgc_free
    \\ simp [] \\ strip_tac \\ fs []
    \\ irule EVERY2_APPEND_suff \\ simp [])
  THEN1
   (say "Raise"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ fs [evaluate_def, pair_case_eq]
    \\ fs [fv_max_rw]
    \\ first_x_assum drule \\ rpt (disch_then drule)
    \\ fs [case_eq_thms] \\ rveq \\ fs [])
  THEN1
   (say "Tick"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ fs [evaluate_def, pair_case_eq]
    \\ Cases_on `s0.clock = 0` \\ fs [] \\ rveq \\ fs []
    \\ fs [fv_max_rw]
    \\ first_x_assum (qpat_assum `evaluate _ = _` o mp_then Any match_mp_tac)
    \\ fs [dec_clock_def])
  THEN1
   (say "Handle"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ rename1 `known limit [x1] _ g0 = ([(e1,a1)], g1)`
    \\ rename1 `known limit [x2] _ g1 = ([(e2,a2)], g)`
    \\ fs [evaluate_def, pair_case_eq]
    \\ `subspt g0 g1 /\ subspt g1 g`
       by (match_mp_tac subspt_known_elist_globals
           \\ rpt (asm_exists_tac \\ simp [])
           \\ fs [unique_set_globals_def,
                  BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
    \\ `subspt g1 g'` by metis_tac [subspt_trans]
    \\ fs [fv_max_rw]
    \\ first_x_assum drule \\ rpt (disch_then drule) \\ strip_tac
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    THEN1 (fs [val_approx_val_merge_I])
    \\ rename1 `evaluate (_,_,s0) = (Rerr (Rraise v), s1)`
    \\ `unique_set_globals [x2] s1.compile_oracle`
         by metis_tac [unique_set_globals_evaluate]
    \\ drule co_disjoint_globals_evaluate \\ disch_then drule \\ strip_tac
    \\ patresolve `known _ _ _ g0 = _` (el 1) known_preserves_esgc_free
    \\ simp [] \\ strip_tac \\ fs []
    \\ `ssgc_free s1 /\ vsgc_free v`
       by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
           \\ rpt (disch_then drule \\ simp []))
    \\ first_x_assum (qspecl_then [`g'`, `[v] ++ env`] mp_tac)
    \\ simp [] \\ rpt (disch_then drule) \\ strip_tac
    \\ Cases_on `res`
    \\ fs [val_approx_val_merge_I])
  THEN1
   (say "Call"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, pair_case_eq]
    \\ fs [fv_max_rw]
    \\ first_x_assum drule \\ rpt (disch_then drule) \\ strip_tac
    \\ fs [case_eq_thms, pair_case_eq, bool_case_eq] \\ rveq \\ fs []
    \\ rename1 `evaluate (_, _, s0) = (Rval vs, s1)`
    \\ fixeqs
    \\ patresolve `known _ _ _ g0 = _` (el 1) known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ `ssgc_free s1 /\ EVERY vsgc_free vs`
       by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
           \\ rpt (disch_then drule \\ simp []))
    \\ rename1 `find_code _ _ _ = SOME (args, exp)`
    \\ `set_globals exp = {||} /\ EVERY vsgc_free args`
       by (fs [find_code_def, case_eq_thms, pair_case_eq]
           \\ metis_tac [ssgc_free_def])
    \\ patresolve `evaluate ([exp],_,_) = _` (el 1) evaluate_changed_globals
    \\ simp [dec_clock_def, set_globals_empty_esgc_free] \\ strip_tac
    \\ patresolve `evaluate ([exp],_,_) = _` (el 1) evaluate_changed_globals
    \\ simp [dec_clock_def, set_globals_empty_esgc_free]
    \\ drule mglobals_extend_DISJOINT_state_globals_approx
    \\ disch_then drule
    \\ impl_tac
    THEN1 metis_tac [co_disjoint_globals_first_n_exps, co_disjoint_globals_evaluate]
    \\ metis_tac [evaluate_SING])
  THEN1
   (say "Op"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ rename1 `known _ _ _ g0 = (ea1, g1)`
    \\ rename1 `[Op _ opn _]`
    \\ `subspt g0 g1 /\ subspt g1 g`
       by (match_mp_tac subspt_known_op_elist_globals
           \\ rpt (goal_assum drule)
           \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION])
    \\ `subspt g1 g'` by metis_tac [subspt_trans]
    \\ fs [evaluate_def, pair_case_eq]
    \\ fs [fv_max_rw]
    \\ first_x_assum drule \\ rpt (disch_then drule) \\ strip_tac
    \\ fs [result_case_eq] \\ rveq \\ fs [] 
    \\ reverse (Cases_on `opn = Install`) \\ fs []
    THEN1
     (fs [case_eq_thms, pair_case_eq] \\ rveq \\ fs []
      \\ irule known_op_correct_approx
      \\ rpt (goal_assum drule \\ simp []))
    THEN1
     (reverse (fs [pair_case_eq, case_eq_thms])
      THEN1 (fs [do_install_def, case_eq_thms] \\ rveq \\ fs []
           \\ pairarg_tac \\ fs []
           \\ fs [bool_case_eq, pair_case_eq, case_eq_thms] \\ rveq \\ fs [])
      \\ reverse conj_tac
      THEN1 (Cases_on `res` \\ fs [known_op_def]
             \\ imp_res_tac evaluate_SING
             \\ rveq \\ simp [])
      \\ rveq
      \\ match_mp_tac known_op_install_correct_approx
      \\ rpt (goal_assum drule \\ simp [])
      \\ rename1 `do_install _ s1 = (_, s2)`
      \\ `ssgc_free s1`
         by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
             \\ rpt (disch_then drule)
             \\ drule known_preserves_esgc_free \\ simp [])
      \\ metis_tac [co_disjoint_globals_evaluate]))
  THEN1
   (say "App"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ rename1 `known _ [x1] _ g1 = _`
    \\ fs [fv_max_rw]
    \\ reverse (fs [inlD_case_eq])
    THEN1 
     ((* inlD_LetInline *)
      Cases_on `pure x1` \\ fs []
      (* both the pure and non-pure cases are solved by the following script *)
      \\ rpt (pairarg_tac \\ fs []) \\ rveq
      \\ rename1 `known _ [x1] _ g1 = (_, g)`
      \\ `subspt g0 g1 /\ subspt g1 g`
           by (match_mp_tac subspt_known_elist_globals
               \\ rpt (goal_assum drule)
               \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
      \\ `subspt g1 g'` by metis_tac [subspt_trans]
      \\ fs [evaluate_def, pair_case_eq, bool_case_eq]
      \\ first_x_assum drule \\ rpt (disch_then drule) \\ strip_tac
      \\ fs [result_case_eq] \\ rveq \\ fs []
      \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
      \\ fs [pair_case_eq]
      \\ `unique_set_globals [x1] s1.compile_oracle` by metis_tac [unique_set_globals_evaluate]
      \\ patresolve `evaluate (_, _, s0) = _` hd evaluate_changed_globals \\ simp [] \\ strip_tac
      \\ patresolve  `known _ _ _ g0 = _` hd known_preserves_esgc_free
      \\ simp [] \\ strip_tac
      \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
      \\ simp [co_disjoint_globals_shift_seq] \\ strip_tac
      \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
      \\ imp_res_tac decide_inline_LetInline_IMP_Clos_fv_max
      \\ rveq \\ fs [] \\ rveq \\ fs []
      \\ rename1 `evaluate (xs,_,s0) = (Rval vs, s1)`
      \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
      \\ `vs <> []` by simp [NOT_NIL_EQ_LENGTH_NOT_0]
      \\ fs [evaluate_app_rw]
      \\ fs [dest_closure_def, check_loc_def]
      \\ fs [case_eq_thms] \\ rveq \\ fs []      
      \\ fs [bool_case_eq] \\ rveq \\ fs []
      \\ fs [pair_case_eq]
      \\ patresolve  `known _ _ _ g1 = _` hd known_preserves_esgc_free
      \\ simp [] \\ strip_tac
      \\ rename1 `known _ [body]  _ g = (_, gdead)`
      \\ `unique_set_globals [body] s2.compile_oracle`
           by (match_mp_tac unique_set_globals_evaluate
               \\ goal_assum (first_assum o mp_then (Pos (el 2)) mp_tac)
               \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION])
      \\ `g = gdead` by (match_mp_tac known_unchanged_globals \\ goal_assum drule \\ simp [])
      \\ fs [TAKE_LENGTH_ID_rwt]
      \\ fs [DROP_NIL |> SPEC_ALL |> EQ_IMP_RULE |> snd]
      \\ rename1 `evaluate (_,_, dec_clock _ _) = (rr, ss)`
      \\ `rr = res /\ ss = s` by (fs [case_eq_thms] \\ rveq \\ fs []) \\ rveq
      \\ imp_res_tac set_globals_empty_esgc_free \\ simp []
      \\ first_x_assum match_mp_tac
      \\ goal_assum drule \\ simp []
      \\ simp [dec_clock_def]
      \\ patresolve `evaluate (_, _, s1) = _` hd evaluate_changed_globals
      \\ simp [] \\ strip_tac
      \\ simp [co_disjoint_globals_shift_seq]
      \\ rpt (disch_then drule))
    THEN
     (rveq \\ fs [evaluate_def, bool_case_eq, pair_case_eq]
      \\ imp_res_tac unique_set_globals_subexps
      \\ `subspt g0 g1 /\ subspt g1 g`
         by (match_mp_tac subspt_known_elist_globals
             \\ rpt (goal_assum drule)
             \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
      \\ `subspt g1 g'` by metis_tac [subspt_trans]
      \\ first_x_assum drule \\ rpt (disch_then drule) \\ strip_tac
      \\ fs [result_case_eq] \\ rveq \\ fs []
      \\ fs [pair_case_eq]
      \\ rename1 `evaluate (xs, _, s0) = (Rval args, s1)`
      \\ rename1 `evaluate ([x1], _, s1) = (_, s2)`
      \\ `unique_set_globals [x1] s1.compile_oracle`
         by metis_tac [unique_set_globals_evaluate]
      \\ drule co_disjoint_globals_evaluate \\ disch_then drule \\ strip_tac
      \\ patresolve `known _ _ _ g0 = _` (el 1) known_preserves_esgc_free
      \\ simp [] \\ strip_tac
      \\ `ssgc_free s1 /\ EVERY vsgc_free args`
         by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
             \\ rpt (disch_then drule \\ simp []))
      \\ first_x_assum drule \\ rpt (disch_then drule) \\ strip_tac
      \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq \\ fs []
      \\ reverse conj_tac
      THEN1 (Cases_on `res` \\ imp_res_tac evaluate_app_IMP_LENGTH
             \\ fs [LENGTH_EQ_NUM_compute])
      \\ imp_res_tac evaluate_SING \\ fs [] \\ rveq \\ fs [] \\ rveq
      \\ rename1 `evaluate ([_], _, _) = (Rval [fval], _)`
      \\ patresolve `known _ _ _ g1 = _` (el 1) known_preserves_esgc_free
      \\ simp [] \\ strip_tac
      \\ `ssgc_free s2 /\ vsgc_free fval`
         by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
             \\ rpt (disch_then drule \\ simp []))
      \\ drule evaluate_app_changed_globals \\ simp [] \\ strip_tac
      \\ drule co_disjoint_globals_evaluate \\ disch_then drule \\ strip_tac
      \\ qmatch_asmsub_abbrev_tac `mglobals_extend _ gd _`
      \\ `DISJOINT (domain g') gd` by metis_tac [co_disjoint_globals_first_n_exps]
      \\ metis_tac [mglobals_extend_DISJOINT_state_globals_approx]))
  THEN1
   (say "Fn"
    \\ rpt (pairarg_tac \\ fs [])
    \\ fs [evaluate_def, bool_case_eq] \\ rveq
    \\ Cases_on `loc_opt`
    \\ fs [case_eq_thms] \\ rveq
    \\ fs [clos_approx_def]
    \\ CASE_TAC \\ simp [])
  THEN1
   (say "Letrec"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ imp_res_tac unique_set_globals_subexps
    \\ fs [evaluate_def, bool_case_eq]
    \\ fs [Once option_case_eq] \\ rveq \\ fs []
    \\ rename1 `_ = SOME fvs`
    \\ `LENGTH fvs = LENGTH fns` by (fs [case_eq_thms] \\ rveq \\ fs [LENGTH_GENLIST])
    \\ `EVERY vsgc_free fvs` by (fs [case_eq_thms] \\ rveq \\ simp [EVERY_GENLIST]
                                 \\ rw [] \\ match_mp_tac EVERY_lookup_vars
                                 \\ goal_assum (qpat_x_assum `lookup_vars _ _ = _` o mp_then Any mp_tac)
                                 \\ simp [])
    \\ fs [fv_max_rw]
    \\ first_x_assum drule \\ simp []
    \\ simp [clos_gen_noinline_eq, REPLICATE_GENLIST]
    \\ Cases_on `loc_opt` \\ fs []
    \\ disch_then match_mp_tac
    \\ simp [EVERY_GENLIST]
    \\ irule EVERY2_APPEND_suff \\ simp []
    \\ fs [case_eq_thms] \\ rveq \\ simp [LIST_REL_GENLIST]));

(* code relation *)

val exp_rel_def = Define `
  exp_rel c aenv g' e1 e2 <=>
    ?g0 g apx k.
      subspt g g' /\
      EVERY val_approx_sgc_free aenv /\
      globals_approx_sgc_free g0 /\
      known (c with inline_factor := k) [e1] aenv g0 = ([(e2, apx)], g)`;

val exp_rel_dec_inline_factor =
  Q.store_thm("exp_rel_dec_inline_factor[simp]",
  `exp_rel (dec_inline_factor c) aenv g e1 e2 <=> exp_rel c aenv g e1 e2`,
  simp [exp_rel_def, dec_inline_factor_def]);

(* value relation *)

val f_rel_def = Define `
  f_rel c aenv g (n1, e1) (n2, e2) <=>
     n1 = n2 /\ exp_rel c (REPLICATE n1 Other ++ aenv) g e1 e2`;

val v1_size_append = Q.store_thm("v1_size_append",
  `!xs ys. closSem$v1_size (xs ++ ys) = v1_size xs + v1_size ys`,
  Induct \\ fs [closSemTheory.v_size_def]);

val v_rel_def = tDefine "v_rel" `
  (v_rel c g (Number i) v <=> v = Number i) /\
  (v_rel c g (Word64 w) v <=> v = Word64 w) /\
  (v_rel c g (ByteVector ws) v <=> v = ByteVector ws) /\
  (v_rel c g (RefPtr n) v <=> v = RefPtr n) /\
  (v_rel c g (Block n xs) v <=>
     ?ys. v = Block n ys /\ LIST_REL (v_rel c g) xs ys) /\
  (v_rel c g (Closure loc_opt args1 env1 num_args e1) v <=>
     every_Fn_vs_NONE [e1] /\
     ?aenv env1a env1b args2 env2a env2b e2.
       if env1 = env1a ++ env1b then
       fv_max (num_args + LENGTH env1a) [e1] /\
       LIST_REL (v_rel c g) args1 args2 /\
       LIST_REL (v_rel c g) env1a env2a /\
       LIST_REL val_approx_val aenv env1a /\
       exp_rel c (REPLICATE num_args Other ++ aenv) g e1 e2 /\
       v = Closure loc_opt args2 (env2a ++ env2b) num_args e2 else F) /\
  (v_rel c g (Recclosure loc_opt args1 env1 funs1 i) v <=>
     EVERY (\(n, e). every_Fn_vs_NONE [e]) funs1 /\
     let clos = case loc_opt of
                  | NONE => REPLICATE (LENGTH funs1) Other
                  | SOME loc => clos_gen_noinline loc 0 funs1
     in ?args2 env2 funs2 aenv.
       LIST_REL (v_rel c g) args1 args2 /\
       LIST_REL (v_rel c g) env1 env2 /\
       LIST_REL val_approx_val aenv env1 /\
       LIST_REL (f_rel c (clos ++ aenv) g) funs1 funs2 /\
       v = Recclosure loc_opt args2 env2 funs2 i)
  `
  (WF_REL_TAC `measure (v_size o FST o SND o SND)` \\ simp [v1_size_append, v_size_def]
   \\ rpt strip_tac \\ imp_res_tac v_size_lemma \\ simp []);

val v_rel_def = save_thm("v_rel_def[simp]",
 v_rel_def |> SIMP_RULE std_ss [] |> CONV_RULE (DEPTH_CONV ETA_CONV));

(* todo try ETA_ss) *)

val v_rel_ind = theorem "v_rel_ind";

val v_rel_app_def = Define `
  (v_rel_app c g (Number i) v args1 <=> v_rel c g (Number i) v) /\
  (v_rel_app c g (Word64 w) v args1 <=> v_rel c g (Word64 w) v) /\
  (v_rel_app c g (ByteVector ws) v args1 <=> v_rel c g (ByteVector ws) v) /\
  (v_rel_app c g (RefPtr n) v args1 <=> v_rel c g (RefPtr n) v) /\
  (v_rel_app c g (Block n xs) v args1 <=> v_rel c g (Block n xs) v) /\
  (v_rel_app c g (Closure loc_opt pargs1 env1 num_args e1) v args1 <=>
     every_Fn_vs_NONE [e1] /\
     ?aenv env1a env1b pargs2 env2a env2b e2 aargs.
       env1 = env1a ++ env1b /\
       fv_max (num_args + LENGTH env1a) [e1] /\
       LIST_REL (v_rel c g) pargs1 pargs2 /\
       LIST_REL (v_rel c g) env1a env2a /\
       LIST_REL val_approx_val aenv env1a /\
       (case args1 of
         | NONE => aargs = REPLICATE num_args Other
	 | SOME args1' => LIST_REL val_approx_val aargs args1' /\
                          pargs1 = []) /\
       exp_rel c (aargs ++ aenv) g e1 e2 /\
       v = Closure loc_opt pargs2 (env2a ++ env2b) num_args e2) /\
  (v_rel_app c g (Recclosure loc_opt pargs1 env1 funs1 i) v args1 <=>
     v_rel c g (Recclosure loc_opt pargs1 env1 funs1 i) v)`;

val v_rel_app_NONE = Q.store_thm(
  "v_rel_app_NONE",
  `v_rel_app c g v1 v2 NONE = v_rel c g v1 v2`,
  Cases_on `v1` \\ simp [v_rel_app_def] \\ metis_tac []);

val exp_rel_upd_inline_factor = Q.store_thm(
  "exp_rel_upd_inline_factor",
  `exp_rel (c with inline_factor := k) = exp_rel c`,
  simp [FUN_EQ_THM, exp_rel_def]);

val f_rel_upd_inline_factor = Q.store_thm(
  "f_rel_upd_inline_factor",
  `f_rel (c with inline_factor := k) = f_rel c`,
  simp [FUN_EQ_THM, FORALL_PROD, f_rel_def, exp_rel_upd_inline_factor]);

val v_rel_upd_inline_factor = Q.store_thm(
  "v_rel_upd_inline_factor",
  `!c. v_rel (c with inline_factor := k) = v_rel c`,
  simp [FUN_EQ_THM]
  \\ ho_match_mp_tac v_rel_ind \\ rw []
  THEN1 (fs [LIST_REL_EL_EQN] \\ rw [] \\ metis_tac [MEM_EL])  
  THEN1 (simp [exp_rel_upd_inline_factor]
         \\ eq_tac \\ rw [] \\ qexists_tac `aenv`
         \\ `env1a ++ env1b = env1a ++ env1b` by simp []
         \\ asm_exists_tac \\ fs []
         \\ `env2a ++ env2b = env2a ++ env2b` by simp []
         \\ goal_assum (pop_assum o mp_then Any mp_tac)
         \\ fs [LIST_REL_EL_EQN] \\ rw [] \\ metis_tac [MEM_EL])
  THEN1 (simp [f_rel_upd_inline_factor]
         \\ eq_tac \\ rw [] \\ qexists_tac `aenv`
         \\ fs [LIST_REL_EL_EQN] \\ rw [] \\ metis_tac [MEM_EL]));

(*
val v_rel_vsgc_free = Q.store_thm(
  "v_rel_vsgc_free",
  `!c g v1 v2. v_rel c g v1 v2 ==> (vsgc_free v1 ==> vsgc_free v2)`, cheat);
  ho_match_mp_tac v_rel_ind \\ simp [] \\ rpt strip_tac
  THEN1 (fs [EVERY_MEM, LIST_REL_EL_EQN] \\ metis_tac [MEM_EL])
  THEN1 (fs [EVERY_MEM, LIST_REL_EL_EQN]
         \\ fs [exp_rel_def]
         \\ drule known_elglobals_dont_grow
         \\ simp [set_globals_empty_esgc_free]
         \\ last_x_assum (qspec_then `env1a` assume_tac)
         \\ last_x_assum (qspec_then `env1a` assume_tac) \\ fs []
         \\ fs [MEM_EL, PULL_EXISTS] \\ rfs []
         \\ rpt strip_tac \\ TRY (metis_tac [])
         cheat)
  THEN1 (fs [EVERY_MEM, LIST_REL_EL_EQN]
         \\ fs [elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS, FORALL_PROD]
         \\ rpt strip_tac
         THEN1 (imp_res_tac (MEM_EL |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GSYM)
                \\ rename1 `nn < LENGTH funs2`
                \\ Cases_on `EL nn funs1` \\ fs []
                \\ first_x_assum (qspec_then `nn` mp_tac) \\ simp []
                \\ simp [f_rel_def, exp_rel_def] \\ strip_tac
                \\ drule known_elglobals_dont_grow \\ simp []
                \\ rename1 `known _ [ee] _ _`
                \\ `set_globals ee = {||}` by metis_tac [MEM_EL]
                \\ simp [set_globals_empty_esgc_free])
         \\ metis_tac [MEM_EL]));


 val v_rel_EVERY_vsgc_free = Q.store_thm(
  "v_rel_EVERY_vsgc_free",
  `!vs1 vs2.
     LIST_REL (v_rel c g) vs1 vs2 ==>
     (EVERY vsgc_free vs1 ==> EVERY vsgc_free vs2)`,
  Induct_on `LIST_REL` >> simp[] >> metis_tac [v_rel_vsgc_free]); *)

val v_rel_Block = Q.store_thm(
  "v_rel_Block[simp]",
  `v_rel c g x (Block n ys) <=>
     ?xs. x = Block n xs /\ LIST_REL (v_rel c g) xs ys`,
  Cases_on `x` \\ fs [v_rel_def] \\ eq_tac \\ rw [] \\ metis_tac []);

val v_rel_Boolv = Q.store_thm(
  "v_rel_Boolv[simp]",
  `(v_rel c g (Boolv b) v ⇔ v = Boolv b) ∧
   (v_rel c g v (Boolv b) ⇔ v = Boolv b)`,
  simp [closSemTheory.Boolv_def] >> Cases_on `v` >> simp[] >> metis_tac[]);

val v_rel_Unit = Q.store_thm(
  "v_rel_Unit[simp]",
  `(v_rel c g Unit v ⇔ v = Unit) ∧ (v_rel c g v Unit ⇔ v = Unit)`,
  simp[Unit_def] >> Cases_on `v` >> simp[] >> metis_tac[])

val v_rel_IMP_v_to_bytes_lemma = prove(
  ``!x y c g.
      v_rel c g x y ==>
      !ns. (v_to_list x = SOME (MAP (Number o $& o (w2n:word8->num)) ns)) <=>
           (v_to_list y = SOME (MAP (Number o $& o (w2n:word8->num)) ns))``,
  ho_match_mp_tac v_to_list_ind \\ rw []
  \\ fs [v_to_list_def]
  \\ Cases_on `tag = cons_tag` \\ fs []
  \\ res_tac \\ fs [case_eq_thms]
  \\ Cases_on `ns` \\ fs []
  \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `h` \\ fs []);

val v_rel_IMP_v_to_bytes = prove(
  ``v_rel c g x y ==> v_to_bytes y = v_to_bytes x``,
  rw [v_to_bytes_def] \\ drule v_rel_IMP_v_to_bytes_lemma \\ fs []);

val v_rel_IMP_v_to_words_lemma = prove(
  ``!x y c g.
      v_rel c g x y ==>
      !ns. (v_to_list x = SOME (MAP Word64 ns)) <=>
           (v_to_list y = SOME (MAP Word64 ns))``,
  ho_match_mp_tac v_to_list_ind \\ rw []
  \\ fs [v_to_list_def]
  \\ Cases_on `tag = cons_tag` \\ fs []
  \\ res_tac \\ fs [case_eq_thms]
  \\ Cases_on `ns` \\ fs []
  \\ eq_tac \\ rw [] \\ fs []
  \\ Cases_on `h` \\ fs []);

val v_rel_IMP_v_to_words = prove(
  ``v_rel c g x y ==> v_to_words y = v_to_words x``,
  rw [v_to_words_def] \\ drule v_rel_IMP_v_to_words_lemma \\ fs []);

(* state relation *)

val (ref_rel_rules, ref_rel_ind, ref_rel_cases) = Hol_reln `
  (!b bs. ref_rel c g (ByteArray b bs) (ByteArray b bs)) /\
  (!xs ys.
    LIST_REL (v_rel c g) xs ys ==>
    ref_rel c g (ValueArray xs) (ValueArray ys))`;

val ref_rel_simps = save_thm("ref_rel_simps[simp]",LIST_CONJ [
  SIMP_CONV (srw_ss()) [ref_rel_cases] ``ref_rel c g (ValueArray vs) x``,
  SIMP_CONV (srw_ss()) [ref_rel_cases] ``ref_rel c g (ByteArray b bs) x``])

val ref_rel_upd_inline_factor = Q.store_thm(
  "ref_rel_upd_inline_factor",
  `ref_rel (c with inline_factor := k) = ref_rel c`,
  simp [FUN_EQ_THM, ref_rel_cases, v_rel_upd_inline_factor]);

val compile_inc_def = Define `
  compile_inc c g (e,xs) =
    let (ea, g') = known (reset_inline_factor c) [e] [] g in (g', FST (HD ea), xs)`;

val oracle_states_subspt_def = Define `
  oracle_states_subspt co <=> !(n:num) k. subspt (FST (FST (co n))) (FST (FST (co (n + k))))
`;

val oracle_states_subspt_alt = Q.store_thm("oracle_states_subspt_alt",
  `!co n k. oracle_states_subspt co /\ n <= k ==>
     subspt (FST (FST (co n))) (FST (FST (co k)))`,
  rw [oracle_states_subspt_def]
  \\ imp_res_tac LESS_EQ_ADD_EXISTS \\ rveq \\ simp []);

val state_rel_def = Define `
  state_rel c g (s:(val_approx num_map#'c,'ffi) closSem$state) (t:('c,'ffi) closSem$state) <=>
    (!n. SND (SND (s.compile_oracle n)) = []) /\
    s.code = FEMPTY /\ t.code = FEMPTY /\
    s.clock = t.clock /\ s.ffi = t.ffi /\ s.max_app = t.max_app /\
    LIST_REL (OPTREL (v_rel c g)) s.globals t.globals /\
    fmap_rel (ref_rel c g) s.refs t.refs /\
    s.compile = state_cc (compile_inc c) t.compile  /\
    t.compile_oracle = state_co (compile_inc c) s.compile_oracle
`;

val state_rel_upd_inline_factor = Q.store_thm(
  "state_rel_upd_inline_factor",
  `state_rel (c with inline_factor := k) = state_rel c`,
  simp [FUN_EQ_THM] \\ rw []
  \\ eq_tac \\ strip_tac \\ fs [state_rel_def]
  \\ fs [v_rel_upd_inline_factor, ref_rel_upd_inline_factor]
  \\ simp [state_cc_def, state_co_def, LAMBDA_PROD,
           compile_inc_def, reset_inline_factor_def])

val v_rel_subspt = Q.store_thm(
  "v_rel_subspt",
  `!c g v1 v2 g'. v_rel c g v1 v2 ∧ subspt g g' ⇒ v_rel c g' v1 v2`,
  ho_match_mp_tac v_rel_ind >> simp[PULL_EXISTS] >> rpt strip_tac
  >- (irule EVERY2_MEM_MONO >> imp_res_tac LIST_REL_LENGTH >>
      simp[FORALL_PROD, MEM_ZIP, PULL_EXISTS] >> qexists_tac `v_rel c g` >>
      simp[] >> metis_tac[MEM_EL])
  >- (qexists_tac `aenv` >>
      qexists_tac `env1a` >> simp[] >>
      qexists_tac `env2a` >> simp[] >>
      rpt conj_tac >>
      TRY (irule EVERY2_MEM_MONO >> imp_res_tac LIST_REL_LENGTH >>
           simp[FORALL_PROD, MEM_ZIP, PULL_EXISTS] >>
           qexists_tac `v_rel c g` >> simp[] >> metis_tac[MEM_EL]) >>
      fs[exp_rel_def] >> metis_tac[subspt_trans])
  >- (qexists_tac `aenv` >>
      simp[] >> rpt conj_tac >>
      TRY (irule EVERY2_MEM_MONO >> imp_res_tac LIST_REL_LENGTH >>
           simp[FORALL_PROD, MEM_ZIP, PULL_EXISTS] >>
           qexists_tac `v_rel c g` >> simp[] >> metis_tac[MEM_EL]) >>
      qpat_x_assum `LIST_REL (f_rel _ _ _) _ _` mp_tac >> simp[LIST_REL_EL_EQN] >>
      rpt strip_tac >> fs[] >> rfs[] >> rpt (pairarg_tac >> fs[]) >>
      rename1 `nn < LENGTH _` >> first_x_assum (qspec_then `nn` mp_tac) >>
      rename1 `f_rel _ _ _ (EL nn fns1) (EL nn fns2)` >>
      Cases_on `EL nn fns1` >> Cases_on `EL nn fns2` >>
      simp[] >> simp[f_rel_def, exp_rel_def] >> metis_tac[subspt_trans]));

val v_rel_LIST_REL_subspt = Q.store_thm(
  "v_rel_LIST_REL_subspt",
  `∀vs1 vs2. LIST_REL (v_rel c g) vs1 vs2 ⇒
             ∀g'. subspt g g' ⇒ LIST_REL (v_rel c g') vs1 vs2`,
  Induct_on `LIST_REL` >> simp[] >> metis_tac[v_rel_subspt]);

val oracle_state_sgc_free_def = Define `
  oracle_state_sgc_free co = !n. globals_approx_sgc_free (FST (FST (co n)))`;

val oracle_state_sgc_free_shift_seq =
  Q.store_thm("oracle_state_sgc_free_shift_seq",
  `!co. oracle_state_sgc_free co ==> !n. oracle_state_sgc_free (shift_seq n co)`,
  rpt strip_tac \\ fs [oracle_state_sgc_free_def, shift_seq_def])

val evaluate_changed_globals_inst = INST_TYPE [``:'c`` |-> ``:val_approx num_map#'c``] evaluate_changed_globals

val co_every_Fn_vs_NONE_def = Define `
  co_every_Fn_vs_NONE co =
    !n exp aux. SND (co n) = (exp, aux) ==>
      every_Fn_vs_NONE [exp] /\
      every_Fn_vs_NONE (MAP (SND o SND) aux)
`;

val co_every_Fn_vs_NONE_shift_seq =
  Q.store_thm("co_every_Fn_vs_NONE_shift_seq",
  `!co. co_every_Fn_vs_NONE co ==> !n. co_every_Fn_vs_NONE (shift_seq n co)`,
  rpt strip_tac \\ fs [co_every_Fn_vs_NONE_def, shift_seq_def] \\ metis_tac [])

val state_rel_co_set_globals = Q.store_thm("state_rel_co_set_globals",
  `state_rel c g s t /\ ssgc_free s /\ oracle_state_sgc_free s.compile_oracle ==>
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
  `state_rel c g s t /\ ssgc_free s /\ oracle_state_sgc_free s.compile_oracle ==>
     elist_globals (first_n_exps t.compile_oracle n) <= elist_globals (first_n_exps s.compile_oracle n)`,
  strip_tac
  \\ imp_res_tac state_rel_co_set_globals
  \\ fs [first_n_exps_def] \\ Induct_on `n`
  \\ fs [GENLIST]
  \\ simp [SNOC_APPEND, elist_globals_append]
  \\ simp [SUB_BAG_UNION]);

val state_rel_unique_set_globals = Q.store_thm("state_rel_unique_set_globals",
  `!xs. state_rel c g s t /\ ssgc_free s /\ oracle_state_sgc_free s.compile_oracle /\
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
  `!g : val_approx num_map. state_rel c g0 s t /\ ssgc_free s /\ oracle_state_sgc_free s.compile_oracle /\
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
  `!c g s t n v1. state_rel c g s t /\ get_global n s.globals = SOME (SOME v1) ==>
   ?v2. get_global n t.globals = SOME (SOME v2) /\ v_rel c g v1 v2`,
  rw [state_rel_def, get_global_def, LIST_REL_EL_EQN]
  \\ metis_tac [OPTREL_SOME]);

val do_app_lemma = Q.prove(
  `!c g s t xs ys opp. state_rel c g s t /\ LIST_REL (v_rel c g) xs ys ==>
    case do_app opp xs s of
      | Rerr err1 => ?err2. do_app opp ys t = Rerr err2 /\
                            exc_rel (v_rel c g) err1 err2
      | Rval (x, s1) => ?y t1. v_rel c g x y /\ state_rel c g s1 t1 /\
                               do_app opp ys t = Rval (y, t1)`,
  rpt gen_tac
  \\ match_mp_tac simple_val_rel_do_app
  \\ conj_tac THEN1 (fs [simple_val_rel_def] \\ rw []
                     \\ rename1 `v_rel _ _ xx _`
                     \\ Cases_on `xx` \\ fs [v_rel_def]
                     \\ metis_tac [])
  \\ fs [simple_state_rel_def, state_rel_def]
  \\ rw [] \\ fs [fmap_rel_def, FLOOKUP_DEF]
  \\ rfs []
  \\ TRY (first_x_assum drule \\ fs [ref_rel_cases])
  \\ fs [FAPPLY_FUPDATE_THM]
  \\ rw [] \\ fs [ref_rel_cases]);

val next_oracle_state_def = Define `
  !co g. next_oracle_state co g <=> FST (FST (co 0n)) = g
`;

val next_g_def = Define `
  next_g (s:(val_approx num_map#'c,'ffi) closSem$state) = FST (FST (s.compile_oracle 0n))
`;

val oracle_states_subspt_shift_seq = Q.store_thm(
  "oracle_states_subspt_shift_seq",
  `oracle_states_subspt co ==> !k. oracle_states_subspt (shift_seq k co)`,
  rw [oracle_states_subspt_def, shift_seq_def]
  \\ rename1 `kk1 + (kk2 + nn)`
  \\ first_x_assum (qspecl_then [`kk1 + nn`, `kk2`] assume_tac)
  \\ fs []);


val evaluate_IMP_shift_seq = Q.store_thm(
  "evaluate__IMP_shift_seq",
  `!es env s0 res s.
     closSem$evaluate (es, env, s0) = (res, s) ==>
       ?k. s.compile_oracle = shift_seq k s0.compile_oracle`,
  metis_tac [evaluate_code]);

val do_install_IMP_shift_seq = Q.store_thm(
  "do_install_IMP_shift_seq",
  `do_install xs s0 = (res, s) ==>
     ?k. s.compile_oracle = shift_seq k s0.compile_oracle`,
   rpt strip_tac  \\ fs [do_install_def]
   \\ fs [case_eq_thms]
   \\ TRY (qexists_tac `0` \\ simp [] \\ NO_TAC)
   \\ pairarg_tac \\ fs []
   \\ fs [bool_case_eq, case_eq_thms, pair_case_eq]
   \\ TRY (qexists_tac `0` \\ simp [] \\ NO_TAC)
   \\ metis_tac []);

val evaluate_app_IMP_shift_seq = Q.store_thm(
  "evaluate_app_IMP_shift_seq",
  `evaluate_app lopt f args s0 = (res, s) ==>
     ?k. s.compile_oracle = shift_seq k s0.compile_oracle`,
  metis_tac [evaluate_app_code]);

val known_correct_approx_no_extra =
  known_correct_approx
  |> SPEC_ALL |> Q.INST [`extra` |-> `[]`] |> GEN_ALL
  |> SIMP_RULE (srw_ss ()) [] ;

val known_correct_approx_split_env =
  known_correct_approx
  |> SPEC_ALL
  |> Q.INST [`env` |-> `temp`]
  |> Q.INST [`extra` |-> `DROP env_len env`
            ,`temp`  |-> `TAKE env_len env`]
  |> GEN_ALL
  |> SIMP_RULE (srw_ss ()) [];

val evaluate_app_exact_rw = Q.store_thm(
  "evaluate_app_exact_rw",
  `args <> [] /\ num_args = LENGTH args
   ==>
   evaluate_app (SOME loc) (Closure (SOME loc) [] env num_args body) args s =
   if s.clock < LENGTH args then
     (Rerr (Rabort Rtimeout_error), s with clock := 0)
   else
     evaluate ([body], args ++ env, dec_clock num_args s)`,
  strip_tac
  \\ simp [evaluate_app_rw, dest_closure_def, check_loc_def]
  \\ fs [NOT_NIL_EQ_LENGTH_NOT_0]
  \\ IF_CASES_TAC \\ simp []
  \\ simp [TAKE_LENGTH_ID_rwt, LENGTH_REVERSE]
  \\ simp [DROP_LENGTH_TOO_LONG]
  \\ EVERY_CASE_TAC \\ simp []);

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

val dest_closure_SOME_IMP = store_thm("dest_closure_SOME_IMP",
  ``dest_closure max_app loc_opt f2 xs = SOME x ==>
    (?loc arg_env clo_env num_args e. f2 = Closure loc arg_env clo_env num_args e) \/
    (?loc arg_env clo_env fns i. f2 = Recclosure loc arg_env clo_env fns i)``,
  fs [dest_closure_def,case_eq_thms] \\ rw [] \\ fs []);

val set_globals_empty_unique_set_globals = Q.store_thm(
  "set_globals_empty_unique_set_globals",
  `set_globals e = {||} ==> (unique_set_globals [e] co <=> unique_set_globals [] co)`,
  simp [unique_set_globals_def]);

val nil_unique_set_globals = Q.store_thm("nil_unique_set_globals",
  `unique_set_globals es co ==> unique_set_globals [] co`,
  simp [unique_set_globals_def]
  \\ simp [elist_globals_append, BAG_ALL_DISTINCT_BAG_UNION]);


val say = say0 "known_correct0";

(*----------------temp-------------------*)
val known_correct0 = Q.prove(
  `(!xs env1full (s0:(val_approx num_map#'c,'ffi) closSem$state) res1 s env1 xenv1
     env2 xenv2 t0 c g0 g g' aenv eas.
      evaluate (xs, env1full, s0) = (res1, s) /\
      known c xs aenv g0 = (eas, g) /\
      state_rel c g' s0 t0 /\
      every_Fn_vs_NONE xs /\
      co_every_Fn_vs_NONE s0.compile_oracle /\
      EVERY esgc_free xs /\ ssgc_free s0 /\
      EVERY vsgc_free env1full /\
      oracle_states_subspt s0.compile_oracle /\
      LIST_REL val_approx_val aenv env1 /\
      oracle_state_sgc_free s0.compile_oracle /\
      globals_approx_sgc_free g0 /\
      state_globals_approx s0 g' /\
      EVERY val_approx_sgc_free aenv /\
      fv_max (LENGTH env1) xs /\
      LIST_REL (v_rel c g') env1 env2 /\
      subspt g0 g /\ subspt g (next_g s0) /\ subspt (next_g s) g' /\
      unique_set_globals xs s0.compile_oracle /\
      co_disjoint_globals g' s0.compile_oracle /\
      env1full = env1 ++ xenv1 /\
      res1 <> Rerr (Rabort Rtype_error) ==>
      ?res2 t.
        evaluate (MAP FST eas, env2 ++ xenv2, t0) = (res2, t) /\
        result_rel (LIST_REL (v_rel c g')) (v_rel c g') res1 res2 /\
        state_rel c g' s t) /\
   (!lopt1 f1 args1 (s0:(val_approx num_map#'c,'ffi) closSem$state) res1 s lopt2 f2 args2 t0 c g argsopt.
      evaluate_app lopt1 f1 args1 s0 = (res1, s) /\
      ssgc_free s0 /\ vsgc_free f1 /\ EVERY vsgc_free args1 /\
      subspt (next_g s) g /\
      oracle_state_sgc_free s0.compile_oracle /\
      co_every_Fn_vs_NONE s0.compile_oracle /\
      oracle_states_subspt s0.compile_oracle /\
      unique_set_globals [] s0.compile_oracle /\
      co_disjoint_globals g s0.compile_oracle /\
      v_rel_app c g f1 f2 argsopt /\
      LIST_REL (v_rel c g) args1 args2 /\
      state_rel c g s0 t0 /\ state_globals_approx s0 g /\
      loptrel f2 (LENGTH args1) lopt1 lopt2 /\
      (IS_SOME argsopt ==> argsopt = SOME args1 /\ args1 <> [] /\ ?exp env. dest_closure s0.max_app lopt1 f1 args1 = SOME (Full_app exp env [])) /\
      res1 <> Rerr (Rabort Rtype_error) ==>
      ?res2 t.
        evaluate_app lopt2 f2 args2 t0 = (res2, t) /\
        result_rel (LIST_REL (v_rel c g)) (v_rel c g) res1 res2 /\
        state_rel c g s t)`,

  ho_match_mp_tac (evaluate_ind |> Q.SPEC `\(x1,x2,x3). P0 x1 x2 x3`
                   |> Q.GEN `P0` |> SIMP_RULE std_ss [FORALL_PROD])
  \\ rpt strip_tac \\ fs [fv_max_rw] \\ rveq
  THEN1
   (say "NIL"
    \\ fs [known_def, evaluate_def] \\ rveq
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ simp [])
  THEN1 cheat (* CONS *)
  THEN1
   (say "Var"
    \\ fs [known_def] \\ rveq \\ fs []
    \\ fs [evaluate_def] \\ rveq
    \\ imp_res_tac LIST_REL_LENGTH
    \\ fs [LIST_REL_EL_EQN, EL_APPEND1])
  THEN1 cheat (* If *)
  THEN1
   (say "Let"
    \\ fs [known_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ rename1 `known _ xs _ g0 = (_, g1)`
    \\ fs [evaluate_def, pair_case_eq]
    \\ rename1 `Let tr _ _`
    \\ rename1 `evaluate (xs, _, s0) = (_, s1)`
    \\ imp_res_tac unique_set_globals_subexps \\ fs []
    \\ patresolve `subspt g0 g` (el 3) subspt_known_elist_globals
    \\ rpt (disch_then drule)
    \\ impl_tac THEN1 (imp_res_tac unique_set_globals_IMP_es_distinct_elist_globals
                       \\ fs [BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
    \\ strip_tac
    \\ `subspt g1 (next_g s0)` by metis_tac [subspt_trans]
    \\ `subspt (next_g s0) (next_g s1) /\ subspt (next_g s1) (next_g s)`
       by (fs [result_case_eq] \\ rveq
           \\ imp_res_tac evaluate_IMP_shift_seq
           \\ fs [next_g_def, shift_seq_def, oracle_states_subspt_alt])
    \\ `subspt (next_g s1) g'` by metis_tac [subspt_trans]
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ disch_then (qspec_then `xenv2` mp_tac)
    \\ fs [result_case_eq] \\ rveq \\ strip_tac \\ fs [] \\ rveq \\ simp [PULL_EXISTS]
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ patresolve `evaluate (xs, _, _) = _` hd evaluate_changed_globals_inst
    \\ simp [] \\ strip_tac \\ fs []
    \\ fs [co_disjoint_globals_shift_seq,
           unique_set_globals_shift_seq,
           co_every_Fn_vs_NONE_shift_seq,
           oracle_state_sgc_free_shift_seq,
           oracle_states_subspt_shift_seq]
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ patresolve `known _ xs _ _ = _` hd known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ patresolve `evaluate (xs, _, _) = _` (el 2) known_correct_approx
    \\ rpt (disch_then drule \\ simp [])
    \\ impl_tac THEN1 metis_tac [subspt_trans]
    \\ strip_tac \\ rveq \\ fs []
    \\ `subspt g (next_g s1)` by metis_tac [subspt_trans]
    \\ simp [] \\ disch_then match_mp_tac
    \\ qexists_tac `vs ++ env1`
    \\ qexists_tac `xenv1` \\ simp []
    \\ metis_tac [EVERY2_APPEND_suff])
  THEN1 cheat (* Raise *)
  THEN1 cheat (* Handle *)
  THEN1 cheat (* Op *)
  THEN1
   (say "Fn"
    \\ fs [known_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, bool_case_eq] \\ rveq
    \\ dsimp []
    \\ qexists_tac `aenv`
    \\ qexists_tac `env1` \\ qexists_tac `xenv1`
    \\ qexists_tac `env2` \\ qexists_tac `xenv2`
    \\ simp []
    \\ conj_tac
    THEN1 fs [state_rel_def]
    THEN1 (simp [exp_rel_def, EVERY_REPLICATE]
           \\ imp_res_tac known_sing_EQ_E \\ rveq \\ fs [] \\ rveq
           \\ qpat_x_assum `known _ _ _ _ = _`
                           (assume_tac o
                            ONCE_REWRITE_RULE [Q.prove (`c = c with inline_factor := c.inline_factor`,
                                                        simp [config_component_equality])])
           \\ goal_assum (pop_assum o mp_then Any mp_tac)
           \\ metis_tac [subspt_trans]))
  THEN1 cheat (* Letrec *)
  THEN1
   (say "App"
    \\ fs [known_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac unique_set_globals_subexps
    \\ imp_res_tac known_LENGTH_EQ_E
    \\ rename1 `known _ _ _ g0 = (_, g1)`
    \\ rename1 `known _ _ _ g1 = (_, g2)`
    \\ `g2 = g` by (fs [inlD_case_eq]
                    \\ rpt (pairarg_tac \\ fs [])
                    \\ fs [bool_case_eq])
    \\ rveq
    \\ patresolve `subspt g0 g` (el 3) subspt_known_elist_globals
    \\ rpt (disch_then drule)
    \\ impl_tac THEN1 (imp_res_tac unique_set_globals_IMP_es_distinct_elist_globals
                       \\ fs [BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
    \\ strip_tac
    \\ `subspt g1 (next_g s0)` by metis_tac [subspt_trans]
    \\ fs [evaluate_def]
    \\ Cases_on `LENGTH xs > 0` \\ fs []
    \\ fs [pair_case_eq]
    \\ rename1 `evaluate (_, _ s0) = (_, s1)`
    \\ `subspt (next_g s0) (next_g s1)`
       by (simp [next_g_def]
           \\ imp_res_tac evaluate_IMP_shift_seq
           \\ imp_res_tac oracle_states_subspt_shift_seq
           \\ fs [oracle_states_subspt_def, shift_seq_def]
           \\ first_x_assum (qspecl_then [`0`, `0`] assume_tac) \\ fs [])
    \\ `subspt (next_g s1) (next_g s)`
       by (simp [next_g_def]
           \\ fs [result_case_eq] \\ rveq \\ fs []
           \\ `?k. s.compile_oracle = shift_seq k s1.compile_oracle`
              by (reverse (fs [pair_case_eq, result_case_eq]) \\ rveq \\ fs []
                  THEN1 (metis_tac [evaluate_IMP_shift_seq])
                  \\ imp_res_tac evaluate_IMP_shift_seq
                  \\ imp_res_tac evaluate_app_IMP_shift_seq
                  \\ fs [] \\ metis_tac [ADD_SYM, ADD_ASSOC])
           \\ imp_res_tac evaluate_IMP_shift_seq \\ fs []
           \\ imp_res_tac oracle_states_subspt_shift_seq
           \\ fs [oracle_states_subspt_def, shift_seq_def])
    \\ `subspt (next_g s1) g'` by metis_tac [subspt_trans]
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ disch_then (qspec_then `xenv2` mp_tac)
    \\ impl_tac THEN1 fs [result_case_eq]  \\ strip_tac
    \\ patresolve `evaluate (_, _, s0) = _` hd evaluate_changed_globals_inst
    \\ simp [] \\ strip_tac \\ fs []
    \\ fs [co_every_Fn_vs_NONE_shift_seq,
           oracle_states_subspt_shift_seq,
           oracle_state_sgc_free_shift_seq,
           unique_set_globals_shift_seq]
    \\ patresolve `known _ _ _ g0 = _` hd known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ patresolve `evaluate (_, _, s0) = _` (el 2) known_correct_approx
    \\ rpt (disch_then drule \\ simp [])
    \\ impl_tac THEN1 metis_tac [subspt_trans]
    \\ strip_tac \\ rveq \\ fs []
    \\ reverse (fs [inlD_case_eq]) \\ rveq
    THEN1
     ((* inlD_LetInline *)
      imp_res_tac decide_inline_LetInline_IMP_Clos_fv_max \\ rveq
      \\ reverse (Cases_on `pure x1`) \\ fs []
      \\ rpt (pairarg_tac \\ fs []) \\ rveq
      \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
      THEN1
       ((* not pure *)
        simp [evaluate_def, evaluate_append]
        \\ fs [result_case_eq] \\ rveq \\ fs []
        \\ fs [pair_case_eq] \\ rveq \\ fs []
        \\ rename1 `evaluate (_, _ s1) = (_, s2)`
        \\ `subspt (next_g s2) (next_g s)`
           by (simp [next_g_def]
               \\ fs [result_case_eq]
               \\ imp_res_tac evaluate_app_IMP_shift_seq
               \\ imp_res_tac evaluate_IMP_shift_seq \\ fs []
               \\ imp_res_tac oracle_states_subspt_shift_seq
               \\ fs [oracle_states_subspt_def, shift_seq_def])
        \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
        \\ disch_then (qspec_then `xenv2` mp_tac)
        \\ simp [co_disjoint_globals_shift_seq]
        \\ impl_tac THEN1 (fs [result_case_eq] \\ metis_tac [subspt_trans])
        \\ strip_tac
        \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
        \\ patresolve `evaluate (_, _, s1) = _` hd evaluate_changed_globals
        \\ simp [] \\ strip_tac \\ fs []
        \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
        \\ patresolve `evaluate (_, _, s1) = _` (el 2) known_correct_approx
        \\ rpt (disch_then drule \\ simp [])
        \\ disch_then (qspec_then `g'` mp_tac)
        \\ simp [co_disjoint_globals_shift_seq,
                 unique_set_globals_shift_seq]
        \\ `subspt g g'` by metis_tac [subspt_trans]
        \\ simp [] \\ strip_tac \\ rveq
        \\ rename1 `known (dec_inline_factor _) [body] _ g = ([(ebody, abody)], gdead)`
        \\ qmatch_assum_abbrev_tac `v_rel _ _ lhclos _`
        \\ rename1 `evaluate (_, _, s0) = (Rval args, _)`
        \\ `v_rel_app c g' lhclos (Closure (SOME m) [] ([r1] ++ env2 ++ xenv2) (LENGTH xs) ebody) (SOME args)`
           by (fs [Abbr `lhclos`, v_rel_app_def]
               \\ qexists_tac `[]` \\ qexists_tac `[]` \\ simp []
               \\ asm_exists_tac \\ simp []
               \\ fs [exp_rel_def] \\ rveq
               \\ fs [dec_inline_factor_def]
               \\ simp [known_extra]
               \\ goal_assum (first_assum o mp_then (Pos last) mp_tac)
               \\ `g = gdead` by (match_mp_tac known_unchanged_globals
                                  \\ asm_exists_tac \\ simp [])
               \\ rveq \\ fs []
               \\ patresolve `known _ [_] _ g1 = _` hd known_preserves_esgc_free
               \\ simp [])
        \\ first_x_assum drule (* inst. evaluate_app i.h. *)
        \\ imp_res_tac nil_unique_set_globals
        \\ simp [oracle_state_sgc_free_shift_seq,
                 co_every_Fn_vs_NONE_shift_seq,
                 oracle_states_subspt_shift_seq,
                 unique_set_globals_shift_seq,
                 co_disjoint_globals_shift_seq]
        \\ rpt (disch_then drule \\ simp [])
        \\ disch_then (qspec_then `SOME m` mp_tac)
        \\ simp [loptrel_def]
        \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
        \\ impl_tac
        THEN1 (fs [decide_inline_def, bool_case_eq]
               \\ simp [NOT_NIL_EQ_LENGTH_NOT_0]
               \\ simp [Abbr `lhclos`, dest_closure_def]
               \\ simp [DROP_NIL]
               \\ simp [check_loc_def]
               \\ fs [dest_closure_def]
               \\ cheat (* LENGTH args <= s2.max_app *))
        \\ qmatch_goalsub_rename_tac `evaluate_app _ _ args2 t2`
        \\ `args2 <> []` by fs [NOT_NIL_EQ_LENGTH_NOT_0]
        \\ simp [evaluate_app_exact_rw]
        \\ strip_tac
        \\ `t2.clock = s2.clock` by fs [state_rel_def]
        \\ simp [evaluate_mk_Ticks_rw]
        \\ fs [bool_case_eq] \\ rveq \\ fs []
        \\ `args2 ⧺ [r1] ⧺ env2 ⧺ xenv2 = args2 ⧺ r1::(env2 ⧺ xenv2)` by simp [APPEND_ASSOC]
        \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND]
        \\ metis_tac [])
      THEN1
       ((* pure *)
        simp [evaluate_def, evaluate_append]
        \\ fs [result_case_eq] \\ rveq \\ fs []
        \\ fs [pair_case_eq] \\ rveq \\ fs []
        \\ rename1 `evaluate (_, _ s1) = (_, s2)`
        \\ `subspt (next_g s2) (next_g s)`
           by (simp [next_g_def]
               \\ fs [result_case_eq]
               \\ imp_res_tac evaluate_app_IMP_shift_seq
               \\ imp_res_tac evaluate_IMP_shift_seq \\ fs []
               \\ imp_res_tac oracle_states_subspt_shift_seq
               \\ fs [oracle_states_subspt_def, shift_seq_def])
        \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
        \\ disch_then (qspec_then `xenv2` mp_tac)
        \\ simp [co_disjoint_globals_shift_seq]
        \\ impl_tac THEN1 (fs [result_case_eq] \\ metis_tac [subspt_trans])
        \\ strip_tac
        \\ reverse (fs [result_case_eq]) \\ rveq \\ fs [] \\ rveq
        THEN1 (rename1 `evaluate ([x1], _, _) = (Rerr err_res, _)`
               \\ drule (pure_correct |> GEN_ALL |> INST_TYPE [``:'c`` |-> ``:val_approx num_map#'c``])
               \\ disch_then (qspecl_then [`s1`, `env1 ++ xenv1`] mp_tac)
               \\ simp [] \\ strip_tac \\ Cases_on `err_res` \\ fs [])
        \\ patresolve `evaluate (_, _, s1) = _` hd evaluate_changed_globals
        \\ simp [] \\ strip_tac \\ fs []
        \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
        \\ patresolve `evaluate (_, _, s1) = _` (el 2) known_correct_approx
        \\ rpt (disch_then drule \\ simp [])
        \\ disch_then (qspec_then `g'` mp_tac)
        \\ simp [co_disjoint_globals_shift_seq,
                 unique_set_globals_shift_seq]
        \\ `subspt g g'` by metis_tac [subspt_trans]
        \\ simp [] \\ strip_tac \\ rveq
        \\ rename1 `known (dec_inline_factor _) [body] _ g = ([(ebody, abody)], gdead)`
        \\ qmatch_assum_abbrev_tac `v_rel _ _ lhclos _`
        \\ rename1 `evaluate (_, _, s0) = (Rval args, _)`
        \\ `v_rel_app c g' lhclos (Closure (SOME m) [] (env2 ++ xenv2) (LENGTH xs) ebody) (SOME args)`
           by (fs [Abbr `lhclos`, v_rel_app_def]
               \\ qexists_tac `[]` \\ qexists_tac `[]` \\ simp []
               \\ asm_exists_tac \\ simp []
               \\ fs [exp_rel_def] \\ rveq
               \\ fs [dec_inline_factor_def]
               \\ simp [known_extra]
               \\ goal_assum (first_assum o mp_then (Pos last) mp_tac)
               \\ `g = gdead` by (match_mp_tac known_unchanged_globals
                                  \\ asm_exists_tac \\ simp [])
               \\ rveq \\ fs []
               \\ patresolve `known _ [_] _ g1 = _` hd known_preserves_esgc_free
               \\ simp [])
        \\ first_x_assum drule (* inst. evaluate_app i.h. *)
        \\ imp_res_tac nil_unique_set_globals
        \\ simp [oracle_state_sgc_free_shift_seq,
                 co_every_Fn_vs_NONE_shift_seq,
                 oracle_states_subspt_shift_seq,
                 unique_set_globals_shift_seq,
                 co_disjoint_globals_shift_seq]
        \\ rpt (disch_then drule \\ simp [])
        \\ disch_then (qspec_then `SOME m` mp_tac)
        \\ simp [loptrel_def]
        \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
        \\ impl_tac
        THEN1 (fs [decide_inline_def, bool_case_eq]
               \\ simp [NOT_NIL_EQ_LENGTH_NOT_0]
               \\ simp [Abbr `lhclos`, dest_closure_def]
               \\ simp [DROP_NIL]
               \\ simp [check_loc_def]
               \\ fs [dest_closure_def]
               \\ cheat (* LENGTH args <= s2.max_app *))
        \\ qmatch_goalsub_rename_tac `evaluate_app _ _ args2 t2`
        \\ `args2 <> []` by fs [NOT_NIL_EQ_LENGTH_NOT_0]
        \\ simp [evaluate_app_exact_rw]
        \\ strip_tac
        \\ `t2.clock = s2.clock` by fs [state_rel_def]
        \\ patresolve `known _ [x1] _ _ = ([e1, _], _)` hd known_preserves_pure
        \\ simp [] \\ strip_tac
        \\ drule (GEN_ALL pure_correct)
        \\ disch_then (qspecl_then [`t`, `env2 ++ xenv2`] mp_tac)
        \\ simp [] \\ strip_tac \\ rveq \\ fs []
        \\ simp [evaluate_mk_Ticks_rw]))
    THEN1
     ((* inlD_Annotate *)
      simp [evaluate_def]
      \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
      \\ fs [pair_case_eq]
      \\ rename1 `evaluate ([_], _ s1) = (_, s2)`
      \\ `subspt (next_g s2) (next_g s)`
          by (simp [next_g_def]
              \\ fs [result_case_eq]
              \\ imp_res_tac evaluate_app_IMP_shift_seq
              \\ imp_res_tac evaluate_IMP_shift_seq \\ fs []
              \\ imp_res_tac oracle_states_subspt_shift_seq
              \\ fs [oracle_states_subspt_def, shift_seq_def])
      \\ `subspt g (next_g s1) ∧ subspt (next_g s2) g'` by metis_tac [subspt_trans]
      \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
      \\ simp [co_disjoint_globals_shift_seq]
      \\ disch_then (qspec_then `xenv2` mp_tac)
      \\ imp_res_tac known_sing_EQ_E
      \\ fs [result_case_eq] \\ strip_tac \\ rveq \\ fs []
      \\ imp_res_tac evaluate_SING \\ fs [] \\ rveq
      \\ first_x_assum match_mp_tac
      \\ imp_res_tac nil_unique_set_globals
      \\ patresolve `evaluate (_, _, s1) = _` hd evaluate_changed_globals_inst
      \\ simp [] \\ strip_tac \\ fs []
      \\ simp [co_every_Fn_vs_NONE_shift_seq,
               oracle_states_subspt_shift_seq,
               oracle_state_sgc_free_shift_seq,
               co_disjoint_globals_shift_seq,
               unique_set_globals_shift_seq]
      \\ qexists_tac `NONE` \\ simp [v_rel_app_NONE]
      \\ patresolve `evaluate (_, _, s1) = _` (el 2) known_correct_approx
      \\ rpt (disch_then drule \\ simp [])
      \\ disch_then (qspec_then `g'` mp_tac)
      \\ simp [co_disjoint_globals_shift_seq,
               unique_set_globals_shift_seq]
      \\ impl_tac THEN1 metis_tac [subspt_trans]
      \\ strip_tac \\ simp []
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ simp [loptrel_def]
      \\ fs [decide_inline_def, va_case_eq, bool_case_eq]
      \\ rveq \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac LIST_REL_LENGTH \\ fs []
      \\ rename1 `FST (EL jj fns1) = FST (EL jj fns2)`
      \\ qpat_x_assum `LIST_REL (f_rel _ _ _) _ _` mp_tac
      \\ simp [LIST_REL_EL_EQN] \\ disch_then (qspec_then `jj` mp_tac)
      \\ Cases_on `EL jj fns1` \\ Cases_on `EL jj fns2`
      \\ simp [f_rel_def])
    THEN1
     ((* inlD_Nothing *)
      simp [evaluate_def]
      \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
      \\ fs [pair_case_eq]
      \\ rename1 `evaluate ([_], _ s1) = (_, s2)`
      \\ `subspt (next_g s2) (next_g s)`
          by (simp [next_g_def]
              \\ fs [result_case_eq]
              \\ imp_res_tac evaluate_app_IMP_shift_seq
              \\ imp_res_tac evaluate_IMP_shift_seq \\ fs []
              \\ imp_res_tac oracle_states_subspt_shift_seq
              \\ fs [oracle_states_subspt_def, shift_seq_def])
      \\ `subspt g (next_g s1) ∧ subspt (next_g s2) g'` by metis_tac [subspt_trans]
      \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
      \\ simp [co_disjoint_globals_shift_seq]
      \\ disch_then (qspec_then `xenv2` mp_tac)
      \\ imp_res_tac known_sing_EQ_E
      \\ fs [result_case_eq] \\ strip_tac \\ rveq \\ fs []
      \\ imp_res_tac evaluate_SING \\ fs [] \\ rveq
      \\ first_x_assum match_mp_tac
      \\ imp_res_tac nil_unique_set_globals
      \\ patresolve `evaluate (_, _, s1) = _` hd evaluate_changed_globals_inst
      \\ simp [] \\ strip_tac \\ fs []
      \\ simp [co_every_Fn_vs_NONE_shift_seq,
               oracle_states_subspt_shift_seq,
               oracle_state_sgc_free_shift_seq,
               co_disjoint_globals_shift_seq,
               unique_set_globals_shift_seq]
      \\ qexists_tac `NONE` \\ simp [v_rel_app_NONE]
      \\ patresolve `evaluate (_, _, s1) = _` (el 2) known_correct_approx
      \\ rpt (disch_then drule \\ simp [])
      \\ disch_then (qspec_then `g'` mp_tac)
      \\ simp [co_disjoint_globals_shift_seq,
               unique_set_globals_shift_seq]
      \\ impl_tac THEN1 metis_tac [subspt_trans]
      \\ simp [loptrel_def]))
  THEN1
   (say "Tick"
    \\ fs [known_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, pair_case_eq]
    \\ `t0.clock = s0.clock` by fs [state_rel_def]
    \\ Cases_on `s0.clock = 0` \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ first_x_assum drule \\ simp []
    \\ disch_then match_mp_tac
    \\ fs [dec_clock_def, state_rel_def, next_g_def]
    \\ asm_exists_tac \\ simp []
    \\ imp_res_tac unique_set_globals_subexps \\ simp [])
  THEN1
   (say "Call"
    \\ fs [known_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, pair_case_eq]
    \\ imp_res_tac unique_set_globals_subexps
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ disch_then (qspec_then `xenv2` mp_tac)
    \\ rename1 `evaluate (_, _ s0) = (_, s1)`
    \\ `subspt (next_g s1) (next_g s) /\ subspt (next_g s1) g'`
       by (reverse conj_asm1_tac THEN1 metis_tac [subspt_trans]
           \\ fs [case_eq_thms, pair_case_eq, bool_case_eq, next_g_def]
           \\ fixeqs \\ imp_res_tac evaluate_IMP_shift_seq
           \\ simp [shift_seq_def, dec_clock_def]
           \\ simp [oracle_states_subspt_alt])
    \\ fs [result_case_eq] \\ strip_tac \\ rveq \\ fs []
    \\ rename1 `evaluate (_, _ t0) = (_, t1)`
    \\ `s1.code = FEMPTY /\ t1.code = FEMPTY` by fs [state_rel_def]
    \\ fs [find_code_def])
  THEN1
   (say "evaluate_app NIL"
    \\ fs [evaluate_def, v_rel_app_NONE] \\ rveq \\ fs [])

  THEN1
   (say "evaluate_app CONS"

    \\ fs [evaluate_def]
    \\ fs [dec_clock_def, ADD1]
    \\ `t0.max_app = s0.max_app /\ s0.clock = t0.clock` by fs [state_rel_def]
    \\ fs [case_eq_thms] \\ fs [] \\ rveq
    THEN1 ((* dest_closure returns Partial_app *)
      imp_res_tac dest_closure_none_loc
      \\ drule dest_closure_SOME_IMP \\ strip_tac
      \\ fs [v_rel_app_def]
      \\ fs [dest_closure_def] \\ rveq
      \\ imp_res_tac LIST_REL_LENGTH
      \\ fs [METIS_PROVE [] ``(if b then SOME x else SOME y) = SOME (if b then x else y)``]
      THEN1
       (IF_CASES_TAC \\ fs []
        \\ IF_CASES_TAC \\ fs [] \\ rveq
        \\ fs [state_rel_def]
        \\ fs [loptrel_def, check_loc_def]
        \\ EVERY_CASE_TAC \\ fs []
        \\ qexists_tac `aenv`
        \\ qexists_tac `env1a` \\ simp []
        \\ qexists_tac `env2a` \\ simp [] 
        \\ irule EVERY2_APPEND_suff \\ simp [])
      THEN1 cheat (* Recclosure *))

    THEN1 ((* dest_closure returns Full_app *)    
      Cases_on `argsopt` \\ fs [] \\ rveq

      THEN1
       (drule dest_closure_SOME_IMP \\ strip_tac \\ rveq
        \\ fs [v_rel_app_def] \\ rveq \\ fs []
        \\ fs [dest_closure_def] \\ rveq
        \\ imp_res_tac LIST_REL_LENGTH
        \\ fs [METIS_PROVE [] ``(if b then SOME x else SOME y) = SOME (if b then x else y)``]

        THEN1
         (IF_CASES_TAC \\ fs [] \\ rveq
          \\ qpat_abbrev_tac `loc_is_ok = check_loc _ lopt2 _ _ _ _`
          \\ `loc_is_ok` by (fs [Abbr `loc_is_ok`, loptrel_def, check_loc_def]
                             \\ TRY (Cases_on `lopt2` \\ fs [])
                             \\ TRY (Cases_on `loc` \\ fs [] \\ rveq)
                             \\ fs [check_loc_def])
          \\ simp [Abbr `loc_is_ok`]
          \\ fs [bool_case_eq] \\ rveq \\ fs []
          THEN1 fs [state_rel_def]
          \\ fs [pair_case_eq]
          \\ rfs [SUB_SUB]
          \\ first_x_assum drule
          \\ fs [exp_rel_def]
          \\ rename1 `known _ _ _ g0 = (_, g1)`
          \\ `g0 = g1` by (match_mp_tac known_unchanged_globals
                           \\ asm_exists_tac \\ simp [])
          \\ disch_then drule
          \\ simp [v_rel_upd_inline_factor, state_rel_upd_inline_factor]
          \\ qmatch_asmsub_abbrev_tac `evaluate (_, fullenv1 ++ _, state1)`
          \\ qmatch_goalsub_abbrev_tac `evaluate (_, fullenv2 ++ extra2, state2)`
          \\ `LIST_REL (v_rel c g) fullenv1 fullenv2`
             by (simp [Abbr `fullenv1`, Abbr `fullenv2`]
                 \\ rpt (irule EVERY2_APPEND_suff \\ simp [])
                 \\ irule EVERY2_TAKE
                 \\ irule EVERY2_APPEND_suff \\ simp [])
          \\ disch_then (pop_assum o mp_then Any mp_tac) \\ simp []
          \\ `state_rel c g state1 state2`
             by (fs [Abbr `state1`, Abbr `state2`, state_rel_def])
          \\ disch_then drule
          \\ disch_then (qspec_then `extra2` mp_tac) \\ simp []
          \\ simp [set_globals_empty_esgc_free]
          \\ simp [EVERY_REVERSE, EVERY_TAKE]
          \\ simp [set_globals_empty_unique_set_globals]
          \\ rename1 `evaluate (_, _, state1) = (_, s1)`
          \\ rveq
          \\ `subspt (next_g state1) (next_g s1) /\ subspt (next_g s1) (next_g s)`
             by (fs [Abbr `state1`]
                 \\ simp [next_g_def]
                 \\ fs [result_case_eq] \\ rveq
                 \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
                 \\ imp_res_tac evaluate_app_IMP_shift_seq
                 \\ imp_res_tac evaluate_IMP_shift_seq \\ fs []
                 \\ imp_res_tac oracle_states_subspt_shift_seq
                 \\ simp [shift_seq_def, oracle_states_subspt_alt])
          \\ fs [Abbr `fullenv1`]
          \\ impl_tac
          THEN1
           (rpt conj_tac
            THEN1 (irule EVERY2_APPEND_suff \\ simp []
                   \\ simp [LIST_REL_EL_EQN, EL_REPLICATE])        
            THEN1 cheat (* subspt g0 (next_g s0) *)
            THEN1 metis_tac [subspt_trans] (* subspt (next_g s1) g *)
            THEN1 fs [result_case_eq])
          \\ strip_tac \\ fs []
          \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
          \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
          \\ reverse (Cases_on `lopt1 = lopt2`)
          THEN1
           (fs [loptrel_def]
            \\ Cases_on `lopt2` \\ fs []
            \\ Cases_on `loc` \\ fs [] \\ rveq \\ fs []
            \\ rename1 `evaluate_app lopt1 f1' _ _ = _`
            \\ qmatch_assum_abbrev_tac `evaluate_app lopt1 f1' next_args1 _ = _`
            \\ qmatch_goalsub_abbrev_tac `evaluate_app _ _ next_args2 _ = _`
            \\ `next_args1 = []` by fs [Abbr `next_args1`, DROP_NIL]
            \\ `next_args2 = []` by fs [Abbr `next_args2`, DROP_NIL]
            \\ fs [Abbr `next_args1`, Abbr `next_args2`]
            \\ rveq \\ simp [])
          \\ first_x_assum match_mp_tac
          \\ qexists_tac `NONE` \\ simp []
          \\ patresolve `evaluate (_, _, state1) = _` hd evaluate_changed_globals
          \\ patresolve `evaluate (_, _, state1) = _` (el 2) known_correct_approx
          \\ unabbrev_all_tac
          \\ rpt (disch_then drule \\ simp [])
          \\ disch_then (qspec_then `g` mp_tac)
          \\ simp [set_globals_empty_unique_set_globals]
          \\ simp [set_globals_empty_esgc_free]
          \\ simp [EVERY_REVERSE, EVERY_TAKE]
          \\ impl_tac THEN1 (irule EVERY2_APPEND_suff \\ simp []
                             \\ simp [LIST_REL_EL_EQN, EL_REPLICATE])
          \\ strip_tac \\ strip_tac
          \\ simp [EVERY_DROP, EVERY_REVERSE]
          \\ simp [oracle_state_sgc_free_shift_seq,
                   co_every_Fn_vs_NONE_shift_seq,
                   oracle_states_subspt_shift_seq,
                   co_disjoint_globals_shift_seq,
                   unique_set_globals_shift_seq]
          \\ simp [v_rel_app_NONE]
          \\ conj_tac THEN1 (irule EVERY2_DROP 
                             \\ irule EVERY2_APPEND_suff \\ simp [])
          \\ simp [loptrel_def])
        THEN1 cheat (* Recclosure *))

      THEN1 ((* ISSOME argsopt *)
        dsimp [] \\ disj2_tac
        \\ fs [bool_case_eq] \\ rveq \\ fs []
        THEN1
         ((* Rtimeout_error *)
          drule dest_closure_SOME_IMP \\ strip_tac \\ rveq
          \\ fs [v_rel_app_def] \\ rveq \\ fs []
          \\ fs [dest_closure_def] \\ rveq \\ fs []
          \\ imp_res_tac LIST_REL_LENGTH
          \\ TRY (rpt (pairarg_tac \\ fs [])
                  \\ rename1 `LIST_REL (f_rel _ _ _) funs1 funs2`
                  \\ rename1 `EL i funs1 = (num_args1, _)`
                  \\ rename1 `EL i funs2 = (num_args2, _)`
                  \\ `num_args1 = num_args2`
                     by (fs [NOT_LESS_EQUAL, LIST_REL_EL_EQN]
                         \\ first_x_assum (qpat_assum `i < _` o mp_then (Pos hd) mp_tac)
                         \\ simp [f_rel_def]))
          \\ fs [bool_case_eq] \\ rveq
          \\ qexists_tac `t0 with clock := 0`
          \\ fs [CONV_RULE (LHS_CONV SYM_CONV) REVERSE_EQ_NIL]
          \\ fs [DROP_NIL, NOT_LESS, ADD1, GREATER_EQ]
          \\ imp_res_tac LESS_EQUAL_ANTISYM \\ fs []
          \\ fs [state_rel_def]
          \\ Cases_on `lopt1 = lopt2`
          \\ fs [loptrel_def]
          \\ Cases_on `lopt2` \\ fs []
          \\ Cases_on `loc` \\ fs [] \\ rveq
          \\ fs [check_loc_def])
        \\ drule dest_closure_SOME_IMP \\ strip_tac \\ rveq
        \\ fs [v_rel_app_def] \\ rveq \\ fs []
        \\ fs [dest_closure_def] \\ rveq
        \\ imp_res_tac LIST_REL_LENGTH
        THEN1
         (IF_CASES_TAC \\ fs [] \\ rveq
          \\ qpat_abbrev_tac `loc_is_ok = check_loc _ lopt2 _ _ _ _`
          \\ `loc_is_ok` by (fs [Abbr `loc_is_ok`, loptrel_def, check_loc_def]
                             \\ TRY (Cases_on `lopt2` \\ fs [])
                             \\ TRY (Cases_on `loc` \\ fs [] \\ rveq)
                             \\ fs [check_loc_def])
          \\ simp [Abbr `loc_is_ok`]
          \\ fs [pair_case_eq]
          \\ first_x_assum drule
          \\ fs [exp_rel_def]
          \\ rename1 `known _ _ _ g0 = (_, g1)`
          \\ `g0 = g1` by (match_mp_tac known_unchanged_globals
                           \\ asm_exists_tac \\ simp [])
          \\ disch_then drule
          \\ simp [v_rel_upd_inline_factor, state_rel_upd_inline_factor]
          \\ qmatch_asmsub_abbrev_tac `evaluate (_, fullenv1 ++ _, state1)`
          \\ qmatch_goalsub_abbrev_tac `evaluate (_, fullenv2 ++ extra2, state2)`
          \\ `LIST_REL (v_rel c g) fullenv1 fullenv2`
             by (simp [Abbr `fullenv1`, Abbr `fullenv2`]
                 \\ rpt (irule EVERY2_APPEND_suff \\ simp [])
                 \\ irule EVERY2_TAKE
                 \\ irule EVERY2_APPEND_suff \\ simp [])
          \\ disch_then (pop_assum o mp_then Any mp_tac) \\ simp []
          \\ `num_args = LENGTH ys + 1` by fs [DROP_NIL]
          \\ `state_rel c g state1 state2`
             by (fs [Abbr `state1`, Abbr `state2`, state_rel_def, DROP_NIL])
          \\ disch_then drule \\ simp []
          \\ simp [set_globals_empty_esgc_free]
          \\ simp [EVERY_REVERSE, EVERY_TAKE]
          \\ simp [set_globals_empty_unique_set_globals]
          \\ fs [Abbr `fullenv1`]
          \\ simp [TAKE_LENGTH_ID_rwt]
          \\ disch_then (qspec_then `extra2` mp_tac)
          \\ impl_tac
          THEN1
           (rpt conj_tac
            THEN1 (simp [TAKE_LENGTH_ID_rwt]
                   \\ irule EVERY2_APPEND_suff \\ simp [])
            THEN1 cheat (* subspt g1 (next_g state1) *)
            THEN1 fs [result_case_eq, list_case_eq] (* subpst (next_g s1) g *)
            THEN1 fs [result_case_eq])
          \\ strip_tac
          \\ fs [result_case_eq] \\ rveq \\ fs []
          \\ imp_res_tac evaluate_SING \\ fs [] \\ rveq
          \\ simp [DROP_LENGTH_TOO_LONG])
        THEN1
         (rpt (pairarg_tac \\ fs [])
          \\ fs [bool_case_eq] \\ rveq
          \\ rename1 `LIST_REL (f_rel _ _ _) funs1 funs2`
          \\ rename1 `EL i funs1 = (num_args1, exp1)`
          \\ rename1 `EL i funs2 = (num_args2, exp2)`
          \\ `num_args1 = num_args2`
             by (fs [NOT_LESS_EQUAL, LIST_REL_EL_EQN]
                 \\ first_x_assum (qpat_assum `i < _` o mp_then (Pos hd) mp_tac)
                 \\ simp [f_rel_def])
          \\ qpat_abbrev_tac `loc_is_ok = check_loc _ lopt2 _ _ _ _`
          \\ `loc_is_ok`
             by (fs [Abbr `loc_is_ok`, loptrel_def]
                 \\ TRY (Cases_on `lopt2` \\ fs [])
                 \\ TRY (Cases_on `loc` \\ fs [] \\ rveq)
                 \\ fs [check_loc_def, DROP_NIL])
          \\ simp [Abbr `loc_is_ok`]
          \\ fs [pair_case_eq]
          \\ first_x_assum drule
          \\ qmatch_asmsub_abbrev_tac `f_rel _ aenvcase`
          \\ `f_rel c aenvcase g (EL i funs1) (EL i funs2)` by fs [LIST_REL_EL_EQN]
          \\ rfs [] \\ fs [f_rel_def, exp_rel_def]
          \\ rename1 `known _ _ _ g0 = (_, g1)`
          \\ `MEM (EL i funs1) funs1` by simp [EL_MEM]
          \\ pop_assum mp_tac \\ simp [] \\ strip_tac
          \\ `g0 = g1` by (match_mp_tac known_unchanged_globals
                           \\ asm_exists_tac \\ simp []
                           \\ fs [elglobals_EQ_EMPTY]
                           \\ first_x_assum irule
                           \\ simp [MEM_MAP]
                           \\ qexists_tac `EL i funs1` \\ simp [])
          \\ rveq
          \\ disch_then drule
          \\ simp [v_rel_upd_inline_factor, state_rel_upd_inline_factor]
          \\ qmatch_asmsub_abbrev_tac `evaluate (_, fullenv1, state1)`
          \\ qmatch_goalsub_abbrev_tac `evaluate (_, fullenv2, state2)`
          \\ `LIST_REL (v_rel c g) fullenv1 fullenv2`
             by (simp [Abbr `fullenv1`, Abbr `fullenv2`]
                 \\ rpt (irule EVERY2_APPEND_suff \\ simp [])
                 THEN1 (irule EVERY2_TAKE
                        \\ irule EVERY2_APPEND_suff \\ simp [])
                 \\ fs [LIST_REL_GENLIST] \\ rw []
                 \\ asm_exists_tac \\ simp [])
          \\ disch_then drule \\ simp []
          \\ `state_rel c g state1 state2`
             by (fs [Abbr `state1`, Abbr `state2`, state_rel_def]
                 \\ fs [CONV_RULE (LHS_CONV SYM_CONV) REVERSE_EQ_NIL, DROP_NIL])
          \\ disch_then drule \\ simp []
          \\ simp [EVERY_REVERSE, EVERY_TAKE, EVERY_GENLIST]
          \\ `set_globals exp1 = {||}`
             by (fs [elglobals_EQ_EMPTY]
                 \\ first_x_assum irule \\ simp [MEM_MAP]
                 \\ qexists_tac `EL i funs1` \\ simp [])
          \\ simp [set_globals_empty_esgc_free]
          \\ simp [set_globals_empty_unique_set_globals]
          \\ impl_tac
          THEN1
           (rpt conj_tac
            THEN1 (fs [EVERY_MEM, FORALL_PROD] \\ metis_tac [])
            THEN1 cheat
            THEN1 cheat
            THEN1 (simp [Abbr `fullenv1`, Abbr `aenvcase`]
                   \\ rpt (irule EVERY2_APPEND_suff \\ simp [])
                   THEN1 simp [LIST_REL_EL_EQN, EL_REPLICATE]
                   \\ Cases_on `loc` \\ simp []
                   THEN1 simp [LIST_REL_EL_EQN, EL_REPLICATE]
                   THEN1 simp [clos_gen_noinline_eq, LIST_REL_EL_EQN])
            THEN1 cheat
            THEN1 fs [result_case_eq])
          \\ strip_tac
          \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
          \\ imp_res_tac evaluate_SING \\ rveq \\ fs [] \\ rveq \\ fs []           
          \\ fs [CONV_RULE (LHS_CONV SYM_CONV) REVERSE_EQ_NIL, DROP_NIL]
          \\ simp [DROP_LENGTH_TOO_LONG]))))




(*----------------real-------------------*)
val known_correct0 = Q.prove(
  `(!xs env1 (s0:(val_approx num_map#'c,'ffi) closSem$state) res1 s env2 t0 c g0 g g' aenv eas env_len.
      evaluate (xs, env1, s0) = (res1, s) /\
      
      known c xs aenv g0 = (eas, g) /\
      state_rel c g' s0 t0 /\
      every_Fn_vs_NONE xs /\
      co_every_Fn_vs_NONE s0.compile_oracle /\
      EVERY esgc_free xs /\ ssgc_free s0 /\
      EVERY vsgc_free env1 /\
      oracle_states_subspt s0.compile_oracle /\
      subspt g0 g /\ subspt g (next_g s0) /\ subspt (next_g s) g' /\
      LIST_REL val_approx_val aenv (TAKE env_len env1) /\
      oracle_state_sgc_free s0.compile_oracle /\
      globals_approx_sgc_free g0 /\
      state_globals_approx s0 g' /\
      EVERY val_approx_sgc_free aenv /\
      fv_max env_len xs /\
      env_rel c g' env_len aenv env1 env2 /\
      unique_set_globals xs s0.compile_oracle /\
      co_disjoint_globals g' s0.compile_oracle /\
      res1 <> Rerr (Rabort Rtype_error) ==>
      ?res2 t.
        evaluate (MAP FST eas, env2, t0) = (res2, t) /\
        result_rel (LIST_REL (v_rel c g')) (v_rel c g') res1 res2 /\
        state_rel c g' s t) /\
   (!lopt1 f1 args1 (s0:(val_approx num_map#'c,'ffi) closSem$state) res1 s lopt2 f2 args2 t0 c g argsopt.
      evaluate_app lopt1 f1 args1 s0 = (res1, s) /\
      ssgc_free s0 /\ vsgc_free f1 /\ EVERY vsgc_free args1 /\
      subspt (next_g s) g /\
      oracle_state_sgc_free s0.compile_oracle /\
      co_every_Fn_vs_NONE s0.compile_oracle /\
      oracle_states_subspt s0.compile_oracle /\
      unique_set_globals [] s0.compile_oracle /\
      co_disjoint_globals g s0.compile_oracle /\
      v_rel_app c g f1 f2 argsopt /\
      LIST_REL (v_rel c g) args1 args2 /\
      state_rel c g s0 t0 /\ state_globals_approx s0 g /\
      loptrel f2 (LENGTH args1) lopt1 lopt2 /\
      (IS_SOME argsopt ==> argsopt = SOME args1 /\ args1 <> [] /\ ?exp env. dest_closure s0.max_app lopt1 f1 args1 = SOME (Full_app exp env [])) /\
      res1 <> Rerr (Rabort Rtype_error) ==>
      ?res2 t.
        evaluate_app lopt2 f2 args2 t0 = (res2, t) /\
        result_rel (LIST_REL (v_rel c g)) (v_rel c g) res1 res2 /\
        state_rel c g s t)`,

  ho_match_mp_tac (evaluate_ind |> Q.SPEC `\(x1,x2,x3). P0 x1 x2 x3`
                   |> Q.GEN `P0` |> SIMP_RULE std_ss [FORALL_PROD])
  \\ rpt strip_tac \\ fs [fv_max_rw]
  THEN1
   (say "NIL"
    \\ fs [known_def, evaluate_def] \\ rveq
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ simp [])
  THEN1 cheat
(*  THEN1
   (say "CONS"
    \\ fs [known_def, evaluate_def, pair_case_eq]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac unique_set_globals_subexps \\ fs []
    \\ patresolve `subspt g0 g` (el 3) subspt_known_elist_globals
    \\ rpt (disch_then drule)
    \\ impl_tac THEN1 (imp_res_tac unique_set_globals_IMP_es_distinct_elist_globals
                       \\ fs [BAG_ALL_DISTINCT_BAG_UNION])
    \\ strip_tac
    \\ rename1 `known _ [_] _ g0 = (_, g1)`
    \\ `subspt g1 (next_g s0)` by metis_tac [subspt_trans]
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ reverse (fs [result_case_eq]) \\ rveq \\ fs []
    THEN1 (strip_tac \\ simp [evaluate_append])
    \\ fs [pair_case_eq] \\ rveq \\ fs []
    \\ `subspt (next_g s0) (next_g s1) /\ subspt (next_g s1) (next_g s)`
       by (simp [next_g_def]
           \\ fs [result_case_eq] \\ rveq \\ fs []
           \\ imp_res_tac evaluate_IMP_shift_seq \\ fs []
           \\ imp_res_tac oracle_states_subspt_shift_seq
           \\ fs [oracle_states_subspt_def, shift_seq_def]
           \\ first_x_assum (qspecl_then [`0`, `0`] assume_tac) \\ fs [])
    \\ impl_tac THEN1 metis_tac [subspt_trans]
    \\ strip_tac \\ simp [evaluate_append]
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ patresolve `evaluate ([_], _, _) = _` hd evaluate_changed_globals_inst
    \\ simp [] \\ strip_tac \\ fs []
    \\ fs [co_disjoint_globals_shift_seq,
           unique_set_globals_shift_seq,
           co_every_Fn_vs_NONE_shift_seq,
           oracle_state_sgc_free_shift_seq]
    \\ patresolve `known _ [_] _ _ = _` hd known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ patresolve `evaluate ([_], _, _) = _` (el 2) known_correct_approx_no_extra
    \\ rpt (disch_then drule \\ simp [])
    \\ impl_tac THEN1 metis_tac [subspt_trans]
    \\ strip_tac \\ rveq \\ fs []
    \\ simp [oracle_states_subspt_shift_seq]
    \\ `subspt g (next_g s1)` by metis_tac [subspt_trans]
    \\ fs [result_case_eq] \\ rveq \\ fs []
    \\ strip_tac \\ simp []
    \\ imp_res_tac known_sing_EQ_E \\ rveq \\ fs [] \\ rveq \\ fs []) *)
  THEN1
   (say "Var"
    \\ fs [known_def] \\ rveq \\ fs []
    \\ fs [evaluate_def] \\ rveq
    \\ imp_res_tac LIST_REL_LENGTH
    \\ fs [env_rel_def, LIST_REL_EL_EQN] \\ rveq \\ fs []
    \\ rfs [EL_TAKE])
    (* fs [env_rel_def, Once fv1_def, fv_def] *)
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
    \\ fs [known_def, evaluate_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ rename1 `known _ _ _ g0 = (_, g1)`
    \\ imp_res_tac unique_set_globals_subexps \\ fs []
    \\ fs [pair_case_eq]
    \\ drule subspt_known_op_elist_globals
    \\ rpt (disch_then drule)
    \\ impl_tac THEN1 (imp_res_tac unique_set_globals_IMP_es_distinct_elist_globals
                       \\ fs [BAG_ALL_DISTINCT_BAG_UNION])
    \\ strip_tac
    \\ `subspt g1 (next_g s0)` by metis_tac [subspt_trans]
    \\ rename [`isGlobal opn`, `gO_destApx apx`]
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ reverse (fs [result_case_eq]) \\ rveq \\ fs []
    THEN1 (strip_tac \\ rveq \\ fs []
           \\ Cases_on `opn` \\ simp [isGlobal_def, evaluate_def]
           \\ Cases_on `apx` \\ simp [gO_destApx_def] \\ rveq
           \\ fs [known_op_def, NULL_EQ, bool_case_eq] \\ rveq
           \\ fs [evaluate_def])
    \\ rename1 `evaluate (_, _, s0) = (_, s1)`
    \\ `subspt (next_g s0) (next_g s1) /\ subspt (next_g s1) (next_g s)`
       by (simp [next_g_def]
           \\ fs [result_case_eq] \\ rveq \\ fs []
           \\ `?k. s.compile_oracle = shift_seq k s1.compile_oracle`
              by (reverse (Cases_on `opn = Install`) \\ fs []
                  THEN1 (qexists_tac `0`
                         \\ fs [case_eq_thms, pair_case_eq] \\ rveq \\ fs []
                         \\ imp_res_tac do_app_const \\ fs [])
                  \\ reverse (fs [pair_case_eq, result_case_eq]) \\ rveq \\ fs []
                  THEN1 (metis_tac [do_install_IMP_shift_seq])
                  \\ imp_res_tac do_install_IMP_shift_seq
                  \\ patresolve `evaluate ([_], _, _) = _` hd evaluate_IMP_shift_seq \\ strip_tac
                  \\ fs [] \\ metis_tac [])
           \\ imp_res_tac evaluate_IMP_shift_seq \\ fs []
           \\ imp_res_tac oracle_states_subspt_shift_seq
           \\ fs [oracle_states_subspt_def, shift_seq_def]
           \\ first_x_assum (qspecl_then [`0`, `0`] assume_tac) \\ fs [])
    \\ impl_tac THEN1 metis_tac [subspt_trans]
    \\ strip_tac
    \\ Cases_on `opn = Install` \\ fs []
    THEN1
     (drule EVERY2_REVERSE \\ strip_tac
      \\ rename1 `evaluate (_, _, s0) = (Rval vs1, _)`
      \\ rename1 `LIST_REL _ vs1 vs2`
      \\ qabbrev_tac `rvs1 = REVERSE vs1`
      \\ qabbrev_tac `rvs2 = REVERSE vs2`
      \\ fs [do_install_def, pair_case_eq]
      \\ fs [list_case_eq, option_case_eq]
      \\ rveq \\ fs [] \\ rveq \\ fs []
      \\ rename1 `[x1;x2] = REVERSE vs1`
      \\ patresolve `v_rel _ _ x1 _` hd v_rel_IMP_v_to_bytes \\ strip_tac
      \\ patresolve `v_rel _ _ x2 _` hd v_rel_IMP_v_to_words \\ strip_tac
      \\ pairarg_tac \\ fs []
      \\ fs [bool_case_eq, option_case_eq] \\ rveq \\ fs []
      \\ fs [pair_case_eq, Once bool_case_eq] \\ rveq \\ fs []
      \\ rename1 `s1.compile_oracle 0 = (_, exp1, aux1)`
      \\ Cases_on `t.compile_oracle 0` \\ PairCases_on `r`
      \\ `r1 = [] /\ aux1 = []` by
         (fs [state_rel_def] \\ rfs [state_co_def]
          \\ rpt (pairarg_tac \\ fs []) \\ rveq
          \\ fs [compile_inc_def]
          \\ pairarg_tac \\ fs [] \\ rveq \\ metis_tac [SND])
      \\ simp [isGlobal_def, evaluate_def, do_install_def]
      \\ Cases_on `t.compile q (r0, [])`
      THEN1 (fs [state_rel_def, state_cc_def, state_co_def]
             \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ rfs []
             \\ fs [compile_inc_def])
      \\ rename1 `_ = SOME xx` \\ PairCases_on `xx` \\ fs []
      \\ reverse IF_CASES_TAC
      THEN1 (pop_assum mp_tac \\ fs []
             \\ fs [state_rel_def] \\ rfs []
             \\ fs [state_cc_def]
             \\ fs [shift_seq_def, state_co_def, state_cc_def]
             \\ rpt (pairarg_tac \\ fs []) \\ rveq
             \\ fs [compile_inc_def, shift_seq_def]
             \\ rpt (pairarg_tac \\ fs []) \\ rveq)
      \\ fs [] \\ rveq
      \\ `t.clock = s1.clock` by fs [state_rel_def]
      \\ fs []
      \\ Cases_on `s1.clock = 0` \\ fs []
      THEN1 (fs [result_case_eq] \\ rveq \\ fs []
             \\ fs [state_rel_def]
             \\ simp [shift_seq_def, FUPDATE_LIST]
             \\ simp [FUN_EQ_THM, state_co_def])
      \\ rveq \\ fs []
      \\ `?apx gg. known (reset_inline_factor c)  [exp1] [] (next_g s1) = ([(r0, apx)], next_g (s1 with compile_oracle := shift_seq 1 s1.compile_oracle))`
         by (fs [state_rel_def] \\ rfs []
             \\ fs [shift_seq_def, state_cc_def]
             \\ rpt (pairarg_tac \\ fs []) \\ rveq
             \\ fs [compile_inc_def] \\ pairarg_tac \\ fs []
             \\ imp_res_tac known_sing_EQ_E \\ rveq
             \\ fs [state_co_def] \\ rfs []
             \\ rpt (pairarg_tac \\ fs []) \\ rveq
             \\ fs [compile_inc_def] \\ rfs [] \\ rveq
             \\ fs [compile_inc_def]
             \\ simp [next_g_def])
      \\ fs [reset_inline_factor_def]
      \\ first_x_assum drule
      \\ simp [v_rel_upd_inline_factor,
               state_rel_upd_inline_factor]
      \\ disch_then match_mp_tac
      \\ simp []
      \\ conj_tac THEN1 fs [state_rel_def, shift_seq_def, FUPDATE_LIST, FUN_EQ_THM, state_co_def]
      \\ patresolve `evaluate (_, _, s0) = _` hd evaluate_IMP_shift_seq
      \\ strip_tac \\ fs []
      \\ simp [oracle_states_subspt_shift_seq,
               co_every_Fn_vs_NONE_shift_seq,
               oracle_state_sgc_free_shift_seq,
               co_disjoint_globals_shift_seq]
      \\ `every_Fn_vs_NONE [exp1]` by (fs [co_every_Fn_vs_NONE_def, shift_seq_def] \\ metis_tac [SND])
      \\ `esgc_free exp1` by (fs [ssgc_free_def, shift_seq_def, shift_seq_def] \\ metis_tac [SND])
      \\ simp []
      \\ conj_tac
      THEN1 (patresolve `evaluate (_, _, s0) = _` hd evaluate_changed_globals \\ simp []
             \\ strip_tac \\ fs [ssgc_free_def, shift_seq_def, FUPDATE_LIST] \\ metis_tac [])
      \\ rename1 `s1.compile_oracle = shift_seq kk s0.compile_oracle`
      \\ conj_tac
      THEN1 (fs [oracle_states_subspt_def, next_g_def, shift_seq_def]
             \\ metis_tac [FST, ADD_SYM])
      \\ conj_tac
      THEN1 (fs [oracle_states_subspt_def, next_g_def, shift_seq_def])
      \\ conj_tac
      THEN1 (`next_g s1 = FST (FST (s0.compile_oracle kk))` by fs [next_g_def, shift_seq_def]
             \\ fs [oracle_state_sgc_free_def])
      \\ `fv_max 0 [exp1]` by cheat (* TODO: Ask Magnus *)
      \\ simp []
      \\ conj_tac
      THEN1 (patresolve `evaluate (_, _, s0) = _` (el 2) known_correct_approx_no_extra
             \\ rpt (disch_then drule \\ simp [])
             \\ metis_tac [subspt_trans])
      THEN1 (qpat_x_assum `unique_set_globals _ s0.compile_oracle` mp_tac
             \\ `exp1 = FST (SND ((shift_seq kk s0.compile_oracle) 0))` by fs [shift_seq_def]
             \\ pop_assum mp_tac
             \\ rpt (pop_assum kall_tac) \\ simp []
             \\ disch_then kall_tac \\ strip_tac
             \\ drule unique_set_globals_shift_seq
             \\ disch_then (qspec_then `kk` mp_tac)
             \\ pop_assum kall_tac \\ strip_tac
             \\ fs [unique_set_globals_def, elist_globals_append, BAG_ALL_DISTINCT_BAG_UNION]
             \\ gen_tac \\ rpt conj_tac
             THEN1 (pop_assum (qspec_then `SUC 0` assume_tac)
                    \\ fs [first_n_exps_def])
             THEN1 (pop_assum (qspec_then `n + 1` assume_tac)
                    \\ fs [first_n_exps_shift_seq, elist_globals_append,
                           BAG_ALL_DISTINCT_BAG_UNION])
             THEN1 (pop_assum (qspec_then `n + 1` assume_tac)
                    \\ fs [first_n_exps_shift_seq, first_n_exps_def,
                           BAG_ALL_DISTINCT_BAG_UNION])))
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
      \\ fs [])
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
(* THEN1
   (say "Fn"
    \\ fs [known_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, bool_case_eq] \\ rveq
    \\ dsimp []
    \\ qexists_tac `REPLICATE num_args Other ++ aenv` \\ simp []
    \\ conj_tac
    THEN1 fs [state_rel_def]
    THEN1 (simp [exp_rel_def, EVERY_REPLICATE]
           \\ imp_res_tac known_sing_EQ_E \\ rveq \\ fs [] \\ rveq
           \\ qpat_x_assum `known _ _ _ _ = _`
                           (assume_tac o
                            ONCE_REWRITE_RULE [Q.prove (`c = c with inline_factor := c.inline_factor`,
                                                        simp [config_component_equality])])
           \\ goal_assum (pop_assum o mp_then Any mp_tac)
           \\ metis_tac [subspt_trans]))*)
  THEN1
   (say "Fn"
    \\ fs [known_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, bool_case_eq] \\ rveq
    \\ dsimp []
    \\ qexists_tac `aenv` \\ simp []
    \\ conj_tac
    THEN1 fs [state_rel_def]
    THEN1 (simp [exp_rel_def, EVERY_REPLICATE]
           \\ imp_res_tac known_sing_EQ_E \\ rveq \\ fs [] \\ rveq
           \\ qpat_x_assum `known _ _ _ _ = _`
                           (assume_tac o
                            ONCE_REWRITE_RULE [Q.prove (`c = c with inline_factor := c.inline_factor`,
                                                        simp [config_component_equality])])
           \\ goal_assum (pop_assum o mp_then Any mp_tac)
           \\ metis_tac [subspt_trans]))
  THEN1
   (say "Letrec"
    \\ cheat)

  (* Skip to evaluate_app CONS *)
  THEN1 cheat
  THEN1 cheat
  THEN1 cheat
  THEN1 cheat


  THEN1
   (say "App"
    \\ fs [known_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac unique_set_globals_subexps
    \\ imp_res_tac known_LENGTH_EQ_E
    \\ rename1 `known _ _ _ g0 = (_, g1)`
    \\ rename1 `known _ _ _ g1 = (_, g2)`
    \\ `g2 = g` by (fs [inlD_case_eq]
                    \\ rpt (pairarg_tac \\ fs [])
                    \\ fs [bool_case_eq])
    \\ rveq
    \\ patresolve `subspt g0 g` (el 3) subspt_known_elist_globals
    \\ rpt (disch_then drule)
    \\ impl_tac THEN1 (imp_res_tac unique_set_globals_IMP_es_distinct_elist_globals
                       \\ fs [BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
    \\ strip_tac
    \\ `subspt g1 (next_g s0)` by metis_tac [subspt_trans]
    \\ fs [evaluate_def]
    \\ Cases_on `LENGTH xs > 0` \\ fs []
    \\ fs [pair_case_eq]
    \\ rename1 `evaluate (_, _ s0) = (_, s1)`
    \\ `subspt (next_g s0) (next_g s1)`
       by (simp [next_g_def]
           \\ imp_res_tac evaluate_IMP_shift_seq
           \\ imp_res_tac oracle_states_subspt_shift_seq
           \\ fs [oracle_states_subspt_def, shift_seq_def]
           \\ first_x_assum (qspecl_then [`0`, `0`] assume_tac) \\ fs [])
    \\ `subspt (next_g s1) (next_g s)`
       by (simp [next_g_def]
           \\ fs [result_case_eq] \\ rveq \\ fs []
           \\ `?k. s.compile_oracle = shift_seq k s1.compile_oracle`
              by (reverse (fs [pair_case_eq, result_case_eq]) \\ rveq \\ fs []
                  THEN1 (metis_tac [evaluate_IMP_shift_seq])
                  \\ imp_res_tac evaluate_IMP_shift_seq
                  \\ imp_res_tac evaluate_app_IMP_shift_seq
                  \\ fs [] \\ metis_tac [ADD_SYM, ADD_ASSOC])
           \\ imp_res_tac evaluate_IMP_shift_seq \\ fs []
           \\ imp_res_tac oracle_states_subspt_shift_seq
           \\ fs [oracle_states_subspt_def, shift_seq_def])
    \\ `subspt (next_g s1) g'` by metis_tac [subspt_trans]
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ disch_then (qspec_then `xenv2` mp_tac)
    \\ impl_tac THEN1 fs [result_case_eq]  \\ strip_tac
    \\ patresolve `evaluate (_, _, s0) = _` hd evaluate_changed_globals_inst
    \\ simp [] \\ strip_tac \\ fs []
    \\ fs [co_every_Fn_vs_NONE_shift_seq,
           oracle_states_subspt_shift_seq,
           oracle_state_sgc_free_shift_seq,
           unique_set_globals_shift_seq]
    \\ patresolve `known _ _ _ g0 = _` hd known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ patresolve `evaluate (_, _, s0) = _` (el 2) known_correct_approx
    \\ rpt (disch_then drule \\ simp [])
    \\ impl_tac THEN1 metis_tac [subspt_trans]
    \\ strip_tac \\ rveq \\ fs []
    \\ reverse (fs [inlD_case_eq]) \\ rveq
    THEN1
     ((* inlD_LetInline *)
      imp_res_tac decide_inline_LetInline_IMP_Clos_fv_max \\ rveq
      \\ reverse (Cases_on `pure x1`) \\ fs []
      \\ rpt (pairarg_tac \\ fs []) \\ rveq
      \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
      THEN1
       ((* not pure *)
        simp [evaluate_def, evaluate_append]
        \\ fs [result_case_eq] \\ rveq \\ fs []
        \\ fs [pair_case_eq] \\ rveq \\ fs []
        \\ rename1 `evaluate (_, _ s1) = (_, s2)`
        \\ `subspt (next_g s2) (next_g s)`
           by (simp [next_g_def]
               \\ fs [result_case_eq]
               \\ imp_res_tac evaluate_app_IMP_shift_seq
               \\ imp_res_tac evaluate_IMP_shift_seq \\ fs []
               \\ imp_res_tac oracle_states_subspt_shift_seq
               \\ fs [oracle_states_subspt_def, shift_seq_def])
        \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
        \\ disch_then (qspec_then `xenv2` mp_tac)
        \\ simp [co_disjoint_globals_shift_seq]
        \\ impl_tac THEN1 (fs [result_case_eq] \\ metis_tac [subspt_trans])
        \\ strip_tac
        \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
        \\ patresolve `evaluate (_, _, s1) = _` hd evaluate_changed_globals
        \\ simp [] \\ strip_tac \\ fs []
        \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
        \\ patresolve `evaluate (_, _, s1) = _` (el 2) known_correct_approx
        \\ rpt (disch_then drule \\ simp [])
        \\ disch_then (qspec_then `g'` mp_tac)
        \\ simp [co_disjoint_globals_shift_seq,
                 unique_set_globals_shift_seq]
        \\ `subspt g g'` by metis_tac [subspt_trans]
        \\ simp [] \\ strip_tac \\ rveq
        \\ rename1 `known (dec_inline_factor _) [body] _ g = ([(ebody, abody)], gdead)`
        \\ qmatch_assum_abbrev_tac `v_rel _ _ lhclos _`
        \\ rename1 `evaluate (_, _, s0) = (Rval args, _)`
        \\ `v_rel_app c g' lhclos (Closure (SOME m) [] ([r1] ++ env2 ++ xenv2) (LENGTH xs) ebody) (SOME args)`
           by (fs [Abbr `lhclos`, v_rel_app_def]
               \\ qexists_tac `[]` \\ qexists_tac `[]` \\ simp []
               \\ asm_exists_tac \\ simp []
               \\ fs [exp_rel_def] \\ rveq
               \\ fs [dec_inline_factor_def]
               \\ simp [known_extra]
               \\ goal_assum (first_assum o mp_then (Pos last) mp_tac)
               \\ `g = gdead` by (match_mp_tac known_unchanged_globals
                                  \\ asm_exists_tac \\ simp [])
               \\ rveq \\ fs []
               \\ patresolve `known _ [_] _ g1 = _` hd known_preserves_esgc_free
               \\ simp [])
        \\ first_x_assum drule (* inst. evaluate_app i.h. *)
        \\ imp_res_tac nil_unique_set_globals
        \\ simp [oracle_state_sgc_free_shift_seq,
                 co_every_Fn_vs_NONE_shift_seq,
                 oracle_states_subspt_shift_seq,
                 unique_set_globals_shift_seq,
                 co_disjoint_globals_shift_seq]
        \\ rpt (disch_then drule \\ simp [])
        \\ disch_then (qspec_then `SOME m` mp_tac)
        \\ simp [loptrel_def]
        \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
        \\ impl_tac
        THEN1 (fs [decide_inline_def, bool_case_eq]
               \\ simp [NOT_NIL_EQ_LENGTH_NOT_0]
               \\ simp [Abbr `lhclos`, dest_closure_def]
               \\ simp [DROP_NIL]
               \\ simp [check_loc_def]
               \\ fs [dest_closure_def]
               \\ cheat (* LENGTH args <= s2.max_app *))
        \\ qmatch_goalsub_rename_tac `evaluate_app _ _ args2 t2`
        \\ `args2 <> []` by fs [NOT_NIL_EQ_LENGTH_NOT_0]
        \\ simp [evaluate_app_exact_rw]
        \\ strip_tac
        \\ `t2.clock = s2.clock` by fs [state_rel_def]
        \\ simp [evaluate_mk_Ticks_rw]
        \\ fs [bool_case_eq] \\ rveq \\ fs []
        \\ `args2 ⧺ [r1] ⧺ env2 ⧺ xenv2 = args2 ⧺ r1::(env2 ⧺ xenv2)` by simp [APPEND_ASSOC]
        \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND]
        \\ metis_tac [])
      THEN1
       ((* pure *)
        simp [evaluate_def, evaluate_append]
        \\ fs [result_case_eq] \\ rveq \\ fs []
        \\ fs [pair_case_eq] \\ rveq \\ fs []
        \\ rename1 `evaluate (_, _ s1) = (_, s2)`
        \\ `subspt (next_g s2) (next_g s)`
           by (simp [next_g_def]
               \\ fs [result_case_eq]
               \\ imp_res_tac evaluate_app_IMP_shift_seq
               \\ imp_res_tac evaluate_IMP_shift_seq \\ fs []
               \\ imp_res_tac oracle_states_subspt_shift_seq
               \\ fs [oracle_states_subspt_def, shift_seq_def])
        \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
        \\ disch_then (qspec_then `xenv2` mp_tac)
        \\ simp [co_disjoint_globals_shift_seq]
        \\ impl_tac THEN1 (fs [result_case_eq] \\ metis_tac [subspt_trans])
        \\ strip_tac
        \\ reverse (fs [result_case_eq]) \\ rveq \\ fs [] \\ rveq
        THEN1 (rename1 `evaluate ([x1], _, _) = (Rerr err_res, _)`
               \\ drule (pure_correct |> GEN_ALL |> INST_TYPE [``:'c`` |-> ``:val_approx num_map#'c``])
               \\ disch_then (qspecl_then [`s1`, `env1 ++ xenv1`] mp_tac)
               \\ simp [] \\ strip_tac \\ Cases_on `err_res` \\ fs [])
        \\ patresolve `evaluate (_, _, s1) = _` hd evaluate_changed_globals
        \\ simp [] \\ strip_tac \\ fs []
        \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
        \\ patresolve `evaluate (_, _, s1) = _` (el 2) known_correct_approx
        \\ rpt (disch_then drule \\ simp [])
        \\ disch_then (qspec_then `g'` mp_tac)
        \\ simp [co_disjoint_globals_shift_seq,
                 unique_set_globals_shift_seq]
        \\ `subspt g g'` by metis_tac [subspt_trans]
        \\ simp [] \\ strip_tac \\ rveq
        \\ rename1 `known (dec_inline_factor _) [body] _ g = ([(ebody, abody)], gdead)`
        \\ qmatch_assum_abbrev_tac `v_rel _ _ lhclos _`
        \\ rename1 `evaluate (_, _, s0) = (Rval args, _)`
        \\ `v_rel_app c g' lhclos (Closure (SOME m) [] (env2 ++ xenv2) (LENGTH xs) ebody) (SOME args)`
           by (fs [Abbr `lhclos`, v_rel_app_def]
               \\ qexists_tac `[]` \\ qexists_tac `[]` \\ simp []
               \\ asm_exists_tac \\ simp []
               \\ fs [exp_rel_def] \\ rveq
               \\ fs [dec_inline_factor_def]
               \\ simp [known_extra]
               \\ goal_assum (first_assum o mp_then (Pos last) mp_tac)
               \\ `g = gdead` by (match_mp_tac known_unchanged_globals
                                  \\ asm_exists_tac \\ simp [])
               \\ rveq \\ fs []
               \\ patresolve `known _ [_] _ g1 = _` hd known_preserves_esgc_free
               \\ simp [])
        \\ first_x_assum drule (* inst. evaluate_app i.h. *)
        \\ imp_res_tac nil_unique_set_globals
        \\ simp [oracle_state_sgc_free_shift_seq,
                 co_every_Fn_vs_NONE_shift_seq,
                 oracle_states_subspt_shift_seq,
                 unique_set_globals_shift_seq,
                 co_disjoint_globals_shift_seq]
        \\ rpt (disch_then drule \\ simp [])
        \\ disch_then (qspec_then `SOME m` mp_tac)
        \\ simp [loptrel_def]
        \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
        \\ impl_tac
        THEN1 (fs [decide_inline_def, bool_case_eq]
               \\ simp [NOT_NIL_EQ_LENGTH_NOT_0]
               \\ simp [Abbr `lhclos`, dest_closure_def]
               \\ simp [DROP_NIL]
               \\ simp [check_loc_def]
               \\ fs [dest_closure_def]
               \\ cheat (* LENGTH args <= s2.max_app *))
        \\ qmatch_goalsub_rename_tac `evaluate_app _ _ args2 t2`
        \\ `args2 <> []` by fs [NOT_NIL_EQ_LENGTH_NOT_0]
        \\ simp [evaluate_app_exact_rw]
        \\ strip_tac
        \\ `t2.clock = s2.clock` by fs [state_rel_def]
        \\ patresolve `known _ [x1] _ _ = ([e1, _], _)` hd known_preserves_pure
        \\ simp [] \\ strip_tac
        \\ drule (GEN_ALL pure_correct)
        \\ disch_then (qspecl_then [`t`, `env2 ++ xenv2`] mp_tac)
        \\ simp [] \\ strip_tac \\ rveq \\ fs []
        \\ simp [evaluate_mk_Ticks_rw]))
    THEN1
     ((* inlD_Annotate *)
      simp [evaluate_def]
      \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
      \\ fs [pair_case_eq]
      \\ rename1 `evaluate ([_], _ s1) = (_, s2)`
      \\ `subspt (next_g s2) (next_g s)`
          by (simp [next_g_def]
              \\ fs [result_case_eq]
              \\ imp_res_tac evaluate_app_IMP_shift_seq
              \\ imp_res_tac evaluate_IMP_shift_seq \\ fs []
              \\ imp_res_tac oracle_states_subspt_shift_seq
              \\ fs [oracle_states_subspt_def, shift_seq_def])
      \\ `subspt g (next_g s1) ∧ subspt (next_g s2) g'` by metis_tac [subspt_trans]
      \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
      \\ simp [co_disjoint_globals_shift_seq]
      \\ disch_then (qspec_then `xenv2` mp_tac)
      \\ imp_res_tac known_sing_EQ_E
      \\ fs [result_case_eq] \\ strip_tac \\ rveq \\ fs []
      \\ imp_res_tac evaluate_SING \\ fs [] \\ rveq
      \\ first_x_assum match_mp_tac
      \\ imp_res_tac nil_unique_set_globals
      \\ patresolve `evaluate (_, _, s1) = _` hd evaluate_changed_globals_inst
      \\ simp [] \\ strip_tac \\ fs []
      \\ simp [co_every_Fn_vs_NONE_shift_seq,
               oracle_states_subspt_shift_seq,
               oracle_state_sgc_free_shift_seq,
               co_disjoint_globals_shift_seq,
               unique_set_globals_shift_seq]
      \\ qexists_tac `NONE` \\ simp [v_rel_app_NONE]
      \\ patresolve `evaluate (_, _, s1) = _` (el 2) known_correct_approx
      \\ rpt (disch_then drule \\ simp [])
      \\ disch_then (qspec_then `g'` mp_tac)
      \\ simp [co_disjoint_globals_shift_seq,
               unique_set_globals_shift_seq]
      \\ impl_tac THEN1 metis_tac [subspt_trans]
      \\ strip_tac \\ simp []
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ simp [loptrel_def]
      \\ fs [decide_inline_def, va_case_eq, bool_case_eq]
      \\ rveq \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac LIST_REL_LENGTH \\ fs []
      \\ rename1 `FST (EL jj fns1) = FST (EL jj fns2)`
      \\ qpat_x_assum `LIST_REL (f_rel _ _ _) _ _` mp_tac
      \\ simp [LIST_REL_EL_EQN] \\ disch_then (qspec_then `jj` mp_tac)
      \\ Cases_on `EL jj fns1` \\ Cases_on `EL jj fns2`
      \\ simp [f_rel_def])
    THEN1
     ((* inlD_Nothing *)
      simp [evaluate_def]
      \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
      \\ fs [pair_case_eq]
      \\ rename1 `evaluate ([_], _ s1) = (_, s2)`
      \\ `subspt (next_g s2) (next_g s)`
          by (simp [next_g_def]
              \\ fs [result_case_eq]
              \\ imp_res_tac evaluate_app_IMP_shift_seq
              \\ imp_res_tac evaluate_IMP_shift_seq \\ fs []
              \\ imp_res_tac oracle_states_subspt_shift_seq
              \\ fs [oracle_states_subspt_def, shift_seq_def])
      \\ `subspt g (next_g s1) ∧ subspt (next_g s2) g'` by metis_tac [subspt_trans]
      \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
      \\ simp [co_disjoint_globals_shift_seq]
      \\ disch_then (qspec_then `xenv2` mp_tac)
      \\ imp_res_tac known_sing_EQ_E
      \\ fs [result_case_eq] \\ strip_tac \\ rveq \\ fs []
      \\ imp_res_tac evaluate_SING \\ fs [] \\ rveq
      \\ first_x_assum match_mp_tac
      \\ imp_res_tac nil_unique_set_globals
      \\ patresolve `evaluate (_, _, s1) = _` hd evaluate_changed_globals_inst
      \\ simp [] \\ strip_tac \\ fs []
      \\ simp [co_every_Fn_vs_NONE_shift_seq,
               oracle_states_subspt_shift_seq,
               oracle_state_sgc_free_shift_seq,
               co_disjoint_globals_shift_seq,
               unique_set_globals_shift_seq]
      \\ qexists_tac `NONE` \\ simp [v_rel_app_NONE]
      \\ patresolve `evaluate (_, _, s1) = _` (el 2) known_correct_approx
      \\ rpt (disch_then drule \\ simp [])
      \\ disch_then (qspec_then `g'` mp_tac)
      \\ simp [co_disjoint_globals_shift_seq,
               unique_set_globals_shift_seq]
      \\ impl_tac THEN1 metis_tac [subspt_trans]
      \\ simp [loptrel_def]))
  THEN1
   (say "Tick"
    \\ fs [known_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, pair_case_eq]
    \\ `t0.clock = s0.clock` by fs [state_rel_def]
    \\ Cases_on `s0.clock = 0` \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ first_x_assum drule \\ simp []
    \\ disch_then match_mp_tac
    \\ fs [dec_clock_def, state_rel_def, next_g_def]
    \\ asm_exists_tac \\ simp []
    \\ imp_res_tac unique_set_globals_subexps \\ simp [])

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

    \\ fs [evaluate_def]
    \\ fs [dec_clock_def, ADD1]
    \\ `t0.max_app = s0.max_app /\ s0.clock = t0.clock` by fs [state_rel_def]
    \\ fs [case_eq_thms] \\ fs [] \\ rveq
    THEN1 ((* dest_closure returns Partial_app *)
      imp_res_tac dest_closure_none_loc
      \\ drule dest_closure_SOME_IMP \\ strip_tac
      \\ fs [v_rel_app_def]
      \\ fs [dest_closure_def] \\ rveq
      \\ imp_res_tac LIST_REL_LENGTH
      \\ fs [METIS_PROVE [] ``(if b then SOME x else SOME y) = SOME (if b then x else y)``]
      THEN1
       (IF_CASES_TAC \\ fs []
        \\ IF_CASES_TAC \\ fs [] \\ rveq
        \\ fs [state_rel_def]
        \\ fs [loptrel_def, check_loc_def]
        \\ EVERY_CASE_TAC \\ fs []
        \\ qexists_tac `aenv` \\ simp [] 
        \\ rveq \\ simp []
        \\ irule EVERY2_APPEND_suff \\ simp [])
      THEN1 cheat (* Recclosure *))

    THEN1 ((* dest_closure returns Full_app *)    
      Cases_on `argsopt` \\ fs [] \\ rveq

      THEN1
       (drule dest_closure_SOME_IMP \\ strip_tac \\ rveq
        \\ fs [v_rel_app_def] \\ rveq \\ fs []
        \\ fs [dest_closure_def] \\ rveq
        \\ imp_res_tac LIST_REL_LENGTH
        \\ fs [METIS_PROVE [] ``(if b then SOME x else SOME y) = SOME (if b then x else y)``]

        THEN1
         (IF_CASES_TAC \\ fs [] \\ rveq
          \\ qpat_abbrev_tac `loc_is_ok = check_loc _ lopt2 _ _ _ _`
          \\ `loc_is_ok` by (fs [Abbr `loc_is_ok`, loptrel_def, check_loc_def]
                             \\ TRY (Cases_on `lopt2` \\ fs [])
                             \\ TRY (Cases_on `loc` \\ fs [] \\ rveq)
                             \\ fs [check_loc_def])
          \\ simp [Abbr `loc_is_ok`]
          \\ fs [bool_case_eq] \\ rveq \\ fs []
          THEN1 fs [state_rel_def]
          \\ fs [pair_case_eq]
          \\ rfs [SUB_SUB]
          \\ first_x_assum drule
          \\ fs [exp_rel_def]
          \\ rename1 `known _ _ _ g0 = (_, g1)`
          \\ `g0 = g1` by (match_mp_tac known_unchanged_globals
                           \\ asm_exists_tac \\ simp [])
          \\ disch_then drule
          \\ simp [v_rel_upd_inline_factor, state_rel_upd_inline_factor]
          \\ qmatch_asmsub_abbrev_tac `evaluate (_, fullenv1, state1)`
          \\ qmatch_goalsub_abbrev_tac `evaluate (_, fullenv2, state2)`
          \\ `LIST_REL (v_rel c g) fullenv1 fullenv2`
             by (simp [Abbr `fullenv1`, Abbr `fullenv2`]
                 \\ rpt (irule EVERY2_APPEND_suff \\ simp [])
                 \\ irule EVERY2_TAKE
                 \\ irule EVERY2_APPEND_suff \\ simp [])
          \\ disch_then drule \\ simp []
          \\ `state_rel c g state1 state2`
             by (fs [Abbr `state1`, Abbr `state2`, state_rel_def])
          \\ disch_then drule \\ simp []
          \\ simp [set_globals_empty_esgc_free]
          \\ simp [EVERY_REVERSE, EVERY_TAKE]

          \\ `fv_max (num_args + LENGTH env2) [e]`
             by (

                 cheat)

          \\ simp [set_globals_empty_unique_set_globals]
          \\ rename1 `evaluate (_, _, state1) = (_, s1)`
          \\ rveq
          \\ `subspt (next_g state1) (next_g s1)`
             by (fs [Abbr `state1`]
                 \\ simp [next_g_def]
                 \\ fs [result_case_eq] \\ rveq
                 \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
                 \\ imp_res_tac evaluate_app_IMP_shift_seq
                 \\ imp_res_tac evaluate_IMP_shift_seq \\ fs []
                 \\ imp_res_tac oracle_states_subspt_shift_seq
                 \\ simp [shift_seq_def]
                 \\ irule oracle_states_subspt_alt \\ simp [])
          \\ simp []
          \\ impl_tac
          THEN1
           (rpt conj_tac
            THEN1 cheat (* subspt g0 (next_g s0) *)
            THEN1 cheat (* subspt (next_g s0) g *)
            THEN1 (simp [Abbr `fullenv1`]
                   \\ irule EVERY2_APPEND_suff \\ simp []
                   \\ simp [LIST_REL_EL_EQN, EL_REPLICATE])
            THEN1 fs [result_case_eq])
          \\ strip_tac \\ fs []
          \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
          \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
          \\ reverse (Cases_on `lopt1 = lopt2`)
          THEN1
           (fs [loptrel_def]
            \\ Cases_on `lopt2` \\ fs []
            \\ Cases_on `loc` \\ fs [] \\ rveq \\ fs []
            \\ rename1 `evaluate_app lopt1 f1' _ _ = _`
            \\ qmatch_assum_abbrev_tac `evaluate_app lopt1 f1' next_args1 _ = _`
            \\ qmatch_goalsub_abbrev_tac `evaluate_app _ _ next_args2 _ = _`
            \\ `next_args1 = []` by fs [Abbr `next_args1`, DROP_NIL]
            \\ `next_args2 = []` by fs [Abbr `next_args2`, DROP_NIL]
            \\ fs [Abbr `next_args1`, Abbr `next_args2`]
            \\ rveq \\ simp [])
          \\ first_x_assum match_mp_tac
          \\ qexists_tac `NONE` \\ simp []
          \\ patresolve `evaluate (_, _, state1) = _` hd evaluate_changed_globals
          \\ patresolve `evaluate (_, _, state1) = _` (el 2) known_correct_approx_no_extra
          \\ unabbrev_all_tac
          \\ rpt (disch_then drule \\ simp [])
          \\ disch_then (qspec_then `g` mp_tac)
          \\ simp [set_globals_empty_esgc_free]
          \\ simp [set_globals_empty_unique_set_globals]
          \\ simp [EVERY_REVERSE, EVERY_TAKE]
          \\ impl_tac THEN1 (irule EVERY2_APPEND_suff \\ simp []
                             \\ simp [LIST_REL_EL_EQN, EL_REPLICATE])
          \\ strip_tac \\ strip_tac
          \\ simp [EVERY_DROP, EVERY_REVERSE]
          \\ simp [oracle_state_sgc_free_shift_seq,
                   co_every_Fn_vs_NONE_shift_seq,
                   oracle_states_subspt_shift_seq,
                   co_disjoint_globals_shift_seq,
                   unique_set_globals_shift_seq]
          \\ simp [v_rel_app_NONE]
          \\ conj_tac THEN1 (irule EVERY2_DROP 
                             \\ irule EVERY2_APPEND_suff \\ simp [])
          \\ simp [loptrel_def])
        THEN1 cheat (* Recclosure *))
      THEN1 ((* ISSOME argsopt *)
        dsimp [] \\ disj2_tac
        \\ fs [bool_case_eq] \\ rveq \\ fs []
        THEN1
         (drule dest_closure_SOME_IMP \\ strip_tac \\ rveq
          \\ fs [v_rel_app_def] \\ rveq \\ fs []
          \\ fs [dest_closure_def] \\ rveq \\ fs []
          \\ imp_res_tac LIST_REL_LENGTH
          \\ TRY (rpt (pairarg_tac \\ fs [])
                  \\ rename1 `LIST_REL (f_rel _ _ _) funs1 funs2`
                  \\ rename1 `EL i funs1 = (num_args1, _)`
                  \\ rename1 `EL i funs2 = (num_args2, _)`
                  \\ `num_args1 = num_args2`
                     by (fs [NOT_LESS_EQUAL, LIST_REL_EL_EQN]
                         \\ first_x_assum (qpat_assum `i < _` o mp_then (Pos hd) mp_tac)
                         \\ simp [f_rel_def]))
          \\ fs [bool_case_eq] \\ rveq
          \\ qexists_tac `t0 with clock := 0`
          \\ fs [CONV_RULE (LHS_CONV SYM_CONV) REVERSE_EQ_NIL]
          \\ fs [DROP_NIL, NOT_LESS, ADD1, GREATER_EQ]
          \\ imp_res_tac LESS_EQUAL_ANTISYM \\ fs []
          \\ fs [state_rel_def]
          \\ Cases_on `lopt1 = lopt2`
          \\ fs [loptrel_def]
          \\ Cases_on `lopt2` \\ fs []
          \\ Cases_on `loc` \\ fs [] \\ rveq
          \\ fs [check_loc_def])
        THEN1
         (drule dest_closure_SOME_IMP \\ strip_tac \\ rveq
          \\ fs [v_rel_app_def] \\ rveq \\ fs []
          \\ fs [dest_closure_def] \\ rveq
          \\ imp_res_tac LIST_REL_LENGTH
          THEN1
           (IF_CASES_TAC \\ fs [] \\ rveq
            \\ qpat_abbrev_tac `loc_is_ok = check_loc _ lopt2 _ _ _ _`
            \\ `loc_is_ok` by (fs [Abbr `loc_is_ok`, loptrel_def, check_loc_def]
                             \\ TRY (Cases_on `lopt2` \\ fs [])
                             \\ TRY (Cases_on `loc` \\ fs [] \\ rveq)
                             \\ fs [check_loc_def])
            \\ simp [Abbr `loc_is_ok`]
            \\ fs [pair_case_eq]
            \\ first_x_assum drule
            \\ fs [exp_rel_def]
            \\ rename1 `known _ _ _ g0 = (_, g1)`
            \\ `g0 = g1` by (match_mp_tac known_unchanged_globals
                             \\ asm_exists_tac \\ simp [])
            \\ disch_then drule
            \\ simp [v_rel_upd_inline_factor, state_rel_upd_inline_factor]
            \\ qmatch_asmsub_abbrev_tac `evaluate (_, fullenv1, state1)`
            \\ qmatch_goalsub_abbrev_tac `evaluate (_, fullenv2, state2)`
            \\ `LIST_REL (v_rel c g) fullenv1 fullenv2`
               by (simp [Abbr `fullenv1`, Abbr `fullenv2`]
                   \\ rpt (irule EVERY2_APPEND_suff \\ simp [])
                   \\ irule EVERY2_TAKE
                   \\ irule EVERY2_APPEND_suff \\ simp [])
            \\ disch_then drule \\ simp []
            \\ `num_args = LENGTH ys + 1` by fs [DROP_NIL]
            \\ `state_rel c g state1 state2`
               by (fs [Abbr `state1`, Abbr `state2`, state_rel_def, DROP_NIL])
            \\ disch_then drule \\ simp []
            \\ simp [set_globals_empty_esgc_free]
            \\ simp [EVERY_REVERSE, EVERY_TAKE]
            \\ simp [set_globals_empty_unique_set_globals]
            \\ impl_tac
            THEN1
             (rpt conj_tac
              THEN1 cheat
              THEN1 cheat
              THEN1 (unabbrev_all_tac \\ rveq \\ fs []
                     \\ simp [TAKE_LENGTH_ID_rwt]
                     \\ irule EVERY2_APPEND_suff \\ simp [])
              THEN1 cheat
              THEN1 fs [result_case_eq])
            \\ strip_tac
            \\ fs [result_case_eq] \\ rveq \\ fs []
            \\ imp_res_tac evaluate_SING \\ fs [] \\ rveq
            \\ simp [DROP_LENGTH_TOO_LONG])
          THEN1
           (rpt (pairarg_tac \\ fs [])
            \\ fs [bool_case_eq] \\ rveq
            \\ rename1 `LIST_REL (f_rel _ _ _) funs1 funs2`
            \\ rename1 `EL i funs1 = (num_args1, exp1)`
            \\ rename1 `EL i funs2 = (num_args2, exp2)`
            \\ `num_args1 = num_args2`
               by (fs [NOT_LESS_EQUAL, LIST_REL_EL_EQN]
                   \\ first_x_assum (qpat_assum `i < _` o mp_then (Pos hd) mp_tac)
                   \\ simp [f_rel_def])
            \\ qpat_abbrev_tac `loc_is_ok = check_loc _ lopt2 _ _ _ _`
            \\ `loc_is_ok`
               by (fs [Abbr `loc_is_ok`, loptrel_def]
                   \\ TRY (Cases_on `lopt2` \\ fs [])
                   \\ TRY (Cases_on `loc` \\ fs [] \\ rveq)
                   \\ fs [check_loc_def, DROP_NIL])
            \\ simp [Abbr `loc_is_ok`]
            \\ fs [pair_case_eq]
            \\ first_x_assum drule
            \\ qmatch_asmsub_abbrev_tac `f_rel _ aenvcase`
            \\ `f_rel c aenvcase g (EL i funs1) (EL i funs2)` by fs [LIST_REL_EL_EQN]
            \\ rfs [] \\ fs [f_rel_def, exp_rel_def]
            \\ rename1 `known _ _ _ g0 = (_, g1)`
            \\ `MEM (EL i funs1) funs1` by simp [EL_MEM]
            \\ pop_assum mp_tac \\ simp [] \\ strip_tac
            \\ `g0 = g1` by (match_mp_tac known_unchanged_globals
                             \\ asm_exists_tac \\ simp []
                             \\ fs [elglobals_EQ_EMPTY]
                             \\ first_x_assum irule
                             \\ simp [MEM_MAP]
                             \\ qexists_tac `EL i funs1` \\ simp [])
            \\ rveq
            \\ disch_then drule
            \\ simp [v_rel_upd_inline_factor, state_rel_upd_inline_factor]
            \\ qmatch_asmsub_abbrev_tac `evaluate (_, fullenv1, state1)`
            \\ qmatch_goalsub_abbrev_tac `evaluate (_, fullenv2, state2)`
            \\ `LIST_REL (v_rel c g) fullenv1 fullenv2`
               by (simp [Abbr `fullenv1`, Abbr `fullenv2`]
                   \\ rpt (irule EVERY2_APPEND_suff \\ simp [])
                   THEN1 (irule EVERY2_TAKE
                          \\ irule EVERY2_APPEND_suff \\ simp [])
                   \\ fs [LIST_REL_GENLIST] \\ rw []
                   \\ asm_exists_tac \\ simp [])
            \\ disch_then drule \\ simp []
            \\ `state_rel c g state1 state2`
               by (fs [Abbr `state1`, Abbr `state2`, state_rel_def]
                   \\ fs [CONV_RULE (LHS_CONV SYM_CONV) REVERSE_EQ_NIL, DROP_NIL])
            \\ disch_then drule \\ simp []
            \\ simp [EVERY_REVERSE, EVERY_TAKE, EVERY_GENLIST]
            \\ `set_globals exp1 = {||}`
               by (fs [elglobals_EQ_EMPTY]
                   \\ first_x_assum irule \\ simp [MEM_MAP]
                   \\ qexists_tac `EL i funs1` \\ simp [])
            \\ simp [set_globals_empty_esgc_free]
            \\ simp [set_globals_empty_unique_set_globals]
            \\ impl_tac
            THEN1
             (rpt conj_tac
              THEN1 (fs [EVERY_MEM, FORALL_PROD] \\ metis_tac [])
              THEN1 cheat
              THEN1 cheat
              THEN1 (simp [Abbr `fullenv1`, Abbr `aenvcase`]
                     \\ rpt (irule EVERY2_APPEND_suff \\ simp [])
                     THEN1 simp [LIST_REL_EL_EQN, EL_REPLICATE]
                     \\ Cases_on `loc` \\ simp []
                     THEN1 simp [LIST_REL_EL_EQN, EL_REPLICATE]
                     THEN1 simp [clos_gen_noinline_eq, LIST_REL_EL_EQN])
              THEN1 cheat
              THEN1 fs [result_case_eq])
            \\ strip_tac
            \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
            \\ imp_res_tac evaluate_SING \\ rveq \\ fs [] \\ rveq \\ fs []           
            \\ fs [CONV_RULE (LHS_CONV SYM_CONV) REVERSE_EQ_NIL, DROP_NIL]
            \\ simp [DROP_LENGTH_TOO_LONG]))))

);

val _ = export_theory();
