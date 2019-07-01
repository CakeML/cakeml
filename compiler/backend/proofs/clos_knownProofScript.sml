(*
  Correctness proof for clos_known
*)

open preamble local open bagLib in end
open closPropsTheory clos_knownTheory clos_knownPropsTheory closSemTheory
     closLangTheory db_varsTheory backendPropsTheory
local open clos_letopProofTheory clos_ticksProofTheory clos_fvsProofTheory in end

val _ = new_theory "clos_knownProof";

val _ = set_grammar_ancestry
  [ "closLang", "closSem", "closProps", "clos_known", "clos_knownProps" ];
val _ = temp_bring_to_front_overload "domain" {Name = "domain", Thy = "sptree"};

fun patresolve p f th = Q.PAT_ASSUM p (mp_then (Pos f) mp_tac th)
fun say0 pfx s g = (print (pfx ^ ": " ^ s ^ "\n"); ALL_TAC g)

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

(* simple properties of constants from clos_known: i.e., merge and known *)

Theorem known_op_changed_globals:
   !opn aenv g0 a g.
     known_op opn aenv g0 = (a, g) ==>
     !i. i ∈ domain g /\ (i ∈ domain g0 ==> lookup i g <> lookup i g0) ==>
         i ∈ SET_OF_BAG (op_gbag opn)
Proof
  rpt gen_tac \\ Cases_on `opn`
  \\ simp [known_op_def, case_eq_thms, op_gbag_def,
           pair_case_eq, bool_case_eq, va_case_eq]
  \\ rw []
  \\ fs [lookup_insert, bool_case_eq]
QED

Theorem known_changed_globals:
   !c xs aenv g0 alist g.
     known c xs aenv g0 = (alist, g) ==>
     !i. i ∈ domain g ∧ (i ∈ domain g0 ==> lookup i g <> lookup i g0) ==>
         i ∈ SET_OF_BAG (elist_globals xs)
Proof
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
  \\ metis_tac []
QED

Theorem known_unchanged_globals:
   !c xs aenv g0 eas1 g1.
     known c xs aenv g0 = (eas1, g1) /\
     elist_globals xs = {||} ==> g0 = g1
Proof
  ho_match_mp_tac known_ind
  \\ simp [known_def]
  \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  THEN1 (Cases_on `op`
         \\ fs [known_op_def, bool_case_eq,
                case_eq_thms, va_case_eq, op_gbag_def])
  THEN1 (fs [inlD_case_eq]
         \\ rpt (pairarg_tac \\ fs [])
         \\ fs [bool_case_eq])
QED


Theorem known_op_changed_globals_alt:
   !opn aenv g0 a g.
     known_op opn aenv g0 = (a, g) ==>
       BAG_OF_SET (domain g) ≤ BAG_OF_SET (domain g0) ⊎ (op_gbag opn)
Proof
  rpt gen_tac \\ Cases_on `opn`
  \\ simp [known_op_def, case_eq_thms, op_gbag_def,
           pair_case_eq, bool_case_eq, va_case_eq]
  \\ rw []
  \\ fs [lookup_insert, bool_case_eq]
  \\ fs [BAG_OF_SET, SUB_BAG, BAG_INN, BAG_UNION, GREATER_EQ, BAG_INSERT]
  \\ rw []
QED

Theorem known_op_changed_globals_alt_set:
   !opn aenv g0 a g.
     known_op opn aenv g0 = (a, g) ==>
       domain g ⊆ domain g0 ∪ SET_OF_BAG (op_gbag opn)
Proof
  rw []
  \\ imp_res_tac known_op_changed_globals_alt
  \\ imp_res_tac SUB_BAG_SET
  \\ fs [SET_OF_BAG_UNION]
QED

Theorem known_changed_globals_alt:
   !c xs aenv g0 alist g.
     known c xs aenv g0 = (alist, g) ==>
       BAG_OF_SET (domain g) ≤ BAG_OF_SET (domain g0) ⊎ (elist_globals xs)
Proof
  ho_match_mp_tac known_ind \\ simp [known_def] \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ fsrw_tac [bagLib.SBAG_SOLVE_ss] []
  THEN1
   (imp_res_tac known_op_changed_globals_alt
    \\ fsrw_tac [bagLib.SBAG_SOLVE_ss] [])
  \\ fs [inlD_case_eq]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ fs [bool_case_eq]
  \\ fsrw_tac [bagLib.SBAG_SOLVE_ss] []
QED

Theorem known_changed_globals_alt_set:
   !c xs aenv g0 alist g.
     known c xs aenv g0 = (alist, g) ==>
       domain g ⊆ domain g0 ∪ SET_OF_BAG (elist_globals xs)
Proof
  rw []
  \\ imp_res_tac known_changed_globals_alt
  \\ imp_res_tac SUB_BAG_SET
  \\ fs [SET_OF_BAG_UNION]
QED

(* Take the first n expression lists returned by the compile oracle. *)
val first_n_exps_def = Define `
  first_n_exps co n = GENLIST (FST o SND o co) n`;

Theorem first_n_exps_shift_seq:
   !co n k. first_n_exps co (n + k) = first_n_exps co k ++ first_n_exps (shift_seq k co) n
Proof
  Induct_on `n`
  \\ rpt strip_tac
  \\ fs [first_n_exps_def]
  \\ REWRITE_TAC [Q.prove (`k + SUC n = SUC (k + n)`, decide_tac)]
  \\ fs [GENLIST]
  \\ fs [shift_seq_def]
QED

Theorem MEM_first_n_exps:
   !k n. k < n ==> !co. MEM (FST (SND (co k))) (first_n_exps co n)
Proof
  rw [first_n_exps_def, MEM_GENLIST] \\ metis_tac []
QED

(* All globals set in the program and in code returned by
   the compile oracle are unique. *)
val unique_set_globals_def = Define `
  unique_set_globals es co <=>
    !n. BAG_ALL_DISTINCT (elist_globals (es ++ FLAT (first_n_exps co n)))`;

Theorem unique_set_globals_shift_seq:
   !es co. unique_set_globals es co ==> !k. unique_set_globals es (shift_seq k co)
Proof
  fs [unique_set_globals_def]
  \\ rpt strip_tac
  \\ pop_assum (qspec_then `n + k` assume_tac)
  \\ fs [first_n_exps_shift_seq]
  \\ fs [elist_globals_append]
  \\ fs [BAG_ALL_DISTINCT_BAG_UNION]
QED

Theorem unique_set_globals_evaluate:
   !es xs env s1 s2 res. unique_set_globals xs s1.compile_oracle /\
   evaluate (es,env,s1) = (res, s2) ==> unique_set_globals xs s2.compile_oracle
Proof
  rpt strip_tac \\ imp_res_tac evaluate_code \\ fs []
  \\ simp [unique_set_globals_shift_seq]
QED

Theorem unique_set_globals_subexps:
  (unique_set_globals (x1::x2::xs) co ==>
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
     unique_set_globals xs co (* /\ !n. BAG_ALL_DISTINCT (op_gbag opn ⊎ (elist_globals (first_n_exps co n)))*)) /\
  (unique_set_globals [Fn t loc_opt vsopt num_args x1] co ==>
     unique_set_globals [x1] co) /\
  (unique_set_globals [Letrec t loc_opt vsopt fns x1] co ==>
     unique_set_globals [x1] co /\ unique_set_globals (MAP SND fns) co) /\
  (unique_set_globals [App t loc_opt x1 xs] co ==>
     unique_set_globals [x1] co /\ unique_set_globals xs co) /\
  (unique_set_globals [Tick t x1] co ==>
     unique_set_globals [x1] co) /\
  (unique_set_globals [Call t ticks dest xs] co ==>
     unique_set_globals xs co)
Proof
  rpt strip_tac
  \\ fs [unique_set_globals_def]
  \\ fs [elist_globals_append]
  \\ fs [BAG_ALL_DISTINCT_BAG_UNION]
QED

val unique_set_globals_subexps = GEN_ALL unique_set_globals_subexps;

Theorem unique_set_globals_IMP_es_distinct_elist_globals:
   !es co. unique_set_globals es co ==> BAG_ALL_DISTINCT (elist_globals es)
Proof
  simp [unique_set_globals_def, elist_globals_append, BAG_ALL_DISTINCT_BAG_UNION]
QED

Theorem set_globals_empty_unique_set_globals:
   set_globals e = {||} ==> (unique_set_globals [e] co <=> unique_set_globals [] co)
Proof
  simp [unique_set_globals_def]
QED

Theorem nil_unique_set_globals:
   unique_set_globals es co ==> unique_set_globals [] co
Proof
  simp [unique_set_globals_def]
  \\ simp [elist_globals_append, BAG_ALL_DISTINCT_BAG_UNION]
QED


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

Theorem val_approx_sgc_free_merge:
   !a1 a2. val_approx_sgc_free a1 /\ val_approx_sgc_free a2 ==>
   val_approx_sgc_free (merge a1 a2)
Proof
  ho_match_mp_tac merge_ind \\ simp []
  \\ rpt strip_tac
  \\ IF_CASES_TAC \\ fs [] \\ rveq
  \\ fs [EVERY_MEM]
  \\ simp [MAP2_MAP, MEM_MAP, PULL_EXISTS]
  \\ simp [MEM_ZIP, PULL_EXISTS]
  \\ fs [MEM_EL]
  \\ metis_tac []
QED

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

Theorem val_approx_val_merge_I_lemma:
   !a1 v. val_approx_val a1 v ==> !a2. val_approx_val (merge a1 a2) v
Proof
  ho_match_mp_tac val_approx_val_ind
  \\ rw [] \\ Cases_on `a2` \\ fs []
  \\ TRY (IF_CASES_TAC \\ fs [] \\ rveq)
  THEN1 fs [LIST_REL_EL_EQN,  MAP2_MAP, EL_MAP, EL_ZIP]
  THEN1 (fs [LIST_REL_EL_EQN] \\ rfs [] \\ rw [] \\ res_tac
         \\ first_x_assum (qspec_then `Impossible` assume_tac) \\ fs [])
QED

Theorem val_approx_val_merge_I:
   !a1 v a2.
     val_approx_val a1 v \/ val_approx_val a2 v ==>
     val_approx_val (merge a1 a2) v
Proof
  metis_tac [val_approx_val_merge_I_lemma, merge_comm]
QED

Theorem evaluate_IMP_shift_seq:
   !es env s0 res s.
     closSem$evaluate (es, env, s0) = (res, s) ==>
       ?k. s.compile_oracle = shift_seq k s0.compile_oracle
Proof
  metis_tac [evaluate_code]
QED

Theorem shift_seq_zero[simp]:
   !co. shift_seq 0 co = co
Proof
  simp [shift_seq_def, ETA_THM]
QED

Theorem shift_seq_add[simp]:
   !co k1 k2. shift_seq k2 (shift_seq k1 co) = shift_seq (k1 + k2) co
Proof
  simp [shift_seq_def]
QED

Theorem do_install_IMP_shift_seq:
   do_install xs s0 = (res, s) ==>
     ?k. s.compile_oracle = shift_seq k s0.compile_oracle
Proof
   rpt strip_tac  \\ fs [do_install_def]
   \\ fs [case_eq_thms]
   \\ TRY (qexists_tac `0` \\ simp [] \\ NO_TAC)
   \\ pairarg_tac \\ fs []
   \\ fs [bool_case_eq, case_eq_thms, pair_case_eq]
   \\ TRY (qexists_tac `0` \\ simp [] \\ NO_TAC)
   \\ metis_tac []
QED

Theorem evaluate_app_IMP_shift_seq:
   evaluate_app lopt f args s0 = (res, s) ==>
     ?k. s.compile_oracle = shift_seq k s0.compile_oracle
Proof
  metis_tac [evaluate_app_code]
QED

val state_globals_approx_def = Define `
  state_globals_approx s g <=>
    !k v a.
      get_global k s.globals = SOME (SOME v) /\ lookup k g = SOME a ==> val_approx_val a v
`;

Theorem state_globals_approx_clock_fupd[simp]:
   state_globals_approx (s with clock updated_by f) g ⇔
   state_globals_approx s g
Proof
  simp[state_globals_approx_def]
QED

Theorem state_globals_approx_dec_clock[simp]:
   state_globals_approx (dec_clock n s) g ⇔ state_globals_approx s g
Proof
  simp[dec_clock_def]
QED

Theorem state_globals_approx_refsfupd[simp]:
   state_globals_approx (s with refs updated_by f) g ⇔
   state_globals_approx s g
Proof
  simp[state_globals_approx_def]
QED

Theorem state_globals_approx_ffifupd[simp]:
   state_globals_approx (s with ffi updated_by f) g ⇔
   state_globals_approx s g
Proof
  simp[state_globals_approx_def]
QED

Theorem state_globals_approx_codeupd[simp]:
   state_globals_approx (s with code updated_by f) g ⇔
   state_globals_approx s g
Proof
  simp[state_globals_approx_def]
QED

Theorem state_globals_approx_coupd[simp]:
   state_globals_approx (s with compile_oracle updated_by f) g ⇔
   state_globals_approx s g
Proof
  simp[state_globals_approx_def]
QED

(* Mapped globals *)

val mapped_globals_def = Define`
  mapped_globals g =
    { i | ∃v. get_global i g = SOME (SOME v) }
`;

(* Extending mapped globals *)

val mglobals_extend_def = Define`
  mglobals_extend g1 mgs g2 ⇔
     mapped_globals g2 ⊆ mapped_globals g1 ∪ mgs ∧
     ∀k v. get_global k g2 = SOME (SOME v) ∧ k ∉ mgs ⇒
           get_global k g1 = SOME (SOME v)`

Theorem mglobals_extend_refl[simp]:
   mglobals_extend s gs s
Proof
  simp[mglobals_extend_def]
QED

Theorem mglobals_extend_trans:
   !s0 s1 s2 g1 g2. mglobals_extend s0 g1 s1 ∧ mglobals_extend s1 g2 s2 ⇒
   mglobals_extend s0 (g1 ∪ g2) s2
Proof
  simp[mglobals_extend_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem mglobals_extend_SUBSET:
   !s0 s g1 g2. mglobals_extend s0 g1 s ∧ g1 ⊆ g2 ⇒ mglobals_extend s0 g2 s
Proof
  simp[mglobals_extend_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem subspt_better_definedg:
   !sp1 sp2 sp3. subspt sp1 sp3 ∧ better_definedg sp1 sp2 ∧ better_definedg sp2 sp3 ⇒
   subspt sp1 sp2
Proof
  simp[subspt_def, better_definedg_def] >> rpt strip_tac >>
  spose_not_then assume_tac >>
  `k ∈ domain sp2 ∧ k ∈ domain sp3` by metis_tac [] >>
  `∃v1 v2 v3. lookup k sp1 = SOME v1 ∧ lookup k sp2 = SOME v2 ∧
              lookup k sp3 = SOME v3` by metis_tac[domain_lookup] >>
  `v3 = v1` by metis_tac[SOME_11] >> rveq >>
  `v1 ◁ v2 ∧ v2 ◁ v1` by metis_tac[THE_DEF] >>
  metis_tac[subapprox_antisym]
QED

Theorem subspt_known_elist_globals:
   ∀c es1 as1 g0 al1 g1 es2 as2 al2 g2.
     known c es1 as1 g0 = (al1, g1) ∧ known c es2 as2 g1 = (al2, g2) ∧
     subspt g0 g2 ∧ BAG_DISJOINT (elist_globals es1) (elist_globals es2) ⇒
     subspt g0 g1 ∧ subspt g1 g2
Proof
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
  fs[BAG_DISJOINT, DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem subspt_known_op_elist_globals:
   ∀c es as1 g0 al1 g1 opn as2 g2 a.
      known c es as1 g0 = (al1,g1) ∧ known_op opn as2 g1 = (a,g2) ∧ subspt g0 g2 ∧
      BAG_DISJOINT (op_gbag opn) (elist_globals es) ⇒
      subspt g0 g1 ∧ subspt g1 g2
Proof
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
  fs[BAG_DISJOINT, DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

(* fv_max *)

val fv_max_def = Define `fv_max n xs = !v. fv v xs ==> v < n`;

Theorem fv_alt:
   !n xs. fv n xs <=> has_var n (SND (free xs))
Proof
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
         \\ asm_exists_tac \\ simp [])
QED

Theorem fv1_alt:
   fv1 n x = has_var n (SND (free [x]))
Proof
  once_rewrite_tac [fv1_def] \\ metis_tac [fv_alt]
QED

Theorem fv_max_rw:
   (fv_max n [] <=> T) /\
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
   (fv_max n [Call tr ticks dest xs] <=> fv_max n xs)
Proof
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
    THEN1 (first_x_assum (qspec_then `v + 1` assume_tac) \\ fs []))
QED

Theorem fv_max_mk_Ticks[simp]:
   !t trc i e. fv_max n [mk_Ticks t trc i e] <=> fv_max n [e]
Proof
  Induct_on `i` \\ simp [mk_Ticks_alt, fv_max_rw]
QED

Theorem fv_max_cons:
   fv_max n (h::t) <=> fv_max n [h] /\ fv_max n t
Proof
  simp [fv_max_def] \\ eq_tac \\ rw [] \\ res_tac
QED

Theorem fv_max_append[simp]:
   !xs ys n. fv_max n (xs ++ ys) <=> fv_max n xs /\ fv_max n ys
Proof
  Induct \\ simp [fv_max_rw] \\ metis_tac [fv_max_cons]
QED

Theorem fv_max_less:
   !m n xs. fv_max m xs /\ m <= n ==> fv_max n xs
Proof
  simp [fv_max_def] \\ rw [] \\ res_tac \\ fs []
QED

Theorem known_op_correct_approx:
   !opn args g0 a g vs s0 v s.
   known_op opn args g0 = (a, g) /\ do_app opn vs s0 = Rval (v, s) /\
   LIST_REL val_approx_val args vs /\ state_globals_approx s0 g0 ==>
     state_globals_approx s g /\ val_approx_val a v
Proof
  rpt gen_tac
  \\ `?this_is_case. this_is_case opn` by (qexists_tac `K T` \\ fs [])
  \\ Cases_on `opn`
  \\ simp [known_op_def, do_app_def, case_eq_thms, va_case_eq, bool_case_eq,
           pair_case_eq]
  \\ rpt strip_tac \\ rveq \\ fs[]
  THEN1
   (fs [state_globals_approx_def] \\ res_tac \\ rfs [])
  THEN1
   (fs [state_globals_approx_def] \\ rw []
    \\ fs [lookup_insert, get_global_def, EL_LUPDATE]
    \\ fs [bool_case_eq] \\ rveq \\ fs []
    \\ metis_tac [])
  THEN1
   (fs [state_globals_approx_def] \\ rw []
    \\ fs [lookup_insert, get_global_def, EL_LUPDATE, bool_case_eq] \\ rveq \\ fs []
    THEN1 (first_x_assum (qspecl_then [`k`, `v`, `merge other a'`] assume_tac)
           \\ fs [] \\ metis_tac [val_approx_val_merge_I])
    THEN1 metis_tac [])
  THEN1
   (fs [state_globals_approx_def, get_global_def,
        EL_APPEND_EQN, bool_case_eq]
    \\ rw [] THEN1 (metis_tac [])
    \\ rename1 `nn - LENGTH (ss:('a,'b) closSem$state).globals`
    \\ `nn = LENGTH ss.globals` by simp [] \\ fs [])
  THEN1
   (rveq \\ fs [LIST_REL_EL_EQN])
  THEN1
   (fs [CaseEq"ffi_result"] \\ rveq
    \\ fs [state_globals_approx_def] \\ metis_tac [])
QED

Theorem ssgc_free_co_shift_seq:
   ssgc_free s ==> !k. ssgc_free (s with compile_oracle := shift_seq k s.compile_oracle)
Proof
  simp [PULL_FORALL] \\ gen_tac
  \\ simp [ssgc_free_def] \\ strip_tac \\ rpt conj_tac \\ fs []
  \\ rpt gen_tac \\ strip_tac \\ fs [shift_seq_def] \\ res_tac \\ simp []
QED

Theorem ssgc_free_do_install:
   !s. ssgc_free s ==>
   ssgc_free (s with <|compile_oracle := shift_seq 1 (s.compile_oracle);
                       code := s.code |++ SND (SND (s.compile_oracle 0))|>)
Proof
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
  THEN1 (simp [shift_seq_def] \\ rw [] \\ res_tac)
QED

Theorem do_install_ssgc:
   !vs s0 es s1. do_install vs s0 = (Rval es, s1) /\ ssgc_free s0 ==>
   ssgc_free s1 /\ EVERY esgc_free es /\ es ≠ [] /\
   s1.compile_oracle = shift_seq 1 s0.compile_oracle /\
   first_n_exps s0.compile_oracle 1 = [es] /\
   mglobals_extend s0.globals EMPTY s1.globals
Proof
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
   \\ res_tac \\ rfs []
QED

val value_ind =
  TypeBase.induction_of ``:closSem$v``
   |> Q.SPECL [`P`, `EVERY P`]
   |> SIMP_RULE (srw_ss()) []
   |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> Q.GEN `P`

Theorem do_app_ssgc:
   !opn args s0 res.
     do_app opn args s0 = res /\
     EVERY vsgc_free args /\ ssgc_free s0 ==>
     (!v s. res = Rval (v, s) ==>
            vsgc_free v /\ ssgc_free s /\
            s.compile_oracle = s0.compile_oracle /\
            mglobals_extend s0.globals (SET_OF_BAG (op_gbag opn)) s.globals) /\
     (!v. res = Rerr (Rraise v) ==> vsgc_free v)
Proof
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
    simp [] >> conj_tac
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
  >- (dsimp[ssgc_free_def, FLOOKUP_UPDATE, bool_case_eq] >>
      rpt strip_tac >> PURE_FULL_CASE_TAC >> fs [] >> rveq
      >- (first_x_assum match_mp_tac >> fs[FLOOKUP_UPDATE,bool_case_eq] >> metis_tac[])
      >- (fs[ssgc_free_def,FLOOKUP_UPDATE, bool_case_eq] >> metis_tac[])
      >- (first_x_assum match_mp_tac >> fs[])
      >- (first_x_assum match_mp_tac >> fs[] >> metis_tac[])
      >- (first_x_assum match_mp_tac >> fs[] >> metis_tac[]))
  >> dsimp[]
QED

Theorem dest_closure_Full_sgc_free:
   dest_closure max_app loc_opt f (arg0::args) =
     SOME (Full_app fbody env rest_args) /\
   vsgc_free f /\ vsgc_free arg0 /\ EVERY vsgc_free args ==>
   set_globals fbody = {||} /\ EVERY vsgc_free env /\ EVERY vsgc_free rest_args
Proof
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
   THEN1 (irule EVERY_DROP \\ simp [EVERY_REVERSE])
QED

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
          mglobals_extend s0.globals
            (SET_OF_BAG (elist_globals es) ∪
             SET_OF_BAG (elist_globals (FLAT (first_n_exps s0.compile_oracle n)))) s.globals) /\
   (!loc_opt f args (s0:('c,'ffi) closSem$state) res s.
      evaluate_app loc_opt f args s0 = (res, s) /\
      ssgc_free s0 /\ vsgc_free f /\ EVERY vsgc_free args ==>
        ssgc_free s /\ rsgc_free res /\
        ?n.
          s.compile_oracle = shift_seq n s0.compile_oracle /\
          mglobals_extend s0.globals
            (SET_OF_BAG (elist_globals (FLAT (first_n_exps s0.compile_oracle n)))) s.globals)`,
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
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0.globals g1 s1.globals`
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1.globals g2 s.globals`
    \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0.globals g3 s.globals`
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
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0.globals g1 s1.globals`
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1.globals g2 s.globals`
    \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0.globals g3 s.globals`
    \\ `g1 ∪ g2 ⊆ g3` suffices_by metis_tac [mglobals_extend_trans, mglobals_extend_SUBSET]
    \\ fs [elist_globals_append, SET_OF_BAG_UNION]
    \\ unabbrev_all_tac \\ rpt (pop_assum kall_tac)
    \\ metis_tac [UNION_ASSOC, UNION_COMM, SUBSET_UNION])
  THEN1
   (say "Let"
    \\ fs [evaluate_def, pair_case_eq, case_eq_thms]
    \\ rveq \\ fs []
    THEN1 (qexists_tac `n + n'` \\ simp [first_n_exps_shift_seq]
           \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0.globals g1 s1.globals`
           \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1.globals g2 s.globals`
           \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0.globals g3 s.globals`
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
           \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0.globals g1 s1.globals`
           \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1.globals g2 s.globals`
           \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0.globals g3 s.globals`
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
    THEN1 ( rveq \\ fs[] \\ qexists_tac`n` \\ simp[op_gbag_def] )
    (*
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
      \\ TRY (rename1 `evaluate (exps, [], _) = (Rval vals, _)`
              \\ `vals ≠ []` by metis_tac [NOT_NIL_EQ_LENGTH_NOT_0, evaluate_IMP_LENGTH]
              \\ simp [EVERY_LAST])
      \\ qexists_tac `n' + (1 + n)`
      \\ simp [first_n_exps_shift_seq]
      \\ rename1 `do_install _ _ = (_, s2)`
      \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0.globals g1 s1.globals`
      \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1.globals g2 s2.globals`
      \\ qmatch_asmsub_abbrev_tac `mglobals_extend s2.globals g3 s.globals`
      \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0.globals g4 s.globals`
      \\ rfs []
      \\ `g1 ∪ g2 ∪ g3 ⊆ g4` suffices_by metis_tac [mglobals_extend_trans, mglobals_extend_SUBSET]
      \\ unabbrev_all_tac
      \\ rpt (pop_assum kall_tac)
      \\ fs [elist_globals_append, SET_OF_BAG_UNION]
      \\ metis_tac [UNION_ASSOC, UNION_COMM, SUBSET_UNION])
    *)
    \\ reverse (fs [result_case_eq, pair_case_eq]) \\ rveq \\ fs []
    \\ drule do_app_ssgc \\ fs [EVERY_REVERSE]
    \\ strip_tac \\ rveq \\ fs []
    THEN1 (rename1 `do_app _ _ _ = Rerr err`
           \\ Cases_on `err` \\ simp []
           \\ qexists_tac `n` \\ fs [SET_OF_BAG_UNION]
           \\ metis_tac [mglobals_extend_SUBSET, UNION_ASSOC, SUBSET_UNION])
    \\ qexists_tac `n` \\ simp []
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0.globals g1 s1.globals`
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1.globals g2 s.globals`
    \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0.globals g3 s.globals`
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
           \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0.globals g1 s1.globals`
           \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1.globals g2 s.globals`
           \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0.globals g3 s.globals`
           \\ `g3 = g1 ∪ g2` suffices_by metis_tac [mglobals_extend_trans]
           \\ unabbrev_all_tac
           \\ simp [elist_globals_append, SET_OF_BAG_UNION]
           \\ metis_tac [UNION_ASSOC, UNION_COMM])
    \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
    \\ qexists_tac `(n'' + n) + n'` \\ simp [first_n_exps_shift_seq]
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0.globals g1 s1.globals`
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1.globals g2 s2.globals`
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s2.globals g3 s.globals`
    \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0.globals g4 s.globals`
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
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0.globals g1 s1.globals`
    \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1.globals g2 s.globals`
    \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0.globals g3 s.globals`
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
           \\ qmatch_asmsub_abbrev_tac `mglobals_extend s0.globals g1 s1.globals`
           \\ qmatch_asmsub_abbrev_tac `mglobals_extend s1.globals g2 s.globals`
           \\ qmatch_goalsub_abbrev_tac `mglobals_extend s0.globals g3 s.globals`
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

Theorem mk_Ticks_set_globals[simp]:
   !t tc n exp. set_globals (mk_Ticks t tc n exp) = set_globals exp
Proof
  Induct_on `n` \\ simp [mk_Ticks_alt]
QED

val gapprox_disjoint_def = Define `
  gapprox_disjoint g xs <=> DISJOINT (domain g) (SET_OF_BAG (elist_globals xs))`;

Theorem gapprox_disjoint_rw:
  (gapprox_disjoint g (x::y::xs) <=>
     gapprox_disjoint g [x] /\ gapprox_disjoint g (y::xs)) /\
  (gapprox_disjoint g [Op tr opn xs] <=>
     gapprox_disjoint g xs /\ DISJOINT (domain g) (SET_OF_BAG (op_gbag opn)))
Proof
 simp [gapprox_disjoint_def, SET_OF_BAG_UNION, DISJOINT_SYM, AC CONJ_ASSOC CONJ_COMM]
QED

val oracle_gapprox_disjoint_def = Define `
  oracle_gapprox_disjoint g co <=> !n. gapprox_disjoint g (FST (SND (co n)))`;

Theorem oracle_gapprox_disjoint_shift_seq:
   oracle_gapprox_disjoint g co ==>
   !k. oracle_gapprox_disjoint g (shift_seq k co)
Proof
  fs [oracle_gapprox_disjoint_def, shift_seq_def]
QED

Theorem oracle_gapprox_disjoint_evaluate:
   !g s0 es env res s1.
     oracle_gapprox_disjoint g s0.compile_oracle /\
     evaluate (es, env, s0) = (res, s1) ==>
     oracle_gapprox_disjoint g s1.compile_oracle
Proof
  rw [] \\ imp_res_tac evaluate_code \\ simp [oracle_gapprox_disjoint_shift_seq]
QED

Theorem oracle_gapprox_disjoint_first_n_exps:
   !g co. oracle_gapprox_disjoint g co <=>
     !n. gapprox_disjoint g (FLAT (first_n_exps co n))
Proof
  rpt gen_tac
  \\ simp [first_n_exps_def, oracle_gapprox_disjoint_def, gapprox_disjoint_def]
  \\ eq_tac
  THEN1
   (strip_tac
    \\ Induct \\ simp []
    \\ simp [GENLIST, SNOC_APPEND, elist_globals_append,
             SET_OF_BAG_UNION]
    \\ simp [DISJOINT_SYM])
  \\ rw []
  \\ pop_assum (qspec_then `SUC n` assume_tac)
  \\ fs [GENLIST, SNOC_APPEND, elist_globals_append, SET_OF_BAG_UNION, DISJOINT_SYM]
QED

Theorem mk_Ticks_esgc_free[simp]:
   !t tc n exp. esgc_free (mk_Ticks t tc n exp) <=> esgc_free exp
Proof
  Induct_on `n` \\ fs [mk_Ticks_alt]
QED

Theorem known_op_preserves_esgc_free:
   !opn args g0 a g.
     known_op opn args g0 = (a, g) /\
     EVERY val_approx_sgc_free args /\
     globals_approx_sgc_free g0 ==>
     val_approx_sgc_free a /\ globals_approx_sgc_free g
Proof
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
         \\ fs [EVERY_EL])
QED

Theorem elist_globals_empty:
   !es. elist_globals es = {||} <=>
        !e. MEM e es ==> set_globals e = {||}
Proof
  Induct \\ fs [] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
QED

Theorem clos_gen_noinline_val_approx_sgc_free:
   !n i fns. EVERY val_approx_sgc_free (clos_gen_noinline n i fns)
Proof
  ho_match_mp_tac clos_gen_noinline_ind
  \\ rw [] \\ fs [clos_gen_noinline_def]
QED

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

Theorem decide_inline_LetInline_IMP_Clos:
   !c fapx lopt arity body.
     decide_inline c fapx lopt arity = inlD_LetInline body ==>
       ?m s. fapx = Clos m arity body s
Proof
  rpt strip_tac
  \\ Cases_on `fapx` \\ fs [decide_inline_def, bool_case_eq]
QED

Theorem decide_inline_LetInline_IMP_Clos_lopt:
   !c fapx lopt arity body.
     decide_inline c fapx lopt arity = inlD_LetInline body ==>
       ?m s. fapx = Clos m arity body s /\
             (lopt = NONE \/ lopt = SOME m)
Proof
  rpt strip_tac
  \\ Cases_on `fapx` \\ fs [decide_inline_def, bool_case_eq]
QED

Theorem known_preserves_esgc_free_0:
   !c es aenv g0 eas1 g.
     known c es aenv g0 = (eas1, g) /\
     EVERY esgc_free es /\
     EVERY val_approx_sgc_free aenv /\
     globals_approx_sgc_free g0 ==>
     elist_globals (MAP FST eas1) ≤ elist_globals es /\
     EVERY esgc_free (MAP FST eas1) /\
     EVERY val_approx_sgc_free (MAP SND eas1) /\
     globals_approx_sgc_free g
Proof
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
         \\ fs[clos_gen_noinline_val_approx_sgc_free]
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
         \\ first_x_assum drule \\ fs [])
QED

Theorem known_preserves_esgc_free:
   !c es aenv g0 eas1 g.
     known c es aenv g0 = (eas1, g) /\
     EVERY esgc_free es /\
     EVERY val_approx_sgc_free aenv /\
     globals_approx_sgc_free g0 ==>
     EVERY esgc_free (MAP FST eas1) /\
     EVERY val_approx_sgc_free (MAP SND eas1) /\
     globals_approx_sgc_free g
Proof
  rpt gen_tac \\ rpt (disch_then strip_assume_tac)
  \\ metis_tac [known_preserves_esgc_free_0]
QED

Theorem known_elglobals_dont_grow:
   !c es aenv g0 eas1 g.
     known c es aenv g0 = (eas1, g) /\
     EVERY esgc_free es /\
     EVERY val_approx_sgc_free aenv /\
     globals_approx_sgc_free g0 ==>
     elist_globals (MAP FST eas1) ≤ elist_globals es
Proof
  rpt gen_tac \\ rpt (disch_then strip_assume_tac)
  \\ metis_tac [known_preserves_esgc_free_0]
QED

Theorem known_preserves_pure:
   !c es aenv g0 eas1 g.
     known c es aenv g0 = (eas1, g) /\
     EVERY pure es ==>
     EVERY pure (MAP FST eas1)
Proof
  ho_match_mp_tac known_ind
  \\ simp [known_def]
  \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ imp_res_tac known_sing_EQ_E
  \\ fs [] \\ rveq
  \\ fs [closLangTheory.pure_def]
  \\ every_case_tac
  \\ fs [closLangTheory.pure_def, closLangTheory.pure_op_def, ETA_THM]
QED

Theorem evaluate_mk_Ticks_rw:
   !t tc n exp env (s:('c,'ffi) closSem$state).
     evaluate ([mk_Ticks t tc n exp], env, s) =
     if s.clock < n then (Rerr (Rabort Rtimeout_error), s with clock := 0)
     else evaluate ([exp], env, dec_clock n s)
Proof
  Induct_on `n`
  THEN1 simp [mk_Ticks_alt, dec_clock_def]
  \\ rw []
  \\ fs [mk_Ticks_alt, evaluate_def, dec_clock_def, ADD1]
  \\ IF_CASES_TAC \\ simp [state_component_equality]
QED

Theorem evaluate_mk_Ticks_IMP:
   !t tc n exp env (s0:('c,'ffi) closSem$state) res s.
     evaluate ([mk_Ticks t tc n exp], env, s0) = (res, s) ==>
     (res = Rerr (Rabort Rtimeout_error) /\ s = s0 with clock := 0) \/
     (evaluate ([exp], env, dec_clock n s0) = (res, s))
Proof
  Induct_on `n` \\ rpt strip_tac
  THEN1 (fs [mk_Ticks_alt, dec_clock_def])
  \\ fs [mk_Ticks_alt] \\ res_tac
  \\ fs [evaluate_def]
  \\ fs [bool_case_eq, dec_clock_def, ADD1, state_component_equality]
QED

Theorem clos_gen_noinline_eq:
   !n c fns.
  clos_gen_noinline n c fns =
  GENLIST (λi. ClosNoInline (2 * (i+c) + n) (FST (EL i fns))) (LENGTH fns)
Proof
  Induct_on`fns`>>fs[FORALL_PROD,clos_gen_noinline_def,GENLIST_CONS]>>rw[]>>
  simp[o_DEF,ADD1]
QED

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

Theorem every_var_mk_Union[simp]:
   every_var P (mk_Union d1 d2) <=> every_var P d1 /\ every_var P d2
Proof
  simp [mk_Union_def] \\ rpt (IF_CASES_TAC \\ simp [every_var_def])
QED


Theorem decide_inline_LetInline_IMP_Clos_fv_max:
   !c fapx lopt arity body.
     decide_inline c fapx lopt arity = inlD_LetInline body ==>
       ?m s. fapx = Clos m arity body s /\
             fv_max arity [body]
Proof
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
  \\ simp []
QED

Theorem known_preserves_fv_max:
   !c es aenv g0 eas1 g n.
     known c es aenv g0 = (eas1, g) /\
     fv_max n es ==>
     fv_max n (MAP FST eas1)
Proof
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
    \\ qspec_then`MAP FST ea2`(fn th => rw[th])(Q.GEN`t`fv_max_cons)
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
    \\ first_x_assum drule \\ simp [])
QED

(* oracle_gapprox_subspt *)
val oracle_gapprox_subspt_def = Define `
  oracle_gapprox_subspt co <=>
    !n. subspt (FST (FST (co n))) (FST (FST (co (SUC n))))
`;

Theorem oracle_gapprox_subspt_add:
   oracle_gapprox_subspt co <=>
     !(n:num) k. subspt (FST (FST (co n))) (FST (FST (co (n + k))))
Proof
  eq_tac \\ rw []
  THEN1
   (Induct_on `k`
    \\ fs [oracle_gapprox_subspt_def]
    \\ first_x_assum (qspec_then `k + n` assume_tac)
    \\ fs [ADD1, AC ADD_ASSOC ADD_COMM]
    \\ metis_tac [subspt_trans])
  \\ rw [oracle_gapprox_subspt_def]
  \\ first_x_assum (qspecl_then [`n`, `1`] mp_tac)
  \\ simp [ADD1]
QED

Theorem oracle_gapprox_subspt_alt:
   !co n k. oracle_gapprox_subspt co /\ n <= k ==>
     subspt (FST (FST (co n))) (FST (FST (co k)))
Proof
  rw [oracle_gapprox_subspt_add]
  \\ imp_res_tac LESS_EQ_ADD_EXISTS \\ rveq \\ simp []
QED

Theorem oracle_gapprox_subspt_shift_seq:
   oracle_gapprox_subspt co ==> !k. oracle_gapprox_subspt (shift_seq k co)
Proof
  rw [] \\ simp [oracle_gapprox_subspt_def, shift_seq_def]
  \\ fs [oracle_gapprox_subspt_alt]
QED

Theorem oracle_gapprox_subspt_evaluate:
   !s0 xs env s0 res s.
     oracle_gapprox_subspt s0.compile_oracle /\
     closSem$evaluate (xs, env, s0) = (res, s) ==>
     oracle_gapprox_subspt s.compile_oracle
Proof
  rw [] \\ imp_res_tac evaluate_code \\ simp [oracle_gapprox_subspt_shift_seq]
QED

(* oracle_state_sgc_free *)
val oracle_state_sgc_free_def = Define `
  oracle_state_sgc_free co = !n. globals_approx_sgc_free (FST (FST (co n)))`;

Theorem oracle_state_sgc_free_shift_seq:
   !co. oracle_state_sgc_free co ==> !n. oracle_state_sgc_free (shift_seq n co)
Proof
  rpt strip_tac \\ fs [oracle_state_sgc_free_def, shift_seq_def]
QED

val next_g_def = Define `
  next_g (s:(val_approx num_map#'c,'ffi) closSem$state) =
    FST (FST (s.compile_oracle 0n))`;

(**)

val mglobals_disjoint_def = Define `
  mglobals_disjoint s xs <=> DISJOINT (mapped_globals s) (SET_OF_BAG (elist_globals xs))`;

Theorem mglobals_disjoint_rw:
  (mglobals_disjoint s (x::y::xs) <=>
     mglobals_disjoint s [x] /\ mglobals_disjoint s (y::xs)) /\
  (mglobals_disjoint s [Let tr xs x] <=>
     mglobals_disjoint s xs /\ mglobals_disjoint s [x]) /\
  (mglobals_disjoint s [Handle tr x1 x2] <=>
     mglobals_disjoint s [x1] /\ mglobals_disjoint s [x2]) /\
  (mglobals_disjoint s [If tr x1 x2 x3] <=>
     mglobals_disjoint s [x1] /\ mglobals_disjoint s [x2] /\ mglobals_disjoint s [x3]) /\
  (mglobals_disjoint s [Raise tr x] <=>
     mglobals_disjoint s [x]) /\
  (mglobals_disjoint s [Tick tr x] <=>
     mglobals_disjoint s [x]) /\
  (mglobals_disjoint s [Call tr ticks dest xs] <=>
     mglobals_disjoint s xs) /\
  (mglobals_disjoint s [Op tr opn xs] <=>
     mglobals_disjoint s xs /\ DISJOINT (mapped_globals s) (SET_OF_BAG (op_gbag opn))) /\
  (mglobals_disjoint s [App tr lopt x1 xs] <=>
     mglobals_disjoint s [x1] /\ mglobals_disjoint s xs) /\
  (mglobals_disjoint s [Letrec tr lopt vs fns x1] <=>
     mglobals_disjoint s (MAP SND fns) /\ mglobals_disjoint s [x1])
Proof
 simp [mglobals_disjoint_def, SET_OF_BAG_UNION, DISJOINT_SYM, AC CONJ_ASSOC CONJ_COMM]
QED

(**)

Theorem known_changed_globals_cases:
   !c xs aenv g0 alist g.
     known c xs aenv g0 = (alist,g) ==>
     !k a. lookup k g = SOME a ==> lookup k g0 = SOME a \/ k ∈ SET_OF_BAG (elist_globals xs)
Proof
  rw [] \\ drule known_changed_globals \\ strip_tac
  \\ fs [domain_lookup, PULL_EXISTS] \\ metis_tac []
QED

Theorem known_op_changed_globals_cases:
   !opn aenv g0 ea g.
     known_op opn aenv g0 = (ea,g) ==>
     !k a. lookup k g = SOME a ==> lookup k g0 = SOME a \/ k ∈ SET_OF_BAG (op_gbag opn)
Proof
  rw [] \\ drule known_op_changed_globals \\ strip_tac
  \\ fs [domain_lookup, PULL_EXISTS] \\ metis_tac []
QED


Theorem state_globals_approx_known_mglobals_disjoint:
   !c xs aenv g0 eas g s.
   known c xs aenv g0 = (eas, g) /\
   mglobals_disjoint s.globals xs /\
   state_globals_approx s g0 ==>
   state_globals_approx s g
Proof
   rw [] \\ simp [state_globals_approx_def] \\ rw []
   \\ drule known_changed_globals_cases
   \\ disch_then drule \\ strip_tac
   THEN1 metis_tac [state_globals_approx_def]
   \\ fs [mglobals_disjoint_def, mapped_globals_def, DISJOINT_ALT, PULL_EXISTS]
   \\ metis_tac []
QED

Theorem mglobals_disjoint_evaluate:
   !s0 xs ys env res s.
   evaluate (ys, env, s0) = (res, s) /\
   ssgc_free s0 /\ EVERY vsgc_free env /\ EVERY esgc_free ys /\
   unique_set_globals (xs ++ ys) s0.compile_oracle /\
   mglobals_disjoint s0.globals xs ==>
   mglobals_disjoint s.globals xs
Proof
  rw [mglobals_disjoint_def, mapped_globals_def, DISJOINT_ALT, PULL_EXISTS]
  \\ drule evaluate_changed_globals \\ simp [] \\ strip_tac
  \\ fs [mglobals_extend_def, mapped_globals_def]
  \\ first_x_assum drule \\ strip_tac
  \\ spose_not_then assume_tac
  \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION, elist_globals_append]
  \\ metis_tac [BAG_DISJOINT_BAG_IN]
QED


Theorem known_changed_globals_cases:
   !c xs aenv g0 alist g.
     known c xs aenv g0 = (alist,g) ==>
     !k a. lookup k g = SOME a ==> lookup k g0 = SOME a \/ k ∈ SET_OF_BAG (elist_globals xs)
Proof
  rw [] \\ drule known_changed_globals \\ strip_tac
  \\ fs [domain_lookup, PULL_EXISTS] \\ metis_tac []
QED

val gapprox_extend_def = Define `
  gapprox_extend g1 gd g2 <=>
    !i. i ∈ domain g2 ∧ (i ∈ domain g1 ==> lookup i g2 ≠ lookup i g1) ==>
        i ∈ gd`;

Theorem state_globals_approx_disjoint_extends:
   !s1 mgx s2 g1 gax g2.
     mglobals_extend s1.globals mgx s2.globals /\ gapprox_extend g1 gax g2 /\
     DISJOINT (mapped_globals s1.globals) gax /\ DISJOINT gax mgx /\
     state_globals_approx s2 g1 ==>
     state_globals_approx s2 g2
Proof
   rw [state_globals_approx_def]
   \\ fs [DISJOINT_ALT]
   \\ fs [mglobals_extend_def, gapprox_extend_def]
   \\ fs [mapped_globals_def, domain_lookup, PULL_EXISTS]
   \\ metis_tac []
QED

Theorem state_globals_approx_evaluate:
   !xs env s0 res s c ys aenv g0 eas g.
   evaluate (xs,env,s0) = (res, s) /\
   known c ys aenv g0 = (eas, g) /\
   ssgc_free s0 /\ EVERY vsgc_free env /\ EVERY esgc_free xs /\
   mglobals_disjoint s0.globals ys /\
   unique_set_globals (xs ++ ys) s0.compile_oracle /\
   state_globals_approx s g0 ==>
   state_globals_approx s g
Proof
   rw [state_globals_approx_def]
   \\ drule known_changed_globals_cases
   \\ disch_then drule \\ strip_tac
   THEN1 (metis_tac [state_globals_approx_def])
   \\ drule evaluate_changed_globals \\ simp [] \\ strip_tac
   \\ fs [mglobals_extend_def]
   \\ first_x_assum drule
   \\ impl_tac THEN1 (fs [unique_set_globals_def, elist_globals_append,
                          BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_BAG_IN]
                      \\ metis_tac [])
   \\ strip_tac
   \\ fs [mglobals_disjoint_def, DISJOINT_ALT, mapped_globals_def, PULL_EXISTS]
   \\ metis_tac []
QED

Theorem state_globals_approx_known_op_evaluate:
   evaluate (xs,env,s0) = (res, s) /\
   known_op opn aargs g0 = (ea, g) /\
   ssgc_free s0 /\ EVERY vsgc_free env /\ EVERY esgc_free xs /\
   DISJOINT (mapped_globals s0.globals) (SET_OF_BAG (op_gbag opn)) /\
   unique_set_globals [Op tr opn xs] s0.compile_oracle /\
   state_globals_approx s g0 ==>
   state_globals_approx s g
Proof
   rw [state_globals_approx_def]
   \\ drule known_op_changed_globals_cases
   \\ disch_then drule \\ strip_tac
   THEN1 (metis_tac [state_globals_approx_def])
   \\ drule evaluate_changed_globals \\ simp [] \\ strip_tac
   \\ fs [mglobals_extend_def]
   \\ first_x_assum drule
   \\ impl_tac THEN1 (fs [unique_set_globals_def, elist_globals_append,
                          BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_BAG_IN]
                      \\ metis_tac [])
   \\ strip_tac
   \\ fs [mglobals_disjoint_def, DISJOINT_ALT, mapped_globals_def, PULL_EXISTS]
   \\ metis_tac []
QED

Theorem elist_globals_first_n_exps_lemma:
   !i k co. i ⋲ elist_globals (FST (SND (co k))) ==>
         !n. k < n ==> i ⋲ elist_globals (FLAT (first_n_exps co n))
Proof
  rw []
  \\ `MEM (FST (SND (co k))) (first_n_exps co n)` by metis_tac [MEM_first_n_exps]
  \\ fs [MEM_SPLIT, elist_globals_append]
QED

Theorem elist_globals_first_n_exps_shift_seq_lemma:
   !i k co. i ⋲ elist_globals (FST (SND (co k))) ==>
         !m n. m < k /\ k < m + n ==> i ⋲ elist_globals (FLAT (first_n_exps (shift_seq m co) n))
Proof
  rw []
  \\ irule elist_globals_first_n_exps_lemma
  \\ simp [shift_seq_def]
  \\ qexists_tac `k - m` \\ simp []
QED

Theorem elist_globals_first_n_exps_exists:
   !i co n. i ⋲ elist_globals (FLAT (first_n_exps co n)) ==>
     ?k. k < n /\ i ⋲ elist_globals (FST (SND (co k)))
Proof
  Induct_on `n` THEN1 simp [first_n_exps_def]
  \\ rw [] \\ fs [ADD1, first_n_exps_shift_seq, elist_globals_append]
  THEN1 (fs [first_n_exps_def] \\ qexists_tac `0` \\ simp [])
  \\ res_tac \\ qexists_tac `k + 1` \\ fs [shift_seq_def]
QED

Theorem oracle_gapprox_disjoint_Install:
   !c co g0 eas g.
     known c (FST (SND (co 0))) [] g0 = (eas, g) /\
     unique_set_globals [] co /\
     oracle_gapprox_disjoint g0 co ==>
     oracle_gapprox_disjoint g (shift_seq 1 co)
Proof
   rw []
   \\ rw [oracle_gapprox_disjoint_def, gapprox_disjoint_def,
       DISJOINT_ALT, domain_lookup, PULL_EXISTS]
   \\ drule known_changed_globals_cases
   \\ disch_then drule \\ reverse strip_tac
   THEN1
    (rename1 `shift_seq 1 co nn`
     \\ spose_not_then (mp_then Any mp_tac elist_globals_first_n_exps_lemma)
     \\ simp [] \\ qexists_tac `nn + 1` \\ simp []
     \\ fs [unique_set_globals_def, first_n_exps_def]
     \\ first_x_assum (qspec_then `SUC (nn + 1)` assume_tac)
     \\ fs [GENLIST_CONS, BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_BAG_IN, elist_globals_append]
     \\ fs [o_DEF, shift_seq_def, ADD1]
     \\ metis_tac [])
   \\ fs [oracle_gapprox_disjoint_def, gapprox_disjoint_def, DISJOINT_ALT, domain_lookup, PULL_EXISTS]
   \\ res_tac \\ simp [shift_seq_def]
QED

Theorem oracle_gapprox_disjoint_shift_seq_unique_set_globals:
   !c xs aenv g0 eas g s0 k.
     known c xs aenv g0 = (eas, g) /\
     unique_set_globals xs s0.compile_oracle /\
     oracle_gapprox_disjoint g0 s0.compile_oracle ==>
     oracle_gapprox_disjoint g (shift_seq k s0.compile_oracle)
Proof
   rw []
   \\ rw [oracle_gapprox_disjoint_def, gapprox_disjoint_def,
       DISJOINT_ALT, domain_lookup, PULL_EXISTS]
   \\ drule known_changed_globals_cases
   \\ disch_then drule \\ reverse strip_tac
   THEN1
    (fs [unique_set_globals_def, elist_globals_append, BAG_ALL_DISTINCT_BAG_UNION]
     \\ fs [BAG_DISJOINT_BAG_IN]
     \\ simp [shift_seq_def]
     \\ spose_not_then assume_tac
     \\ drule elist_globals_first_n_exps_lemma
     \\ disch_then (qspec_then `k + n + 1` mp_tac) \\ simp []
     \\ metis_tac [])
   \\ fs [oracle_gapprox_disjoint_def, gapprox_disjoint_def, DISJOINT_ALT, domain_lookup, PULL_EXISTS]
   \\ res_tac \\ simp [shift_seq_def]
QED

(* essentially a duplicate of the above  *)
Theorem oracle_gapprox_disjoint_lemma:
   !xs env s0 res s c aenv g0 eas g.
     evaluate (xs,env,s0) = (res,s) /\
     known c xs aenv g0 = (eas, g) /\
     unique_set_globals xs s0.compile_oracle /\
     oracle_gapprox_disjoint g0 s0.compile_oracle ==>
     oracle_gapprox_disjoint g s.compile_oracle
Proof
   rw [] \\ imp_res_tac evaluate_IMP_shift_seq
   \\ metis_tac [oracle_gapprox_disjoint_shift_seq_unique_set_globals]
QED

val say = say0 "known_correct_approx";

Theorem known_correct_approx:
   !c xs aenv g0 eas g env extra s0:((val_approx num_map#'c,'ffi) closSem$state) res s.
   known c xs aenv g0 = (eas, g) /\
   evaluate (xs, env ++ extra, s0) = (res, s) /\
   (*fv_max (LENGTH env) xs /\*)
   unique_set_globals xs s0.compile_oracle /\
   LIST_REL val_approx_val aenv env /\
   state_globals_approx s0 g0 /\
   mglobals_disjoint s0.globals xs /\
   oracle_gapprox_disjoint g0 s0.compile_oracle /\
   ssgc_free s0 /\ EVERY vsgc_free (env ++ extra) /\ EVERY esgc_free xs /\
   EVERY val_approx_sgc_free aenv /\ globals_approx_sgc_free g0
   ==>
     state_globals_approx s g /\
     !vs. res = Rval vs ==> LIST_REL val_approx_val (MAP SND eas) vs
Proof
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
    \\ drule oracle_gapprox_disjoint_lemma
    \\ rpt (disch_then drule \\ simp []) \\ strip_tac
    \\ fs [fv_max_rw, mglobals_disjoint_rw]
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp []) \\ strip_tac
    \\ reverse (fs [result_case_eq]) \\ rveq \\ fs []
    THEN1
     (irule state_globals_approx_evaluate
      \\ rpt (goal_assum drule \\ simp []))
    \\ fs [pair_case_eq]
    \\ patresolve `unique_set_globals (_::_) _` hd unique_set_globals_evaluate
    \\ disch_then drule \\ simp [] \\ strip_tac
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ patresolve `known _ [_] _ _ = _` (el 1) known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ rename1 `evaluate ([_], _, _) = (_, s1)`
    \\ `ssgc_free s1`
       by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
           \\ rpt (disch_then drule \\ simp []))
    \\ simp []
    \\ imp_res_tac oracle_gapprox_disjoint_evaluate
    \\ impl_tac
    THEN1
     (match_mp_tac mglobals_disjoint_evaluate
      \\ rpt (goal_assum drule) \\ simp []
      \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION,
             elist_globals_append, BAG_DISJOINT_SYM])
    \\ strip_tac
    \\ imp_res_tac known_sing_EQ_E
    \\ fs [result_case_eq] \\ rveq \\ fs [])
  THEN1
   (say "Var"
    \\ fs [evaluate_def, bool_case_eq] \\ rveq
    \\ fs [any_el_ALT] \\ fs [fv_max_rw, EL_APPEND1, LIST_REL_EL_EQN]
    \\ rw[EL_APPEND1])
  THEN1
   (say "If"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ rename1 `known _ [x1] _ g0 = ([(e1,a1)], g1)`
    \\ rename1 `known _ [x2] _ g1 = ([(e2,a2)], g2)`
    \\ rename1 `known _ [x3] _ g2 = ([(e3,a3)], g)`
    \\ fs [evaluate_def, pair_case_eq]
    \\ fs [fv_max_rw, mglobals_disjoint_rw]
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp []) \\ strip_tac
    \\ reverse (fs [result_case_eq]) \\ rveq \\ fs []
    THEN1
     (irule state_globals_approx_evaluate
      \\ `?eaunused. known c [x2; x3] aenv g1 = (eaunused, g)` by simp [known_def]
      \\ rpt (goal_assum drule \\ simp [])
      \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION]
      \\ simp [mglobals_disjoint_rw])
    \\ rename1 `evaluate (_, _, s0) = (_, s1)`
    \\ `ssgc_free s1`
       by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
           \\ rpt (disch_then drule \\ simp []))
    \\ patresolve `known _ _ _ g0 = _` (el 1) known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ patresolve `known _ _ _ g1 = _` (el 1) known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ reverse (fs [bool_case_eq]) \\ fixeqs \\ rveq
    THEN1
     (irule state_globals_approx_known_mglobals_disjoint
      \\ `?eaunused. known c [x2; x3] aenv g1 = (eaunused, g)` by simp [known_def]
      \\ rpt (goal_assum drule \\ simp [])
      \\ irule mglobals_disjoint_evaluate
      \\ goal_assum (qpat_x_assum `evaluate _ = _` o mp_then Any mp_tac)
      \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM]
      \\ simp [mglobals_disjoint_rw])
    THEN1
     (first_x_assum drule \\ rpt (disch_then drule \\ simp [])
      \\ `unique_set_globals [x3] s1.compile_oracle`
         by (irule unique_set_globals_evaluate \\ goal_assum drule
             \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION])
      \\ `mglobals_disjoint s1.globals [x3]`
         by (match_mp_tac mglobals_disjoint_evaluate
             \\ rpt (goal_assum drule) \\ simp []
             \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
      \\ `state_globals_approx s1 g2`
         by (match_mp_tac state_globals_approx_evaluate
             \\ rpt (goal_assum drule \\ simp [])
             \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION])
      \\ `oracle_gapprox_disjoint g2 s1.compile_oracle`
         by (imp_res_tac evaluate_IMP_shift_seq \\ simp []
             \\ irule oracle_gapprox_disjoint_shift_seq_unique_set_globals
             \\ `?eaunused. known c [x1; x2] aenv g0 = (eaunused, g2)` by simp [known_def]
             \\ rpt (goal_assum drule \\ simp [])
             \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION])
      \\ simp [] \\ strip_tac
      \\ Cases_on `res` \\ fs []
      \\ metis_tac [val_approx_val_merge_I])
    THEN1
     (first_x_assum drule \\ rpt (disch_then drule \\ simp [])
      \\ `unique_set_globals [x2] s1.compile_oracle`
         by (irule unique_set_globals_evaluate \\ goal_assum drule
             \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION])
      \\ `mglobals_disjoint s1.globals [x2]`
         by (match_mp_tac mglobals_disjoint_evaluate
             \\ rpt (goal_assum drule) \\ simp []
             \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
      \\ `oracle_gapprox_disjoint g1 s1.compile_oracle`
         by (imp_res_tac evaluate_IMP_shift_seq \\ simp []
             \\ irule oracle_gapprox_disjoint_shift_seq_unique_set_globals
             \\ `?eaunused. known c [x1; x2] aenv g0 = (eaunused, g2)` by simp [known_def]
             \\ rpt (goal_assum drule \\ simp []))
      \\ simp [] \\ strip_tac
      \\ reverse conj_tac
      THEN1 (Cases_on `res` \\ fs [] \\ metis_tac [val_approx_val_merge_I])
      \\ match_mp_tac state_globals_approx_evaluate
      \\ rpt (goal_assum drule \\ simp [])
      \\ `mglobals_disjoint s1.globals [x3]`
         by (match_mp_tac mglobals_disjoint_evaluate
             \\ rpt (goal_assum drule) \\ simp []
             \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
      \\ `unique_set_globals [x2; x3] s1.compile_oracle`
         by (irule unique_set_globals_evaluate \\ goal_assum drule
             \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION])
      \\ simp []))
  THEN1
   (say "Let"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ rename1 `known _ xs _ g0 = (ea1, g1)`
    \\ rename1 `known _ [x2] _ g1 = ([(e2,a2)], g)`
    \\ imp_res_tac unique_set_globals_subexps
    \\ fs[mglobals_disjoint_rw, fv_max_rw]
    \\ reverse(fs[evaluate_def, result_case_eq, pair_case_eq]) \\ rveq
    >- (
      first_x_assum drule \\ fs[]
      \\ strip_tac
      \\ irule state_globals_approx_known_mglobals_disjoint
      \\ asm_exists_tac \\ rw[]
      \\ irule mglobals_disjoint_evaluate
      \\ goal_assum(first_assum o mp_then (Pat`closSem$evaluate`) mp_tac)
      \\ fs[unique_set_globals_def,elist_globals_append] )
    \\ imp_res_tac evaluate_IMP_LENGTH
    \\ last_x_assum drule \\ fs[]
    \\ disch_then irule
    \\ last_assum(mp_then Any mp_tac evaluate_changed_globals)
    \\ fs[] \\ strip_tac
    \\ last_assum(mp_then (Pat`known`) mp_tac known_preserves_esgc_free)
    \\ fs[] \\ strip_tac
    \\ last_assum(mp_then (Pat`closSem$evaluate`) mp_tac oracle_gapprox_disjoint_lemma)
    \\ disch_then drule
    \\ fs[] \\ strip_tac
    \\ conj_tac
    >- (
      irule mglobals_disjoint_evaluate
      \\ goal_assum(first_assum o mp_then (Pat`closSem$evaluate`) mp_tac)
      \\ fs[unique_set_globals_def,elist_globals_append] )
    \\ first_x_assum drule \\ fs[]
    \\ strip_tac
    \\ conj_tac
    >- ( irule unique_set_globals_shift_seq \\ fs[] )
    \\ irule EVERY2_APPEND_suff \\ fs[])
  THEN1
   (say "Raise"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ fs [evaluate_def, pair_case_eq]
    \\ fs [fv_max_rw, mglobals_disjoint_rw]
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ fs [case_eq_thms] \\ rveq \\ fs [])
  THEN1
   (say "Tick"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ fs [evaluate_def, pair_case_eq]
    \\ fs [fv_max_rw, mglobals_disjoint_rw]
    \\ Cases_on `s0.clock = 0` \\ fs [] \\ rveq \\ fs []
    THEN1 metis_tac [state_globals_approx_known_mglobals_disjoint]
    \\ first_x_assum (qpat_assum `evaluate _ = _` o mp_then Any match_mp_tac)
    \\ fs [dec_clock_def, next_g_def, mglobals_disjoint_def])
  THEN1
   (say "Handle"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ rename1 `known limit [x1] _ g0 = ([(e1,a1)], g1)`
    \\ rename1 `known limit [x2] _ g1 = ([(e2,a2)], g)`
    \\ fs [evaluate_def, pair_case_eq]
    \\ imp_res_tac unique_set_globals_subexps
    \\ fs[mglobals_disjoint_rw, fv_max_rw]
    \\ reverse(fs[evaluate_def, result_case_eq, CaseEq"error_result"]) \\ rveq
    >- (
      first_x_assum drule \\ fs[]
      \\ strip_tac
      \\ irule state_globals_approx_known_mglobals_disjoint
      \\ asm_exists_tac \\ rw[]
      \\ irule mglobals_disjoint_evaluate
      \\ goal_assum(first_assum o mp_then (Pat`closSem$evaluate`) mp_tac)
      \\ fs[unique_set_globals_def,elist_globals_append]
      \\ fs[BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
    >- (
      first_x_assum drule \\ fs[]
      \\ strip_tac
      \\ `v::(env++extra) = (v::env ++ extra)` by fs[]
      \\ pop_assum SUBST_ALL_TAC
      \\ first_x_assum drule \\ fs[ADD1]
      \\ impl_tac
      >- (
        conj_tac
        >- (
          last_assum(mp_then (Pat`closSem$evaluate`)mp_tac unique_set_globals_evaluate)
          \\ disch_then drule \\ fs[] )
        \\ conj_tac
        >- (
          irule mglobals_disjoint_evaluate
          \\ goal_assum(first_assum o mp_then (Pat`closSem$evaluate`) mp_tac)
          \\ fs[unique_set_globals_def,elist_globals_append]
          \\ fs[BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
        \\ conj_tac
        >- (
          last_assum(mp_then (Pat`closSem$evaluate`)mp_tac oracle_gapprox_disjoint_lemma)
          \\ disch_then drule \\ fs[] )
        \\ last_assum(mp_then Any mp_tac evaluate_changed_globals)
        \\ fs[] \\ strip_tac
        \\ last_assum(mp_then (Pat`known`) mp_tac known_preserves_esgc_free)
        \\ fs[] )
      \\ rw[]
      \\ irule val_approx_val_merge_I \\ fs[] )
    \\ first_x_assum drule \\ fs[]
    \\ strip_tac \\ fs[] \\ rveq
    \\ conj_tac
    >- (
      drule state_globals_approx_evaluate
      \\ disch_then drule
      \\ disch_then irule
      \\ fs[unique_set_globals_def,elist_globals_append] )
    \\ irule val_approx_val_merge_I \\ fs[])
  THEN1
   (say "Call"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, pair_case_eq]
    \\ fs [fv_max_rw]
    \\ first_x_assum drule \\ fs[]
    \\ impl_tac >- fs[mglobals_disjoint_def]
    \\ strip_tac
    \\ reverse conj_tac
    >-(
      rw[]
      \\ fs[result_case_eq, option_case_eq, pair_case_eq, bool_case_eq]
      \\ rveq \\ fs[] \\ fixeqs
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ fs[LENGTH_EQ_NUM_compute])
    \\ fs[result_case_eq, option_case_eq, pair_case_eq, bool_case_eq]
    \\ rveq \\ fs[] \\ fixeqs
    \\ fs[mglobals_disjoint_rw]
    \\ rename1 `evaluate (_, _, s0) = (Rval vs, s1)`
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
    \\ last_assum(mp_then Any mp_tac oracle_gapprox_disjoint_lemma)
    \\ disch_then drule
    \\ fs[] \\ strip_tac
    \\ fs[oracle_gapprox_disjoint_def, gapprox_disjoint_def]
    \\ fs[state_globals_approx_def]
    \\ fs[mglobals_extend_def] \\ rw[]
    \\ first_assum drule
    \\ impl_tac
    >- (
      strip_tac
      \\ drule elist_globals_first_n_exps_exists
      \\ disch_then(qx_choose_then`m`strip_assume_tac)
      \\ fs[IN_DISJOINT, domain_lookup]
      \\ metis_tac[] )
    \\ metis_tac[])
  THEN1
   (say "Op"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ rename1 `known _ _ _ g0 = (ea1, g1)`
    \\ rename1 `[Op _ opn _]`
    \\ fs [evaluate_def, pair_case_eq]
    \\ rename1 `evaluate _ = (_, s1)`
    \\ fs [fv_max_rw, mglobals_disjoint_rw]
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ strip_tac
    \\ reverse (fs [result_case_eq]) \\ rveq \\ fs []
    THEN1
     (irule state_globals_approx_known_op_evaluate
      \\ rpt (goal_assum drule \\ simp []))
    \\ reverse (Cases_on `opn = Install`) \\ fs []
    THEN1
     (fs [result_case_eq, pair_case_eq] \\ rveq \\ fs []
      THEN1 (irule known_op_correct_approx
             \\ rpt (goal_assum drule \\ simp []))
      \\ irule state_globals_approx_known_op_evaluate
      \\ rpt (goal_assum drule \\ simp []))
    \\ fs [known_op_def] \\ rveq \\ fs []
    (*
    \\ reverse (fs [result_case_eq, pair_case_eq]) \\ rveq \\ fs []
    THEN1
     (fs [do_install_def, case_eq_thms] \\ rveq \\ fs []
      \\ pairarg_tac \\ fs []
      \\ fs [bool_case_eq, pair_case_eq, case_eq_thms] \\ rveq \\ fs [])
    \\ rename1 `do_install _ _ = (_, s2)`
    \\ `?n. s.compile_oracle = shift_seq n s1.compile_oracle /\
            mglobals_extend s1 (SET_OF_BAG (elist_globals (FLAT (first_n_exps s1.compile_oracle n)))) s`
       by (drule evaluate_changed_globals
           \\ drule do_install_ssgc
           \\ last_assum (mp_then (Pos hd) mp_tac evaluate_changed_globals)
           \\ simp [] \\ disch_then kall_tac \\ strip_tac \\ strip_tac
           \\ goal_assum drule
           \\ last_assum (mp_then (Pos hd) mp_tac mglobals_extend_trans)
           \\ disch_then drule
           \\ fs [first_n_exps_shift_seq, SET_OF_BAG_UNION, elist_globals_append])
    \\ `oracle_gapprox_disjoint g s1.compile_oracle`
       by (irule oracle_gapprox_disjoint_lemma
           \\ rpt (goal_assum drule \\ simp []))
    \\ pop_assum mp_tac \\ simp [oracle_gapprox_disjoint_first_n_exps]
    \\ rw [state_globals_approx_def]
    \\ first_x_assum (qspec_then `n` assume_tac)
    \\ fs [gapprox_disjoint_def, DISJOINT_ALT, domain_lookup, PULL_EXISTS]
    \\ pop_assum drule \\ strip_tac
    \\ fs [mglobals_extend_def]
    \\ first_x_assum drule \\ simp [] \\ strip_tac
    \\ metis_tac [state_globals_approx_def]*))
  THEN1
   (say "App"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ rename1 `known _ [x1] _ g1 = _`
    \\ fs [fv_max_rw, mglobals_disjoint_rw]
    \\ reverse (fs [inlD_case_eq])
    THEN1
     ((* inlD_LetInline *)
      Cases_on `pure x1` \\ fs []
      (* This solve both the pure and the non-pure case *)
      THEN
       (rpt (pairarg_tac \\ fs []) \\ rveq
        \\ rename1 `known _ [x1] _ g1 = (_, g)`
        \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
        \\ reverse (fs [evaluate_def, bool_case_eq, pair_case_eq]) \\ rveq
        THEN1 metis_tac [state_globals_approx_known_mglobals_disjoint]
        \\ first_x_assum drule \\ rpt (disch_then drule) \\ strip_tac
        \\ reverse (fs [result_case_eq]) \\ rveq \\ fs []
        THEN1
         (irule state_globals_approx_evaluate
          \\ rpt (goal_assum drule \\ simp [])
          \\ fs [unique_set_globals_def, elist_globals_append,
                 BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
        \\ fs [pair_case_eq]
        \\ `unique_set_globals [x1] s1.compile_oracle` by metis_tac [unique_set_globals_evaluate]
        \\ patresolve `evaluate (_, _, s0) = _` hd evaluate_changed_globals \\ simp [] \\ strip_tac
        \\ patresolve  `known _ _ _ g0 = _` hd known_preserves_esgc_free
        \\ simp [] \\ strip_tac
        \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
        \\ patresolve `evaluate (_, _, s0) = _` hd oracle_gapprox_disjoint_lemma
        \\ rpt (disch_then drule \\ simp []) \\ strip_tac
        \\ `mglobals_disjoint s1.globals [x1]`
           by (match_mp_tac mglobals_disjoint_evaluate
               \\ rpt (goal_assum drule) \\ simp []
               \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION,
                      elist_globals_append, BAG_DISJOINT_SYM])
        \\ simp [] \\ strip_tac
        \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
        \\ imp_res_tac decide_inline_LetInline_IMP_Clos_fv_max
        \\ rveq \\ fs [] \\ rveq \\ fs []
        \\ rename1 `evaluate (xs,_,s0) = (Rval vs, s1)`
        \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
        \\ `vs <> []` by simp [NOT_NIL_EQ_LENGTH_NOT_0]
        \\ fs [evaluate_app_rw]
        \\ fs [dest_closure_def, check_loc_def]
        \\ fs [case_eq_thms] \\ rveq \\ fs []
        \\ fs [bool_case_eq] \\ rveq \\ fs [next_g_def]
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
        \\ simp [mglobals_disjoint_def]
        \\ patresolve `evaluate (_, _, s1) = _` hd oracle_gapprox_disjoint_lemma
        \\ rpt (disch_then drule \\ simp [])))
    (* This solves the 2 non-inlining cases *)
    THEN
     (reverse (fs [evaluate_def, bool_case_eq, pair_case_eq]) \\ rveq
      THEN1 metis_tac [state_globals_approx_known_mglobals_disjoint]
      \\ first_x_assum drule \\ rpt (disch_then drule) \\ strip_tac
      \\ reverse (fs [result_case_eq]) \\ rveq \\ fs []
      THEN1
       (irule state_globals_approx_evaluate
        \\ rpt (goal_assum drule \\ simp [])
        \\ fs [unique_set_globals_def, elist_globals_append,
               BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
      \\ fs [pair_case_eq]
      \\ rename1 `evaluate (xs, _, s0) = (Rval args, s1)`
      \\ rename1 `evaluate ([x1], _, s1) = (_, s2)`
      \\ `unique_set_globals [x1] s1.compile_oracle`
         by metis_tac [unique_set_globals_evaluate]
      \\ patresolve `known _ _ _ g0 = _` (el 1) known_preserves_esgc_free
      \\ simp [] \\ strip_tac
      \\ `ssgc_free s1 /\ EVERY vsgc_free args`
         by (patresolve `ssgc_free _` (el 2) evaluate_changed_globals
             \\ rpt (disch_then drule \\ simp []))
      \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
      \\ patresolve `evaluate (_, _, s0) = _` hd oracle_gapprox_disjoint_lemma
      \\ rpt (disch_then drule \\ simp []) \\ strip_tac
      \\ `mglobals_disjoint s1.globals [x1]`
         by (match_mp_tac mglobals_disjoint_evaluate
             \\ rpt (goal_assum drule) \\ simp []
             \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION,
                    elist_globals_append, BAG_DISJOINT_SYM])
      \\ simp [] \\ strip_tac
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
      \\ `oracle_gapprox_disjoint g s2.compile_oracle`
         by (irule oracle_gapprox_disjoint_lemma
             \\ rpt (goal_assum drule \\ simp []))
      \\ pop_assum mp_tac \\ simp [oracle_gapprox_disjoint_first_n_exps]
      \\ rw [state_globals_approx_def]
      \\ first_x_assum (qspec_then `n` assume_tac)
      \\ fs [gapprox_disjoint_def, DISJOINT_ALT, domain_lookup, PULL_EXISTS]
      \\ pop_assum drule \\ strip_tac
      \\ fs [mglobals_extend_def]
      \\ first_x_assum drule \\ simp [] \\ strip_tac
      \\ metis_tac [state_globals_approx_def]))
  THEN1
   (say "Fn"
    \\ rpt (pairarg_tac \\ fs [])
    \\ drule known_unchanged_globals \\ simp [] \\ strip_tac
    \\ fs [evaluate_def, bool_case_eq] \\ rveq
    \\ Cases_on `loc_opt`
    \\ fs [case_eq_thms] \\ rveq
    \\ fs [clos_approx_def]
    \\ CASE_TAC \\ simp [])
  THEN1
   (say "Letrec"
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ fs [mglobals_disjoint_rw]
    \\ reverse (fs [evaluate_def, bool_case_eq]) \\ rveq
    THEN1 metis_tac [state_globals_approx_known_mglobals_disjoint]
    \\ fs [Once option_case_eq] \\ rveq \\ fs []
    THEN1 metis_tac [state_globals_approx_known_mglobals_disjoint]
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
    \\ fs [case_eq_thms] \\ rveq \\ simp [LIST_REL_GENLIST])
QED

(* code relation *)

val exp_rel_def = Define `
  exp_rel c aenv g' e1 e2 <=>
    ?g0 g apx k.
      subspt g g' /\
      EVERY val_approx_sgc_free aenv /\
      globals_approx_sgc_free g0 /\
      known (c with inline_factor := k) [e1] aenv g0 = ([(e2, apx)], g)`;

Theorem exp_rel_dec_inline_factor[simp]:
   exp_rel (dec_inline_factor c) aenv g e1 e2 <=> exp_rel c aenv g e1 e2
Proof
  simp [exp_rel_def, dec_inline_factor_def]
QED

(* value relation *)

val f_rel_def = Define `
  f_rel c aenv g (n1, e1) (n2, e2) <=>
     n1 = n2 /\ exp_rel c (REPLICATE n1 Other ++ aenv) g e1 e2`;

Theorem v1_size_append:
   !xs ys. closSem$v1_size (xs ++ ys) = v1_size xs + v1_size ys
Proof
  Induct \\ fs [closSemTheory.v_size_def]
QED

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
     in ?aenv env1a env1b args2 env2a env2b funs2.
       if env1 = env1a ++ env1b then
       EVERY (\(num_args, exp). fv_max (num_args + LENGTH funs1 + LENGTH env1a) [exp]) funs1 /\
       LIST_REL (v_rel c g) args1 args2 /\
       LIST_REL (v_rel c g) env1a env2a /\
       LIST_REL val_approx_val aenv env1a /\
       LIST_REL (f_rel c (clos ++ aenv) g) funs1 funs2 /\
       v = Recclosure loc_opt args2 (env2a ++ env2b) funs2 i else F)
  `
  (WF_REL_TAC `measure (v_size o FST o SND o SND)` \\ simp [v1_size_append, v_size_def]
   \\ rpt strip_tac \\ imp_res_tac v_size_lemma \\ simp []);

val v_rel_def = save_thm("v_rel_def[simp,compute]",
  v_rel_def |> SIMP_RULE (bool_ss ++ ETA_ss) []);

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

Theorem v_rel_app_NONE:
   v_rel_app c g v1 v2 NONE = v_rel c g v1 v2
Proof
  Cases_on `v1` \\ simp [v_rel_app_def] \\ metis_tac []
QED

Theorem exp_rel_upd_inline_factor:
   exp_rel (c with inline_factor := k) = exp_rel c
Proof
  simp [FUN_EQ_THM, exp_rel_def]
QED

Theorem f_rel_upd_inline_factor:
   f_rel (c with inline_factor := k) = f_rel c
Proof
  simp [FUN_EQ_THM, FORALL_PROD, f_rel_def, exp_rel_upd_inline_factor]
QED

Theorem v_rel_upd_inline_factor:
   !c. v_rel (c with inline_factor := k) = v_rel c
Proof
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
         \\ `env1a ++ env1b = env1a ++ env1b` by simp []
         \\ asm_exists_tac \\ fs []
         \\ `env2a ++ env2b = env2a ++ env2b` by simp []
         \\ goal_assum (pop_assum o mp_then Any mp_tac)
         \\ fs [LIST_REL_EL_EQN] \\ rw [] \\ metis_tac [MEM_EL])
QED

Theorem v_rel_Block[simp]:
   v_rel c g x (Block n ys) <=>
     ?xs. x = Block n xs /\ LIST_REL (v_rel c g) xs ys
Proof
  Cases_on `x` \\ fs [v_rel_def] \\ eq_tac \\ rw [] \\ metis_tac []
QED

Theorem v_rel_Boolv[simp]:
   (v_rel c g (Boolv b) v ⇔ v = Boolv b) ∧
   (v_rel c g v (Boolv b) ⇔ v = Boolv b)
Proof
  simp [closSemTheory.Boolv_def] >> Cases_on `v` >> simp[] >> metis_tac[]
QED

Theorem v_rel_Unit[simp]:
   (v_rel c g Unit v ⇔ v = Unit) ∧ (v_rel c g v Unit ⇔ v = Unit)
Proof
  simp[Unit_def] >> Cases_on `v` >> simp[] >> metis_tac[]
QED

val v_rel_IMP_v_to_bytes_lemma = prove(
  ``!x y c g.
      v_rel c g x y ==>
      !ns. (v_to_list x = SOME (MAP (Number o $& o (w2n:word8->num)) ns)) <=>
           (v_to_list y = SOME (MAP (Number o $& o (w2n:word8->num)) ns))``,
  ho_match_mp_tac v_to_list_ind \\ rw []
  \\ fs [v_to_list_def]
  \\ Cases_on `tag = backend_common$cons_tag` \\ fs []
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
  \\ Cases_on `tag = backend_common$cons_tag` \\ fs []
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

Theorem ref_rel_upd_inline_factor:
   ref_rel (c with inline_factor := k) = ref_rel c
Proof
  simp [FUN_EQ_THM, ref_rel_cases, v_rel_upd_inline_factor]
QED

val compile_inc_def = Define `
  compile_inc c g (es,xs) =
    let (eas, g') = known (reset_inline_factor c) es [] g in (g', MAP FST eas, xs)`;

val state_rel_def = Define `
  state_rel c g (s:(val_approx num_map#'c,'ffi) closSem$state) (t:('c,'ffi) closSem$state) <=>
    (!n. SND (SND (s.compile_oracle n)) = []) /\
    (!n. fv_max 0 (FST (SND (s.compile_oracle n)))) /\
    s.code = FEMPTY /\ t.code = FEMPTY /\
    s.clock = t.clock /\ s.ffi = t.ffi /\ s.max_app = t.max_app /\
    LIST_REL (OPTREL (v_rel c g)) s.globals t.globals /\
    fmap_rel (ref_rel c g) s.refs t.refs /\
    s.compile = state_cc (compile_inc c) t.compile  /\
    t.compile_oracle = state_co (compile_inc c) s.compile_oracle
`;

Theorem state_rel_upd_inline_factor:
   state_rel (c with inline_factor := k) = state_rel c
Proof
  simp [FUN_EQ_THM] \\ rw []
  \\ eq_tac \\ strip_tac \\ fs [state_rel_def]
  \\ fs [v_rel_upd_inline_factor, ref_rel_upd_inline_factor]
  \\ simp [state_cc_def, state_co_def, LAMBDA_PROD,
           compile_inc_def, reset_inline_factor_def]
QED

Theorem v_rel_subspt:
   !c g v1 v2 g'. v_rel c g v1 v2 ∧ subspt g g' ⇒ v_rel c g' v1 v2
Proof
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
      qexists_tac `env1a` >> simp[] >>
      qexists_tac `env2a` >> simp[] >>
      simp[] >> rpt conj_tac >>
      TRY (irule EVERY2_MEM_MONO >> imp_res_tac LIST_REL_LENGTH >>
           simp[FORALL_PROD, MEM_ZIP, PULL_EXISTS] >>
           qexists_tac `v_rel c g` >> simp[] >> metis_tac[MEM_EL]) >>
      qpat_x_assum `LIST_REL (f_rel _ _ _) _ _` mp_tac >> simp[LIST_REL_EL_EQN] >>
      rpt strip_tac >> fs[] >> rfs[] >> rpt (pairarg_tac >> fs[]) >>
      rename1 `nn < LENGTH _` >> first_x_assum (qspec_then `nn` mp_tac) >>
      rename1 `f_rel _ _ _ (EL nn fns1) (EL nn fns2)` >>
      Cases_on `EL nn fns1` >> Cases_on `EL nn fns2` >>
      simp[] >> simp[f_rel_def, exp_rel_def] >> metis_tac[subspt_trans])
QED

Theorem v_rel_LIST_REL_subspt:
   ∀vs1 vs2. LIST_REL (v_rel c g) vs1 vs2 ⇒
             ∀g'. subspt g g' ⇒ LIST_REL (v_rel c g') vs1 vs2
Proof
  Induct_on `LIST_REL` >> simp[] >> metis_tac[v_rel_subspt]
QED

Theorem ref_rel_subspt:
   !c g r1 r2 g'. ref_rel c g r1 r2 /\ subspt g g' ==> ref_rel c g' r1 r2
Proof
  Cases_on `r1` \\ rw [] \\ metis_tac [v_rel_LIST_REL_subspt]
QED

Theorem state_rel_subspt:
   !c g s1 s2 g'. state_rel c g s1 s2 /\ subspt g g' ==> state_rel c g' s1 s2
Proof
  rw [state_rel_def]
  THEN1 (irule LIST_REL_mono \\ metis_tac [OPTREL_MONO, v_rel_subspt])
  THEN1 (irule fmap_rel_mono \\ metis_tac [ref_rel_subspt])
QED

val co_every_Fn_vs_NONE_def = Define `
  co_every_Fn_vs_NONE co =
    !n exps aux. SND (co n) = (exps, aux) ==>
      every_Fn_vs_NONE exps /\
      every_Fn_vs_NONE (MAP (SND o SND) aux)
`;

Theorem co_every_Fn_vs_NONE_shift_seq:
   !co. co_every_Fn_vs_NONE co ==> !n. co_every_Fn_vs_NONE (shift_seq n co)
Proof
  rpt strip_tac \\ fs [co_every_Fn_vs_NONE_def, shift_seq_def] \\ metis_tac []
QED

Theorem state_rel_co_elist_globals:
   state_rel c g s t /\ ssgc_free s /\ oracle_state_sgc_free s.compile_oracle ==>
     elist_globals (FST (SND (t.compile_oracle n))) <= elist_globals (FST (SND (s.compile_oracle n)))
Proof
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
  \\ qpat_x_assum `!n e a. _` (qspec_then `nn` mp_tac) \\ simp []
QED

Theorem state_rel_first_n_exps:
   state_rel c g s t /\ ssgc_free s /\ oracle_state_sgc_free s.compile_oracle ==>
     elist_globals (FLAT (first_n_exps t.compile_oracle n)) <= elist_globals (FLAT (first_n_exps s.compile_oracle n))
Proof
  strip_tac
  \\ imp_res_tac state_rel_co_elist_globals
  \\ fs [first_n_exps_def] \\ Induct_on `n`
  \\ fs [GENLIST]
  \\ simp [SNOC_APPEND, elist_globals_append]
  \\ simp [SUB_BAG_UNION]
QED

Theorem state_rel_unique_set_globals:
   !xs. state_rel c g s t /\ ssgc_free s /\ oracle_state_sgc_free s.compile_oracle /\
   unique_set_globals xs s.compile_oracle ==> unique_set_globals xs t.compile_oracle
Proof
  rpt strip_tac
  \\ imp_res_tac state_rel_first_n_exps
  \\ fs [unique_set_globals_def]
  \\ fs [elist_globals_append, BAG_ALL_DISTINCT_BAG_UNION]
  \\ gen_tac
  \\ rpt (qpat_x_assum `!n. _` (qspec_then `n` assume_tac))
  \\ fs []
  \\ imp_res_tac SUB_BAG_DIFF_EQ \\ pop_assum (fn th => fs [Once th])
  \\ fs [BAG_ALL_DISTINCT_BAG_UNION]
QED

Theorem state_rel_get_global_IMP:
   !c g s t n v1. state_rel c g s t /\ get_global n s.globals = SOME (SOME v1) ==>
   ?v2. get_global n t.globals = SOME (SOME v2) /\ v_rel c g v1 v2
Proof
  rw [state_rel_def, get_global_def, LIST_REL_EL_EQN]
  \\ metis_tac [OPTREL_SOME]
QED

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

Theorem evaluate_app_exact_rw:
   args <> [] /\ num_args = LENGTH args
   ==>
   evaluate_app (SOME loc) (Closure (SOME loc) [] env num_args body) args s =
   if s.clock < LENGTH args then
     (Rerr (Rabort Rtimeout_error), s with clock := 0)
   else
     evaluate ([body], args ++ env, dec_clock num_args s)
Proof
  strip_tac
  \\ simp [evaluate_app_rw, dest_closure_def, check_loc_def]
  \\ fs [NOT_NIL_EQ_LENGTH_NOT_0]
  \\ IF_CASES_TAC \\ simp []
  \\ simp [TAKE_LENGTH_ID_rwt, LENGTH_REVERSE]
  \\ simp [DROP_LENGTH_TOO_LONG]
  \\ EVERY_CASE_TAC \\ simp []
QED

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

Theorem dest_closure_SOME_IMP:
   dest_closure max_app loc_opt f2 xs = SOME x ==>
    (?loc arg_env clo_env num_args e. f2 = Closure loc arg_env clo_env num_args e) \/
    (?loc arg_env clo_env fns i. f2 = Recclosure loc arg_env clo_env fns i)
Proof
  fs [dest_closure_def,case_eq_thms] \\ rw [] \\ fs []
QED

Theorem state_globals_approx_subspt:
   !g0 g s. subspt g0 g /\ state_globals_approx s g ==>
   state_globals_approx s g0
Proof
  rw [state_globals_approx_def] \\ res_tac
  \\ fs [subspt_def, domain_lookup]
QED

Theorem oracle_gapprox_disjoint_subspt:
   !g0 g co. subspt g0 g /\ oracle_gapprox_disjoint g co ==>
   oracle_gapprox_disjoint g0 co
Proof
  rw [oracle_gapprox_disjoint_def, gapprox_disjoint_def, DISJOINT_ALT]
  \\ fs [subspt_def, domain_lookup]
QED

Theorem decide_inline_inlD_LetInline_sgc_free:
   !c a lopt n body. decide_inline c a lopt n = inlD_LetInline body /\ val_approx_sgc_free a ==> set_globals body = {||}
Proof
  rw [] \\ fs [decide_inline_def, va_case_eq, bool_case_eq]
  \\ rveq \\ fs []
QED

Theorem known_op_subspt:
   !opn aargs g0 a g.
     known_op opn aargs g0 = (a, g) /\
     BAG_DISJOINT (BAG_OF_SET (domain g0)) (op_gbag opn) ==>
     BAG_OF_SET (domain g) ≤ BAG_OF_SET (domain g0) ⊎ op_gbag opn /\
     subspt g0 g
Proof
  Cases_on `opn` \\ fs [known_op_def]
  \\ rpt (gen_tac ORELSE disch_then strip_assume_tac)
  THEN1 fs [bool_case_eq, option_case_eq]
  THEN1
   (fs [list_case_eq, option_case_eq] \\ rveq
    \\ fs [BAG_DISJOINT, DISJOINT_ALT, domain_lookup, PULL_EXISTS]
    \\ fs [op_gbag_def]
    \\ reverse conj_tac
    THEN1 (rw [subspt_lookup, lookup_insert] \\ rw [] \\ fs [])
    \\ rw [SUB_BAG, BAG_INN, BAG_OF_SET]
    \\ Cases_on `x = n ∨ x ∈ domain g0` \\ fs [] \\ rveq
    \\ fs [BAG_UNION, BAG_INSERT, domain_lookup])
  THEN1 fs [list_case_eq, va_case_eq, bool_case_eq]
QED

Theorem known_subspt:
   !c xs aenv g0 eas g.
     known c xs aenv g0 = (eas, g) /\
     EVERY esgc_free xs /\ EVERY val_approx_sgc_free aenv /\ globals_approx_sgc_free g0 /\
     BAG_ALL_DISTINCT (BAG_OF_SET (domain g0) ⊎ elist_globals xs) ==>
     BAG_OF_SET (domain g) ≤ BAG_OF_SET (domain g0) ⊎ elist_globals xs /\
     subspt g0 g
Proof
  ho_match_mp_tac known_ind
  \\ rpt conj_tac \\ rpt (gen_tac ORELSE disch_then strip_assume_tac)
  \\ fs [known_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ fs [BAG_ALL_DISTINCT_BAG_UNION]
  THEN1
   (rename1 `known _ _ _ g0 = (_, g1)`
    \\ last_x_assum (mp_then (Pos hd) mp_tac known_preserves_esgc_free) \\ simp [] \\ strip_tac
    \\ patresolve `BAG_OF_SET (domain g1) ≤ _` hd BAG_DISJOINT_SUB_BAG \\ simp []
    \\ disch_then (qspec_then `elist_globals (y::xs)` mp_tac) \\ simp [] \\ strip_tac
    \\ fsrw_tac [bagLib.SBAG_SOLVE_ss] []
    \\ metis_tac [subspt_trans])
  THEN1
   (rename1 `known _ _ _ g0 = (_, g1)` \\ rename1 `known _ _ _ g1 = (_, g2)`
    \\ last_x_assum (mp_then (Pos hd) mp_tac known_preserves_esgc_free) \\ simp [] \\ strip_tac
    \\ last_x_assum (mp_then (Pos hd) mp_tac known_preserves_esgc_free) \\ simp [] \\ strip_tac
    \\ patresolve `BAG_OF_SET (domain g1) ≤ _` hd BAG_DISJOINT_SUB_BAG \\ simp []
    \\ disch_then (qspec_then `elist_globals [x2; x3]` mp_tac) \\ simp [] \\ strip_tac
    \\ fsrw_tac [bagLib.SBAG_SOLVE_ss] []
    \\ patresolve `BAG_OF_SET (domain g2) ≤ _` hd BAG_DISJOINT_SUB_BAG \\ simp []
    \\ disch_then (qspec_then `elist_globals [x3]` mp_tac) \\ simp [] \\ strip_tac
    \\ fsrw_tac [bagLib.SBAG_SOLVE_ss] []
    \\ metis_tac [subspt_trans])
  THEN1
   (rename1 `known _ _ _ g0 = (_, g1)`
    \\ last_x_assum (mp_then (Pos hd) mp_tac known_preserves_esgc_free) \\ simp [] \\ strip_tac
    \\ patresolve `BAG_OF_SET (domain g1) ≤ _` hd BAG_DISJOINT_SUB_BAG \\ simp []
    \\ disch_then (qspec_then `elist_globals [x2]` mp_tac) \\ simp [] \\ strip_tac
    \\ fsrw_tac [bagLib.SBAG_SOLVE_ss] [BAG_DISJOINT_SYM]
    \\ metis_tac [subspt_trans])
  THEN1
   (rename1 `known _ _ _ g0 = (_, g1)`
    \\ last_x_assum (mp_then (Pos hd) mp_tac known_preserves_esgc_free) \\ simp [] \\ strip_tac
    \\ patresolve `BAG_OF_SET (domain g1) ≤ _` hd BAG_DISJOINT_SUB_BAG \\ simp []
    \\ disch_then (qspec_then `elist_globals [x2]` mp_tac) \\ simp [] \\ strip_tac
    \\ fsrw_tac [bagLib.SBAG_SOLVE_ss] [BAG_DISJOINT_SYM]
    \\ metis_tac [subspt_trans])
  THEN1
   (rename1 `known _ _ _ g0 = (_, g1)`
    \\ patresolve `BAG_OF_SET (domain g1) ≤ _` hd BAG_DISJOINT_SUB_BAG \\ simp []
    \\ disch_then (qspec_then `op_gbag op` mp_tac) \\ fs [BAG_DISJOINT_SYM] \\ strip_tac
    \\ drule known_op_subspt \\ fs [BAG_DISJOINT_SYM] \\ strip_tac
    \\ fsrw_tac [bagLib.SBAG_SOLVE_ss] [BAG_DISJOINT_SYM]
    \\ metis_tac [subspt_trans])
  THEN1
   (rename1 `known _ _ _ g0 = (_, g1)` \\ rename1 `known _ _ _ g1 = (_, g2)`
    \\ last_x_assum (mp_then (Pos hd) mp_tac known_preserves_esgc_free) \\ simp [] \\ strip_tac
    \\ patresolve `BAG_OF_SET (domain g1) ≤ _` hd BAG_DISJOINT_SUB_BAG \\ simp []
    \\ disch_then (qspec_then `elist_globals [x]` mp_tac) \\ simp [] \\ strip_tac
    \\ fsrw_tac [bagLib.SBAG_SOLVE_ss] [BAG_DISJOINT_SYM]
    \\ fs [inlD_case_eq] \\ rveq
    \\ fsrw_tac [bagLib.SBAG_SOLVE_ss] [BAG_DISJOINT_SYM]
    THEN1 metis_tac [subspt_trans]
    THEN1 metis_tac [subspt_trans]
    \\ imp_res_tac known_sing_EQ_E \\ rveq \\ fs [] \\ rveq
    \\ last_x_assum (mp_then (Pos hd) mp_tac known_preserves_esgc_free) \\ simp [] \\ strip_tac
    \\ drule decide_inline_inlD_LetInline_sgc_free \\ simp [] \\ strip_tac
    \\ imp_res_tac set_globals_empty_esgc_free
    \\ rpt (pairarg_tac \\ fs [])
    \\ fs [bool_case_eq]
    \\ fsrw_tac [bagLib.SBAG_SOLVE_ss] []
    \\ metis_tac [subspt_trans])
  THEN1
   (imp_res_tac set_globals_empty_esgc_free
    \\ fs [EVERY_REPLICATE])
  THEN1
   (last_x_assum irule \\ CASE_TAC
    THEN1 simp [EVERY_REPLICATE]
    \\ simp [clos_gen_noinline_eq, EVERY_GENLIST])
QED


(* Set globals in all future installs is disjoint from currently mapped globals. *)
val state_oracle_mglobals_disjoint_def = Define `
  state_oracle_mglobals_disjoint s <=> !n. mglobals_disjoint s.globals (FST (SND (s.compile_oracle n)))`;

Theorem state_oracle_mglobals_disjoint_evaluate_suff:
   !xs env s0 res s. evaluate (xs, env, s0) = (res, s) /\
   ssgc_free s0 /\ EVERY esgc_free xs /\ EVERY vsgc_free env /\
   unique_set_globals xs s0.compile_oracle /\
   mglobals_disjoint s0.globals xs /\
   state_oracle_mglobals_disjoint s0 ==>
   state_oracle_mglobals_disjoint s
Proof
  rw [state_oracle_mglobals_disjoint_def, mglobals_disjoint_def, DISJOINT_ALT]
  \\ drule evaluate_changed_globals \\ simp [] \\ strip_tac
  \\ fs [mglobals_extend_def]
  \\ imp_res_tac SUBSET_THM
  \\ fs [IN_DEF]
  THEN1 (fs [DISJOINT_ALT, IN_DEF, shift_seq_def])
  THEN1 (fs [unique_set_globals_def, elist_globals_append, BAG_ALL_DISTINCT_BAG_UNION]
         \\ fs [BAG_DISJOINT, DISJOINT_ALT, shift_seq_def, PULL_FORALL]
         \\ spose_not_then (mp_then (Pos hd) mp_tac elist_globals_first_n_exps_lemma)
         \\ simp [] \\ rename1 `nn1 + nn2` \\ qexists_tac `nn1 + nn2 + 1` \\ simp [])
  THEN1 (
    fs [unique_set_globals_def, elist_globals_append, BAG_ALL_DISTINCT_BAG_UNION]
    \\ CCONTR_TAC \\ fs[]
    \\ drule elist_globals_first_n_exps_lemma
    \\ disch_then(qspec_then`n+1`mp_tac)
    \\ impl_tac >- rw[]
    \\ qmatch_assum_rename_tac`x <: elist_globals (FLAT (first_n_exps _ m))`
    \\ qmatch_assum_abbrev_tac`x <: elist_globals (FLAT (first_n_exps co m))`
    \\ last_x_assum(qspec_then`(n+1)+m`mp_tac)
    \\ simp[first_n_exps_shift_seq, elist_globals_append, BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_BAG_IN]
    \\ rw[] \\ metis_tac[])
QED

val say = say0 "known_correct0";

val known_correct0 = Q.prove(
  `(!xs env1full (s0:(val_approx num_map#'c,'ffi) closSem$state) res1 s env1 xenv1
     env2 xenv2 t0 c g0 g aenv eas.
      evaluate (xs, env1full, s0) = (res1, s) /\
      known c xs aenv g0 = (eas, g) /\
      state_rel c (next_g s0) s0 t0 /\
      every_Fn_vs_NONE xs /\
      co_every_Fn_vs_NONE s0.compile_oracle /\
      mglobals_disjoint s0.globals xs /\
      oracle_gapprox_disjoint (next_g s0) s0.compile_oracle /\
      state_oracle_mglobals_disjoint s0 /\
      EVERY esgc_free xs /\ ssgc_free s0 /\
      EVERY vsgc_free env1full /\
      LIST_REL val_approx_val aenv env1 /\
      oracle_state_sgc_free s0.compile_oracle /\
      globals_approx_sgc_free g0 /\
      EVERY val_approx_sgc_free aenv /\
      state_globals_approx s0 (next_g s0) /\
      subspt g0 g /\ subspt g (next_g s0) /\
      oracle_gapprox_subspt s0.compile_oracle /\
      fv_max (LENGTH env1) xs /\
      LIST_REL (v_rel c (next_g s0)) env1 env2 /\
      unique_set_globals xs s0.compile_oracle /\
      env1full = env1 ++ xenv1 /\
      res1 <> Rerr (Rabort Rtype_error) ==>
      ?res2 t.
        evaluate (MAP FST eas, env2 ++ xenv2, t0) = (res2, t) /\
        result_rel (LIST_REL (v_rel c (next_g s))) (v_rel c (next_g s)) res1 res2 /\
        state_rel c (next_g s) s t /\
        state_globals_approx s (next_g s) /\
        oracle_gapprox_disjoint (next_g s) s.compile_oracle) /\
   (!lopt1 f1 args1 (s0:(val_approx num_map#'c,'ffi) closSem$state) res1 s lopt2 f2 args2 t0 c argsopt.
      evaluate_app lopt1 f1 args1 s0 = (res1, s) /\
      v_rel_app c (next_g s0) f1 f2 argsopt /\
      oracle_gapprox_disjoint (next_g s0) s0.compile_oracle /\
      state_oracle_mglobals_disjoint s0 /\
      ssgc_free s0 /\ vsgc_free f1 /\ EVERY vsgc_free args1 /\
      oracle_state_sgc_free s0.compile_oracle /\
      co_every_Fn_vs_NONE s0.compile_oracle /\
      unique_set_globals [] s0.compile_oracle /\
      LIST_REL (v_rel c (next_g s0)) args1 args2 /\
      state_rel c (next_g s0) s0 t0 /\
      state_globals_approx s0 (next_g s0) /\
      oracle_gapprox_subspt s0.compile_oracle /\
      loptrel f2 (LENGTH args1) lopt1 lopt2 /\
      (IS_SOME argsopt ==> argsopt = SOME args1 /\ args1 <> [] /\ ?exp env. dest_closure s0.max_app lopt1 f1 args1 = SOME (Full_app exp env [])) /\
      res1 <> Rerr (Rabort Rtype_error) ==>
      ?res2 t.
        evaluate_app lopt2 f2 args2 t0 = (res2, t) /\
        result_rel (LIST_REL (v_rel c (next_g s))) (v_rel c (next_g s)) res1 res2 /\
        state_rel c (next_g s) s t /\
        state_globals_approx s (next_g s) /\
        oracle_gapprox_disjoint (next_g s) s.compile_oracle)`,
  ho_match_mp_tac (evaluate_ind |> Q.SPEC `\(x1,x2,x3). P0 x1 x2 x3`
                   |> Q.GEN `P0` |> SIMP_RULE std_ss [FORALL_PROD])
  \\ rpt strip_tac \\ fs [fv_max_rw, mglobals_disjoint_rw] \\ rveq
  THEN1
   (say "NIL"
    \\ fs [known_def, evaluate_def] \\ rveq
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ simp [])
  THEN1
   (say "CONS"
    \\ fs [known_def, evaluate_def, pair_case_eq]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ imp_res_tac unique_set_globals_subexps \\ fs []
    \\ rename1 `known _ [_] _ g0 = (_, g1)`
    \\ `subspt g0 g1 ∧ subspt g1 g`
       by (irule subspt_known_elist_globals
           \\ simp [] \\ rpt (goal_assum drule)
           \\ fs [unique_set_globals_def,
                  elist_globals_append, BAG_ALL_DISTINCT_BAG_UNION])
    \\ `subspt g1 (next_g s0)` by metis_tac [subspt_trans]
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ disch_then (qspec_then `xenv2` mp_tac)
    \\ reverse (fs [result_case_eq]) \\ rveq \\ fs []
    THEN1 (strip_tac \\ simp [evaluate_append])
    \\ strip_tac \\ simp [evaluate_append]
    \\ patresolve `evaluate ([_], _, _) = _` hd evaluate_changed_globals
    \\ simp [] \\ strip_tac \\ fs []
    \\ fs [unique_set_globals_shift_seq,
           co_every_Fn_vs_NONE_shift_seq,
           oracle_state_sgc_free_shift_seq]
    \\ patresolve `known _ [_] _ _ = _` hd known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ fs [pair_case_eq]
    (* mglobals_disjoint s1 (y::xs) *)
    \\ patresolve `evaluate ([_], _, _) = _` hd mglobals_disjoint_evaluate
    \\ simp [] \\ disch_then (first_x_assum o mp_then Any mp_tac)
    \\ impl_tac THEN1 (fs [unique_set_globals_def, elist_globals_append, AC ASSOC_BAG_UNION COMM_BAG_UNION])
    \\ strip_tac
    (**)
    \\ `subspt (next_g s0) (next_g s1)`
       by (simp [next_g_def, shift_seq_def, oracle_gapprox_subspt_alt])
    \\ `subspt g (next_g s1)` by metis_tac [subspt_trans]
    \\ `state_oracle_mglobals_disjoint s1`
       by (match_mp_tac state_oracle_mglobals_disjoint_evaluate_suff
           \\ goal_assum drule \\ simp [])
    \\ `oracle_gapprox_subspt s1.compile_oracle`
       by (simp [oracle_gapprox_subspt_shift_seq])
    \\ rfs []
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ disch_then (qspecl_then [`env2`, `xenv2`] mp_tac)
    \\ impl_tac THEN1 (conj_tac THEN1 metis_tac [v_rel_LIST_REL_subspt]
                       \\ fs [result_case_eq])
    \\ fs [result_case_eq] \\ rveq \\ fs []
    \\ strip_tac \\ fs [] \\ rveq
    \\ imp_res_tac known_sing_EQ_E \\ rveq \\ fs []
    \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
    \\ `subspt (next_g s1) (next_g s)`
       by (imp_res_tac evaluate_IMP_shift_seq
           \\ simp [next_g_def, shift_seq_def, oracle_gapprox_subspt_alt])
    \\ metis_tac [v_rel_subspt])
  THEN1
   (say "Var"
    \\ fs [known_def] \\ rveq \\ fs []
    \\ fs [evaluate_def] \\ rveq
    \\ imp_res_tac LIST_REL_LENGTH
    \\ fs [any_el_ALT, LIST_REL_EL_EQN, EL_APPEND1])
  THEN1
   (say "If"
    \\ fs [known_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ rename1 `known _ [x1] _ g0 = (_, g1)`
    \\ rename1 `known _ [x2] _ g1 = (eas2, g2)`
    \\ rename1 `known _ [x3] _ g2 = (eas3, g)`
    \\ patresolve `subspt g0 g` (el 3) subspt_known_elist_globals
    \\ disch_then drule
    \\ disch_then (qspecl_then [`[x2;x3]`, `aenv`] mp_tac)
    \\ simp [known_def]
    \\ impl_tac THEN1 (imp_res_tac unique_set_globals_IMP_es_distinct_elist_globals
                       \\ fs [BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
    \\ strip_tac
    \\ `subspt g1 (next_g s0)` by metis_tac [subspt_trans]
    \\ fs [evaluate_def, pair_case_eq]
    \\ imp_res_tac known_sing_EQ_E
    \\ imp_res_tac unique_set_globals_subexps
    \\ first_x_assum drule \\ simp []
    \\ rpt (disch_then drule \\ simp [])
    \\ disch_then (qspec_then `xenv2` mp_tac)
    \\ fs [result_case_eq]
    \\ strip_tac \\ rveq \\ fs []
    \\ `subspt g1 g2 /\ subspt g2 g`
       by (irule subspt_known_elist_globals
           \\ simp [] \\ rpt (goal_assum drule)
           \\ fs [unique_set_globals_def,
                  elist_globals_append, BAG_ALL_DISTINCT_BAG_UNION])
    \\ patresolve `evaluate ([x1], _, _) = _` hd evaluate_changed_globals
    \\ simp [] \\ strip_tac
    \\ imp_res_tac evaluate_SING \\ rveq
    \\ qpat_assum (`known _ _ _ g0 = _`) (mp_then Any mp_tac known_preserves_esgc_free)
    \\ simp [] \\ strip_tac
    \\ qpat_assum (`known _ _ _ g1 = _`) (mp_then Any mp_tac known_preserves_esgc_free)
    \\ simp [] \\ strip_tac
    \\ `state_oracle_mglobals_disjoint s1`
       by (irule state_oracle_mglobals_disjoint_evaluate_suff
           \\ goal_assum (first_assum o mp_then (Pat `closSem$evaluate`) mp_tac)
           \\ simp [])
    \\ `subspt (next_g s0) (next_g s1)`
       by simp [next_g_def, shift_seq_def, oracle_gapprox_subspt_alt]
    \\ fs [bool_case_eq] \\ rveq \\ fs []
    THEN
     (fixeqs
      \\ first_x_assum drule
      \\ rpt (disch_then drule \\ simp [])
      \\ simp [co_every_Fn_vs_NONE_shift_seq,
               oracle_state_sgc_free_shift_seq,
               oracle_gapprox_subspt_shift_seq,
               unique_set_globals_shift_seq]
      \\ rename1 `evaluate ([x_taken_branch], _, s1)`
      \\ patresolve `evaluate ([x1], _, _) = _` hd mglobals_disjoint_evaluate
      \\ disch_then (qspec_then `[x_taken_branch]` mp_tac)
      \\ simp []
      \\ impl_tac
      THEN1 (fs [unique_set_globals_def, elist_globals_append,
                 BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
      \\ strip_tac
      \\ simp []
      \\ disch_then (first_assum o mp_then (Pat `LIST_REL`) mp_tac)
      \\ simp []
      \\ disch_then (qspecl_then [`env2`, `xenv2`] mp_tac)
      \\ impl_tac
      THEN1 metis_tac [subspt_trans, v_rel_LIST_REL_subspt]
      \\ strip_tac \\ fs []))
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
           \\ fs [next_g_def, shift_seq_def, oracle_gapprox_subspt_alt])
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ disch_then (qspec_then `xenv2` mp_tac)
    \\ fs [result_case_eq] \\ rveq \\ strip_tac \\ fs [] \\ rveq \\ simp [PULL_EXISTS]
    \\ imp_res_tac known_sing_EQ_E \\ fs [] \\ rveq
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ patresolve `evaluate (xs, _, _) = _` hd evaluate_changed_globals
    \\ simp [] \\ strip_tac \\ fs []
    \\ fs [unique_set_globals_shift_seq,
           co_every_Fn_vs_NONE_shift_seq,
           oracle_state_sgc_free_shift_seq,
           oracle_gapprox_subspt_shift_seq]
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ patresolve `known _ xs _ _ = _` hd known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ patresolve `evaluate (xs, _, _) = _` (el 2) known_correct_approx
    \\ rpt (disch_then drule \\ simp [])
    \\ impl_tac THEN1 metis_tac [state_globals_approx_subspt, oracle_gapprox_disjoint_subspt]
    \\ strip_tac \\ rveq \\ fs []
    \\ `subspt g (next_g s1)` by metis_tac [subspt_trans]
    \\ simp [] \\ disch_then match_mp_tac
    \\ qexists_tac `vs ++ env1`
    \\ qexists_tac `xenv1`
    \\ `state_oracle_mglobals_disjoint s1`
       by (match_mp_tac state_oracle_mglobals_disjoint_evaluate_suff
           \\ goal_assum drule \\ simp [])
    \\ `mglobals_disjoint s1.globals [x2]`
       by (match_mp_tac mglobals_disjoint_evaluate
           \\ goal_assum drule
           \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION, elist_globals_append])
    \\ simp []
    \\ metis_tac [EVERY2_APPEND_suff, v_rel_LIST_REL_subspt])
  THEN1
   (say "Raise"
    \\ fs [known_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, pair_case_eq, result_case_eq]
    \\ rveq \\ fs []
    \\ imp_res_tac unique_set_globals_subexps
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ disch_then (qspec_then `xenv2` strip_assume_tac)
    \\ imp_res_tac known_sing_EQ_E \\ rveq \\ fs [] \\ rveq
    \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
    \\ imp_res_tac evaluate_SING \\ rveq \\ fs [])
  THEN1
   (say "Handle"
    \\ fs [known_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ rename1 `known _ [x1] _ g0 = (_, g1)`
    \\ fs [evaluate_def, pair_case_eq]
    \\ rename1 `evaluate ([x1], _, s0) = (_, s1)`
    \\ imp_res_tac unique_set_globals_subexps \\ fs []
    \\ patresolve `subspt g0 g` (el 3) subspt_known_elist_globals
    \\ rpt (disch_then drule)
    \\ impl_tac THEN1 (imp_res_tac unique_set_globals_IMP_es_distinct_elist_globals
                       \\ fs [BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
    \\ strip_tac
    \\ `subspt (next_g s0) (next_g s1)`
       by (fs [result_case_eq] \\ rveq
           \\ imp_res_tac evaluate_IMP_shift_seq
           \\ fs [next_g_def, shift_seq_def, oracle_gapprox_subspt_alt])
    \\ `subspt g1 (next_g s0) /\ subspt g (next_g s1)` by metis_tac [subspt_trans]
    \\ imp_res_tac known_sing_EQ_E \\ rveq \\ fs [] \\ rveq
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ disch_then (qspec_then `xenv2` mp_tac)
    \\ fs [case_eq_thms] \\ rw [] \\ fs [] \\ rw []
    \\ first_x_assum drule
    \\ rpt (disch_then drule \\ simp [])
    \\ patresolve `evaluate ([x1], _, _) = _` hd evaluate_changed_globals
    \\ simp [] \\ strip_tac \\ fs []
    \\ fs [unique_set_globals_shift_seq,
           co_every_Fn_vs_NONE_shift_seq,
           oracle_state_sgc_free_shift_seq,
           oracle_gapprox_subspt_shift_seq]
    \\ simp [PULL_EXISTS]
    \\ disch_then match_mp_tac \\ simp []
    \\ `env1 ⧺ xenv1 = env1 ⧺ xenv1` by simp []
    \\ goal_assum (pop_assum o mp_then Any mp_tac)
    \\ simp [ADD1]
    \\ `state_oracle_mglobals_disjoint s1`
        by (match_mp_tac state_oracle_mglobals_disjoint_evaluate_suff
            \\ goal_assum drule \\ simp [])
    \\ `mglobals_disjoint s1.globals [x2]`
        by (match_mp_tac mglobals_disjoint_evaluate
            \\ goal_assum drule
            \\ fs [unique_set_globals_def, BAG_ALL_DISTINCT_BAG_UNION,
                   elist_globals_append, BAG_DISJOINT_SYM])
    \\ patresolve `known _ [x1] _ _ = _` hd known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ metis_tac [v_rel_LIST_REL_subspt])
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
    \\ disch_then (qspec_then `xenv2` mp_tac)
    \\ reverse (fs [result_case_eq]) \\ rveq \\ fs []
    THEN1 (strip_tac \\ rveq \\ fs []
           \\ Cases_on `opn` \\ simp [isGlobal_def, evaluate_def]
           \\ Cases_on `apx` \\ simp [gO_destApx_def] \\ rveq
           \\ fs [known_op_def, NULL_EQ, bool_case_eq] \\ rveq
           \\ fs [evaluate_def])
    \\ rename1 `evaluate (_, _, s0) = (_, s1)`
    \\ strip_tac
    \\ `state_oracle_mglobals_disjoint s1`
       by (match_mp_tac state_oracle_mglobals_disjoint_evaluate_suff
           \\ goal_assum drule \\ simp [])
    \\ Cases_on `opn = Install` \\ fs []
    (*
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
      \\ rename1 `s1.compile_oracle 0 = (_, exps1, aux1)`
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
             \\ rpt (pairarg_tac \\ fs []) \\ rw []
             \\ imp_res_tac known_LENGTH_EQ_E
             \\ rfs [NOT_NIL_EQ_LENGTH_NOT_0])
      \\ fs [] \\ rveq
      \\ `t.clock = s1.clock` by fs [state_rel_def]
      \\ fs []
      \\ Cases_on `s1.clock = 0` \\ fs []
      THEN1
       (fs [result_case_eq] \\ rveq \\ fs []
        \\ conj_asm1_tac
        THEN1
         (fs [state_rel_def, shift_seq_def, next_g_def]
          \\ simp [FUPDATE_LIST, FUN_EQ_THM, state_co_def]
          \\ conj_tac
          THEN1 (irule LIST_REL_mono
                 \\ qexists_tac `OPTREL (v_rel c (FST cfg))` \\ rw []
                 \\ irule OPTREL_MONO
                 \\ qexists_tac `v_rel c (FST cfg)` \\ rw []
                 \\ irule v_rel_subspt
                 \\ qexists_tac `FST cfg` \\ simp []
                 \\ imp_res_tac evaluate_IMP_shift_seq
                 \\ fs [shift_seq_def]
                 \\ rename1 `s0.compile_oracle kk1 = (cfg, _, _)`
                 \\ drule oracle_gapprox_subspt_alt
                 \\ disch_then (qspec_then `kk1` mp_tac)
                 \\ simp [])
          \\ irule fmap_rel_mono
          \\ goal_assum (first_assum o mp_then Any mp_tac) \\ rw[]
          \\ irule ref_rel_subspt
          \\ goal_assum (first_assum o mp_then Any mp_tac) \\ rw[]
          \\ fs[state_cc_def]
          \\ pairarg_tac \\ fs[]
          \\ pairarg_tac \\ fs[]
          \\ fs[CaseEq"option",CaseEq"prod"] \\ rw[]
          \\ qpat_assum`_ = FST (s1.compile_oracle 1)`(assume_tac o SYM) \\ fs[]
          \\ fs[compile_inc_def]
          \\ pairarg_tac \\ fs[] \\ rveq
          \\ drule known_subspt
          \\ qpat_x_assum`_ = (_,s1)`assume_tac
          \\ drule evaluate_changed_globals
          \\ fs[]
          \\ strip_tac
          \\ fs[shift_seq_def]
          \\ fs[oracle_state_sgc_free_def]
          \\ qpat_assum`∀n. globals_approx_sgc_free _`(qspec_then`n+1`mp_tac)
          \\ qpat_x_assum`∀n. globals_approx_sgc_free _`(qspec_then`n`mp_tac)
          \\ simp[globals_approx_sgc_free_def]
          \\ fs[ssgc_free_def]
          \\ first_x_assum(qspec_then`0`mp_tac)
          \\ simp[]
          \\ fs[oracle_gapprox_disjoint_def]
          \\ qpat_x_assum`∀n. gapprox_disjoint _ _`(qspec_then`0`mp_tac)
          \\ simp[gapprox_disjoint_def]
          \\ srw_tac[DNF_ss][]
          \\ first_x_assum match_mp_tac
          \\ conj_tac >- metis_tac[]
          \\ simp[BAG_ALL_DISTINCT_BAG_UNION]
          \\ imp_res_tac unique_set_globals_shift_seq
          \\ pop_assum kall_tac
          \\ pop_assum(qspec_then`n`mp_tac)
          \\ simp[unique_set_globals_def,elist_globals_append,BAG_ALL_DISTINCT_BAG_UNION,shift_seq_def]
          \\ simp[first_n_exps_def]
          \\ disch_then(qspec_then`1`mp_tac)
          \\ simp[] \\ strip_tac
          \\ simp[BAG_DISJOINT_BAG_IN]
          \\ fs[IN_DISJOINT])
        \\ conj_tac
        THEN1
         (irule state_globals_approx_known_mglobals_disjoint
          \\ fs [state_rel_def, state_co_def, LAMBDA_PROD, compile_inc_def, shift_seq_def]
          \\ rfs [] \\ rpt (pairarg_tac \\ fs []) \\ rw []
          \\ fs [next_g_def, shift_seq_def]
          \\ rename1 `s1.compile_oracle 0 = ((pre_install_g, _), _, _)`
          \\ fs [state_cc_def, compile_inc_def]
          \\ rpt (pairarg_tac \\ fs []) \\ rw []
          \\ goal_assum drule \\ simp []
          \\ fs [state_oracle_mglobals_disjoint_def]
          \\ metis_tac [SND, FST])
        THEN1
         (match_mp_tac oracle_gapprox_disjoint_Install
          \\ fs [state_rel_def, state_co_def, LAMBDA_PROD, compile_inc_def, shift_seq_def]
          \\ rfs [] \\ rpt (pairarg_tac \\ fs []) \\ rw []
          \\ fs [next_g_def, shift_seq_def]
          \\ rename1 `s1.compile_oracle 0 = ((pre_install_g, _), eval_exp, _)`
          \\ fs [state_cc_def, compile_inc_def]
          \\ rpt (pairarg_tac \\ fs []) \\ rw []
          \\ goal_assum drule \\ simp []
          \\ metis_tac [nil_unique_set_globals, unique_set_globals_evaluate]))
      \\ rveq \\ fs []
      \\ `?gg eas. r0 = MAP FST eas /\
                   known (reset_inline_factor c) exps1 [] (next_g s1) =
                     (eas, next_g (s1 with compile_oracle := shift_seq 1 s1.compile_oracle))`
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
      \\ qmatch_goalsub_abbrev_tac `evaluate (_, [], tgoal)`
      \\ fs [pair_case_eq]
      \\ first_x_assum drule
      \\ disch_then drule
      \\ simp [reset_inline_factor_def, v_rel_upd_inline_factor, state_rel_upd_inline_factor]
      \\ disch_then (qspecl_then [`[]`, `tgoal`] mp_tac)
      \\ reverse impl_tac
      THEN1
       (fs [result_case_eq] \\ strip_tac \\ rw [] \\ fs []
        \\ irule LIST_REL_IMP_LAST \\ simp []
        \\ metis_tac [LIST_REL_LENGTH, evaluate_IMP_LENGTH, NOT_NIL_EQ_LENGTH_NOT_0])
      \\ patresolve `evaluate (_, _, s0) = _` hd evaluate_IMP_shift_seq
      \\ strip_tac \\ fs []
      \\ rename1 `s1.compile_oracle = shift_seq kk s0.compile_oracle`
      \\ simp [co_every_Fn_vs_NONE_shift_seq, oracle_state_sgc_free_shift_seq]
      \\ `every_Fn_vs_NONE exps1` by (fs [co_every_Fn_vs_NONE_def, shift_seq_def] \\ metis_tac [SND])
      \\ `EVERY esgc_free exps1` by (fs [ssgc_free_def, shift_seq_def, shift_seq_def] \\ metis_tac [SND])
      \\ `fv_max 0 exps1` by (fs [state_rel_def] \\ metis_tac [SND, FST])
      \\ simp [Abbr `tgoal`]
      \\ rpt conj_tac
      THEN1
       (fs [state_rel_def, shift_seq_def, next_g_def]
        \\ simp [FUPDATE_LIST, FUN_EQ_THM, state_co_def]
        \\ conj_tac
        THEN1 (irule LIST_REL_mono
               \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ rw []
               \\ irule OPTREL_MONO
               \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ rw []
               \\ irule v_rel_subspt
               \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ rw []
               \\ imp_res_tac evaluate_IMP_shift_seq
               \\ fs [shift_seq_def]
               \\ rename1 `s0.compile_oracle kk1 = (cfg, _, _)`
               \\ drule oracle_gapprox_subspt_alt
               \\ disch_then (qspec_then `kk1` mp_tac)
               \\ simp [])
        \\ irule fmap_rel_mono
        \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ rw []
        \\ irule ref_rel_subspt
        \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ rw []
        \\ fs[state_cc_def]
        \\ pairarg_tac \\ fs[]
        \\ pairarg_tac \\ fs[]
        \\ fs[CaseEq"option",CaseEq"prod"] \\ rw[]
        \\ qpat_assum`_ = FST (s0.compile_oracle _)`(assume_tac o SYM) \\ fs[]
        \\ fs[compile_inc_def]
        \\ pairarg_tac \\ fs[] \\ rveq
        \\ drule known_subspt
        \\ fs[ssgc_free_def]
        \\ fs[oracle_state_sgc_free_def]
        \\ qpat_x_assum`∀n. globals_approx_sgc_free _`(qspec_then`kk`mp_tac)
        \\ simp[]
        \\ fs[oracle_gapprox_disjoint_def]
        \\ qpat_x_assum`∀n. gapprox_disjoint _ _`(qspec_then`0`mp_tac)
        \\ simp[gapprox_disjoint_def]
        \\ srw_tac[DNF_ss][]
        \\ first_x_assum match_mp_tac
        \\ simp[BAG_ALL_DISTINCT_BAG_UNION]
        \\ imp_res_tac unique_set_globals_shift_seq
        \\ pop_assum kall_tac
        \\ pop_assum(qspec_then`kk`mp_tac)
        \\ simp[unique_set_globals_def,elist_globals_append,BAG_ALL_DISTINCT_BAG_UNION,shift_seq_def]
        \\ simp[first_n_exps_def]
        \\ disch_then(qspec_then`1`mp_tac)
        \\ simp[] \\ strip_tac
        \\ simp[BAG_DISJOINT_BAG_IN]
        \\ fs[IN_DISJOINT])
      THEN1
       (fs [state_oracle_mglobals_disjoint_def, mglobals_disjoint_def]
        \\ metis_tac [FST, SND])
      THEN1
       (qpat_assum `oracle_gapprox_disjoint (next_g s1) _`
                   (mp_then Any mp_tac oracle_gapprox_disjoint_Install)
        \\ simp [] \\ disch_then drule
        \\ simp [next_g_def] \\ disch_then irule
        \\ metis_tac [nil_unique_set_globals, unique_set_globals_shift_seq])
      THEN1
       (fs [state_oracle_mglobals_disjoint_def, mglobals_disjoint_def, shift_seq_def])
      THEN1
       (patresolve `evaluate (_, _, s0) = _` hd evaluate_changed_globals \\ simp []
        \\ strip_tac \\ fs [ssgc_free_def, shift_seq_def, FUPDATE_LIST] \\ metis_tac [])
      THEN1
       (`next_g s1 = FST (FST (s0.compile_oracle kk))` by fs [next_g_def, shift_seq_def]
        \\ fs [oracle_state_sgc_free_def])
      THEN1
       (patresolve `evaluate (_, _, s0) = _` (el 2) known_correct_approx
        \\ rpt (disch_then drule \\ simp [])
        \\ impl_tac THEN1 metis_tac [state_globals_approx_subspt, oracle_gapprox_disjoint_subspt]
        \\ simp [] \\ strip_tac
        \\ irule state_globals_approx_known_mglobals_disjoint
        \\ fs [next_g_def] \\ goal_assum drule \\ simp []
        \\ fs [state_oracle_mglobals_disjoint_def, mglobals_disjoint_def]
        \\ metis_tac [FST, SND])
      THEN1 simp [next_g_def, shift_seq_def, oracle_gapprox_subspt_alt]
      THEN1 simp [next_g_def, shift_seq_def, oracle_gapprox_subspt_alt]
      THEN1 simp [oracle_gapprox_subspt_shift_seq]
      THEN1
       (qpat_x_assum `unique_set_globals _ s0.compile_oracle` mp_tac
        \\ `exps1 = FST (SND ((shift_seq kk s0.compile_oracle) 0))` by fs [shift_seq_def]
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
                      elist_globals_append, BAG_ALL_DISTINCT_BAG_UNION]))
      THEN1 fs [result_case_eq])*)
    \\ Cases_on `isGlobal opn /\ gO_destApx apx <> gO_None`
    THEN1
     (fs []
      \\ Cases_on `opn` \\ fs [isGlobal_def]
      \\ Cases_on `apx` \\ fs[gO_destApx_def] \\ rveq
      \\ fs [known_op_def, NULL_EQ, bool_case_eq] \\ rveq
      \\ imp_res_tac known_LENGTH_EQ_E \\ fs [LENGTH_NIL_SYM] \\ rveq
      \\ fs [evaluate_def, do_app_def] \\ rveq \\ fs []
      \\ fs [case_eq_thms, pair_case_eq] \\ rveq \\ fs [] \\ rveq \\ fs []
      \\ rename1 `lookup nn gg`
      \\ Cases_on `lookup nn gg` \\ fs [] \\ rveq
      \\ `state_globals_approx s gg` by metis_tac [state_globals_approx_subspt]
      \\ imp_res_tac subspt_lookup \\ fs []
      \\ fs [state_globals_approx_def] \\ res_tac
      \\ fs [])
    THEN1
     (qmatch_goalsub_abbrev_tac `evaluate ([op_part _], _, _)`
      \\ `?tr. op_part = Op tr opn` by (fs [Abbr `op_part`] \\ metis_tac [])
      \\ qpat_x_assum `~(_ /\ _)` kall_tac
      \\ qpat_x_assum `Abbrev _` kall_tac
      \\ rw []
      \\ simp [evaluate_def]
      \\ qmatch_asmsub_abbrev_tac `do_app _ vvs _`
      \\ qmatch_goalsub_abbrev_tac `do_app _ wws _`
      \\ drule do_app_lemma
      \\ disch_then (qspecl_then [`vvs`, `wws`, `opn`] mp_tac)
      \\ impl_tac
      THEN1 (irule LIST_REL_mono
             \\ simp [Abbr `vvs`, Abbr `wws`, LIST_REL_REVERSE_EQ]
             \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ rw [])
      \\ fs [case_eq_thms, pair_case_eq]
      \\ rveq \\ fs []
      \\ strip_tac \\ fs []
      \\ imp_res_tac do_app_const \\ fs [next_g_def]
      \\ drule known_correct_approx
      \\ disch_then drule \\ simp []
      \\ `state_globals_approx s0 g0 ∧ oracle_gapprox_disjoint g0 s0.compile_oracle`
         by metis_tac [state_globals_approx_subspt, oracle_gapprox_disjoint_subspt]
      \\ simp [] \\ strip_tac
      \\ qpat_assum `do_app _ _ s1 = _` (mp_then Any mp_tac known_op_correct_approx)
      \\ disch_then drule \\ simp [Abbr `vvs`] \\ strip_tac
      \\ `ssgc_free s1 /\ EVERY vsgc_free vs`
         by (patresolve `evaluate (_, _, s0) = _` hd evaluate_changed_globals
             \\ simp [] \\ strip_tac)
      \\ patresolve `do_app _ _ s1 = _` hd do_app_ssgc
      \\ simp [EVERY_REVERSE] \\ strip_tac
      \\ reverse (Cases_on `?n. opn = SetGlobal n`)
      THEN1 (Cases_on `opn`
             \\ fs [op_gbag_def, mglobals_extend_def]
             \\ fs [state_globals_approx_def] \\ rw []
             \\ res_tac)
      \\ rw [] \\ fs [op_gbag_def, mglobals_extend_def]
      \\ fs [state_globals_approx_def] \\ rw []
      \\ res_tac
      \\ Cases_on `k = n` \\ fs [] \\ rw []
      \\ `vs = [v]`
         by (fs [do_app_def, list_case_eq, option_case_eq]
             \\ rw [] \\ fs [get_global_def, EL_LUPDATE])
      \\ rw [] \\ fs [] \\ rw []
      \\ rename1 `val_approx_val (SND ea1) v`
      \\ PairCases_on `ea1` \\ fs []
      \\ `?aaa. lookup k g = SOME aaa /\ ea11 ◁ aaa`
         by (fs [known_op_def, option_case_eq] \\ rw [])
      \\ imp_res_tac evaluate_IMP_shift_seq
      \\ `subspt (next_g s0) (next_g s1)` by (simp [next_g_def, shift_seq_def, oracle_gapprox_subspt_alt])
      \\ `subspt g (next_g s1)` by metis_tac [next_g_def, subspt_trans]
      \\ pop_assum (fn th => assume_tac (SIMP_RULE (srw_ss()) [next_g_def, subspt_def, domain_lookup, PULL_EXISTS] th))
      \\ res_tac \\ rfs []))
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
           \\ simp []))
  THEN1
   (say "Letrec"
    \\ fs [known_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, bool_case_eq]
    \\ fixeqs
    \\ first_x_assum drule
    \\ rpt (disch_then drule \\ simp [])
    \\ qmatch_asmsub_abbrev_tac `evaluate (_, rcs1 ++ env1 ++ xenv1, _)`
    \\ qmatch_goalsub_abbrev_tac `evaluate (_, rcs2 ++ env2 ++ xenv2, _)`
    \\ disch_then (qspecl_then [`rcs1 ++ env1`, `xenv1`] mp_tac)
    \\ disch_then (qspecl_then [`rcs2 ++ env2`, `xenv2`] mp_tac)
    \\ fs [Abbr `rcs1`, Abbr `rcs2`]
    \\ reverse impl_tac
    THEN1 (strip_tac
           \\ dsimp [EVERY_MAP, LAMBDA_PROD]
           \\ `t0.max_app = s0.max_app` by fs [state_rel_def]
           \\ imp_res_tac known_sing_EQ_E
           \\ fs [] \\ rw [])
    \\ imp_res_tac unique_set_globals_subexps \\ simp []
    \\ imp_res_tac LIST_REL_LENGTH
    \\ rw []
    THEN1 simp [EVERY_GENLIST]
    THEN1 (irule EVERY2_APPEND_suff \\ simp []
           \\ Cases_on `loc`
           \\ simp [LIST_REL_EL_EQN, EL_REPLICATE, clos_gen_noinline_eq])
    THEN1 (Cases_on `loc`
           \\ simp [EVERY_REPLICATE, clos_gen_noinline_val_approx_sgc_free])
    \\ irule EVERY2_APPEND_suff \\ simp []
    \\ simp [LIST_REL_EL_EQN]
    \\ fs [Once every_Fn_vs_NONE_EVERY, EVERY_MAP, LAMBDA_PROD]
    \\ rw []
    \\ qexists_tac `aenv`
    \\ qexists_tac `env1` \\ simp []
    \\ qexists_tac `env2` \\ simp []
    \\ fs [LIST_REL_EL_EQN]
    \\ rw []
    \\ simp [EL_MAP]
    \\ pairarg_tac
    \\ fs [f_rel_def, exp_rel_def]
    \\ qexists_tac `g0`
    \\ qexists_tac `g0`
    \\ simp [EVERY_REPLICATE]
    \\ `subspt g0 (next_g s0)` by metis_tac [subspt_trans]
    \\ qmatch_goalsub_abbrev_tac `(FST (HD (FST knownfn)))`
    \\ `∃ebody apx g0'. knownfn = ([(ebody,apx)],g0')` by metis_tac [known_sing]
    \\ simp []
    \\ qexists_tac `apx`
    \\ qexists_tac `c.inline_factor`
    \\ conj_tac
    THEN1 (Cases_on `loc`
           \\ simp [EVERY_REPLICATE, clos_gen_noinline_val_approx_sgc_free])
    \\ fs [Abbr `knownfn`]
    \\ `c with inline_factor := c.inline_factor = c` by simp[config_component_equality]
    \\ simp []
    \\ drule known_unchanged_globals
    \\ rename1 `EL nn fns = (num_args, xx)`
    \\ `MEM (EL nn fns) fns` by fs [EL_MEM]
    \\ rfs [] \\ fs [MEM_SPLIT]
    \\ fs [elist_globals_append])
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
    \\ fs [evaluate_def]
    \\ Cases_on `LENGTH xs > 0` \\ fs []
    \\ fs [pair_case_eq]
    \\ rename1 `evaluate (_, _ s0) = (_, s1)`
    \\ `subspt g0 g1 ∧ subspt g1 g`
       by (irule subspt_known_elist_globals
           \\ simp [] \\ rpt (goal_assum drule)
           \\ fs [unique_set_globals_def, elist_globals_append,
                  BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
    \\ `subspt g1 (next_g s0)` by metis_tac [subspt_trans]
    \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
    \\ disch_then (qspec_then `xenv2` mp_tac)
    \\ impl_tac THEN1 fs [result_case_eq] \\ strip_tac
    \\ patresolve `evaluate (_, _, s0) = _` hd evaluate_changed_globals
    \\ simp [] \\ strip_tac \\ fs []
    \\ fs [co_every_Fn_vs_NONE_shift_seq,
           oracle_state_sgc_free_shift_seq,
           unique_set_globals_shift_seq]
    \\ patresolve `known _ _ _ g0 = _` hd known_preserves_esgc_free
    \\ simp [] \\ strip_tac
    \\ patresolve `evaluate (_, _, s0) = _` (el 2) known_correct_approx
    \\ disch_then drule \\ simp []
    \\ `subspt g0 (next_g s0)` by metis_tac [subspt_trans]
    \\ `subspt (next_g s0) (next_g s1)`
       by (simp [next_g_def, shift_seq_def, oracle_gapprox_subspt_alt])
    \\ `subspt g (next_g s1)` by metis_tac [subspt_trans]
    \\ `oracle_gapprox_subspt s1.compile_oracle` by simp [oracle_gapprox_subspt_shift_seq]
    \\ rfs []
    \\ impl_tac THEN1 metis_tac [state_globals_approx_subspt, oracle_gapprox_disjoint_subspt]
    \\ strip_tac
    \\ `state_oracle_mglobals_disjoint s1`
       by (match_mp_tac state_oracle_mglobals_disjoint_evaluate_suff
           \\ goal_assum drule \\ simp [])
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
        (* mglobals_disjoint s1 [x1] *)
        \\ patresolve `evaluate (_, _, s0) = _` hd mglobals_disjoint_evaluate
        \\ simp [] \\ disch_then (qspec_then `[x1]` mp_tac)
        \\ impl_tac THEN1 (fs [unique_set_globals_def, elist_globals_append, AC ASSOC_BAG_UNION COMM_BAG_UNION])
        \\ strip_tac
        (**)
        \\ `LIST_REL (v_rel c (next_g s1)) env1 env2` by (
          irule LIST_REL_mono
          \\ goal_assum(first_assum o mp_then Any mp_tac)
          \\ rw[]
          \\ irule v_rel_subspt
          \\ goal_assum(first_assum o mp_then Any mp_tac)
          \\ fs[] )
        \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
        \\ disch_then (qspec_then `xenv2` mp_tac)
        \\ impl_tac THEN1 fs [result_case_eq]
        \\ strip_tac
        \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
        \\ patresolve `evaluate (_, _, s1) = _` hd evaluate_changed_globals
        \\ simp [] \\ strip_tac \\ fs []
        \\ imp_res_tac evaluate_SING \\ rveq \\ fs [] \\ rveq
        \\ rename1 `known (dec_inline_factor _) [body] _ g = ([(ebody, abody)], gdead)`
        \\ patresolve `evaluate ([_], _, s1) = _` (el 2) known_correct_approx
        \\ disch_then drule \\ simp []
        \\ fs [unique_set_globals_shift_seq]
        \\ `subspt g1 (next_g s1)` by metis_tac [subspt_trans]
        \\ impl_tac THEN1 metis_tac [state_globals_approx_subspt, oracle_gapprox_disjoint_subspt]
        \\ strip_tac \\ rveq \\ fs [] \\ rveq
        \\ qmatch_assum_abbrev_tac `evaluate_app _ lhclos _ _ = _`
        \\ rename1 `evaluate (_, _, s0) = (Rval args, _)`
        \\ qmatch_goalsub_abbrev_tac `evaluate (_, _ ++ [fnclos] ++ env2 ++ xenv2, _)`
        \\ `subspt (next_g s1) (next_g s2)` by (
             simp[next_g_def, shift_seq_def]
             \\ irule oracle_gapprox_subspt_alt
             \\ fs[] )
        \\ `v_rel_app c (next_g s2) lhclos (Closure (SOME m) [] ([fnclos] ++ env2 ++ xenv2) (LENGTH xs) ebody) (SOME args)`
           by (fs [Abbr `lhclos`, v_rel_app_def]
               \\ qexists_tac `[]` \\ qexists_tac `[]` \\ simp []
               \\ asm_exists_tac \\ simp []
               \\ fs [exp_rel_def] \\ rveq
               \\ fs [dec_inline_factor_def]
               \\ goal_assum (first_assum o mp_then (Pos last) mp_tac)
               \\ patresolve `known _ [_] _ g1 = _` hd known_preserves_esgc_free
               \\ simp [] \\ strip_tac
               \\ `g = gdead` by (match_mp_tac known_unchanged_globals
                                  \\ asm_exists_tac \\ simp [])
               \\ rw []
               \\ metis_tac [subspt_trans])
        \\ first_x_assum drule (* inst. evaluate_app i.h. *)
        \\ `state_oracle_mglobals_disjoint s2` by (
          irule state_oracle_mglobals_disjoint_evaluate_suff
          \\ goal_assum(first_assum o mp_then (Pat`closSem$evaluate`) mp_tac)
          \\ fs[unique_set_globals_shift_seq] )
        \\ rename1 `LIST_REL _ args args2`
        \\ `LIST_REL (v_rel c (next_g s2)) args args2` by (
          irule LIST_REL_mono
          \\ goal_assum(first_assum o mp_then Any mp_tac)
          \\ rw[]
          \\ irule v_rel_subspt
          \\ goal_assum(first_assum o mp_then Any mp_tac)
          \\ fs[] )
        \\ imp_res_tac nil_unique_set_globals
        \\ simp [oracle_state_sgc_free_shift_seq,
                 co_every_Fn_vs_NONE_shift_seq,
                 oracle_gapprox_subspt_shift_seq,
                 unique_set_globals_shift_seq]
        \\ rpt (disch_then drule \\ simp [] )
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
               \\ spose_not_then assume_tac
               \\ Cases_on `args = []` \\ simp []
               \\ fs [evaluate_app_rw, dest_closure_def, check_loc_def])
        \\ qmatch_goalsub_rename_tac `evaluate_app _ _ args2 t2`
        \\ `args2 <> []` by fs [NOT_NIL_EQ_LENGTH_NOT_0]
        \\ simp [evaluate_app_exact_rw]
        \\ strip_tac
        \\ `t2.clock = s2.clock` by fs [state_rel_def]
        \\ simp [evaluate_mk_Ticks_rw]
        \\ fs [bool_case_eq] \\ rveq \\ fs []
        \\ rewrite_tac [GSYM APPEND_ASSOC, APPEND]
        \\ goal_assum drule \\ simp [])
      THEN1
       ((* pure *)
        simp [evaluate_def, evaluate_append]
        \\ fs [result_case_eq] \\ rveq \\ fs []
        \\ fs [pair_case_eq] \\ rveq \\ fs []
        \\ rename1 `evaluate (_, _ s1) = (_, s2)`
        \\ patresolve `evaluate (_, _, s0) = _` hd mglobals_disjoint_evaluate
        \\ simp [] \\ disch_then (qspec_then `[x1]` mp_tac)
        \\ impl_tac THEN1 (fs [unique_set_globals_def, elist_globals_append, AC ASSOC_BAG_UNION COMM_BAG_UNION])
        \\ strip_tac
        \\ `LIST_REL (v_rel c (next_g s1)) env1 env2` by (
          irule LIST_REL_mono
          \\ goal_assum(first_assum o mp_then Any mp_tac)
          \\ rw[]
          \\ irule v_rel_subspt
          \\ goal_assum(first_assum o mp_then Any mp_tac)
          \\ fs[])
        \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
        \\ disch_then (qspec_then `xenv2` mp_tac)
        \\ impl_tac THEN1 (fs [result_case_eq]
                           \\ metis_tac [v_rel_LIST_REL_subspt, subspt_trans])
        \\ strip_tac
        \\ reverse (fs [result_case_eq]) \\ rveq \\ fs [] \\ rveq
        THEN1 (rename1 `evaluate ([x1], _, _) = (Rerr err_res, _)`
               \\ drule (pure_correct |> GEN_ALL |> INST_TYPE [``:'c`` |-> ``:val_approx num_map#'c``])
               \\ disch_then (qspecl_then [`s1`, `env1 ++ xenv1`] mp_tac)
               \\ simp [] \\ strip_tac \\ Cases_on `err_res` \\ fs [])
        \\ `subspt (next_g s1) (next_g s2)`
           by (fs [result_case_eq]
               \\ imp_res_tac evaluate_IMP_shift_seq
               \\ simp [next_g_def, shift_seq_def, oracle_gapprox_subspt_alt])
        \\ patresolve `evaluate (_, _, s1) = _` hd evaluate_changed_globals
        \\ simp [] \\ strip_tac \\ fs []
        \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
        \\ patresolve `evaluate (_, _, s1) = _` (el 2) known_correct_approx
        \\ rpt (disch_then drule \\ simp [])
        \\ simp [unique_set_globals_shift_seq]
        \\ impl_tac THEN1 metis_tac [oracle_gapprox_disjoint_subspt, subspt_trans]
        \\ strip_tac \\ rveq
        \\ rename1 `known (dec_inline_factor _) [body] _ g = ([(ebody, abody)], gdead)`
        \\ qmatch_assum_abbrev_tac `v_rel _ _ lhclos _`
        \\ rename1 `evaluate (_, _, s0) = (Rval args, _)`
        \\ `v_rel_app c (next_g s2) lhclos (Closure (SOME m) [] (env2 ++ xenv2) (LENGTH xs) ebody) (SOME args)`
           by (fs [Abbr `lhclos`, v_rel_app_def]
               \\ qexists_tac `[]` \\ qexists_tac `[]` \\ simp []
               \\ asm_exists_tac \\ simp []
               \\ fs [exp_rel_def] \\ rveq
               \\ fs [dec_inline_factor_def]
               \\ goal_assum (first_assum o mp_then (Pos last) mp_tac)
               \\ patresolve `known _ [_] _ g1 = _` hd known_preserves_esgc_free
               \\ simp [] \\ strip_tac
               \\ `g = gdead` by (match_mp_tac known_unchanged_globals
                                  \\ asm_exists_tac \\ simp [])
               \\ rveq \\ metis_tac [subspt_trans])
        \\ first_x_assum drule (* inst. evaluate_app i.h. *)
        \\ imp_res_tac nil_unique_set_globals
        \\ simp [oracle_state_sgc_free_shift_seq,
                 co_every_Fn_vs_NONE_shift_seq,
                 oracle_gapprox_subspt_shift_seq,
                 unique_set_globals_shift_seq]
        \\ `state_oracle_mglobals_disjoint s2` by (
          irule state_oracle_mglobals_disjoint_evaluate_suff
          \\ goal_assum(first_assum o mp_then (Pat`closSem$evaluate`) mp_tac)
          \\ fs[unique_set_globals_shift_seq] )
        \\ patresolve `LIST_REL _ args _` hd v_rel_LIST_REL_subspt
        \\ disch_then (qspec_then `next_g s2` mp_tac) \\ simp [] \\ strip_tac
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
               \\ spose_not_then assume_tac
               \\ Cases_on `args = []` \\ simp []
               \\ fs [evaluate_app_rw, dest_closure_def, check_loc_def])
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
      \\ patresolve `evaluate (_, _, s0) = _` hd mglobals_disjoint_evaluate
      \\ simp []
      \\ disch_then (qspec_then `[x1]` mp_tac)
      \\ impl_tac
      THEN1 (fs [unique_set_globals_def, elist_globals_append,
                 BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
      \\ strip_tac
      \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
      \\ disch_then (qspecl_then [`env2`, `xenv2`] mp_tac)
      \\ impl_tac THEN1 (fs [result_case_eq]
                         \\ metis_tac [v_rel_LIST_REL_subspt, subspt_trans])
      \\ strip_tac
      \\ imp_res_tac known_sing_EQ_E
      \\ fs [result_case_eq] \\ rveq \\ fs []
      \\ imp_res_tac evaluate_SING \\ fs [] \\ rveq
      \\ first_x_assum match_mp_tac
      \\ imp_res_tac nil_unique_set_globals
      \\ patresolve `evaluate (_, _, s1) = _` hd evaluate_changed_globals
      \\ simp [] \\ strip_tac \\ fs []
      \\ qexists_tac `NONE` \\ simp [v_rel_app_NONE]
      \\ simp [co_every_Fn_vs_NONE_shift_seq,
               oracle_gapprox_subspt_shift_seq,
               oracle_state_sgc_free_shift_seq,
               unique_set_globals_shift_seq]
      \\ `state_oracle_mglobals_disjoint s2`
         by (match_mp_tac state_oracle_mglobals_disjoint_evaluate_suff
             \\ goal_assum drule
             \\ simp [unique_set_globals_shift_seq])
      \\ `subspt (next_g s1) (next_g s2)`
         by (simp [next_g_def, shift_seq_def, oracle_gapprox_subspt_alt])
      \\ simp []
      \\ conj_tac THEN1 metis_tac [v_rel_LIST_REL_subspt]
      \\ patresolve `evaluate (_, _, s1) = _` (el 2) known_correct_approx
      \\ rpt (disch_then drule \\ simp [])
      \\ simp [unique_set_globals_shift_seq]
      \\ impl_tac
      THEN1
       (irule oracle_gapprox_disjoint_shift_seq_unique_set_globals
        \\ goal_assum (first_assum o mp_then (Pat `known`) mp_tac)
        \\ simp []
        \\ metis_tac [oracle_gapprox_disjoint_subspt])
      \\ strip_tac
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ simp [loptrel_def]
      \\ fs [decide_inline_def, va_case_eq, bool_case_eq]
      \\ rw [] \\ fs [] \\ rw [] \\ fs []
      \\ imp_res_tac LIST_REL_LENGTH \\ fs []
      \\ rename1 `FST (EL jj fns1) = FST (EL jj fns2)`
      \\ qpat_x_assum `LIST_REL (f_rel _ _ _) _ _` mp_tac
      \\ simp [LIST_REL_EL_EQN]
      \\ disch_then (qspec_then `jj` mp_tac)
      \\ Cases_on `EL jj fns1`
      \\ Cases_on `EL jj fns2`
      \\ simp [f_rel_def])
    THEN1
     ((* inlD_Nothing *)
      simp [evaluate_def]
      \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
      \\ fs [pair_case_eq]
      \\ rename1 `evaluate ([_], _ s1) = (_, s2)`
      \\ patresolve `evaluate (_, _, s0) = _` hd mglobals_disjoint_evaluate
      \\ simp []
      \\ disch_then (qspec_then `[x1]` mp_tac)
      \\ impl_tac
      THEN1 (fs [unique_set_globals_def, elist_globals_append,
                 BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_SYM])
      \\ strip_tac
      \\ first_x_assum drule \\ rpt (disch_then drule \\ simp [])
      \\ disch_then (qspecl_then [`env2`, `xenv2`] mp_tac)
      \\ impl_tac THEN1 (fs [result_case_eq]
                         \\ metis_tac [v_rel_LIST_REL_subspt, subspt_trans])
      \\ strip_tac
      \\ imp_res_tac known_sing_EQ_E
      \\ fs [result_case_eq] \\ rveq \\ fs []
      \\ imp_res_tac evaluate_SING \\ fs [] \\ rveq
      \\ first_x_assum match_mp_tac
      \\ imp_res_tac nil_unique_set_globals
      \\ patresolve `evaluate (_, _, s1) = _` hd evaluate_changed_globals
      \\ simp [] \\ strip_tac \\ fs []
      \\ qexists_tac `NONE`
      \\ simp [v_rel_app_NONE,
               co_every_Fn_vs_NONE_shift_seq,
               oracle_gapprox_subspt_shift_seq,
               oracle_state_sgc_free_shift_seq,
               unique_set_globals_shift_seq]
      \\ `state_oracle_mglobals_disjoint s2`
         by (match_mp_tac state_oracle_mglobals_disjoint_evaluate_suff
             \\ goal_assum drule
             \\ simp [unique_set_globals_shift_seq])
      \\ `subspt (next_g s1) (next_g s2)`
         by (simp [next_g_def, shift_seq_def, oracle_gapprox_subspt_alt])
      \\ simp []
      \\ conj_tac THEN1 metis_tac [v_rel_LIST_REL_subspt]
      \\ simp [loptrel_def]))
  THEN1
   (say "Tick"
    \\ fs [known_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, pair_case_eq]
    \\ `t0.clock = s0.clock` by fs [state_rel_def]
    \\ Cases_on `s0.clock = 0`
    \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac known_sing_EQ_E
    \\ fs [] \\ rveq
    \\ first_x_assum drule \\ simp []
    \\ disch_then match_mp_tac
    \\ fs [dec_clock_def, state_rel_def, next_g_def,
           state_oracle_mglobals_disjoint_def, mglobals_disjoint_def]
    \\ asm_exists_tac \\ simp []
    \\ imp_res_tac unique_set_globals_subexps \\ simp [])
  THEN1
   (say "Call"
    \\ fs [known_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [evaluate_def, pair_case_eq]
    \\ imp_res_tac unique_set_globals_subexps
    \\ first_x_assum drule
    \\ rpt (disch_then drule \\ simp [])
    \\ disch_then (qspec_then `xenv2` mp_tac)
    \\ fs [result_case_eq] \\ rw []
    \\ fs [state_rel_def, find_code_def])
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
        \\ EVERY_CASE_TAC \\ fs [next_g_def]
        \\ qexists_tac `aenv`
        \\ qexists_tac `env1a` \\ simp []
        \\ qexists_tac `env2a` \\ simp []
        \\ irule EVERY2_APPEND_suff \\ simp [])
      \\ rpt (pairarg_tac \\ fs [])
      \\ rename1 `EL ii _`
      \\ qpat_assum `LIST_REL _ fns _` (fn th =>
           strip_assume_tac (SIMP_RULE (srw_ss()) [LIST_REL_EL_EQN] th))
      \\ pop_assum (qspec_then `ii` mp_tac)
      \\ simp [f_rel_def]
      \\ strip_tac
      \\ fs [bool_case_eq]
      THEN1
       (fs [state_rel_def, next_g_def, loptrel_def, check_loc_def]
        \\ Cases_on `lopt2` \\ fs []
        \\ Cases_on `loc` \\ fs [])
      \\ rw []
      \\ dsimp []
      \\ fs [state_rel_def, next_g_def]
      \\ goal_assum (first_assum o mp_then (Pat `val_approx_val`) mp_tac)
      \\ simp []
      \\ goal_assum (first_assum o mp_then (Pat `LIST_REL`) mp_tac)
      \\ simp []
      \\ reverse conj_tac
      THEN1 (irule EVERY2_APPEND_suff \\ simp [])
      \\ fs [loptrel_def, check_loc_def]
      \\ Cases_on `lopt2` \\ fs []
      \\ Cases_on `loc` \\ fs [])
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
          THEN1 fs [state_rel_def, next_g_def]
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
          \\ `LIST_REL (v_rel c (next_g state1)) fullenv1 fullenv2`
             by (unabbrev_all_tac \\ fs [next_g_def]
                 \\ rpt (irule EVERY2_APPEND_suff \\ simp [])
                 \\ irule EVERY2_TAKE
                 \\ irule EVERY2_APPEND_suff \\ simp [])
          \\ disch_then (pop_assum o mp_then Any mp_tac) \\ simp []
          \\ `state_rel c (next_g state1) state1 state2`
             by (fs [Abbr `state1`, Abbr `state2`, state_rel_def, next_g_def])
          \\ disch_then drule
          \\ disch_then (qspec_then `extra2` mp_tac) \\ simp []
          \\ simp [set_globals_empty_esgc_free]
          \\ simp [EVERY_REVERSE, EVERY_TAKE]
          \\ simp [set_globals_empty_unique_set_globals]
          \\ rename1 `evaluate (_, _, state1) = (_, s1)`
          \\ rveq
          \\ `subspt (next_g state1) (next_g s1) /\ subspt (next_g s1) (next_g s)`
             by (fs [Abbr `state1`, result_case_eq] \\ rveq
                 \\ imp_res_tac evaluate_SING \\ rveq \\ fs []
                 \\ imp_res_tac evaluate_app_IMP_shift_seq
                 \\ imp_res_tac evaluate_IMP_shift_seq \\ fs []
                 \\ simp [next_g_def, shift_seq_def, oracle_gapprox_subspt_alt])
          \\ simp [mglobals_disjoint_def]
          \\ fs [Abbr `fullenv1`]
          \\ impl_tac
          THEN1
           (fs [Abbr `state1`, next_g_def,
                state_oracle_mglobals_disjoint_def, mglobals_disjoint_def]
            \\ conj_tac
            THEN1 (irule EVERY2_APPEND_suff \\ simp []
                   \\ simp [LIST_REL_EL_EQN, EL_REPLICATE])
            \\ fs [result_case_eq])
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
          \\ simp [set_globals_empty_unique_set_globals]
          \\ simp [set_globals_empty_esgc_free]
          \\ simp [EVERY_REVERSE, EVERY_TAKE]
          \\ impl_tac
          THEN1
           (rpt conj_tac
            THEN1 (irule EVERY2_APPEND_suff \\ simp []
                   \\ simp [LIST_REL_EL_EQN, EL_REPLICATE])
            THEN1 metis_tac [state_globals_approx_subspt]
            THEN1 fs [mglobals_disjoint_def]
            THEN1 metis_tac [oracle_gapprox_disjoint_subspt])
          \\ strip_tac \\ strip_tac
          \\ simp [EVERY_DROP, EVERY_REVERSE]
          \\ simp [oracle_state_sgc_free_shift_seq,
                   co_every_Fn_vs_NONE_shift_seq,
                   oracle_gapprox_subspt_shift_seq,
                   unique_set_globals_shift_seq]
          \\ simp [loptrel_def]
          \\ simp [v_rel_app_NONE]
          \\ `state_oracle_mglobals_disjoint s1`
             by (match_mp_tac state_oracle_mglobals_disjoint_evaluate_suff
                 \\ goal_assum drule \\ simp []
                 \\ simp [set_globals_empty_unique_set_globals]
                 \\ simp [set_globals_empty_esgc_free]
                 \\ simp [EVERY_REVERSE, EVERY_TAKE]
                 \\ fs [mglobals_disjoint_def, state_oracle_mglobals_disjoint_def])
          \\ simp []
          \\ irule EVERY2_DROP
          \\ irule EVERY2_APPEND_suff
          \\ fs [next_g_def]
          \\ metis_tac [v_rel_LIST_REL_subspt, v_rel_subspt])
        \\ rpt (pairarg_tac \\ fs [])
        \\ rename1 `EL ii _`
        \\ qpat_assum `LIST_REL _ fns _` (fn th =>
             strip_assume_tac (SIMP_RULE (srw_ss()) [LIST_REL_EL_EQN] th))
        \\ pop_assum (qspec_then `ii` mp_tac)
        \\ simp [f_rel_def]
        \\ strip_tac
        \\ IF_CASES_TAC \\ fs [] \\ rveq
        \\ qpat_abbrev_tac `loc_is_ok = check_loc _ lopt2 _ _ _ _`
        \\ `loc_is_ok` by (fs [Abbr `loc_is_ok`, loptrel_def, check_loc_def]
                           \\ TRY (Cases_on `lopt2` \\ fs [])
                           \\ TRY (Cases_on `loc` \\ fs [] \\ rveq)
                           \\ fs [check_loc_def])
        \\ simp [Abbr `loc_is_ok`]
        \\ fs [bool_case_eq] \\ rveq \\ fs []
        THEN1 (fs [state_rel_def, next_g_def])
        \\ fs [pair_case_eq]
        \\ rfs [SUB_SUB]
        \\ first_x_assum drule
        \\ fs [exp_rel_def]
        \\ rename1 `known _ _ _ g0 = (_, g1)`
        \\ qmatch_asmsub_rename_tac `evaluate ([exp1], _, _)`
        \\ `set_globals exp1 = {||}`
           by (fs [elglobals_EQ_EMPTY]
               \\ first_assum irule
               \\ simp [MEM_EL]
               \\ qexists_tac `ii`
               \\ simp [EL_MAP])
        \\ `g0 = g1` by (match_mp_tac known_unchanged_globals
                         \\ asm_exists_tac \\ simp [])
        \\ disch_then drule
        \\ simp [v_rel_upd_inline_factor, state_rel_upd_inline_factor]
        \\ qmatch_asmsub_abbrev_tac `evaluate (_, fullenv1 ++ _, state1)`
        \\ qmatch_goalsub_abbrev_tac `evaluate (_, fullenv2 ++ extra2, state2)`
        \\ `LIST_REL (v_rel c (next_g state1)) fullenv1 fullenv2`
           by (unabbrev_all_tac \\ fs [next_g_def]
               \\ rpt (irule EVERY2_APPEND_suff \\ simp [])
               \\ conj_tac
               THEN1
                (irule EVERY2_APPEND_suff \\ simp []
                 \\ irule EVERY2_TAKE
                 \\ irule EVERY2_APPEND_suff \\ simp [])
               \\ rw [LIST_REL_GENLIST]
               \\ goal_assum (first_assum o mp_then (Pat `val_approx_val`) mp_tac)
               \\ simp []
               \\ goal_assum (first_assum o mp_then Any mp_tac)
               \\ simp [])
        \\ disch_then (pop_assum o mp_then Any mp_tac)
        \\ simp []
        \\ `state_rel c (next_g state1) state1 state2`
           by (fs [Abbr `state1`, Abbr `state2`, state_rel_def, next_g_def])
        \\ disch_then (pop_assum o mp_then Any mp_tac)
        \\ disch_then (qspec_then `extra2` mp_tac)
        \\ simp [EVERY_REVERSE, EVERY_TAKE, EVERY_GENLIST,
                 set_globals_empty_esgc_free,
                 set_globals_empty_unique_set_globals,
                 mglobals_disjoint_def]
        \\ `every_Fn_vs_NONE [exp1]`
            by (qpat_assum `EVERY (λ(n,e). every_Fn_vs_NONE [e]) _` (fn th =>
                  SIMP_RULE (srw_ss()) [EVERY_EL] th |> mp_tac)
                \\ disch_then (qspec_then `ii` mp_tac)
                \\ simp [])
        \\ `fv_max (LENGTH fullenv1) [exp1]`
            by (qpat_assum `EVERY (λ(n,e). fv_max _ _) _` (fn th =>
                  SIMP_RULE (srw_ss()) [EVERY_EL] th |> mp_tac)
                \\ disch_then (qspec_then `ii` mp_tac)
                \\ simp [Abbr `fullenv1`])
        \\ simp []
        \\ impl_tac
        THEN1
         (fs [Abbr `state1`, next_g_def,
              state_oracle_mglobals_disjoint_def, mglobals_disjoint_def]
          \\ conj_tac
          THEN1
           (simp [Abbr `fullenv1`]
            \\ rpt (irule EVERY2_APPEND_suff \\ simp [])
            \\ conj_tac
            THEN1 (simp [LIST_REL_EL_EQN, EL_REPLICATE])
            \\ CASE_TAC
            \\ simp [LIST_REL_EL_EQN, EL_REPLICATE, clos_gen_noinline_eq])
          \\ fs [result_case_eq])
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
          \\ rw [])
        \\ first_x_assum match_mp_tac
        \\ qexists_tac `NONE` \\ simp []
        \\ patresolve `evaluate (_, _, state1) = _` hd evaluate_changed_globals
        \\ patresolve `evaluate (_, _, state1) = _` (el 2) known_correct_approx
        \\ unabbrev_all_tac
        \\ rpt (disch_then drule \\ simp [])
        \\ simp [EVERY_REVERSE, EVERY_TAKE, EVERY_GENLIST,
                 set_globals_empty_esgc_free,
                 set_globals_empty_unique_set_globals,
                 mglobals_disjoint_def]
        \\ `state_globals_approx s0 g0` by metis_tac [state_globals_approx_subspt]
        \\ `oracle_gapprox_disjoint g0 s0.compile_oracle` by metis_tac [oracle_gapprox_disjoint_subspt]
        \\ simp []
        \\ impl_tac
        THEN1
         (rpt (irule EVERY2_APPEND_suff \\ simp [])
          \\ conj_tac
          THEN1 (simp [LIST_REL_EL_EQN, EL_REPLICATE])
          \\ CASE_TAC
          \\ simp [LIST_REL_EL_EQN, EL_REPLICATE, clos_gen_noinline_eq])
        \\ strip_tac \\ strip_tac
        \\ simp [EVERY_DROP, EVERY_REVERSE]
        \\ simp [oracle_state_sgc_free_shift_seq,
                 co_every_Fn_vs_NONE_shift_seq,
                 oracle_gapprox_subspt_shift_seq,
                 unique_set_globals_shift_seq]
        \\ simp [loptrel_def]
        \\ simp [v_rel_app_NONE]
        \\ `state_oracle_mglobals_disjoint s1`
           by (irule state_oracle_mglobals_disjoint_evaluate_suff
               \\ goal_assum (first_assum o mp_then (Pat `closSem$evaluate`) mp_tac)
               \\ simp [EVERY_REVERSE, EVERY_TAKE, EVERY_GENLIST,
                        set_globals_empty_unique_set_globals,
                        set_globals_empty_esgc_free]
               \\ fs [mglobals_disjoint_def, state_oracle_mglobals_disjoint_def])
        \\ simp []
        \\ irule EVERY2_DROP
        \\ irule EVERY2_APPEND_suff
        \\ simp []
        \\ `subspt (next_g s0) (next_g s1)`
           by (simp [next_g_def, shift_seq_def, oracle_gapprox_subspt_alt])
        \\ metis_tac [v_rel_LIST_REL_subspt, v_rel_subspt])
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
          \\ fs [state_rel_def, next_g_def]
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
          \\ `LIST_REL (v_rel c (next_g state1)) fullenv1 fullenv2`
             by (unabbrev_all_tac \\ fs [next_g_def]
                 \\ rpt (irule EVERY2_APPEND_suff \\ simp [])
                 \\ irule EVERY2_TAKE
                 \\ irule EVERY2_APPEND_suff \\ simp [])
          \\ disch_then (pop_assum o mp_then Any mp_tac) \\ simp []
          \\ `num_args = LENGTH ys + 1` by fs [DROP_NIL]
          \\ `state_rel c (next_g state1) state1 state2`
             by (fs [Abbr `state1`, Abbr `state2`, next_g_def, state_rel_def, DROP_NIL])
          \\ disch_then drule \\ simp []
          \\ disch_then (qspec_then `extra2` mp_tac)
          \\ simp [set_globals_empty_esgc_free]
          \\ simp [EVERY_REVERSE, EVERY_TAKE]
          \\ simp [set_globals_empty_unique_set_globals]
          \\ `s1 = s` by fs [case_eq_thms]
          \\ simp []
          \\ fs [Abbr `fullenv1`]
          \\ simp [TAKE_LENGTH_ID_rwt]
          \\ rveq
          \\ impl_tac
          THEN1 (fs [Abbr `state1`, next_g_def,
                     state_oracle_mglobals_disjoint_def, mglobals_disjoint_def]
                 \\ fs [result_case_eq] \\ metis_tac [EVERY2_APPEND_suff])
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
          \\ `f_rel c aenvcase (next_g s0) (EL i funs1) (EL i funs2)` by fs [LIST_REL_EL_EQN]
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
          \\ qmatch_asmsub_abbrev_tac `evaluate (_, fullenv1 ++ _, state1)`
          \\ qmatch_goalsub_abbrev_tac `evaluate (_, fullenv2 ++ extra2, state2)`
          \\ `LIST_REL (v_rel c (next_g state1)) fullenv1 fullenv2`
             by (unabbrev_all_tac \\ fs [next_g_def]
                 \\ rpt (irule EVERY2_APPEND_suff \\ simp [] \\ TRY conj_tac)
                 THEN1 (irule EVERY2_TAKE
                        \\ irule EVERY2_APPEND_suff \\ simp [])
                 THEN1 (fs [LIST_REL_GENLIST] \\ rw []
                        \\ `env1a ++ env1b = env1a ++ env1b` by simp []
                        \\ rpt (asm_exists_tac \\ simp [])))
          \\ disch_then (pop_assum o mp_then Any mp_tac)
          \\ `state_rel c (next_g state1) state1 state2`
             by (fs [Abbr `state1`, Abbr `state2`, state_rel_def, next_g_def]
                 \\ fs [CONV_RULE (LHS_CONV SYM_CONV) REVERSE_EQ_NIL, DROP_NIL])
          \\ disch_then drule \\ simp []
          \\ disch_then (qspec_then `extra2` mp_tac)
          \\ simp [EVERY_REVERSE, EVERY_TAKE, EVERY_GENLIST]
          \\ `set_globals exp1 = {||}`
             by (fs [elglobals_EQ_EMPTY]
                 \\ first_x_assum irule \\ simp [MEM_MAP]
                 \\ qexists_tac `EL i funs1` \\ simp [])
          \\ simp [set_globals_empty_esgc_free, set_globals_empty_unique_set_globals]
          \\ `s1 = s` by fs [case_eq_thms] \\ simp []
          \\ `every_Fn_vs_NONE [exp1]` by (fs [EVERY_MEM, FORALL_PROD] \\ metis_tac [])
          \\ `fv_max (LENGTH fullenv1) [exp1]`
             by (fs [Abbr `fullenv1`, EVERY_MEM, FORALL_PROD]
                 \\ irule fv_max_less
                 \\ qexists_tac `num_args1 + LENGTH env2a` \\ simp [])
          \\ `LIST_REL val_approx_val (REPLICATE num_args1 Other ⧺ aenvcase) fullenv1`
             by (simp [Abbr `fullenv1`, Abbr `aenvcase`]
                 \\ rpt (irule EVERY2_APPEND_suff \\ simp [] \\ TRY conj_tac)
                 THEN1 simp [LIST_REL_EL_EQN, EL_REPLICATE]
                 \\ Cases_on `loc` \\ simp []
                 THEN1 simp [LIST_REL_EL_EQN, EL_REPLICATE]
                 \\ simp [clos_gen_noinline_eq, LIST_REL_EL_EQN])
          \\ simp []
          \\ unabbrev_all_tac
          \\ fs [next_g_def, state_oracle_mglobals_disjoint_def, mglobals_disjoint_def]
          \\ impl_tac THEN1 fs [result_case_eq]
          \\ strip_tac
          \\ fs [result_case_eq] \\ rveq \\ fs [] \\ rveq
          \\ imp_res_tac evaluate_SING \\ rveq \\ fs [] \\ rveq \\ fs []
          \\ fs [CONV_RULE (LHS_CONV SYM_CONV) REVERSE_EQ_NIL, DROP_NIL]
          \\ simp [DROP_LENGTH_TOO_LONG])))));

Theorem semantics_known:
   semantics (ffi:'ffi ffi_state) max_app FEMPTY co
     (state_cc (compile_inc c) cc) xs <> Fail ==>
   (!n. SND (SND (co n)) = []) /\
   (!n. fv_max 0 (FST (SND (co n)))) /\
   (!n exps aux. SND (co n) = (exps,aux) ==> EVERY esgc_free exps) /\
   every_Fn_vs_NONE xs /\
   co_every_Fn_vs_NONE co /\
   oracle_gapprox_subspt co /\
   oracle_state_sgc_free co /\
   unique_set_globals xs co /\
   EVERY esgc_free xs /\
   fv_max 0 xs /\
   FST (FST (co 0)) = g /\
   oracle_gapprox_disjoint g co /\
   known c xs [] LN = (eas, g) ==>
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     (state_co (compile_inc c) co) cc (MAP FST eas) =
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     co (state_cc (compile_inc c) cc) xs
Proof
  strip_tac
  \\ ho_match_mp_tac IMP_semantics_eq
  \\ fs [] \\ fs [eval_sim_def] \\ rw []
  \\ drule (CONJUNCT1 known_correct0)
  \\ simp []
  \\ disch_then drule
  \\ disch_then (qspec_then `[]` mp_tac)
  \\ disch_then (qspec_then `initial_state ffi max_app FEMPTY
                               (state_co (compile_inc c) co) cc k` mp_tac)
  \\ rename1 `evaluate (xs, _, _) = (res1, s2)`
  \\ impl_tac
  THEN1
   (fs [state_rel_def, initial_state_def, fmap_rel_def]
    \\ simp [globals_approx_sgc_free_def, lookup_def]
    \\ simp [state_globals_approx_def, get_global_def]
    \\ simp [ssgc_free_def]
    \\ simp [state_oracle_mglobals_disjoint_def, mglobals_disjoint_def, mapped_globals_def, get_global_def]
    \\ simp [next_g_def]
    \\ rw [] THEN1 res_tac
    \\ fs [PAIR_FST_SND_EQ] \\ rfs [] \\ rw [])
  \\ strip_tac
  \\ qexists_tac `0` \\ simp []
  \\ fs [state_rel_def]
  \\ Cases_on `res1` \\ fs []
  \\ Cases_on `e` \\ fs []
QED

Theorem code_locs_mk_Ticks[simp]:
   ∀a b c d. code_locs [mk_Ticks a b c d] = code_locs [d]
Proof
  recInduct mk_Ticks_ind \\ rw[]
  \\ rw[Once mk_Ticks_def]
  \\ rw[code_locs_def]
QED

Theorem contains_closures_code_locs:
   ∀es. ¬contains_closures es ⇒ code_locs es = []
Proof
  recInduct contains_closures_ind
  \\ rw[contains_closures_def]
  \\ rw[code_locs_def]
QED

Theorem code_locs_decide_inline:
   decide_inline a b c d = inlD_LetInline e ⇒ code_locs [e] = []
Proof
  rw[decide_inline_def]
  \\ fs[CaseEq"val_approx",bool_case_eq]
  \\ rveq
  \\ imp_res_tac contains_closures_code_locs
QED

Theorem known_code_locs_bag:
   !c xs aenv g0 eas g.
     known c xs aenv g0 = (eas, g) ==>
     LIST_TO_BAG (code_locs (MAP FST eas)) ≤ LIST_TO_BAG (code_locs xs)
Proof
  recInduct known_ind
  \\ rw[known_def] \\ rw[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ imp_res_tac known_sing_EQ_E \\ rw []
  \\ fs [code_locs_def, code_locs_append, LIST_TO_BAG_APPEND]
  \\ srw_tac [bagLib.SBAG_SOLVE_ss] []
  THEN1 (simp [Once code_locs_cons, code_locs_append, LIST_TO_BAG_APPEND]
         \\ srw_tac [bagLib.SBAG_SOLVE_ss] [])
  THEN1 (qpat_abbrev_tac `gooblygook = gO_destApx _`
         \\ Cases_on `gooblygook` \\ simp [code_locs_def])
  THEN1 (fs [inlD_case_eq] \\ rw []
         \\ fs [code_locs_def, code_locs_append, LIST_TO_BAG_APPEND]
         \\ srw_tac [bagLib.SBAG_SOLVE_ss] []
         \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
         \\ imp_res_tac code_locs_decide_inline
         \\ imp_res_tac known_sing_EQ_E
         \\ fs [bool_case_eq] \\ rw []
         \\ simp [code_locs_def, code_locs_append, LIST_TO_BAG_APPEND]
         \\ fs [LIST_TO_BAG_def]
         \\ srw_tac [bagLib.SBAG_SOLVE_ss] [])
  \\ simp[MAP_MAP_o, o_DEF, UNCURRY, code_locs_map]
  \\ irule (el 7 (CONJUNCTS SUB_BAG_UNION)) \\ simp []
  \\ irule LIST_TO_BAG_SUB_BAG_FLAT_suff
  \\ fs[EVERY2_MAP]
  \\ irule EVERY2_refl
  \\ simp[MAP_EQ_f, FORALL_PROD]
  \\ rw[]
  \\ first_x_assum drule
  \\ simp[GSYM FST_pair]
  \\ rpt(pairarg_tac \\ fs[])
  \\ imp_res_tac known_LENGTH_EQ_E
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ rveq \\ fs[]
QED

Theorem compile_code_locs_bag:
   clos_known$compile kc es = (kc', es') ⇒
     LIST_TO_BAG (code_locs es') ≤ LIST_TO_BAG (code_locs es)
Proof
  Cases_on`kc`
  \\ rw[clos_knownTheory.compile_def]
  \\ pairarg_tac \\ fs[]
  \\ rw [] \\ fs [clos_letopProofTheory.code_locs_let_op,
       clos_ticksProofTheory.code_locs_remove_ticks]
  \\ imp_res_tac known_code_locs_bag \\ rw[]
  \\ fs[clos_fvsTheory.compile_def]
QED

Theorem compile_LENGTH:
   clos_known$compile kc es = (kc', es') ⇒ LENGTH es' = LENGTH es
Proof
  Cases_on`kc` \\ rw[compile_def]
  \\ pairarg_tac \\ fs[] \\ rw[]
  \\ fs [clos_letopTheory.LENGTH_let_op,clos_ticksTheory.LENGTH_remove_ticks,
         clos_fvsTheory.compile_def]
  \\ imp_res_tac known_LENGTH_EQ_E
  \\ fs[clos_fvsProofTheory.LENGTH_remove_fvs]
QED

val syntax_ok_def = Define`
  syntax_ok xs ⇔
    every_Fn_vs_NONE xs ∧
    EVERY esgc_free xs`;

val syntax_oracle_ok_def = Define`
  syntax_oracle_ok xs co ⇔
    syntax_ok xs ∧
    co_every_Fn_vs_NONE co ∧
    oracle_state_sgc_free co ∧
    oracle_gapprox_subspt co ∧
    oracle_gapprox_disjoint (FST (FST (co 0))) co ∧
    unique_set_globals xs co ∧
    (∀n. SND(SND(co n)) = [] ∧
         syntax_ok (FST (SND (co n))))`;

val known_cc_def = Define `
  known_cc known_conf cc =
    (case known_conf of
     | SOME kcfg =>
       (pure_cc clos_fvsProof$compile_inc
         (state_cc (compile_inc kcfg)
           (pure_cc clos_ticksProof$compile_inc
             (pure_cc clos_letopProof$compile_inc
               (cc:'b clos_cc):'b clos_cc):'b clos_cc)))
     | NONE      => state_cc (CURRY I) cc :(val_approx num_map # 'b) clos_cc)`;

val known_co_def = Define `
  known_co known_conf (co : (val_approx num_map # 'b) clos_co) =
    (case known_conf of
     | SOME kcfg => (pure_co clos_letopProof$compile_inc o
                       ((pure_co clos_ticksProof$compile_inc o
                          (state_co (compile_inc kcfg)
                            (pure_co clos_fvsProof$compile_inc o co)
                            : 'b clos_co)) : 'b clos_co))
     | NONE      => (state_co (CURRY I) co) : 'b clos_co)`;

Theorem FST_known_co:
   FST (known_co kc co n) = SND (FST (co n))
Proof
  rw[known_co_def] \\ CASE_TAC
  \\ simp[backendPropsTheory.FST_state_co]
QED

Theorem semantics_compile:
   closSem$semantics ffi max_app FEMPTY co cc1 xs ≠ Fail ∧
   (cc1 = known_cc known_conf cc) ∧
   (co1 = known_co known_conf co) ∧
   (compile known_conf xs = (known_conf', es)) ∧
   (IS_SOME known_conf ⇒
      syntax_oracle_ok xs co ∧ 1 ≤ max_app ∧
      FST (FST (co 0)) = (THE known_conf').val_approx_spt)
   ⇒
   semantics ffi max_app FEMPTY co1 cc es =
   semantics ffi max_app FEMPTY co cc1 xs
Proof
  simp [known_co_def,known_cc_def]
  \\ strip_tac
  \\ Cases_on`known_conf` \\ fs[compile_def]
  >- ( match_mp_tac semantics_CURRY_I \\ fs[] )
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ drule (clos_fvsProofTheory.semantics_compile)
  \\ impl_tac
  >- ( fs[syntax_oracle_ok_def] )
  \\ disch_then (fn th => fs [GSYM th])
  \\ drule (GEN_ALL semantics_known) \\ fs []
  \\ impl_keep_tac THEN1
   (fs[syntax_ok_def,syntax_oracle_ok_def]
    \\ simp[clos_fvsTheory.compile_def]
    \\ conj_tac
    >- ( gen_tac \\ Cases_on`SND (co n)` \\ EVAL_TAC )
    \\ conj_tac
    >- (
      gen_tac \\ Cases_on`SND (co n)` \\ EVAL_TAC
      \\ fs[co_every_Fn_vs_NONE_def]
      \\ first_x_assum(qspec_then`n`mp_tac)
      \\ rw[]
      \\ drule clos_fvsProofTheory.fv_max_remove_fvs
      \\ disch_then(qspec_then`0`mp_tac)
      \\ rw[])
    \\ conj_tac
    >- (
      gen_tac \\ Cases_on`SND (co n)` \\ EVAL_TAC
      \\ rw[] \\ rw[]
      \\ first_x_assum(qspec_then`n`mp_tac)
      \\ rw[] )
    \\ fs[co_every_Fn_vs_NONE_def]
    \\ conj_tac
    >- (
      gen_tac \\ Cases_on`SND (co n)` \\ EVAL_TAC
      \\ rw[] \\ rw[]
      \\ first_x_assum(qspec_then`n`mp_tac)
      \\ rw[] )
    \\ fs[oracle_gapprox_subspt_def]
    \\ fs[oracle_state_sgc_free_def]
    \\ conj_tac
    >- (
      fs[unique_set_globals_def, elist_globals_append, first_n_exps_def]
      \\ fs[elist_globals_FOLDR, MAP_FLAT, MAP_GENLIST]
      \\ fs[o_DEF]
      \\ gen_tac
      \\ qmatch_goalsub_abbrev_tac`FLAT (GENLIST X n)`
      \\ qmatch_asmsub_abbrev_tac`GENLIST Y`
      \\ `X =Y`
      by (
        simp[Abbr`X`,Abbr`Y`, FUN_EQ_THM]
        \\ qx_gen_tac`m` \\ Cases_on`SND (co m)` \\ EVAL_TAC
        \\ simp[])
      \\ fs[] )
    \\ fs[oracle_gapprox_disjoint_def]
    \\ conj_tac
    >- (
      drule clos_fvsProofTheory.fv_max_remove_fvs
      \\ disch_then(qspec_then`0`mp_tac)
      \\ rw[fv_max_def] )
    \\ fs[gapprox_disjoint_def]
    \\ gen_tac
    \\ Cases_on`SND (co n)`
    \\ simp[clos_fvsProofTheory.compile_inc_def]
    \\ first_x_assum(qspec_then`n`mp_tac) \\ simp[]
    \\ first_x_assum(qspec_then`n`mp_tac) \\ simp[]
    \\ simp[clos_fvsTheory.compile_def] )
  \\ disch_then (fn th => fs [GSYM th])
  \\ drule (GEN_ALL clos_ticksProofTheory.semantics_remove_ticks)
  \\ impl_keep_tac THEN1
   (fs [syntax_oracle_ok_def,state_co_def] \\ rw []
    \\ pairarg_tac \\ fs []
    \\ PairCases_on `progs`
    \\ fs [compile_inc_def]
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ first_x_assum (qspec_then `n` assume_tac) \\ fs [] \\ rfs []
    \\ Cases_on`co n` \\ fs[backendPropsTheory.pure_co_def]
    \\ Cases_on`r` \\ fs[clos_fvsProofTheory.compile_inc_def])
  \\ disch_then (fn th => fs [th])
  \\ drule (GEN_ALL clos_letopProofTheory.semantics_let_op)
  \\ reverse impl_tac \\ fs [] \\ rw []
  \\ first_x_assum (qspec_then `n` assume_tac) \\ fs []
  \\ qmatch_assum_abbrev_tac `SND pp = []`
  \\ Cases_on `pp` \\ fs [clos_ticksProofTheory.compile_inc_def]
  \\ fs []
QED

Theorem every_Fn_SOME_mk_Ticks:
   ∀t tc n e. every_Fn_SOME [e] ⇒ every_Fn_SOME [mk_Ticks t tc n e]
Proof
  recInduct mk_Ticks_ind
  \\ rw[Once mk_Ticks_def]
  \\ rw[Once mk_Ticks_def]
  \\ fs[]
  \\ rw[Once mk_Ticks_def]
QED

Theorem every_Fn_vs_NONE_mk_Ticks:
   ∀t tc n e. every_Fn_vs_NONE [e] ⇒ every_Fn_vs_NONE [mk_Ticks t tc n e]
Proof
  recInduct mk_Ticks_ind
  \\ rw[Once mk_Ticks_def]
  \\ rw[Once mk_Ticks_def]
  \\ fs[]
  \\ rw[Once mk_Ticks_def]
QED

val val_approx_every_Fn_SOME_def = tDefine"val_approx_every_Fn_SOME"`
  (val_approx_every_Fn_SOME (Tuple _ vs) ⇔ EVERY val_approx_every_Fn_SOME vs) ∧
  (val_approx_every_Fn_SOME (Clos _ _ b _) ⇔ every_Fn_SOME [b]) ∧
  (val_approx_every_Fn_SOME _ ⇔ T)`
(wf_rel_tac`measure val_approx_size`
 \\ gen_tac \\ Induct \\ EVAL_TAC
 \\ rw[] \\ res_tac \\ rw[]);
val _ = export_rewrites["val_approx_every_Fn_SOME_def"];

Theorem val_approx_every_Fn_SOME_merge:
   ∀a b. val_approx_every_Fn_SOME a ∧ val_approx_every_Fn_SOME b ⇒
     val_approx_every_Fn_SOME (merge a b)
Proof
  recInduct merge_ind
  \\ rw[merge_def]
  \\ fs[EVERY_MEM,MAP2_MAP,MEM_MAP]
  \\ rw[]
  \\ imp_res_tac MEM_ZIP_MEM_MAP
  \\ rfs[UNCURRY]
QED

Theorem decide_inline_every_Fn_SOME:
   val_approx_every_Fn_SOME b ∧ decide_inline a b c d = inlD_LetInline e ⇒
   every_Fn_SOME [e]
Proof
  rw[decide_inline_def,CaseEq"val_approx",CaseEq"bool"]
  \\ fs[]
QED

val globals_approx_every_Fn_SOME_def = Define`
  globals_approx_every_Fn_SOME g =
    (∀c d. lookup c g = SOME d ⇒ val_approx_every_Fn_SOME d)`;

Theorem known_op_every_Fn_SOME:
   known_op op x y = (a,b) ∧
  EVERY val_approx_every_Fn_SOME x ∧
  globals_approx_every_Fn_SOME y
   ⇒ val_approx_every_Fn_SOME a ∧
     globals_approx_every_Fn_SOME b
Proof
  Cases_on`op` \\ fs[known_op_def]
  \\ rw[] \\ fsrw_tac[ETA_ss][CaseEq"prod",CaseEq"option",NULL_EQ,CaseEq"list",CaseEq"val_approx",CaseEq"bool"]
  \\ rw[] \\ fs[]
  \\ fs[EVERY_MEM,MEM_EL,PULL_EXISTS,globals_approx_every_Fn_SOME_def,lookup_insert]
  \\ rw[] \\ fs[]
  \\ TRY ( match_mp_tac val_approx_every_Fn_SOME_merge \\ fs[] )
  \\ last_x_assum match_mp_tac \\ fs[]
  \\ TRY asm_exists_tac \\ fs[]
  \\ intLib.COOPER_TAC
QED

Theorem clos_gen_no_inline_every_Fn_SOME:
   !(xs:(num,closLang$exp) alist) n x.
   EVERY val_approx_every_Fn_SOME (clos_gen_noinline x n xs)
Proof
  Induct \\ rw [clos_gen_noinline_def]
  \\ PairCases_on `h`
  \\ rw [clos_gen_noinline_def]
QED

Theorem known_every_Fn_SOME:
   ∀a b c d.
    every_Fn_SOME b ∧ EVERY val_approx_every_Fn_SOME c ∧
    globals_approx_every_Fn_SOME d
    ⇒
    every_Fn_SOME (MAP FST (FST (known a b c d))) ∧
    EVERY val_approx_every_Fn_SOME (MAP SND (FST (known a b c d))) ∧
    globals_approx_every_Fn_SOME (SND (known a b c d))
Proof
  recInduct known_ind
  \\ rw[known_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ imp_res_tac known_sing_EQ_E \\ rveq \\ fs[]
  \\ TRY ( match_mp_tac val_approx_every_Fn_SOME_merge \\ fs[] )
  \\ fs[IS_SOME_EXISTS, any_el_ALT, EVERY_REPLICATE] \\ rveq \\ fs[]
  >- ( rw[] \\ fs[EVERY_MEM,MEM_EL,PULL_EXISTS] )
  >- ( CASE_TAC \\ fs[] \\ CASE_TAC \\ fs[] )
  >- ( imp_res_tac known_op_every_Fn_SOME \\ fs[EVERY_REVERSE])
  >- ( imp_res_tac known_op_every_Fn_SOME \\ fs[EVERY_REVERSE])
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ TRY(reverse conj_tac >- fs[Once every_Fn_SOME_EVERY, EVERY_SNOC])
    \\ match_mp_tac every_Fn_SOME_mk_Ticks
    \\ imp_res_tac known_sing_EQ_E
    \\ fs[] \\ rveq
    \\ imp_res_tac decide_inline_every_Fn_SOME
    \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ imp_res_tac known_sing_EQ_E
    \\ fs[] \\ rveq
    \\ imp_res_tac decide_inline_every_Fn_SOME
    \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[])
  >- (
    rw[clos_approx_def]
    \\ CASE_TAC \\ fs[] )
  \\ fs [clos_gen_no_inline_every_Fn_SOME, Once every_Fn_SOME_EVERY]
  \\ fs [EVERY_MEM] \\ rw []
  \\ fs [MEM_MAP, FORALL_PROD, EXISTS_PROD, PULL_EXISTS] \\ rw []
  \\ first_x_assum drule \\ rw []
  \\ first_x_assum drule \\ rw []
  \\ rename1 `known c [pp] qq`
  \\ Cases_on `known c [pp] qq g`
  \\ imp_res_tac known_sing_EQ_E \\ fs []
QED

val val_approx_every_Fn_vs_NONE_def = tDefine"val_approx_every_Fn_vs_NONE"`
  (val_approx_every_Fn_vs_NONE (Tuple _ vs) ⇔ EVERY val_approx_every_Fn_vs_NONE vs) ∧
  (val_approx_every_Fn_vs_NONE (Clos _ _ b _) ⇔ every_Fn_vs_NONE [b]) ∧
  (val_approx_every_Fn_vs_NONE _ ⇔ T)`
(wf_rel_tac`measure val_approx_size`
 \\ gen_tac \\ Induct \\ EVAL_TAC
 \\ rw[] \\ res_tac \\ rw[]);
val _ = export_rewrites["val_approx_every_Fn_vs_NONE_def"];

Theorem val_approx_every_Fn_vs_NONE_merge:
   ∀a b. val_approx_every_Fn_vs_NONE a ∧ val_approx_every_Fn_vs_NONE b ⇒
     val_approx_every_Fn_vs_NONE (merge a b)
Proof
  recInduct clos_knownTheory.merge_ind
  \\ rw[clos_knownTheory.merge_def]
  \\ fs[EVERY_MEM,MAP2_MAP,MEM_MAP]
  \\ rw[]
  \\ imp_res_tac MEM_ZIP_MEM_MAP
  \\ rfs[UNCURRY]
QED

Theorem decide_inline_every_Fn_vs_NONE:
   val_approx_every_Fn_vs_NONE b ∧ decide_inline a b c d = inlD_LetInline e ⇒
   every_Fn_vs_NONE [e]
Proof
  rw[clos_knownTheory.decide_inline_def,CaseEq"val_approx",CaseEq"bool"]
  \\ fs[]
QED

val globals_approx_every_Fn_vs_NONE_def = Define`
  globals_approx_every_Fn_vs_NONE g =
    (∀c d. lookup c g = SOME d ⇒ val_approx_every_Fn_vs_NONE d)`;

Theorem known_op_every_Fn_vs_NONE:
   known_op op x y = (a,b) ∧
  EVERY val_approx_every_Fn_vs_NONE x ∧
  globals_approx_every_Fn_vs_NONE y
   ⇒ val_approx_every_Fn_vs_NONE a ∧
     globals_approx_every_Fn_vs_NONE b
Proof
  Cases_on`op` \\ fs[clos_knownTheory.known_op_def]
  \\ rw[] \\ fsrw_tac[ETA_ss][CaseEq"prod",CaseEq"option",NULL_EQ,CaseEq"list",CaseEq"val_approx",CaseEq"bool"]
  \\ rw[] \\ fs[]
  \\ fs[EVERY_MEM,MEM_EL,PULL_EXISTS,globals_approx_every_Fn_vs_NONE_def,lookup_insert]
  \\ rw[] \\ fs[]
  \\ TRY ( match_mp_tac val_approx_every_Fn_vs_NONE_merge \\ fs[] )
  \\ last_x_assum match_mp_tac \\ fs[]
  \\ TRY asm_exists_tac \\ fs[]
  \\ intLib.COOPER_TAC
QED

Theorem clos_gen_no_inline_every_Fn_vs_NONE:
   !(xs:(num,closLang$exp) alist) n x.
   EVERY val_approx_every_Fn_vs_NONE (clos_gen_noinline x n xs)
Proof
  Induct \\ rw [clos_knownTheory.clos_gen_noinline_def]
  \\ PairCases_on `h`
  \\ rw [clos_knownTheory.clos_gen_noinline_def]
QED

Theorem known_every_Fn_vs_NONE:
   ∀a b c d.
    every_Fn_vs_NONE b ∧ EVERY val_approx_every_Fn_vs_NONE c ∧
    globals_approx_every_Fn_vs_NONE d
    ⇒
    every_Fn_vs_NONE (MAP FST (FST (known a b c d))) ∧
    EVERY val_approx_every_Fn_vs_NONE (MAP SND (FST (known a b c d))) ∧
    globals_approx_every_Fn_vs_NONE (SND (known a b c d))
Proof
  recInduct clos_knownTheory.known_ind
  \\ rw[clos_knownTheory.known_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ imp_res_tac clos_knownTheory.known_sing_EQ_E \\ rveq \\ fs[]
  \\ TRY ( match_mp_tac val_approx_every_Fn_vs_NONE_merge \\ fs[] )
  \\ fs[IS_SOME_EXISTS, any_el_ALT, EVERY_REPLICATE] \\ rveq \\ fs[]
  >- ( rw[] \\ fs[EVERY_MEM,MEM_EL,PULL_EXISTS] )
  >- ( CASE_TAC \\ fs[] \\ CASE_TAC \\ fs[] )
  >- ( imp_res_tac known_op_every_Fn_vs_NONE \\ fs[EVERY_REVERSE])
  >- ( imp_res_tac known_op_every_Fn_vs_NONE \\ fs[EVERY_REVERSE])
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ TRY(reverse conj_tac >- fs[Once every_Fn_vs_NONE_EVERY, EVERY_SNOC])
    \\ match_mp_tac every_Fn_vs_NONE_mk_Ticks
    \\ imp_res_tac clos_knownTheory.known_sing_EQ_E
    \\ fs[] \\ rveq
    \\ imp_res_tac decide_inline_every_Fn_vs_NONE
    \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ imp_res_tac clos_knownTheory.known_sing_EQ_E
    \\ fs[] \\ rveq
    \\ imp_res_tac decide_inline_every_Fn_vs_NONE
    \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[])
  >- (
    rw[clos_knownTheory.clos_approx_def]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[] )
  \\ last_x_assum mp_tac
  \\ PURE_TOP_CASE_TAC
  \\ fs [EVERY_REPLICATE, clos_gen_no_inline_every_Fn_vs_NONE] \\ rw []
  \\ fs [Once every_Fn_vs_NONE_EVERY]
  \\ fs [EVERY_MEM] \\ rw []
  \\ fs [MEM_MAP, FORALL_PROD, EXISTS_PROD, PULL_EXISTS] \\ rw []
  \\ first_x_assum drule \\ rw []
  \\ first_x_assum drule \\ fs [MEM_REPLICATE_EQ] \\ rw []
  \\ rename1 `known c [pp] qq`
  \\ Cases_on `known c [pp] qq g`
  \\ imp_res_tac clos_knownTheory.known_sing_EQ_E \\ fs []
QED

Theorem known_every_Fn_vs_NONE:
   ∀a b c d.
    every_Fn_vs_NONE b ∧ EVERY val_approx_every_Fn_vs_NONE c ∧
    globals_approx_every_Fn_vs_NONE d
    ⇒
    every_Fn_vs_NONE (MAP FST (FST (known a b c d))) ∧
    EVERY val_approx_every_Fn_vs_NONE (MAP SND (FST (known a b c d))) ∧
    globals_approx_every_Fn_vs_NONE (SND (known a b c d))
Proof
  recInduct clos_knownTheory.known_ind
  \\ rw[clos_knownTheory.known_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ imp_res_tac clos_knownTheory.known_sing_EQ_E \\ rveq \\ fs[]
  \\ TRY ( match_mp_tac val_approx_every_Fn_vs_NONE_merge \\ fs[] )
  \\ fs[IS_SOME_EXISTS, any_el_ALT, EVERY_REPLICATE] \\ rveq \\ fs[]
  >- ( rw[] \\ fs[EVERY_MEM,MEM_EL,PULL_EXISTS] )
  >- ( CASE_TAC \\ fs[] \\ CASE_TAC \\ fs[] )
  >- ( imp_res_tac known_op_every_Fn_vs_NONE \\ fs[EVERY_REVERSE])
  >- ( imp_res_tac known_op_every_Fn_vs_NONE \\ fs[EVERY_REVERSE])
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ TRY(reverse conj_tac >- fs[Once every_Fn_vs_NONE_EVERY, EVERY_SNOC])
    \\ match_mp_tac every_Fn_vs_NONE_mk_Ticks
    \\ imp_res_tac clos_knownTheory.known_sing_EQ_E
    \\ fs[] \\ rveq
    \\ imp_res_tac decide_inline_every_Fn_vs_NONE
    \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ imp_res_tac clos_knownTheory.known_sing_EQ_E
    \\ fs[] \\ rveq
    \\ imp_res_tac decide_inline_every_Fn_vs_NONE
    \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[])
  >- (
    rw[clos_knownTheory.clos_approx_def]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[] )
  \\ last_x_assum mp_tac
  \\ PURE_TOP_CASE_TAC
  \\ fs [EVERY_REPLICATE, clos_gen_no_inline_every_Fn_vs_NONE] \\ rw []
  \\ fs [Once every_Fn_vs_NONE_EVERY]
  \\ fs [EVERY_MEM] \\ rw []
  \\ fs [MEM_MAP, FORALL_PROD, EXISTS_PROD, PULL_EXISTS] \\ rw []
  \\ first_x_assum drule \\ rw []
  \\ first_x_assum drule \\ fs [MEM_REPLICATE_EQ] \\ rw []
  \\ rename1 `known c [pp] qq`
  \\ Cases_on `known c [pp] qq g`
  \\ imp_res_tac clos_knownTheory.known_sing_EQ_E \\ fs []
QED

(* no_Labels *)

val val_approx_no_Labels_def = tDefine "val_approx_no_Labels" `
  (val_approx_no_Labels (ClosNoInline m n) <=> T) /\
  (val_approx_no_Labels (Clos m n e s) <=> no_Labels e) /\
  (val_approx_no_Labels (Tuple tag vas) <=> EVERY val_approx_no_Labels vas) /\
  (val_approx_no_Labels _ <=> T)
` (WF_REL_TAC `measure val_approx_size`
   \\ Induct_on `vas` \\ simp []
   \\ rw [] THEN1 simp [val_approx_size_def]
   \\ first_x_assum drule
   \\ disch_then (qspec_then `tag` assume_tac)
   \\ fs [val_approx_size_def]);

Theorem decide_inline_no_Labels:
   val_approx_no_Labels b ∧ decide_inline a b c d = inlD_LetInline e ⇒
   no_Labels e
Proof
  rw[decide_inline_def,CaseEq"val_approx",CaseEq"bool"]
  \\ fs[val_approx_no_Labels_def]
QED

val globals_approx_no_Labels_def = Define`
  globals_approx_no_Labels g =
    (∀c d. lookup c g = SOME d ⇒ val_approx_no_Labels d)`;

Theorem val_approx_no_Labels_merge:
   ∀a b. val_approx_no_Labels a ∧ val_approx_no_Labels b ⇒
         val_approx_no_Labels (merge a b)
Proof
  recInduct clos_knownTheory.merge_ind
  \\ rw[clos_knownTheory.merge_def,val_approx_no_Labels_def]
  \\ fs[EVERY_MEM,MAP2_MAP,MEM_MAP]
  \\ rw[] \\ imp_res_tac MEM_ZIP_MEM_MAP
  \\ rfs[UNCURRY]
QED

Theorem known_op_no_Labels:
   known_op op x y = (a,b) ∧
  EVERY val_approx_no_Labels x ∧
  globals_approx_no_Labels y
   ⇒ val_approx_no_Labels a ∧
     globals_approx_no_Labels b
Proof
  Cases_on`op` \\ fs[clos_knownTheory.known_op_def] \\ rw[]
  \\ fsrw_tac[ETA_ss][CaseEq"prod",CaseEq"option",NULL_EQ,
                      CaseEq"list",CaseEq"val_approx",CaseEq"bool"]
  \\ rw[] \\ fs[val_approx_no_Labels_def]
  \\ fs[EVERY_MEM,MEM_EL,PULL_EXISTS,globals_approx_no_Labels_def,lookup_insert]
  \\ rw[] \\ fs[]
  \\ TRY ( match_mp_tac val_approx_no_Labels_merge \\ fs[] )
  \\ last_x_assum match_mp_tac \\ fs[]
  \\ TRY asm_exists_tac \\ fs[]
  \\ intLib.COOPER_TAC
QED

Theorem no_Labels_mk_Ticks:
   ∀t tc n e. no_Labels e ⇒ no_Labels (mk_Ticks t tc n e)
Proof
  recInduct mk_Ticks_ind
  \\ rw[Once mk_Ticks_def]
  \\ rw[Once mk_Ticks_def]
  \\ fs[] \\ rw[Once mk_Ticks_def]
QED

Theorem clos_gen_no_inline_no_Labels:
   !(xs:(num,closLang$exp) alist) n x.
   EVERY val_approx_no_Labels (clos_gen_noinline x n xs)
Proof
  Induct \\ rw [clos_gen_noinline_def]
  \\ PairCases_on `h`
  \\ rw [clos_gen_noinline_def,val_approx_no_Labels_def]
QED

Theorem known_no_Labels:
   ∀a b c d.
    EVERY no_Labels b ∧ EVERY val_approx_no_Labels c ∧
    globals_approx_no_Labels d
    ⇒
    EVERY no_Labels (MAP FST (FST (known a b c d))) ∧
    EVERY val_approx_no_Labels (MAP SND (FST (known a b c d))) ∧
    globals_approx_no_Labels (SND (known a b c d))
Proof
  recInduct clos_knownTheory.known_ind
  \\ rw[clos_knownTheory.known_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ imp_res_tac clos_knownTheory.known_sing_EQ_E
  \\ rveq \\ fs[] \\ rveq \\ fs[]
  \\ fs [val_approx_no_Labels_def]
  \\ TRY (match_mp_tac val_approx_no_Labels_merge \\ fs [])
  \\ fs[IS_SOME_EXISTS, any_el_ALT, EVERY_REPLICATE] \\ rveq \\ fs[]
  >- (rw[] \\ fs[EVERY_MEM,MEM_EL,PULL_EXISTS,val_approx_no_Labels_def] )
  >- (IF_CASES_TAC \\ fs[] \\ CASE_TAC \\ fs[] )
  \\ fs [val_approx_no_Labels_def]
  >- (imp_res_tac known_op_no_Labels \\ fs[EVERY_REVERSE])
  >- (imp_res_tac known_op_no_Labels \\ fs[EVERY_REVERSE])
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ TRY(reverse conj_tac \\ fs[Once every_Fn_vs_NONE_EVERY, EVERY_SNOC])
    \\ match_mp_tac no_Labels_mk_Ticks
    \\ imp_res_tac clos_knownTheory.known_sing_EQ_E
    \\ fs[] \\ rveq
    \\ imp_res_tac decide_inline_no_Labels
    \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[val_approx_no_Labels_def]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ imp_res_tac clos_knownTheory.known_sing_EQ_E
    \\ fs[] \\ rveq
    \\ imp_res_tac decide_inline_no_Labels
    \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[val_approx_no_Labels_def]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[val_approx_no_Labels_def])
  >- (
    rw[clos_knownTheory.clos_approx_def,val_approx_no_Labels_def]
    \\ TOP_CASE_TAC \\ fs[val_approx_no_Labels_def]
    \\ TOP_CASE_TAC \\ fs[val_approx_no_Labels_def] )
  \\ last_x_assum mp_tac
  \\ PURE_TOP_CASE_TAC
  \\ fs [EVERY_REPLICATE, clos_gen_no_inline_no_Labels] \\ rw []
  \\ fs [EVERY_MEM] \\ rw []
  \\ fs [MEM_MAP, FORALL_PROD, EXISTS_PROD, PULL_EXISTS] \\ rw []
  \\ fs [val_approx_no_Labels_def]
  \\ first_x_assum drule \\ rw []
  \\ first_x_assum drule \\ fs [MEM_REPLICATE_EQ] \\ rw []
  \\ fs [val_approx_no_Labels_def]
  \\ rename1 `known c [pp] qq`
  \\ Cases_on `known c [pp] qq g`
  \\ imp_res_tac clos_knownTheory.known_sing_EQ_E \\ fs []
QED

Theorem compile_no_Labels:
   compile (SOME c) xs = (res,ys) /\ EVERY no_Labels xs ==>
    ?c1. res = SOME c1 /\ EVERY no_Labels ys /\
         globals_approx_no_Labels c1.val_approx_spt
Proof
  fs [clos_knownTheory.compile_def,clos_fvsTheory.compile_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ strip_tac \\ rveq \\ fs []
  \\ qspecl_then [`c`,`remove_fvs 0 xs`,`[]`,`LN`]
         mp_tac known_no_Labels
  \\ fs [clos_fvsProofTheory.remove_fvs_no_Labels]
  \\ impl_tac THEN1
    (fs [globals_approx_no_Labels_def,lookup_def])
  \\ metis_tac [clos_ticksProofTheory.remove_ticks_no_Labels,
                clos_letopProofTheory.let_op_no_Labels]
QED

(* obeys_max_app *)

val val_approx_obeys_max_app_def = tDefine "val_approx_obeys_max_app" `
  (val_approx_obeys_max_app k (ClosNoInline m n) <=> T) /\
  (val_approx_obeys_max_app k (Clos m n e s) <=> obeys_max_app k e) /\
  (val_approx_obeys_max_app k (Tuple tag vas) <=> EVERY (val_approx_obeys_max_app k) vas) /\
  (val_approx_obeys_max_app k _ <=> T)
` (WF_REL_TAC `measure (val_approx_size o SND)`
   \\ Induct_on `vas` \\ simp []
   \\ rw [] THEN1 simp [val_approx_size_def]
   \\ first_x_assum drule
   \\ disch_then (qspec_then `tag` assume_tac)
   \\ fs [val_approx_size_def]);

Theorem decide_inline_obeys_max_app:
   val_approx_obeys_max_app k b ∧ decide_inline a b c d = inlD_LetInline e ⇒
   obeys_max_app k e
Proof
  rw[decide_inline_def,CaseEq"val_approx",CaseEq"bool"]
  \\ fs[val_approx_obeys_max_app_def]
QED

val globals_approx_obeys_max_app_def = Define`
  globals_approx_obeys_max_app k g =
    (∀c d. lookup c g = SOME d ⇒ val_approx_obeys_max_app k d)`;

Theorem val_approx_obeys_max_app_merge:
   ∀a b. val_approx_obeys_max_app k a ∧ val_approx_obeys_max_app k b ⇒
         val_approx_obeys_max_app k (merge a b)
Proof
  recInduct clos_knownTheory.merge_ind
  \\ rw[clos_knownTheory.merge_def,val_approx_obeys_max_app_def]
  \\ fs[EVERY_MEM,MAP2_MAP,MEM_MAP]
  \\ rw[] \\ imp_res_tac MEM_ZIP_MEM_MAP
  \\ rfs[UNCURRY]
QED

Theorem known_op_obeys_max_app:
   known_op op x y = (a,b) ∧
  EVERY (val_approx_obeys_max_app k) x ∧
  globals_approx_obeys_max_app k y
   ⇒ val_approx_obeys_max_app k a ∧
     globals_approx_obeys_max_app k b
Proof
  Cases_on`op` \\ fs[clos_knownTheory.known_op_def] \\ rw[]
  \\ fsrw_tac[ETA_ss][CaseEq"prod",CaseEq"option",NULL_EQ,
                      CaseEq"list",CaseEq"val_approx",CaseEq"bool"]
  \\ rw[] \\ fs[val_approx_obeys_max_app_def]
  \\ fs[EVERY_MEM,MEM_EL,PULL_EXISTS,globals_approx_obeys_max_app_def,lookup_insert]
  \\ rw[] \\ fs[]
  \\ TRY ( match_mp_tac val_approx_obeys_max_app_merge \\ fs[] )
  \\ last_x_assum match_mp_tac \\ fs[]
  \\ TRY asm_exists_tac \\ fs[]
  \\ intLib.COOPER_TAC
QED

Theorem obeys_max_app_mk_Ticks:
   ∀t tc n e. obeys_max_app k e ⇒ obeys_max_app k (mk_Ticks t tc n e)
Proof
  recInduct mk_Ticks_ind
  \\ rw[Once mk_Ticks_def]
  \\ rw[Once mk_Ticks_def]
  \\ fs[] \\ rw[Once mk_Ticks_def]
QED

Theorem clos_gen_no_inline_obeys_max_app:
   !(xs:(num,closLang$exp) alist) n x.
   EVERY (val_approx_obeys_max_app k) (clos_gen_noinline x n xs)
Proof
  Induct \\ rw [clos_gen_noinline_def]
  \\ PairCases_on `h`
  \\ rw [clos_gen_noinline_def,val_approx_obeys_max_app_def]
QED

Theorem known_IMP_LENGTH:
   known c xs vs g = (ys,g') ==> LENGTH ys = LENGTH xs
Proof
  metis_tac [known_LENGTH,FST]
QED

Theorem known_obeys_max_app:
   ∀a b c d.
    EVERY (obeys_max_app k) b ∧ EVERY (val_approx_obeys_max_app k) c ∧
    globals_approx_obeys_max_app k d
    ⇒
    EVERY (obeys_max_app k) (MAP FST (FST (known a b c d))) ∧
    EVERY (val_approx_obeys_max_app k) (MAP SND (FST (known a b c d))) ∧
    globals_approx_obeys_max_app k (SND (known a b c d))
Proof
  recInduct clos_knownTheory.known_ind
  \\ rw[clos_knownTheory.known_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ imp_res_tac clos_knownTheory.known_sing_EQ_E
  \\ rveq \\ fs[] \\ rveq \\ fs[]
  \\ fs [val_approx_obeys_max_app_def]
  \\ TRY (match_mp_tac val_approx_obeys_max_app_merge \\ fs [])
  \\ fs[IS_SOME_EXISTS, any_el_ALT, EVERY_REPLICATE] \\ rveq \\ fs[]
  >- (rw[] \\ fs[EVERY_MEM,MEM_EL,PULL_EXISTS,val_approx_obeys_max_app_def] )
  >- (IF_CASES_TAC \\ fs[] \\ CASE_TAC \\ fs[] )
  \\ fs [val_approx_obeys_max_app_def]
  >- (imp_res_tac known_op_obeys_max_app \\ fs[EVERY_REVERSE])
  >- (imp_res_tac known_op_obeys_max_app \\ fs[EVERY_REVERSE])
  \\ imp_res_tac known_IMP_LENGTH \\ fs []
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ TRY(reverse conj_tac \\ fs[Once every_Fn_vs_NONE_EVERY, EVERY_SNOC])
    \\ match_mp_tac obeys_max_app_mk_Ticks
    \\ imp_res_tac clos_knownTheory.known_sing_EQ_E
    \\ fs[] \\ rveq
    \\ imp_res_tac decide_inline_obeys_max_app
    \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[val_approx_obeys_max_app_def]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ imp_res_tac clos_knownTheory.known_sing_EQ_E
    \\ fs[] \\ rveq
    \\ imp_res_tac decide_inline_obeys_max_app
    \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[val_approx_obeys_max_app_def]
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ CASE_TAC \\ fs[val_approx_obeys_max_app_def])
  >- (
    rw[clos_knownTheory.clos_approx_def,val_approx_obeys_max_app_def]
    \\ TOP_CASE_TAC \\ fs[val_approx_obeys_max_app_def]
    \\ TOP_CASE_TAC \\ fs[val_approx_obeys_max_app_def] )
  \\ last_x_assum mp_tac
  \\ PURE_TOP_CASE_TAC
  \\ fs [EVERY_REPLICATE, clos_gen_no_inline_obeys_max_app] \\ rw []
  \\ fs [EVERY_MEM] \\ rw []
  \\ fs [MEM_MAP, FORALL_PROD, EXISTS_PROD, PULL_EXISTS] \\ rw []
  \\ fs [val_approx_obeys_max_app_def]
  \\ first_x_assum drule \\ rw []
  \\ first_x_assum drule \\ fs [MEM_REPLICATE_EQ] \\ rw []
  \\ fs [val_approx_obeys_max_app_def]
  \\ rename1 `known c [pp] qq`
  \\ Cases_on `known c [pp] qq g`
  \\ imp_res_tac clos_knownTheory.known_sing_EQ_E \\ fs []
QED

Theorem compile_obeys_max_app:
   compile (SOME c) xs = (res,ys) /\ EVERY (obeys_max_app k) xs ==>
    ?c1. res = SOME c1 /\ EVERY (obeys_max_app k) ys /\
         globals_approx_obeys_max_app k c1.val_approx_spt
Proof
  fs [clos_knownTheory.compile_def,clos_fvsTheory.compile_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ strip_tac \\ rveq \\ fs []
  \\ qspecl_then [`c`,`remove_fvs 0 xs`,`[]`,`LN`]
         mp_tac known_obeys_max_app
  \\ fs [clos_fvsProofTheory.remove_fvs_obeys_max_app]
  \\ impl_tac THEN1 (fs [globals_approx_obeys_max_app_def,lookup_def])
  \\ metis_tac [clos_ticksProofTheory.remove_ticks_obeys_max_app,
                clos_letopProofTheory.let_op_obeys_max_app]
QED

(* names *)

Theorem get_code_labels_mk_Ticks[simp]:
   ∀a b c d. get_code_labels (mk_Ticks a b c d) = get_code_labels d
Proof
  recInduct clos_knownTheory.mk_Ticks_ind
  \\ rw[]
  \\ rw[Once clos_knownTheory.mk_Ticks_def]
QED

(*
val val_approx_bodies_def = tDefine"val_approx_bodies_def"`
  val_approx_bodies [] = [] ∧
  val_approx_bodies [ClosNoInline _ _] = [] ∧
  val_approx_bodies [Clos _ _ body _] = [body] ∧
  val_approx_bodies [Tuple _ ls] = val_approx_bodies ls ∧
  val_approx_bodies [_] = [] ∧
  val_approx_bodies (x::ls) = val_approx_bodies [x] ++ val_approx_bodies ls`
 (wf_rel_tac`measure val_approx1_size`);

val val_approx_bodies_def =
  val_approx_bodies_def
  |> SIMP_RULE(srw_ss()++ETA_ss)[]
  |> curry save_thm "val_approx_bodies_def[simp,compute]";

Theorem val_approx_bodies_cons:
   val_approx_bodies (x::ys) = val_approx_bodies [x] ++ val_approx_bodies ys
Proof
  Cases_on`ys` \\ rw[]
QED

Theorem val_approx_bodies_append:
   ∀l1 l2. val_approx_bodies (l1 ++ l2) = val_approx_bodies l1 ++ val_approx_bodies l2
Proof
  Induct
  \\ rw[Once val_approx_bodies_cons]
  \\ rw[Once val_approx_bodies_cons,SimpRHS]
QED

Theorem val_approx_bodies_map:
   ∀xs. val_approx_bodies (MAP f xs) = FLAT (MAP (λx. val_approx_bodies [f x]) xs)
Proof
  Induct \\ rw[] \\ rw[Once val_approx_bodies_cons]
QED

Theorem app_call_dests_val_approx_bodies_merge:
   ∀a1 a2. app_call_dests x (val_approx_bodies [merge a1 a2]) ⊆
           app_call_dests x (val_approx_bodies [a1]) ∪
           app_call_dests x (val_approx_bodies [a2])
Proof
  recInduct merge_ind \\ rw[]
  \\ simp[Once(app_call_dests_map |> Q.ISPEC`ls:closLang$exp list`
               |> Q.GEN`f` |> Q.SPEC`I` |> SIMP_RULE (srw_ss()) [])]
  \\ fs[MAP2_MAP, val_approx_bodies_map]
  \\ simp[SUBSET_DEF, MEM_MAP, MEM_FLAT, PULL_EXISTS]
  \\ rw[MEM_ZIP] \\ fs[]
  \\ first_x_assum(qspecl_then[`EL n xs`,`EL n ys`]mp_tac)
  \\ impl_tac >- metis_tac[MEM_EL]
  \\ simp[Once(app_call_dests_map |> Q.ISPEC`ls:closLang$exp list`
               |> Q.GEN`f` |> Q.SPEC`I` |> SIMP_RULE (srw_ss()) [])]
  \\ simp[SUBSET_DEF, MEM_MAP, PULL_EXISTS]
  \\ disch_then drule \\ rw[] >| [disj1_tac, disj2_tac]
  \\ pop_assum mp_tac
  \\ simp[Once(app_call_dests_map |> Q.ISPEC`ls:closLang$exp list`
               |> Q.GEN`f` |> Q.SPEC`I` |> SIMP_RULE (srw_ss()) [])]
  \\ rw[MEM_MAP]
  \\ simp[Once(val_approx_bodies_map |> Q.ISPEC`ls:val_approx list`
               |> Q.GEN`f` |> Q.SPEC`I` |> SIMP_RULE (srw_ss()) [])]
  \\ simp[Once(app_call_dests_map |> Q.ISPEC`ls:closLang$exp list`
               |> Q.GEN`f` |> Q.SPEC`I` |> SIMP_RULE (srw_ss()) [])]
  \\ rw[MEM_MAP, MEM_FLAT, PULL_EXISTS]
  \\ asm_exists_tac \\ rw[]
  \\ metis_tac[MEM_EL]
QED
*)

(*
val val_approx_dests_def = tDefine"val_approx_dests_def"`
  val_approx_dests a [] = {} ∧
  val_approx_dests a [ClosNoInline loc _] = {loc} ∧
  val_approx_dests a [Clos loc _ body _] = loc INSERT app_call_dests a [body] ∧
  val_approx_dests a [Tuple _ ls] = val_approx_dests a ls ∧
  val_approx_dests a [_] = {} ∧
  val_approx_dests a (x::ls) = val_approx_dests a [x] ∪ val_approx_dests a ls`
 (wf_rel_tac`measure (val_approx1_size o SND)`);

val val_approx_dests_def =
  val_approx_dests_def
  |> SIMP_RULE(srw_ss()++ETA_ss)[]
  |> curry save_thm "val_approx_dests_def[simp,compute]";

Theorem val_approx_dests_cons:
   val_approx_dests a (x::ys) = val_approx_dests a [x] ∪ val_approx_dests a ys
Proof
  Cases_on`ys` \\ rw[]
QED

Theorem val_approx_dests_append:
   ∀l1 l2. val_approx_dests a (l1 ++ l2) = val_approx_dests a l1 ∪ val_approx_dests a l2
Proof
  Induct
  \\ rw[Once val_approx_dests_cons]
  \\ rw[Once val_approx_dests_cons,SimpRHS]
  \\ rw[UNION_ASSOC]
QED

Theorem val_approx_dests_reverse:
   ∀ls. val_approx_dests x (REVERSE ls) = val_approx_dests x ls
Proof
  Induct \\ simp[val_approx_dests_append]
  \\ simp[Once val_approx_dests_cons, SimpRHS]
  \\ rw[EXTENSION] \\ metis_tac[]
QED

Theorem val_approx_dests_map:
   ∀xs. val_approx_dests a (MAP f xs) = BIGUNION (set (MAP (λx. val_approx_dests a [f x]) xs))
Proof
  Induct \\ rw[] \\ rw[Once val_approx_dests_cons]
QED

Theorem val_approx_dests_replicate:
   val_approx_dests x (REPLICATE n y) = if 0 < n then val_approx_dests x [y] else {}
Proof
  `n = LENGTH (GENLIST ARB n)` by simp[]
  \\ pop_assum SUBST1_TAC
  \\ simp[GSYM MAP_K_REPLICATE]
  \\ simp[val_approx_dests_map]
  \\ simp[Once EXTENSION, PULL_EXISTS, MEM_MAP, MEM_GENLIST]
  \\ rw[] \\ metis_tac[]
QED

Theorem val_approx_dests_merge:
   ∀x y. val_approx_dests a [merge x y] ⊆ val_approx_dests a [x] ∪ val_approx_dests a [y]
Proof
  recInduct clos_knownTheory.merge_ind
  \\ rw[clos_knownTheory.merge_def]
  \\ fs[SUBSET_DEF, PULL_EXISTS, MEM_MAP, MAP2_MAP, FORALL_PROD, MEM_ZIP]
  \\ rw[] \\ fs[MEM_EL, PULL_EXISTS]
  \\ fs[val_approx_dests_map, MEM_MAP]
  \\ rfs[MEM_ZIP] \\ rw[] \\ fs[]
  \\ first_x_assum drule \\ simp[]
  \\ disch_then drule
  \\ disch_then drule
  \\ rw[] >| [disj1_tac , disj2_tac ]
  \\ simp[Once(val_approx_dests_map |> Q.ISPEC`ls:val_approx list`
               |> Q.GEN`f` |> Q.SPEC`I` |> SIMP_RULE (srw_ss()) [])]
  \\ rw[MEM_MAP, MEM_EL, PULL_EXISTS]
  \\ metis_tac[]
QED

val val_approx_dests_to_sing =
  (val_approx_dests_map |> Q.ISPEC`ls:val_approx list`
               |> Q.GEN`f` |> Q.SPEC`I` |> SIMP_RULE (srw_ss()) [])

Theorem app_call_dests_mk_Ticks[simp]:
   ∀a b c d. app_call_dests x [mk_Ticks a b c d] = app_call_dests x [d]
Proof
  recInduct clos_knownTheory.mk_Ticks_ind
  \\ rw[]
  \\ rw[Once clos_knownTheory.mk_Ticks_def]
QED

Theorem known_app_call_dests:
   ∀a b c d e f.
    known a b c d = (e,f)
    ⇒
    app_call_dests x (MAP FST e) ∪
    val_approx_dests x (MAP SND e) ∪
    val_approx_dests x (toList f)
    ⊆
    app_call_dests x b ∪
    val_approx_dests x c ∪
    val_approx_dests x (toList d)
Proof
  recInduct clos_knownTheory.known_ind
  \\ rpt conj_tac
  \\ simp[clos_knownTheory.known_def]
  \\ TRY (gen_tac \\ rpt gen_tac \\ strip_tac)
  \\ TRY (gen_tac \\ rpt gen_tac \\ strip_tac)
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  >- (
    fs[app_call_dests_append, val_approx_dests_append]
    \\ fs[SUBSET_DEF] \\ metis_tac[] )
  \\ imp_res_tac known_sing_EQ_E \\ rveq \\ fs[]
  >- (
    rw[any_el_ALT]
    \\ pop_assum mp_tac
    \\ qid_spec_tac`v`
    \\ Induct_on`vs`
    \\ simp[]
    \\ gen_tac \\ Cases \\ simp[]
    \\ rw[Once val_approx_dests_cons, SimpR``(SUBSET)``, app_call_dests_append]
    \\ fs[SUBSET_DEF] \\ metis_tac[] )
  >- (
    rveq
    \\ simp[GSYM CONJ_ASSOC]
    \\ conj_tac >- ( fs[SUBSET_DEF] \\ metis_tac[] )
    \\ conj_tac >- ( fs[SUBSET_DEF] \\ metis_tac[] )
    \\ conj_tac >- ( fs[SUBSET_DEF] \\ metis_tac[] )
    \\ reverse conj_tac >- ( fs[SUBSET_DEF] \\ metis_tac[] )
    \\ match_mp_tac SUBSET_TRANS
    \\ qspecl_then[`x`,`a2`,`a3`]mp_tac (Q.GEN`a`val_approx_dests_merge)
    \\ strip_tac
    \\ asm_exists_tac
    \\ fs[SUBSET_DEF] \\ metis_tac[] )
  >- (
    rveq \\ fs[val_approx_dests_append, app_call_dests_append]
    \\ fs[SUBSET_DEF] \\ metis_tac[] )
  >- (
    rveq
    \\ simp[GSYM CONJ_ASSOC]
    \\ conj_tac >- ( fs[SUBSET_DEF] \\ metis_tac[] )
    \\ fs[Q.SPEC`Other`(Q.GEN`x`val_approx_dests_cons)]
    \\ conj_tac >- ( fs[SUBSET_DEF] \\ metis_tac[] )
    \\ reverse conj_tac >- ( fs[SUBSET_DEF] \\ metis_tac[] )
    \\ match_mp_tac SUBSET_TRANS
    \\ qspecl_then[`x`,`a1`,`a2`]mp_tac (Q.GEN`a`val_approx_dests_merge)
    \\ strip_tac
    \\ asm_exists_tac
    \\ fs[SUBSET_DEF] \\ metis_tac[] )
  >- ( rw[] \\ fs[SUBSET_DEF] \\ metis_tac[] )
  >- (
    Cases_on`op` \\ fs[isGlobal_def, known_op_def, NULL_EQ]
    \\ fs[CaseEq"bool", CaseEq"option", CaseEq"list", CaseEq"val_approx"] \\ rveq \\ fs[gO_destApx_def]
    \\ fs[Once SWAP_REVERSE_SYM, val_approx_dests_append]
    >- (
      qpat_x_assum`_ ⊆ _`mp_tac
      \\ simp[Once(val_approx_dests_map |> Q.ISPEC`ls:val_approx list`
                   |> Q.GEN`f` |> Q.SPEC`I` |> SIMP_RULE (srw_ss()) [])]
      \\ simp[SUBSET_DEF, MEM_MAP, PULL_EXISTS, MEM_toList]
      \\ strip_tac
      \\ conj_tac
      >- ( rw[] \\ every_case_tac \\ fs[] )
      \\ rw[]
      \\ first_x_assum drule
      \\ disch_then drule
      \\ rw[] )
    >- (
      simp[Once(val_approx_dests_map |> Q.ISPEC`ls:val_approx list`
                 |> Q.GEN`f` |> Q.SPEC`I` |> SIMP_RULE (srw_ss()) [])]
      \\ fs[SUBSET_DEF, PULL_EXISTS, MEM_MAP, MEM_toList, lookup_insert]
      \\ rw[]
      \\ first_x_assum irule
      \\ simp[Once val_approx_dests_to_sing, MEM_MAP, PULL_EXISTS, MEM_toList]
      \\ metis_tac[] )
    >- (
      simp[Once val_approx_dests_to_sing]
      \\ fs[SUBSET_DEF, PULL_EXISTS, MEM_MAP, MEM_toList, lookup_insert]
      \\ rw[]
      >- (
        (val_approx_dests_merge |> SIMP_RULE(srw_ss())[SUBSET_DEF] |> drule)
        \\ reverse(rw[]) >- metis_tac[]
        \\ first_x_assum irule
        \\ simp[Once val_approx_dests_to_sing, MEM_MAP, PULL_EXISTS, MEM_toList]
        \\ metis_tac[] )
      \\ first_x_assum irule
      \\ simp[Once val_approx_dests_to_sing, MEM_MAP, PULL_EXISTS, MEM_toList]
      \\ metis_tac[] )
    >- fs[val_approx_dests_reverse]
    >- (
      qmatch_goalsub_rename_tac`EL _ ls`
      \\ qpat_x_assum`val_approx_dests _ ls ⊆ _`mp_tac
      \\ simp[Once val_approx_dests_to_sing, MEM_MAP, PULL_EXISTS, MEM_toList]
      \\ simp[SUBSET_DEF, PULL_EXISTS, MEM_MAP, MEM_toList]
      \\ simp[MEM_EL, PULL_EXISTS]
      \\ rw[]
      \\ first_x_assum irule
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ intLib.COOPER_TAC )
    )
  >-  (
    rveq
    \\ fs[CaseEq"inliningDecision"] \\ rveq \\ fs[]
    >- (
      Cases_on`loc_opt` \\ rw[]
      \\ fs[SUBSET_DEF] \\ metis_tac[] )
    >- (
      IF_CASES_TAC \\ fs[]
      >- ( fs[SUBSET_DEF] \\ metis_tac[] )
      \\ reverse conj_tac >- ( fs[SUBSET_DEF] \\ metis_tac[] )
      \\ reverse conj_tac >- ( fs[SUBSET_DEF] \\ metis_tac[] )
      \\ reverse conj_tac >- ( fs[SUBSET_DEF] \\ metis_tac[] )
      \\ fs[decide_inline_def, CaseEq"val_approx", CaseEq"bool"] \\ rveq \\ fs[]
      \\ fs[SUBSET_DEF] \\ metis_tac[] )
    >- (
      rpt(pairarg_tac \\ fs[])
      \\ imp_res_tac known_sing_EQ_E \\ fs[] \\ rveq
      \\ fs[decide_inline_def, CaseEq"val_approx"] \\ rveq \\ fs[]
      \\ fs[CaseEq"bool"] \\ rveq \\ fs[app_call_dests_append, val_approx_dests_append]
      \\ rw[] \\ fs[SUBSET_DEF] \\ metis_tac[] ))
  >- (
    rveq
    \\ fs[val_approx_dests_append, val_approx_dests_replicate]
    \\ PURE_CASE_TAC \\ fs[]
    \\ fs[clos_approx_def]
    \\ PURE_CASE_TAC \\ fs[]
    \\ fs[SUBSET_DEF] )
  >- (
    rveq
    \\ fs[val_approx_dests_append, app_call_dests_append, val_approx_dests_replicate]
    \\ PURE_CASE_TAC \\ fs[val_approx_dests_replicate, clos_gen_noinline_eq]
    >- (
      reverse conj_tac >- ( fs[SUBSET_DEF] \\ metis_tac[] )
      \\ reverse conj_tac >- ( fs[SUBSET_DEF] \\ metis_tac[] )
      \\ reverse conj_tac >- ( fs[SUBSET_DEF] \\ metis_tac[] )
      \\ simp[Once(app_call_dests_map |> Q.ISPEC`ls:closLang$exp list`
                   |> Q.GEN`f` |> Q.SPEC`I` |> SIMP_RULE (srw_ss()) [])]
      \\ fs[SUBSET_DEF, MEM_MAP, PULL_EXISTS, FORALL_PROD]
      \\ rw[]
      \\ first_x_assum drule
      \\ qmatch_goalsub_abbrev_tac`known aa bb cc dd`
      \\ Cases_on`known aa bb cc dd`
      \\ unabbrev_all_tac \\ fs[] \\ rw[]
      \\ imp_res_tac known_sing_EQ_E \\ fs[] \\ rveq
      \\ simp[Once(app_call_dests_map |> Q.ISPEC`ls:closLang$exp list`
                   |> Q.GEN`f` |> Q.SPEC`I` |> SIMP_RULE (srw_ss()) [])]
      \\ simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD]
      \\ metis_tac[] )
    \\ last_x_assum mp_tac
    \\ qmatch_goalsub_abbrev_tac`val_approx_dests x gn`
    \\ `val_approx_dests x gn = {}`
    by (
      simp[Once val_approx_dests_to_sing]
      \\ simp[Abbr`gn`, MAP_GENLIST, Once EXTENSION, MEM_GENLIST]
      \\ Cases_on`LENGTH fns` \\ simp[]
      \\ metis_tac[prim_recTheory.LESS_0] )
    \\ fs[]
    \\ strip_tac
    \\ reverse conj_tac >- ( fs[SUBSET_DEF] \\ metis_tac[] )
    \\ reverse conj_tac >- ( fs[SUBSET_DEF] \\ metis_tac[] )
    \\ reverse conj_tac >- ( fs[SUBSET_DEF] \\ metis_tac[] )
    \\ simp[Once(app_call_dests_map |> Q.ISPEC`ls:closLang$exp list`
                 |> Q.GEN`f` |> Q.SPEC`I` |> SIMP_RULE (srw_ss()) [])]
    \\ fs[SUBSET_DEF, MEM_MAP, PULL_EXISTS, FORALL_PROD]
    \\ rw[]
    \\ first_x_assum drule
    \\ qmatch_goalsub_abbrev_tac`known aa bb cc dd`
    \\ Cases_on`known aa bb cc dd`
    \\ unabbrev_all_tac \\ fs[] \\ rw[]
    \\ imp_res_tac known_sing_EQ_E \\ fs[] \\ rveq
    \\ simp[Once(app_call_dests_map |> Q.ISPEC`ls:closLang$exp list`
                 |> Q.GEN`f` |> Q.SPEC`I` |> SIMP_RULE (srw_ss()) [])]
    \\ simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD]
    \\ metis_tac[] )
QED

Theorem compile_locs:
   clos_known$compile b number_code = (kc,known_code) /\
    call_dests number_code = ∅ /\ app_dests number_code = ∅ /\
    (case b of SOME x => (∀n. val_approx_dests (SOME n) (toList x.val_approx_spt) = {}) | _ => T) ==>
    call_dests known_code = ∅ /\
    app_dests known_code ⊆ set (code_locs known_code)
Proof
  strip_tac
  \\ Cases_on`b` \\ fs[clos_knownTheory.compile_def]
  \\ rveq \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ simp[clos_letopProofTheory.code_locs_let_op,
          clos_ticksProofTheory.code_locs_remove_ticks]
  \\ drule (GEN_ALL known_app_call_dests)
  \\ disch_then(fn th => assume_tac (SPEC``SOME T`` th) \\ assume_tac (SPEC``SOME F`` th))
  \\ fs[] \\ rfs[]
  \\ ...
QED
*)

val _ = export_theory();
