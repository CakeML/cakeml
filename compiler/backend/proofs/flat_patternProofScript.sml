(*
  Correctness proof for flat_pattern
*)

open preamble flat_patternTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     flatLangTheory flatSemTheory flatPropsTheory backendPropsTheory
     pattern_semanticsTheory
local open bagSimps induct_tweakLib in end

val _ = new_theory "flat_patternProof"

val _ = set_grammar_ancestry ["flat_pattern",
                              "misc","ffi","bag","flatProps",
                              "backendProps","backend_common",
                              "pattern_semantics"];

(* simple properties *)
Theorem op_sets_globals_gbag:
  op_sets_globals op = (op_gbag op <> {||})
Proof
  Cases_on `op` \\ simp [op_sets_globals_def, op_gbag_def]
QED

Theorem compile_exp_set_globals_FST_SND:
  (!cfg x. FST (SND (compile_exp cfg x)) =
    (set_globals x <> {||})) /\
   (!cfg xs. FST (SND (compile_exps cfg xs)) =
    (elist_globals xs <> {||})) /\
  (!cfg ps. FST (SND (compile_match cfg ps)) =
    (elist_globals (MAP SND ps) <> {||}))
Proof
  ho_match_mp_tac compile_exp_ind \\ rw [compile_exp_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ fs [flatPropsTheory.elist_globals_REVERSE, op_sets_globals_gbag]
  \\ simp [DISJ_ASSOC]
  \\ simp [EXISTS_MEM, elist_globals_eq_empty, PULL_EXISTS, MEM_MAP]
  \\ simp [EXISTS_PROD, ELIM_UNCURRY]
  \\ metis_tac []
QED

Theorem compile_exp_set_globals_tup:
  (!cfg x i sg y. compile_exp cfg x = (i, sg, y) ==>
    sg = (set_globals x <> {||})) /\
   (!cfg xs i sg ys. compile_exps cfg xs = (i, sg, ys) ==>
    sg = (elist_globals xs <> {||})) /\
  (!cfg ps i sg ps2. compile_match cfg ps = (i, sg, ps2) ==>
    sg = (elist_globals (MAP SND ps) <> {||}))
Proof
  metis_tac [compile_exp_set_globals_FST_SND, FST, SND]
QED

(* decoding the encoded names *)

Theorem sum_string_ords_eq:
  sum_string_ords i s = SUM (MAP (\c. ORD c - 35) (DROP i s))
Proof
  measureInduct_on `(\i. LENGTH s - i) i`
  \\ simp [Once sum_string_ords_def]
  \\ rw [rich_listTheory.DROP_EL_CONS, listTheory.DROP_LENGTH_TOO_LONG]
QED

Theorem dec_enc:
  !xs. dec_name_to_num (enc_num_to_name i xs) =
  i + SUM (MAP (\c. ORD c - 35) xs)
Proof
  measureInduct_on `I i`
  \\ simp [Once enc_num_to_name_def]
  \\ CASE_TAC \\ simp [dec_name_to_num_def, sum_string_ords_eq]
QED

Theorem enc_num_to_name_inj:
  (enc_num_to_name i [] = enc_num_to_name j []) = (i = j)
Proof
  metis_tac [dec_enc |> Q.SPEC `[]` |> SIMP_RULE list_ss []]
QED

(* lists and lookups *)

Theorem LIST_REL_ALOOKUP_OPTREL:
  !xs ys. LIST_REL R xs ys /\
  (!x y. R x y /\ MEM x xs /\ MEM y ys /\ (v = FST x \/ v = FST y) ==>
    FST x = FST y /\ R2 (SND x) (SND y))
  ==> OPTREL R2 (ALOOKUP xs v) (ALOOKUP ys v)
Proof
  Induct \\ rpt (Cases ORELSE gen_tac)
  \\ simp [optionTheory.OPTREL_def]
  \\ qmatch_goalsub_abbrev_tac `ALOOKUP (pair :: _)`
  \\ Cases_on `pair`
  \\ simp []
  \\ rpt strip_tac
  \\ last_x_assum drule
  \\ impl_tac >- metis_tac []
  \\ simp []
  \\ strip_tac
  \\ first_x_assum drule
  \\ rw []
  \\ fs [optionTheory.OPTREL_def]
QED

Theorem LIST_REL_ALOOKUP:
  !xs ys. LIST_REL R xs ys /\
  (!x y. R x y /\ MEM x xs /\ MEM y ys /\ (v = FST x \/ v = FST y) ==> x = y)
  ==> ALOOKUP xs v = ALOOKUP ys v
Proof
  REWRITE_TAC [GSYM optionTheory.OPTREL_eq]
  \\ rpt strip_tac
  \\ drule_then irule LIST_REL_ALOOKUP_OPTREL
  \\ metis_tac []
QED

Theorem LIST_REL_FILTER_MONO:
  !xs ys. LIST_REL R (FILTER P1 xs) (FILTER P2 ys) /\
  (!x. MEM x xs /\ P3 x ==> P1 x) /\
  (!y. MEM y ys /\ P4 y ==> P2 y) /\
  (!x y. MEM x xs /\ MEM y ys /\ R x y ==> P3 x = P4 y)
  ==> LIST_REL R (FILTER P3 xs) (FILTER P4 ys)
Proof
  Induct
  >- (
    simp [FILTER_EQ_NIL, EVERY_MEM]
    \\ metis_tac []
  )
  \\ gen_tac
  \\ simp []
  \\ reverse CASE_TAC
  >- (
    CASE_TAC
    >- metis_tac []
    \\ rw []
  )
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [FILTER_EQ_CONS]
  \\ rename [`_ = ys_pre ++ [y] ++ ys_post`]
  \\ rveq \\ fs []
  \\ fs [FILTER_APPEND]
  \\ first_x_assum drule
  \\ simp []
  \\ disch_tac
  \\ `FILTER P4 ys_pre = []` by (fs [FILTER_EQ_NIL, EVERY_MEM] \\ metis_tac [])
  \\ rw []
  \\ metis_tac []
QED

Theorem COND_false:
  ~ P ==> ((if P then x else y) = y)
Proof
  simp []
QED

Theorem COND_true:
  P ==> ((if P then x else y) = x)
Proof
  simp []
QED

Theorem FILTER_EQ_MONO = LIST_REL_FILTER_MONO
  |> Q.GEN `R` |> Q.ISPEC `(=)` |> REWRITE_RULE [LIST_REL_eq]

Theorem FILTER_EQ_MONO_TRANS = FILTER_EQ_MONO
  |> Q.GEN `P2` |> Q.SPEC `\x. T`
  |> Q.GEN `P4` |> Q.SPEC `P3`
  |> REWRITE_RULE [FILTER_T]

Theorem FILTER_EQ_ALOOKUP_EQ:
  !xs ys. FILTER P xs = ys /\ (!z. P (x, z)) ==>
  ALOOKUP xs x = ALOOKUP ys x
Proof
  Induct \\ simp []
  \\ Cases
  \\ rw []
  \\ fs []
QED

Theorem ALOOKUP_FILTER_EQ = FILTER_EQ_ALOOKUP_EQ |> SIMP_RULE bool_ss []
  |> GSYM;

Theorem MEM_enumerate_EL:
  !xs i x. MEM x (enumerate i xs) = (?j. j < LENGTH xs /\ x = (i + j, EL j xs))
Proof
  Induct \\ rw [miscTheory.enumerate_def]
  \\ simp [indexedListsTheory.LT_SUC]
  \\ EQ_TAC \\ rw []
  \\ simp [EL_CONS, ADD1]
  \\ simp [GSYM ADD1]
  \\ qexists_tac `0` \\ simp []
QED

Theorem ALL_DISTINCT_enumerate:
  !xs i. ALL_DISTINCT (enumerate i xs)
Proof
  Induct \\ rw [miscTheory.enumerate_def, MEM_enumerate_EL]
QED

Definition pure_eval_to_def:
  pure_eval_to s env exp v = (evaluate env s [exp] = (s, Rval [v]))
End

Theorem pmatch_list_Match_IMP_LENGTH:
  !xs ys env env' s. pmatch_list c_env s xs ys env = Match env' ==>
  LENGTH xs = LENGTH ys
Proof
  Induct
  >- (
    Cases \\ simp [flatSemTheory.pmatch_def]
  )
  >- (
    gen_tac \\ Cases \\ simp [flatSemTheory.pmatch_def]
    \\ simp [CaseEq "match_result"]
    \\ metis_tac []
  )
QED

Theorem pmatch_list_append_Match_exists:
  (pmatch_list c_env s (xs ++ ys) vs pre_bindings = Match bindings) =
  (?vs1 vs2 bindings1. vs = vs1 ++ vs2 /\
  pmatch_list c_env s xs vs1 pre_bindings = Match bindings1 /\
  pmatch_list c_env s ys vs2 bindings1 = Match bindings)
Proof
  Cases_on `LENGTH vs <> LENGTH xs + LENGTH ys`
  >- (
    EQ_TAC \\ rw []
    \\ imp_res_tac pmatch_list_Match_IMP_LENGTH
    \\ fs []
  )
  \\ fs []
  \\ qspecl_then [`xs`, `TAKE (LENGTH xs) vs`, `ys`, `DROP (LENGTH xs) vs`,
        `c_env`, `s`, `pre_bindings`]
    mp_tac flatPropsTheory.pmatch_list_append
  \\ rw []
  \\ simp [CaseEq "match_result"]
  \\ EQ_TAC \\ rw []
  \\ imp_res_tac pmatch_list_Match_IMP_LENGTH
  \\ simp [TAKE_APPEND, DROP_APPEND, DROP_LENGTH_TOO_LONG]
  \\ rpt (goal_assum (first_assum o mp_then Any mp_tac))
  \\ simp []
QED

Definition ALOOKUP_rel_def:
  ALOOKUP_rel P R env1 env2 =
  (!x. P x ==> OPTREL R (ALOOKUP env1 x) (ALOOKUP env2 x))
End

Theorem ALOOKUP_rel_empty:
  ALOOKUP_rel P R [] []
Proof
  simp [ALOOKUP_rel_def, OPTREL_def]
QED

Theorem ALOOKUP_rel_cons_false:
  (~ P x ==> ALOOKUP_rel P R ((x, y) :: env1) env2 = ALOOKUP_rel P R env1 env2)
  /\
  (~ P x ==> ALOOKUP_rel P R env1 ((x, y) :: env2) = ALOOKUP_rel P R env1 env2)
Proof
  simp [ALOOKUP_rel_def]
  \\ metis_tac [COND_CLAUSES]
QED

Theorem ALOOKUP_rel_APPEND_L_false:
  EVERY ((~) o P o FST) xs ==>
  ALOOKUP_rel P R (xs ++ ys) zs =
  ALOOKUP_rel P R ys zs
Proof
  rw [ALOOKUP_rel_def, ALOOKUP_APPEND]
  \\ EQ_TAC \\ rw []
  \\ first_x_assum drule
  \\ CASE_TAC \\ simp []
  \\ drule ALOOKUP_MEM
  \\ fs [EVERY_MEM, FORALL_PROD]
  \\ metis_tac []
QED

Theorem ALOOKUP_rel_refl:
  (!x y. P x /\ MEM (x, y) xs ==> R y y) ==> ALOOKUP_rel P R xs xs
Proof
  rw [ALOOKUP_rel_def]
  \\ Cases_on `ALOOKUP xs x`
  \\ simp [OPTREL_def]
  \\ metis_tac [ALOOKUP_MEM]
QED

Theorem ALOOKUP_rel_cons:
  (P x ==> R y z) /\ ALOOKUP_rel P R ys zs ==>
  ALOOKUP_rel P R ((x, y) :: ys) ((x, z) :: zs)
Proof
  rw [ALOOKUP_rel_def] \\ rw [] \\ simp [OPTREL_def]
QED

Theorem ALOOKUP_rel_mono:
  ALOOKUP_rel P R xs ys /\
  (!x y z. P' x ==> P x) /\
  (!x y z. P' x /\ R y z ==> R' y z) ==>
  ALOOKUP_rel P' R' xs ys
Proof
  rw [ALOOKUP_rel_def]
  \\ fs [OPTREL_def]
  \\ metis_tac []
QED

Theorem ALOOKUP_rel_mono_rel:
  (!y z. R y z ==> R' y z) ==>
  ALOOKUP_rel P R xs ys ==>
  ALOOKUP_rel P R' xs ys
Proof
  metis_tac [ALOOKUP_rel_mono]
QED

Theorem ALOOKUP_rel_append_suff:
  ALOOKUP_rel P R xs1 xs3 /\ ALOOKUP_rel P R xs2 xs4 ==>
  ALOOKUP_rel P R (xs1 ++ xs2) (xs3 ++ xs4)
Proof
  rw [ALOOKUP_rel_def, ALOOKUP_APPEND]
  \\ res_tac
  \\ EVERY_CASE_TAC
  \\ fs [OPTREL_def]
QED

Theorem ALOOKUP_rel_EQ_ALOOKUP:
  ALOOKUP_rel P (=) xs ys /\ P x ==>
  ALOOKUP xs x = ALOOKUP ys x
Proof
  simp [ALOOKUP_rel_def]
QED

Theorem ALOOKUP_rel_eq_fst:
  !xs ys.
  LIST_REL (\x y. FST x = FST y /\ (P (FST x) ==> R (SND x) (SND y))) xs ys ==>
  ALOOKUP_rel P R xs ys
Proof
  Induct \\ rpt Cases
  \\ fs [ALOOKUP_rel_def, OPTREL_def]
  \\ Cases_on `h`
  \\ rw []
  \\ rw []
QED

Theorem env_set_v_noop:
  env with <| v := env.v |> = env
Proof
  simp [environment_component_equality]
QED

Theorem pat_bindings_evaluate_FOLDR_lemma:
  !h xs.
  (!x. MEM x xs ==> IS_SOME (f x)) /\
  (!x. IMAGE (THE o f) (set xs) ⊆ new_names) /\
  (!x. MEM x xs ==> (!env2.
    ALOOKUP_rel (\x. x ∉ new_names) (=) env2.v env.v ==>
    evaluate env2 s [g x] = (s, Rval [h x])))
  ==>
  !env2.
  ALOOKUP_rel (\x. x ∉ new_names) (=) env2.v env.v ==>
  evaluate env2 s
    [FOLDR (λx exp. flatLang$Let t (f x) (g x) exp) exp xs] =
  evaluate (env2 with v := MAP (λx. (THE (f x), h x)) (REVERSE xs) ++ env2.v)
        s [exp]
Proof
  gen_tac \\ Induct \\ simp [env_set_v_noop]
  \\ rw []
  \\ simp [evaluate_def]
  \\ fs [DISJ_IMP_THM, FORALL_AND_THM, IMP_CONJ_THM, IS_SOME_EXISTS]
  \\ rfs []
  \\ simp [libTheory.opt_bind_def, ALOOKUP_rel_cons_false]
  \\ simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]
QED

(*
Theorem pat_bindings_evaluate_FOLDR_lemma:
  !new_names.
  (!x. MEM x xs ==> IS_SOME (f x)) /\
  (!x. IMAGE (THE o f) (set xs) ⊆ new_names) /\
  (!x. MEM x xs ==> (?rv. !env2.
    ALOOKUP_rel (\x. x ∉ new_names) (=) env2.v env.v ==>
    evaluate env2 s [g x] = (s, Rval [rv])))
  ==>
  evaluate env s
    [FOLDR (λx exp. flatLang$Let t (f x) (g x) exp) exp xs] =
  evaluate (env with v := MAP (λx. (THE (f x),
        case evaluate env s [g x] of (_, Rval rv) => HD rv)) (REVERSE xs)
             ++ env.v) s [exp]
Proof
  rw []
  \\ DEP_REWRITE_TAC [pat_bindings_evaluate_FOLDR_lemma1]
  \\ simp [ALOOKUP_rel_refl]
QED
*)

Definition v_cons_in_c_def1:
  v_cons_in_c c (Conv stmp xs) = (
    (case stmp of SOME con_stmp => (con_stmp, LENGTH xs) ∈ c
        | NONE => T) /\
    EVERY (v_cons_in_c c) xs) /\
  v_cons_in_c c (Vectorv vs) = EVERY (v_cons_in_c c) vs /\
  v_cons_in_c c (Closure env n exp) =
  EVERY (\x. v_cons_in_c c (SND x)) env.v /\
  v_cons_in_c c (Recclosure env funs n) =
  EVERY (\x. v_cons_in_c c (SND x)) env.v /\
  v_cons_in_c c other = T
Termination
  WF_REL_TAC `measure (v_size o SND)`
  \\ rw []
  \\ fs [MEM_SPLIT, SUM_APPEND, v_size_aux, v_size_def]
End

Theorem v_cons_in_c_def[simp] = v_cons_in_c_def1
    |> CONV_RULE (DEPTH_CONV ETA_CONV)
    |> SIMP_RULE bool_ss [prove (``(λx. v_cons_in_c c (SND x))
        = (v_cons_in_c c o SND)``, simp [o_DEF])]

Theorem EVERY_MAPi_simple:
  (!i j x. P (f i x) = P (f j x)) ==>
  EVERY P (MAPi f xs) = EVERY P (MAP (f 0) xs)
Proof
  simp [EVERY_EL, EL_MAP]
  \\ metis_tac []
QED

val EVERY_EL_IMP = ASSUME ``EVERY P xs`` |> REWRITE_RULE [EVERY_EL]
  |> DISCH_ALL

(* a note on 'naming' below. the existing (encoded) names in the program
   (in the original x and exp)
   are < j for starting val j. during the recursion, j increases to i, with
   new names i < nm < j appearing in the new env, and in *expressions* in
   n_bindings. note *names* in n_bindings/pre_bindings come from the original
   program. also new/old names mix in env, thus the many filters. *)

Theorem compile_pat_bindings_simulation:
  ! t i n_bindings exp exp2 spt s vs pre_bindings bindings env s2 res vset.
  compile_pat_bindings t i n_bindings exp = (spt, exp2) /\
  pmatch_list c_env s (MAP FST n_bindings) vs pre_bindings = Match bindings /\
  evaluate env s [exp2] = (s2, res) /\
  LIST_REL (\(_, k, v_exp) v. !env2. k ∈ domain spt /\
        ALOOKUP_rel ((\k. k > j /\ k < i) o dec_name_to_num) (=) env2.v env.v
        ==>
        pure_eval_to s env2 v_exp v)
    n_bindings vs /\
  EVERY ((\k. k < j) o dec_name_to_num o FST) pre_bindings /\
  j < i /\
  ALOOKUP_rel ((\k. k < j) o dec_name_to_num) (=) env.v
    (pre_bindings ++ base_vs) /\
  EVERY (v_cons_in_c s.c ∘ SND) env.v /\
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) s.refs /\
  EVERY (v_cons_in_c s.c) vs /\
  EVERY (\(p, k, _). EVERY (\nm. dec_name_to_num nm < j) (pat_bindings p []) /\
        j < k /\ k < i) n_bindings
  ==>
  ?env2. evaluate env2 s [exp] = (s2, res) /\
  env2.c = env.c /\
  EVERY (v_cons_in_c s.c ∘ SND) env2.v /\
  ALOOKUP_rel ((\k. k < j) o dec_name_to_num) (=) env2.v (bindings ++ base_vs)
Proof
  ho_match_mp_tac compile_pat_bindings_ind
  \\ rpt conj_tac
  \\ simp_tac bool_ss [compile_pat_bindings_def, flatSemTheory.pmatch_def,
        PULL_EXISTS, EVERY_DEF, PAIR_EQ, MAP, LIST_REL_NIL, LIST_REL_CONS1,
        LIST_REL_CONS2, FORALL_PROD]
  \\ rpt strip_tac
  \\ fs [] \\ rveq \\ fs []
  \\ fs [flatSemTheory.pmatch_def]
  >- (
    metis_tac []
  )
  >- (
    metis_tac []
  )
  >- (
    rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ fs [evaluate_def]
    \\ qpat_x_assum `!env. _ ==> pure_eval_to _ _ x _` mp_tac
    \\ disch_then (qspec_then `env` mp_tac)
    \\ simp [pure_eval_to_def, ALOOKUP_rel_refl]
    \\ rw []
    \\ fs [pat_bindings_def]
    \\ last_x_assum (drule_then drule)
    \\ simp [libTheory.opt_bind_def]
    \\ disch_then irule
    \\ simp [libTheory.opt_bind_def]
    \\ simp [ALOOKUP_rel_cons]
    \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac LIST_REL_mono)
    \\ simp [FORALL_PROD, ALOOKUP_rel_cons_false]
  )
  >- (
    qmatch_asmsub_abbrev_tac `pmatch _ _ (Plit l) lv`
    \\ Cases_on `lv` \\ fs [flatSemTheory.pmatch_def]
    \\ qpat_x_assum `_ = Match _` mp_tac
    \\ simp [CaseEq "match_result", bool_case_eq]
    \\ rw []
    \\ metis_tac []
  )
  >- (
    (* Pcon *)
    qmatch_asmsub_abbrev_tac `pmatch _ _ (Pcon stmp _) con_v`
    \\ qpat_x_assum `_ = Match _` mp_tac
    \\ simp [CaseEq "match_result"]
    \\ rw []
    \\ Cases_on `con_v` \\ fs [flatSemTheory.pmatch_def]
    \\ rename [`Conv stmp' con_vs`]
    \\ fs [bool_case_eq]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ fs [MAP_MAP_o |> REWRITE_RULE [o_DEF], UNCURRY, Q.ISPEC `SND` ETA_THM]
    \\ fs [LENGTH_enumerate, MAP_enumerate_MAPi, MAPi_eq_MAP]
    \\ qpat_x_assum `evaluate _ _ [FOLDR _ _ _] = _` mp_tac
    \\ simp [ELIM_UNCURRY]
    \\ DEP_REWRITE_TAC [Q.ISPEC
        `\ (x : (num # 'y) # 'z). EL (FST (FST x)) (con_vs : v list)`
        pat_bindings_evaluate_FOLDR_lemma |> Q.GEN `new_names`]
    \\ simp []
    \\ conj_tac >- (
      qexists_tac `{x | ~ (dec_name_to_num x < i)}`
      \\ simp [SUBSET_DEF, MEM_FILTER, MEM_MAPi, PULL_EXISTS]
      \\ simp [dec_enc, ALOOKUP_rel_refl]
      \\ rw [IS_SOME_EXISTS]
      \\ qpat_x_assum `!env. _ ==> pure_eval_to _ _ x _`
        (qspec_then `env2` mp_tac)
      \\ DEP_REWRITE_TAC [COND_false]
      \\ simp [PULL_EXISTS, NULL_FILTER, MEM_MAPi]
      \\ asm_exists_tac \\ simp []
      \\ impl_tac \\ simp [pure_eval_to_def, evaluate_def, do_app_def]
      \\ drule_then irule ALOOKUP_rel_mono
      \\ simp []
    )
    \\ rw []
    \\ fs [Q.ISPEC `Match m` EQ_SYM_EQ]
    \\ fs [PULL_EXISTS, pmatch_list_append_Match_exists]
    \\ last_x_assum (drule_then (drule_then drule))
    \\ simp []
    \\ disch_then irule
    \\ DEP_REWRITE_TAC [ALOOKUP_rel_APPEND_L_false]
    \\ simp [MAP_APPEND, REVERSE_APPEND, MEM_MAP, MEM_FILTER,
      EVERY_MEM, MEM_MAPi, PULL_EXISTS, dec_enc, FORALL_PROD]
    \\ simp []
    \\ rpt strip_tac
    \\ TRY (
      fs [EVERY_MEM, FORALL_PROD]
      \\ res_tac
      \\ simp []
      \\ NO_TAC
    )
    \\ TRY (
      fs [pat_bindings_def, pats_bindings_FLAT_MAP, EVERY_FLAT, EVERY_REVERSE]
      \\ fs [EVERY_EL, FORALL_PROD, UNCURRY, EL_MAP, MEM_EL]
      \\ NO_TAC
    )
    \\ irule LIST_REL_APPEND_suff
    \\ conj_tac
    >- (
      (* new elements *)
      simp [LIST_REL_EL_EQN, LENGTH_enumerate, EL_enumerate, EL_MAP]
      \\ simp [pure_eval_to_def, evaluate_def, option_case_eq]
      \\ rw []
      \\ drule_then (fn t => DEP_REWRITE_TAC [t]) ALOOKUP_rel_EQ_ALOOKUP
      \\ simp [dec_enc]
      \\ fs [sptreeTheory.domain_lookup]
      \\ simp [ALOOKUP_APPEND, option_case_eq]
      \\ DEP_REWRITE_TAC [GSYM MEM_ALOOKUP |> Q.SPEC `MAP f zs`]
      \\ simp [MEM_MAP, EXISTS_PROD, MEM_FILTER, MEM_MAPi, enc_num_to_name_inj]
      \\ simp [MAP_MAP_o, o_DEF, MAP_REVERSE]
      \\ irule ALL_DISTINCT_MAP_INJ
      \\ simp [MEM_FILTER, FORALL_PROD, MEM_MAPi, enc_num_to_name_inj]
      \\ irule FILTER_ALL_DISTINCT
      \\ simp [MAPi_enumerate_MAP]
      \\ irule ALL_DISTINCT_MAP_INJ
      \\ simp [FORALL_PROD, ALL_DISTINCT_enumerate]
    )
    (* prior env *)
    \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac LIST_REL_mono)
    \\ simp [FORALL_PROD]
    \\ rpt strip_tac
    \\ first_x_assum irule
    \\ simp []
    \\ conj_tac \\ TRY (IF_CASES_TAC \\ simp [] \\ NO_TAC)
    \\ rw [ALOOKUP_rel_def]
    \\ drule_then (fn t => DEP_REWRITE_TAC [t]) ALOOKUP_rel_EQ_ALOOKUP
    \\ simp [ALOOKUP_APPEND, option_case_eq, ALOOKUP_NONE, MEM_MAP, FORALL_PROD,
        MEM_FILTER, MEM_MAPi]
    \\ CCONTR_TAC \\ fs []
    \\ fs [dec_enc]
  )
  >- (
    (* Pref *)
    qpat_x_assum `_ = Match _` mp_tac
    \\ qmatch_goalsub_abbrev_tac `pmatch _ _ (Pref _) ref_v`
    \\ Cases_on `ref_v` \\ simp [flatSemTheory.pmatch_def]
    \\ rw [CaseEq "match_result", option_case_eq, CaseEq "store_v"]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ qpat_x_assum `!env. _ ==> pure_eval_to _ _ x _` mp_tac
    \\ disch_then (qspec_then `env` mp_tac)
    \\ simp [evaluate_def, pure_eval_to_def, ALOOKUP_rel_refl]
    \\ rw []
    \\ fs [evaluate_def, do_app_def]
    \\ last_x_assum (first_assum o mp_then (Pat `evaluate _ _ _ = _`) mp_tac)
    \\ simp []
    \\ disch_then match_mp_tac
    \\ simp [CaseEq "match_result", PULL_EXISTS]
    \\ rpt (CHANGED_TAC (asm_exists_tac \\ simp []))
    \\ fs [libTheory.opt_bind_def, pat_bindings_def]
    \\ simp [ALOOKUP_rel_cons_false, dec_enc]
    \\ fs [store_lookup_def]
    \\ drule_then drule EVERY_EL_IMP
    \\ rw []
    >- (
      rw [pure_eval_to_def, evaluate_def, option_case_eq]
      \\ drule_then (fn t => DEP_REWRITE_TAC [t]) ALOOKUP_rel_EQ_ALOOKUP
      \\ simp [dec_enc]
    )
    >- (
      first_x_assum (fn t => mp_tac t \\ match_mp_tac LIST_REL_mono)
      \\ simp [FORALL_PROD]
      \\ rw []
      \\ first_x_assum irule
      \\ simp []
      \\ rw [ALOOKUP_rel_def]
      \\ drule_then (fn t => DEP_REWRITE_TAC [t]) ALOOKUP_rel_EQ_ALOOKUP
      \\ simp [dec_enc, FILTER_FILTER]
      \\ rw []
      \\ fs [dec_enc]
    )
    >- (
      fs [EVERY_MEM, FORALL_PROD]
      \\ rw [] \\ res_tac \\ simp []
    )
  )
QED

val s = ``s:('c, 'ffi) flatSem$state``;
val s1 = mk_var ("s1", type_of s);
val s2 = mk_var ("s2", type_of s);
(* on the right side of the state relation, the pattern compiler's config is
   also needed in the compiler state *)
val t = ``t:((config # 'c), 'ffi) flatSem$state``;

val _ = IndDefLib.add_mono_thm ALOOKUP_rel_mono_rel;

Inductive v_rel:
  (!v v'. simple_basic_val_rel v v' /\
    LIST_REL v_rel (v_container_xs v) (v_container_xs v') ==>
    v_rel v v') /\
  (!N env1 n x env2 cfg.
     env_rel N env1 env2 /\
     FST (compile_exp cfg x) < N ==>
     v_rel (Closure env1 n x)
       (Closure env2 n (SND (SND (compile_exp cfg x))))) /\
  (!N env1 fs x env2 cfg.
     env_rel N env1 env2 /\
     EVERY (\(n,m,e). FST (compile_exp cfg e) < N) fs ==>
     v_rel (Recclosure env1 fs x) (Recclosure env2
         (MAP (\(n,m,e). (n,m, SND (SND (compile_exp cfg e)))) fs) x))
  /\
  (!N env1 env2.
     ALOOKUP_rel (\x. dec_name_to_num x < N) v_rel env1.v env2.v /\
     env1.c = env2.c /\
     initial_ctors ⊆ env2.c ==>
     env_rel N env1 env2)
End

Theorem v_rel_l_cases = TypeBase.nchotomy_of ``: v``
  |> concl |> dest_forall |> snd |> strip_disj
  |> map (rhs o snd o strip_exists)
  |> map (curry mk_comb ``v_rel``)
  |> map (fn t => mk_comb (t, ``v2 : v``))
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> LIST_CONJ

val env_rel_def = ``env_rel N env1 env2``
    |> SIMP_CONV bool_ss [v_rel_cases]

val add_q = augment_srw_ss [simpLib.named_rewrites "pair_rel_thm"
  [quotient_pairTheory.PAIR_REL_THM]];

Definition extend_eval_config_def:
  extend_eval_config st ec = Eval <| compile := (\env (st, st') decs.
        let (decs, env, st') = ec.compile env st' decs in
        let (st, decs) = compile_decs st decs in
        (decs, env, (st, st'))); compiler_state := (st, ec.compiler_state) |>
End

Definition state_rel_def:
  state_rel ^s ^t <=>
    t.clock = s.clock /\
    LIST_REL (sv_rel v_rel) s.refs t.refs /\
    t.ffi = s.ffi /\
    LIST_REL (OPTREL v_rel) s.globals t.globals /\
    t.c = s.c /\
    (?st ec. s.eval_mode = Eval ec /\
        t.eval_mode = extend_eval_config st ec)
End

Theorem state_rel_initial_state:
  state_rel (initial_state ffi k (Eval ec))
    (initial_state ffi k (extend_eval_config cfg ec))
Proof
  fs [state_rel_def, initial_state_def]
  \\ metis_tac []
QED

Triviality state_rel_IMP_clock:
  state_rel s t ==> t.clock = s.clock
Proof
  fs [state_rel_def]
QED

Triviality state_rel_IMP_c:
  state_rel s t ==> t.c = s.c
Proof
  fs [state_rel_def]
QED

Theorem state_rel_c_update:
  state_rel s1 s2 /\ f s1.c = g s1.c ==>
  state_rel (s1 with c updated_by f) (s2 with c updated_by g)
Proof
  simp [state_rel_def]
QED

Overload nv_rel[local] =
  ``\N. ALOOKUP_rel (\x. dec_name_to_num x < N) v_rel``

Definition match_rel_def:
  (match_rel N (Match env1) (Match env2) <=> nv_rel N env1 env2) /\
  (match_rel N No_match No_match <=> T) /\
  (match_rel N Match_type_error Match_type_error <=> T) /\
  (match_rel N _ _ <=> F)
End

Theorem match_rel_thms[simp]:
   (match_rel N Match_type_error e <=> e = Match_type_error) /\
   (match_rel N e Match_type_error <=> e = Match_type_error) /\
   (match_rel N No_match e <=> e = No_match) /\
   (match_rel N e No_match <=> e = No_match)
Proof
  Cases_on `e` \\ rw [match_rel_def]
QED

Theorem MAX_ADD_LESS:
  (MAX i j + k < l) = (i + k < l /\ j + k < l)
Proof
  rw [MAX_DEF]
QED

Theorem LESS_MAX_ADD:
  (l < MAX i j + k) = (l < i + k \/ l < j + k)
Proof
  rw [MAX_DEF]
QED

Theorem MAX_ADD_LE:
  (MAX i j + k <= l) = (i + k <= l /\ j + k <= l)
Proof
  rw [MAX_DEF]
QED

Theorem env_rel_mono:
  env_rel i env1 env2 /\ j <= i ==>
  env_rel j env1 env2
Proof
  rw [env_rel_def]
  \\ drule_then irule ALOOKUP_rel_mono
  \\ simp [FORALL_PROD]
QED

Theorem env_rel_ALOOKUP:
  env_rel N env1 env2 /\ dec_name_to_num n < N ==>
  OPTREL v_rel (ALOOKUP env1.v n) (ALOOKUP env2.v n)
Proof
  rw [env_rel_def, ALOOKUP_rel_def]
QED

Theorem ALOOKUP_MAP_3:
  (!x. MEM x xs ==> FST (f x) = FST x) ==>
  ALOOKUP (MAP f xs) x = OPTION_MAP (\y. SND (f (x, y))) (ALOOKUP xs x)
Proof
  Induct_on `xs` \\ rw []
  \\ fs [DISJ_IMP_THM, FORALL_AND_THM]
  \\ Cases_on `f h`
  \\ Cases_on `h`
  \\ rw []
  \\ fs []
QED

Theorem ALOOKUP_rel_MAP_same:
  (!x. MEM x xs ==> FST (f x) = FST (g x) /\
    (P (FST (g x)) ==> R (SND (f x)) (SND (g x)))) ==>
  ALOOKUP_rel P R (MAP f xs) (MAP g xs)
Proof
  Induct_on `xs` \\ rw [ALOOKUP_rel_empty]
  \\ fs [DISJ_IMP_THM, FORALL_AND_THM]
  \\ Cases_on `f h` \\ Cases_on `g h`
  \\ fs [ALOOKUP_rel_cons]
QED

Theorem do_opapp_thm:
  do_opapp vs1 = SOME (env1, exp) /\ LIST_REL v_rel vs1 vs2
  ==>
  ?i sg exp' env2 cfg. compile_exp cfg exp = (i, sg, exp') /\
  env_rel (i + 1) env1 env2 /\ do_opapp vs2 = SOME (env2, exp')
Proof
  simp [do_opapp_def, pair_case_eq, case_eq_thms, PULL_EXISTS]
  \\ rw []
  \\ fs [v_rel_l_cases]
  \\ rveq \\ fs []
  \\ simp [PAIR_FST_SND_EQ]
  >- (
    qexists_tac `cfg`
    \\ fs [LENGTH_SND_compile_exps, env_rel_def]
    \\ irule ALOOKUP_rel_cons
    \\ simp []
    \\ drule_then irule ALOOKUP_rel_mono
    \\ simp []
  )
  \\ fs [PULL_EXISTS, find_recfun_ALOOKUP, ALOOKUP_MAP]
  \\ simp [ALOOKUP_MAP_3, FORALL_PROD]
  \\ qexists_tac `cfg`
  \\ simp [LENGTH_SND_compile_exps]
  \\ simp [MAP_MAP_o, o_DEF, UNCURRY, Q.ISPEC `FST` ETA_THM]
  \\ fs [env_rel_def]
  \\ irule ALOOKUP_rel_cons
  \\ simp [build_rec_env_eq_MAP]
  \\ irule ALOOKUP_rel_append_suff
  \\ simp [MAP_MAP_o, o_DEF, UNCURRY]
  \\ conj_tac
  >- (
    irule ALOOKUP_rel_MAP_same
    \\ rw [UNCURRY, v_rel_l_cases, env_rel_def]
    \\ metis_tac []
  )
  \\ drule_then irule ALOOKUP_rel_mono
  \\ simp []
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [EVERY_MEM]
  \\ res_tac
  \\ fs []
QED

Theorem do_opapp_thm_REVERSE:
  do_opapp (REVERSE vs1) = SOME (env1, exp) /\ LIST_REL v_rel vs1 vs2
  ==>
  ?i sg exp' env2 cfg.
  compile_exp cfg exp = (i, sg, exp') /\
  env_rel (i + 1) env1 env2 /\
  do_opapp (REVERSE vs2) = SOME (env2, exp')
Proof
  rw []
  \\ drule_then irule do_opapp_thm
  \\ simp []
QED

Theorem pmatch_thm:
  (!env ^s p v vs r s1 v1 vs1.
    pmatch env s p v vs = r /\
    r <> Match_type_error /\
    state_rel s s1 /\
    v_rel v v1 /\
    nv_rel N vs vs1
    ==> ?r1. pmatch env s1 p v1 vs1 = r1 /\ match_rel N r r1) /\
  (!env ^s ps v vs r s1 v1 vs1.
    pmatch_list env s ps v vs = r /\
    r <> Match_type_error /\
    state_rel s s1 ∧
    LIST_REL v_rel v v1 /\
    nv_rel N vs vs1
    ==> ?r1. pmatch_list env s1 ps v1 vs1 = r1 /\ match_rel N r r1)
Proof
  ho_match_mp_tac flatSemTheory.pmatch_ind
  \\ simp [flatSemTheory.pmatch_def, match_rel_def, v_rel_l_cases]
  \\ rw [match_rel_def]
  \\ imp_res_tac state_rel_IMP_c
  \\ fs [flatSemTheory.pmatch_def, pmatch_stamps_ok_OPTREL]
  \\ rfs []
  \\ imp_res_tac LIST_REL_LENGTH \\ fs []
  >- ( irule ALOOKUP_rel_cons \\ simp [] )
  >- (
    fs [store_lookup_def, bool_case_eq, option_case_eq]
    \\ every_case_tac \\ rfs []
    \\ rpt (first_x_assum drule)
    \\ fs [state_rel_def, LIST_REL_EL_EQN]
    \\ rfs []
    \\ rpt (first_x_assum drule)
    \\ simp []
  )
  >- (
    every_case_tac \\ fs []
    \\ rpt (first_x_assum drule \\ rw [])
    \\ TRY (rpt (asm_exists_tac \\ simp []) \\ NO_TAC)
    \\ fs [match_rel_def]
  )
QED

Theorem simple_val_rel_step_isClosure:
  simple_basic_val_rel x y ==> ~ isClosure x /\ ~ isClosure y
Proof
  Cases_on `x` \\ simp [simple_basic_val_rel_def]
  \\ rw [] \\ simp []
QED

Theorem simple_val_rel:
  simple_val_rel v_rel
Proof
  simp [simple_val_rel_def, v_rel_cases]
  \\ rw [] \\ simp []
  \\ EQ_TAC \\ rw [] \\ fs []
  \\ metis_tac [simple_val_rel_step_isClosure]
QED

Theorem simple_state_rel:
  simple_state_rel v_rel state_rel
Proof
  simp [simple_state_rel_def, state_rel_def]
QED

Theorem do_app_thm = MATCH_MP simple_do_app_thm
    (CONJ simple_val_rel simple_state_rel)

Theorem do_app_thm_REVERSE:
  do_app s1 op (REVERSE vs1) = SOME (t1, r1) /\
  state_rel s1 s2 /\ LIST_REL v_rel vs1 vs2
  ==>
  ?t2 r2. result_rel v_rel v_rel r1 r2 /\
  state_rel t1 t2 /\ do_app s2 op (REVERSE vs2) = SOME (t2, r2)
Proof
  rw []
  \\ drule_then irule do_app_thm
  \\ simp []
QED

Theorem do_if_helper:
  do_if b x y = SOME e /\ v_rel b b' ==>
  ((b' = Boolv T) = (b = Boolv T)) /\ ((b' = Boolv F) = (b = Boolv F))
Proof
  simp [Once v_rel_cases]
  \\ Cases_on `b`
  \\ rw [Boolv_def]
  \\ EQ_TAC \\ rw [] \\ fs []
QED

Theorem list_max_LESS_EVERY:
  (list_max xs < N) = (0 < N /\ EVERY (\x. x < N) xs)
Proof
  Induct_on `xs`
  \\ simp [list_max_def |> REWRITE_RULE [GSYM MAX_DEF]]
  \\ metis_tac []
QED

Theorem max_dec_name_LESS_EVERY:
  (max_dec_name ns < N) = (0 < N /\ EVERY (\n. dec_name_to_num n < N) ns)
Proof
  Induct_on `ns` \\ simp [max_dec_name_def]
  \\ metis_tac []
QED

Definition encode_val_def:
  encode_val (Litv l) = Litv l /\
  encode_val (Conv stmp xs) = Term
    (case stmp of NONE => NONE | SOME (i, _) => SOME i)
    (MAP encode_val xs) /\
  encode_val (Loc n) = RefPtr n /\
  encode_val others = Other
Termination
  WF_REL_TAC `measure v_size`
  \\ rw []
  \\ fs [MEM_SPLIT, SUM_APPEND, v_size_aux]
End

Theorem decode_test_simulation:
  dt_test test enc_v = SOME b /\
  pure_eval_to s env x v /\
  enc_v = encode_val v
  ==>
  pure_eval_to s env (decode_test tr test x) (Boolv b)
Proof
  Cases_on `test` \\ Cases_on `v`
  \\ simp [encode_val_def]
  \\ EVERY_CASE_TAC
  \\ rw []
  \\ fs [dt_test_def]
  \\ fs [decode_test_def, pure_eval_to_def, evaluate_def]
  \\ simp [do_app_def, do_eq_def, lit_same_type_sym]
  \\ rw [Boolv_def]
QED

Theorem app_pos_Term_IMP:
  !xs n. app_pos refs (Pos n pos) (Term c xs) = SOME y ==>
  n < LENGTH xs /\ app_pos refs pos (EL n xs) = SOME y
Proof
  Induct_on `xs`
  \\ simp [app_pos_def]
  \\ rw []
  \\ Cases_on `n`
  \\ fs [app_pos_def]
QED

Definition encode_refs_def:
  encode_refs s = FUN_FMAP (\i. encode_val (case EL i s.refs of Refv v => v))
    (count (LENGTH s.refs) ∩ {i | ?v. EL i s.refs = Refv v})
End

Theorem FLOOKUP_encode_refs:
  FLOOKUP (encode_refs s) n = if n < LENGTH s.refs
  then (case EL n s.refs of Refv v => SOME (encode_val v) | _ => NONE)
  else NONE
Proof
  simp [encode_refs_def, FLOOKUP_FUN_FMAP]
  \\ EVERY_CASE_TAC \\ simp []
QED

Theorem decode_pos_simulation:
  !pos exp x. app_pos (encode_refs s) pos (encode_val x) = SOME enc_y /\
  pure_eval_to s env exp x
  ==>
  ?y. enc_y = encode_val y /\
  pure_eval_to s env (decode_pos tr exp pos) y
Proof
  Induct
  \\ simp [app_pos_def, decode_pos_def]
  \\ rw []
  \\ fs [pure_eval_to_def]
  \\ first_x_assum irule
  \\ Cases_on `n` \\ Cases_on `x` \\ fs [app_pos_def, encode_val_def]
  >- (
    Cases_on `l` \\ fs [app_pos_def]
    \\ simp [evaluate_def, do_app_def]
  )
  >- (
    fs [option_case_eq]
    \\ simp [evaluate_def, do_app_def]
    \\ fs [store_lookup_def, FLOOKUP_encode_refs, case_eq_thms]
  )
  >- (
    simp [evaluate_def, do_app_def]
    \\ Cases_on `l` \\ fs [app_pos_def]
    \\ drule app_pos_Term_IMP
    \\ csimp [EL_MAP]
  )
QED

Theorem fold_Boolv = GSYM (LIST_CONJ [
  Boolv_def |> REWRITE_RULE [GSYM backend_commonTheory.bool_to_tag_def],
  backend_commonTheory.bool_to_tag_def])

Theorem do_eq_Boolv:
  do_eq (Boolv x) (Boolv y) = Eq_val (x = y)
Proof
  EVAL_TAC \\ EVERY_CASE_TAC \\ fs []
QED

Theorem do_if_Boolv:
  do_if (Boolv x) y z = SOME (if x then y else z)
Proof
  EVAL_TAC \\ EVERY_CASE_TAC \\ fs []
QED

val init_in_c_imps1 = ASSUME ``initial_ctors ⊆ c``
  |> SIMP_RULE (srw_ss()) [initial_ctors_def]
  |> CONJUNCTS |> map DISCH_ALL

Theorem init_in_c_bool_tag:
  initial_ctors ⊆ c ==>
  ((bool_to_tag bv,SOME bool_id),0) ∈ c
Proof
  rw [initial_ctors_def, backend_commonTheory.bool_to_tag_def]
QED

Theorem decode_guard_simulation:
  !b. dt_eval_guard (encode_refs s) (encode_val y) gd = SOME b /\
  pure_eval_to s env x y /\
  initial_ctors ⊆ s.c /\
  initial_ctors ⊆ env.c
  ==>
  pure_eval_to s env (decode_guard tr x gd) (Boolv b)
Proof
  Induct_on `gd`
  \\ simp [decode_guard_def, FORALL_PROD, dt_eval_guard_def]
  \\ fs [pure_eval_to_def, evaluate_def, option_case_eq]
  \\ rw []
  \\ imp_res_tac init_in_c_bool_tag
  \\ fs [Bool_def, evaluate_def, fold_Boolv, do_app_def, do_eq_Boolv,
        do_if_Boolv, bool_case_eq]
  \\ drule decode_test_simulation
  \\ fs [pure_eval_to_def]
  \\ disch_then irule
  \\ drule decode_pos_simulation
  \\ simp [pure_eval_to_def]
  \\ disch_then drule
  \\ metis_tac []
QED

val v_cons_in_c_exn_simps = map (QCONV (SIMP_CONV (srw_ss())
    [subscript_exn_v_def, bind_exn_v_def, chr_exn_v_def, div_exn_v_def]))
  [``v_cons_in_c c subscript_exn_v``,
    ``v_cons_in_c c bind_exn_v``,
    ``v_cons_in_c c chr_exn_v``,
    ``v_cons_in_c c div_exn_v``];

Theorem init_in_c_imps2:
  (initial_ctors ⊆ c ==> v_cons_in_c c Unitv) /\
  (initial_ctors ⊆ c ==> v_cons_in_c c (Boolv b))
Proof
  rw [Unitv_def, Boolv_def] \\ fs [initial_ctors_def]
QED

Theorem init_in_c_list_to_v:
  initial_ctors ⊆ c ==>
  v_cons_in_c c (list_to_v xs) = EVERY (v_cons_in_c c) xs
Proof
  Induct_on `xs` \\ simp [list_to_v_def, list_ctors_def, initial_ctors_def]
QED

val init_in_c_simps = init_in_c_imps1 @ v_cons_in_c_exn_simps
    @ CONJUNCTS init_in_c_imps2 @ [init_in_c_list_to_v]

Theorem v_to_list_in_c:
  !v vs. v_to_list v = SOME vs /\ v_cons_in_c c v ==>
  EVERY (v_cons_in_c c) vs
Proof
  ho_match_mp_tac v_to_list_ind
  \\ simp [v_to_list_def, case_eq_thms]
  \\ rw [] \\ simp []
QED

Theorem simp_guard_thm:
  !gd x. dt_eval_guard r v gd = SOME x ==>
  dt_eval_guard r v (simp_guard gd) = SOME x
Proof
  ho_match_mp_tac simp_guard_ind
  \\ rw [simp_guard_def]
  \\ fs [dt_eval_guard_def]
  \\ EVERY_CASE_TAC
  \\ fs []
  \\ rfs []
  \\ metis_tac []
QED

Theorem decode_dtree_simulation:
  pattern_semantics$dt_eval (encode_refs s) (encode_val y) dtree = SOME v /\
  pure_eval_to s env x y /\
  initial_ctors ⊆ s.c /\
  initial_ctors ⊆ env.c
  ==>
  evaluate env s [decode_dtree tr exps x default_x dtree] =
  evaluate env s [case v of MatchSuccess i => (case lookup i exps of
    SOME exp => exp | NONE => default_x) | _ => default_x]
Proof
  Induct_on `dtree`
  \\ simp [dt_eval_def, decode_dtree_def]
  \\ rw [evaluate_def]
  \\ fs [option_case_eq]
  \\ imp_res_tac simp_guard_thm
  \\ drule_then drule decode_guard_simulation
  \\ rfs [dt_eval_guard_def, init_in_c_bool_tag]
  \\ rw [pure_eval_to_def]
  \\ fs []
  \\ simp [do_if_Boolv]
  \\ CASE_TAC \\ fs []
QED

Definition c_type_map_rel_def:
  c_type_map_rel c type_map = (!stmp ty_id len.
    (((stmp, SOME ty_id), len) ∈ c) ==>
        ?tys. lookup ty_id type_map = SOME tys /\ MEM (stmp, len) tys)
End

Theorem c_type_map_rel_subspt:
  c_type_map_rel c tm /\ subspt tm tm' ==>
  c_type_map_rel c tm'
Proof
  fs [c_type_map_rel_def, subspt_lookup]
  \\ metis_tac []
QED

Theorem ctor_same_type_v_cons_is_sibling:
  ctor_same_type (SOME stmp) (SOME stmp') /\
  c_type_map_rel c tm /\
  (stmp, len) ∈ c /\
  (stmp', len') ∈ c /\
  stmp' = (x, SOME y) ==>
  pattern_semantics$is_sibling (x, len') (lookup y tm)
Proof
  simp [c_type_map_rel_def]
  \\ Cases_on `stmp` \\ Cases_on `stmp'` \\ rw []
  \\ rfs [ctor_same_type_def]
  \\ first_x_assum (fn t => drule t \\ imp_res_tac t)
  \\ rveq \\ fs []
  \\ rveq \\ fs []
  \\ simp [pattern_semanticsTheory.is_sibling_def]
QED

Theorem is_sibling_lookup_subspt:
  pattern_semantics$is_sibling (x, len) (lookup y tm) /\
  subspt tm' tm ==>
  pattern_semantics$is_sibling (x, len) (lookup y tm')
Proof
  rw [subspt_lookup]
  \\ first_x_assum (qspec_then `y` mp_tac)
  \\ Cases_on `lookup y tm` \\ Cases_on `lookup y tm'`
  \\ fs [pattern_semanticsTheory.is_sibling_def]
  \\ rw [] \\ simp []
QED

Theorem encode_pat_match_simulation:
  (! c_env ^s pat v pre_bindings res.
  flatSem$pmatch c_env s pat v pre_bindings = res /\
  res <> Match_type_error /\
  v_cons_in_c s.c v /\
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) s.refs /\
  c_type_map_rel s.c tm
  ==>
  pattern_semantics$pmatch (encode_refs s) (encode_pat tm pat) (encode_val v) =
  (if res = No_match then PMatchFailure else PMatchSuccess)
  ) /\
  (! c_env ^s ps vs pre_bindings res.
  flatSem$pmatch_list c_env s ps vs pre_bindings = res /\
  res <> Match_type_error /\
  EVERY (v_cons_in_c s.c) vs /\
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) s.refs /\
  c_type_map_rel s.c tm
  ==>
  pattern_semantics$pmatch_list (encode_refs s) (MAP (encode_pat tm) ps)
    (MAP encode_val vs) =
  (if res = No_match then PMatchFailure else PMatchSuccess))
Proof
  ho_match_mp_tac flatSemTheory.pmatch_ind
  \\ rpt strip_tac
  \\ fs [encode_pat_def, encode_val_def,
    Q.ISPEC `encode_val` ETA_THM, Q.ISPEC `encode_pat m` ETA_THM]
  \\ fs [flatSemTheory.pmatch_def, pmatch_def]
  \\ TRY (fs [pmatch_stamps_ok_def, bool_case_eq] \\ rveq \\ fs [] \\ NO_TAC)
  >- (
    (* conses *)
    fs [Q.GEN `t` bool_case_eq |> Q.ISPEC `Match_type_error`] \\ fs []
    \\ fs [pmatch_stamps_ok_OPTREL, v_cons_in_c_def, OPTREL_def]
    \\ rfs [] \\ fs []
    \\ simp [pmatch_def]
    \\ drule_then drule ctor_same_type_v_cons_is_sibling
    \\ rpt (disch_then drule)
    \\ every_case_tac \\ fs [ctor_same_type_def, same_ctor_def, pmatch_def,
            pattern_semanticsTheory.is_sibling_def]
    \\ rveq \\ fs []
    \\ rpt strip_tac
    \\ drule_then drule is_sibling_lookup_subspt
    \\ simp []
  )
  >- (
    (* refs *)
    fs [case_eq_thms]
    \\ rveq \\ fs []
    \\ fs [FLOOKUP_encode_refs, store_lookup_def, EVERY_EL]
    \\ first_x_assum drule
    \\ simp []
  )
  >- (
    fs [CaseEq "match_result"]
    \\ rveq \\ fs []
  )
QED

Theorem pmatch_rows_encode:
  !pats j_offs.
  pmatch_rows c_env pats s v <> Match_type_error /\
  v_cons_in_c s.c v /\
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) s.refs /\
  c_type_map_rel s.c cfg.type_map
  ==>
  case (pattern_semantics$match (encode_refs s)
    (MAPi (λj (p,_). (encode_pat cfg.type_map p, j + j_offs)) pats)
        (encode_val v))
    of NONE => F
    | SOME (MatchSuccess n) => ?i env. n = i + j_offs /\ i < LENGTH pats /\
        pmatch c_env s (FST (EL i pats)) v [] = Match env /\
        pmatch_rows c_env pats s v = Match (env, EL i pats)
    | _ => pmatch_rows c_env pats s v = No_match
Proof
  Induct_on `pats`
  \\ simp [FORALL_PROD, pmatch_rows_def, match_def]
  \\ rw []
  \\ qmatch_asmsub_abbrev_tac `pmatch _ _ hd_pat _ []`
  \\ Cases_on `pmatch c_env s hd_pat v [] = Match_type_error`
  \\ fs []
  \\ drule_then drule
    (SIMP_RULE bool_ss [] (CONJUNCT1 (Q.INST [`tm'` |-> `tm`] encode_pat_match_simulation)))
  \\ simp [combinTheory.o_ABS_L]
  \\ disch_then drule
  \\ first_x_assum (qspec_then `SUC j_offs` mp_tac)
  \\ simp_tac (bool_ss ++ numSimps.ARITH_AC_ss) [ADD1]
  (* make this variable sort left by hand. ugh *)
  \\ qabbrev_tac `aj_offs = j_offs`
  \\ rw []
  >- (
    (* match failed *)
    rpt (CASE_TAC \\ fs [])
    \\ rfs []
    \\ simp [GSYM ADD1]
  )
  \\ Cases_on `pmatch c_env s hd_pat v []` \\ fs []
  \\ EVERY_CASE_TAC \\ fs []
  \\ qexists_tac `0` \\ simp []
QED

Theorem naive_pattern_match_correct:
  !t mats vs exp res bindings.
  naive_pattern_match t mats = exp /\
  pmatch_list c_env s (MAP FST mats) vs bindings = res /\
  res <> Match_type_error /\
  LIST_REL (pure_eval_to s env) (MAP SND mats) vs /\
  initial_ctors ⊆ s.c /\
  initial_ctors ⊆ env.c ==>
  pure_eval_to s env exp (Boolv (res <> No_match))
Proof
  ho_match_mp_tac naive_pattern_match_ind
  \\ simp [naive_pattern_match_def]
  \\ rw []
  \\ fs [pure_eval_to_def, evaluate_def, Bool_def, init_in_c_bool_tag,
        fold_Boolv, flatSemTheory.pmatch_def]
  \\ Cases_on `y` \\ fs [flatSemTheory.pmatch_def]
  >- (
    (* lit eq *)
    fs [do_app_def, do_eq_def]
    \\ rw []
    \\ fs [lit_same_type_sym, do_if_Boolv]
    \\ EVERY_CASE_TAC \\ fs []
    \\ simp [evaluate_def, Bool_def, fold_Boolv, init_in_c_bool_tag]
  )
  >- (
    (* cons no tag *)
    rw [] \\ fs [pmatch_stamps_ok_OPTREL, OPTREL_def]
    \\ first_x_assum (qspecl_then [`l ++ ys`, `bindings`] mp_tac)
    \\ simp [flatPropsTheory.pmatch_list_append, o_DEF]
    \\ simp [listTheory.LIST_REL_APPEND_EQ]
    \\ simp [LIST_REL_EL_EQN, pure_eval_to_def, evaluate_def, do_app_def]
  )
  >- (
    (* cons with tag *)
    qmatch_goalsub_abbrev_tac `if ~ ok then Match_type_error else _`
    \\ Cases_on `ok` \\ fs []
    \\ fs [markerTheory.Abbrev_def, pmatch_stamps_ok_OPTREL, OPTREL_SOME]
    \\ rveq \\ fs []
    \\ rename [`ctor_same_type (SOME stmp) (SOME stmp')`]
    \\ Cases_on `stmp` \\ Cases_on `stmp'`
    \\ fs [ctor_same_type_def]
    \\ rveq \\ fs []
    \\ simp [do_app_def]
    \\ simp [do_if_Boolv]
    \\ rw [] \\ fs [] \\ simp [evaluate_def, fold_Boolv, init_in_c_bool_tag]
    \\ TRY (EVERY_CASE_TAC \\ fs [] \\ NO_TAC)
    \\ first_x_assum (qspecl_then [`l ++ ys`, `bindings`] mp_tac)
    \\ simp [flatPropsTheory.pmatch_list_append, o_DEF]
    \\ simp [listTheory.LIST_REL_APPEND_EQ]
    \\ simp [LIST_REL_EL_EQN, pure_eval_to_def, evaluate_def, do_app_def]
  )
  >- (
    (* ref *)
    CASE_TAC \\ fs []
    \\ CASE_TAC \\ fs []
    \\ fs [PULL_EXISTS, flatSemTheory.pmatch_def]
    \\ fs [do_app_def]
  )
QED

Theorem naive_pattern_matches_correct:
  !t x mats dflt exp v res.
  naive_pattern_matches t x mats dflt = exp /\
  pure_eval_to s env x v /\
  pmatch_rows env mats s v = res /\
  res <> Match_type_error /\
  initial_ctors ⊆ s.c /\
  initial_ctors ⊆ env.c ==>
  evaluate env s [exp] = (case res of Match (_, _, exp) =>
      evaluate env s [exp]
    | _ => evaluate env s [dflt])
Proof
  ho_match_mp_tac naive_pattern_matches_ind
  \\ simp [naive_pattern_matches_def, pmatch_rows_def]
  \\ rw []
  \\ simp [evaluate_def]
  \\ `?pm_exp. naive_pattern_match t [(p,x)] = pm_exp` by simp []
  \\ drule naive_pattern_match_correct
  \\ simp [PULL_EXISTS, flatSemTheory.pmatch_def]
  \\ disch_then (qspecl_then [`s`, `env`, `env`, `[]`, `v`] mp_tac)
  \\ fs [pure_eval_to_def]
  \\ impl_tac
  >- rpt (CASE_TAC \\ fs [])
  \\ simp [do_if_Boolv]
  \\ rpt (CASE_TAC \\ fs [])
QED

Theorem pmatch_rows_same_FST:
  !pats pats2. MAP FST pats = MAP FST pats2 ==>
  case pmatch_rows c_env pats s v of
    | Match_type_error => pmatch_rows c_env pats2 s v = Match_type_error
    | No_match => pmatch_rows c_env pats2 s v = No_match
    | Match (env,p,e) => ?i. i < LENGTH pats2 /\ EL i pats = (p, e) /\
        pmatch_rows c_env pats2 s v = Match (env, EL i pats2)
Proof
  Induct \\ simp [pmatch_rows_def]
  \\ gen_tac \\ Cases \\ simp []
  \\ Cases_on `h` \\ Cases_on `h'`
  \\ simp [pmatch_rows_def]
  \\ rw []
  \\ first_x_assum drule
  \\ rpt (CASE_TAC \\ fs [])
  \\ rw []
  \\ TRY (qexists_tac `0` \\ simp [] \\ NO_TAC)
  \\ TRY (qexists_tac `SUC i` \\ simp [] \\ NO_TAC)
QED

Triviality comp_thm = pattern_compTheory.comp_thm
  |> REWRITE_RULE [GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE]
  |> SIMP_RULE bool_ss [IS_SOME_EXISTS, PULL_EXISTS]

Theorem evaluate_compile_pats:
  pmatch_rows env pats s v <> Match_type_error /\
  pure_eval_to s env exp v /\
  v_cons_in_c s.c v /\
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) s.refs /\
  c_type_map_rel s.c cfg.type_map /\
  initial_ctors ⊆ s.c /\
  initial_ctors ⊆ env.c
  ==>
  evaluate env s [compile_pats cfg naive t N exp default_x pats] =
  evaluate env s [case pmatch_rows env pats s v of
    | Match (env', p', e') => compile_pat_rhs t N exp (p', e')
    | _ => default_x]
Proof
  rw [compile_pats_def]
  \\ fs []
  >- (
    (* naive case *)
    drule (SIMP_RULE bool_ss [] naive_pattern_matches_correct)
    \\ disch_then (fn t => DEP_REWRITE_TAC [t])
    \\ simp []
    \\ qmatch_goalsub_abbrev_tac `ZIP map_pats`
    \\ Q.ISPECL_THEN [`s`, `v`, `env`, `ZIP map_pats`, `pats`] mp_tac
        (Q.GENL [`s`, `v`, `c_env`] pmatch_rows_same_FST)
    \\ fs [markerTheory.Abbrev_def, MAP_ZIP]
    \\ rpt (CASE_TAC \\ fs [])
    \\ rw []
    \\ rfs [EL_ZIP, EL_MAP]
  )
  \\ drule (Q.SPECL [`pats`, `0`] pmatch_rows_encode)
  \\ rpt (disch_then drule)
  \\ TOP_CASE_TAC
  \\ imp_res_tac comp_thm
  \\ drule_then drule decode_dtree_simulation
  \\ simp [lookup_fromList]
  \\ EVERY_CASE_TAC \\ fs []
  \\ simp [EL_MAP]
QED

Theorem compile_match_pmatch_rows:
  !pats k sg pats2 res.
  compile_match cfg pats = (k, sg, pats2) /\
  state_rel s t /\
  v_rel v v' /\
  k <= N /\
  env_rel N c_env1 c_env2 /\
  pmatch_rows c_env1 pats s v = res ==>
  case res of
    | Match_type_error => T
    | No_match => pmatch_rows c_env2 pats2 t v' = No_match
    | Match (env, p, e) => ?i env'. i < LENGTH pats /\ i < LENGTH pats2 /\
        (p, e) = EL i pats /\ nv_rel N env env' /\
        pmatch_rows c_env2 pats2 t v' = Match (env', EL i pats2)
Proof
  Induct
  \\ simp [FORALL_PROD, compile_exp_def, pmatch_rows_def]
  \\ rw []
  \\ `?vs. c_env2 = c_env1 with <| v := vs |>`
    by fs [env_rel_def, environment_component_equality]
  \\ rpt (pairarg_tac \\ fs [])
  \\ Cases_on `pmatch c_env1 s p_1 v []` \\ fs []
  \\ drule (CONJUNCT1 pmatch_thm)
  \\ simp []
  \\ disch_then (drule_then drule)
  \\ simp []
  \\ disch_then (qspecl_then [`N`, `[]`] mp_tac)
  \\ simp [ALOOKUP_rel_empty]
  \\ rw []
  \\ fs [pmatch_rows_def]
  \\ EVERY_CASE_TAC \\ fs [match_rel_def]
  \\ TRY (qexists_tac `0` \\ simp [] \\ NO_TAC)
  \\ TRY (qexists_tac `SUC i'` \\ simp [] \\ NO_TAC)
QED

Theorem compile_match_EL:
  !pats pats2 k sg i.
  compile_match cfg pats = (k, sg, pats2) /\
  i < LENGTH pats /\
  EL i pats = (pat, exp) ==>
  ?exp_i sg exp'.
  compile_exp cfg exp = (exp_i, sg, exp') /\
  EL i pats2 = (pat, exp') /\
  exp_i <= k /\ max_dec_name (pat_bindings pat []) <= k
Proof
  Induct
  \\ simp [FORALL_PROD, compile_exp_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ imp_res_tac LENGTH_compile_exps_IMP
  \\ Cases_on `i`
  \\ fs [] \\ rveq \\ fs []
  \\ first_x_assum drule
  \\ rw []
  \\ simp []
QED

Theorem evaluate_compile_pat_rhs:
  evaluate (env2 with v updated_by f) s
    [compile_pat_rhs tr N (Var_local tr (enc_num_to_name N ""))
    (p, exp)] = (t, res) /\
  pmatch env2 s p v [] = Match bindings /\
  env_rel M env1 env2 /\
  nv_rel M l_bindings bindings /\
  f env2.v = (enc_num_to_name N "", v) :: env2.v /\
  N <= M /\
  EVERY (v_cons_in_c s.c ∘ SND) env2.v /\
  v_cons_in_c s.c v /\
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) s.refs /\
  max_dec_name (pat_bindings p []) < N - 1
  ==>
  ?ext_env.
  evaluate ext_env s [exp] = (t, res) /\
  env_rel (N - 1) (env1 with <| v := l_bindings ++ env1.v |>) ext_env /\
  EVERY (v_cons_in_c s.c ∘ SND) ext_env.v
Proof
  simp [compile_pat_rhs_def, max_dec_name_LESS_EVERY]
  \\ qmatch_goalsub_abbrev_tac `evaluate _ _ [SND comp]`
  \\ PairCases_on `comp`
  \\ fs [markerTheory.Abbrev_def, Q.ISPEC `(a, b)` EQ_SYM_EQ]
  \\ rw []
  \\ drule (compile_pat_bindings_simulation |> SPEC_ALL |> Q.GEN `vs`
        |> Q.SPEC `[v]`)
  \\ simp [flatSemTheory.pmatch_def, CaseEq "match_result"]
  \\ rpt (disch_then drule)
  \\ disch_then (qspecl_then [`N - 1`, `env2.v`] mp_tac)
  \\ simp []
  \\ impl_tac
  >- (
    simp [ALOOKUP_rel_def, pure_eval_to_def, evaluate_def, dec_enc]
    \\ rw [] \\ fs [dec_enc]
  )
  \\ rw []
  \\ asm_exists_tac
  \\ fs [env_rel_def]
  \\ fs [ALOOKUP_rel_def, ALOOKUP_APPEND]
  \\ rw []
  \\ rpt (first_x_assum (qspec_then `x` mp_tac))
  \\ simp [OPTREL_def, case_eq_thms]
  \\ rw [] \\ fs []
QED

Theorem do_app_v_inv:
  do_app s op vs = SOME (t, r) /\
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) s.refs /\
  EVERY (OPTION_ALL (v_cons_in_c s.c)) s.globals /\
  initial_ctors ⊆ s.c /\
  EVERY (v_cons_in_c s.c) vs
  ==>
  t.c = s.c /\
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) t.refs /\
  EVERY (OPTION_ALL (v_cons_in_c s.c)) t.globals /\
  EVERY (v_cons_in_c s.c) (result_vs (list_result r))
Proof
  simp [do_app_def, case_eq_thms, pair_case_eq, bool_case_eq, store_alloc_def,
    store_assign_def]
  \\ rpt disch_tac \\ fs []
  \\ rveq \\ simp init_in_c_simps
  \\ TRY (pairarg_tac \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [])
  \\ fs [IMP_EVERY_LUPDATE, EVERY_MAP, IS_SOME_EXISTS, GREATER_EQ,
    NOT_LESS_EQUAL, EVERY_REPLICATE]
  \\ TRY (drule_then drule EVERY_EL_IMP \\ simp [])
  \\ TRY (
    drule_then drule v_to_list_in_c
    \\ imp_res_tac v_to_list_in_c
    \\ simp []
  )
  \\ fs [store_lookup_def]
  \\ rw [IMP_EVERY_LUPDATE]
  \\ drule_then drule EVERY_EL_IMP \\ rw []
  \\ drule_then drule EVERY_EL_IMP \\ rw []
QED

Theorem do_opapp_v_inv:
  do_opapp vs = SOME (env, exp) /\
  EVERY (v_cons_in_c c) vs
  ==>
  EVERY (v_cons_in_c c ∘ SND) env.v
Proof
  simp [do_opapp_def, case_eq_thms]
  \\ rw [] \\ fs []
  \\ fs [find_recfun_ALOOKUP, pair_case_eq]
  \\ rveq \\ fs [build_rec_env_eq_MAP, EVERY_MAP]
  \\ simp [UNCURRY]
QED

Theorem state_rel_dec_clock:
  state_rel s1 s2 ==> state_rel (dec_clock s1) (dec_clock s2)
Proof
  simp [state_rel_def, dec_clock_def]
QED

Theorem OPTION_ALL_FORALL:
  OPTION_ALL P x = (!y. x = SOME y ==> P y)
Proof
  Cases_on `x` \\ simp []
QED

Theorem v_cons_in_c_SUBSET:
  !c v. v_cons_in_c c v ==> c ⊆ c' ==> v_cons_in_c c' v
Proof
  ho_match_mp_tac v_cons_in_c_def1_ind
  \\ rw []
  \\ EVERY_CASE_TAC \\ rw [] \\ fs [EVERY_MEM, FORALL_PROD]
  \\ metis_tac [SUBSET_DEF]
QED

Definition cfg_inv_def:
  cfg_inv cfg s <=>
  EVERY (EVERY (v_cons_in_c s.c) ∘ store_v_vs) s.refs /\
  EVERY (OPTION_ALL (v_cons_in_c s.c)) s.globals /\
  initial_ctors ⊆ s.c /\
  ~ MEM [] (toList cfg.type_map) /\
  c_type_map_rel s.c cfg.type_map
End

Theorem cfg_inv_dec_clock:
  cfg_inv cfg (dec_clock s) = cfg_inv cfg s
Proof
  simp [dec_clock_def, cfg_inv_def]
QED

Theorem v_to_environment_rel:
  v_to_environment envv = SOME env /\ v_rel envv envv' ==>
  v_to_environment envv' = SOME env
Proof
  cheat
QED

Theorem v_to_decs_rel:
  v_to_decs decsv = SOME decs /\ v_rel decsv decsv' ==>
  v_to_decs decsv' = SOME decs
Proof
  cheat
QED

Theorem environment_to_v_rel:
  v_rel (environment_to_v env) (environment_to_v env)
Proof
  cheat
QED

Theorem do_eval_thm:
  do_eval (REVERSE xs) s = SOME (decs, s', rv) /\
  state_rel s t /\
  LIST_REL v_rel xs ys ==>
  ?rv' cfg' decs' t'.
  do_eval (REVERSE ys) t = SOME (decs', t', rv') /\
  state_rel s' t' /\
  v_rel rv rv' /\
  decs' = SND (compile_decs cfg' decs) /\
  t'.c = t.c
Proof
  rw [state_rel_def, extend_eval_config_def]
  \\ fs [do_eval_def, case_eq_thms]
  \\ fs [Q.SPECL [`xs`, `[y1; y2]`] listTheory.SWAP_REVERSE_SYM]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ rveq \\ fs []
  \\ drule_then drule v_to_environment_rel
  \\ drule_then drule v_to_decs_rel
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ qexists_tac `st`
  \\ simp [environment_to_v_rel]
QED

Theorem EVERY_v_cons_in_c_SUBSET:
  !vs. EVERY (v_cons_in_c c) vs /\ c ⊆ c' ==> EVERY (v_cons_in_c c') vs
Proof
  simp [EVERY_MEM] \\ metis_tac [v_cons_in_c_SUBSET]
QED

Theorem EVERY_v_cons_in_c_o_SUBSET = EVERY_v_cons_in_c_SUBSET
    |> Q.SPEC `MAP f xs`
    |> REWRITE_RULE [EVERY_MAP, GSYM o_DEF]

Triviality initial_ctors_env_rel:
  env_rel N env1 env2 ==> initial_ctors ⊆ env1.c /\ initial_ctors ⊆ env2.c
Proof
  simp [env_rel_def]
QED

Theorem evaluate_decs_sing:
  evaluate_decs s c [d] = evaluate_dec s c d
Proof
  simp [flatSemTheory.evaluate_def]
  \\ every_case_tac \\ simp []
QED

val cfg_inv_cheat = Q.prove (`cfg_inv cfg s`, cheat);

val evaluate_ind2 = induct_tweakLib.list_single_induct evaluate_ind;

Theorem compile_exps_evaluate:
  (!env1 ^s1 xs t1 r1 i sg ys N env2 s2 cfg.
    evaluate env1 s1 xs = (t1, r1) /\
    compile_exps cfg xs = (i, sg, ys) /\
    env_rel N env1 env2 /\ state_rel s1 s2 /\ i < N /\
    cfg_inv cfg s2 /\
    EVERY (v_cons_in_c s2.c ∘ SND) env2.v /\
    initial_ctors ⊆ s2.c /\
    r1 <> Rerr (Rabort Rtype_error)
    ==>
    ?t2 r2.
      result_rel (LIST_REL v_rel) v_rel r1 r2 /\
      state_rel t1 t2 /\
      evaluate env2 s2 ys = (t2, r2) /\
      cfg_inv cfg t2 /\
      EVERY (v_cons_in_c t2.c) (result_vs r2) /\
      s2.c ⊆ t2.c
  ) /\
  (!^s1 c decs s2 t1 cfg c' cfg' decs' res.
  evaluate_decs s1 c decs = (t1, c', res) /\
  compile_decs cfg decs = (cfg', decs') /\
  state_rel s1 s2 /\
  initial_ctors ⊆ s2.c /\
  initial_ctors ⊆ c /\
  cfg_inv cfg s2 /\
  res <> SOME (Rabort Rtype_error)
  ==>
  ?t2 res'.
  evaluate_decs s2 c decs' = (t2, c', res') /\
  OPTREL (exc_rel v_rel) res res' /\
  initial_ctors ⊆ t2.c /\
  initial_ctors ⊆ c' /\
  cfg_inv cfg' t2 /\
  state_rel t1 t2
  )
Proof
  ho_match_mp_tac evaluate_ind2
  \\ simp [evaluate_decs_sing]
  \\ simp [evaluate_def, compile_exp_def, compile_decs_def, result_vs_def]
  \\ rpt (gen_tac ORELSE disch_tac ORELSE conj_tac)
  \\ simp [v_rel_rules]
  \\ fs [pair_case_eq,
    Q.GEN `t` bool_case_eq |> Q.ISPEC `(x, Rerr (Rabort Rtype_error))`,
    Q.GEN `f` bool_case_eq |> Q.ISPEC `(x, Rerr (Rabort Rtype_error))`]
  \\ fs []
  \\ fs [miscTheory.UNCURRY_eq_pair, PULL_EXISTS]
  \\ rpt (pairarg_tac \\ fs [])
  \\ imp_res_tac LENGTH_compile_exps_IMP
  \\ fs [quantHeuristicsTheory.LIST_LENGTH_2, listTheory.LENGTH_CONS]
  \\ rveq \\ fs [evaluate_def, v_rel_rules, GSYM PULL_FORALL]
  \\ TRY (rename [`rv_1 ≠ Rerr (Rabort Rtype_error) ==> _`]
    \\ (Cases_on `rv_1 = Rerr (Rabort Rtype_error)` >- fs [])
    \\ fs [])
  \\ TRY (rename [`rv_1 ≠ Rerr (Rabort Rtype_error) /\ _`]
    \\ (Cases_on `rv_1 = Rerr (Rabort Rtype_error)` >- fs [])
    \\ fs [])
  >- (
    rpt (first_x_assum drule \\ rw [])
    \\ rveq \\ fs []
    \\ fs [case_eq_thms, pair_case_eq] \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_length
    \\ rfs [] \\ fs []
    \\ first_x_assum drule
    \\ rpt (disch_then drule)
    \\ (impl_tac >- metis_tac [EVERY_v_cons_in_c_o_SUBSET, SUBSET_TRANS])
    \\ rw []
    \\ fs [quantHeuristicsTheory.LIST_LENGTH_2, listTheory.LENGTH_CONS]
    \\ rveq \\ fs []
    \\ rveq \\ fs []
    \\ metis_tac [v_cons_in_c_SUBSET, SUBSET_TRANS]
  )
  >- (
    rpt (first_x_assum drule \\ rw [])
    \\ rveq \\ fs []
    \\ simp [evaluate_def, v_cons_in_c_def]
    \\ fs [case_eq_thms, pair_case_eq] \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_length
    \\ rpt (first_x_assum drule \\ rw [])
    \\ fs [quantHeuristicsTheory.LIST_LENGTH_2, listTheory.LENGTH_CONS]
    \\ rveq \\ fs []
  )
  >- (
    (* Handle *)
    simp [evaluate_def, pat_bindings_def, pmatch_rows_def,
        flatSemTheory.pmatch_def]
    \\ fs [case_eq_thms] \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ rw []
    \\ first_x_assum (drule_then (drule_then drule))
    \\ TRY (fs [MAX_ADD_LESS, PULL_EXISTS] \\ NO_TAC)
    (* down to raise+pmatch case *)
    \\ impl_tac >- fs [MAX_ADD_LESS]
    \\ rw []
    \\ fs [result_vs_def]
    \\ rename [`compile_match _ _ = (k, _)`]
    \\ DEP_REWRITE_TAC [Q.GEN `v` evaluate_compile_pats |> Q.SPEC `v'`]
    \\ simp [pure_eval_to_def, evaluate_def]
    \\ rfs [cfg_inv_def]
    \\ `k <= N` by fs [MAX_ADD_LESS]
    \\ drule_then drule compile_match_pmatch_rows
    \\ rpt (disch_then drule)
    \\ imp_res_tac initial_ctors_env_rel
    \\ fs [CaseEq "match_result", pair_case_eq, bool_case_eq] \\ rveq
    \\ fs [] \\ rfs [] \\ simp [evaluate_def, result_vs_def]
    (* down to Match case *)
    \\ rpt disch_tac
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ drule_then (drule_then drule) compile_match_EL
    \\ rw [] \\ fs []
    \\ imp_res_tac pmatch_rows_IMP_pmatch
    \\ qmatch_goalsub_abbrev_tac `x = (_, _)`
    \\ PairCases_on `x`
    \\ fs [markerTheory.Abbrev_def, Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ drule evaluate_compile_pat_rhs
    \\ rpt (disch_then drule)
    \\ simp [LESS_MAX_ADD]
    \\ impl_tac >- metis_tac [EVERY_v_cons_in_c_o_SUBSET]
    \\ disch_tac
    \\ fs []
    \\ last_x_assum (drule_then (drule_then drule))
    \\ fs [LESS_MAX_ADD, SUBSET_DEF]
  )
  >- (
    (* Conv, no tag *)
    last_x_assum (drule_then (drule_then drule))
    \\ rw [] \\ simp []
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ rveq \\ fs []
    \\ rfs []
    \\ fs []
    \\ simp [v_rel_rules, EVERY_REVERSE]
  )
  >- (
    (* Conv with tag *)
    last_x_assum (drule_then (drule_then drule))
    \\ simp [bool_case_eq]
    \\ rw [] \\ simp []
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ rveq \\ fs []
    \\ simp [PULL_EXISTS, v_rel_rules, EVERY_REVERSE]
    \\ imp_res_tac evaluate_length
    \\ imp_res_tac state_rel_IMP_c
    \\ fs [env_rel_def]
    \\ rfs []
    \\ imp_res_tac SUBSET_IMP
    \\ fs []
  )
  >- (
    drule_then drule env_rel_ALOOKUP
    \\ strip_tac \\ fs [optionTheory.OPTREL_def]
  )
  >- (
    fs [option_case_eq]
    \\ CASE_TAC \\ fs []
    \\ imp_res_tac ALOOKUP_MEM
    \\ fs [EVERY_MEM]
    \\ res_tac
    \\ fs []
  )
  >- (
    simp [Once v_rel_cases]
    \\ fs [env_rel_def]
    \\ metis_tac [FST, SND, HD]
  )
  >- (
    (* App *)
    last_x_assum (drule_then (drule_then drule))
    \\ rw []
    \\ fs [case_eq_thms] \\ rveq \\ fs [] \\ rveq \\ rfs []
    \\ fs []
    \\ Cases_on `op = Opapp`
    >- (
      fs [option_case_eq, pair_case_eq]
      \\ rveq \\ fs []
      \\ drule_then drule do_opapp_thm_REVERSE
      \\ rw []
      \\ imp_res_tac state_rel_IMP_clock
      \\ imp_res_tac LENGTH_compile_exps_IMP
      \\ fs [bool_case_eq, quantHeuristicsTheory.LIST_LENGTH_2]
      \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ]
      \\ imp_res_tac state_rel_dec_clock
      \\ last_x_assum drule
      \\ rpt (disch_then drule)
      \\ impl_tac
      \\ simp [cfg_inv_dec_clock]
      \\ simp [EVAL ``(dec_clock s).c``]
      \\ simp [cfg_inv_cheat]
      \\ metis_tac [do_opapp_v_inv, EVERY_REVERSE, SUBSET_TRANS]
    )
    \\ Cases_on `op = Eval`
    >- (
      fs [option_case_eq, pair_case_eq]
      \\ rveq \\ fs []
      \\ drule_then drule do_eval_thm
      \\ rpt (disch_then drule)
      \\ rpt strip_tac \\ fs []
      \\ imp_res_tac state_rel_IMP_clock
      \\ fs [bool_case_eq, Q.ISPEC `(a, b)` EQ_SYM_EQ]
      \\ fs [pair_case_eq]
      \\ rename [`_ = SND (compile_decs cfg' decs2)`]
      \\ Cases_on `compile_decs cfg' decs2`
      \\ fs [] \\ rveq \\ fs []
      \\ simp [cfg_inv_cheat]
      \\ first_assum (assume_tac o MATCH_MP state_rel_dec_clock)
      \\ last_x_assum (drule_then drule)
      \\ simp [EVAL ``(dec_clock s).c``, cfg_inv_cheat]
      \\ impl_tac >- (fs [env_rel_def, SUBSET_DEF] \\ CCONTR_TAC \\ fs [])
      \\ rw []
      \\ fs [option_case_eq] \\ rveq \\ fs []
      \\ rfs [env_rel_def, PULL_EXISTS, OPTREL_def]
      \\ simp [PULL_EXISTS]
      \\ fs [SUBSET_DEF]
      \\ cheat (* eval .c and v_cons props *)
    )
    \\ fs [option_case_eq, pair_case_eq]
    \\ rveq \\ fs []
    \\ drule_then (drule_then drule) do_app_thm_REVERSE
    \\ rw []
    \\ drule do_app_const
    \\ drule do_app_v_inv
    \\ simp [cfg_inv_cheat]
    \\ fs [cfg_inv_def, EVERY_REVERSE]
  )
  >- (
    (* If *)
    last_x_assum (drule_then (drule_then drule))
    \\ rw []
    \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ rveq \\ fs []
    \\ rfs []
    \\ imp_res_tac flatPropsTheory.evaluate_sing
    \\ rveq \\ fs []
    \\ drule_then drule do_if_helper
    \\ rw []
    \\ fs [do_if_def, bool_case_eq]
    \\ rveq \\ fs []
    \\ last_x_assum (drule_then (drule_then drule))
    \\ fs []
    \\ impl_tac >- metis_tac [SUBSET_TRANS, EVERY_v_cons_in_c_o_SUBSET]
    \\ rw []
    \\ simp []
    \\ metis_tac [SUBSET_TRANS, EVERY_v_cons_in_c_o_SUBSET]
  )
  >- (
    (* Mat *)
    simp [evaluate_def, pat_bindings_def, flatSemTheory.pmatch_def]
    \\ last_x_assum (drule_then (drule_then drule))
    \\ impl_tac >- (fs [MAX_ADD_LESS, SUBSET_DEF] \\ CCONTR_TAC \\ fs [])
    \\ rw []
    \\ fs [case_eq_thms] \\ rveq \\ fs [] \\ rveq \\ fs []
    \\ DEP_REWRITE_TAC [Q.GEN `v` evaluate_compile_pats |> Q.SPEC `HD v'`]
    \\ simp [pure_eval_to_def, evaluate_def, libTheory.opt_bind_def]
    \\ imp_res_tac flatPropsTheory.evaluate_sing
    \\ rveq \\ fs []
    \\ rename [`compile_match _ _ = (k, _)`]
    \\ drule_then drule compile_match_pmatch_rows
    \\ rfs [cfg_inv_def]
    \\ `k <= N` by fs [MAX_ADD_LESS]
    \\ rpt (disch_then drule)
    \\ imp_res_tac initial_ctors_env_rel
    \\ fs [CaseEq "match_result", pair_case_eq, bool_case_eq] \\ rveq \\ fs []
    >- (
      (* no match *)
      simp [PULL_EXISTS, evaluate_def]
      \\ rw [bind_exn_v_def, v_rel_l_cases]
      \\ rfs [initial_ctors_def]
    )
    \\ rw [] \\ simp []
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ drule_then (drule_then drule) compile_match_EL
    \\ rw []
    \\ fs []
    \\ imp_res_tac pmatch_rows_IMP_pmatch
    (* pull out evaluate *)
    \\ qmatch_goalsub_abbrev_tac `x = (_, _)`
    \\ PairCases_on `x`
    \\ fs [markerTheory.Abbrev_def, Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ drule_then drule evaluate_compile_pat_rhs
    \\ rpt (disch_then drule)
    \\ simp [LESS_MAX_ADD, libTheory.opt_bind_def]
    \\ impl_tac >- metis_tac [EVERY_v_cons_in_c_o_SUBSET]
    \\ disch_tac \\ fs []
    \\ last_x_assum (drule_then (drule_then drule))
    \\ simp [LESS_MAX_ADD]
    \\ fs [SUBSET_DEF]
  )
  >- (
    (* Let *)
    last_x_assum (drule_then (drule_then drule))
    \\ rw []
    \\ fs [case_eq_thms] \\ rveq \\ fs [] \\ rveq \\ rfs [] \\ fs []
    \\ last_x_assum (first_assum o mp_then (Pat `state_rel _ _`) mp_tac)
    \\ disch_then drule
    \\ imp_res_tac evaluate_sing
    \\ fs []
    \\ qmatch_goalsub_abbrev_tac `evaluate upd_env _ _ = _`
    \\ disch_then (qspecl_then [`N`, `upd_env`] mp_tac)
    \\ reverse impl_tac >- (rw [] \\ simp [] \\ fs [SUBSET_DEF])
    \\ drule_then drule EVERY_v_cons_in_c_o_SUBSET
    \\ fs [env_rel_def, libTheory.opt_bind_def, markerTheory.Abbrev_def]
    \\ CASE_TAC \\ simp []
    \\ simp [ALOOKUP_rel_cons]
    \\ fs [SUBSET_DEF]
  )
  >- (
    fs [bool_case_eq]
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ fs [MAP_MAP_o, o_DEF, UNCURRY, ETA_THM]
    \\ first_x_assum irule
    \\ simp [build_rec_env_eq_MAP, EVERY_MAP, o_DEF]
    \\ asm_exists_tac
    \\ fs [env_rel_def, FILTER_APPEND]
    \\ irule ALOOKUP_rel_append_suff
    \\ simp [UNCURRY, MAP_MAP_o, o_DEF]
    \\ irule ALOOKUP_rel_eq_fst
    \\ rw [LIST_REL_EL_EQN, EL_MAP, UNCURRY]
    \\ simp [Once v_rel_cases]
    \\ fs [ELIM_UNCURRY, list_max_LESS_EVERY, EVERY_MAP, env_rel_def]
    \\ metis_tac []
  )
  >- (
    rename [`compile_dec cfg (Dlet e)`]
    \\ fs [compile_dec_def] \\ rveq \\ fs []
    \\ `?N sg exps. compile_exp cfg e = (N, sg, exps)`
        by metis_tac [pair_CASES]
    \\ last_x_assum drule
    \\ disch_then (first_assum o mp_then (Pat `state_rel _ _`) mp_tac)
    \\ disch_then (qspecl_then [`N + 1`, `<| v := []; c := c |>`] mp_tac)
    \\ simp [env_rel_def, ALOOKUP_rel_empty]
    \\ rveq \\ fs []
    \\ impl_tac >- (CCONTR_TAC \\ fs [])
    \\ rw []
    \\ simp [evaluate_def]
    \\ fs [Unitv_def, case_eq_thms, bool_case_eq]
    \\ rveq \\ fs [v_rel_l_cases]
    \\ rveq \\ fs []
    \\ simp [OPTREL_def]
    \\ fs [SUBSET_DEF]
  )
  >- (
    rename [`compile_dec cfg (Dtype id ctors)`]
    \\ fs [bool_case_eq]
    \\ imp_res_tac state_rel_IMP_c
    \\ fs [compile_dec_def]
    \\ rveq \\ fs []
    \\ simp [evaluate_def, OPTREL_def]
    \\ simp [state_rel_c_update]
    \\ rfs [SUBSET_DEF]
    \\ simp [cfg_inv_cheat]
  )
  >- (
    rename [`compile_dec cfg (Dexn id arity)`]
    \\ imp_res_tac state_rel_IMP_c
    \\ fs [compile_dec_def]
    \\ rveq \\ fs []
    \\ simp [evaluate_def]
    \\ fs [bool_case_eq, OPTREL_def, state_rel_c_update]
    \\ rveq \\ fs []
    \\ rfs [SUBSET_DEF]
    \\ simp [cfg_inv_cheat]
  )
  >- simp [OPTREL_def]
  >- (
    fs [compile_decs_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ fs [UNCURRY_eq_pair, PULL_EXISTS]
    \\ first_x_assum (drule_then drule)
    \\ simp []
    \\ impl_tac >- (CCONTR_TAC \\ fs [])
    \\ simp [evaluate_decs_sing]
    \\ strip_tac
    \\ reverse (fs [OPTREL_def])
    >- (
      (* exception raised *)
      fs [pair_case_eq, option_case_eq]
      \\ rveq \\ fs [] \\ rveq \\ fs []
      \\ simp [cfg_inv_cheat]
    )
    \\ fs []
    \\ first_x_assum (drule_then (drule_then drule))
    \\ simp [cfg_inv_cheat]
    \\ rw []
    \\ fs [pair_case_eq, option_case_eq]
  )
QED

Theorem compile_decs_eval_sim:
  eval_sim ffi prog prog' (Eval ec) (extend_eval_config cfg1 ec)
    (\decs decs'. compile_decs cfg2 decs = (cfg', decs')) F
Proof
  simp [eval_sim_def]
  \\ rpt strip_tac
  \\ qexists_tac `0`
  \\ simp []
  \\ drule_then drule (last (CONJUNCTS compile_exps_evaluate))
  \\ disch_then (qspec_then `initial_state ffi k (extend_eval_config cfg1 ec)`
    mp_tac)
  \\ simp [state_rel_initial_state]
  \\ simp [cfg_inv_cheat]
  \\ impl_tac >- simp [initial_state_def]
  \\ rw []
  \\ fs [OPTREL_def]
  \\ rw []
  \\ fs [state_rel_def]
QED

Theorem compile_decs_semantics:
  compile_decs cfg prog = (cfg', prog') /\
  semantics (Eval ec) ffi prog <> Fail
  ==>
  semantics (Eval ec) ffi prog =
  semantics (extend_eval_config cfg2 ec) ffi prog'
Proof
  rw []
  \\ irule (DISCH_ALL (MATCH_MP (hd (RES_CANON IMP_semantics_eq))
        (UNDISCH_ALL compile_decs_eval_sim)))
  \\ simp []
  \\ asm_exists_tac
  \\ simp []
QED

(* set_globals and esgc properties *)

Theorem set_globals_decode_pos:
  !p exp. set_globals exp = {||} ==>
  set_globals (decode_pos t exp p) = {||}
Proof
  Induct \\ simp [decode_pos_def, op_gbag_def]
QED

Theorem set_globals_decode_test:
  set_globals exp = {||} ==>
  set_globals (decode_test t d exp) = {||}
Proof
  Cases_on `d`
  \\ simp [decode_test_def, op_gbag_def]
QED

Theorem set_globals_decode_guard:
  set_globals exp = {||} ==>
  set_globals (decode_guard t exp gd) = {||}
Proof
  Induct_on `gd` \\ simp [decode_guard_def, Bool_def, op_gbag_def]
  \\ simp [set_globals_decode_test, set_globals_decode_pos]
QED

Theorem set_globals_decode_dtree_empty:
  set_globals x = {||} /\ set_globals dflt = {||} /\
  EVERY (\y. set_globals y = {||}) (toList br_spt) ==>
  set_globals (decode_dtree t br_spt x dflt dtree) = {||}
Proof
  Induct_on `dtree`
  \\ simp [decode_dtree_def]
  \\ rw []
  \\ simp [set_globals_decode_guard]
  \\ CASE_TAC
  \\ fs [EVERY_MEM, FORALL_PROD, MEM_toList]
  \\ metis_tac []
QED

Theorem inv_on_FOLDR:
  !f. (!x v. MEM x xs ==> f (g x v) = f v) ==>
  f (FOLDR g v xs) = f v
Proof
  gen_tac \\ Induct_on `xs` \\ simp []
QED

Theorem set_globals_compile_pat_bindings:
  !t i n_bindings exp.
  EVERY (\(_, _, v_exp). set_globals v_exp = {||}) n_bindings ==>
  set_globals (SND (compile_pat_bindings t i n_bindings exp)) =
  set_globals exp
Proof
  ho_match_mp_tac compile_pat_bindings_ind
  \\ rw [compile_pat_bindings_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ simp [op_gbag_def]
  \\ DEP_REWRITE_TAC [Q.ISPEC `set_globals` inv_on_FOLDR]
  \\ simp [FORALL_PROD, op_gbag_def]
  \\ fs [EVERY_MAP, ELIM_UNCURRY]
QED

Theorem set_globals_naive_pattern_match:
  !t xs. EVERY (\v. set_globals (SND v) = {||}) xs ==>
  set_globals (naive_pattern_match t xs) = {||}
Proof
  ho_match_mp_tac naive_pattern_match_ind
  \\ simp [naive_pattern_match_def, op_gbag_def, Bool_def]
  \\ rw []
  \\ fs []
  \\ fs [EVERY_EL, op_gbag_def]
QED

Theorem set_globals_naive_pattern_matches:
  set_globals x = {||} ==>
  set_globals (naive_pattern_matches t x ps dflt) =
  elist_globals (dflt :: MAP SND ps)
Proof
  Induct_on `ps`
  \\ simp [FORALL_PROD, naive_pattern_matches_def,
        set_globals_naive_pattern_match]
  \\ simp_tac (bool_ss ++ bagSimps.BAG_ss) []
QED

Theorem set_toList_fromList:
  set (toList (fromList xs)) = set xs
Proof
  simp [EXTENSION, MEM_toList, lookup_fromList, MEM_EL]
  \\ metis_tac []
QED

Theorem set_globals_compile_pats:
  (~ naive ==> elist_globals (dflt :: MAP SND ps) = {||}) /\
  set_globals x = {||} ==>
  set_globals (compile_pats cfg naive t N x dflt ps) =
  elist_globals (dflt :: MAP SND ps)
Proof
  simp [compile_pats_def]
  \\ rw []
  >- (
    simp [set_globals_naive_pattern_matches, MAP_ZIP]
    \\ simp [elist_globals_FOLDR]
    \\ irule FOLDR_CONG
    \\ simp [MAP_MAP_o]
    \\ irule MAP_CONG
    \\ simp [FORALL_PROD, compile_pat_rhs_def, set_globals_compile_pat_bindings]
  )
  \\ DEP_REWRITE_TAC [set_globals_decode_dtree_empty]
  \\ simp [EVERY_MEM, set_toList_fromList]
  \\ fs [elist_globals_eq_empty, MEM_MAP, PULL_EXISTS]
  \\ fs [FORALL_PROD, compile_pat_rhs_def, set_globals_compile_pat_bindings]
  \\ metis_tac []
QED

Theorem compile_exp_set_globals:
  (!cfg exp N sg exp'. compile_exp cfg exp = (N, sg, exp')
  ==>
  set_globals exp' = set_globals exp)
  /\
  (!cfg exps N sg exps'. compile_exps cfg exps = (N, sg, exps')
  ==>
  elist_globals exps' = elist_globals exps)
  /\
  (!cfg m N sg m'. compile_match cfg m = (N, sg, m')
  ==>
  elist_globals (MAP SND m') = elist_globals (MAP SND m))
Proof
  ho_match_mp_tac compile_exp_ind
  \\ fs [compile_exp_def]
  \\ fs [miscTheory.UNCURRY_eq_pair, PULL_EXISTS]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ imp_res_tac LENGTH_compile_exps_IMP
  \\ fs [quantHeuristicsTheory.LIST_LENGTH_2, elist_globals_REVERSE]
  \\ rveq \\ fs []
  \\ TRY (DEP_REWRITE_TAC [set_globals_compile_pats]
    \\ imp_res_tac compile_exp_set_globals_tup
    \\ simp [])
  \\ simp [elist_globals_FOLDR] \\ irule FOLDR_CONG
  \\ simp [MAP_MAP_o] \\ irule MAP_CONG
  \\ simp [FORALL_PROD] \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ first_x_assum drule
  \\ imp_res_tac LENGTH_compile_exps_IMP
  \\ fs [quantHeuristicsTheory.LIST_LENGTH_2, elist_globals_REVERSE]
QED

Theorem compile_decs_elist_globals:
  !decs cfg decs' cfg'. compile_decs cfg decs = (cfg', decs')
  ==>
  elist_globals (MAP dest_Dlet (FILTER is_Dlet decs')) =
  elist_globals (MAP dest_Dlet (FILTER is_Dlet decs))
Proof
  Induct
  \\ rw [compile_decs_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ Cases_on `h` \\ fs [compile_dec_def]
  \\ last_x_assum drule \\ rw []
  \\ rveq \\ fs []
  \\ qmatch_goalsub_abbrev_tac `compile_exp cfg exp`
  \\ `?N sg e'. compile_exp cfg exp = (N, sg, e')` by metis_tac [pair_CASES]
  \\ imp_res_tac LENGTH_compile_exps_IMP
  \\ imp_res_tac compile_exp_set_globals
  \\ fs [quantHeuristicsTheory.LIST_LENGTH_2]
QED

Theorem esgc_free_decode_pos:
  !p exp. esgc_free exp ==>
  esgc_free (decode_pos t exp p)
Proof
  Induct \\ simp [decode_pos_def]
QED

Theorem esgc_free_decode_test:
  esgc_free exp ==> esgc_free (decode_test t d exp)
Proof
  Cases_on `d`
  \\ simp [decode_test_def]
QED

Theorem esgc_free_decode_guard:
  esgc_free exp ==> esgc_free (decode_guard t exp gd)
Proof
  Induct_on `gd` \\ simp [decode_guard_def, Bool_def]
  \\ simp [esgc_free_decode_test, esgc_free_decode_pos]
QED

Theorem esgc_free_decode_dtree:
  esgc_free v_exp /\ esgc_free dflt /\
  EVERY (\y. esgc_free y) (toList br_spt) ==>
  esgc_free (decode_dtree t br_spt v_exp dflt dtree)
Proof
  Induct_on `dtree`
  \\ simp [decode_dtree_def]
  \\ rw []
  \\ simp [esgc_free_decode_guard]
  \\ CASE_TAC
  \\ fs [MEM_toList, EVERY_MEM, FORALL_PROD]
  \\ metis_tac []
QED

Theorem esgc_free_compile_pat_bindings:
  !t i n_bindings exp.
  esgc_free exp /\
  EVERY (\(_, _, v_exp). esgc_free v_exp) n_bindings ==>
  esgc_free (SND (compile_pat_bindings t i n_bindings exp))
Proof
  ho_match_mp_tac compile_pat_bindings_ind
  \\ rw [compile_pat_bindings_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ simp [op_gbag_def]
  \\ DEP_REWRITE_TAC [Q.ISPEC `esgc_free` inv_on_FOLDR]
  \\ simp [FORALL_PROD, op_gbag_def]
  \\ fs [EVERY_MAP, ELIM_UNCURRY]
QED

Theorem esgc_free_naive_pattern_match:
  !t xs. EVERY esgc_free (MAP SND xs) ==>
  esgc_free (naive_pattern_match t xs)
Proof
  ho_match_mp_tac naive_pattern_match_ind
  \\ simp [naive_pattern_match_def, Bool_def]
  \\ rw []
  \\ fs [EVERY_EL]
QED

Theorem esgc_free_naive_pattern_matches:
  !t x xs dflt. EVERY esgc_free (x :: dflt :: MAP SND xs) ==>
  esgc_free (naive_pattern_matches t x xs dflt)
Proof
  ho_match_mp_tac naive_pattern_matches_ind
  \\ simp [naive_pattern_matches_def, esgc_free_naive_pattern_match]
QED

Theorem esgc_free_compile_pats:
  esgc_free dflt /\ EVERY esgc_free (MAP SND ps) ==>
  esgc_free (compile_pats cfg naive t N (Var_local t' nm) dflt ps)
Proof
  rw [compile_pats_def]
  \\ DEP_REWRITE_TAC [esgc_free_decode_dtree, esgc_free_naive_pattern_matches]
  \\ simp [MAP_ZIP]
  \\ fs [EVERY_MEM, set_toList_fromList, MEM_MAP, PULL_EXISTS, FORALL_PROD]
  \\ rw [compile_pat_rhs_def]
  \\ irule esgc_free_compile_pat_bindings
  \\ simp []
  \\ metis_tac []
QED

Theorem compile_exp_esgc_free:
  (!cfg exp N sg exp'. compile_exp cfg exp = (N, sg, exp') /\
  esgc_free exp
  ==>
  esgc_free exp')
  /\
  (!cfg exps N sg exps'. compile_exps cfg exps = (N, sg, exps') /\
  EVERY esgc_free exps
  ==>
  EVERY esgc_free exps')
  /\
  (!cfg m N sg m'. compile_match cfg m = (N, sg, m') /\
  EVERY (esgc_free o SND) m
  ==>
  EVERY (esgc_free o SND) m')
Proof
  ho_match_mp_tac compile_exp_ind
  \\ fs [compile_exp_def]
  \\ fs [miscTheory.UNCURRY_eq_pair, PULL_EXISTS]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ imp_res_tac LENGTH_compile_exps_IMP
  \\ fs [quantHeuristicsTheory.LIST_LENGTH_2, EVERY_REVERSE]
  \\ rveq \\ fs []
  \\ TRY (irule esgc_free_compile_pats \\ fs [EVERY_MAP, o_DEF])
  \\ imp_res_tac compile_exp_set_globals
  \\ fs [elist_globals_eq_empty, MEM_MAP, FORALL_PROD, PULL_EXISTS]
  \\ rw []
  \\ res_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ imp_res_tac compile_exp_set_globals
  \\ imp_res_tac LENGTH_compile_exps_IMP
  \\ fs [quantHeuristicsTheory.LIST_LENGTH_2, EVERY_REVERSE]
QED

Theorem compile_decs_esgc_free:
  !decs cfg decs' cfg'. compile_decs cfg decs = (cfg', decs') /\
  EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet decs))
  ==>
  EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet decs'))
Proof
  Induct
  \\ rw [compile_decs_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ Cases_on `h` \\ fs [compile_dec_def]
  \\ last_x_assum drule \\ rw []
  \\ rveq \\ fs []
  \\ qmatch_goalsub_abbrev_tac `compile_exp cfg exp`
  \\ `?N sg e'. compile_exp cfg exp = (N, sg, e')` by metis_tac [pair_CASES]
  \\ imp_res_tac LENGTH_compile_exps_IMP
  \\ drule (CONJUNCT1 compile_exp_esgc_free)
  \\ fs [quantHeuristicsTheory.LIST_LENGTH_2]
QED

Theorem naive_pattern_match_no_Mat:
  !t xs. EVERY (no_Mat o SND) xs ==>
  no_Mat (naive_pattern_match t xs)
Proof
  ho_match_mp_tac naive_pattern_match_ind
  \\ simp [naive_pattern_match_def, Bool_def]
  \\ rw []
  \\ fs []
  \\ fs [EVERY_EL]
QED

Theorem naive_pattern_matches_no_Mat:
  !t x xs dflt. EVERY no_Mat (x :: dflt :: MAP SND xs) ==>
  no_Mat (naive_pattern_matches t x xs dflt)
Proof
  ho_match_mp_tac naive_pattern_matches_ind
  \\ simp [naive_pattern_matches_def, naive_pattern_match_no_Mat]
QED

Theorem compile_pat_bindings_no_Mat:
  !t i n_bindings exp.
  no_Mat exp /\
  EVERY (\(_, _, v_exp). no_Mat v_exp) n_bindings ==>
  no_Mat (SND (compile_pat_bindings t i n_bindings exp))
Proof
  ho_match_mp_tac compile_pat_bindings_ind
  \\ rw [compile_pat_bindings_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ simp []
  \\ DEP_REWRITE_TAC [Q.ISPEC `no_Mat` inv_on_FOLDR]
  \\ simp [FORALL_PROD]
  \\ fs [EVERY_MAP, ELIM_UNCURRY]
QED

Theorem decode_pos_no_Mat:
  !p exp. no_Mat exp ==>
  no_Mat (decode_pos t exp p)
Proof
  Induct \\ simp [decode_pos_def]
QED

Theorem decode_test_no_Mat:
  no_Mat exp ==> no_Mat (decode_test t d exp)
Proof
  Cases_on `d`
  \\ simp [decode_test_def]
QED

Theorem decode_guard_no_Mat:
  no_Mat exp ==> no_Mat (decode_guard t exp gd)
Proof
  Induct_on `gd` \\ simp [decode_guard_def, Bool_def]
  \\ simp [decode_test_no_Mat, decode_pos_no_Mat]
QED

Theorem decode_dtree_no_Mat:
  no_Mat v_exp /\ no_Mat dflt /\
  EVERY no_Mat (toList br_spt) ==>
  no_Mat (decode_dtree t br_spt v_exp dflt dtree)
Proof
  Induct_on `dtree`
  \\ simp [decode_dtree_def]
  \\ rw []
  \\ simp [decode_guard_no_Mat]
  \\ CASE_TAC
  \\ fs [MEM_toList, EVERY_MEM, FORALL_PROD]
  \\ metis_tac []
QED

Theorem compile_pats_no_Mat:
  no_Mat dflt /\ no_Mat x /\ EVERY no_Mat (MAP SND ps) ==>
  no_Mat (compile_pats cfg naive t N x dflt ps)
Proof
  simp [compile_pats_def]
  \\ rw []
  \\ DEP_REWRITE_TAC [naive_pattern_matches_no_Mat, decode_dtree_no_Mat]
  \\ simp [MAP_ZIP]
  \\ fs [EVERY_MEM, set_toList_fromList, MEM_MAP, PULL_EXISTS, FORALL_PROD]
  \\ rw [compile_pat_rhs_def]
  \\ res_tac
  \\ simp [compile_pat_bindings_no_Mat]
QED

Theorem compile_exp_no_Mat:
  (!cfg exp N sg exp'.
  compile_exp cfg exp = (N, sg, exp') ==>
  no_Mat exp') /\
  (!cfg exps N sg exps'.
  compile_exps cfg exps = (N, sg, exps') ==>
  EVERY no_Mat exps') /\
  (!cfg pats N sg pats'.
  compile_match cfg pats = (N, sg, pats') ==>
  EVERY no_Mat (MAP SND pats'))
Proof
  ho_match_mp_tac compile_exp_ind
  \\ simp [compile_exp_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ imp_res_tac LENGTH_compile_exps_IMP
  \\ fs [quantHeuristicsTheory.LIST_LENGTH_2, listTheory.LENGTH_CONS]
  \\ rveq \\ fs []
  \\ fs [EVERY_REVERSE, Q.ISPEC `no_Mat` ETA_THM, compile_pats_no_Mat]
  \\ simp [EVERY_MEM, MEM_MAP, FORALL_PROD, PULL_EXISTS]
  \\ rw []
  \\ res_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ imp_res_tac LENGTH_compile_exps_IMP
  \\ fs [quantHeuristicsTheory.LIST_LENGTH_2, listTheory.LENGTH_CONS]
  \\ rveq \\ fs []
QED

Theorem compile_decs_no_Mat:
  !decs cfg decs' cfg'. compile_decs cfg decs = (cfg', decs')
  ==>
  no_Mat_decs decs'
Proof
  Induct
  \\ simp [compile_decs_def]
  \\ Cases
  \\ simp [compile_decs_def, compile_dec_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ res_tac
  \\ fs []
  \\ qmatch_goalsub_abbrev_tac `compile_exp cfg exp`
  \\ `?N sg e'. compile_exp cfg exp = (N, sg, e')` by metis_tac [pair_CASES]
  \\ imp_res_tac LENGTH_compile_exps_IMP
  \\ drule (CONJUNCT1 compile_exp_no_Mat)
  \\ fs [quantHeuristicsTheory.LIST_LENGTH_2, listTheory.LENGTH_CONS]
QED

val _ = export_theory()
