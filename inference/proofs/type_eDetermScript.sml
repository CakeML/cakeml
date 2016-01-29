open preamble;
open rich_listTheory alistTheory;
open miscTheory;
open libTheory typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory;
open astPropsTheory;
open typeSysPropsTheory;
open inferPropsTheory;
open miscLib;
open infer_eSoundTheory;
open infer_eCompleteTheory;

val _ = new_theory "type_eDeterm";

val _ = temp_tight_equality ();

val sub_completion_empty = Q.prove (
`!m n s s'. sub_completion m n s [] s' ⇔ count n ⊆ FDOM s' ∧ (∀uv. uv ∈ FDOM s' ⇒ check_t m ∅ (t_walkstar s' (Infer_Tuvar uv))) ∧ s = s'`,
 srw_tac[] [sub_completion_def, pure_add_constraints_def] >>
 metis_tac []);

val infer_pe_complete = Q.store_thm ("infer_pe_complete",
  `check_menv menv ∧
    menv_alpha menv tenvM ∧ 
    tenvC_ok cenv ∧
    num_tvs tenv = tvs ∧
    check_env {} env ∧
    tenv_invC FEMPTY env tenv ∧
    type_p tvs cenv p t1 tenv1 ∧
    type_e tenvM cenv tenv e t1
    ⇒
    ?t t' tenv' st st' s constrs s'.
      infer_e menv cenv env e init_infer_state = (Success t, st) ∧
      infer_p cenv p st = (Success (t', tenv'), st') ∧
      t_unify st'.subst t t' = SOME s ∧
      sub_completion (num_tvs tenv) st'.next_uvar s constrs s' ∧
      FDOM s' = count st'.next_uvar ∧  
      t1 = convert_t (t_walkstar s' t') ∧
      t1 = convert_t (t_walkstar s' t) ∧
      t_wfs s ∧
      simp_tenv_invC s' (num_tvs tenv) tenv' tenv1`,
  srw_tac[] [] >>
  (infer_e_complete |> CONJUNCT1 |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
  (infer_p_complete |> CONJUNCT1 |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
  srw_tac[] [] >>
  `t_wfs init_infer_state.subst` by srw_tac[] [t_wfs_def, init_infer_state_def] >>
  first_x_assum (qspecl_then [`FEMPTY`, `menv`, `env`, `init_infer_state`, `[]`] mp_tac) >>
  srw_tac[] [sub_completion_empty, init_infer_state_def] >>
  `t_wfs st'.subst`
          by (imp_res_tac (CONJUNCT1 infer_e_wfs) >>
              full_simp_tac(srw_ss()) [init_infer_state_def]) >>
  first_x_assum (qspecl_then [`s'`, `st'`, `constraints'`] mp_tac) >>
  srw_tac[] [] >>
  MAP_EVERY qexists_tac [`t''`, `tenv'`, `st''`] >>
  srw_tac[] [] >>
  `t_wfs st''.subst` by metis_tac [infer_p_wfs] >>
  `check_t (num_tvs tenv) {} (t_walkstar s' t') ∧ check_t (num_tvs tenv) {} (t_walkstar s'' t'')`
              by (conj_tac >>
                  match_mp_tac (GEN_ALL sub_completion_completes) >>
                  srw_tac[] []
                  >- metis_tac [sub_completion_wfs]
                  >- (imp_res_tac (CONJUNCT1 infer_e_check_t) >>
                      full_simp_tac(srw_ss()) [])
                  >- full_simp_tac(srw_ss()) [sub_completion_def]
                  >- metis_tac [sub_completion_wfs]
                  >- (imp_res_tac (CONJUNCT1 infer_p_check_t) >>
                      full_simp_tac(srw_ss()) [])
                  >- full_simp_tac(srw_ss()) [sub_completion_def]) >>
  `t_walkstar s'' (t_walkstar s' t') = t_walkstar s'' (t_walkstar s'' t'')` by metis_tac [convert_bi_remove] >>
  `t_walkstar s'' t' = t_walkstar s'' t''`
            by metis_tac [t_walkstar_SUBMAP, SUBMAP_REFL, t_compat_def] >>
  `t_compat st''.subst s''`
               by metis_tac [pure_add_constraints_success, sub_completion_def, t_compat_def] >>
  `?si. t_unify st''.subst t' t'' = SOME si ∧ t_compat si s''` by metis_tac [t_compat_eqs_t_unify] >>
  qexists_tac `si` >>
  `t_wfs si` by metis_tac [t_unify_wfs] >>
  srw_tac[] [] >>
  full_simp_tac(srw_ss())[sub_completion_def] >>
  `pure_add_constraints st''.subst [t',t''] si` by (
    simp[pure_add_constraints_def] ) >>
  `t_wfs s''` by metis_tac[pure_add_constraints_wfs] >>
  `pure_add_constraints s'' [t',t''] s''` by
    (match_mp_tac pure_add_constraints_ignore >>
     full_simp_tac(srw_ss())[t_walkstar_eqn,t_walk_eqn]) >>
  `pure_add_constraints st''.subst (constraints''++[(t',t'')]) s''` by (
    metis_tac[pure_add_constraints_append]) >>
  pop_assum(fn th =>
    mp_tac (MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]
                       (ONCE_REWRITE_RULE[CONJ_COMM]
                         (GEN_ALL pure_add_constraints_swap))) th)) >>
  simp[] >> disch_then(qx_choose_then`si2`strip_assume_tac) >>
  `pure_add_constraints si constraints'' si2` by (
    metis_tac[pure_add_constraints_append,
              pure_add_constraints_functional,
              CONS_APPEND]) >>
  imp_res_tac infer_p_next_uvar_mono >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  qspecl_then[`num_tvs tenv`,`si2`,`s''`]mp_tac(GEN_ALL t_compat_bi_ground) >>
  discharge_hyps >- simp[] >> strip_tac >> simp[] >>
  conj_tac >- (
    full_simp_tac(srw_ss())[SUBSET_DEF,EXTENSION] >> srw_tac[][] >> res_tac >> DECIDE_TAC ) >>
  full_simp_tac(srw_ss())[simp_tenv_invC_def] >>
  metis_tac[]);

val unconvert_11 = Q.prove (
`!t1 t2. check_freevars 0 [] t1 ∧ check_freevars 0 [] t2 ⇒ 
  (unconvert_t t1 = unconvert_t t2 ⇔ t1 = t2)`,
 ho_match_mp_tac unconvert_t_ind >>
 srw_tac[] [unconvert_t_def] >>
 Cases_on `t2` >>
 full_simp_tac(srw_ss()) [unconvert_t_def, check_freevars_def] >>
 full_simp_tac(srw_ss()) [EVERY_MEM] >>
 eq_tac >>
 srw_tac[] [] >>
 match_mp_tac LIST_EQ >>
 srw_tac[] []
 >- metis_tac [LENGTH_MAP] >>
 `x < LENGTH l` by metis_tac [LENGTH_MAP] >>
 `EL x (MAP (λa. unconvert_t a) ts) = EL x (MAP (λa. unconvert_t a) l)` by metis_tac [] >>
 rev_full_simp_tac(srw_ss()) [EL_MAP] >>
 metis_tac [EL_MEM]);

val type_p_pat_bindings = Q.store_thm ("type_p_pat_bindings",
`(∀tvs cenv p t tenv.
  type_p tvs cenv p t tenv ⇒ MAP FST tenv = pat_bindings p []) ∧
 (∀tvs cenv ps ts tenv.
  type_ps tvs cenv ps ts tenv ⇒ MAP FST tenv = pats_bindings ps [])`,
 ho_match_mp_tac type_p_ind >>
 srw_tac[] [pat_bindings_def] >>
 metis_tac [evalPropsTheory.pat_bindings_accum]);

val infer_e_type_pe_determ = Q.store_thm ("infer_e_type_pe_determ",
`!tenvM menv cenv env tenv p e st st' t t' tenv' s.
  ALL_DISTINCT (MAP FST tenv') ∧
  check_menv menv ∧
  menv_alpha menv tenvM ∧
  tenvC_ok cenv ∧
  check_env {} env ∧
  num_tvs tenv = 0 ∧
  tenv_invC FEMPTY env tenv ∧
  infer_e menv cenv env e init_infer_state = (Success t, st) ∧
  infer_p cenv p st = (Success (t', tenv'), st') ∧
  t_unify st'.subst t t' = SOME s ∧
  EVERY (\(n, t). check_t 0 {} (t_walkstar s t)) tenv'
  ⇒
  type_pe_determ tenvM cenv tenv p e`,
 srw_tac[] [type_pe_determ_def] >>
 mp_tac (Q.INST [`tvs`|->`0`] infer_pe_complete) >>
 srw_tac[] [] >>
 mp_tac (Q.INST [`t1`|->`t2`, `tenv1` |-> `tenv2`,`tvs`|->`0`] infer_pe_complete) >>
 srw_tac[] [] >>
 match_mp_tac LIST_EQ >>
 imp_res_tac type_p_pat_bindings >>
 imp_res_tac infer_p_bindings >>
 pop_assum (qspecl_then [`[]`] mp_tac) >>
 srw_tac[] []
 >- metis_tac [LENGTH_MAP] >>
 full_simp_tac(srw_ss()) [simp_tenv_invC_def] >>
 first_x_assum (qspecl_then [`FST (EL x tenv2)`, `SND (EL x tenv2)`] mp_tac) >>
 first_x_assum (qspecl_then [`FST (EL x tenv1)`, `SND (EL x tenv1)`] mp_tac) >>
 `ALL_DISTINCT (MAP FST tenv2) ∧ x < LENGTH tenv2` by metis_tac [LENGTH_MAP] >>
 srw_tac[] [ALOOKUP_ALL_DISTINCT_EL, LENGTH_MAP] >>
 `?k1 t1 k2 t2. EL x tenv1 = (k1,t1) ∧ EL x tenv2 = (k2, t2)` by metis_tac [pair_CASES] >> 
 full_simp_tac(srw_ss()) [] >>
 conj_asm1_tac
 >- (`EL x (MAP FST tenv1) = EL x (MAP FST tenv2)` by metis_tac [] >>
     rev_full_simp_tac(srw_ss()) [EL_MAP]) >>
 srw_tac[] [GSYM unconvert_11] >>
 full_simp_tac(srw_ss()) [EVERY_MEM] >>
 imp_res_tac ALOOKUP_MEM >>
 res_tac >>
 full_simp_tac(srw_ss()) [sub_completion_def] >>
 imp_res_tac pure_add_constraints_success >>
 full_simp_tac(srw_ss()) [t_compat_def] >>
 metis_tac [t_walkstar_no_vars]);

val generalise_complete_lem = Q.prove (
`∀n s t tvs s' t' tvs next_uvar.
  t_wfs s ∧ check_s 0 (count next_uvar) s ∧
  check_t 0 (count next_uvar) t ∧
  generalise 0 n FEMPTY (t_walkstar s t) = (tvs,s',t') ⇒
  ∃ec1 last_sub.
    t' = t_walkstar last_sub t ∧ t_wfs last_sub ∧
    sub_completion (tvs + n) next_uvar s ec1 last_sub`,
 srw_tac[] [] >>
 mp_tac (Q.SPECL [`n`, `s`, `[t]`] generalise_complete) >>
 srw_tac[] [generalise_def, LET_THM]);

val t_vars_check_t = prove(``
  (∀t.
  ¬check_t 0 {} t ∧ 
  check_t 0 s t ⇒
  ∃n'. n' ∈ s ∧ n' ∈ t_vars t) ∧ 
  (∀ts.
  ∀x.MEM x ts ⇒ 
    ¬check_t 0 {} x ∧ 
    check_t 0 s x ⇒ 
    ∃n'. n' ∈ s ∧ n' ∈ t_vars x)``,
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  srw_tac[][check_t_def,t_vars_eqn]>>
  full_simp_tac(srw_ss())[EXISTS_MEM,EVERY_MEM]>>res_tac>>
  qexists_tac `n'`>>
  full_simp_tac(srw_ss())[MEM_MAP]>>
  metis_tac[])

val t_walkstar_diff = prove(``
  t_wfs s1 ∧ t_wfs s2 ∧ 
  (t_walkstar s1 (Infer_Tuvar n) ≠ t_walkstar s2 (Infer_Tuvar n))
  ⇒ 
  (∀t.(n ∈ t_vars t) ⇒ t_walkstar s1 t ≠ t_walkstar s2 t) ∧
  (∀ts. 
  ∀x. MEM x ts ⇒ 
    n ∈ t_vars x ⇒ t_walkstar s1 x ≠ t_walkstar s2 x)``,
  strip_tac>>
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  srw_tac[][t_vars_eqn]>>full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[t_walkstar_eqn,t_walk_eqn,MEM_MAP]>>
  res_tac>>rev_full_simp_tac(srw_ss())[]>>
  SPOSE_NOT_THEN assume_tac>>
  imp_res_tac MAP_EQ_f>>
  metis_tac[])

val type_pe_determ_infer_e = Q.store_thm ("type_pe_determ_infer_e",
`!tenvM menv cenv env tenv p e st st' t t' tenv' s.
  ALL_DISTINCT (MAP FST tenv') ∧
  check_menv menv ∧
  menv_alpha menv tenvM ∧ 
  tenvC_ok cenv ∧
  check_env {} env ∧
  num_tvs tenv = 0 ∧
  tenv_inv FEMPTY env tenv ∧
  infer_e menv cenv env e init_infer_state = (Success t, st) ∧
  infer_p cenv p st = (Success (t', tenv'), st') ∧
  t_unify st'.subst t t' = SOME s ∧
  type_pe_determ tenvM cenv tenv p e
  ⇒
  EVERY (\(n, t). check_t 0 {} (t_walkstar s t)) tenv'`,
 srw_tac[] [type_pe_determ_def, check_cenv_tenvC_ok] >>
 `t_wfs init_infer_state.subst` by srw_tac[] [t_wfs_def, init_infer_state_def] >>
 `t_wfs st.subst` by metis_tac [infer_e_wfs] >>
 `t_wfs st'.subst` by metis_tac [infer_p_wfs] >>
 `t_wfs s` by metis_tac [t_unify_wfs] >>
 `check_t 0 (count st.next_uvar) t`
          by (imp_res_tac infer_e_check_t >>
              full_simp_tac(srw_ss()) [init_infer_state_def]) >>
 `check_s 0 (count st.next_uvar) st.subst`
           by (match_mp_tac (CONJUNCT1 infer_e_check_s) >>
               MAP_EVERY qexists_tac [`menv`, `cenv`, `env`, `e`, `init_infer_state`] >>
               srw_tac[] [init_infer_state_def, check_s_def]) >>
 `?l. set l = count st'.next_uvar DIFF FDOM s ∧ ALL_DISTINCT l`
          by metis_tac [FINITE_COUNT, FINITE_DIFF, SET_TO_LIST_INV, ALL_DISTINCT_SET_TO_LIST] >>
 qabbrev_tac `inst1 = MAP (\n. (Infer_Tuvar n, Infer_Tbool)) l` >>
 qabbrev_tac `inst2 = MAP (\n. (Infer_Tuvar n, Infer_Tint)) l` >>
(* Because we're instantiating exactly the unconstrained variables *)
 let
   fun tac q q1 =
     simp[sub_completion_def] >>
     qexists_tac`s |++ (MAP (λn. (n, ^q)) l)` >>
     conj_asm1_tac >- (
       qunabbrev_tac q1 >>
       qpat_assum`t_wfs s`mp_tac >>
       qpat_assum`set l = X`mp_tac >>
       qpat_assum`ALL_DISTINCT l`mp_tac >>
       qspec_tac(`st'.next_uvar`,`n`) >>
       map_every qid_spec_tac[`s`,`l`] >>
       Induct >>
       simp[pure_add_constraints_def,FUPDATE_LIST_THM] >> srw_tac[][] >>
       qho_match_abbrev_tac`∃s2. P s2 ∧ Q s2` >>
       qsuff_tac`∃s2. P s2 ∧ (t_wfs s2 ⇒ Q s2)`>-metis_tac[t_unify_wfs] >>
       simp[Abbr`P`,t_unify_eqn,t_walk_eqn,Infer_Tbool_def,Infer_Tint_def,Once t_vwalk_eqn] >>
       simp[FLOOKUP_DEF] >> srw_tac[][] >- (
         full_simp_tac(srw_ss())[EXTENSION] >> metis_tac[] ) >>
       simp[t_ext_s_check_eqn,Once t_oc_eqn,t_walk_eqn] >>
       simp[GSYM Infer_Tbool_def,GSYM Infer_Tint_def,Abbr`Q`] >> strip_tac >>
       first_x_assum (match_mp_tac o MP_CANON) >>
       simp[FDOM_FUPDATE] >> full_simp_tac(srw_ss())[EXTENSION] >> metis_tac[] ) >>
     conj_tac >- (
       full_simp_tac(srw_ss())[EXTENSION,SUBSET_DEF,FDOM_FUPDATE_LIST,MEM_MAP,EXISTS_PROD] ) >>
     simp[FDOM_FUPDATE_LIST,MEM_MAP,EXISTS_PROD] >>
     imp_res_tac pure_add_constraints_wfs >>
     ntac 3 (pop_assum kall_tac) >>
     reverse(srw_tac[][]) >- (
       srw_tac[][t_walkstar_eqn,t_walk_eqn,Once t_vwalk_eqn,flookup_fupdate_list] >>
       BasicProvers.CASE_TAC >- (
         imp_res_tac ALOOKUP_FAILS >>
         full_simp_tac(srw_ss())[MEM_MAP,EXTENSION] >> metis_tac[] ) >>
       imp_res_tac ALOOKUP_MEM >> full_simp_tac(srw_ss())[MEM_MAP] >>
       srw_tac[][Infer_Tbool_def,Infer_Tint_def] >> srw_tac[][check_t_def] ) >>
     first_assum(fn th=> mp_tac (MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] (CONJUNCT1 infer_p_check_s)) th)) >>
     simp[] >> disch_then(qspec_then`0`mp_tac) >> simp[] >> strip_tac >>
     match_mp_tac t_walkstar_check >>
     simp[check_t_def,FDOM_FUPDATE_LIST] >>
     (t_unify_check_s
      |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(same_const``t_unify`` o fst o strip_comb o lhs))))
      |> REWRITE_RULE[GSYM AND_IMP_INTRO]
      |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
     imp_res_tac infer_p_next_uvar_mono >>
     first_assum(fn th => mp_tac (MATCH_MP (CONJUNCT1 check_t_more5) th)) >>
     disch_then(qspec_then`count st'.next_uvar`mp_tac) >>
     simp[SUBSET_DEF] >> strip_tac >>
     imp_res_tac (CONJUNCT1 infer_p_check_t) >>
     disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> simp[] >>
     strip_tac >>
     (pure_add_constraints_check_s
      |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(same_const``pure_add_constraints`` o fst o strip_comb))))
      |> REWRITE_RULE[GSYM AND_IMP_INTRO]
      |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
     disch_then(qspecl_then[`0`,`st'.next_uvar`]mp_tac) >> simp[] >>
     discharge_hyps >- (
       simp[Abbr q1,EVERY_MEM,MEM_MAP,PULL_EXISTS,check_t_def,Infer_Tbool_def,Infer_Tint_def] ) >>
     strip_tac >>
     match_mp_tac (MP_CANON check_s_more3) >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     simp[SUBSET_DEF,MEM_MAP,PULL_EXISTS]
 in
   `?s1. sub_completion 0 st'.next_uvar s inst1 s1` by (tac ``Infer_Tbool`` `inst1`) >>
   `?s2. sub_completion 0 st'.next_uvar s inst2 s2` by (tac ``Infer_Tint`` `inst2`)
 end >>
  `t_wfs s1 ∧ t_wfs s2` by metis_tac[sub_completion_wfs] >>
 imp_res_tac sub_completion_unify2 >>
 imp_res_tac infer_p_constraints >>
 (sub_completion_add_constraints |> REWRITE_RULE[GSYM AND_IMP_INTRO] |>
  (fn th => first_assum(mp_tac o MATCH_MP th))) >> simp[] >>
 disch_then imp_res_tac >>
 (infer_e_sound |> CONJUNCT1 |> REWRITE_RULE[GSYM AND_IMP_INTRO] |>
  (fn th => first_assum(mp_tac o MATCH_MP th))) >> simp[] >>
 simp[init_infer_state_def] >>
 disch_then(qspec_then`tenv`mp_tac) >> simp[] >>
 disch_then(qspec_then`tenvM`mp_tac o (CONV_RULE (RESORT_FORALL_CONV List.rev))) >> simp[] >>
 full_simp_tac(srw_ss())[sub_completion_def,GSYM AND_IMP_INTRO] >>
 disch_then(fn th =>
   first_x_assum(mp_tac o MATCH_MP th) >>
   first_x_assum(mp_tac o MATCH_MP th)) >>
 imp_res_tac infer_p_next_uvar_mono >>
 `count st.next_uvar ⊆ count st'.next_uvar` by simp[SUBSET_DEF] >>
 discharge_hyps >- metis_tac[SUBSET_TRANS] >> simp[] >>
 discharge_hyps >- metis_tac[tenv_inv_empty_to] >> strip_tac >>
 discharge_hyps >- metis_tac[SUBSET_TRANS] >> simp[] >>
 discharge_hyps >- metis_tac[tenv_inv_empty_to] >> strip_tac >>
 imp_res_tac infer_p_check_t>>
 assume_tac (infer_p_sound |> CONJUNCT1)>>
 first_assum (qspecl_then
   [`cenv`,`p`,`st`,`t'`,`tenv'`,`st'`,`0`,`(t,t')::inst1`,`s1`]assume_tac)>>
 first_x_assum (qspecl_then
   [`cenv`,`p`,`st`,`t'`,`tenv'`,`st'`,`0`,`(t,t')::inst2`,`s2`]assume_tac)>>
 rev_full_simp_tac(srw_ss())[sub_completion_def]>>
 res_tac>>pop_assum kall_tac>>
 (*Because t,t' is part of the unifications that yielded s1 and s2*)
 `t_compat s s1 ∧ t_compat s s2` by (
   imp_res_tac pure_add_constraints_success >> srw_tac[][] ) >>
 `t_walkstar s t = t_walkstar s t'` by (
   imp_res_tac t_unify_unifier ) >>
 `convert_t (t_walkstar s2 t') = convert_t (t_walkstar s2 t)` by (
   full_simp_tac(srw_ss())[t_compat_def] >> metis_tac[] ) >>
 pop_assum SUBST_ALL_TAC>>rev_full_simp_tac(srw_ss())[]>>
 res_tac>>pop_assum kall_tac>>
 `convert_t (t_walkstar s1 t') = convert_t (t_walkstar s1 t)` by (
   full_simp_tac(srw_ss())[t_compat_def] >> metis_tac[] ) >>
 pop_assum SUBST_ALL_TAC>>rev_full_simp_tac(srw_ss())[]>>
 full_simp_tac(srw_ss())[convert_env_def]>>
 spose_not_then strip_assume_tac >>
 full_simp_tac(srw_ss())[EXISTS_MEM,EXISTS_PROD] >>
 qpat_assum`MAP X Y = Z`mp_tac >> simp[] >>
 simp[LIST_EQ_REWRITE,EL_MAP,UNCURRY] >>
 qpat_assum`MEM X Y`mp_tac >> simp[MEM_EL] >> strip_tac >>
 qexists_tac`n` >>
 pop_assum(assume_tac o SYM) >> simp[] >>
 full_simp_tac(srw_ss())[EVERY_MEM] >>
 first_x_assum(qspec_then`EL n tenv'`mp_tac) >>
 discharge_hyps >- metis_tac[MEM_EL] >> simp[] >> strip_tac >>
 qmatch_assum_rename_tac`check_t 0 (count st'.next_uvar) tt` >>
 `t_vars tt ⊆ count (st'.next_uvar)` by imp_res_tac check_t_t_vars >>
 imp_res_tac infer_p_check_s>> ntac 7 (pop_assum kall_tac)>>
 `check_s 0 (count st'.next_uvar) s` by 
   (match_mp_tac t_unify_check_s>>
   Q.LIST_EXISTS_TAC [`st'.subst`,`t`,`t'`]>>full_simp_tac(srw_ss())[]>>
   `count st.next_uvar ⊆ count st'.next_uvar` by
     (imp_res_tac infer_p_next_uvar_mono>>
     srw_tac[][count_def,SUBSET_DEF]>>DECIDE_TAC)>>
   metis_tac[check_t_more5,infer_p_check_t])>>
 `check_t 0 (count st'.next_uvar) (t_walkstar s tt)` by
   (match_mp_tac t_walkstar_check>>full_simp_tac(srw_ss())[]>>
   `count st'.next_uvar ⊆ count st'.next_uvar ∪ FDOM s` by full_simp_tac(srw_ss())[]>>
   metis_tac[check_t_more5,check_s_more3])>>
  imp_res_tac t_vars_check_t>>
  ntac 5 (pop_assum kall_tac)>>
  imp_res_tac t_walkstar_vars_notin>>
  `t_walkstar s1 tt ≠ t_walkstar s2 tt` by
    (Q.ISPECL_THEN [`s2`,`s1`,`n'`]mp_tac (GEN_ALL t_walkstar_diff)>>
    discharge_hyps>-
      (rev_full_simp_tac(srw_ss())[]>>
      `MEM n' l` by full_simp_tac(srw_ss())[]>>
      `t_walkstar s1 (Infer_Tuvar n') = Infer_Tbool ∧
       t_walkstar s2 (Infer_Tuvar n') = Infer_Tint ` by
        (imp_res_tac pure_add_constraints_apply>>
        unabbrev_all_tac>>
        full_simp_tac(srw_ss())[MAP_EQ_f,FORALL_PROD,MEM_MAP]>>
        ntac 2 (pop_assum kall_tac)>>
        pop_assum (qspecl_then [`Infer_Tuvar n'`,`Infer_Tint`] mp_tac)>>
        pop_assum (qspecl_then [`Infer_Tuvar n'`,`Infer_Tbool`] mp_tac)>>
        ntac 4 (pop_assum kall_tac)>>
        full_simp_tac(srw_ss())[t_walkstar_eqn,t_walk_eqn,Infer_Tint_def,Infer_Tbool_def])>>
      full_simp_tac(srw_ss())[Infer_Tint_def,Infer_Tbool_def])>>
    srw_tac[][]>>pop_assum kall_tac>>
    pop_assum (qspec_then `t_walkstar s tt` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    metis_tac[t_compat_def])>>
  assume_tac (GEN_ALL (CONJUNCT1 check_t_less))>>
  first_assum(qspecl_then [`count st'.next_uvar`,`s1`,`0`,`tt`] assume_tac)>>
  first_x_assum(qspecl_then [`count st'.next_uvar`,`s2`,`0`,`tt`]assume_tac)>>
  `count st'.next_uvar ∩ COMPL (FDOM s1) = {} ∧
   count st'.next_uvar ∩ COMPL (FDOM s2) = {}` by
    (full_simp_tac(srw_ss())[EXTENSION,SUBSET_DEF]>>metis_tac[])>>
  full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
  metis_tac[check_t_empty_unconvert_convert_id]);

 
 (*From ¬check_t 0 {} (t_walkstar s tt) it should follow that
   t_walkstar s tt must contain some unification variables.
   (*
   first_assum(
     mp_tac o (MATCH_MP (GEN_ALL(CONTRAPOS(SPEC_ALL(CONJUNCT1 check_t_walkstar)))))) >>
   *)
   But we know that s is completed by s1 and s2 therefore those
   unification variables are exactly bound in s1 and s2 to 
   Infer_Tbool and Infer_Tint, hence the walkstars must differ *)

val infer_funs_complete = store_thm("infer_funs_complete",``
  tenv_ok (bind_var_list2 tenv Empty) ∧ 
  check_menv menv ∧ 
  menv_alpha menv tenvM ∧ 
  tenvC_ok cenv ∧
  tenv_invC FEMPTY itenv (bind_var_list2 tenv Empty) ∧
  check_env {} itenv ∧ 
  type_funs tenvM cenv (bind_var_list 0 tenv'' (bind_tvar tvs (bind_var_list2 tenv Empty))) funs tenv'' 
  ⇒ 
  ∃funs_ts st st' constr s.
  infer_funs menv cenv 
    (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) funs (MAP (λn. Infer_Tuvar (init_infer_state.next_uvar+n)) (COUNT_LIST (LENGTH funs)))++itenv) funs (init_infer_state with next_uvar:= init_infer_state.next_uvar + LENGTH funs) =
    (Success funs_ts,st) ∧
  st.next_uvar = st'.next_uvar ∧
  pure_add_constraints st.subst
    (ZIP (MAP (λn. Infer_Tuvar (init_infer_state.next_uvar + n))
              (COUNT_LIST (LENGTH funs)),funs_ts)) st'.subst ∧
  (*I think this should be 0*)
  check_s 0 (count st'.next_uvar) st'.subst ∧ 
  sub_completion tvs st'.next_uvar st'.subst constr s ∧ 
  FDOM s = count st'.next_uvar ∧ 
  MAP SND tenv'' = MAP (convert_t o t_walkstar s) funs_ts``,
  srw_tac[][]>>
  full_simp_tac(srw_ss())[check_env_def]>>
  imp_res_tac type_funs_distinct >> full_simp_tac(srw_ss())[FST_triple] >>
  imp_res_tac type_funs_MAP_FST >>
  imp_res_tac type_funs_Tfn>>
  simp[init_infer_state_def,ETA_AX] >>
  qpat_abbrev_tac`itenv2 = x ++ itenv` >>
  qpat_abbrev_tac`st:(num|->infer_t)infer_st = X Y` >>
  `st.subst = FEMPTY` by simp[Abbr`st`] >>
  `t_wfs st.subst` by simp[t_wfs_def] >>
  `st.next_uvar = LENGTH funs` by ( simp[Abbr`st`] ) >>
  simp[LENGTH_COUNT_LIST] >>
  `EVERY (check_freevars tvs []) (MAP SND tenv'')` by
     (full_simp_tac(srw_ss())[EVERY_MEM,MEM_MAP,PULL_EXISTS,EXISTS_PROD]>>
     srw_tac[][]>>
     `ALOOKUP tenv'' p_1 = SOME e` by 
       metis_tac[ALOOKUP_ALL_DISTINCT_MEM]>>
     res_tac>>
     full_simp_tac(srw_ss())[num_tvs_bind_var_list,bind_tvar_def]>>
     Cases_on`tvs=0`>>full_simp_tac(srw_ss())[num_tvs_bvl2,num_tvs_def]>>
     rev_full_simp_tac(srw_ss())[])>>
   Q.ISPECL_THEN [`init_infer_state`,`[]:(infer_t,infer_t) alist`,`FEMPTY:num|->infer_t`,`MAP SND tenv''`,`tvs`] mp_tac extend_multi_props>>
   discharge_hyps>-
       full_simp_tac(srw_ss())[init_infer_state_def,t_wfs_def,pure_add_constraints_def,count_def]
   >>
   BasicProvers.LET_ELIM_TAC>>
   first_assum(mp_tac o MATCH_MP(last(CONJUNCTS infer_e_complete))) >>
   disch_then(qspecl_then[`s'`,`menv`,`itenv2`,`st`,`new_constraints`]mp_tac) >>
   discharge_hyps>-
      (full_simp_tac(srw_ss())[]>>
      conj_tac >- (
       simp[Abbr`itenv2`,MAP2_MAP,LENGTH_COUNT_LIST,check_env_merge] >>
       reverse conj_tac >- (
         match_mp_tac (MP_CANON check_env_more) >>
         qexists_tac`0` >> simp[] >> simp[check_env_def] ) >>
       simp[check_env_def,EVERY_MAP] >>
       simp[EVERY_MEM,MEM_ZIP,FORALL_PROD,LENGTH_COUNT_LIST,EL_MAP,PULL_EXISTS] >>
       simp[EL_COUNT_LIST,check_t_def] ) >>
      full_simp_tac(srw_ss())[init_infer_state_def]>>
      `LENGTH tenv'' = LENGTH funs` by
        metis_tac[LENGTH_MAP]>>
      srw_tac[][]
      >-
        (full_simp_tac(srw_ss())[sub_completion_def]>>
        full_simp_tac(srw_ss())[num_tvs_bind_var_list,bind_tvar_def]>>
        IF_CASES_TAC>>full_simp_tac(srw_ss())[num_tvs_bvl2,num_tvs_def]>>
        full_simp_tac(srw_ss())[Abbr`targs`,EL_MAP,EVERY_EL]>>
        metis_tac[check_freevars_to_check_t])
      >>
        full_simp_tac(srw_ss())[Abbr`itenv2`,tenv_invC_def]>>
        simp[GSYM bvl2_to_bvl,lookup_bvl2,bind_tvar_rewrites, deBruijn_inc0,lookup_tenv_def] >>
        `LENGTH tys = LENGTH funs` by simp[Abbr`tys`,LENGTH_COUNT_LIST] >>
        simp[MAP2_MAP,ZIP_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
        simp[tenv_add_tvs_def,ALOOKUP_MAP] >>
        rpt gen_tac >>
        Cases_on`ALOOKUP tenv'' x` >> simp[] >- (
          CASE_TAC >> simp[] >>
          CASE_TAC >> simp[] >>
          strip_tac >>
          `t = r` by (
            imp_res_tac lookup_freevars >>
            metis_tac[nil_deBruijn_inc] ) >>
          conj_tac >- metis_tac[lookup_freevars] >>
          simp[ALOOKUP_APPEND] >>
          reverse CASE_TAC >- (
            imp_res_tac ALOOKUP_MEM >>
            `MEM x (MAP FST funs)` by (
              rev_full_simp_tac(srw_ss())[MEM_MAP,MEM_ZIP,MEM_EL] >>
              metis_tac[] ) >>
            imp_res_tac ALOOKUP_FAILS >>
            rev_full_simp_tac(srw_ss())[] >>
            full_simp_tac(srw_ss())[MEM_MAP,EXISTS_PROD] ) >>
          full_simp_tac(srw_ss())[tenv_alpha_def,tenv_invC_def,bvl2_lookup] >>
          first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
          strip_tac >> simp[] >>
          CASE_TAC >- metis_tac[] >>
          imp_res_tac ALOOKUP_MEM >>
          full_simp_tac(srw_ss())[EVERY_MEM,FORALL_PROD,check_env_def] >>
          metis_tac[] ) >>
        strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
        first_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
        simp[num_tvs_bind_var_list] >>
        simp[bind_tvar_rewrites,num_tvs_bvl2,num_tvs_def] >>
        strip_tac >> conj_tac >- metis_tac[] >>
        simp[ALOOKUP_APPEND] >>
        CASE_TAC >- (
          imp_res_tac ALOOKUP_FAILS >>
          imp_res_tac ALOOKUP_MEM >>
          `MEM x (MAP FST funs)` by (
            simp[] >>
            simp[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
            metis_tac[] ) >>
          rev_full_simp_tac(srw_ss())[MEM_MAP,MEM_ZIP,EXISTS_PROD,MEM_EL] >>
          metis_tac[] ) >>
        Cases_on`x'`>>simp[] >>
        imp_res_tac ALOOKUP_MEM >>
        full_simp_tac(srw_ss())[MEM_MAP] >>
        simp[check_t_def] >>
        `SND p < LENGTH funs` by (
          rev_full_simp_tac(srw_ss())[MEM_ZIP] >>
          simp[Abbr`tys`,EL_COUNT_LIST] ) >>
        simp[] >>
        simp[Abbr`targs`,EL_MAP] >>
        rpt BasicProvers.VAR_EQ_TAC >>
        rev_full_simp_tac(srw_ss())[MEM_ZIP] >> BasicProvers.VAR_EQ_TAC >>
        simp[Abbr`tys`,EL_COUNT_LIST] >>
        rev_full_simp_tac(srw_ss())[EL_COUNT_LIST,LENGTH_COUNT_LIST] >>
        `FST (EL n funs) = FST (EL n tenv'')` by (
          qpat_assum`MAP FST x = MAP FST y`mp_tac >>
          simp[Once LIST_EQ_REWRITE,EL_MAP] ) >>
        `MEM (FST (EL n tenv''), SND (EL n tenv'')) tenv''` by (
          simp[MEM_EL] >> metis_tac[] ) >>
        imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >> full_simp_tac(srw_ss())[])
   >>
   srw_tac[][]>>
   imp_res_tac infer_funs_length>>
   full_simp_tac(srw_ss())[sub_completion_def]>>
   `t_compat st'.subst s'' ∧ t_wfs s''` by
     metis_tac[pure_add_constraints_success,infer_e_wfs]>>
   qpat_abbrev_tac `ls:(infer_t#infer_t)list = ZIP (A,B)`>>
   `pure_add_constraints s'' ls s''` by
     (match_mp_tac pure_add_constraints_ignore>>
     full_simp_tac(srw_ss())[Abbr`ls`]>>
     full_simp_tac(srw_ss())[EVERY_MEM,MEM_ZIP,LENGTH_COUNT_LIST,PULL_EXISTS]>>
     srw_tac[][]>>
     full_simp_tac(srw_ss())[EL_MAP,EL_COUNT_LIST,LENGTH_COUNT_LIST]>>
     `LENGTH tenv'' = LENGTH env'` by metis_tac[LENGTH_MAP]>>
     last_x_assum(qspec_then`n` assume_tac)>>
     rev_full_simp_tac(srw_ss())[init_infer_state_def]>>
     full_simp_tac(srw_ss())[t_compat_def,Abbr`targs`,EL_MAP]>>
     full_simp_tac(srw_ss())[EL_MAP,MAP_MAP_o]>>
     match_mp_tac EQ_TRANS >>
     qexists_tac`t_walkstar s'' (t_walkstar s' (Infer_Tuvar n))` >>
     conj_asm1_tac >- simp[] >>
     match_mp_tac EQ_TRANS >>
     qexists_tac`t_walkstar s' (Infer_Tuvar n)` >>
     conj_asm1_tac >- (
       match_mp_tac t_walkstar_no_vars >>
       metis_tac[check_t_empty_unconvert_convert_id] ) >>
     simp[EL_MAP] >>
     `n < st'.next_uvar` by
       (imp_res_tac(last(CONJUNCTS infer_e_next_uvar_mono)) >>
       DECIDE_TAC ) >>
     full_simp_tac(srw_ss())[]>>
     `EVERY (check_t 0 (count st'.next_uvar)) env'` by (
       match_mp_tac (last(CONJUNCTS infer_e_check_t)) >>
       first_assum (match_exists_tac o concl) >> simp[] >>
       simp[Abbr`itenv2`,check_env_def,MAP2_MAP,LENGTH_COUNT_LIST] >>
       reverse conj_tac >- (
         full_simp_tac(srw_ss())[EVERY_MEM,check_env_def] >>
         full_simp_tac(srw_ss())[FORALL_PROD] >>
         srw_tac[][] >>
         match_mp_tac(MP_CANON(CONJUNCT1 check_t_more5)) >>
         res_tac >> HINT_EXISTS_TAC >> simp[] ) >>
       simp[EVERY_MAP,UNCURRY] >>
       simp[EVERY_MEM,MEM_ZIP,Abbr`tys`,LENGTH_COUNT_LIST,PULL_EXISTS,EL_MAP,EL_COUNT_LIST] >>
       simp[check_t_def] )>>
     simp[]>>
     match_mp_tac (GEN_ALL check_t_empty_unconvert_convert_id) >>
     qexists_tac`tvs` >>
     match_mp_tac(CONJUNCT1 check_t_walkstar) >>
     simp[] >>
     conj_tac >- ( full_simp_tac(srw_ss())[EVERY_MEM,MEM_EL,PULL_EXISTS] ) >>
     srw_tac[][] >> res_tac>>
     FULL_SIMP_TAC(srw_ss())[num_tvs_bind_var_list,bind_tvar_rewrites,num_tvs_bvl2,num_tvs_def])>>
   `pure_add_constraints st'.subst (constraints' ++ls) s''` by metis_tac[pure_add_constraints_append]>>
   imp_res_tac pure_add_constraints_swap>>
   pop_assum mp_tac >>
   discharge_hyps>-
     metis_tac[infer_e_wfs]>>
   srw_tac[][]>>
   full_simp_tac(srw_ss())[pure_add_constraints_append]>>
   qexists_tac`<|next_uvar:=st'.next_uvar;subst:=s2'|>`>>full_simp_tac(srw_ss())[]>>
   qexists_tac`constraints'`>>qexists_tac`si`>>
   simp[]>>
   qspecl_then[`tvs`,`si`,`s''`]mp_tac(GEN_ALL t_compat_bi_ground) >>
   discharge_hyps >-
    FULL_SIMP_TAC(srw_ss())[num_tvs_bind_var_list,bind_tvar_rewrites,num_tvs_bvl2,num_tvs_def]>>
   srw_tac[][]>>
   full_simp_tac(srw_ss())[MAP_EQ_f]>>
   qpat_assum`A=FDOM si` (SUBST_ALL_TAC o SYM)>>
   match_mp_tac pure_add_constraints_check_s>>
   qexists_tac`st'.subst`>>qexists_tac`ls`>>
   `check_env (count st.next_uvar) itenv2` by (
       simp[Abbr`itenv2`,check_env_def,MAP2_MAP,LENGTH_COUNT_LIST] >>
       reverse conj_tac >- (
         simp[EVERY_MEM] >>
         full_simp_tac(srw_ss())[FORALL_PROD] >>
         srw_tac[][] >>
         match_mp_tac(MP_CANON(CONJUNCT1 check_t_more5)) >>
         full_simp_tac(srw_ss())[EVERY_MEM,FORALL_PROD] >>
         res_tac >> HINT_EXISTS_TAC >> simp[] ) >>
       simp[EVERY_MAP,UNCURRY] >>
       simp[EVERY_MEM,MEM_ZIP,Abbr`tys`,LENGTH_COUNT_LIST,PULL_EXISTS,EL_MAP,EL_COUNT_LIST] >>
       simp[check_t_def] ) >>
     full_simp_tac(srw_ss())[]>>
     conj_tac >- (
       match_mp_tac(last(CONJUNCTS infer_e_wfs)) >>
       first_assum(match_exists_tac o concl) >>
       simp[t_wfs_def] ) >>
     reverse conj_tac >- (
       match_mp_tac(last(CONJUNCTS infer_e_check_s)) >>
       first_assum(match_exists_tac o concl) >>
       simp[GSYM check_cenv_tenvC_ok,check_s_def])>>
     simp[Abbr`ls`,EVERY_MEM,MEM_ZIP,LENGTH_COUNT_LIST,EL_MAP,PULL_EXISTS,EL_COUNT_LIST] >>
     simp[check_t_def] >>
     imp_res_tac (last(CONJUNCTS infer_e_next_uvar_mono)) >>
     srw_tac[][] >- DECIDE_TAC >>
     imp_res_tac(last(CONJUNCTS infer_e_check_t)) >>
     full_simp_tac(srw_ss())[EVERY_MEM,PULL_EXISTS,MEM_EL] >>
     res_tac >> imp_res_tac check_t_more2 >> full_simp_tac(srw_ss())[] ) 


val _ = export_theory ();

