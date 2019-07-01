(*
  Prove determinism lemmas about the type inferencer.
*)
open preamble;
open libTheory typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory;
open astPropsTheory;
open typeSysPropsTheory;
open inferPropsTheory;
open infer_eSoundTheory;
open infer_eCompleteTheory;
open envRelTheory namespacePropsTheory;
open namespaceTheory

val _ = new_theory "type_eDeterm";

val sub_completion_empty = Q.prove (
`!m n s s'. sub_completion m n s [] s' ⇔ count n ⊆ FDOM s' ∧ (∀uv. uv ∈ FDOM s' ⇒ check_t m ∅ (t_walkstar s' (Infer_Tuvar uv))) ∧ s = s'`,
 rw [sub_completion_def, pure_add_constraints_def] >>
 metis_tac []);

Theorem type_p_pat_bindings:
 (∀tvs tenv p t new_bindings.
  type_p tvs tenv p t new_bindings ⇒ MAP FST new_bindings = pat_bindings p []) ∧
 (∀tvs tenv ps ts new_bindings.
  type_ps tvs tenv ps ts new_bindings ⇒ MAP FST new_bindings = pats_bindings ps [])
Proof
 ho_match_mp_tac type_p_ind >>
 rw [pat_bindings_def] >>
 metis_tac [semanticPrimitivesPropsTheory.pat_bindings_accum]
QED

Theorem infer_pe_complete:
   ienv_ok {} ienv ∧
    env_rel_complete FEMPTY ienv tenv (bind_tvar tvs Empty) ∧
    ALL_DISTINCT (pat_bindings p []) ∧
    type_p tvs tenv p t1 tenv1 ∧
    type_e tenv (bind_tvar tvs Empty) e t1
    ⇒
    ?t t' new_bindings st st' s constrs s'.
      infer_e loc ienv e (init_infer_state ss) = (Success t, st) ∧
      infer_p loc ienv p st = (Success (t', new_bindings), st') ∧
      t_unify st'.subst t t' = SOME s ∧
      sub_completion tvs st'.next_uvar s constrs s' ∧
      FDOM s' = count st'.next_uvar ∧
      t1 = convert_t (t_walkstar s' t') ∧
      t1 = convert_t (t_walkstar s' t) ∧
      t_wfs s ∧
      (* This might be implied by something above *)
      EVERY (λ(n,t). check_t tvs {} (t_walkstar s' t)) new_bindings ∧
      convert_env s' new_bindings = tenv1
Proof
  rw []
  >> drule (CONJUNCT1 infer_e_complete)
  >> drule (CONJUNCT1 infer_p_complete) >>
  rw [] >>
  `t_wfs (init_infer_state ss).subst` by rw [t_wfs_def, init_infer_state_def] >>
  first_x_assum (qspecl_then [`loc`, `FEMPTY`, `ienv`, `init_infer_state ss`, `[]`] mp_tac) >>
  rw [sub_completion_empty, init_infer_state_def] >>
  `t_wfs st'.subst`
          by (imp_res_tac (CONJUNCT1 infer_e_wfs) >>
              fs [init_infer_state_def]) >>
  first_x_assum (qspecl_then [`loc`, `s'`, `ienv`, `st'`, `constraints'`] mp_tac) >>
  fs[AND_IMP_INTRO]>>
  impl_tac>-
    (fs[env_rel_complete_def,ienv_ok_def,sub_completion_def]>>
    rw[]>>
    res_tac>>fs[]>>
    imp_res_tac check_t_more2>>
    fs[])>>
  rw [] >>
  MAP_EVERY qexists_tac [`t''`, `new_bindings`, `st''`] >>
  rw [] >>
  `t_wfs st''.subst` by metis_tac [infer_p_wfs] >>
  `check_t tvs {} (t_walkstar s' t') ∧ check_t tvs {} (t_walkstar s'' t'')`
              by (conj_tac >>
                  match_mp_tac (GEN_ALL sub_completion_completes) >>
                  rw []
                  >- metis_tac [sub_completion_wfs]
                  >- (imp_res_tac (CONJUNCT1 infer_e_check_t) >>
                      fs [ienv_ok_def])
                  >- (fs [sub_completion_def]>>
                     res_tac>>
                     imp_res_tac check_t_more2>>
                     fs[])
                  >- metis_tac [sub_completion_wfs]
                  >- (imp_res_tac (CONJUNCT1 infer_p_check_t) >>
                      fs [])
                  >- fs [sub_completion_def]) >>
  `t_walkstar s'' (t_walkstar s' t') = t_walkstar s'' (t_walkstar s'' t'')` by metis_tac [convert_bi_remove] >>
  `t_walkstar s'' t' = t_walkstar s'' t''`
            by metis_tac [t_walkstar_SUBMAP, SUBMAP_REFL, t_compat_def] >>
  `t_compat st''.subst s''`
               by metis_tac [pure_add_constraints_success, sub_completion_def, t_compat_def] >>
  `?si. t_unify st''.subst t' t'' = SOME si ∧ t_compat si s''` by metis_tac [t_compat_eqs_t_unify] >>
  qexists_tac `si` >>
  `t_wfs si` by metis_tac [t_unify_wfs] >>
  rw [] >>
  fs[sub_completion_def] >>
  `pure_add_constraints st''.subst [t',t''] si` by (
    simp[pure_add_constraints_def] ) >>
  `t_wfs s''` by metis_tac[pure_add_constraints_wfs] >>
  `pure_add_constraints s'' [t',t''] s''` by
    (match_mp_tac pure_add_constraints_ignore >>
     fs[t_walkstar_eqn,t_walk_eqn]) >>
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
  qspecl_then[`tvs`,`si2`,`s''`]mp_tac(GEN_ALL t_compat_bi_ground) >>
  impl_tac >- simp[] >> strip_tac >> simp[] >>
  conj_tac >- (
    fs[SUBSET_DEF,EXTENSION] >> rw[] >> res_tac >> DECIDE_TAC ) >>
  fs[simp_tenv_invC_def,convert_env_def] >>
  imp_res_tac type_p_pat_bindings>>fs[]>>
  imp_res_tac infer_p_bindings>>
  pop_assum(qspec_then`[]` assume_tac)>>fs[]>>
  fs[EVERY_MEM,FORALL_PROD]>>rw[]
  >-
    (`ALOOKUP new_bindings p_1 = SOME p_2` by
      (match_mp_tac ALOOKUP_ALL_DISTINCT_MEM>>
      fs[])>>
    res_tac>>res_tac>>fs[]>>
    metis_tac[check_freevars_to_check_t])
  >>
    qpat_assum`MAP FST A = B` mp_tac>>
    ONCE_REWRITE_TAC [LIST_EQ_REWRITE]>>
    strip_tac>>rfs[EL_MAP]>>
    rw[]>>
    pairarg_tac>>fs[]>>
    Cases_on`EL x tenv1`>>
    first_x_assum(qspec_then`x` mp_tac)>>fs[LENGTH_MAP]>>rw[]>>
    `ALOOKUP new_bindings q = SOME t` by
      (match_mp_tac ALOOKUP_ALL_DISTINCT_MEM>>
      fs[]>>metis_tac[MEM_EL])>>
    `ALOOKUP tenv1 q = SOME r` by
      (match_mp_tac ALOOKUP_ALL_DISTINCT_MEM>>
      fs[]>>metis_tac[MEM_EL])>>
    first_x_assum(qspecl_then[`q`,`r`] mp_tac)>>
    rw[]>>
    metis_tac[check_freevars_empty_convert_unconvert_id]
QED

val unconvert_11 = Q.prove (
`!t1 t2. check_freevars 0 [] t1 ∧ check_freevars 0 [] t2 ⇒
  (unconvert_t t1 = unconvert_t t2 ⇔ t1 = t2)`,
 ho_match_mp_tac unconvert_t_ind >>
 rw [unconvert_t_def] >>
 Cases_on `t2` >>
 fs [unconvert_t_def, check_freevars_def] >>
 fs [EVERY_MEM] >>
 eq_tac >>
 rw [] >>
 match_mp_tac LIST_EQ >>
 rw []
 >- metis_tac [LENGTH_MAP] >>
 `x < LENGTH l` by metis_tac [LENGTH_MAP] >>
 `EL x (MAP (λa. unconvert_t a) ts) = EL x (MAP (λa. unconvert_t a) l)` by metis_tac [] >>
 rfs [EL_MAP] >>
 metis_tac [EL_MEM]);

Theorem infer_e_type_pe_determ:
 !loc ienv p e st st' t t' tenv' s.
  ALL_DISTINCT (MAP FST tenv') ∧
  ienv_ok {} ienv ∧
  env_rel_complete FEMPTY ienv tenv Empty ∧
  infer_e loc ienv e (init_infer_state ss) = (Success t, st) ∧
  infer_p loc ienv p st = (Success (t', tenv'), st') ∧
  t_unify st'.subst t t' = SOME s ∧
  EVERY (\(n, t). check_t 0 {} (t_walkstar s t)) tenv'
  ⇒
  type_pe_determ tenv Empty p e
Proof
 rw [type_pe_determ_def] >>
 mp_tac (Q.INST [`tvs`|->`0`] infer_pe_complete) >>
 simp[]>>impl_keep_tac>-
   (imp_res_tac infer_p_bindings>>fs[])>>
 rw [] >>
 mp_tac (Q.INST [`t1`|->`t2`, `tenv1` |-> `tenv2`,`tvs`|->`0`] infer_pe_complete) >>
 rw [] >>rfs[]>>
 fs[convert_env_def]>>
 fs[EVERY_MEM,MAP_EQ_f,FORALL_PROD]>>rw[]>>
 fs [sub_completion_def] >>
 imp_res_tac pure_add_constraints_success >>
 fs [t_compat_def] >>
 metis_tac [t_walkstar_no_vars]
QED

Theorem t_vars_check_t:
    (∀t.
  ¬check_t 0 {} t ∧
  check_t 0 s t ⇒
  ∃n'. n' ∈ s ∧ n' ∈ t_vars t) ∧
  (∀ts.
  ∀x.MEM x ts ⇒
    ¬check_t 0 {} x ∧
    check_t 0 s x ⇒
    ∃n'. n' ∈ s ∧ n' ∈ t_vars x)
Proof
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[check_t_def,t_vars_eqn]>>
  fs[EXISTS_MEM,EVERY_MEM]>>res_tac>>
  qexists_tac `n'`>>
  fs[MEM_MAP]>>
  metis_tac[]
QED

Theorem t_walkstar_diff:
    t_wfs s1 ∧ t_wfs s2 ∧
  (t_walkstar s1 (Infer_Tuvar n) ≠ t_walkstar s2 (Infer_Tuvar n))
  ⇒
  (∀t.(n ∈ t_vars t) ⇒ t_walkstar s1 t ≠ t_walkstar s2 t) ∧
  (∀ts.
  ∀x. MEM x ts ⇒
    n ∈ t_vars x ⇒ t_walkstar s1 x ≠ t_walkstar s2 x)
Proof
  strip_tac>>
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[t_vars_eqn]>>fs[]>>
  fs[t_walkstar_eqn,t_walk_eqn,MEM_MAP]>>
  res_tac>>rfs[]>>
  SPOSE_NOT_THEN assume_tac>>
  imp_res_tac MAP_EQ_f>>
  metis_tac[]
QED

val env_rel_sound_weaken = Q.prove(
  `env_rel_sound FEMPTY ienv tenv tenvE ∧ t_wfs s ⇒
   env_rel_sound s ienv tenv tenvE`,
  fs[env_rel_sound_def]>>rw[]>>res_tac>>
  qexists_tac`tvs'`>>fs[]>>
  match_mp_tac tscheme_approx_weakening>>fs[]>>
  qexists_tac`num_tvs tenvE`>>qexists_tac`FEMPTY`>>fs[SUBMAP_FEMPTY])|>GEN_ALL
  |> curry save_thm "env_rel_sound_weaken";

Theorem type_pe_determ_infer_e:
 !loc ienv p e st st' t t' new_bindings s.
  ALL_DISTINCT (MAP FST new_bindings) ∧
  (*
  check_menv ienv.inf_m ∧
  menv_alpha ienv.inf_m tenv.m ∧
  tenv_ctor_ok tenv.c ∧
  ienv.inf_c = tenv.c ∧
  ienv.inf_t = tenv.t ∧
  tenv_tabbrev_ok tenv.t ∧
  check_env {} ienv.inf_v ∧
  num_tvs tenv.v = 0 ∧
  tenv_inv FEMPTY ienv.inf_v tenv.v ∧*)
  env_rel_sound FEMPTY ienv tenv Empty ∧
  ienv_ok {} ienv ∧
  infer_e loc ienv e (init_infer_state ss) = (Success t, st) ∧
  infer_p loc ienv p st = (Success (t', new_bindings), st') ∧
  t_unify st'.subst t t' = SOME s ∧
  type_pe_determ tenv Empty p e
  ⇒
  EVERY (\(n, t). check_t 0 {} (t_walkstar s t)) new_bindings
Proof
 rw [type_pe_determ_def] >>
 `t_wfs (init_infer_state ss).subst` by rw [t_wfs_def, init_infer_state_def] >>
 `t_wfs st.subst` by metis_tac [infer_e_wfs] >>
 `t_wfs st'.subst` by metis_tac [infer_p_wfs] >>
 `t_wfs s` by metis_tac [t_unify_wfs] >>
 `check_t 0 (count st.next_uvar) t`
          by (imp_res_tac infer_e_check_t >>
              fs [init_infer_state_def,ienv_ok_def]) >>
 `check_s 0 (count st.next_uvar) st.subst`
           by (match_mp_tac (CONJUNCT1 infer_e_check_s) >>
               MAP_EVERY qexists_tac [`loc`, `ienv`, `e`, `init_infer_state ss`] >>
               rw [init_infer_state_def, check_s_def]) >>
 `?l. set l = count st'.next_uvar DIFF FDOM s ∧ ALL_DISTINCT l`
          by metis_tac [FINITE_COUNT, FINITE_DIFF, SET_TO_LIST_INV, ALL_DISTINCT_SET_TO_LIST] >>
 qabbrev_tac `inst1 = MAP (\n. (Infer_Tuvar n, (Infer_Tapp [] Tbool_num))) l` >>
 qabbrev_tac `inst2 = MAP (\n. (Infer_Tuvar n, (Infer_Tapp [] Tint_num))) l` >>
  (* Because we're instantiating exactly the unconstrained variables *)
 let
   fun tac q q1 =
     simp[sub_completion_def] >>
     qexists_tac`s |++ (MAP (λn. (n, ^q)) l)` >>
     conj_asm1_tac >- (
       qunabbrev_tac q1 >>
       qpat_x_assum`t_wfs s`mp_tac >>
       qpat_x_assum`set l = X`mp_tac >>
       qpat_x_assum`ALL_DISTINCT l`mp_tac >>
       qspec_tac(`st'.next_uvar`,`n`) >>
       map_every qid_spec_tac[`s`,`l`] >>
       Induct >>
       simp[pure_add_constraints_def,FUPDATE_LIST_THM] >> rw[] >>
       qho_match_abbrev_tac`∃s2. P s2 ∧ Q s2` >>
       qsuff_tac`∃s2. P s2 ∧ (t_wfs s2 ⇒ Q s2)`>-metis_tac[t_unify_wfs] >>
       simp[Abbr`P`,t_unify_eqn,t_walk_eqn,Once t_vwalk_eqn] >>
       simp[FLOOKUP_DEF] >> rw[] >- (
         fs[EXTENSION] >> metis_tac[] ) >>
       simp[t_ext_s_check_eqn,Once t_oc_eqn,t_walk_eqn] >>
       simp[Abbr`Q`] >> strip_tac >>
       first_x_assum (match_mp_tac o MP_CANON) >>
       simp[FDOM_FUPDATE] >> fs[EXTENSION] >> metis_tac[] ) >>
     conj_tac >- (
       fs[EXTENSION,SUBSET_DEF,FDOM_FUPDATE_LIST,MEM_MAP,EXISTS_PROD] ) >>
     simp[FDOM_FUPDATE_LIST,MEM_MAP,EXISTS_PROD] >>
     imp_res_tac pure_add_constraints_wfs >>
     ntac 3 (pop_assum kall_tac) >>
     reverse(rw[]) >- (
       rw[t_walkstar_eqn,t_walk_eqn,Once t_vwalk_eqn,flookup_fupdate_list] >>
       BasicProvers.CASE_TAC >- (
         imp_res_tac ALOOKUP_FAILS >>
         fs[MEM_MAP,EXTENSION] >> metis_tac[] ) >>
       imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP] >>
       rw[] >> rw[check_t_def] ) >>
     first_assum(fn th=> mp_tac (MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] (CONJUNCT1 infer_p_check_s)) th)) >>
     simp[] >> disch_then(qspec_then`0`mp_tac) >> simp[AND_IMP_INTRO] >>
     impl_tac>-
       fs[ienv_ok_def]>>
     strip_tac >>
     match_mp_tac t_walkstar_check >>
     simp[check_t_def,FDOM_FUPDATE_LIST] >>
     (t_unify_check_s
      |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(same_const``t_unify`` o fst o strip_comb o lhs))))
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
      |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(same_const``pure_add_constraints`` o fst o strip_comb))))
      |> REWRITE_RULE[GSYM AND_IMP_INTRO]
      |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
     disch_then(qspecl_then[`0`,`st'.next_uvar`]mp_tac) >> simp[] >>
     impl_tac >- simp[Abbr q1,EVERY_MEM,MEM_MAP,PULL_EXISTS,check_t_def] >>
     strip_tac >>
     match_mp_tac (MP_CANON check_s_more3) >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     simp[SUBSET_DEF,MEM_MAP,PULL_EXISTS]
 in
   `?s1. sub_completion 0 st'.next_uvar s inst1 s1` by (tac ``Infer_Tapp [] Tbool_num`` `inst1`) >>
   `?s2. sub_completion 0 st'.next_uvar s inst2 s2` by (tac ``Infer_Tapp [] Tint_num`` `inst2`)
 end >>
 `t_wfs s1 ∧ t_wfs s2` by metis_tac[sub_completion_wfs] >>
 imp_res_tac env_rel_sound_weaken>>
 ntac 4 (pop_assum kall_tac)>>
 imp_res_tac sub_completion_unify2 >>
 imp_res_tac infer_p_constraints >>
 (sub_completion_add_constraints |> REWRITE_RULE[GSYM AND_IMP_INTRO] |>
  (fn th => first_assum(mp_tac o MATCH_MP th))) >> simp[] >>
 disch_then imp_res_tac >>
 (* Derive type_e on the two instantiations *)
 (infer_e_sound |> CONJUNCT1 |> SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] |>
  (fn th => first_assum(mp_tac o MATCH_MP th))) >> simp[] >>
 simp[init_infer_state_def] >>
 disch_then imp_res_tac>>fs[]>> pop_assum kall_tac>>
 fs[sub_completion_def,GSYM AND_IMP_INTRO]>>
 first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th))>>
 first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th))>>
 imp_res_tac infer_p_next_uvar_mono >>
 `count st.next_uvar ⊆ count st'.next_uvar` by simp[SUBSET_DEF] >>
 impl_tac >- metis_tac[SUBSET_TRANS] >> simp[] >>
 strip_tac>>
 impl_tac >- metis_tac[SUBSET_TRANS] >> simp[] >>
 strip_tac>>
 imp_res_tac infer_p_check_t>>
 assume_tac (infer_p_sound |> CONJUNCT1)>>
 first_assum (qspecl_then
   [`loc`, `ienv`,`p`,`st`,`t'`,`tenv`,`new_bindings`,`st'`,`0`,`(t,t')::inst1`,`s1`]assume_tac)>>
 first_x_assum (qspecl_then
   [`loc`, `ienv`,`p`,`st`,`t'`,`tenv`,`new_bindings`,`st'`,`0`,`(t,t')::inst2`,`s2`]assume_tac)>>
 rfs[sub_completion_def,ienv_ok_def,env_rel_sound_def]>>
 (*Because t,t' is part of the unifications that yielded s1 and s2*)
 `t_compat s s1 ∧ t_compat s s2` by (
   imp_res_tac pure_add_constraints_success >> rw[] ) >>
 `t_walkstar s t = t_walkstar s t'` by (
   imp_res_tac t_unify_unifier ) >>
 `convert_t (t_walkstar s2 t') = convert_t (t_walkstar s2 t)` by (
   fs[t_compat_def] >> metis_tac[] ) >>
 pop_assum SUBST_ALL_TAC>>rfs[]>>
 res_tac>>pop_assum kall_tac>>
 `convert_t (t_walkstar s1 t') = convert_t (t_walkstar s1 t)` by (
   fs[t_compat_def] >> metis_tac[] ) >>
 pop_assum SUBST_ALL_TAC>>rfs[]>>
 fs[convert_env_def]>>
 spose_not_then strip_assume_tac >>
 fs[EXISTS_MEM,EXISTS_PROD] >>
 qpat_x_assum`MAP X Y = Z`mp_tac >> simp[] >>
 simp[LIST_EQ_REWRITE,EL_MAP,UNCURRY] >>
 qpat_x_assum`MEM X Y`mp_tac >> simp[MEM_EL] >> strip_tac >>
 qexists_tac`n` >>
 pop_assum(assume_tac o SYM) >> simp[] >>
 fs[EVERY_MEM] >>
 first_x_assum(qspec_then`EL n new_bindings`mp_tac) >>
 impl_tac >- metis_tac[MEM_EL] >> simp[] >> strip_tac >>
 qmatch_assum_rename_tac`check_t 0 (count st'.next_uvar) tt` >>
 `t_vars tt ⊆ count (st'.next_uvar)` by imp_res_tac check_t_t_vars >>
 drule (CONJUNCT1 infer_p_check_s) >> disch_then imp_res_tac >>
 `check_s 0 (count st'.next_uvar) s` by
   (match_mp_tac t_unify_check_s>>
   Q.LIST_EXISTS_TAC [`st'.subst`,`t`,`t'`]>>fs[]>>
   `count st.next_uvar ⊆ count st'.next_uvar` by
     (imp_res_tac infer_p_next_uvar_mono>>
     rw[count_def,SUBSET_DEF]>>DECIDE_TAC)>>
   metis_tac[check_t_more5,infer_p_check_t])>>
 `check_t 0 (count st'.next_uvar) (t_walkstar s tt)` by
   (match_mp_tac t_walkstar_check>>fs[]>>
   `count st'.next_uvar ⊆ count st'.next_uvar ∪ FDOM s` by fs[]>>
   metis_tac[check_t_more5,check_s_more3])>>
  imp_res_tac t_vars_check_t>>
  ntac 5 (pop_assum kall_tac)>>
  imp_res_tac t_walkstar_vars_notin>>
  `t_walkstar s1 tt ≠ t_walkstar s2 tt` by
    (Q.ISPECL_THEN [`s2`,`s1`,`n'`]mp_tac (GEN_ALL t_walkstar_diff)>>
    impl_tac>-
      (rfs[]>>
      `MEM n' l` by fs[]>>
      `t_walkstar s1 (Infer_Tuvar n') = Infer_Tapp [] Tbool_num ∧
       t_walkstar s2 (Infer_Tuvar n') = Infer_Tapp [] Tint_num ` by
        (imp_res_tac pure_add_constraints_apply>>
        unabbrev_all_tac>>
        fs[MAP_EQ_f,FORALL_PROD,MEM_MAP]>>
        fsrw_tac[DNF_ss][] >>
        res_tac >>
        fs[t_walkstar_eqn, t_walk_eqn])>>
      fs[]>>EVAL_TAC)>>
    rw[]>>pop_assum kall_tac>>
    pop_assum (qspec_then `t_walkstar s tt` assume_tac)>>rfs[]>>
    metis_tac[t_compat_def])>>
  assume_tac (GEN_ALL (CONJUNCT1 check_t_less))>>
  first_assum(qspecl_then [`count st'.next_uvar`,`s1`,`0`,`tt`] assume_tac)>>
  first_x_assum(qspecl_then [`count st'.next_uvar`,`s2`,`0`,`tt`]assume_tac)>>
  `count st'.next_uvar ∩ COMPL (FDOM s1) = {} ∧
   count st'.next_uvar ∩ COMPL (FDOM s2) = {}` by
    (fs[EXTENSION,SUBSET_DEF]>>metis_tac[])>>
  fs[]>>rfs[]>>
  metis_tac[check_t_empty_unconvert_convert_id]
QED

 (*From ¬check_t 0 {} (t_walkstar s tt) it should follow that
   t_walkstar s tt must contain some unification variables.
   (*
   first_assum(
     mp_tac o (MATCH_MP (GEN_ALL(CONTRAPOS(SPEC_ALL(CONJUNCT1 check_t_walkstar)))))) >>
   *)
   But we know that s is completed by s1 and s2 therefore those
   unification variables are exactly bound in s1 and s2 to
   Infer_Tbool and Infer_Tint, hence the walkstars must differ *)

Theorem infer_funs_complete:
    ienv_ok {} ienv ∧
  tenv_ok tenv ∧
  env_rel_complete FEMPTY ienv tenv Empty ∧
  type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs Empty)) funs bindings
  ⇒
  ∃funs_ts st st' constr s.
  infer_funs loc
    (ienv with inf_v:= nsAppend (alist_to_ns (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) funs (MAP (λn. Infer_Tuvar n)
       (COUNT_LIST (LENGTH funs))))) ienv.inf_v) funs ((init_infer_state ss) with next_uvar:= (init_infer_state ss).next_uvar + LENGTH funs) =
    (Success funs_ts,st) ∧
  st.next_uvar = st'.next_uvar ∧
  st.next_id = st'.next_id ∧
  pure_add_constraints st.subst
    (ZIP (MAP (λn. Infer_Tuvar ((init_infer_state ss).next_uvar + n))
              (COUNT_LIST (LENGTH funs)),funs_ts)) st'.subst ∧
  check_s 0 (count st'.next_uvar) st'.subst ∧
  sub_completion tvs st'.next_uvar st'.subst constr s ∧
  FDOM s = count st'.next_uvar ∧
  MAP SND bindings = MAP (convert_t o t_walkstar s) funs_ts
Proof
  rw[]>>
  imp_res_tac type_funs_distinct >> fs[FST_triple] >>
  imp_res_tac type_funs_MAP_FST >>
  imp_res_tac type_funs_Tfn>>
  Q.ISPECL_THEN [`(init_infer_state ss)`,`[]:(infer_t,infer_t) alist`,`FEMPTY:num|->infer_t`,`MAP SND bindings`,`tvs`] mp_tac extend_multi_props>>
  fs[]>>
  impl_keep_tac>-
    (fs[t_wfs_def,init_infer_state_def,pure_add_constraints_def,EVERY_MAP,FORALL_PROD,EVERY_MEM]>>
    rw[]>>
    imp_res_tac ALOOKUP_ALL_DISTINCT_MEM>>res_tac>>fs[])>>
  qmatch_goalsub_abbrev_tac`pure_add_constraints _ init_constraints init_subst`>>rw[]>>
  qmatch_goalsub_abbrev_tac`infer_funs _ ienv_upd _`>>rw[]>>
  drule (el 3 (CONJUNCTS infer_e_complete))>>
  disch_then (qspecl_then [`loc`, `init_subst`,`ienv_upd`,`((init_infer_state ss) with next_uvar := LENGTH funs)`,`init_constraints`] mp_tac)>>
  fs[Abbr`ienv_upd`]>>
  impl_keep_tac>-
    (* Hmm, this gets re-proved a lot*)
    (fs[ienv_ok_def,ienv_val_ok_def]>>
    CONJ_TAC>-
      (match_mp_tac nsAll_nsAppend>>
      rw[]
      >-
        (match_mp_tac nsAll_alist_to_ns>>
        simp[MAP2_MAP,LENGTH_COUNT_LIST]>>
        fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,MEM_ZIP,LENGTH_COUNT_LIST]>>rw[]>>
        simp[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST,check_t_def])
       >>
         irule nsAll_mono>>
         HINT_EXISTS_TAC>>
         simp[FORALL_PROD]>>
         metis_tac[check_t_more])>>
    fs[init_infer_state_def,sub_completion_def]>>
    CONJ_ASM2_TAC >- fs[] >> rw[]
    >-
      metis_tac[LENGTH_MAP]
    >>
      fs[env_rel_complete_def,lookup_var_def,lookup_varE_def]>>
      Cases>>fs[]
      >-
        (qpat_abbrev_tac`ls = MAP2 A funs C `>>
        `MAP FST ls = MAP FST funs` by
          (fs[Abbr`ls`,MAP2_MAP,LENGTH_COUNT_LIST,MAP_MAP_o]>>
          rpt(qpat_x_assum`A=B` sym_sub_tac)>>
          qpat_abbrev_tac`ls = MAP A (COUNT_LIST B)`>>
          `LENGTH ls = LENGTH funs` by fs[Abbr`ls`,LENGTH_COUNT_LIST]>>
          pop_assum mp_tac>>
          rpt(pop_assum kall_tac)>>
          qid_spec_tac`ls`>>
          Induct_on`funs`>>
          fs[COUNT_LIST_def,FORALL_PROD,LENGTH_NIL]>>
          rw[]>>
          Cases_on`ls`>>fs[])>>
        fs[tveLookup_bvl]>>
        FULL_CASE_TAC>>fs[]
        >-
          (fs[tveLookup_def]>>
          fs[nsLookup_nsAppend_some,nsLookup_alist_to_ns_some,nsLookup_alist_to_ns_none]>>
          fs[id_to_mods_def]>>
          ntac 3 strip_tac>>res_tac>>fs[]>>
          rw[] >- metis_tac[]>>
          qexists_tac`tvs''`>>qexists_tac`t'`>>rw[]
          >-
            metis_tac[ALOOKUP_NONE]
          >>
            match_mp_tac tscheme_approx_weakening>>asm_exists_tac>>fs[])
        >>
          res_tac>>fs[]>>
          fs[deBruijn_inc0]>>
          rw[] >- metis_tac[]>>
          fs[nsLookup_nsAppend_some,nsLookup_alist_to_ns_some,nsLookup_alist_to_ns_none]>>
          fs[id_to_mods_def]>>
          imp_res_tac ALOOKUP_MEM>>fs[MEM_EL]>>
          `EL n' ls = (n,0,Infer_Tuvar n') ∧ n' < LENGTH ls` by
            (fs[Abbr`ls`,MAP2_MAP,LENGTH_COUNT_LIST]>>
            `n = EL n' (MAP FST funs) ∧ n' < LENGTH funs` by
               metis_tac[EL_MAP,FST,LENGTH_MAP]>>
            ntac 2 (pop_assum mp_tac)>>
            rpt(pop_assum kall_tac)>>
            simp[EL_MAP,LENGTH_COUNT_LIST,EL_ZIP,EL_COUNT_LIST]>>
            pairarg_tac>>fs[])>>
          qexists_tac`0`>>
          qexists_tac`Infer_Tuvar n'`>>
          rw[]
          >-
            metis_tac[ALOOKUP_ALL_DISTINCT_EL,FST,SND]
          >>
            fs[tscheme_approx_def,LENGTH_NIL,infer_deBruijn_subst_id,EL_MAP]>>
            qpat_assum`A = EL n' B` sym_sub_tac>>fs[]>>
            imp_res_tac check_freevars_to_check_t>>
            metis_tac[t_walkstar_no_vars])
      >>
        fs[nsLookup_nsAppend_some,nsLookup_alist_to_ns_some,nsLookup_alist_to_ns_none]>>
        ntac 3 strip_tac>>res_tac>>rw[]
        >-
          metis_tac[]
        >-
          (fs[alist_to_ns_def]>>Cases_on`p1`>>fs[nsLookupMod_def])
        >>
          match_mp_tac tscheme_approx_weakening>>asm_exists_tac>>fs[])>>
  rw[]>> fs[]>>
  (*
  Note: This is the standard trick to swap the order of unification with subcompletion in the completeness proofs *)
  qmatch_goalsub_abbrev_tac`pure_add_constraints _ ls _`>>
  fs[sub_completion_def]>>
  `t_compat st'.subst s' ∧ t_wfs st'.subst ∧ t_wfs s'` by
    (imp_res_tac infer_e_wfs>>rfs[]>>
    metis_tac[pure_add_constraints_success])>>
  imp_res_tac infer_funs_length>>
  (* First, we show that re-applying the unifications after subcompletion is irrelevant *)
  `pure_add_constraints s' ls s'` by
    (match_mp_tac pure_add_constraints_ignore>>rw[]>>
    fs[Abbr`ls`,EVERY_MEM,FORALL_PROD,MEM_ZIP,LENGTH_COUNT_LIST]>>
    rw[]>>
    fs[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST]>>
    (* In this case, the completion was already forced initially *)
    first_x_assum(qspec_then `n` mp_tac)>>
    impl_tac>-
      fs[SUBSET_DEF]>>
    simp[EL_MAP]>>
    imp_res_tac infer_e_check_t>>rfs[ienv_ok_def]>>
    drule (CONJUNCT1 check_t_walkstar)>>
    disch_then(qspecl_then[`EL n env'`,`tvs`] mp_tac)>>
    impl_tac>-
      (fs[EVERY_EL]>>res_tac>>
      metis_tac[CONJUNCT1 check_t_more2,ADD_CLAUSES])>>
    rw[]>>
    `t_walkstar s' (EL n env') = t_walkstar init_subst (Infer_Tuvar n)` by
      metis_tac [check_t_empty_unconvert_convert_id]>>
    pop_assum SUBST_ALL_TAC>>
    pop_assum kall_tac>>
    fs [t_compat_def] >>
    metis_tac [t_walkstar_no_vars])>>
  (* Next we compose the constraints *)
  `pure_add_constraints st'.subst (constraints' ++ls) s'` by metis_tac[pure_add_constraints_append]>>
  imp_res_tac pure_add_constraints_swap>>
  (* And break it upwe compose the constraints *)
  fs[pure_add_constraints_append]>>
  (* The thing in the middle is the desired unification *)
  qexists_tac`<|next_uvar:=st'.next_uvar;subst:=s2'';next_id:=st'.next_id|>`>>
  fs[]>>
  qexists_tac`constraints'`>>qexists_tac`si'`>>
  simp[]>>
  qspecl_then[`tvs`,`si'`,`s'`]mp_tac(GEN_ALL t_compat_bi_ground) >>
  impl_tac >-
    fs[]>>
  fs[GSYM MAP_MAP_o]>>rw[]>>
  qpat_x_assum`A=FDOM si'` sym_sub_tac>>
  match_mp_tac pure_add_constraints_check_s>>
  qexists_tac`st'.subst`>>qexists_tac`ls`>>
  imp_res_tac infer_e_next_uvar_mono>>
  imp_res_tac infer_e_check_t>>
  rfs[ienv_ok_def]>>
  rw[]
  >-
    (fs[Abbr`ls`,EVERY_MEM,FORALL_PROD,MEM_ZIP,LENGTH_COUNT_LIST]>>
    rw[]>>simp[EL_MAP,EL_COUNT_LIST,LENGTH_COUNT_LIST]
    >-
      fs[check_t_def]
    >>
      metis_tac[MEM_EL])
  >>
    match_mp_tac (el 4 (CONJUNCTS infer_e_check_s))>>
    asm_exists_tac>>fs[ienv_ok_def,init_infer_state_def,check_s_def]
QED

val _ = export_theory ();
