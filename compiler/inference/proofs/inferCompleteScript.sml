(*
  Proves completeness of the type inferencer, i.e. if there is a type
  for the program, then the type inferencer will find a type (the most
  general type).
*)

open preamble semanticPrimitivesTheory namespacePropsTheory
     astTheory astPropsTheory typeSystemTheory typeSysPropsTheory
     unifyTheory inferTheory inferPropsTheory envRelTheory
     infer_eSoundTheory infer_eCompleteTheory type_eDetermTheory type_dCanonTheory;
open terminationTheory

val _ = new_theory "inferComplete";

val generalise_no_uvars = Q.prove (
`(!t m n s dbvars.
  check_t dbvars {} t
  ⇒
  generalise m n s t = (0,s,t)) ∧
 (!ts m n s dbvars.
  EVERY (check_t dbvars {}) ts
  ⇒
  generalise_list m n s ts = (0,s,ts))`,
 ho_match_mp_tac infer_tTheory.infer_t_induction >>
 srw_tac[] [generalise_def, check_t_def]
 >- metis_tac [PAIR_EQ] >>
 rw [PULL_FORALL] >>
 res_tac >>
 pop_assum (qspecl_then [`s`, `n`, `m`] mp_tac) >>
 rw [] >>
 rw [] >>
 first_x_assum (qspecl_then [`s'`, `n`, `m`] mp_tac) >>
 rw [] >>
 rw [] >>
 metis_tac [PAIR_EQ]);

val t_ind = t_induction
  |> Q.SPECL[`P`,`EVERY P`]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) []
  |> Q.GEN`P`;

Theorem env_rel_binding_lemma:
  !t fvs fvs' subst.
   check_freevars 0 fvs' t ∧
   set fvs' ⊆ set fvs ∧
   ALL_DISTINCT fvs'
   ⇒
   infer_deBruijn_subst subst
     (infer_type_subst (ZIP (fvs',MAP Infer_Tvar_db (COUNT_LIST (LENGTH (fvs'))))) t) =
   infer_deBruijn_subst
     (GENLIST (λn.
          infer_deBruijn_subst subst
            (case find_index (EL n fvs) fvs' 0 of
               NONE => Infer_Tapp [] arb
             | SOME t => Infer_Tvar_db t)) (LENGTH fvs))
     (infer_type_subst (ZIP (fvs,GENLIST (λx. Infer_Tvar_db x) (LENGTH fvs))) t)
Proof
  ho_match_mp_tac t_ind >>
  rw [infer_type_subst_def, infer_deBruijn_subst_def, check_freevars_def]
  >- (
    qmatch_assum_abbrev_tac `MEM name _` >>
    every_case_tac >>
    fs [ALOOKUP_FAILS, SUBSET_DEF, MEM_MAP, MEM_ZIP, LENGTH_COUNT_LIST,
        infer_deBruijn_subst_def]
    >- (
      every_case_tac >>
      fs [GSYM find_index_NOT_MEM, infer_deBruijn_subst_def, MEM_EL] >>
      rw [] >>
      metis_tac [])
    >- (
      every_case_tac >>
      fs [GSYM find_index_NOT_MEM, infer_deBruijn_subst_def, MEM_EL] >>
      rw [] >>
      metis_tac [])
    >- (
      every_case_tac >>
      fs [GSYM find_index_NOT_MEM, infer_deBruijn_subst_def, MEM_EL] >>
      rw [] >>
      metis_tac [])
    >- (
      imp_res_tac ALOOKUP_MEM >>
      fs [MEM_ZIP, LENGTH_COUNT_LIST] >>
      rw [] >>
      fs [EL_MAP, LENGTH_COUNT_LIST, infer_deBruijn_subst_def, EL_COUNT_LIST] >>
      drule find_index_ALL_DISTINCT_EL >>
      disch_then drule >>
      disch_then (qspec_then `0` mp_tac) >>
      asm_simp_tac std_ss [] >>
      rw [infer_deBruijn_subst_def]))
  >- (
    irule LIST_EQ >>
    rw [EL_MAP] >>
    fs [EVERY_EL])
QED

Theorem env_rel_binding_lemma2:
   !t fvs fvs' subst.
    check_freevars 0 fvs' t ∧
    set fvs' ⊆ set fvs ∧
    ALL_DISTINCT fvs'
    ⇒
    infer_deBruijn_subst subst
      (infer_type_subst (ZIP (fvs,GENLIST (λx. Infer_Tvar_db x) (LENGTH fvs))) t) =
    infer_deBruijn_subst
      (GENLIST (λn.
           infer_deBruijn_subst subst
             (case find_index (EL n fvs') fvs 0 of
                NONE => Infer_Tapp [] TC_int
              | SOME t => Infer_Tvar_db t)) (LENGTH fvs'))
      (infer_type_subst (ZIP (fvs',MAP Infer_Tvar_db (COUNT_LIST (LENGTH fvs')))) t)
Proof
  ho_match_mp_tac t_ind >>
  rw [infer_type_subst_def, infer_deBruijn_subst_def, check_freevars_def]
  >- (
    qmatch_assum_abbrev_tac `MEM name _` >>
    every_case_tac >>
    fs [ALOOKUP_FAILS, SUBSET_DEF, MEM_MAP, MEM_ZIP, LENGTH_COUNT_LIST,
        infer_deBruijn_subst_def]
    >- (
      every_case_tac >>
      fs [GSYM find_index_NOT_MEM, infer_deBruijn_subst_def, MEM_EL] >>
      rw [] >>
      metis_tac [])
    >- (
      every_case_tac >>
      fs [GSYM find_index_NOT_MEM, infer_deBruijn_subst_def, MEM_EL] >>
      rw [] >>
      metis_tac [])
    >- (
      every_case_tac >>
      fs [GSYM find_index_NOT_MEM, infer_deBruijn_subst_def, MEM_EL] >>
      rw [] >>
      metis_tac [])
    >- (
      imp_res_tac ALOOKUP_MEM >>
      fs [MEM_ZIP, LENGTH_COUNT_LIST] >>
      rw [] >>
      fs [EL_MAP, LENGTH_COUNT_LIST, infer_deBruijn_subst_def, EL_COUNT_LIST] >>
      imp_res_tac ALOOKUP_find_index_SOME >>
      fs [MAP_ZIP, EL_ZIP, LENGTH_GENLIST, LENGTH_ZIP] >>
      rfs [MAP_ZIP, EL_ZIP, LENGTH_GENLIST, LENGTH_ZIP] >>
      rw [infer_deBruijn_subst_def]))
  >- (
    irule LIST_EQ >>
    rw [EL_MAP] >>
    fs [EVERY_EL])
QED

Theorem unconvert_type_subst:
   (!t subst fvs.
     check_freevars 0 fvs t ∧ set fvs ⊆ set (MAP FST subst) ⇒
     unconvert_t (type_subst (alist_to_fmap subst) t) =
     infer_type_subst (MAP (\(x,y). (x, unconvert_t y)) subst) t) ∧
  (!ts subst fvs.
     EVERY (check_freevars 0 fvs) ts ∧ set fvs ⊆ set (MAP FST subst) ⇒
     MAP (unconvert_t o type_subst (alist_to_fmap subst)) ts =
     MAP (infer_type_subst (MAP (\(x,y). (x, unconvert_t y)) subst)) ts)
Proof
 Induct >>
 rw [unconvert_t_def, type_subst_def, infer_type_subst_def, MAP_MAP_o,
     check_freevars_def] >>
 fs [combinTheory.o_DEF]
 >- (
   every_case_tac >>
   fs [ALOOKUP_MAP] >>
   fs [] >>
   fs [ALOOKUP_NONE, SUBSET_DEF] >>
   metis_tac []) >>
 metis_tac []
QED

Theorem env_rel_binding:
   !fvs t fvs' name.
   check_freevars 0 fvs' t ∧
   set fvs' ⊆ set fvs
   ⇒
   env_rel
     <|v :=
        nsSing name
          (LENGTH fvs,
           type_subst
             (alist_to_fmap (ZIP (fvs,MAP Tvar_db (GENLIST (λx. x) (LENGTH fvs)))))
             t);
      c := nsEmpty;
      t := nsEmpty|>
    <|inf_v :=
        nsSing name
          (LENGTH (nub fvs'),
           infer_type_subst
             (ZIP (nub fvs', MAP Infer_Tvar_db (COUNT_LIST (LENGTH (nub fvs')))))
             t);
      inf_c := nsEmpty;
      inf_t := nsEmpty|>
Proof
  rw [env_rel_def]
  >- (
    rw [ienv_ok_def, ienv_val_ok_def] >>
    Cases_on `nub fvs' = []` >>
    fs []
    >- (
      simp [COUNT_LIST_def] >>
      irule (CONJUNCT1 infer_type_subst_empty_check) >>
      fs [nub_eq_nil])
    >- (
      irule check_t_infer_type_subst_dbs >>
      qexists_tac `0` >>
      rw [] >>
      metis_tac [check_freevars_type_name_subst]))
  >- (
    rw [typeSoundInvariantsTheory.tenv_ok_def, typeSoundInvariantsTheory.tenv_val_ok_def] >>
    irule check_freevars_subst_single >>
    rw [EVERY_MAP, EVERY_GENLIST, check_freevars_def] >>
    rw [] >>
    irule check_freevars_add >>
    qexists_tac `0` >>
    rw [] >>
    irule check_freevars_more >>
    metis_tac [])
  >- (
    rw [env_rel_sound_def, lookup_var_def]
    >- (
      irule check_freevars_subst_single >>
      rw [EVERY_MAP, EVERY_GENLIST, check_freevars_def] >>
      irule check_freevars_add >>
      qexists_tac `0` >>
      rw [] >>
      irule check_freevars_more >>
      metis_tac []) >>
    rw [tscheme_approx_def, t_walkstar_FEMPTY] >>
    drule (CONJUNCT1 unconvert_type_subst) >>
    disch_then (qspec_then `ZIP (fvs,MAP Tvar_db (GENLIST (λx. x) (LENGTH fvs)))` mp_tac) >>
    impl_tac
    >- (
      fs [SUBSET_DEF] >>
      rw [MEM_MAP, MEM_ZIP, LENGTH_GENLIST] >>
      fs [PULL_EXISTS] >>
      metis_tac [MEM_EL]) >>
    simp [] >>
    disch_then kall_tac >>
    `MAP (\(x,y). (x:string, unconvert_t y)) = MAP (\p. (FST p, unconvert_t (SND p)))`
      by (AP_TERM_TAC >> rw [LAMBDA_PROD]) >>
    simp [GSYM ZIP_MAP, LENGTH_GENLIST, MAP_GENLIST, combinTheory.o_DEF, unconvert_t_def] >>
    EXISTS_TAC ``GENLIST (\n. case find_index (EL n (fvs:tvarN list)) (nub fvs') 0
                                of NONE => Infer_Tapp [] TC_int
                                 | SOME t => Infer_Tvar_db t) (LENGTH fvs)`` >>
    rw [EVERY_GENLIST]
    >- (
      every_case_tac >>
      rw [check_t_def] >>
      drule find_index_LESS_LENGTH >>
      rw []) >>
    rw [MAP_GENLIST, combinTheory.o_DEF] >>
    irule env_rel_binding_lemma >>
    rw [all_distinct_nub] >>
    metis_tac [check_freevars_more, nub_set, SUBSET_DEF])
  >- (
   rw [env_rel_complete_def, lookup_var_def]
   >- (
     qexists_tac `LENGTH fvs` >>
     irule check_freevars_subst_single >>
     rw [EVERY_MAP, EVERY_GENLIST, check_freevars_def] >>
     irule check_freevars_add >>
     qexists_tac `0` >>
     rw [] >>
     irule check_freevars_more >>
     metis_tac []) >>
    rw [tscheme_approx_def, t_walkstar_FEMPTY] >>
    drule (CONJUNCT1 unconvert_type_subst) >>
    disch_then (qspec_then `ZIP (fvs,MAP Tvar_db (GENLIST (λx. x) (LENGTH fvs)))` mp_tac) >>
    impl_tac
    >- (
      fs [SUBSET_DEF] >>
      rw [MEM_MAP, MEM_ZIP, LENGTH_GENLIST] >>
      fs [PULL_EXISTS] >>
      metis_tac [MEM_EL]) >>
    simp [] >>
    disch_then kall_tac >>
    `MAP (\(x,y). (x:string, unconvert_t y)) = MAP (\p. (FST p, unconvert_t (SND p)))`
      by (AP_TERM_TAC >> rw [LAMBDA_PROD]) >>
    simp [GSYM ZIP_MAP, LENGTH_GENLIST, MAP_GENLIST, combinTheory.o_DEF, unconvert_t_def] >>
    EXISTS_TAC ``GENLIST (\n. case find_index (EL n (nub fvs':tvarN list)) fvs 0
                                of NONE => Infer_Tapp [] TC_int
                                 | SOME t => Infer_Tvar_db t) (LENGTH (nub fvs'))`` >>
    rw [EVERY_GENLIST]
    >- (
      every_case_tac >>
      rw [check_t_def] >>
      drule find_index_LESS_LENGTH >>
      rw []) >>
    rw [MAP_GENLIST, combinTheory.o_DEF] >>
    irule env_rel_binding_lemma2 >>
    rw [all_distinct_nub] >>
    metis_tac [check_freevars_more, nub_set, SUBSET_DEF])
QED

val env_rel_complete_bind = Q.prove(`
  env_rel_complete FEMPTY ienv tenv Empty ⇒
  env_rel_complete FEMPTY ienv tenv (bind_tvar tvs Empty)`,
  fs[env_rel_complete_def,bind_tvar_def,lookup_var_def,lookup_varE_def,tveLookup_def]>>rw[]>>every_case_tac>>fs[]>>
  res_tac>>fs[]>> TRY(metis_tac[])>>
  match_mp_tac tscheme_approx_weakening>>asm_exists_tac>>fs[t_wfs_def]);

Theorem type_pe_determ_canon_infer_e:
 !loc ienv p e st st' t t' new_bindings s.
  ALL_DISTINCT (MAP FST new_bindings) ∧
  env_rel_sound FEMPTY ienv tenv Empty ∧
  ienv_ok {} ienv ∧
  start_type_id ≤ ss.next_id ∧
  inf_set_tids_ienv (count ss.next_id) ienv ∧
  infer_e loc ienv e (init_infer_state ss) = (Success t, st) ∧
  infer_p loc ienv p st = (Success (t', new_bindings), st') ∧
  t_unify st'.subst t t' = SOME s ∧
  type_pe_determ_canon ss.next_id tenv Empty p e
  ⇒
  EVERY (\(n, t). check_t 0 {} (t_walkstar s t)) new_bindings
Proof
 rw [type_pe_determ_canon_def] >>
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
 fs[AND_IMP_INTRO]>>
 first_x_assum (qpat_assum`type_p _ _ _ _ (_ s1 _)` o mp_then Any mp_tac)>>
 disch_then (qpat_assum`type_p _ _ _ _ (_ s2 _)` o mp_then Any mp_tac)>>
 `convert_t (t_walkstar s1 t') = convert_t (t_walkstar s1 t)` by (
   fs[t_compat_def] >> metis_tac[] ) >>
 simp[]>>
 impl_tac >- (
   imp_res_tac infer_p_inf_set_tids \\ fs[]
   \\ fs[convert_env_def,EVERY_MAP, UNCURRY, set_tids_subset_def]
   \\ simp[EVERY_MEM, GSYM FORALL_AND_THM, GSYM IMP_CONJ_THM]
   \\ ntac 2 strip_tac
   \\ DEP_REWRITE_TAC[GSYM inf_set_tids_unconvert]
   \\ DEP_REWRITE_TAC[check_t_empty_unconvert_convert_id]
   \\ conj_tac >- (
     fs[EVERY_MEM]
     \\ res_tac
     \\ pairarg_tac \\ fs[]
     \\ conj_tac \\ qexists_tac`0` \\ irule t_walkstar_check
     \\ fs[]
     \\ (conj_tac >- (
           irule check_s_more3
           \\ asm_exists_tac \\ fs[]
           \\ irule pure_add_constraints_check_s
           \\ goal_assum(first_assum o mp_then(Pos last) mp_tac)
           \\ simp[GSYM CONJ_ASSOC]
           \\ conj_tac
           >- (
             irule (CONJUNCT1 check_t_more5)
             \\ asm_exists_tac \\ fs[] )
           \\ reverse conj_tac
           >- (
             irule(CONJUNCT1 infer_p_check_s)
             \\ goal_assum(first_assum o mp_then(Pat`infer_p`) mp_tac)
             \\ fs[] )
           \\ simp[EVERY_MEM,Abbr`inst1`,Abbr`inst2`]
           \\ simp[MEM_MAP,PULL_EXISTS, check_t_def] ))
     \\ irule (CONJUNCT1 check_t_more5)
     \\ asm_exists_tac \\ fs[])
   \\ first_assum(mp_then (Pos last) mp_tac (GEN_ALL (CONJUNCT1 t_unify_set_tids)))
   \\ simp[]
   \\ disch_then(qspec_then`count ss.next_id`mp_tac)
   \\ impl_tac
   >- (
     imp_res_tac infer_p_inf_set_tids \\ fs[]
     \\ imp_res_tac infer_e_inf_set_tids \\ fs[]
     \\ rw[] \\ first_x_assum irule \\ fs[]
     \\ fs[start_type_id_prim_tids_count])
   \\ strip_tac
   \\ last_x_assum(mp_then (Pos last) mp_tac (GEN_ALL pure_add_constraints_set_tids))
   \\ last_x_assum(mp_then (Pos last) mp_tac (GEN_ALL pure_add_constraints_set_tids))
   \\ simp[EVERY_MAP]
   \\ disch_then(qspec_then`count ss.next_id`mp_tac)
   \\ impl_tac >- (
     simp[EVERY_MAP,Abbr`inst2`,inf_set_tids_subset_def,inf_set_tids_def]
     \\ EVAL_TAC \\ fs[start_type_id_def] )
   \\ strip_tac
   \\ disch_then(qspec_then`count ss.next_id`mp_tac)
   \\ impl_tac >- (
     simp[EVERY_MAP,Abbr`inst1`,inf_set_tids_subset_def,inf_set_tids_def]
     \\ EVAL_TAC \\ fs[start_type_id_def] )
   \\ strip_tac
   \\ simp[GSYM inf_set_tids_subset_def]
   \\ fs[EVERY_MEM, PULL_FORALL, AND_IMP_INTRO, GSYM CONJ_ASSOC]
   \\ conj_tac \\ irule (SIMP_RULE std_ss [] t_walkstar_set_tids) \\ fs[]
   \\ first_x_assum irule \\ fs[start_type_id_prim_tids_count]
   \\ (infer_e_inf_set_tids |> CONJUNCT1 |> GEN_ALL |> drule)
   \\ disch_then(first_assum o mp_then(Pat`inf_set_tids_ienv`)mp_tac)
   \\ fs[start_type_id_prim_tids_count]) \\
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




fun str_assums strs = ConseqConv.DISCH_ASM_CONSEQ_CONV_TAC
        (ConseqConv.CONSEQ_REWRITE_CONV ([], strs, []));

val ap_lemma = Q.prove (`!f. x = y ==> f x = f y`, fs []);

Theorem inf_set_tids_extend_dec_ienv:
   inf_set_tids_ienv (count n) ienv2
    /\ inf_set_tids_ienv (count m) ienv
    /\ m <= n
    ==> inf_set_tids_ienv (count n) (extend_dec_ienv ienv2 ienv)
Proof
  fs [inf_set_tids_ienv_def]
  \\ rpt disch_tac
  \\ fs[extend_dec_ienv_def]
  \\ conj_tac
  >- (
    match_mp_tac nsAll_nsAppend \\ fs[]
    \\ fs[inf_set_tids_unconvert,inf_set_tids_subset_def]
    \\ irule nsAll_mono
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ rw[SUBSET_DEF, UNCURRY]
    \\ res_tac \\ rw[])
  \\ conj_tac
  >- (
    match_mp_tac nsAll_nsAppend \\ fs[]
    \\ irule nsAll_mono
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ rw[SUBSET_DEF, UNCURRY, inf_set_tids_subset_def]
    \\ fs[EVERY_MEM]
    \\ rw[] \\ res_tac \\ fs[] )
  \\ match_mp_tac nsAll_nsAppend \\ fs[]
  \\ irule nsAll_mono
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[SUBSET_DEF, UNCURRY, inf_set_tids_subset_def]
  \\ rw[] \\ res_tac \\ fs[]
QED

Theorem infer_d_complete_canon:
  (!d n tenv ids tenv' ienv st1.
   type_d_canon n tenv d ids tenv' ∧
   env_rel tenv ienv ∧
   inf_set_tids_ienv (count n) ienv ∧
   st1.next_id = n ∧ start_type_id ≤ n
   ⇒
   ?ienv' st2.
     env_rel tenv' ienv' ∧
     st2.next_id = st1.next_id + ids ∧
     infer_d ienv d st1 = (Success ienv', st2)) ∧
  (!ds n tenv ids tenv' ienv st1.
   type_ds_canon n tenv ds ids tenv' ∧
   env_rel tenv ienv ∧
   inf_set_tids_ienv (count n) ienv ∧
   st1.next_id = n ∧ start_type_id ≤ n
   ⇒
   ?ienv' st2.
     env_rel tenv' ienv' ∧
     st2.next_id = st1.next_id + ids ∧
     infer_ds ienv ds st1 = (Success ienv', st2))
Proof
  Induct>>
  rw [] >>
  imp_res_tac type_d_canon_tenv_ok >>
  qpat_x_assum`_ _ _ _ _ tenv'` mp_tac>>
  simp[Once type_d_canon_cases]>>rw[]
  >- ( (* Let poly *)
    rw[infer_d_def,success_eqns,init_state_def] >>
    `ienv_ok {} ienv` by fs [env_rel_def] >>
    `env_rel_complete FEMPTY ienv tenv Empty` by fs [env_rel_def] >>
    imp_res_tac env_rel_complete_bind>>
    pop_assum (qspec_then`tvs` assume_tac)>>
    drule (GEN_ALL infer_pe_complete) >>
    rpt (disch_then drule) >>
    disch_then (qspecl_then [`st1`,`<| loc := SOME l; err := ienv.inf_t |>`] mp_tac) >>
    rw [] >>
    simp [init_state_def, success_eqns] >>
    pairarg_tac >>
    fs[success_eqns]>>
    CONJ_ASM2_TAC
    >-
      (* the subcompletion of s corresponding to generalise_list *)
      (drule (GEN_ALL generalise_complete)>>
      disch_then(qspecl_then[`st'.next_uvar`,`Tbool_num`,`count st'.next_id`]mp_tac o
                 CONV_RULE(RESORT_FORALL_CONV(List.rev)))>>fs[]>>
      impl_keep_tac>-
        (`t_wfs (init_infer_state st1).subst` by (EVAL_TAC>>fs[t_wfs_def])>>
        imp_res_tac infer_e_wfs>>
        imp_res_tac infer_p_wfs>>
        imp_res_tac infer_e_check_t>>
        rfs[]>>
        imp_res_tac infer_p_check_t>>
        fs[EVERY_MAP,FORALL_PROD,LAMBDA_PROD,ienv_ok_def]>>
        rfs[]>>
        match_mp_tac t_unify_check_s>>fs[]>>
        asm_exists_tac>>fs[]>>
        rw[]
        >-
          (match_mp_tac (CONJUNCT1 infer_p_check_s)>>asm_exists_tac>>fs[]>>
          match_mp_tac (el 1 (CONJUNCTS infer_e_check_s))>>asm_exists_tac>>
          fs[ienv_ok_def,check_s_def,init_infer_state_def])
        >>
          imp_res_tac check_t_more4>>
          pop_assum match_mp_tac>>
          metis_tac[infer_e_next_uvar_mono,infer_p_next_uvar_mono])>>
      fs[env_rel_def]>>rw[]
      >-
         (imp_res_tac infer_d_check >>
         pop_assum kall_tac>>
         pop_assum (mp_tac o (CONV_RULE (RESORT_FORALL_CONV (sort_vars ["d","st1"]))))>>
         disch_then(qspecl_then[`Dlet l p e`,`st1`] assume_tac)>>
         fs[infer_d_def,success_eqns,init_state_def])
      >-
        (fs[namespaceTheory.alist_to_ns_def]>>
        Cases_on`x`>>fs[namespaceTheory.nsLookupMod_def])
      >-
        (* Soundness direction:
           Because the type system chooses a MGU (assumption 4),
           we show that the inferred (and generalised) type is sound, and so the type system
           must generalise it
        *)
        (rw[env_rel_sound_def]>>
        simp[lookup_var_def]>>
        fs[nsLookup_alist_to_ns_some,tenv_add_tvs_def,ALOOKUP_MAP]>>
        imp_res_tac generalise_list_length>>fs[]>>
        imp_res_tac ALOOKUP_MEM>>
        rfs[MEM_ZIP,convert_env_def,ALOOKUP_MAP,EL_MAP]>>
        simp[ALOOKUP_ALL_DISTINCT_EL]>>
        imp_res_tac infer_p_constraints>>
        `pure_add_constraints st'.subst [t',t''] s` by fs[pure_add_constraints_def]>>
        `type_e tenv (bind_tvar num_tvs' Empty) e (convert_t (t_walkstar last_sub t'))` by
          (match_mp_tac (infer_e_sound|>CONJUNCT1)>>
          asm_exists_tac>>simp[]>>
          fs[sub_completion_def]>>
          (* constraints arising from patterns and the unification step *)
          qexists_tac`ts'++[t',t'']++ec1`>>
          CONJ_TAC>-
            (* TODO: Maybe this should be renamed to env_rel_sound_empty_to...*)
            (match_mp_tac env_rel_e_sound_empty_to >>fs[]>>
            match_mp_tac env_rel_sound_extend_tvs>>
            fs[t_wfs_def])>>
          fs[pure_add_constraints_append,init_infer_state_def,t_wfs_def]>>
          rw[]>- metis_tac[]>>
          imp_res_tac infer_p_next_uvar_mono>>
          fs[SUBSET_DEF])>>
        `type_p num_tvs' tenv p (convert_t (t_walkstar last_sub t'')) (convert_env last_sub new_bindings)` by
          (match_mp_tac(infer_p_sound|>CONJUNCT1)>>
          asm_exists_tac>>fs[ienv_ok_def,typeSoundInvariantsTheory.tenv_ok_def]>>
          fs[env_rel_sound_def,sub_completion_def]>>
          qexists_tac`[t',t'']++ec1`>>rw[pure_add_constraints_append]
          >-
            (imp_res_tac infer_e_wfs>>
            fs[init_infer_state_def,t_wfs_def])>>
          metis_tac[])>>
        `t_walkstar last_sub t' = t_walkstar last_sub t''` by
          (match_mp_tac sub_completion_apply>>
          map_every qexists_tac [`num_tvs'`,`st'.next_uvar`,`s`,`ec1`]>>
          fs[]>>
          match_mp_tac t_unify_apply>>
          qexists_tac `st'.subst`>>
          fs[]>>
          imp_res_tac infer_e_wfs>>
          imp_res_tac infer_p_wfs>>
          fs[init_infer_state_def,t_wfs_def])>>
        pop_assum SUBST_ALL_TAC>>
        first_x_assum drule>> simp[]>>
        impl_tac >- (
          drule (GEN_ALL (CONJUNCT1 infer_p_inf_set_tids))
          \\ drule (CONJUNCT1 infer_e_wfs)
          \\ simp[] \\ strip_tac
          \\ simp[convert_env_def, EVERY_MAP, UNCURRY]
          \\ qmatch_goalsub_abbrev_tac`set_tids_subset tids`
          \\ disch_then(qspec_then`tids`mp_tac)
          \\ impl_tac >- (
            fs[Abbr`tids`,start_type_id_prim_tids_count]
            \\ drule(GEN_ALL(CONJUNCT1 infer_e_inf_set_tids))
            \\ srw_tac[DNF_ss][]
            \\ first_x_assum match_mp_tac
            \\ simp[start_type_id_prim_tids_count] )
          \\ fs[EVERY_MEM]
          \\ rpt strip_tac
          \\ simp[set_tids_subset_def]
          \\ simp[GSYM inf_set_tids_unconvert]
          \\ DEP_REWRITE_TAC[check_t_empty_unconvert_convert_id]
          \\ conj_tac
          >- (
            fs[sub_completion_def]
            \\ qexists_tac`num_tvs'`
            \\ irule (CONJUNCT1 check_t_walkstar)
            \\ fs[]
            \\ fs[UNCURRY,MEM_MAP,PULL_EXISTS]
            \\ res_tac
            \\ imp_res_tac check_t_more2 \\ fs[]
            \\ pop_assum(qspec_then`num_tvs'`assume_tac)
            \\ irule (CONJUNCT1 check_t_more5)
            \\ HINT_EXISTS_TAC \\ fs[] )
          \\ match_mp_tac (SIMP_RULE(srw_ss())[inf_set_tids_subset_def]t_walkstar_set_tids)
          \\ fs[inf_set_tids_subset_def]
          \\ first_x_assum match_mp_tac
          \\ conj_tac >- ( EVAL_TAC \\ fs[start_type_id_def] )
          \\ irule (CONJUNCT1 t_unify_set_tids)
          \\ goal_assum(first_assum o mp_then (Pat`t_unify`)mp_tac)
          \\ `prim_tids T tids` by metis_tac[start_type_id_prim_tids_count]
          \\ imp_res_tac infer_e_inf_set_tids \\ fs[]
          \\ imp_res_tac infer_p_inf_set_tids \\ fs[]
          \\ imp_res_tac infer_e_wfs \\ fs[]
          \\ imp_res_tac infer_p_wfs \\ fs[]) >>
        fs[LIST_REL_EL_EQN]>>
        strip_tac>>
        pop_assum (qspec_then`n` assume_tac)>>
        rfs[MAP_MAP_o,EL_MAP,convert_env_def]>>
        pairarg_tac>>fs[]>>
        pairarg_tac>>fs[]>>
        imp_res_tac tscheme_inst_to_approx>>
        rveq>>fs[]>>
        `check_t num_tvs' {} (t_walkstar last_sub t''')` by
          (qspec_then`last_sub`drule(Q.GENL[`s`,`uvars`,`n`](CONJUNCT1 check_t_less))>> rw[] \\
          fs[sub_completion_def, PULL_FORALL]>>
          pop_assum(qspecl_then [`count st'.next_uvar`,`num_tvs'`,`t'''`] mp_tac)>>
          impl_tac>-
            (fs[EVERY_EL,EL_MAP]>>
            qpat_x_assum`!n''. n'' < A ⇒ B` (qspec_then `n` assume_tac)>>rfs[])>>
          rfs[]>>
          `count st'.next_uvar ∩ COMPL(FDOM last_sub) = {}` by
            (fs[EXTENSION]>>
            rw[]>>
            Cases_on`x < st'.next_uvar`>>fs[]>>
            fs[SUBSET_DEF])>>
          fs[])>>
        `check_t tvs {} (t_walkstar s' t''')` by
          (fs[EVERY_EL]>>
          first_x_assum(qspec_then`n`kall_tac)>>
          first_x_assum(qspec_then`n`assume_tac)>>rfs[])>>
        metis_tac[check_t_to_check_freevars,check_t_empty_unconvert_convert_id])
      >-
        (* completeness direction -- use the substitution from infer_e_complete *)
        (simp[env_rel_complete_def,lookup_var_def]>>
        ntac 4 strip_tac>>
        fs[nsLookup_alist_to_ns_some,tenv_add_tvs_def,ALOOKUP_MAP,convert_env_def]>>
        imp_res_tac ALOOKUP_MEM>>
        fs[MEM_EL]>>
        pop_assum (assume_tac o SYM)>>
        qpat_abbrev_tac`lss = ZIP(A,B)`>>
        `x' = FST (EL n lss) ∧ ALL_DISTINCT (MAP FST lss) ∧ n < LENGTH lss` by
          (rw[Abbr`lss`]
          >-
            (simp[EL_ZIP,EL_MAP]>>
            metis_tac[FST])
          >>
            simp[MAP_ZIP])>>
        simp[ALOOKUP_ALL_DISTINCT_EL]>>
        ntac 3 (pop_assum kall_tac)>>
        fs[Abbr`lss`,EL_ZIP,EL_MAP]>>
        rw[]
        >-
          (fs[EVERY_EL]>>
          first_x_assum(qspec_then`n` kall_tac)>>
          first_x_assum(qspec_then`n` assume_tac)>>
          rfs[]>>
          metis_tac[check_t_to_check_freevars])
        >>
          (* copied proof from soundness dir *)
          `check_t num_tvs' {} (t_walkstar last_sub t''')` by
            (qspec_then`last_sub`drule(Q.GENL[`s`,`uvars`,`n`](CONJUNCT1 check_t_less))>> rw[] \\
            fs[sub_completion_def, PULL_FORALL]>>
            pop_assum(qspecl_then [`count st'.next_uvar`,`num_tvs'`,`t'''`] mp_tac)>>
            impl_tac>-
              (fs[EVERY_EL,EL_MAP]>>
              qpat_x_assum`!n''. n'' < A ⇒ B` (qspec_then `n` assume_tac)>>rfs[])>>
            `count st'.next_uvar ∩ COMPL(FDOM last_sub) = {}` by
              (fs[EXTENSION]>>
              rw[]>>
              Cases_on`x < st'.next_uvar`>>fs[]>>
              fs[SUBSET_DEF])>>
            fs[])>>
          `t_walkstar last_sub t''' = unconvert_t (convert_t (t_walkstar last_sub t'''))` by
            metis_tac[check_t_empty_unconvert_convert_id]>>
          pop_assum SUBST1_TAC>>
          match_mp_tac tscheme_inst_to_approx>>
          fs[tscheme_inst_def]>>
          (* rest of this follows the same proof as infer_d_sound *)
          imp_res_tac generalise_subst>>
          fs[]>>
          (* Rewrite last_sub back into an infer_subst *)
          `t_walkstar last_sub t''' = infer_subst s'' (t_walkstar s t''')` by
             (fs[MAP_MAP_o,LIST_EQ_REWRITE,EL_MAP,infer_subst_FEMPTY]>>
             pop_assum(qspec_then`n` assume_tac)>>
             rfs[])>>
          fs[sub_completion_def]>>
          Q.ISPECL_THEN [`tvs`,`s'`] mp_tac (GEN_ALL generalise_subst_exist)>>
          impl_tac>-
            (fs[]>>
            metis_tac[pure_add_constraints_success])>>
          rw[]>>
          (* This produces the appropriate substitution mentioned above *)
          pop_assum (qspecl_then[`MAP (t_walkstar s) (MAP SND new_bindings)`,`[]`,`FEMPTY`,`num_tvs'`,`s''`,`MAP (t_walkstar last_sub) (MAP SND new_bindings)`] mp_tac)>>
          fs[]>>
          impl_keep_tac
          >-
            (fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
            fs[GSYM FORALL_AND_THM]>>fs[GSYM IMP_CONJ_THM]>>
            ntac 2 strip_tac>>
            CONJ_ASM2_TAC
            >-
              metis_tac[check_t_t_vars]
            >>
            match_mp_tac t_walkstar_check>> fs[]>>
            last_x_assum (qspec_then `y'` kall_tac)>>
            last_x_assum (qspec_then `y'` assume_tac)>>rfs[]>>
            fs[UNCURRY]>>
            reverse CONJ_TAC>-
             (match_mp_tac (check_t_more5|>CONJUNCT1|>MP_CANON)>>
             HINT_EXISTS_TAC>>
             fs[])>>
            match_mp_tac (check_s_more3 |> MP_CANON)>>
            qexists_tac `count st'.next_uvar`>>
            fs[])
          >>
          rw[]>>
          (* Pick the substitution, except turn it into deBruijn vars *)
          qexists_tac`MAP convert_t subst'`>>fs[]>>
          `check_t 0 (count st'.next_uvar) t'''` by
            (fs[EVERY_EL]>>
            rpt(first_x_assum (qspec_then `n` assume_tac))>>
            rfs[EL_MAP])>>
          `check_t (LENGTH subst') {} (infer_subst s'' (t_walkstar s t'''))` by
            (qpat_x_assum `A = infer_subst B C` sym_sub_tac>>
            Q.SPECL_THEN [`count (st'.next_uvar)`,`last_sub`,`LENGTH subst'`,`t'''`] mp_tac (check_t_less |> CONJUNCT1 |>GEN_ALL)>>
            simp[])>>
          CONJ_ASM1_TAC>-
            metis_tac[check_t_to_check_freevars]>>
          CONJ_TAC>-
            (fs[EVERY_MAP,EVERY_MEM]>>
            metis_tac[check_t_to_check_freevars])>>
          imp_res_tac deBruijn_subst_convert>>
          pop_assum(qspec_then `subst'`assume_tac)>>fs[]>>
          AP_TERM_TAC>>
          Q.ISPECL_THEN [`s'`,`s''`,`subst'`,`_`,`count st'.next_uvar`] mp_tac (GEN_ALL infer_deBruijn_subst_infer_subst_walkstar)>>
          impl_tac>-
            (fs[SUBSET_DEF]>>
            rw[]>>
            fs[IN_FRANGE]>>
            metis_tac[pure_add_constraints_wfs])>>
          rw[]>>
          pop_assum kall_tac>>
          pop_assum(qspec_then `t_walkstar s t'''` mp_tac)>>
          impl_tac>-
            (imp_res_tac infer_p_check_t>>
            fs[EXTENSION,SUBSET_DEF]>>
            fs[MEM_MAP,PULL_EXISTS]>>
            imp_res_tac ALOOKUP_MEM>>
            fs[FORALL_PROD,EXISTS_PROD]>>
            CONJ_TAC>-
              metis_tac[MEM_EL]>>
            reverse CONJ_TAC>-
              metis_tac[MEM_EL]
            >>
            fs[EVERY_MAP,MAP_MAP_o,EVERY_MEM,UNCURRY]>>
            match_mp_tac t_walkstar_check>>fs[]>>
            CONJ_TAC>-
              (match_mp_tac check_s_more5>>
              asm_exists_tac>>fs[])
              >>
              imp_res_tac check_t_more5>>
              fs[SUBSET_DEF,EXTENSION])
          >>
          rw[]>>
          metis_tac[pure_add_constraints_wfs,t_walkstar_SUBMAP,pure_add_constraints_success]))
    >-
      (imp_res_tac infer_e_next_id_const>>
      imp_res_tac infer_p_next_id_const>>
      imp_res_tac infer_p_bindings>>
      pop_assum(qspec_then`[]` mp_tac)>>
      fs[init_infer_state_def]>>metis_tac[]))
  >- ( (* Let mono *)
    rw [infer_d_def, success_eqns,init_state_def] >>
    `ienv_ok {} ienv` by fs [env_rel_def] >>
    qpat_x_assum`env_rel A B` mp_tac>>
    simp[Once env_rel_def] >> strip_tac>>
    drule (GEN_ALL infer_pe_complete) >>
    disch_then (qspec_then`0` mp_tac)>>
    fs[bind_tvar_def]>>
    rpt (disch_then drule) >>
    disch_then (qspecl_then [`st1`,`<| loc := SOME l; err := ienv.inf_t |>`] mp_tac) >>
    rw [] >>
    simp[success_eqns]>>
    pairarg_tac >> fs[success_eqns]>>
    imp_res_tac infer_p_bindings>>
    pop_assum(qspec_then`[]` assume_tac)>>
    fs[]>>
    imp_res_tac type_pe_determ_canon_infer_e>>
    qmatch_asmsub_abbrev_tac`generalise_list 0 0 FEMPTY ls`>>
    `EVERY (check_t 0 {}) ls` by
      (fs[Abbr`ls`,EVERY_MEM,MAP_MAP_o,o_DEF]>>fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS,FORALL_PROD]>>
      metis_tac[])>>
    drule (el 2 (CONJUNCTS generalise_no_uvars))>>
    rw[Abbr`ls`]>>fs[]
    >- (
      qmatch_abbrev_tac `env_rel tenv' ienv'` >>
      `ienv' = tenv_to_ienv tenv'`
        by (
          unabbrev_all_tac >>
          rw [tenv_to_ienv_def, tenv_add_tvs_def, MAP_MAP_o, combinTheory.o_DEF, convert_env_def, LAMBDA_PROD] >>
          rw [namespaceTheory.alist_to_ns_def] >>
          fs [ELIM_UNCURRY] >>
          irule LIST_EQ >>
          rw [EL_MAP, EL_ZIP] >>
          fs [EVERY_MEM, MEM_EL] >>
          `check_t 0 {} (t_walkstar s' (SND (EL x new_bindings)))` by metis_tac [] >>
          drule check_t_empty_unconvert_convert_id >>
          rw [] >>
          fs [sub_completion_def] >>
          imp_res_tac pure_add_constraints_success>>
          imp_res_tac t_walkstar_SUBMAP >>
          metis_tac [t_walkstar_no_vars]) >>
      rw [] >>
      irule env_rel_tenv_to_ienv >>
      unabbrev_all_tac >>
      rw [typeSoundInvariantsTheory.tenv_ok_def]
      )
    >- (
      imp_res_tac infer_e_next_id_const>>
      imp_res_tac infer_p_next_id_const>>
      fs[init_infer_state_def]))
  >- ( (* Letrec *)
    qmatch_goalsub_rename_tac`Dletrec locs funs` >>
    rw[infer_d_def,success_eqns,init_state_def]>>
    `ienv_ok {} ienv` by fs[env_rel_def]>>
    drule (GEN_ALL infer_funs_complete)>>
    disch_then (qspecl_then [`tvs`, `tenv`, `st1`, `<| loc := SOME locs; err := ienv.inf_t |>`, `funs`, `bindings`] mp_tac) >>
    fs[]>>
    impl_tac>-
      fs[env_rel_def]>>
    rw[]>>fs[LENGTH_COUNT_LIST]>>
    imp_res_tac type_funs_distinct >> fs[FST_triple] >>
    imp_res_tac type_funs_MAP_FST >>
    imp_res_tac type_funs_Tfn>>
    simp[PULL_EXISTS]>>
    CONV_TAC (RESORT_EXISTS_CONV (sort_vars ["st''''"]))>>
    qexists_tac`st'`>>simp[]>>
    pairarg_tac>>fs[success_eqns] >>
    drule (GEN_ALL generalise_complete)>>
    disch_then(qspecl_then[`st'.next_uvar`,`Tbool_num`,`count st'.next_id`]mp_tac o
               CONV_RULE(RESORT_FORALL_CONV(List.rev)))>>fs[]>>
    `t_wfs st.subst` by
      (imp_res_tac infer_e_wfs>>
      fs[])>>
    impl_keep_tac>-
      (rfs[]>>rw[]
      >-
        metis_tac[pure_add_constraints_success]
      >>
        imp_res_tac infer_e_next_uvar_mono>>fs[EVERY_MAP,EVERY_MEM,MEM_COUNT_LIST,check_t_def])>>
    fs[env_rel_def]>> strip_tac>>
    `LENGTH funs_ts = LENGTH funs` by metis_tac[LENGTH_MAP]>>
    `MAP (t_walkstar last_sub) funs_ts = ts'` by
      (simp[LIST_EQ_REWRITE,LENGTH_COUNT_LIST,EL_MAP,EL_COUNT_LIST]>>rw[]>>
      match_mp_tac sub_completion_apply>>
      qpat_assum`t_wfs st'.subst` (match_exists_tac o concl)>>fs[]>>
      rw[GSYM PULL_EXISTS]
      >-
        (imp_res_tac pure_add_constraints_apply>>
        qpat_x_assum`MAP _ _ = _` mp_tac>>
        simp[Once LIST_EQ_REWRITE]>>
        disch_then(qspec_then`x` assume_tac)>>rfs[LENGTH_COUNT_LIST,EL_MAP,EL_ZIP,EL_COUNT_LIST])
      >>
        metis_tac[])>>
    simp[GSYM CONJ_ASSOC]
    \\ conj_tac
    >- (
      imp_res_tac (CONJUNCT1 infer_d_check)
      \\ pop_assum (mp_tac o (CONV_RULE (RESORT_FORALL_CONV (sort_vars ["d"]))))
      \\ disch_then(qspec_then`Dletrec locs funs` mp_tac)
      \\ simp[Once infer_d_def,success_eqns,Once init_state_def,LENGTH_COUNT_LIST,PULL_EXISTS]
      \\ disch_then match_mp_tac
      \\ asm_exists_tac \\ simp[]
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ simp[success_eqns] )
    \\ conj_tac >-
      (fs[namespaceTheory.alist_to_ns_def]>>
      Cases_on`x`>>fs[namespaceTheory.nsLookupMod_def])
    \\ imp_res_tac infer_e_next_id_const \\ fs[init_infer_state_def]
    \\ conj_tac >-
      (* Soundness direction:
         Because the type system chooses a MGU (assumption 4),
         we show that the inferred (and generalised) type is sound, and so the type system
         must generalise it
      *)
      (
      rw[env_rel_sound_def]>>
      simp[lookup_var_def]>>
      fs[nsLookup_alist_to_ns_some,tenv_add_tvs_def,ALOOKUP_MAP]>>
      imp_res_tac ALOOKUP_MEM>>
      rfs[MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,MEM_ZIP]>>
      rw[]>>pairarg_tac>>fs[]>>rw[]>>
      `n < LENGTH bindings ∧ f = FST (EL n bindings) ` by
        (qpat_x_assum`MAP FST A = B` mp_tac>>
        simp[Once LIST_EQ_REWRITE,EL_MAP]>>
        metis_tac[EL_MAP,LENGTH_MAP,FST])>>
      pop_assum SUBST1_TAC>>
      simp[ALOOKUP_ALL_DISTINCT_EL]>>
      drule (infer_e_sound |> CONJUNCTS |> el 4)>>
      disch_then(qspecl_then[`tenv`,`bind_var_list 0 (MAP2 (λ(x,y,z) t. (x,(convert_t ∘ t_walkstar last_sub) t)) funs funs_ts) (bind_tvar num_gen Empty)`] mp_tac)>>
      qmatch_asmsub_abbrev_tac`pure_add_constraints st.subst c1 st'.subst`>>
      disch_then(qspecl_then[`c1++ec1`,`last_sub`] mp_tac)>>
      impl_tac>-
        (fs[sub_completion_def]>>rw[]
        >-
          (fs[ienv_ok_def,ienv_val_ok_def]>>
          match_mp_tac nsAll_nsAppend>>
          rw[]
          >-
           (match_mp_tac nsAll_alist_to_ns>>
           fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,MEM_ZIP,LENGTH_COUNT_LIST]>>rw[]>>
           simp[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST,check_t_def])
          >>
            irule nsAll_mono>>
            HINT_EXISTS_TAC>>
            simp[FORALL_PROD]>>
            metis_tac[check_t_more])
        >-
          (drule (env_rel_e_sound_letrec_merge0|>INST_TYPE [alpha|->``:tvarN``,beta|->``:exp``])>>
          simp[MAP2_MAP,LENGTH_COUNT_LIST]>>
          disch_then(qspecl_then[`funs`,`ienv`,`tenv`,`bind_tvar num_gen Empty`,`0n`] mp_tac)>>
          fs[sub_completion_def,SUBSET_DEF]>>impl_tac
          >-
            (rw[]
            >-
              (imp_res_tac infer_e_next_uvar_mono>>fs[])
            >>
              match_mp_tac env_rel_sound_extend_tvs>>fs[]>>
              match_mp_tac env_rel_e_sound_empty_to>>fs[])
          >>
          qpat_abbrev_tac `A = MAP _ _`>>
          qpat_abbrev_tac `ls1 = MAP _ _`>>
          qpat_abbrev_tac `ls2 = MAP _ _`>>
          `ls1=ls2` by
            (unabbrev_all_tac>>
            fs[LIST_EQ_REWRITE,LENGTH_ZIP,LENGTH_COUNT_LIST,EL_MAP,EL_ZIP]>>rw[]>>
            pairarg_tac>>fs[EL_COUNT_LIST])>>
          fs[])
        >>
          metis_tac[pure_add_constraints_append])>>
      strip_tac>>fs[LIST_REL_EL_EQN]>>
      first_x_assum drule >> simp[]
      \\ impl_tac
      >- (
        fs[EVERY_MAP,MAP2_MAP,UNCURRY,set_tids_subset_def]
        \\ simp[EVERY_MEM,MEM_ZIP,FORALL_PROD,PULL_EXISTS]
        \\ simp[GSYM inf_set_tids_unconvert]
        \\ rw[]
        \\ DEP_REWRITE_TAC[check_t_empty_unconvert_convert_id]
        \\ qpat_x_assum`MAP _ _ = MAP _ _`mp_tac
        \\ simp[LIST_EQ_REWRITE, EL_MAP, LENGTH_COUNT_LIST, EL_COUNT_LIST]
        \\ strip_tac
        \\ fs[sub_completion_def]
        \\ conj_tac
        >- (
          qexists_tac`num_gen`
          \\ first_x_assum irule
          \\ fs[SUBSET_DEF]
          \\ first_x_assum irule
          \\ fs[]
          \\ imp_res_tac infer_e_next_uvar_mono \\ fs[] )
        \\ match_mp_tac (SIMP_RULE(srw_ss())[inf_set_tids_subset_def]t_walkstar_set_tids)
        \\ fs[inf_set_tids_def]
        \\ first_x_assum irule
        \\ fs[]
        \\ conj_tac >- (fs[start_type_id_def,Tbool_num_def])
        \\ irule pure_add_constraints_set_tids
        \\ goal_assum(first_assum o mp_then (Pos last) mp_tac)
        \\ simp[Abbr`c1`, MAP_ZIP, LENGTH_COUNT_LIST]
        \\ simp[EVERY_MAP, inf_set_tids_subset_def, inf_set_tids_def]
        \\ drule (GEN_ALL(last(CONJUNCTS infer_e_inf_set_tids)))
        \\ fs[]
        \\ disch_then match_mp_tac
        \\ fs[start_type_id_prim_tids_count]
        \\ fs[inf_set_tids_ienv_def]
        \\ match_mp_tac nsAll_nsAppend
        \\ fs[]
        \\ match_mp_tac nsAll_alist_to_ns
        \\ fs[EVERY_MAP, UNCURRY, every_zip_snd, LENGTH_COUNT_LIST]
        \\ fs[inf_set_tids_subset_def, inf_set_tids_def])
      \\ strip_tac
      \\ pop_assum (qspec_then`n` assume_tac)>>
      rfs[MAP2_MAP,EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST]>>
      pairarg_tac>>fs[]>>
      pairarg_tac>>fs[]>>
      `t_walkstar last_sub (Infer_Tuvar n) = t_walkstar last_sub t'` by
        (fs[Once LIST_EQ_REWRITE]>>
        first_x_assum(qspec_then`n` kall_tac)>>
        first_x_assum(qspec_then`n` assume_tac)>>
        rfs[EL_MAP,EL_COUNT_LIST,EL_ZIP]>>fs[])>>
      imp_res_tac ALOOKUP_ALL_DISTINCT_EL >>res_tac>>fs[]>>
      Cases_on`EL n bindings`>>fs[]>>
      imp_res_tac tscheme_inst_to_approx>>
      rveq>>fs[]>>
      `check_t num_gen {} (t_walkstar last_sub t')` by
        (imp_res_tac infer_e_next_uvar_mono>>
        rpt (qpat_x_assum`A=B` sym_sub_tac)>>
        fs[sub_completion_def]>>
        fs[SUBSET_DEF])>>
      metis_tac[check_t_to_check_freevars,check_t_empty_unconvert_convert_id])
    \\ (
      simp[env_rel_complete_def,lookup_var_def,PULL_EXISTS]>>
      fs[nsLookup_alist_to_ns_some,tenv_add_tvs_def,ALOOKUP_MAP,
         convert_env_def,MAP2_MAP,LENGTH_COUNT_LIST,PULL_EXISTS]>>
      ntac 3 strip_tac >>
      imp_res_tac ALOOKUP_MEM>>
      fs[MEM_EL]>>
      pop_assum (assume_tac o SYM)>>
      qpat_abbrev_tac`lss = MAP f (ZIP(A,B))`>>
      `MAP FST lss = MAP FST funs` by
        (fs[Abbr`lss`]>>simp[Once LIST_EQ_REWRITE,LENGTH_COUNT_LIST]>>rw[]
        >-
          metis_tac[LENGTH_MAP]
        >>
          qpat_x_assum`A = MAP FST bindings` sym_sub_tac>>
          fs[EL_MAP,LENGTH_COUNT_LIST,EL_ZIP,EL_COUNT_LIST]>>pairarg_tac>>fs[])>>
      `x' = FST (EL n lss) ∧ ALL_DISTINCT (MAP FST lss) ∧ n < LENGTH lss` by
        (
        CONJ_ASM2_TAC>>rw[Abbr`lss`]
        >-
          (fs[EL_MAP,LENGTH_ZIP,LENGTH_COUNT_LIST,EL_ZIP,LENGTH_COUNT_LIST,EL_COUNT_LIST]>>
          pairarg_tac>>fs[]>>
          qpat_x_assum`MAP FST funs = A` mp_tac>>
          simp[Once LIST_EQ_REWRITE]>>rw[]>>rfs[EL_MAP,LENGTH_MAP]>>
          metis_tac[FST])
        >>
          simp[LENGTH_COUNT_LIST]>>metis_tac[LENGTH_MAP])>>
      simp[ALOOKUP_ALL_DISTINCT_EL]>>
      fs[Abbr`lss`,EL_ZIP,EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST]>>
      pairarg_tac \\ fs[] \\
      rw[]
      \\ res_tac \\ fs[]
      \\ asm_exists_tac \\ fs[]
      >>
        `check_t num_gen {} (t_walkstar last_sub (Infer_Tuvar n))` by
          (fs[sub_completion_def]>>
          imp_res_tac infer_e_next_uvar_mono>>fs[SUBSET_DEF])>>
        imp_res_tac check_t_empty_unconvert_convert_id>>
        pop_assum (SUBST1_TAC o SYM)>>
        match_mp_tac tscheme_inst_to_approx>>
        fs[tscheme_inst_def]>>
        (* rest of this follows the same proof as infer_d_sound *)
        imp_res_tac generalise_subst>>
        fs[]>>
        (* Rewrite last_sub back into an infer_subst *)
        `t_walkstar last_sub (Infer_Tuvar n) = infer_subst s' (t_walkstar st'.subst (Infer_Tuvar n))` by
           (fs[MAP_MAP_o,LIST_EQ_REWRITE,EL_MAP,infer_subst_FEMPTY]>>
           pop_assum(qspec_then`n` assume_tac)>>
           rfs[EL_COUNT_LIST])>>
        fs[sub_completion_def]>>
        qmatch_asmsub_abbrev_tac`generalise_list _ _ _ (MAP _ uvars)`>>
        Q.ISPECL_THEN [`tvs`,`s`] mp_tac (GEN_ALL generalise_subst_exist)>>
        impl_tac>-
          (fs[]>>
          metis_tac[pure_add_constraints_success])>>
        rw[]>>
        (* This produces the appropriate substitution mentioned above *)
        pop_assum (qspecl_then[`MAP (t_walkstar st'.subst) uvars`,`[]`,`FEMPTY`,`num_gen`,`s'`,`MAP (t_walkstar last_sub) uvars`] mp_tac)>>
        fs[]>>
        impl_keep_tac
        >-
          (fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
          fs[GSYM FORALL_AND_THM]>>fs[GSYM IMP_CONJ_THM]>>
          ntac 2 strip_tac>>
          CONJ_ASM2_TAC
          >-
            metis_tac[check_t_t_vars]
          >>
          match_mp_tac t_walkstar_check>> fs[]>>
          last_x_assum (qspec_then `y` assume_tac)>>rfs[]>>
          reverse CONJ_TAC>-
           (match_mp_tac (check_t_more5|>CONJUNCT1|>MP_CANON)>>
           HINT_EXISTS_TAC>>
           fs[])>>
          match_mp_tac (check_s_more3 |> MP_CANON)>>
          qexists_tac `count st'.next_uvar`>>
          fs[])
        >>
        rw[]>>
        (* Pick the substitution, except turn it into deBruijn vars *)
        qexists_tac`MAP convert_t subst'`>>fs[]>>
        CONJ_ASM1_TAC>-
          metis_tac[check_t_to_check_freevars]>>
        CONJ_TAC>-
          (fs[EVERY_MAP,EVERY_MEM]>>
          metis_tac[check_t_to_check_freevars])>>
        imp_res_tac deBruijn_subst_convert>>
        pop_assum(qspec_then `subst'`assume_tac)>>fs[]>>
        `Tapp [t1; t2] Tfn_num = convert_t (t_walkstar s (Infer_Tuvar n))` by
          (qpat_x_assum`MAP SND A = B` mp_tac>>
          simp[Once LIST_EQ_REWRITE]>>
          rw[]>>
          pop_assum (qspec_then`n` assume_tac)>>rfs[EL_MAP]>>
          AP_TERM_TAC >>
          `pure_add_constraints st.subst ((ZIP(uvars,funs_ts))++constr) s` by
            metis_tac[pure_add_constraints_append,pure_add_constraints_success]>>
          imp_res_tac pure_add_constraints_apply>>
          fs[Abbr`uvars`,MAP_APPEND,MAP_ZIP,Once LIST_EQ_REWRITE,LENGTH_COUNT_LIST]>>
          first_x_assum(qspec_then`n` kall_tac)>>
          first_x_assum(qspec_then`n` assume_tac)>>
          rfs[EL_APPEND1,EL_MAP,EL_ZIP,EL_COUNT_LIST,MAP_COUNT_LIST])>>
        pop_assum SUBST_ALL_TAC>>
        AP_TERM_TAC>>
        Q.ISPECL_THEN [`s`,`s'`,`subst'`,`_`,`count st'.next_uvar`] mp_tac (GEN_ALL infer_deBruijn_subst_infer_subst_walkstar)>>
        impl_tac>-
          (fs[SUBSET_DEF]>>
          rw[]>>
          fs[IN_FRANGE]>>
          metis_tac[pure_add_constraints_wfs])>>
        rw[]>>
        pop_assum kall_tac>>
        pop_assum(qspec_then `t_walkstar st'.subst (Infer_Tuvar n)` mp_tac)>>
        impl_tac>-
          (fs[Abbr`uvars`,EVERY_MEM,MEM_MAP,MEM_COUNT_LIST,PULL_EXISTS,SUBSET_DEF]>>
          metis_tac[])
        >>
        rw[]>>
        metis_tac[pure_add_constraints_wfs,t_walkstar_SUBMAP,pure_add_constraints_success])
    )
  >- ( (* Dtype *)
    rw [infer_d_def, success_eqns,n_fresh_id_def]
    >- (
      qmatch_abbrev_tac `env_rel tenv' ienv'` >>
      `ienv' = tenv_to_ienv tenv'`
        by (
          unabbrev_all_tac >>
          rw [tenv_to_ienv_def] >>
          fs [env_rel_def, env_rel_complete_def]) >>
      rw [] >>
      irule env_rel_tenv_to_ienv >>
      fs[env_rel_def])>>
    fs[env_rel_def,env_rel_sound_def])
  >- ( (* Dtabbrev *)
    `tenv.t = ienv.inf_t` by fs [env_rel_def, env_rel_complete_def] >>
    fs [] >>
    rw [infer_d_def,success_eqns, type_name_check_subst_comp_thm] >>
    qmatch_abbrev_tac `env_rel tenv' ienv'` >>
    `ienv' = tenv_to_ienv tenv'`
      by (
        unabbrev_all_tac >>
        rw [tenv_to_ienv_def] >>
        fs [env_rel_def, env_rel_complete_def]) >>
    rw [] >>
    irule env_rel_tenv_to_ienv >>
    fs[env_rel_def])
  >- ( (* Dexn *)
    `tenv.t = ienv.inf_t` by fs [env_rel_def, env_rel_complete_def] >>
    fs [] >>
    rw [infer_d_def, success_eqns,type_name_check_subst_comp_thm] >>
    qmatch_abbrev_tac `env_rel tenv' ienv'` >>
    `ienv' = tenv_to_ienv tenv'`
      by (
        unabbrev_all_tac >>
        rw [tenv_to_ienv_def] >>
        fs [env_rel_def, env_rel_complete_def] >>
        metis_tac []) >>
    rw [] >>
    irule env_rel_tenv_to_ienv >>
    fs[env_rel_def])
  >- ( (* Dmod*)
    rw[infer_d_def,success_eqns]>>
    first_x_assum drule>>
    disch_then drule>>
    disch_then (qspec_then`st1` assume_tac)>>rfs[]>>
    match_mp_tac env_rel_lift>>
    fs[])
  >- ( (* Dlocal *)
    rw[infer_d_def,success_eqns]>>
    rpt (first_x_assum drule >> rw [])>>
    str_assums [ISPEC ``infer_st_next_id`` ap_lemma]>>
    fs[]>>
    first_x_assum match_mp_tac>>
    fs[env_rel_extend]>>
    irule inf_set_tids_extend_dec_ienv>>
    imp_res_tac (CONJUNCT2 infer_d_inf_set_tids)>>
    rfs[]>>
    goal_assum(first_assum o mp_then Any mp_tac)>>
    fs[]
  )
  >-
    rw[infer_d_def,success_eqns]
  >>
    rw[infer_d_def,success_eqns]>>
    last_x_assum drule>>disch_then drule>>
    disch_then (qspec_then`st1` assume_tac)>>rfs[]>>
    qpat_x_assum`_ = _` (assume_tac o SYM)>>
    fs[]>>last_x_assum drule>>
    drule env_rel_extend>>
    last_x_assum assume_tac>>
    disch_then drule>> strip_tac>>
    disch_then drule>> simp[]
    \\ impl_tac >- (
      drule(CONJUNCT1 infer_d_inf_set_tids)
      \\ fs[]
      \\ strip_tac
      \\ irule inf_set_tids_extend_dec_ienv
      \\ fs[]
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ fs[])
    \\ rw[] >>
    fs[]>>
    metis_tac[env_rel_extend]
QED

Theorem infer_ds_complete:
   type_ds T tenv ds ids tenv' ∧
   env_rel tenv ienv ∧
   (* do you need both of these? *)
   inf_set_tids_ienv (count st1.next_id) ienv ∧
   set_tids_tenv (count st1.next_id) tenv ∧
   DISJOINT ids (count st1.next_id) ∧
   start_type_id ≤ st1.next_id
   ⇒
   ∃g mapped_tenv' ienv' st2.
     infer_ds ienv ds st1 = (Success ienv', st2) ∧
     (*
     BIJ g (count st1.next_id ∪ count ids) (count (st1.next_id + ids)) ∧
     *)
     tenv_equiv (remap_tenv g tenv') mapped_tenv' ∧
     env_rel mapped_tenv' ienv' ∧
     st2.next_id = st1.next_id + CARD ids
Proof
  rw[]
  \\ drule(CONJUNCT2 type_d_type_d_canon)
  \\ simp[]
  \\ disch_then drule
  \\ disch_then(qspecl_then[`I`,`st1.next_id`]mp_tac)
  \\ simp[start_type_id_prim_tids_count, good_remap_def]
  \\ disch_then (qspec_then`tenv`mp_tac)
  (*
  \\ impl_tac
  >- (
    fs[]
    \\ fs[inf_set_tids_ienv_def, set_tids_tenv_def]
    \\ fs[inf_set_tids_subset_def, set_tids_subset_def]
    \\ fs[inf_set_tids_unconvert]
    \\ fs[env_rel_def, env_rel_complete_def] \\ rfs[]
    \\ fs[namespaceTheory.nsAll_def,lookup_var_def,lookup_varE_def,FORALL_PROD]
    \\ rw[]
    \\ res_tac
    \\ res_tac
    \\ fs[tscheme_approx_def] \\ rw[]
    \\ fs[t_walkstar_FEMPTY]
    \\ drule (CONJUNCT1 infer_deBruijn_subst_id2)
    \\ simp[GSYM inf_set_tids_unconvert]
    \\ first_x_assum match_mp_tac
    \\ qexists_tac`i` \\ simp[]
    \\ pop_assum(qspec_then`GENLIST Infer_Tvar_db p_1`mp_tac)
    \\ simp[infer_deBruijn_subst_id2]
    \\ ... )
  *)
  \\ rw[]
  \\ drule (CONJUNCT2 infer_d_complete_canon)
  \\ disch_then drule \\ fs[]
  \\ disch_then(qspec_then`st1`mp_tac)
  \\ simp[]
  (*
  \\ impl_tac
  >- (
    fs[inf_set_tids_ienv_def, set_tids_tenv_def]
    \\ fs[inf_set_tids_subset_def, set_tids_subset_def]
    \\ fs[inf_set_tids_unconvert]
    \\ fs[env_rel_def, env_rel_complete_def] \\ rfs[]
    \\ fs[namespaceTheory.nsAll_def,lookup_var_def,lookup_varE_def,FORALL_PROD]
    \\ rw[]
  *)
  \\ rw[] \\ asm_exists_tac \\ fs[]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  (*
  \\ imp_res_tac DISJOINT_SYM
  \\ drule (GEN_ALL BIJ_extend_bij) \\ fs[]*)
QED

(*
Theorem check_specs_complete:
   !mn tenvT specs decls tenv.
    type_specs mn tenvT specs decls tenv ⇒
    ∀st1 extra_idecls extra_ienv.
      tenv_abbrev_ok tenvT ⇒
      ?st2 idecls new_ienv.
        decls = convert_decls idecls ∧
        env_rel tenv new_ienv ∧
        check_specs mn tenvT extra_idecls extra_ienv specs st1 =
          (Success (append_decls idecls extra_idecls,extend_dec_ienv new_ienv extra_ienv), st2)
Proof
  ho_match_mp_tac type_specs_ind >>
  rw [check_specs_def, success_eqns]
  >- (
    fs [extend_dec_ienv_def, empty_decls_def, convert_decls_def, append_decls_def,
        inf_decls_component_equality, inf_env_component_equality] >>
    qexists_tac `empty_inf_decls` >>
    qexists_tac `<| inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsEmpty |>` >>
    rw [empty_inf_decls_def])
  >- (
    drule (CONJUNCT1 check_freevars_t_to_freevars) >>
    disch_then (qspec_then `st1` strip_assume_tac) >>
    rw [PULL_EXISTS] >>
    qho_match_abbrev_tac
      `?st2 idecls new_ienv. _ idecls ∧ _ new_ienv ∧ check_specs _ _ _ (extra_ienv with inf_v := nsBind name new extra_ienv.inf_v) _ _ = (Success (_ idecls new_ienv), st2)` >>
    simp [] >>
    first_x_assum (qspecl_then [`st'`, `extra_idecls`, `(extra_ienv with inf_v := nsBind name new extra_ienv.inf_v)`] mp_tac) >>
    rw [] >>
    rw [] >>
    qexists_tac `idecls` >>
    qexists_tac `extend_dec_ienv new_ienv <| inf_v := nsSing name new; inf_c := nsEmpty; inf_t := nsEmpty |>` >>
    unabbrev_all_tac >>
    rw []
    >- (
      irule env_rel_extend >>
      rw [] >>
      irule env_rel_binding >>
      rw [] >>
      irule check_freevars_type_name_subst >>
      rw [] >>
      metis_tac [t_to_freevars_check])
    >- (
      rw [extend_dec_ienv_def] >>
      simp_tac std_ss [GSYM nsAppend_assoc, nsAppend_nsSing]))
 >- (
    qho_match_abbrev_tac
      `?st2 idecls new_ienv. _ idecls ∧ _ new_ienv ∧ _ ∧ check_specs _ _ eid'
         <| inf_v := _ ; inf_c := nsAppend new_ctors _; inf_t := nsAppend new_t _ |> _ _ = (Success (_ idecls new_ienv), st2)` >>
    simp [] >>
    `tenv_abbrev_ok new_t`
      by (
        unabbrev_all_tac >>
        simp [typeSoundInvariantsTheory.tenv_abbrev_ok_def] >>
        irule nsAll_alist_to_ns >>
        simp [EVERY_MAP, LAMBDA_PROD, check_freevars_def, EVERY_MEM] >>
        REWRITE_TAC [ELIM_UNCURRY]) >>
    `tenv_abbrev_ok (nsAppend new_t tenvT)` by metis_tac [tenv_abbrev_ok_merge] >>
    fs [] >>
    first_x_assum (qspecl_then [`st1`, `eid'`,
       `<|inf_v := extra_ienv.inf_v; inf_c := nsAppend new_ctors extra_ienv.inf_c; inf_t := nsAppend new_t extra_ienv.inf_t|>`] mp_tac) >>
    rw [] >>
    rw [] >>
    qexists_tac `append_decls idecls <| inf_defined_types := MAP (λ(tvs,tn,ctors). mk_id mn tn) td;
              inf_defined_mods := []; inf_defined_exns := []|>` >>
    qexists_tac `extend_dec_ienv new_ienv <| inf_v := nsEmpty; inf_c := new_ctors; inf_t := new_t |>` >>
    unabbrev_all_tac >>
    rw []
    >- (
      simp [convert_append_decls] >>
      rw [convert_decls_def])
    >- (
      irule env_rel_extend >>
      rw [] >>
      qmatch_abbrev_tac `env_rel tenv' ienv'` >>
      `ienv_ok {} ienv'`
        by (
          unabbrev_all_tac >>
          simp [ienv_ok_def, ienv_val_ok_def] >>
          irule check_ctor_tenv_ok >>
          simp []) >>
      `tenv' = ienv_to_tenv ienv'`
        by (
          unabbrev_all_tac >>
          rw [ienv_to_tenv_def]) >>
      rw [] >>
      irule env_rel_ienv_to_tenv >>
      unabbrev_all_tac >>
      rw [ienv_ok_def])
    >- rw [append_decls_def]
    >- rw [extend_dec_ienv_def])
  >- (
    qho_match_abbrev_tac
      `?st2 idecls new_ienv. _ idecls ∧ _ new_ienv ∧ check_specs _ _ eid' (_ with inf_t := nsBind name new_t _) _ _ = (Success (_ idecls new_ienv), st2)` >>
    simp [] >>
    `tenv_abbrev_ok (nsBind name new_t tenvT)`
      by (
        fs [typeSoundInvariantsTheory.tenv_abbrev_ok_def] >>
        irule nsAll_nsBind >>
        unabbrev_all_tac >>
        rw [] >>
        metis_tac [typeSoundInvariantsTheory.tenv_abbrev_ok_def, check_freevars_type_name_subst]) >>
    first_x_assum (qspecl_then [`st1`, `eid'`, `extra_ienv with inf_t := nsBind name new_t extra_ienv.inf_t`] mp_tac) >>
    rw [] >>
    rw [] >>
    qexists_tac `idecls` >>
    qexists_tac `extend_dec_ienv new_ienv <| inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsSing tn (tvs,type_name_subst tenvT t)|>` >>
    unabbrev_all_tac >>
    rw []
    >- (
      irule env_rel_extend >>
      simp [] >>
      qmatch_abbrev_tac `env_rel tenv' ienv'` >>
      `tenv' = ienv_to_tenv ienv'`
        by (
          unabbrev_all_tac >>
          rw [ienv_to_tenv_def]) >>
      simp [] >>
      irule env_rel_ienv_to_tenv >>
      unabbrev_all_tac >>
      rw [ienv_ok_def, ienv_val_ok_def, typeSoundInvariantsTheory.tenv_abbrev_ok_def] >>
      metis_tac [check_freevars_type_name_subst]) >>
    simp [extend_dec_ienv_def] >>
    simp_tac std_ss [nsAppend_nsSing, GSYM nsAppend_assoc])
  >- (
    fs [] >>
    qho_match_abbrev_tac
      `?st2 idecls new_ienv. _ idecls ∧ _ new_ienv ∧ check_specs _ _ eid' (extra_ienv with inf_c := nsBind name new_c extra_ienv.inf_c) _ _ = (Success (_ idecls new_ienv), st2)` >>
    simp [] >>
    first_x_assum (qspecl_then [`st1`, `eid'`, `extra_ienv with inf_c := nsBind name new_c extra_ienv.inf_c`] mp_tac) >>
    rw [] >>
    rw [] >>
    qexists_tac `append_decls idecls <| inf_defined_types := []; inf_defined_mods := []; inf_defined_exns := [mk_id mn name]|>` >>
    qexists_tac `extend_dec_ienv new_ienv <| inf_v := nsEmpty; inf_c := nsSing name ([],MAP (type_name_subst tenvT) ts, TypeExn (mk_id mn name)); inf_t := nsEmpty |>` >>
    unabbrev_all_tac >>
    simp [convert_append_decls] >>
    rw [convert_decls_def]
    >- (
      irule env_rel_extend >>
      simp [] >>
      qmatch_abbrev_tac `env_rel tenv' ienv'` >>
      `tenv' = ienv_to_tenv ienv'`
        by (
          unabbrev_all_tac >>
          rw [ienv_to_tenv_def]) >>
      simp [] >>
      irule env_rel_ienv_to_tenv >>
      unabbrev_all_tac >>
      rw [ienv_ok_def, ienv_val_ok_def, typeSoundInvariantsTheory.tenv_ctor_ok_def] >>
      fs [EVERY_MEM, EVERY_MAP, check_exn_tenv_def] >>
      metis_tac [check_freevars_type_name_subst])
    >- simp [append_decls_def]
    >- (
      simp [extend_dec_ienv_def] >>
      simp_tac std_ss [nsAppend_nsSing, GSYM nsAppend_assoc] >>
      metis_tac []))
  >- (
    qho_match_abbrev_tac
      `?st2 idecls new_ienv. _ idecls ∧ _ new_ienv ∧ check_specs _ _ eid' (_ with inf_t := nsBind name new_t _) _ _ = (Success (_ idecls new_ienv), st2)` >>
    simp [] >>
    `tenv_abbrev_ok (nsBind name new_t tenvT)`
      by (
        fs [typeSoundInvariantsTheory.tenv_abbrev_ok_def] >>
        irule nsAll_nsBind >>
        unabbrev_all_tac >>
        rw [check_freevars_def, EVERY_MAP, EVERY_MEM]) >>
    first_x_assum (qspecl_then [`st1`, `eid'`, `extra_ienv with inf_t := nsBind name new_t extra_ienv.inf_t`] mp_tac) >>
    rw [] >>
    rw [] >>
    qexists_tac `append_decls idecls <| inf_defined_types := [mk_id mn name]; inf_defined_mods := []; inf_defined_exns := []|>` >>
    qexists_tac `extend_dec_ienv new_ienv <| inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsSing tn (tvs,Tapp (MAP Tvar tvs) (TC_name (mk_id mn tn)))|>` >>
    unabbrev_all_tac >>
    rw []
    >- (
      simp [convert_append_decls] >>
      simp [convert_decls_def])
    >- (
      irule env_rel_extend >>
      simp [] >>
      qmatch_abbrev_tac `env_rel tenv' ienv'` >>
      `tenv' = ienv_to_tenv ienv'`
        by (
          unabbrev_all_tac >>
          rw [ienv_to_tenv_def]) >>
      simp [] >>
      irule env_rel_ienv_to_tenv >>
      unabbrev_all_tac >>
      rw [ienv_ok_def, ienv_val_ok_def, typeSoundInvariantsTheory.tenv_abbrev_ok_def] >>
      rw [check_freevars_def, EVERY_MAP, EVERY_MEM])
    >- simp [append_decls_def]
    >- (
      simp [extend_dec_ienv_def] >>
      simp_tac std_ss [nsAppend_nsSing, GSYM nsAppend_assoc]))
QED

val n_fresh_uvar_rw = Q.prove(`
  ∀n st.n_fresh_uvar n st = (Success (GENLIST (λi.Infer_Tuvar(i+st.next_uvar)) n), st with next_uvar := st.next_uvar + n)`,
  Induct>>simp[Once n_fresh_uvar_def]
  >-
    (EVAL_TAC>>fs[infer_st_component_equality])
  >>
    rw[st_ex_bind_def,fresh_uvar_def,st_ex_return_def,ADD1]>>
    simp[GENLIST_CONS,GSYM ADD1]>>
    AP_THM_TAC>>AP_TERM_TAC>>fs[o_DEF]>>
    fs[FUN_EQ_THM])

val t_walkstar_infer_deBruijn_subst = Q.prove(`
 t_wfs s ∧
 LENGTH ls = tvs ∧
 EVERY (check_t y {}) ls ∧
 (∀n. n < tvs ⇒ t_walkstar s (Infer_Tuvar n) = EL n ls)
 ⇒
  ((∀t.
  check_t tvs {} t
  ⇒
  t_walkstar s (infer_deBruijn_subst ls t) =
  t_walkstar s (infer_deBruijn_subst (GENLIST Infer_Tuvar tvs) t)) ∧
  (∀ts.
  EVERY (check_t tvs {}) ts
  ⇒
  MAP ((t_walkstar s) o (infer_deBruijn_subst ls)) ts =
  MAP ((t_walkstar s) o (infer_deBruijn_subst (GENLIST Infer_Tuvar tvs))) ts))`,
  strip_tac>>ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[check_t_def,infer_deBruijn_subst_def]>>
  fs[EVERY_MEM,MEM_EL]
  >-
    metis_tac[t_walkstar_no_vars]
  >>
    fs[t_walkstar_eqn1,MAP_MAP_o,MAP_EQ_f]);

val infer_deBruijn_subst_check_t = Q.prove(`
  EVERY (check_t tvs {}) ls
  ⇒
  (∀t.
  check_t (LENGTH ls) {} t
  ⇒
  check_t tvs {} (infer_deBruijn_subst ls t)) ∧
  (∀ts.
  EVERY (check_t (LENGTH ls) {}) ts
  ⇒
  EVERY (check_t tvs {}) (MAP (infer_deBruijn_subst ls) ts))`,
  strip_tac>>ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[check_t_def,infer_deBruijn_subst_def]>>
  fs[EVERY_MEM,MEM_EL]>>
  metis_tac[]);

Theorem check_tscheme_inst_complete:
   !tvs_spec t_spec tvs_impl t_impl id.
    check_t tvs_impl {} t_impl ∧
    check_t tvs_spec {} t_spec ∧
    tscheme_approx 0 FEMPTY (tvs_spec,t_spec) (tvs_impl,t_impl) ⇒
    check_tscheme_inst id (tvs_spec,t_spec) (tvs_impl,t_impl)
Proof
  rw [tscheme_approx_def, check_tscheme_inst_def] >>
  fs [t_walkstar_FEMPTY] >>
  simp [st_ex_bind_def, init_state_def, init_infer_state_def, st_ex_return_def,
        add_constraint_def] >>
  simp[n_fresh_uvar_rw]>>
  imp_res_tac infer_deBruijn_subst_id2>>
  ntac 2 (pop_assum kall_tac)>>
  first_x_assum(qspec_then`GENLIST Infer_Tvar_db tvs_spec` mp_tac)>>
  qpat_abbrev_tac`ls = MAP (infer_deBruijn_subst A) B`>>
  rw[]>>fs[]>>rfs[]>>
  `EVERY (check_t tvs_spec {}) ls` by
    (fs[Abbr`ls`,EVERY_MAP,MAP_MAP_o,EVERY_MEM]>>
    rw[]>>
    match_mp_tac (infer_deBruijn_subst_check_t|>UNDISCH|>CONJUNCT1|>DISCH_ALL|>GEN_ALL|>(SIMP_RULE (srw_ss()) [PULL_FORALL,AND_IMP_INTRO]))>>
    CONJ_TAC>-
      fs[EVERY_GENLIST,check_t_def]>>
    fs[LENGTH_GENLIST])>>
  Q.ISPECL_THEN [`init_infer_state`,`[]:(infer_t,infer_t) alist`,`FEMPTY:num|->infer_t`,`MAP convert_t ls`,`tvs_spec`] mp_tac extend_multi_props>>
  impl_tac>-
    (fs[init_infer_state_def,pure_add_constraints_def]>>
    fs[t_wfs_def,EVERY_MAP,EVERY_MEM,Abbr`ls`]>>
    metis_tac[check_t_to_check_freevars])>>
  BasicProvers.LET_ELIM_TAC>>fs[init_infer_state_def]>>
  `targs = ls` by
    (fs[Abbr`targs`,MAP_MAP_o,MAP_EQ_ID]>>
    metis_tac[check_t_empty_unconvert_convert_id,EVERY_MEM])>>fs[]>>
  imp_res_tac (t_walkstar_infer_deBruijn_subst)>>
  ntac 3 (pop_assum kall_tac)>>
  pop_assum mp_tac>>
  ntac 8 (pop_assum kall_tac)>>
  simp[]>>
  disch_then (qspec_then`t_impl`mp_tac)>>
  qmatch_goalsub_abbrev_tac`t_unify A B C`>>
  strip_tac>>
  `∃D. t_unify A B C = SOME D` by
    (match_mp_tac (GEN_ALL eqs_t_unify)>>
    qexists_tac`s'`>>
    fs[markerTheory.Abbrev_def]>>
    rpt var_eq_tac>>
    fs[t_walkstar_FEMPTY,ETA_AX,t_wfs_def])>>
  fs[]
QED

Theorem check_weak_ienv_complete:
   !tenv_impl tenv_spec ienv_impl ienv_spec.
    weak_tenv tenv_impl tenv_spec ∧
    env_rel tenv_impl ienv_impl ∧
    env_rel tenv_spec ienv_spec
    ⇒
    check_weak_ienv ienv_impl ienv_spec
Proof
  rw [weak_tenv_def, check_weak_ienv_def, GSYM nsSub_compute_thm]
  >- (
    fs [namespaceTheory.nsSub_def, env_rel_def, env_rel_sound_def,
        lookup_var_def, env_rel_complete_def] >>
    rw [] >>
    rpt (first_x_assum drule) >>
    rw [] >>
    rpt (first_x_assum drule) >>
    rw [] >>
    fs [tscheme_inst2_def] >>
    PairCases_on `v2` >>
    rpt (first_x_assum drule) >>
    rw [] >>
    fs [] >>
    match_mp_tac check_tscheme_inst_complete>>
    fs[ienv_ok_def,ienv_val_ok_def]>>
    imp_res_tac nsLookup_nsAll>>
    rfs[]>>
    metis_tac [tscheme_approx_trans, tscheme_inst_to_approx]) >>
  fs [env_rel_def, env_rel_sound_def]
QED

Theorem check_weak_decls_complete:
   !idecls1 idecls2.
    weak_decls (convert_decls idecls1) (convert_decls idecls2)
    ⇒
    check_weak_decls idecls1 idecls2
Proof
  rw [weak_decls_def, check_weak_decls_def, convert_decls_def, SUBSET_DEF,
      list_subset_def, list_set_eq_def] >>
  fs [EVERY_MEM]
QED
*)

val _ = export_theory ();
