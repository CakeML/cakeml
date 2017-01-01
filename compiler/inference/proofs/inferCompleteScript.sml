open preamble;
open libTheory typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory;
open astPropsTheory;
open typeSysPropsTheory;
open inferPropsTheory;

open infer_eSoundTheory;
open infer_eCompleteTheory;
open type_eDetermTheory envRelTheory namespacePropsTheory;

val _ = new_theory "inferComplete";

fun Abbrev_wrap eqth =
    EQ_MP (SYM (Thm.SPEC (concl eqth) markerTheory.Abbrev_def)) eqth

fun ABB l r =
 CHOOSE_THEN (fn th => SUBST_ALL_TAC th THEN ASSUME_TAC (Abbrev_wrap(SYM th)))
             (Thm.EXISTS(mk_exists(l, mk_eq(r, l)), r) (Thm.REFL r));

fun ABBREV_TAC eq = let val (l,r) = dest_eq eq in ABB l r end;

local
   val match_var_or_const = ref true
in
   val () = Feedback.register_btrace
               ("pat_abbrev_tac2: match var/const", match_var_or_const)

   fun pat_abbrev_tac2 fv_set eq (g as (asl, w)) =
      let
         val (l, r) = dest_eq eq
         val l' = variant (HOLset.listItems (FVL [r] fv_set)) l
         fun finder (_,tm) = can (match_term r) tm
         fun k tm = (match_term r tm,tm)
         val result = bvk_find_term finder k w
      in
         case result of
            NONE => raise ERR "pat_abbrev_tac2" "No matching term found"
          | SOME ((_,tys),t) => ABB (inst tys l') t g
      end
end

fun qpat_abbrev_tac2 q (gl as (asl,w)) =
 let val fv_set = FVL (w::asl) empty_tmset
     val ctxt = HOLset.listItems fv_set
     val eq = Parse.parse_in_context ctxt q
 in
   pat_abbrev_tac2 fv_set eq
 end gl;

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

val env_rel_binding_lemma = Q.store_thm ("env_rel_binding_lemma",
  `!t fvs fvs' subst.
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
                NONE => Infer_Tapp [] TC_int
              | SOME t => Infer_Tvar_db t)) (LENGTH fvs))
      (infer_type_subst (ZIP (fvs,GENLIST (λx. Infer_Tvar_db x) (LENGTH fvs))) t)`,
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
      >>asm_simp_tac std_ss [] >>
      rw [infer_deBruijn_subst_def]))
  >- (
    irule LIST_EQ >>
    rw [EL_MAP] >>
    fs [EVERY_EL]));

val env_rel_binding_lemma2 = Q.store_thm ("env_rel_binding_lemma2",
  `!t fvs fvs' subst.
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
      (infer_type_subst (ZIP (fvs',MAP Infer_Tvar_db (COUNT_LIST (LENGTH fvs')))) t)`,
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
    fs [EVERY_EL]));

val unconvert_type_subst = Q.store_thm ("unconvert_type_subst",
  `(!t subst fvs.
     check_freevars 0 fvs t ∧ set fvs ⊆ set (MAP FST subst) ⇒
     unconvert_t (type_subst (alist_to_fmap subst) t) =
     infer_type_subst (MAP (\(x,y). (x, unconvert_t y)) subst) t) ∧
  (!ts subst fvs.
     EVERY (check_freevars 0 fvs) ts ∧ set fvs ⊆ set (MAP FST subst) ⇒
     MAP (unconvert_t o type_subst (alist_to_fmap subst)) ts =
     MAP (infer_type_subst (MAP (\(x,y). (x, unconvert_t y)) subst)) ts)`,
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
 metis_tac []);

val env_rel_binding = Q.store_thm ("env_rel_binding",
  `!fvs t fvs' name.
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
      inf_t := nsEmpty|>`,
  rw [env_rel_def]
  >- (
    rw [ienv_ok_def, ienv_val_ok_def] >>
    Cases_on `nub fvs' = []` >>
    fs []
    >- (
      simp [COUNT_LIST_def] >>
      irule (CONJUNCT1 infer_type_subst_empty_check) >>
      fs [nub_eq_nil] >>
      metis_tac [t_to_freevars_check])
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
    metis_tac [check_freevars_more, nub_set, SUBSET_DEF]));

val env_rel_complete_bind = Q.prove(`
  env_rel_complete FEMPTY ienv tenv Empty ⇒
  env_rel_complete FEMPTY ienv tenv (bind_tvar tvs Empty)`,
  fs[env_rel_complete_def,bind_tvar_def,lookup_var_def,lookup_varE_def,tveLookup_def]>>rw[]>>every_case_tac>>fs[]>>
  res_tac>>fs[]>> TRY(metis_tac[])>>
  match_mp_tac tscheme_approx_weakening>>asm_exists_tac>>fs[t_wfs_def]);

(* TODO: This seems like it must have been proven elsewhere *)
val generalise_list_length = Q.prove(`
  ∀a b c d e f g.
  generalise_list a b c d = (e,f,g) ⇒ LENGTH g = LENGTH d`,
  Induct_on`d`>>fs[generalise_def]>>rw[]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  res_tac>>fs[]>>rveq>>fs[])

val infer_d_complete = Q.store_thm ("infer_d_complete",
  `!mn decls tenv ienv d st1 decls' tenv' idecls.
    type_d T mn decls tenv d decls' tenv' ∧
    env_rel tenv ienv ∧
    decls = convert_decls idecls
    ⇒
    ?idecls' ienv' st2.
      decls' = convert_decls idecls' ∧
      env_rel tenv' ienv' ∧
      infer_d mn idecls ienv d st1 = (Success (idecls',ienv'), st2)`,
  rw [] >>
  drule type_d_tenv_ok_helper >>
  rw [] >>
  fs [type_d_cases]
  >- ( (* Let poly *)
    rw [infer_d_def, success_eqns] >>
    `ienv_ok {} ienv` by fs [env_rel_def] >>
    `env_rel_complete FEMPTY ienv tenv Empty` by fs [env_rel_def] >>
    imp_res_tac env_rel_complete_bind>>
    pop_assum (qspec_then`tvs` assume_tac)>>
    drule (GEN_ALL infer_pe_complete) >>
    rpt (disch_then drule) >>
    rw [] >>
    qexists_tac `empty_inf_decls` >>
    simp [init_state_def, success_eqns] >>
    pairarg_tac >>
    fs[success_eqns]>>
    CONJ_TAC >-
    simp [empty_decls_def, convert_decls_def, empty_inf_decls_def]>>
    CONJ_ASM2_TAC
    >-
      (* the subcompletion of s corresponding to generalise_list *)
      (drule generalise_complete>>
      disch_then(qspec_then`st'.next_uvar` mp_tac)>>fs[]>>
      impl_keep_tac>-
        (`t_wfs init_infer_state.subst` by (EVAL_TAC>>fs[t_wfs_def])>>
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
        (*Recover the check_t property directly from infer_d_check*)
        (imp_res_tac infer_d_check >>
        pop_assum (mp_tac o (CONV_RULE (RESORT_FORALL_CONV (sort_vars ["d"]))))>>
        disch_then(qspec_then`Dlet p e` assume_tac)>>fs[infer_d_def,success_eqns,init_state_def]>>
        rfs[guard_def]>>
        `MAP FST new_bindings = pat_bindings p []` by
          (imp_res_tac type_p_pat_bindings>>
          fs[convert_env_def,MAP_MAP_o]>>
          pop_assum sym_sub_tac>>
          simp[MAP_EQ_f]>>fs[FORALL_PROD])>>
        fs[]>>rfs[success_eqns])
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
        res_tac>>
        pop_assum kall_tac>>
        fs[LIST_REL_EL_EQN]>>
        pop_assum (qspec_then`n` assume_tac)>>
        rfs[MAP_MAP_o,EL_MAP,convert_env_def]>>
        pairarg_tac>>fs[]>>
        pairarg_tac>>fs[]>>
        imp_res_tac tscheme_inst_to_approx>>
        rveq>>fs[]>>
        `check_t num_tvs' {} (t_walkstar last_sub t''')` by
          (imp_res_tac (CONJUNCT1 check_t_less)>>
          pop_assum kall_tac>>
          fs[sub_completion_def]>>
          pop_assum(qspecl_then [`count st'.next_uvar`,`t'''`] mp_tac)>>
          impl_tac>-
            (fs[EVERY_EL,EL_MAP]>>
            qpat_x_assum`!n''. n'' < A ⇒ B` (qspec_then `n` assume_tac)>>rfs[])>>
          disch_then(qspec_then`num_tvs'` assume_tac)>>rfs[]>>
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
            (imp_res_tac (CONJUNCT1 check_t_less)>>
            pop_assum kall_tac>>
            fs[sub_completion_def]>>
            pop_assum(qspecl_then [`count st'.next_uvar`,`t'''`] mp_tac)>>
            impl_tac>-
              (fs[EVERY_EL,EL_MAP]>>
              qpat_x_assum`!n''. n'' < A ⇒ B` (qspec_then `n` assume_tac)>>rfs[])>>
            disch_then(qspec_then`num_tvs'` assume_tac)>>rfs[]>>
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
      (imp_res_tac infer_p_bindings>>
      pop_assum(qspec_then`[]` mp_tac)>>
      fs[]>>metis_tac[]))
  >- ( (* Let mono *)
    rw [infer_d_def, success_eqns] >>
    `ienv_ok {} ienv` by fs [env_rel_def] >>
    qpat_x_assum`env_rel A B` mp_tac>>
    simp[Once env_rel_def] >> strip_tac>>
    drule (GEN_ALL infer_pe_complete) >>
    disch_then (qspec_then`0` mp_tac)>>
    fs[bind_tvar_def]>>
    rpt (disch_then drule) >>
    rw [] >>
    qexists_tac `empty_inf_decls` >>
    simp [init_state_def, success_eqns] >>
    pairarg_tac >> fs[success_eqns]>>
    imp_res_tac infer_p_bindings>>
    pop_assum(qspec_then`[]` assume_tac)>>
    fs[]>> imp_res_tac type_pe_determ_infer_e>>
    qmatch_asmsub_abbrev_tac`generalise_list 0 0 FEMPTY ls`>>
    `EVERY (check_t 0 {}) ls` by
      (fs[Abbr`ls`,EVERY_MEM,MAP_MAP_o,o_DEF]>>fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS,FORALL_PROD]>>
      metis_tac[])>>
    drule (el 2 (CONJUNCTS generalise_no_uvars))>>
    rw[Abbr`ls`]>>fs[]
    >- simp [empty_decls_def, convert_decls_def, empty_inf_decls_def]
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
      rw [typeSoundInvariantsTheory.tenv_ok_def]))
  >- ( (* Letrec *)
    rw[infer_d_def,success_eqns,init_state_def]>>
    `ienv_ok {} ienv` by fs[env_rel_def]>>
    drule infer_funs_complete>>
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
    pairarg_tac>>fs[success_eqns]>>rw[]
    >-
      (EVAL_TAC>>fs[])
    >-
      (drule generalise_complete>>
      disch_then(qspec_then`st'.next_uvar` mp_tac)>>fs[]>>
      `t_wfs init_infer_state.subst` by (EVAL_TAC>>fs[t_wfs_def])>>
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
          pop_assum kall_tac>>
          pop_assum mp_tac>>
          simp[Once LIST_EQ_REWRITE]>>
          disch_then(qspec_then`x` assume_tac)>>rfs[LENGTH_COUNT_LIST,EL_MAP,EL_ZIP,EL_COUNT_LIST])
        >>
          metis_tac[])>>
      rw[]
      >-
        (*Recover the check_t property directly from infer_d_check*)
        (imp_res_tac infer_d_check >>
        pop_assum (mp_tac o (CONV_RULE (RESORT_FORALL_CONV (sort_vars ["d"]))))>>
        disch_then(qspec_then`Dletrec funs` assume_tac)>>fs[infer_d_def,success_eqns,init_state_def]>>
        rfs[guard_def,LENGTH_COUNT_LIST]>>
        pop_assum match_mp_tac>>
        CONV_TAC (RESORT_EXISTS_CONV (sort_vars ["st''''"]))>>
        qexists_tac`st'`>>fs[success_eqns]>>
        metis_tac[LENGTH_MAP])
      >-
        (fs[namespaceTheory.alist_to_ns_def]>>
        Cases_on`x`>>fs[namespaceTheory.nsLookupMod_def])
      >-
        (* Soundness direction:
           Because the type system chooses a MGU (assumption 4),
           we show that the inferred (and generalised) type is sound, and so the type system
           must generalise it
        *)
        (
        rw[env_rel_sound_def]>>
        simp[lookup_var_def]>>
        fs[nsLookup_alist_to_ns_some,tenv_add_tvs_def,ALOOKUP_MAP]>>
        imp_res_tac generalise_list_length>>fs[]>>
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
        res_tac>> pop_assum kall_tac>>
        pop_assum (qspec_then`n` assume_tac)>>
        fs[MAP2_MAP]>>
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
      >-
        cheat)
    >-
      metis_tac[LENGTH_MAP])
  >- ( (* Dtype *)
    rw [infer_d_def, success_eqns]
    >- rw [convert_decls_def, empty_inf_decls_def]
    >- (
      qmatch_abbrev_tac `env_rel tenv' ienv'` >>
      `ienv' = tenv_to_ienv tenv'`
        by (
          unabbrev_all_tac >>
          rw [tenv_to_ienv_def] >>
          fs [env_rel_def, env_rel_complete_def]) >>
      rw [] >>
      irule env_rel_tenv_to_ienv >>
      first_x_assum irule >>
      fs [env_rel_def])
    >- fs [env_rel_def, env_rel_sound_def]
    >- (
      rw [EVERY_MAP, EVERY_MEM] >>
      pairarg_tac >>
      rw [] >>
      fs [convert_decls_def, DISJOINT_DEF, EXTENSION] >>
      first_x_assum (qspec_then `mk_id mn tn` mp_tac) >>
      rw [MEM_MAP] >>
      first_x_assum (qspec_then `(tvs,tn,ctors)` mp_tac) >>
      rw []))
  >- ( (* Abbrev *)
    rw [infer_d_def, success_eqns, empty_decls_def, convert_decls_def, empty_inf_decls_def]
    >- (
      qmatch_abbrev_tac `env_rel tenv' ienv'` >>
      `ienv' = tenv_to_ienv tenv'`
        by (
          unabbrev_all_tac >>
          rw [tenv_to_ienv_def] >>
          fs [env_rel_def, env_rel_complete_def]) >>
      rw [] >>
      irule env_rel_tenv_to_ienv >>
      first_x_assum irule >>
      fs [env_rel_def])
    >- fs [env_rel_def, env_rel_sound_def])
  >- ( (* Exn *)
    rw [infer_d_def, success_eqns, empty_decls_def, convert_decls_def, empty_inf_decls_def]
    >- (
      qmatch_abbrev_tac `env_rel tenv' ienv'` >>
      `ienv' = tenv_to_ienv tenv'`
        by (
          unabbrev_all_tac >>
          rw [tenv_to_ienv_def] >>
          fs [env_rel_def, env_rel_complete_def] >>
          metis_tac []) >>
      rw [] >>
      irule env_rel_tenv_to_ienv >>
      first_x_assum irule >>
      fs [env_rel_def])
    >- fs [env_rel_def, env_rel_sound_def]
    >- fs [convert_decls_def, DISJOINT_DEF, EXTENSION]));

val infer_ds_complete = Q.store_thm ("infer_ds_complete",
  `!x mn decls tenv ds decls' tenv'.
    type_ds x mn decls tenv ds decls' tenv' ⇒
    !idecls ienv st1.
      env_rel tenv ienv ∧
      decls = convert_decls idecls ∧
      x = T
      ⇒
      ?idecls' ienv' st2.
        decls' = convert_decls idecls' ∧
        env_rel tenv' ienv' ∧
        infer_ds mn idecls ienv ds st1 = (Success (idecls',ienv'), st2)`,
  ho_match_mp_tac type_ds_ind >>
  rw [infer_ds_def, success_eqns]
  >- simp [empty_decls_def, empty_inf_decls_def, convert_decls_def] >>
  drule infer_d_complete >>
  disch_then drule >>
  disch_then (qspecl_then [`st1`, `idecls`] mp_tac) >>
  rw [] >>
  rw [] >>
  fs [GSYM convert_append_decls] >>
  first_x_assum (qspec_then `append_decls idecls' idecls` mp_tac) >>
  simp [] >>
  disch_then (qspecl_then [`extend_dec_ienv ienv' ienv`, `st2`] mp_tac) >>
  impl_tac
  >- (irule env_rel_extend >> simp []) >>
  rw [] >>
  rw [success_eqns, convert_append_decls] >>
  metis_tac [env_rel_extend]);

val check_specs_complete = Q.store_thm ("check_specs_complete",
  `!mn tenvT specs decls tenv.
    type_specs mn tenvT specs decls tenv ⇒
    ∀st1 extra_idecls extra_ienv.
      tenv_abbrev_ok tenvT ⇒
      ?st2 idecls new_ienv.
        decls = convert_decls idecls ∧
        env_rel tenv new_ienv ∧
        check_specs mn tenvT extra_idecls extra_ienv specs st1 =
          (Success (append_decls idecls extra_idecls,extend_dec_ienv new_ienv extra_ienv), st2)`,
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
      `?st2 idecls new_ienv. _ idecls ∧ _ new_ienv ∧ _ ∧ check_specs _ _ eid' <| inf_v := _ ; inf_c := nsAppend new_ctors _; inf_t := nsAppend new_t _ |> _ _ = (Success (_ idecls new_ienv), st2)` >>
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
    first_x_assum (qspecl_then [`st1`, `eid'`, `<|inf_v := extra_ienv.inf_v; inf_c := nsAppend new_ctors extra_ienv.inf_c; inf_t := nsAppend new_t extra_ienv.inf_t|>`] mp_tac) >>
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
      simp_tac std_ss [nsAppend_nsSing, GSYM nsAppend_assoc])));

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

(* TODO: I hope this is true *)
val check_tscheme_inst_complete = Q.store_thm ("check_tscheme_inst_complete",
  `!tvs_spec t_spec tvs_impl t_impl id.
    check_t tvs_impl {} t_impl ∧
    check_t tvs_spec {} t_spec ∧
    tscheme_approx 0 FEMPTY (tvs_spec,t_spec) (tvs_impl,t_impl) ⇒
    check_tscheme_inst id (tvs_spec,t_spec) (tvs_impl,t_impl)`,
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
  fs[]);

val check_weak_ienv_complete = Q.store_thm ("check_weak_ienv_complete",
  `!tenv_impl tenv_spec ienv_impl ienv_spec.
    weak_tenv tenv_impl tenv_spec ∧
    env_rel tenv_impl ienv_impl ∧
    env_rel tenv_spec ienv_spec
    ⇒
    check_weak_ienv ienv_impl ienv_spec`,
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
  fs [env_rel_def, env_rel_sound_def]);

val check_weak_decls_complete = Q.store_thm ("check_weak_decls_complete",
  `!idecls1 idecls2.
    weak_decls (convert_decls idecls1) (convert_decls idecls2)
    ⇒
    check_weak_decls idecls1 idecls2`,
  rw [weak_decls_def, check_weak_decls_def, convert_decls_def, SUBSET_DEF,
      list_subset_def, list_set_eq_def] >>
  fs [EVERY_MEM]);

val infer_top_complete = Q.store_thm ("infer_top_complete",
  `!decls tenv ienv top st1 decls' tenv' idecls.
    type_top T decls tenv top decls' tenv' ∧
    env_rel tenv ienv ∧
    decls = convert_decls idecls
    ⇒
    ?idecls' ienv' st2.
      decls' = convert_decls idecls' ∧
      env_rel tenv' ienv' ∧
      infer_top idecls ienv top st1 = (Success (idecls',ienv'), st2)`,
  rw [type_top_cases] >>
  rw [infer_top_def, success_eqns]
  >- (
    drule infer_d_complete >>
    disch_then drule >>
    disch_then (qspecl_then [`st1`, `idecls`] mp_tac) >>
    rw [] >>
    qexists_tac `idecls'` >>
    rw [success_eqns]) >>
  drule infer_ds_complete >>
  disch_then drule >>
  disch_then (qspecl_then [`idecls`, `st1`] mp_tac) >>
  rw [] >>
  rw [success_eqns] >>
  fs [check_signature_def, typeSystemTheory.check_signature_cases,
      success_eqns]
  >- (
    fs [union_decls_def, convert_decls_def, GSYM INSERT_SING_UNION] >>
    metis_tac [env_rel_lift])
  >- (
    drule (INST_TYPE [``:'a`` |-> ``:(num |-> infer_t) infer_st``] check_specs_complete) >>
    `ienv.inf_t = tenv.t` by fs [env_rel_def, ienv_ok_def, env_rel_sound_def] >>
    simp [GSYM PULL_FORALL] >>
    impl_tac
    >- fs [env_rel_def, ienv_ok_def] >>
    disch_then (qspecl_then [`st2`, `empty_inf_decls`, `<|inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsEmpty|>`] mp_tac) >>
    rw [] >>
    rw [success_eqns]
    >- simp [GSYM INSERT_SING_UNION, union_decls_def, convert_decls_def]
    >- (
      simp [extend_dec_ienv_empty] >>
      metis_tac [env_rel_lift])
    >- fs [convert_decls_def]
    >- (
      simp [extend_dec_ienv_empty] >>
      metis_tac [check_weak_ienv_complete])
    >- metis_tac [check_weak_decls_complete]));

val infer_prog_complete = Q.store_thm ("infer_prog_complete",
  `!x decls tenv prog decls' tenv'.
    type_prog x decls tenv prog decls' tenv' ⇒
    !st1 idecls ienv.
    env_rel tenv ienv ∧
    decls = convert_decls idecls ∧
    x = T
    ⇒
    ?idecls' ienv' st2.
      decls' = convert_decls idecls' ∧
      env_rel tenv' ienv' ∧
      infer_prog idecls ienv prog st1 = (Success (idecls',ienv'), st2)`,
  ho_match_mp_tac type_prog_ind >>
  rw [infer_prog_def, success_eqns]
  >- rw [convert_decls_def, empty_decls_def, empty_inf_decls_def] >>
  drule infer_top_complete >>
  disch_then drule >>
  disch_then (qspecl_then [`st1`, `idecls`] mp_tac) >>
  rw [] >>
  rw [success_eqns] >>
  `env_rel (extend_dec_tenv tenv1 tenv) (extend_dec_ienv ienv' ienv)`
    by metis_tac [env_rel_extend] >>
  first_x_assum drule >>
  simp [GSYM convert_append_decls] >>
  disch_then (qspecl_then [`st2`, `append_decls idecls' idecls`] mp_tac) >>
  rw [] >>
  rw [success_eqns, convert_append_decls] >>
  metis_tac [env_rel_extend]);

val _ = export_theory ();
