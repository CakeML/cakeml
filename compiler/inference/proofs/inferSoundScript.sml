(*
  Proves soundness of the type inferencer: any type assignment
  produced by the type inferencer is a valid type for the program.
*)
open preamble
open typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory infer_tTheory
     astPropsTheory inferPropsTheory typeSysPropsTheory infer_eSoundTheory envRelTheory type_eDetermTheory
     infer_eCompleteTheory namespacePropsTheory

val _ = new_theory "inferSound";

val letrec_lemma2 = Q.prove (
`!funs_ts l l' s s'.
 (!t1 t2. t_walkstar s t1 = t_walkstar s t2 ⇒  t_walkstar s' t1 = t_walkstar s' t2) ∧
 (LENGTH funs_ts = LENGTH l) ∧
 (LENGTH funs_ts = LENGTH l') ∧
 MAP (λn. t_walkstar s (Infer_Tuvar n)) l' = MAP (t_walkstar s) funs_ts
 ⇒
 (MAP2 (λ(f,x,e) t. (f,t)) l (MAP (λn. convert_t (t_walkstar s' (Infer_Tuvar n))) l')
  =
  MAP2 (λ(x,y,z) t. (x,convert_t (t_walkstar s' t))) l funs_ts)`,
induct_on `funs_ts` >>
cases_on `l` >>
cases_on `l'` >>
rw [] >>
fs [] >|
[PairCases_on `h` >>
     rw [] >>
     metis_tac [],
 metis_tac []]);

val sub_completion_empty = Q.prove (
`!m n s s'. sub_completion m n s [] s' ⇔ count n ⊆ FDOM s' ∧ (∀uv. uv ∈ FDOM s' ⇒ check_t m ∅ (t_walkstar s' (Infer_Tuvar uv))) ∧ s = s'`,
 rw [sub_completion_def, pure_add_constraints_def] >>
 metis_tac []);

val generalise_none = Q.prove (
`(!t s' t' x.
   check_t 0 x t ∧
   generalise 0 0 FEMPTY t = (0, s', t')
   ⇒
   s' = FEMPTY ∧
   check_t 0 {} t) ∧
 (!ts s' ts' x.
   EVERY (check_t 0 x) ts ∧
   generalise_list 0 0 FEMPTY ts = (0, s', ts')
   ⇒
   s' = FEMPTY ∧
   EVERY (check_t 0 {}) ts)`,
 ho_match_mp_tac infer_t_induction >>
 rw [generalise_def, check_t_def, LET_THM, LAMBDA_PROD]
 >- (`?n s' t'. generalise_list 0 0 FEMPTY ts = (n,s',t')` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     metis_tac [])
 >- (`?n s' t'. generalise_list 0 0 FEMPTY ts = (n,s',t')` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     metis_tac []) >>
 `?n' s'' t''. generalise 0 0 FEMPTY t = (n',s'',t'')` by metis_tac [pair_CASES] >>
 fs [] >>
 `?n s' t'. generalise_list 0 n' s'' ts = (n,s',t')` by metis_tac [pair_CASES] >>
 fs [] >>
 rw [] >>
 metis_tac []);

val lookup_var_empty = Q.prove(`
  lookup_var x (bind_tvar tvs Empty) tenv =
  lookup_var x Empty tenv`,
  rw[bind_tvar_def,lookup_var_def,lookup_varE_def]>>
  EVERY_CASE_TAC>>fs[tveLookup_def]);

(* TODO: This should be generalized eventually *)
Theorem env_rel_complete_bind:
    env_rel_complete FEMPTY ienv tenv Empty ⇒
  env_rel_complete FEMPTY ienv tenv (bind_tvar tvs Empty)
Proof
  rw[env_rel_complete_def,lookup_var_empty]>>res_tac>>fs[]
  >-
    metis_tac[]
  >>
  match_mp_tac tscheme_approx_weakening>>qexists_tac`0`>>
  HINT_EXISTS_TAC>>
  fs[t_wfs_def]
QED

(* TODO: The generated set of type identifiers (tids)
  must be related to st2.next_id in some way
  The current relation might be wrong *)

(* the set of ids n1 .... n2-1 *)
val set_ids_def = Define`
  set_ids n1 (n2:num) = {m | n1 ≤ m ∧ m < n2}`

val set_ids_eq = Q.prove(`
  set_ids n1 n2 =
  set (GENLIST (λx. x + n1) (n2-n1))`,
  fs[set_ids_def,EXTENSION,MEM_MAP,MEM_GENLIST]>>
  rw[EQ_IMP_THM]>>
  qexists_tac`x-n1`>>fs[]);

Theorem set_ids_same[simp]:
   set_ids x x = {}
Proof
  rw[set_ids_eq]
QED

Theorem set_ids_eq_union:
   x <= y /\ y <= z ==> set_ids x z = set_ids x y UNION set_ids y z
Proof
  fs [set_ids_def, EXTENSION]
QED

Theorem set_ids_eq_union_eq:
   x <= y /\ y <= z /\ s = set_ids y z
    ==> set_ids x z = set_ids x y UNION s
Proof
  fs [set_ids_eq_union]
QED

fun str_tac strs = ConseqConv.CONSEQ_CONV_TAC
  (ConseqConv.CONSEQ_REWRITE_CONV ([], strs, []));

Theorem infer_d_sound:
   (!d tenv ienv st1 st2 ienv'.
    infer_d ienv d st1 = (Success ienv', st2) ∧
    env_rel tenv ienv ∧
    start_type_id ≤ st1.next_id
    ⇒
    type_d T tenv d (set_ids st1.next_id st2.next_id) (ienv_to_tenv ienv')) ∧
  (!ds tenv ienv st1 st2 ienv'.
    infer_ds ienv ds st1 = (Success ienv', st2) ∧
    env_rel tenv ienv ∧
    start_type_id ≤ st1.next_id
    ⇒
    type_ds T tenv ds (set_ids st1.next_id st2.next_id) (ienv_to_tenv ienv'))
Proof
  Induct
  >- (
    (* Dlet *)
    rw[infer_d_def,success_eqns]>>
    pairarg_tac \\ fs[success_eqns]
    \\ fs[init_state_def] \\ rveq
    \\ drule (CONJUNCT1 infer_e_sound)
    \\ fs[init_state_def, env_rel_def]
    \\ imp_res_tac(CONJUNCT1 infer_e_wfs) \\ fs[]
    \\ drule (CONJUNCT1 infer_p_sound)
    \\ simp[]
    \\ `(init_infer_state st1).next_uvar = 0` by (fs [init_infer_state_def] >> rw []) >>
    drule (CONJUNCT1 infer_p_wfs) >>
    disch_then drule >>
    strip_tac >>
    drule t_unify_wfs >>
    disch_then drule >>
    strip_tac >>
    drule (CONJUNCT1 infer_e_check_t) >>
    impl_tac >- fs [ienv_ok_def] >>
    strip_tac >>
    drule (CONJUNCT1 infer_e_check_s) >>
    simp [] >>
    disch_then (qspec_then `0` mp_tac) >>
    impl_tac >- simp [check_s_def, init_infer_state_def] >>
    strip_tac >>
    drule (CONJUNCT1 infer_p_check_t) >>
    strip_tac >>
    drule (CONJUNCT1 infer_p_check_s) >>
    disch_then (qspec_then `0` mp_tac) >>
    impl_tac >- fs [ienv_ok_def] >>
    strip_tac >>
    drule t_unify_check_s >>
    simp [] >>
    disch_then drule >>
    simp [] >>
    impl_tac >- metis_tac [infer_p_next_uvar_mono, check_t_more4] >>
    strip_tac >>
    pairarg_tac >>
    rename1 `generalise_list _ _ _ _ = (tvs, s2, ts)` >>
    rename1 `Success (t2,bindings), st1'` >>
    `?ec1 last_sub.
          ts = MAP (t_walkstar last_sub) (MAP SND bindings) ∧
          t_wfs last_sub ∧
          sub_completion tvs st1'.next_uvar s ec1 last_sub`
     by (
       `tvs = tvs +0 ` by DECIDE_TAC>>pop_assum SUBST1_TAC>>
       drule generalise_complete>>fs[]>>
       fs[LAMBDA_PROD, EVERY_MAP] >>
       metis_tac[]) >>
    drule sub_completion_unify2 >>
    disch_then drule >>
    strip_tac >>
    drule (CONJUNCT1 sub_completion_infer_p) >>
    disch_then drule >>
    strip_tac >>
    `env_rel_sound FEMPTY ienv tenv (bind_tvar tvs Empty)`
     by (
      `t_wfs FEMPTY` by rw [t_wfs_def]
      >> metis_tac [env_rel_sound_extend_tvs]) >>
    drule env_rel_e_sound_empty_to >>
    disch_then drule >>
    disch_then drule >>
    strip_tac >>
    strip_tac >>
    disch_then drule >>
    simp [] >>
    disch_then drule >>
    pop_assum (qspecl_then [`tenv`, `tvs`, `(t1,t2)::ec1`, `last_sub`] mp_tac) >>
    impl_tac
    >- fs [typeSoundInvariantsTheory.tenv_ok_def, env_rel_sound_def] >>
    rw [] >>
    `t_walkstar last_sub t2 = t_walkstar last_sub t1`
      by (
        imp_res_tac infer_e_wfs >>
        imp_res_tac infer_p_wfs >>
        imp_res_tac t_unify_wfs >>
        metis_tac [sub_completion_apply, t_unify_apply]) >>
    imp_res_tac infer_e_next_id_const >>
    imp_res_tac infer_p_next_id_const >>
    `st1.next_id = st1'.next_id` by fs[init_infer_state_def] >>
    Cases_on `is_value e` >>
    fs [success_eqns] >>
    rw [Once type_d_cases, ienv_to_tenv_def]
    >- (
      qexists_tac `tvs` >>
      qexists_tac `convert_t (t_walkstar last_sub t2)` >>
      qexists_tac `convert_env last_sub bindings` >>
      rw []
      >- (
        simp [ZIP_MAP, tenv_add_tvs_def] >>
        simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, convert_env_def])
      >- (imp_res_tac infer_p_bindings >> fs [])
      >- (
        drule (GEN_ALL env_rel_complete_bind) >>
        disch_then (qspec_then `tvs'` assume_tac) >>
        drule (GEN_ALL infer_pe_complete) >>
        `ALL_DISTINCT (pat_bindings p [])` by
          (imp_res_tac type_p_pat_bindings>>
          `MAP FST bindings = pat_bindings p []` by
            (pop_assum sym_sub_tac>>
            simp[convert_env_def,MAP_MAP_o,MAP_EQ_f,FORALL_PROD])>>
          fs[])>>
        rpt (disch_then drule) >>
        disch_then (qspecl_then [`st1`,`<| loc := SOME l; err := ienv.inf_t |>`] mp_tac) >>
        strip_tac >>
        rfs [] >>
        fs[] >>
        rfs[] >>
        rpt var_eq_tac >>
        (* The "new" subcompletion s'' maps types in bindings to some type schemes with tvs' quantified variables *)
        simp[LIST_REL_EL_EQN,EL_MAP,convert_env_def,tenv_add_tvs_def]>>rw[]>>
        pairarg_tac>>fs[]>>
        pairarg_tac>>fs[]>>
        pairarg_tac>>fs[]>>
        fs[tscheme_inst_def]>>
        (* We need to instantiate the deB vars in t''', which are introduced under last_sub to the unification done in s'' *)
        imp_res_tac generalise_subst>>
        fs[]>>
        (* Rewrite last_sub back into an infer_subst *)
        `t_walkstar last_sub t'''' = infer_subst s2 (t_walkstar s t'''')` by
           (fs[MAP_MAP_o,LIST_EQ_REWRITE,EL_MAP,infer_subst_FEMPTY]>>
           pop_assum(qspec_then`n` assume_tac)>>rfs[])>>
        fs[sub_completion_def]>>
        Q.ISPECL_THEN [`tvs'`,`s''`] mp_tac (GEN_ALL generalise_subst_exist)>>
        impl_tac>-
          (fs[]>>
          metis_tac[pure_add_constraints_success])>>
        rw[]>>
        (* This produces the appropriate substitution mentioned above *)
        pop_assum (qspecl_then[`MAP (t_walkstar s) (MAP SND bindings)`,`[]`,`FEMPTY`,`tvs`,`s2`,`MAP (t_walkstar last_sub) (MAP SND bindings)`] mp_tac)>>
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
       `check_t 0 (count st'.next_uvar) t''''` by
         (fs[EVERY_EL]>>
         last_x_assum(qspec_then`n` assume_tac)>>rfs[])>>
       `check_t (LENGTH subst') {} (infer_subst s2 (t_walkstar s t''''))` by
         (qpat_x_assum `A = infer_subst B C` sym_sub_tac>>
         Q.SPECL_THEN [`count (st'.next_uvar)`,`last_sub`,`LENGTH subst'`,`t''''`] mp_tac (check_t_less |> CONJUNCT1 |>GEN_ALL)>>
         simp[]>>
         rw[]>>
         `count st'.next_uvar ∩ COMPL(FDOM last_sub) = {}` by
           (simp[EXTENSION]>>fs[SUBSET_DEF]>>
           metis_tac[])>>
         fs[])>>
     CONJ_ASM1_TAC>-
       metis_tac[check_t_to_check_freevars]>>
     CONJ_TAC>-
       (fs[EVERY_MAP,EVERY_MEM]>>
       metis_tac[check_t_to_check_freevars])>>
     imp_res_tac deBruijn_subst_convert>>
     pop_assum(qspec_then `subst'`assume_tac)>>fs[]>>
     AP_TERM_TAC>>
     Q.ISPECL_THEN [`s''`,`s2`,`subst'`,`_`,`count st'.next_uvar`] mp_tac (GEN_ALL infer_deBruijn_subst_infer_subst_walkstar)>>
     impl_tac>-
       (fs[SUBSET_DEF]>>
       rw[]>>
       fs[IN_FRANGE]>>
       metis_tac[pure_add_constraints_wfs])>>
     rw[]>>
     pop_assum kall_tac>>
     pop_assum(qspec_then `t_walkstar s t''''` mp_tac)>>
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
         first_x_assum(qspec_then`(n',t'''')` mp_tac)>>
         impl_tac>- metis_tac[MEM_EL]>>
         imp_res_tac check_t_more5>>
         fs[SUBSET_DEF,EXTENSION])
       >>
       rw[]>>
       metis_tac[pure_add_constraints_wfs,t_walkstar_SUBMAP,pure_add_constraints_success]))
    >- (
     qexists_tac `convert_t (t_walkstar last_sub t2)`
     >> qexists_tac `convert_env last_sub bindings`
     >> rw []
     >- (
       simp [ZIP_MAP, tenv_add_tvs_def]
       >> simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, convert_env_def])
     >-
       (match_mp_tac (GEN_ALL infer_e_type_pe_determ)>>
       qexists_tac`st1` >>
       qexists_tac `<| loc := SOME l; err := ienv.inf_t |>` >>
       HINT_EXISTS_TAC>>fs[]>>
       imp_res_tac(CONJUNCT2 generalise_none)>>
       pop_assum(qspec_then`count st1'.next_uvar` mp_tac)>>
       impl_tac>>fs[EVERY_MAP,EVERY_MEM,FORALL_PROD]>>
       rw[]>>res_tac>>
       qpat_x_assum `t_wfs s` assume_tac>>
       drule t_walkstar_check>>
       disch_then match_mp_tac>>
       rw[]
       >- (match_mp_tac check_s_more5>>HINT_EXISTS_TAC>>fs[])
       >- (match_mp_tac (SIMP_RULE (srw_ss()) [AND_IMP_INTRO, PULL_FORALL] (CONJUNCT1 check_t_more5))>>HINT_EXISTS_TAC>>fs[]))
     >- (
       imp_res_tac infer_p_bindings
       >> fs [])
     >- fs [bind_tvar_def]))
 (* Dletrec*)
  >- (
   rw[infer_d_def] >>
   fs[success_eqns] >>
   rename1 `infer_funs <| loc := SOME loc; err := ienv.inf_t |> _ _ _ = _` >>
   fs[init_state_def]>>
   pairarg_tac>>fs[success_eqns]>>rw[]>>
   `t_wfs (init_infer_state st1).subst` by rw [init_infer_state_def, t_wfs_def] >>
   `(init_infer_state st1).next_uvar = 0` by (fs [init_infer_state_def] >> rw []) >>
   `t_wfs st''''.subst` by
     (imp_res_tac infer_e_wfs>>fs[])>>
   (*MAP2 looks nasty to work with...*)
   rename [`ALL_DISTINCT (MAP FST l)`] >>
   qabbrev_tac `bindings = ZIP (MAP FST l,(MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH l))))`>>
   qmatch_asmsub_abbrev_tac`nsAppend (alist_to_ns mapp)`>>
   fs[]>>
   `mapp = MAP (λ(n,t). (n,0,t)) bindings` by
     (unabbrev_all_tac>>fs[MAP2_MAP,LENGTH_COUNT_LIST,ZIP_MAP,MAP_MAP_o,MAP_EQ_f,FORALL_PROD])>>
   `ienv_val_ok (count (LENGTH l)) (nsAppend (alist_to_ns mapp) ienv.inf_v)` by
     (fs[ienv_ok_def,ienv_val_ok_def]>>
     match_mp_tac nsAll_nsAppend>>
     rw[]
     >-
       (fs[Abbr`bindings`]>> match_mp_tac nsAll_alist_to_ns>>
       fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,MEM_ZIP,LENGTH_COUNT_LIST]>>rw[]>>
       simp[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST,check_t_def])
     >>
       fs[env_rel_def,ienv_ok_def,ienv_val_ok_def] >>
       irule nsAll_mono>>
       HINT_EXISTS_TAC>>
       simp[FORALL_PROD]>>
       metis_tac[check_t_more])>>
   fs[Abbr`mapp`] >>
   (* properties of infer_e *)
   drule (el 4 (CONJUNCTS infer_e_check_t))>>
   rfs[]>>strip_tac>>
   drule (el 4 (CONJUNCTS infer_e_check_s))>>
   disch_then(qspec_then`0` mp_tac)>>
   impl_tac>-
     fs[ienv_ok_def,init_infer_state_def,check_s_def,env_rel_def]>>
   strip_tac>>
   drule (el 4 (CONJUNCTS infer_e_next_uvar_mono))>>
   simp[]>>strip_tac>>
   drule generalise_complete>>fs[]>>
   disch_then(qspec_then`st''''.next_uvar` mp_tac)>>
   impl_keep_tac
   >-
     (rw[]
     >- metis_tac [pure_add_constraints_wfs, infer_e_wfs, infer_st_rewrs]
     >-
        (match_mp_tac pure_add_constraints_check_s>>fs[]>>
        ntac 2 HINT_EXISTS_TAC>>rfs[]>>
        simp[EVERY_MEM,MEM_ZIP,FORALL_PROD]>>
        rw[]
        >-
          fs[EL_MAP,EL_COUNT_LIST,LENGTH_COUNT_LIST,check_t_def]
        >>
          metis_tac[EVERY_MEM,MEM_EL])
     >>
        fs[EVERY_MEM,MEM_MAP,MEM_COUNT_LIST]>>rw[]>>
        fs[check_t_def])
   >>
   rw[]>>
   imp_res_tac sub_completion_add_constraints >>
   `env_rel_sound last_sub ienv tenv (bind_tvar num_gen Empty)` by
     (match_mp_tac env_rel_e_sound_empty_to>>
     fs[sub_completion_wfs, env_rel_def]>>
     match_mp_tac env_rel_sound_extend_tvs>>fs[t_wfs_def])>>
   qabbrev_tac `tenv_v'' = bind_var_list 0 (convert_env last_sub bindings) (bind_tvar num_gen Empty)` >>
   `num_tvs tenv_v'' = num_gen` by (unabbrev_all_tac>>fs[bind_tvar_def])>>
   drule (el 4 (CONJUNCTS infer_e_sound)) >> fs[] >>
   qmatch_asmsub_abbrev_tac`sub_completion num_gen _ _ constraints _`>>
   disch_then(qspecl_then[`tenv`,`tenv_v''`,`constraints`,`last_sub`] mp_tac)>>fs[]>>
   impl_tac>-
     (rw[]
     >-
       fs[ienv_ok_def,env_rel_def]
     >>
       fs[Abbr`tenv_v''`]>>
       match_mp_tac env_rel_sound_merge0>>fs[sub_completion_def]>>
       fs[Abbr`bindings`]>>
       fs[EVERY_MEM,MEM_ZIP,FORALL_PROD,LENGTH_COUNT_LIST]>>rw[]>>
       fs[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST,check_t_def,SUBSET_DEF])>>
   strip_tac>>
   fs[sub_completion_def]>>
   imp_res_tac pure_add_constraints_apply>>
   fs[Abbr`constraints`]>>
   rfs[GSYM MAP_MAP_o,MAP_ZIP,LENGTH_COUNT_LIST]>>
   rw[Once type_d_cases] >>
   imp_res_tac infer_e_next_id_const >>
   pop_assum mp_tac \\ rw[Once init_infer_state_def] >>
   qexists_tac`convert_env last_sub bindings`>>
   qexists_tac`num_tvs tenv_v''`>>fs[Abbr`tenv_v''`]>>
   `(MAP2 (λ(x,y,z) t. (x,convert_t (t_walkstar last_sub t))) l funs_ts) = convert_env last_sub bindings` by
     (fs[MAP2_MAP,convert_env_def,Abbr`bindings`]>>
     match_mp_tac LIST_EQ_MAP_PAIR>>
     fs[MAP_MAP_o,o_DEF,LAMBDA_PROD]>>
     rw[]
     >-
       (match_mp_tac LIST_EQ>>fs[LENGTH_COUNT_LIST,EL_MAP,EL_ZIP]>>rw[]>>
       pairarg_tac>>fs[])
     >>
       ntac 3 (pop_assum mp_tac)>>simp[LIST_EQ_REWRITE]>>
       fs[LENGTH_COUNT_LIST,EL_MAP,EL_ZIP]>>rw[]>>
       pairarg_tac>>fs[])>>
   fs[]>>rw[]
   >-
     (simp[ienv_to_tenv_def, tenv_add_tvs_def, convert_env_def, MAP2_ZIP]>>
     pop_assum mp_tac>>
     simp[Abbr`bindings`,MAP_MAP_o,o_DEF,MAP2_MAP,LENGTH_COUNT_LIST,LAMBDA_PROD,tenv_add_tvs_def,LIST_EQ_REWRITE,convert_env_def,EL_MAP]>>
     rw[]>>
     first_x_assum(qspec_then`x` assume_tac)>>
     rfs[]>>rpt(pairarg_tac>>fs[])>>
     rfs[EL_ZIP,LENGTH_COUNT_LIST,EL_MAP,EL_COUNT_LIST]>>
     rw[])
   >>
     imp_res_tac type_funs_distinct >> fs[FST_triple] >>
     imp_res_tac type_funs_MAP_FST >>
     imp_res_tac type_funs_Tfn>>
     fs[env_rel_def] >>
     drule (GEN_ALL infer_funs_complete)>>fs[]>>
     disch_then (qspecl_then [`tvs'`,`tenv`,`st1`,`<| loc := SOME loc; err := ienv.inf_t |>`,`l`,`bindings'`] assume_tac)>>rfs[]>>
     `st'.subst = st'''''.subst` by
       metis_tac[pure_add_constraints_functional]>>
     simp[LIST_REL_EL_EQN]>>
     fs[convert_env_def,tenv_add_tvs_def]>>
     CONJ_ASM1_TAC
     >-
       metis_tac[LENGTH_MAP]>>
     rw[EL_MAP]>>
     pairarg_tac>>fs[]>>
     pairarg_tac>>fs[]>>
     pairarg_tac>>fs[]>>
     fs[tscheme_inst_def]>>
     `t'' = Infer_Tuvar n` by
       (pop_assum mp_tac>>fs[Abbr`bindings`]>>
       `LENGTH bindings' = LENGTH funs_ts` by metis_tac[LENGTH_MAP]>>
       fs[EL_ZIP,LENGTH_MAP,LENGTH_COUNT_LIST,EL_MAP,EL_COUNT_LIST])>>
     `LENGTH bindings = LENGTH funs_ts` by metis_tac[LENGTH_MAP]>>
     imp_res_tac generalise_subst>>
     fs[]>>
     (* Rewrite last_sub back into an infer_subst *)
     `t_walkstar last_sub t'' = infer_subst s (t_walkstar st'''''.subst t'')` by
       (fs[MAP_MAP_o,LIST_EQ_REWRITE,EL_MAP,infer_subst_FEMPTY]>>
       pop_assum(qspec_then`n` assume_tac)>>
       rfs[EL_COUNT_LIST,EL_MAP])>>
     fs[sub_completion_def]>>
     Q.ISPECL_THEN [`tvs'`,`s'`] mp_tac (GEN_ALL generalise_subst_exist)>>
     impl_tac>-
       (fs[]>>
       metis_tac[pure_add_constraints_success])>>
     rw[]>>
     (* This produces the appropriate substitution mentioned above *)
     pop_assum (qspecl_then[`MAP (t_walkstar st'''''.subst) (MAP (λn. Infer_Tuvar n) (COUNT_LIST (LENGTH funs_ts)))`,
                            `[]`,`FEMPTY`,`num_tvs tenv_v''`,`s`,`MAP (t_walkstar last_sub) funs_ts`] mp_tac)>>
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
       fs[check_t_def,MEM_COUNT_LIST]>>
       rw[]
       >-
         (match_mp_tac (check_s_more3|> SIMP_RULE std_ss[PULL_FORALL,AND_IMP_INTRO])>>
         asm_exists_tac>>fs[])
       >>
         res_tac>>
         match_mp_tac (check_t_more5|> CONJUNCT1 |> SIMP_RULE std_ss[PULL_FORALL,AND_IMP_INTRO])>>
         asm_exists_tac>>fs[])
     >>
     rw[]>>
     (* Pick the substitution, except turn it into deBruijn vars *)
     qexists_tac`MAP convert_t subst'`>>fs[]>>
     `check_t 0 (count st'''''.next_uvar) (Infer_Tuvar n)` by
       (fs[EVERY_EL]>>
       last_x_assum(qspec_then`n` kall_tac)>>
       last_x_assum(qspec_then`n` mp_tac)>>
       fs[LENGTH_COUNT_LIST,EL_MAP,EL_COUNT_LIST])>>
     `check_t (LENGTH subst') {} (infer_subst s (t_walkstar st'''''.subst (Infer_Tuvar n)))` by
       (qpat_x_assum `A = infer_subst B C` sym_sub_tac>>
       Q.SPECL_THEN [`count (st'''''.next_uvar)`,`last_sub`,`LENGTH subst'`,`Infer_Tuvar n`] mp_tac (check_t_less |> CONJUNCT1 |>GEN_ALL)>>
       simp[]>>
       rw[]>>
       `count st'''''.next_uvar ∩ COMPL(FDOM last_sub) = {}` by
         (simp[EXTENSION]>>fs[SUBSET_DEF]>>
         metis_tac[])>>
       fs[]>>metis_tac[])>>
     CONJ_ASM1_TAC>-
       metis_tac[check_t_to_check_freevars]>>
     CONJ_TAC>-
       (fs[EVERY_MAP,EVERY_MEM]>>
       metis_tac[check_t_to_check_freevars])>>
     imp_res_tac deBruijn_subst_convert>>
     pop_assum(qspec_then `subst'`assume_tac)>>fs[]>>
     `t = convert_t (t_walkstar s' (Infer_Tuvar n))` by
       (rfs[EL_MAP,MAP_MAP_o]>>
       qpat_x_assum`MAP SND bindings' = _` mp_tac>>
       qpat_x_assum`_ = MAP (t_walkstar st'''''.subst) _` mp_tac>>
       simp[LIST_EQ_REWRITE, LENGTH_COUNT_LIST] >>
       disch_then(qspec_then`n`mp_tac) \\ simp[EL_MAP, LENGTH_COUNT_LIST, EL_COUNT_LIST]
       \\ strip_tac
       \\ disch_then(qspec_then`n`mp_tac)
       \\ rw[]
       \\ metis_tac[pure_add_constraints_success,t_compat_def])>>
     simp[]>>
     AP_TERM_TAC>>
     Q.ISPECL_THEN [`s'`,`s`,`subst'`,`_`,`count st'.next_uvar`] mp_tac (GEN_ALL infer_deBruijn_subst_infer_subst_walkstar)>>
     impl_tac>-
       (fs[SUBSET_DEF]>>
       rw[]>>
       fs[IN_FRANGE]>>
       metis_tac[pure_add_constraints_wfs])>>
     rw[]>>
     pop_assum kall_tac>>
     pop_assum(qspec_then `t_walkstar st'''''.subst (Infer_Tuvar n)` mp_tac)>>
     impl_tac>-
       (fs[EXTENSION,SUBSET_DEF]>>
       qpat_x_assum`MAP A (MAP B C ) = _ _ funs_ts` sym_sub_tac>>
       fs[MEM_MAP,PULL_EXISTS]>>
       imp_res_tac ALOOKUP_MEM>>
       fs[FORALL_PROD,EXISTS_PROD]>>
       CONJ_TAC>-
         metis_tac[MEM_COUNT_LIST]>>
       reverse CONJ_TAC>-
         metis_tac[MEM_COUNT_LIST]
       >>
       fs[EVERY_MAP,MAP_MAP_o,EVERY_MEM,UNCURRY]>>
       match_mp_tac t_walkstar_check>>fs[]>>
       CONJ_TAC>-
         (match_mp_tac check_s_more5>>
         asm_exists_tac>>fs[])
       >>
       last_x_assum(qspec_then`n` mp_tac)>>fs[MEM_COUNT_LIST]>>
       strip_tac>>
       imp_res_tac check_t_more5>>
       fs[SUBSET_DEF,EXTENSION])
     >>
     rw[]>>
     metis_tac[pure_add_constraints_wfs,t_walkstar_SUBMAP,pure_add_constraints_success]
  )
  >- (
    (* Dtype *)
    rw[infer_d_def,success_eqns]>>
    simp[Once type_d_cases]>>
    simp[set_ids_eq]>>
    qmatch_goalsub_abbrev_tac`set ls = _`>>
    qexists_tac`ls`>>
    fs[Abbr`ls`,n_fresh_id_def]>>
    rveq>>fs[ienv_to_tenv_def]>>
    fs[env_rel_def,env_rel_sound_def]>>
    simp[ALL_DISTINCT_GENLIST]>>
    fs[DISJOINT_DEF,EXTENSION,MEM_MAP,MEM_GENLIST]>>
    pop_assum mp_tac>>
    EVAL_TAC>>fs[])
  >- (
    (* Dtabbrev *)
    rw[infer_d_def,success_eqns]>>
    imp_res_tac type_name_check_subst_thm >>
    imp_res_tac type_name_check_subst_state >>
    fs [] >>
    simp[Once type_d_cases]>>
    fs[set_ids_def,ienv_to_tenv_def,env_rel_def, env_rel_sound_def] >>
    metis_tac [])
  >- (
    (* Dexn *)
    rw[infer_d_def,success_eqns]>>
    imp_res_tac type_name_check_subst_thm >>
    imp_res_tac type_name_check_subst_state >>
    fs [] >>
    simp[Once type_d_cases]>>
    fs[set_ids_def,ienv_to_tenv_def,env_rel_def, env_rel_sound_def]>>
    metis_tac[ETA_AX])
 >- (
    (* Dmod *)
    rw[infer_d_def,success_eqns]>>
    simp[Once type_d_cases]>>
    first_x_assum drule>> disch_then drule>>fs[]>> strip_tac>>
    HINT_EXISTS_TAC>>fs[]>>
    simp[ienv_to_tenv_def,tenvLift_def,lift_ienv_def,nsLift_nsMap])
  >- (
    (* Dlocal *)
    rw[infer_d_def, success_eqns]
    >> rpt (first_x_assum drule >> rw [])
    >> simp[Once type_d_cases]
    >> goal_assum(first_assum o mp_then Any mp_tac)
    >> str_tac [set_ids_eq_union_eq]
    >> fs []
    >> imp_res_tac infer_d_next_id_mono
    >> fs []
    >> first_x_assum (fn a =>
      CHANGED_TAC (str_tac [a, env_rel_extend, env_rel_ienv_to_tenv]))
    >> fs []
    >> conj_tac
    >- metis_tac [env_rel_def, infer_d_check]
    >> fs [set_ids_def,EXTENSION,DISJOINT_DEF]
  )
  >- (
    (* infer_ds [] *)
    fs[infer_d_def,success_eqns,env_rel_def]>>
    rw[] >> EVAL_TAC)
  >- (
    (* infer_ds (d::ds) *)
    rw[]>>
    fs[infer_d_def,success_eqns]>>
    rename1 `infer_d ienv1 _ _ = (Success ienv2, sti)` >>
    rename1 `infer_ds _ _ _ = (Success ienv3, _)` >>
    rpt(first_x_assum drule)>>
    rpt(disch_then drule)>>
    strip_tac>>strip_tac>>
    simp[Once type_d_cases] >>
    rw[]>>
    qexists_tac `ienv_to_tenv ienv2` >>
    qexists_tac `ienv_to_tenv ienv3` >>
    qexists_tac`set_ids st1.next_id sti.next_id`>>
    qexists_tac`set_ids sti.next_id st2.next_id`>>
    imp_res_tac infer_d_next_id_mono>>
    fs[ienv_to_tenv_extend]>>
    rw[]
    >-
      fs[set_ids_def,EXTENSION]
    >- (
      first_x_assum match_mp_tac>>fs[]>>
      match_mp_tac env_rel_extend>>fs[]>>
      match_mp_tac env_rel_ienv_to_tenv>>fs[]>>
      fs[env_rel_def]>>
      metis_tac[infer_d_check])
    >>
      fs[set_ids_def,EXTENSION,DISJOINT_DEF])
QED

Theorem db_subst_infer_subst_swap2:
 (!t s tvs uvar n.
  t_wfs s ∧
  check_t tvs {} t
  ⇒
  (convert_t
    (t_walkstar s
       (infer_deBruijn_subst
          (MAP (λn. Infer_Tuvar n) (COUNT_LIST tvs))
          t)) =
   deBruijn_subst 0
    (MAP (convert_t o t_walkstar s)
       (MAP (λn. Infer_Tuvar n) (COUNT_LIST tvs)))
    (convert_t t))) ∧
 (!ts s tvs uvar n.
  t_wfs s ∧
  EVERY (\t. check_t tvs {} t) ts ⇒
  (MAP (convert_t o
       t_walkstar s o
       infer_deBruijn_subst (MAP (λn. Infer_Tuvar n) (COUNT_LIST tvs)))
      ts =
   MAP (deBruijn_subst 0 (MAP (convert_t o t_walkstar s) (MAP (λn. Infer_Tuvar n) (COUNT_LIST tvs))) o
       convert_t)
      ts))
Proof
ho_match_mp_tac infer_t_induction >>
rw [convert_t_def, deBruijn_subst_def, EL_MAP, t_walkstar_eqn1,
    infer_deBruijn_subst_def, MAP_MAP_o, combinTheory.o_DEF, check_t_def,
    LENGTH_COUNT_LIST]
QED

(*
Theorem check_tscheme_inst_sound:
   !tvs_impl t_impl tvs_spec t_spec.
    check_t tvs_impl {} t_impl ∧
    check_t tvs_spec {} t_spec ∧
    check_tscheme_inst x (tvs_spec,t_spec) (tvs_impl,t_impl)
    ⇒
    tscheme_inst (tvs_spec, convert_t t_spec) (tvs_impl, convert_t t_impl)
Proof
  rw [check_tscheme_inst_def, tscheme_inst_def] >>
  every_case_tac >>
  fs [success_eqns] >>
  rw [] >>
  fs [init_state_def, init_infer_state_def] >>
  var_eq_tac >>
  fs [] >>
  `t_wfs FEMPTY` by rw [t_wfs_def] >>
  drule t_unify_apply >>
  disch_then drule >>
  rw [] >>
  drule t_unify_wfs >>
  disch_then drule >>
  strip_tac >>
  `t_walkstar s t_spec = t_spec` by metis_tac [t_walkstar_no_vars] >>
  fs [] >>
  rw [db_subst_infer_subst_swap2] >>
  rw [MAP_MAP_o, combinTheory.o_DEF] >>
  `?s'. ALL_DISTINCT (MAP FST s') ∧
     (FEMPTY |++ s' = FUN_FMAP (\x. Infer_Tapp [] Tc_int) (count tvs_impl DIFF FDOM s))`
    by metis_tac [fmap_to_list] >>
  `FINITE (count tvs_impl DIFF FDOM s)` by metis_tac [FINITE_COUNT, FINITE_DIFF] >>
  `t_wfs (s |++ s')`
    by (
      `t_vR s = t_vR (s |++ s')`
        by (
          rw [t_vR_eqn, FUN_EQ_THM] >>
          cases_on `FLOOKUP (s |++ s') x'` >>
          fs [flookup_update_list_none, flookup_update_list_some] >>
          cases_on `FLOOKUP s x'` >>
          fs [flookup_update_list_none, flookup_update_list_some] >>
          `FLOOKUP (FEMPTY |++ s') x' = SOME x''` by rw [flookup_update_list_some] >>
          pop_assum mp_tac >>
          rw [FLOOKUP_FUN_FMAP, t_vars_eqn] >>
          rw [FLOOKUP_FUN_FMAP, t_vars_eqn] >>
          fs [FLOOKUP_DEF]) >>
       fs [t_wfs_eqn]) >>
  qexists_tac `MAP (\n. convert_t (t_walkstar (s |++ s') (Infer_Tuvar n))) (COUNT_LIST tvs_impl)` >>
  rw [LENGTH_COUNT_LIST, check_t_to_check_freevars, EVERY_MAP] >>
  `FDOM (FEMPTY |++ s') = count tvs_impl DIFF FDOM s` by metis_tac [FDOM_FMAP] >>
  `check_s tvs_spec (count tvs_impl) s`
    by (
     drule t_unify_check_s >>
     simp [] >>
     disch_then irule >>
     simp [check_s_def, check_t_infer_db_subst2] >>
     metis_tac [check_t_more, check_t_more2, arithmeticTheory.ADD_COMM])
  >- (
    rw [EVERY_MEM] >>
    irule check_t_to_check_freevars >>
    irule t_walkstar_check >>
    simp [check_t_def, FDOM_FUPDATE_LIST]
    >> conj_tac >- (
      fs [check_s_def, fdom_fupdate_list2] >>
      rw [] >>
      rw [FUPDATE_LIST_APPLY_NOT_MEM] >>
      `count tvs_impl ⊆ FDOM s ∪ set (MAP FST s')` by rw [SUBSET_DEF]
      >- metis_tac [check_t_more5]
      >- metis_tac [check_t_more5] >>
      `FLOOKUP (s |++ s') uv = SOME ((s |++ s') ' uv)`
        by rw [FLOOKUP_DEF, FDOM_FUPDATE_LIST] >>
      fs [flookup_update_list_some]
      >- (
        imp_res_tac ALOOKUP_MEM >>
        fs[] >>
        imp_res_tac (GSYM mem_to_flookup) >>
        fs[] >>
        ntac 2 (pop_assum mp_tac) >>
        rw [FLOOKUP_FUN_FMAP] >>
        rw [check_t_def])
      >- (
        pop_assum mp_tac >>
        rw [FLOOKUP_DEF]))
    >- (
      fs [EXTENSION, MEM_COUNT_LIST] >>
      res_tac >>
      fs [FDOM_FUPDATE_LIST]))
  >- (
    imp_res_tac t_walkstar_no_vars >>
    fs [] >>
    rw [SIMP_RULE (srw_ss()) [MAP_MAP_o, combinTheory.o_DEF] (GSYM db_subst_infer_subst_swap2)] >>
    AP_TERM_TAC >>
    simp[MAP_GENLIST,COUNT_LIST_GENLIST,ETA_AX] >>
    match_mp_tac (SIMP_RULE (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM,AND_IMP_INTRO] no_vars_extend_subst) >>
    rw []
    >- (
      rw [DISJOINT_DEF, EXTENSION] >>
      metis_tac [])
    >- (
      imp_res_tac check_t_t_vars  >>
      fs [EXTENSION, SUBSET_DEF, COUNT_LIST_GENLIST, MAP_GENLIST] >>
      metis_tac []))
QED

Theorem weak_tenv_ienv_to_tenv:
   !ienv1 ienv2.
    ienv_ok {} ienv1 ∧ ienv_ok {} ienv2 ∧
    check_weak_ienv ienv1 ienv2 ⇒ weak_tenv (ienv_to_tenv ienv1) (ienv_to_tenv ienv2)
Proof
  rw [check_weak_ienv_def, weak_tenv_def, ienv_to_tenv_def, GSYM nsSub_compute_thm] >>
  simp [nsSub_nsMap] >>
  fs [tscheme_inst2_def] >>
  irule nsSub_mono2 >>
  rw [] >>
  HINT_EXISTS_TAC >>
  rw [] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  fs [] >>
  rw [] >>
  fs [ienv_ok_def, ienv_val_ok_def] >>
  drule nsLookup_nsAll >>
  disch_then drule >>
  rw [] >>
  qpat_x_assum `nsAll _ ienv2.inf_v` mp_tac >>
  drule nsLookup_nsAll >>
  disch_then drule >>
  rw [] >>
  metis_tac [check_tscheme_inst_sound]
QED

Theorem weak_decls_ienv_to_tenv:
   !idecls1 idecls2.
    check_weak_decls idecls1 idecls2 ⇒ weak_decls (convert_decls idecls1) (convert_decls idecls2)
Proof
  rw [check_weak_decls_def, weak_decls_def, convert_decls_def, SUBSET_DEF,
      EVERY_MEM, list_subset_def, list_set_eq_def, EXTENSION] >>
  metis_tac []
QED

val check_freevars_nub = Q.prove (
`(!t x fvs.
  check_freevars x fvs t ⇒
  check_freevars x (nub fvs) t) ∧
 (!ts x fvs.
  EVERY (check_freevars x fvs) ts ⇒
  EVERY (check_freevars x (nub fvs)) ts)`,
Induct >>
rw [check_freevars_def] >> metis_tac[]);

val check_specs_sound = Q.prove (
  `!mn tenvT idecls1 ienv1 specs st1 idecls2 ienv2 st2.
    check_specs mn tenvT idecls1 ienv1 specs st1 = (Success (idecls2,ienv2), st2) ∧
    tenv_abbrev_ok tenvT
    ⇒
    ?decls3 ienv3.
      type_specs mn tenvT specs decls3 (ienv_to_tenv ienv3) ∧
      convert_decls idecls2 = union_decls decls3 (convert_decls idecls1) ∧
      ienv2 = extend_dec_ienv ienv3 ienv1`,
  ho_match_mp_tac check_specs_ind >>
  rw [check_specs_def, success_eqns]
  >- (
    rw [Once type_specs_cases] >>
    qexists_tac `<|inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsEmpty|>` >>
    rw [ienv_to_tenv_def, extend_dec_ienv_def, inf_env_component_equality])
  >- (
    first_x_assum drule >>
    rw [] >>
    qexists_tac `decls3` >>
    qmatch_assum_abbrev_tac
      `check_specs _ _ _ (ienv1 with inf_v := nsBind name new_binding ienv1.inf_v) _ _ = _` >>
    simp [Once type_specs_cases] >>
    qexists_tac `ienv3 with inf_v := nsAppend ienv3.inf_v (nsSing name new_binding)` >>
    rw [extend_dec_ienv_def, extend_dec_tenv_def, ienv_to_tenv_def, nsMap_nsAppend,
        nsAppend_nsSing]
    >- (
      HINT_EXISTS_TAC >>
      rw [ienv_to_tenv_def] >>
      unabbrev_all_tac >>
      fs [] >>
      qexists_tac `nub fvs` >>
      conj_asm2_tac
      >- (
        rpt AP_TERM_TAC >>
        drule check_freevars_type_name_subst >>
        disch_then drule >>
        disch_then drule >>
        rw [convert_t_subst, LENGTH_COUNT_LIST, MAP_MAP_o, combinTheory.o_DEF,
            convert_t_def, MAP_GENLIST, COUNT_LIST_GENLIST])
      >- metis_tac [t_to_freevars_check, check_freevars_nub])
    >- metis_tac [GSYM nsAppend_assoc, nsAppend_nsSing])
  >- (
    first_x_assum drule >>
    impl_tac
    >- (
      irule tenv_abbrev_ok_merge >>
      simp [] >>
      rw [typeSoundInvariantsTheory.tenv_abbrev_ok_def] >>
      irule nsAll_alist_to_ns >>
      simp [EVERY_MAP] >>
      rw [EVERY_MEM] >>
      pairarg_tac >>
      simp [] >>
      pairarg_tac >>
      simp [] >>
      pairarg_tac >>
      fs [] >>
      rw [check_freevars_def, EVERY_MAP, EVERY_MEM]) >>
    rw [] >>
    simp [Once type_specs_cases, PULL_EXISTS] >>
    qmatch_assum_abbrev_tac
      `check_specs _ _ _ <| inf_v := _;
                            inf_c := nsAppend new_ctors _;
                            inf_t := nsAppend new_tdefs _ |> _ _ = _` >>
    qexists_tac `extend_dec_ienv ienv3 <| inf_v := nsEmpty; inf_c := new_ctors;
                                    inf_t := new_tdefs |>` >>
    qexists_tac `ienv_to_tenv ienv3` >>
    qexists_tac `decls3` >>
    rw [ienv_to_tenv_def, extend_dec_ienv_def, extend_dec_tenv_def] >>
    rw [union_decls_def, convert_decls_def] >>
    rw [EXTENSION] >>
    metis_tac [])
  >- (
    simp [Once type_specs_cases, PULL_EXISTS] >>
    first_x_assum (qspec_then `nsBind tn (tvs,type_name_subst tenvT t) nsEmpty` mp_tac) >>
    simp [] >>
    disch_then drule >>
    impl_tac
    >- (
      fs [typeSoundInvariantsTheory.tenv_abbrev_ok_def] >>
      irule nsAll_nsBind >>
      simp [] >>
      irule check_freevars_type_name_subst >>
      simp [typeSoundInvariantsTheory.tenv_abbrev_ok_def]) >>
    rw [] >>
    qmatch_assum_abbrev_tac
      `check_specs _ _ _ (ienv1 with inf_t := nsBind name new_t _) _ _ = _` >>
    qexists_tac `decls3` >>
    qexists_tac `ienv3 with inf_t := nsAppend ienv3.inf_t (nsSing name new_t)` >>
    qexists_tac `ienv_to_tenv ienv3` >>
    rw [ienv_to_tenv_def, extend_dec_ienv_def, extend_dec_tenv_def] >>
    metis_tac [nsAppend_nsSing, nsAppend_assoc])
  >- (
    first_x_assum drule >>
    rw [] >>
    simp [Once type_specs_cases, PULL_EXISTS] >>
    qmatch_assum_abbrev_tac
      `check_specs _ _ _ (ienv1 with inf_c := nsBind name new_binding ienv1.inf_c) _ _ = _` >>
    qexists_tac `ienv3 with inf_c := nsAppend ienv3.inf_c (nsSing name new_binding)` >>
    rw [extend_dec_ienv_def, extend_dec_tenv_def, ienv_to_tenv_def, nsMap_nsAppend,
        nsAppend_nsSing] >>
    qexists_tac `ienv_to_tenv ienv3` >>
    simp [] >>
    HINT_EXISTS_TAC >>
    rw [ienv_to_tenv_def, union_decls_def, convert_decls_def] >>
    metis_tac [GSYM nsAppend_assoc, nsAppend_nsSing, INSERT_SING_UNION, UNION_ASSOC])
  >- (
    simp [Once type_specs_cases, PULL_EXISTS] >>
    first_x_assum (qspec_then `nsBind tn (tvs,Tapp (MAP Tvar tvs) (TC_name (mk_id mn tn))) nsEmpty` mp_tac) >>
    simp [] >>
    disch_then drule >>
    impl_tac
    >- (
      fs [typeSoundInvariantsTheory.tenv_abbrev_ok_def] >>
      irule nsAll_nsBind >>
      simp [check_freevars_def, EVERY_MAP, EVERY_MEM]) >>
    rw [] >>
    qmatch_assum_abbrev_tac
      `check_specs _ _ _ (ienv1 with inf_t := nsBind name new_binding ienv1.inf_t) _ _ = _` >>
    qexists_tac `ienv3 with inf_t := nsAppend ienv3.inf_t (nsSing name new_binding)` >>
    qexists_tac `ienv_to_tenv ienv3` >>
    qexists_tac `decls3` >>
    simp [ienv_to_tenv_def, extend_dec_tenv_def, extend_dec_ienv_def,
          union_decls_def, convert_decls_def] >>
    metis_tac [GSYM nsAppend_assoc, nsAppend_nsSing, INSERT_SING_UNION, UNION_ASSOC]));

Theorem infer_top_sound:
   !idecls ienv top st1 idecls' ienv' st2 tenv.
    infer_top idecls ienv top st1 = (Success (idecls',ienv'), st2) ∧
    env_rel tenv ienv
    ⇒
    type_top T (convert_decls idecls) tenv top (convert_decls idecls') (ienv_to_tenv ienv')
Proof
  rw [] >>
  Cases_on `top` >>
  fs [infer_top_def, success_eqns, type_top_cases] >>
  pairarg_tac >>
  fs []
  >- (
    fs [success_eqns] >>
    pairarg_tac >>
    fs [success_eqns] >>
    rpt var_eq_tac >>
    drule infer_ds_sound >>
    disch_then drule >>
    rw [] >>
    rename1 `check_signature _ ienv.inf_t _ idecls2 ienv2 sig st2 =
               (Success (idecls3,ienv3), st3)` >>
    Cases_on `sig` >>
    fs [check_signature_def, typeSystemTheory.check_signature_cases,
        success_eqns]
    >- (
      rpt var_eq_tac >>
      qexists_tac `ienv_to_tenv ienv2` >>
      qexists_tac `convert_decls idecls2` >>
      rw [convert_decls_def, union_decls_def, GSYM INSERT_SING_UNION, ienv_to_tenv_lift]) >>
    pairarg_tac >>
    fs [success_eqns] >>
    rpt var_eq_tac >>
    qexists_tac `ienv_to_tenv ienv2` >>
    rename1 `check_weak_ienv _ ienv3` >>
    qexists_tac `ienv_to_tenv ienv3` >>
    qexists_tac `convert_decls idecls2` >>
    rename1 `check_weak_decls _ idecls3` >>
    qexists_tac `convert_decls idecls3` >>
    rw [ienv_to_tenv_lift]
    >- simp [convert_decls_def, union_decls_def, GSYM INSERT_SING_UNION]
    >- simp [convert_decls_def]
    >- (
      irule weak_tenv_ienv_to_tenv >>
      fs [env_rel_def]
      >> conj_tac >- metis_tac [infer_ds_check] >>
      drule infer_ds_check >>
      rw [] >>
      drule check_specs_check >>
      disch_then irule >>
      fs [ienv_ok_def, ienv_val_ok_def])
    >- metis_tac [weak_decls_ienv_to_tenv]
    >- (
      drule check_specs_sound >>
      fs [env_rel_def, ienv_ok_def] >>
      rw [] >>
      fs [convert_decls_def, empty_inf_decls_def, extend_dec_ienv_def,
          union_decls_def, ienv_to_tenv_def, env_rel_sound_def] >>
      `<|defined_mods := decls3.defined_mods;
         defined_types := decls3.defined_types;
         defined_exns := decls3.defined_exns|> = decls3`
        by rw [decls_component_equality] >>
      metis_tac []))
  >- (
    irule infer_d_sound >>
    rw [] >>
    fs [success_eqns] >>
    metis_tac [])
QED

Theorem infer_prog_sound:
   !idecls ienv prog st1 idecls' ienv' st2 tenv.
    infer_prog idecls ienv prog st1 = (Success (idecls',ienv'), st2) ∧
    env_rel tenv ienv
    ⇒
    type_prog T (convert_decls idecls) tenv prog (convert_decls idecls') (ienv_to_tenv ienv')
Proof
  induct_on `prog` >>
  rw [infer_prog_def, success_eqns]
  >- rw [empty_decls_def,convert_decls_def, empty_inf_decls_def]
  >- rw [ienv_to_tenv_def] >>
  rw [Once type_prog_cases] >>
  pairarg_tac >>
  fs [success_eqns] >>
  pairarg_tac >>
  fs [success_eqns] >>
  rpt var_eq_tac >>
  drule infer_top_sound >>
  disch_then drule >>
  strip_tac >>
  rename1 `infer_top idecls1 ienv1 _ _ = (Success (idecls2, ienv2), _)` >>
  rename1 `infer_prog _ _ _ _ = (Success (idecls3, ienv3), _)` >>
  qexists_tac `ienv_to_tenv ienv2` >>
  qexists_tac `ienv_to_tenv ienv3` >>
  qexists_tac `convert_decls idecls2` >>
  qexists_tac `convert_decls idecls3` >>
  simp [ienv_to_tenv_extend, GSYM convert_append_decls] >>
  first_x_assum irule >>
  qexists_tac `extend_dec_ienv ienv2 ienv1` >>
  simp [] >>
  metis_tac [env_rel_extend, env_rel_ienv_to_tenv, env_rel_def,
  infer_top_invariant]
QED
*)

val _ = export_theory ();
