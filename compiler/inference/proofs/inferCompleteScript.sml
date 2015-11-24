open preamble;
open libTheory typeSystemTheory astTheory semanticPrimitivesTheory terminationTheory inferTheory unifyTheory;
open astPropsTheory;
open typeSysPropsTheory;
open inferPropsTheory;

open infer_eSoundTheory;
open infer_eCompleteTheory;
open type_eDetermTheory

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
 rw [generalise_def, check_t_def]
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

(* this might be totally wrong

val generalise_uvars = prove(
  ``(∀t m n s u d. FINITE u ∧ check_t d u t ⇒ FST(generalise m n s t) ≤ n + CARD (u DIFF (FDOM s))) ∧
    (∀ts m n s u d. FINITE u ∧ EVERY (check_t d u) ts ⇒ FST(generalise_list m n s ts) ≤ CARD (u DIFF (FDOM s)))``,
  ho_match_mp_tac infer_tTheory.infer_t_induction >>
  rw[generalise_def,check_t_def] >> rw[] >>
  TRY BasicProvers.CASE_TAC >> simp[] >>
  fsrw_tac[boolSimps.ETA_ss][] >- metis_tac[FST] >- (
    fs[FLOOKUP_DEF] >>
    `FINITE (FDOM s)` by simp[] >>
    asm_simp_tac std_ss [GSYM(MP_CANON CARD_DIFF)] >>
    `∃z. u DIFF FDOM s = n INSERT z ∧ n ∉ z ∧ FINITE z` by (
      qexists_tac`u DIFF (n INSERT (FDOM s))` >>
      simp[EXTENSION] >> metis_tac[] ) >>
    first_x_assum (CHANGED_TAC o SUBST1_TAC) >>
    simp[] ) >>
  last_x_assum(qspecl_then[`m`,`n`,`s`]mp_tac) >> simp[] >> strip_tac >>
  last_x_assum(qspecl_then[`m`,`num_gen+n`,`s'`]mp_tac) >> simp[] >> strip_tac >>
  res_tac >> simp[]

  fs[GSYM AND_IMP_INTRO] >>
  rpt(first_x_assum(fn th => first_assum(mp_tac o MATCH_MP th))) >>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP th))

  res_tac
  metis_tac[FST,arithmeticTheory.ADD_ASSOC,arithmeticTheory.ADD_COMM]
*)

val tenv_inv_letrec_merge2 = prove(``
  ∀funs:(tvarN,tvarN #exp)alist tenv' env tenv s tenv'' tenv'''.
    tenv''' = (MAP2 (λ(f,x,e) uvar. (f,0,uvar)) funs
          (MAP (λn. Infer_Tuvar n)
             (COUNT_LIST (LENGTH funs))) ++ env) ∧
    tenv'' = (bind_var_list 0
          (MAP2 (λ(f,x,e) t. (f,t)) funs
             (MAP
                (λn.
                   convert_t
                     (t_walkstar s (Infer_Tuvar n)))
                (COUNT_LIST (LENGTH funs)))) tenv) ∧
     t_wfs s ∧ tenv_inv s env tenv ⇒
     tenv_inv s tenv''' tenv''``,
    rw[]>>
    imp_res_tac (INST_TYPE [alpha|->``:tvarN``,beta|->``:exp``,delta|->``:num|->infer_t``] tenv_inv_letrec_merge)>>
    pop_assum(qspecl_then [`<|subst:=FEMPTY;next_uvar:=0|>`,`funs`] assume_tac)>>
    fs[]);

val infer_d_complete = Q.prove (
`!mn mdecls tdecls edecls menv d decls' tenvT' cenv' tenv tenv' st itenv.
  tenv_val_ok (bind_var_list2 tenv_v Empty) ∧
  tenv_mod_ok tenv.m ∧
  check_env ∅ itenv ∧
  tenv_ctor_ok tenv.c ∧
  tenv_tabbrev_ok tenv.t ∧
  check_menv menv ∧
  tenv_ctor_ok tenv.c ∧
  type_d T mn <| defined_mods := set mdecls; defined_types := set tdecls; defined_exns := set edecls |> (tenv with v := bind_var_list2 tenv_v Empty) d decls' tenvT' cenv' tenv' ∧
  tenv_alpha itenv (bind_var_list2 tenv_v Empty) ∧
  menv_alpha menv tenv.m
  ⇒
  ?st' mdecls'' tdecls'' edecls'' itenv'.
    set mdecls'' = decls'.defined_mods ∧
    set tdecls'' = decls'.defined_types ∧
    set edecls'' = decls'.defined_exns ∧
    infer_d mn (mdecls,tdecls,edecls) tenv.t menv tenv.c itenv d st =
      (Success ((mdecls'',tdecls'',edecls''), tenvT', cenv', itenv'), st') ∧
    tenv_alpha itenv' (bind_var_list2 tenv' Empty) ∧
    MAP FST itenv' = MAP FST tenv' ∧
    check_env {} itenv'`,
 rw [type_d_cases] >>
 rw [infer_d_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def] >>
 fs [empty_decls_def,check_env_def]
 (* Let generalisation case *)
 >- (
   rw[PULL_EXISTS] >>
   (infer_pe_complete
    |> (CONV_RULE(LAND_CONV(lift_conjunct_conv(can(match_term``type_e h i j``)))))
    |> REWRITE_RULE[GSYM AND_IMP_INTRO] |> GEN_ALL
    |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
   simp [bind_tvar_rewrites, num_tvs_bvl2, num_tvs_def] >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> simp[] >>
   disch_then(qspecl_then[`menv`,`itenv`]mp_tac) >>
   discharge_hyps >- (
     fs[tenv_alpha_def,tenv_invC_def,bind_tvar_rewrites] >>
     rpt gen_tac >> strip_tac >>
     qmatch_assum_abbrev_tac`lookup_tenv x tvs tenvx = SOME y` >>
     `num_tvs tenvx = 0` by
       simp[Abbr`tenvx`,num_tvs_bvl2,num_tvs_def] >>
     qspecl_then[`tvs`,`FST y`,`tenvx`,`x`]mp_tac lookup_tenv_val_inc_tvs >>
     simp[Abbr`y`] >>
     disch_then(qspec_then`t'`mp_tac) >> simp[] >>
     disch_then(fn th => first_x_assum(mp_tac o C MATCH_MP th)) >>
     strip_tac >>
     metis_tac[])
     (* conj_tac >- metis_tac[] >> simp[] >>
     reverse IF_CASES_TAC >- metis_tac[] >> fs[] >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     fs[Abbr`tenvx`,num_tvs_bvl2,num_tvs_def] >>
     `tvs = tvs + 0` by simp[] >> pop_assum SUBST1_TAC >>
     match_mp_tac(MP_CANON(CONJUNCT2 check_t_more2)) >>
     first_assum ACCEPT_TAC *) >>
   discharge_hyps_keep >- simp[check_env_def] >>
   simp[]>>
   strip_tac >> simp[] >>
   imp_res_tac infer_p_bindings >> fs[] >>
   qho_match_abbrev_tac`∃a b c. tr = (a,b,c) ∧ Q a b c` >>
   `∃a b c. tr = (a,b,c)` by metis_tac[pair_CASES] >> simp[] >> fs[Abbr`Q`,Abbr`tr`] >>
   fs[init_infer_state_def] >>
   qspecl_then[`0`,`s`,`MAP SND tenv'`]mp_tac generalise_complete >> simp[] >>
   disch_then(qspec_then`st'.next_uvar`mp_tac) >>
   discharge_hyps >- (
     conj_tac >- (
       match_mp_tac t_unify_check_s >>
       CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``t_unify`` o fst o strip_comb o lhs))) >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       fs[GSYM init_infer_state_def] >>
       `t_wfs (init_infer_state.subst)` by rw[init_infer_state_def,t_wfs_def] >>
       `t_wfs st.subst` by imp_res_tac infer_e_wfs >>
       `t_wfs st'.subst` by imp_res_tac infer_p_wfs >>
       imp_res_tac infer_p_check_t >> simp[] >>
       imp_res_tac(CONJUNCT1 infer_e_check_t) >>
       conj_tac >- (
         match_mp_tac (MP_CANON(CONJUNCT1 check_t_more5)) >>
         rfs[init_infer_state_def] >>
         rfs[check_env_def] >>
         first_assum(match_exists_tac o concl) >>
         imp_res_tac infer_p_next_uvar_mono >>
         simp[SUBSET_DEF] ) >>
       match_mp_tac (CONJUNCT1 infer_p_check_s) >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp[GSYM check_cenv_tenvC_ok] >>
       match_mp_tac (CONJUNCT1 infer_e_check_s) >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp[GSYM check_cenv_tenvC_ok] >>
       simp[init_infer_state_def] >>
       simp[check_s_def] >>
       simp[check_env_def]) >>
     imp_res_tac infer_p_check_t >>
     fs[EVERY_MEM,EVERY_MAP,FORALL_PROD] >>
     metis_tac[] ) >>
   strip_tac >> simp[ZIP_MAP] >>
   simp[MAP_MAP_o,combinTheory.o_DEF] >>
   rfs[convert_env2_def,tenv_add_tvs_def] >>
   simp[MAP_MAP_o,EVERY_MAP,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
   imp_res_tac type_p_pat_bindings >> simp[] >>
   reverse conj_asm2_tac >- (
     fs[sub_completion_def] >>
     imp_res_tac infer_p_check_t >>
     fs[EVERY_MEM,FORALL_PROD] >>
     rw[] >> res_tac >>
     `count st'.next_uvar ∩ COMPL (FDOM last_sub) = {}` by (
       simp[EXTENSION] >> fs[SUBSET_DEF] >>
       metis_tac[] ) >>
     (check_t_less |> CONJUNCT1 |> Q.GENL[`s`,`uvars`,`n`]
      |> Q.SPECL[`a`,`count (st':(num|->infer_t) infer_st).next_uvar`,`last_sub`]
      |> mp_tac) >>
     simp[] ) >>
   simp[tenv_alpha_def] >>
   conj_tac >- (
     simp[tenv_inv_def] >>
     simp[LAMBDA_PROD,ALOOKUP_MAP,PULL_EXISTS,GSYM bvl2_lookup] >>
     rw[] >>
     fs[simp_tenv_invC_def] >>
     res_tac >> res_tac >> simp[] >> fs[] >>
     rpt BasicProvers.VAR_EQ_TAC >>
     reverse IF_CASES_TAC >- (
       imp_res_tac ALOOKUP_MEM >>
       fs[EVERY_MEM,FORALL_PROD] >>
       metis_tac[] ) >>
     `convert_t (t_walkstar s' p2) = t` by (
       metis_tac[check_freevars_empty_convert_unconvert_id] ) >>
     BasicProvers.VAR_EQ_TAC >>
     fs[tenv_alpha_def]>>
     `tenv_inv last_sub itenv (bind_tvar a (bind_var_list2 tenv_v Empty))` by metis_tac [tenv_inv_empty_to,tenv_inv_extend_tvar_empty_subst] >>
     `type_e (tenv with v := bind_tvar a (bind_var_list2 tenv_v Empty)) e (convert_t (t_walkstar last_sub t'))` by
       (match_mp_tac (infer_e_sound|>CONJUNCT1)>>
       simp [] >>
       first_assum (match_exists_tac o concl)>>
       fs[bind_tvar_rewrites,num_tvs_bvl2,num_tvs_def,t_wfs_def,check_cenv_tenvC_ok]>>
       fs[sub_completion_def]>>
       imp_res_tac infer_p_constraints>>
       imp_res_tac infer_p_next_uvar_mono>>
       `pure_add_constraints st'.subst [t',t''] s` by
         fs[pure_add_constraints_def]>>
       qexists_tac`ts++[t',t'']++ec1`>>
       CONJ_TAC>-
         metis_tac[pure_add_constraints_append]>>
       fs[SUBSET_DEF]>>simp[])>>
     `type_p a tenv.c p (convert_t (t_walkstar last_sub t'')) (convert_env last_sub tenv')` by
       (match_mp_tac(infer_p_sound|>CONJUNCT1)>>
       first_assum (match_exists_tac o concl)>>
       imp_res_tac infer_e_wfs>>
       fs[t_wfs_def,check_cenv_tenvC_ok,sub_completion_def]>>
       `pure_add_constraints st'.subst [t',t''] s` by
         fs[pure_add_constraints_def]>>
       metis_tac[pure_add_constraints_append])>>
     `t_walkstar last_sub t' = t_walkstar last_sub t''`
             by (imp_res_tac infer_e_wfs >>
                 imp_res_tac infer_p_wfs >>
                 imp_res_tac t_unify_wfs >>
                 match_mp_tac sub_completion_apply>>
                 `t_wfs FEMPTY` by fs[t_wfs_def]>>
                 fs[]>>rfs[]>>
                 metis_tac[t_unify_apply])>>
     pop_assum SUBST_ALL_TAC>>
     res_tac>>
     fs[weakE_def,convert_env_def]>>
     first_x_assum (qspec_then `x` mp_tac)>>
     fs[ALOOKUP_MAP])>>
   (*TENVINVC*)
   simp[tenv_invC_def] >>
   simp[LAMBDA_PROD,ALOOKUP_MAP,PULL_EXISTS,GSYM bvl2_lookup] >>
   rw[] >>
   fs[simp_tenv_invC_def] >>
   res_tac >> simp[] >>
   reverse IF_CASES_TAC >- (
     imp_res_tac ALOOKUP_MEM >>
     fs[EVERY_MEM,FORALL_PROD] >>
     metis_tac[] ) >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   simp[num_tvs_bvl2,num_tvs_def] >>
   imp_res_tac generalise_subst>>
   `t_walkstar last_sub t'''' = infer_subst b (t_walkstar s t'''')` by
     (fs[MAP_MAP_o,LIST_EQ_REWRITE,EL_MAP,infer_subst_FEMPTY]>>
     imp_res_tac ALOOKUP_MEM>>
     fs[MEM_EL]>>
     metis_tac[SND])>>
   fs[sub_completion_def]>>
   Q.ISPECL_THEN [`tvs`,`s'`] mp_tac (GEN_ALL generalise_subst_exist)>>discharge_hyps
   >-
     (fs[]>>
     `t_wfs FEMPTY` by fs[t_wfs_def]>>
     imp_res_tac infer_e_wfs>>
     imp_res_tac infer_p_wfs>>
     imp_res_tac t_unify_wfs>>
     rfs[]>>
     metis_tac[pure_add_constraints_wfs])
   >>
     rw[]>>
     pop_assum (qspecl_then[`MAP (t_walkstar s) (MAP SND tenv')`,`[]`,`FEMPTY`,`a`,`b`,`MAP (t_walkstar last_sub) (MAP SND tenv')`] mp_tac)>>
     discharge_hyps_keep
     >-
       (fs[]>>
       imp_res_tac (infer_e_check_t |>CONJUNCT1)>>
       fs[check_env_def]>>rfs[]>>
       first_assum (mp_tac o (MATCH_MP (infer_e_check_s|>CONJUNCT1|>ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO])))>>
       simp[t_wfs_def]>>
       disch_then (qspec_then`0` mp_tac)>>
       discharge_hyps>-
         fs[check_env_def,check_s_def,check_cenv_tenvC_ok]>>
       strip_tac>>fs[check_s_def]>>
       imp_res_tac (infer_p_check_t |> CONJUNCT1)>>
       first_assum (mp_tac o (MATCH_MP (infer_p_check_s|>CONJUNCT1|>ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO])))>>
       disch_then(qspec_then`0` mp_tac)>>
       discharge_hyps>-
         (fs[check_env_def,check_s_def,check_cenv_tenvC_ok]>>
         imp_res_tac infer_e_wfs>>
         fs[t_wfs_def])
       >>
       strip_tac>>
       fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
       fs[GSYM FORALL_AND_THM]>>fs[GSYM IMP_CONJ_THM]>>
       ntac 2 strip_tac>>
       CONJ_ASM2_TAC>-
         metis_tac[check_t_t_vars]
       >>
       first_x_assum (qspec_then `y'` assume_tac)>>rfs[]>>
       fs[UNCURRY]>>
       match_mp_tac t_walkstar_check>> fs[]>>
       reverse CONJ_TAC>-
         (match_mp_tac (check_t_more5|>CONJUNCT1|>MP_CANON)>>
         HINT_EXISTS_TAC>>
         fs[])
       >>
       match_mp_tac (check_s_more3 |> MP_CANON)>>
       qexists_tac `count st'.next_uvar`>>
       fs[]>>
       match_mp_tac t_unify_check_s>>
       CONV_TAC (STRIP_QUANT_CONV (lift_conjunct_conv is_eq)) >>
       first_assum (match_exists_tac o concl)>>
       fs[]>>CONJ_TAC>-
         (match_mp_tac (check_t_more5|>CONJUNCT1|>MP_CANON)>>
         qexists_tac`count st.next_uvar`>>
         fs[]>>
         imp_res_tac infer_e_next_uvar_mono>>
         imp_res_tac infer_p_next_uvar_mono>>
         fs[SUBSET_DEF]>>
         DECIDE_TAC)
       >>
       `t_wfs FEMPTY` by fs[t_wfs_def]>>
       imp_res_tac infer_p_wfs >>
       imp_res_tac infer_e_wfs>>fs[])
    >>
       rw[]>>
       qexists_tac`subst'`>>fs[]>>
       CONJ_ASM1_TAC>-
         fs[EVERY_MEM]
       >>
       Q.ISPECL_THEN [`s'`,`b`,`subst'`,`tvs`,`count st'.next_uvar`] mp_tac (GEN_ALL infer_deBruijn_subst_infer_subst_walkstar)>>
       discharge_hyps>-
         (fs[SUBSET_DEF]>>
         rw[]>>
         fs[IN_FRANGE]>>
         metis_tac[pure_add_constraints_wfs])>>
       rw[]>>
       pop_assum kall_tac>>
       pop_assum(qspec_then `t_walkstar s t''''` mp_tac)>>
       discharge_hyps>-
         (
         imp_res_tac infer_p_check_t>>
         fs[EXTENSION,SUBSET_DEF]>>
         fs[MEM_MAP,PULL_EXISTS]>>
         imp_res_tac ALOOKUP_MEM>>
         fs[FORALL_PROD,EXISTS_PROD]>>
         CONJ_TAC>-
           metis_tac[]>>
         reverse CONJ_TAC>-
           metis_tac[]
         >>
         fs[EVERY_MAP,MAP_MAP_o,EVERY_MEM,UNCURRY]>>
         `t'''' = SND (x,t'''')` by fs[]>>
         metis_tac[])
       >>
       rw[]>>
       metis_tac[pure_add_constraints_wfs,t_walkstar_SUBMAP,pure_add_constraints_success])
 (* Non generalised let *)
 >- (
     simp[PULL_EXISTS] >>
     (infer_pe_complete
      |> CONV_RULE(LAND_CONV(lift_conjunct_conv(same_const``type_e`` o fst o strip_comb)))
      |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
      |> GEN_ALL
      |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
     simp[num_tvs_bvl2,num_tvs_def] >>
     simp[GSYM AND_IMP_INTRO]>>
     disch_then(fn th => first_assum(mp_tac o MATCH_MP th))>>
     disch_then(qspecl_then[`menv`,`itenv`] mp_tac)>>
     simp[AND_IMP_INTRO]>>
     discharge_hyps >- (
       fs[tenv_alpha_def,check_env_def] ) >>
     strip_tac >> simp[] >>
     imp_res_tac infer_p_bindings >>
     pop_assum (qspecl_then [`[]`] assume_tac) >>
     fs [] >>
     (type_pe_determ_infer_e
      |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(same_const``type_pe_determ`` o fst o strip_comb))))
      |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
      |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
     simp[num_tvs_bvl2,num_tvs_def] >>
     simp[GSYM AND_IMP_INTRO] >>
     disch_then (fn th => first_assum(mp_tac o MATCH_MP th)) >>
     disch_then (fn th => first_assum(mp_tac o MATCH_MP th)) >>
     disch_then (fn th => first_assum(mp_tac o MATCH_MP th)) >>
     simp[check_env_def] >>
     discharge_hyps >- fs[tenv_alpha_def] >>
     strip_tac >>
     `EVERY (check_t 0 {}) (MAP (t_walkstar s) (MAP SND tenv'))` by (
       simp[EVERY_MAP,LAMBDA_PROD] ) >>
     imp_res_tac generalise_no_uvars >>
     pop_assum (qspecl_then [`FEMPTY`, `0`, `init_infer_state.next_uvar`] mp_tac) >>
     simp[MAP_MAP_o,ZIP_MAP,combinTheory.o_DEF] >>
     disch_then kall_tac >>
     simp[EVERY_MAP,LAMBDA_PROD,UNCURRY,FST_pair] >>
     reverse conj_tac >- (
       simp[tenv_add_tvs_def,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
       imp_res_tac type_p_pat_bindings >> fs[] ) >>
     simp[tenv_alpha_def] >>
     conj_tac >- (
       simp[tenv_inv_def,ALOOKUP_MAP,PULL_EXISTS,GSYM bvl2_lookup,tenv_add_tvs_def] >>
       rw[] >> fs[simp_tenv_invC_def] >>
       res_tac >> res_tac >> simp[] >>
       reverse IF_CASES_TAC >- (
         fs[EVERY_MEM,FORALL_PROD] >>
         imp_res_tac ALOOKUP_MEM >>
         metis_tac[] ) >>
       simp[LENGTH_NIL] >>
       simp[deBruijn_subst_nothing] >>
       fs[] >> rw[] >>
       fs[sub_completion_def]>>
       imp_res_tac pure_add_constraints_success>>
       qpat_assum `unconvert_t t = B` (assume_tac o Q.AP_TERM `convert_t`) >>
       imp_res_tac t_walkstar_SUBMAP>>
       first_x_assum(qspec_then `p2` SUBST_ALL_TAC)>>
       metis_tac[check_freevars_empty_convert_unconvert_id,t_walkstar_no_vars])>>
     simp[tenv_invC_def,GSYM bvl2_lookup,tenv_add_tvs_def,PULL_EXISTS,ALOOKUP_MAP] >>
     rw[] >>
     qexists_tac`0` >>
     fs[simp_tenv_invC_def] >>
     res_tac >> res_tac >> simp[] >>
     reverse IF_CASES_TAC >- (
       fs[EVERY_MEM,FORALL_PROD] >>
       imp_res_tac ALOOKUP_MEM >>
       metis_tac[] ) >>
     simp[LENGTH_NIL,infer_deBruijn_subst_id] >>
     fs[sub_completion_def]>>
     imp_res_tac pure_add_constraints_success>>
     qpat_assum `unconvert_t t = B` (assume_tac o Q.AP_TERM `convert_t`) >>
     imp_res_tac t_walkstar_SUBMAP>>
     first_x_assum(qspec_then `t''''` SUBST_ALL_TAC)>>
     metis_tac[check_freevars_empty_convert_unconvert_id,t_walkstar_no_vars])
 (* generalised letrec *)
 >- (
   simp[PULL_EXISTS] >>
   (infer_funs_complete
    |> REWRITE_RULE[GSYM AND_IMP_INTRO] |> GEN_ALL
    |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
   fs[tenv_alpha_def,check_env_def]>>
   rpt (disch_then (fn th=> first_assum (mp_tac o MATCH_MP th)))>>
   rw[]>>
   fs[init_infer_state_def]>>
   qexists_tac`st'`>>fs[]>>
   imp_res_tac type_funs_distinct >> fs[FST_triple] >> imp_res_tac type_funs_MAP_FST >>
   imp_res_tac type_funs_Tfn>>
   simp[init_infer_state_def,ETA_AX] >>
   imp_res_tac infer_funs_length>>
   fs[sub_completion_def,LENGTH_COUNT_LIST]>>
   qho_match_abbrev_tac`∃a b c. tr = (a,b,c) ∧ Q a b c` >>
   `∃a b c. tr = (a,b,c)` by metis_tac[pair_CASES] >> simp[] >> fs[Abbr`Q`,Abbr`tr`] >>
   first_assum(mp_tac o MATCH_MP(
     generalise_complete
     |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(is_eq))))
     |> REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
   disch_then(qspec_then`st'.next_uvar`mp_tac) >>
   simp[AND_IMP_INTRO] >>
   discharge_hyps >- (
     fs[check_s_def]>>
     simp[EVERY_MAP,check_t_def] >>
     simp[EVERY_MEM,MEM_COUNT_LIST] >>
     imp_res_tac (last(CONJUNCTS infer_e_next_uvar_mono)) >>
     fs[]>>rw[]>- DECIDE_TAC >>
     `t_wfs FEMPTY` by fs[t_wfs_def]>>
     imp_res_tac infer_e_wfs>>
     rfs[]>>
     metis_tac[pure_add_constraints_wfs]) >>
   strip_tac >>
   rw[]
   >-
     (
     qpat_assum `pure_add_constraints st.subst A st'.subst` mp_tac>>
     qpat_abbrev_tac `ls:(infer_t,infer_t)alist = ZIP (A,B)`>>
     strip_tac>>
     qabbrev_tac`tenv_new = bind_var_list 0 (MAP2 (λ(f,x,e) t. (f,t)) funs (MAP
     (convert_t o (t_walkstar last_sub) o Infer_Tuvar) (COUNT_LIST (LENGTH funs)))) (bind_tvar a (bind_var_list2 tenv_v Empty))`>>
     `tenv.c = (tenv with v := tenv_new).c` by rw [] >>
     full_simp_tac (std_ss) [] >>
     first_assum (mp_tac o MATCH_MP (infer_e_sound |> CONJUNCTS |> last |> SIMP_RULE (srw_ss()) [Once (GSYM AND_IMP_INTRO)]))>>
     fs[check_cenv_tenvC_ok]>>
     disch_then (qspecl_then [`ls++ec1`,`last_sub`] mp_tac)>>
     discharge_hyps>-
      (
      fs[sub_completion_def,num_tvs_bind_var_list,bind_tvar_rewrites,num_tvs_bvl2,num_tvs_def,check_env_def]>>
      rw[]
      >-
        fs[t_wfs_def]
      >-
        (fs[MAP2_MAP,LENGTH_COUNT_LIST,EVERY_MAP,EVERY_MEM,MEM_MAP,MEM_ZIP,PULL_EXISTS,EL_MAP,EL_COUNT_LIST,UNCURRY]>>
        rw[check_t_def])
      >-
        (fs[EVERY_MEM]>>rw[]>>res_tac>>PairCases_on`e`>>fs[]>>
        metis_tac[check_t_more])
      >-
        metis_tac[pure_add_constraints_append]
      >-
        fs[Abbr`tenv_new`,num_tvs_bind_var_list,bind_tvar_rewrites,num_tvs_bvl2,num_tvs_def]
      >>
        fs[Abbr`tenv_new`]>>
        match_mp_tac tenv_inv_letrec_merge2>>
        qexists_tac`funs`>>fs[]>>
        qexists_tac`bind_tvar a (bind_var_list2 tenv_v Empty)`>>
        fs[combinTheory.o_DEF]>>
        metis_tac[tenv_inv_empty_to,tenv_inv_extend_tvar_empty_subst,check_env_def])
     >>
     simp[Abbr`tenv_new`]>>
     qpat_abbrev_tac2 `funs_ls1 = list$MAP2 A B C`>>
     qpat_abbrev_tac2 `funs_ls2 = list$MAP2 A B C`>>
     `funs_ls1 = funs_ls2` by
       (simp[Abbr`funs_ls1`,Abbr`funs_ls2`,MAP2_MAP,LENGTH_COUNT_LIST,LIST_EQ_REWRITE,PULL_EXISTS,EL_MAP,EL_ZIP,EL_COUNT_LIST]>>rw[]>>
       simp[UNCURRY]>>
       AP_TERM_TAC>>
       `t_wfs st.subst` by (
         imp_res_tac(last(CONJUNCTS infer_e_wfs)) >>
         pop_assum mp_tac >> discharge_hyps >- simp[t_wfs_def] >>
         rw[] ) >>
       `t_compat st'.subst last_sub` by (
         imp_res_tac pure_add_constraints_wfs >>
         metis_tac[sub_completion_def,pure_add_constraints_success,SUBMAP_t_compat] ) >>
       fs[t_compat_def]>>
       imp_res_tac t_compat_pure_add_constraints_2 >>
       pop_assum mp_tac >>
       simp[EVERY_MEM,Abbr`ls`,MEM_ZIP,LENGTH_COUNT_LIST,PULL_EXISTS,EL_MAP,EL_COUNT_LIST] >>
       metis_tac[])>>
    rw[] >>
    first_x_assum(qspecl_then [`a`,`funs_ls1`] assume_tac)>>rfs[]>>
    fs[weakE_def,tenv_inv_def]>>rw[]>>
    fs[lookup_bvl2]>>
    first_x_assum(qspec_then`x` assume_tac)>>
    Cases_on`ALOOKUP (tenv_add_tvs a funs_ls1) x`
    >-
      (imp_res_tac ALOOKUP_FAILS >>
      unabbrev_all_tac>>
      imp_res_tac ALOOKUP_MEM>>
      rfs[MAP2_MAP,LENGTH_COUNT_LIST,tenv_add_tvs_def,MEM_MAP,FORALL_PROD,MEM_ZIP,EXISTS_PROD,EL_MAP,EL_COUNT_LIST,UNCURRY]>>
      metis_tac[FST,PAIR])
    >>
    PairCases_on`x'`>>
    fs[]>>
    CASE_TAC>>fs[]>>
    PairCases_on`x'`>>fs[]>>
    fs[deBruijn_inc0]>>
    reverse IF_CASES_TAC >- (
      imp_res_tac ALOOKUP_MEM >>
      pop_assum mp_tac >>
      simp[MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
      simp[MEM_ZIP,PULL_EXISTS,LENGTH_COUNT_LIST] >> rpt gen_tac >> strip_tac >>
      pop_assum mp_tac >>
      simp[EL_MAP,LENGTH_COUNT_LIST,t_walkstar_FEMPTY,EL_COUNT_LIST] >>
      strip_tac >> var_eq_tac >>
      fs[sub_completion_def] >>
      `n ∈ FDOM last_sub` by (
        fs[SUBSET_DEF] >>
        first_x_assum match_mp_tac >>
        imp_res_tac (last(CONJUNCTS infer_e_next_uvar_mono)) >>
        fs[] >> DECIDE_TAC ) >>
      metis_tac[] ) >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    `tvs' = a ∧ x'0 = a` by (
      imp_res_tac ALOOKUP_MEM >>
      ntac 2 (pop_assum mp_tac) >>
      simp[tenv_add_tvs_def] >>
      simp[MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,PULL_EXISTS,EXISTS_PROD] ) >>
    rpt var_eq_tac >> simp[] >>
    imp_res_tac ALOOKUP_MEM >>
    ntac 2 (pop_assum mp_tac) >>
    simp[MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,PULL_EXISTS,EXISTS_PROD,tenv_add_tvs_def] >>
    qunabbrev_tac`funs_ls1` >>
    rator_x_assum`Abbrev`mp_tac >>
    simp[markerTheory.Abbrev_def] >>
    simp[MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
    simp[Once LIST_EQ_REWRITE] >>
    simp[LENGTH_COUNT_LIST,EL_MAP,EL_ZIP,UNCURRY,MEM_ZIP,PULL_EXISTS,EL_COUNT_LIST] >>
    strip_tac >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    Q.ISPEC_THEN`MAP FST funs`(mp_tac o fst o EQ_IMP_RULE) EL_ALL_DISTINCT_EL_EQ >>
    discharge_hyps >- simp[] >>
    qpat_assum`MAP  FST X = Y`kall_tac >>
    simp[EL_MAP] >>
    metis_tac[FST,PAIR,PAIR_EQ] )
   >- (
   simp[tenv_invC_def] >>
   simp[LAMBDA_PROD,ALOOKUP_MAP,PULL_EXISTS,GSYM bvl2_lookup] >>
   rw[] >>
   pop_assum mp_tac >>
   simp[tenv_add_tvs_def,ALOOKUP_MAP] >> strip_tac >>
   first_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
   simp[num_tvs_bind_var_list,bind_tvar_rewrites,num_tvs_bvl2,num_tvs_def] >>
   strip_tac >> simp[] >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   rpt var_eq_tac >>
   qmatch_assum_abbrev_tac`check_freevars tvs [] t` >>
   simp[MAP2_MAP,LENGTH_COUNT_LIST,ZIP_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
   qpat_abbrev_tac2`ls = MAP X Z` >>
   Cases_on`ALOOKUP ls x` >- (
     imp_res_tac ALOOKUP_FAILS >>
     fs[Abbr`ls`] >> pop_assum mp_tac >>
     simp[MEM_MAP] >>
     imp_res_tac ALOOKUP_MEM >>
     `MEM x (MAP FST bindings)` by metis_tac[MEM_MAP,FST] >>
     `MEM x (MAP FST funs)` by metis_tac[] >>
     pop_assum mp_tac >>
     simp[MEM_MAP,EXISTS_PROD,MEM_ZIP,LENGTH_COUNT_LIST,MEM_EL] ) >>
   PairCases_on`x'`>>simp[] >>
   imp_res_tac ALOOKUP_MEM >>
   pop_assum kall_tac >>
   pop_assum mp_tac >>
   simp[Abbr`ls`,MEM_MAP,PULL_EXISTS] >>
   gen_tac >> strip_tac >>
   reverse IF_CASES_TAC >- (
     `F` suffices_by rw[] >> pop_assum mp_tac >>
     simp[] >>
     fs[sub_completion_def] >>
     first_x_assum match_mp_tac >>
     pop_assum mp_tac >>
     simp[MEM_ZIP,LENGTH_COUNT_LIST,PULL_EXISTS,EL_COUNT_LIST] >>
     fs[SUBSET_DEF] >>
     imp_res_tac (last(CONJUNCTS infer_e_next_uvar_mono)) >>
     fs[] >> rw[] >>
     first_x_assum match_mp_tac >>
     DECIDE_TAC ) >>
   fs[sub_completion_def]>>
   Q.ISPECL_THEN [`tvs`,`s`] mp_tac (GEN_ALL generalise_subst_exist)>>
   discharge_hyps >-
     (fs[]>>
     `t_wfs FEMPTY` by fs[t_wfs_def]>>
     imp_res_tac infer_e_wfs>>
     imp_res_tac infer_p_wfs>>
     imp_res_tac t_unify_wfs>>
     rfs[]>>
     metis_tac[pure_add_constraints_wfs])
   >>
   disch_then(strip_assume_tac o CONJUNCT2) >>
   pop_assum(fn th => (first_assum(
     mp_tac o MATCH_MP(ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO](CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(can(match_term``X = (a,b,c)``)))))th))))) >>
   simp[LENGTH_NIL] >>
   `t_wfs st'.subst` by
     (imp_res_tac infer_e_wfs>>
        fs[]>>
        pop_assum mp_tac>>discharge_hyps>-fs[t_wfs_def]>>
        metis_tac[pure_add_constraints_wfs])>>
   discharge_hyps_keep >-
      (CONJ_ASM1_TAC>-
      (fs[EVERY_MAP,EVERY_MEM,MEM_COUNT_LIST]>>
      rw[]>>match_mp_tac t_walkstar_check >>
      rw[]
      >-
        (match_mp_tac (check_s_more3|>MP_CANON)>>
        qexists_tac`count st'.next_uvar`>>fs[])
      >-
        (fs[check_t_def]>>
        imp_res_tac infer_e_next_uvar_mono>>
        fs[]>>DECIDE_TAC))
      >>
      fs[EVERY_MAP,EVERY_MEM]>>rw[]>>
      metis_tac[check_t_t_vars])
   >>
   rw[]>>
   qexists_tac`subst'`>>simp[] >>
   CONJ_ASM1_TAC>- fs[EVERY_MEM] >>
   imp_res_tac generalise_subst>>
   PairCases_on`p`>>fs[]>>
   `MEM p3 (COUNT_LIST (LENGTH funs_ts))` by
     rfs[MEM_ZIP,LENGTH_COUNT_LIST,EL_COUNT_LIST,MEM_COUNT_LIST]>>
   `t_walkstar last_sub (Infer_Tuvar p3) = infer_subst b (t_walkstar st'.subst (Infer_Tuvar p3))` by
     (fs[MAP_MAP_o,LIST_EQ_REWRITE,EL_MAP,infer_subst_FEMPTY,EL_COUNT_LIST]>>
     first_x_assum(qspec_then `p3` mp_tac)>>
     fs[LENGTH_COUNT_LIST,MEM_COUNT_LIST]>>
     rfs[EL_COUNT_LIST])>>
    fs[]>>
    Q.ISPECL_THEN [`s`,`b`,`subst'`,`tvs`,`count st'.next_uvar`] mp_tac (GEN_ALL infer_deBruijn_subst_infer_subst_walkstar)>>
     discharge_hyps>-
       (fs[SUBSET_DEF]>>
       rw[]>>
       fs[IN_FRANGE]>>
       metis_tac[pure_add_constraints_wfs])
     >>
     rw[]>>
     pop_assum kall_tac>>
     pop_assum(qspec_then `t_walkstar st'.subst (Infer_Tuvar p3)` mp_tac)>>
     discharge_hyps>-
       (
       fs[EXTENSION,SUBSET_DEF]>>
       fs[MEM_MAP,PULL_EXISTS]>>
       imp_res_tac ALOOKUP_MEM>>
       fs[FORALL_PROD,EXISTS_PROD]>>
       CONJ_TAC>-
         metis_tac[]>>
       reverse CONJ_TAC>-
         metis_tac[]
       >>
       fs[EVERY_MEM,MEM_MAP,MAP_MAP_o,UNCURRY]>>
       metis_tac[])
     >>
     rw[]>>
     imp_res_tac ALOOKUP_MEM>>
     `MAP (t_walkstar s) funs_ts =
      MAP (t_walkstar s o Infer_Tuvar) (COUNT_LIST (LENGTH funs_ts))` by
       (
       simp[LENGTH_COUNT_LIST,LIST_EQ_REWRITE,PULL_EXISTS,EL_MAP,EL_ZIP,EL_COUNT_LIST]>>rw[]>>
       `t_wfs st.subst` by (
         imp_res_tac(last(CONJUNCTS infer_e_wfs)) >>
         fs[t_wfs_def])>>
       `t_compat st'.subst s` by (
         imp_res_tac pure_add_constraints_wfs >>
         metis_tac[sub_completion_def,pure_add_constraints_success,SUBMAP_t_compat] ) >>
       fs[t_compat_def]>>
       imp_res_tac t_compat_pure_add_constraints_2 >>
       pop_assum kall_tac>>pop_assum mp_tac >>
       simp[EVERY_MEM,MEM_ZIP,LENGTH_COUNT_LIST,PULL_EXISTS,EL_MAP,EL_COUNT_LIST] >>
       metis_tac[])>>
     `(p0,t) = EL p3 bindings ∧ t = EL p3 (MAP SND bindings)` by
       (fs[MEM_EL,EL_COUNT_LIST,LENGTH_COUNT_LIST]>>
       `p0 = EL n''' (MAP FST bindings)` by
         (fs[EL_MAP]>>metis_tac[FST])>>
       qpat_assum` A = EL n B` mp_tac>>
       `n < LENGTH funs` by metis_tac[LENGTH_ZIP,LENGTH_COUNT_LIST]>>
       simp[EL_ZIP,EL_COUNT_LIST,LENGTH_COUNT_LIST,LENGTH_ZIP,PAIR]>>
       strip_tac>>
       `n = n'''` by
         (`EL n''' (MAP FST bindings) = EL n (MAP FST funs)` by
           (fs[EL_MAP]>>metis_tac[FST])>>
         `n''' < LENGTH funs_ts` by
           metis_tac[LENGTH_MAP]>>
        Q.ISPEC_THEN`MAP FST funs`(mp_tac o fst o EQ_IMP_RULE) EL_ALL_DISTINCT_EL_EQ >>
        rw[EQ_IMP_THM]>>
        pop_assum(qspecl_then [`n`,`n'''`] assume_tac)>>rfs[LENGTH_MAP])
       >>
       `t = EL n''' (MAP SND bindings)` by
         (simp[EL_MAP]>>
         metis_tac[SND])>>
       fs[])>>
     fs[EL_MAP,MEM_COUNT_LIST]>>
     qpat_assum`MAP A B = MAP C D` mp_tac>>
     fs[LIST_EQ_REWRITE,LENGTH_COUNT_LIST]>>
     disch_then (qspec_then`p3` assume_tac)>>rfs[EL_MAP]>>
     fs[EL_MAP,LENGTH_COUNT_LIST]>>
     simp[EL_COUNT_LIST]>>
     `p3 < st'.next_uvar` by
       (imp_res_tac infer_e_next_uvar_mono>>
       fs[]>>DECIDE_TAC)>>
     metis_tac[pure_add_constraints_wfs,t_walkstar_SUBMAP,pure_add_constraints_success,check_t_empty_unconvert_convert_id])
   >-
     (simp[MAP2_MAP,LENGTH_COUNT_LIST,ZIP_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
     simp[GSYM combinTheory.o_DEF,MAP_ZIP,LENGTH_COUNT_LIST] >>
     simp[tenv_add_tvs_def,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] )
   >>
     simp[MAP2_MAP,LENGTH_COUNT_LIST,ZIP_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
     simp[EVERY_MAP] >>
     simp[EVERY_MEM,MEM_ZIP,LENGTH_COUNT_LIST,PULL_EXISTS,EL_COUNT_LIST] >>
     fs[sub_completion_def] >>
     rw[] >>
     first_x_assum match_mp_tac >>
     fs[SUBSET_DEF] >>
     first_x_assum match_mp_tac >>
     imp_res_tac infer_e_next_uvar_mono >>
     fs[]>>
     DECIDE_TAC)
(* Type definition *)
 >- (rw [PULL_EXISTS] >>
     Cases_on `tenv.t` >>
     fs [merge_mod_env_def, EVERY_MAP, EVERY_MEM, DISJOINT_DEF, EXTENSION] >>
     rw []
     >- (PairCases_on `x` >>
         fs [] >>
         CCONTR_TAC >>
         fs [METIS_PROVE [] ``x ∨ y ⇔ ~y ⇒ x``] >>
         res_tac >>
         fs [MEM_MAP, LAMBDA_PROD, FORALL_PROD, EXISTS_PROD] >>
         metis_tac [])
     >- (fs[tenv_alpha_empty]))
 (* Exception definition *)
 >- fs[tenv_alpha_empty]
 >- metis_tac []
 >- fs[tenv_alpha_empty]);

val infer_ds_complete = prove(``
!ds mn mdecls tdecls edecls menv decls' tenvT' cenv' tenv tenv' st itenv tenv_v.
  check_menv menv ∧
  tenv_mod_ok tenv.m ∧
  tenv_val_ok (bind_var_list2 tenv_v Empty) ∧
  check_env ∅ itenv ∧
  tenv_ctor_ok tenv.c ∧
  tenv_tabbrev_ok tenv.t ∧
  type_ds T mn <|defined_mods := set mdecls; defined_types := set tdecls; defined_exns := set edecls|> (tenv with v := bind_var_list2 tenv_v Empty) ds decls' tenvT' cenv' tenv' ∧
  tenv_alpha itenv (bind_var_list2 tenv_v Empty) ∧
  menv_alpha menv tenv.m
  ⇒
  ?st' mdecls'' tdecls'' edecls'' itenv'.
    set mdecls'' = decls'.defined_mods ∧
    set tdecls'' = decls'.defined_types ∧
    set edecls'' = decls'.defined_exns ∧
    infer_ds mn (mdecls,tdecls,edecls) tenv.t menv tenv.c itenv ds st =
      (Success ((mdecls'',tdecls'',edecls''), tenvT', cenv', itenv'), st') ∧
    (*for induction*)
    tenv_alpha itenv' (bind_var_list2 tenv' Empty) ∧
    MAP FST itenv' = MAP FST tenv' ∧
    (*maybe implied as well*)
    check_env ∅ itenv'``,
  Induct>-
  (rw [Once type_ds_cases, infer_ds_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def,empty_decls_def,check_env_def]>>
  fs[tenv_alpha_def,bind_var_list2_def,tenv_invC_def,lookup_tenv_val_def,tenv_inv_def])
  >>
  rw [Once type_ds_cases, infer_ds_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def,empty_decls_def,check_env_def]>>
  fs[]>>
  fs[empty_decls_def] >>
    (infer_d_complete|>
      CONV_RULE(
        STRIP_QUANT_CONV(LAND_CONV(
          lift_conjunct_conv(same_const``type_d`` o fst o strip_comb))))
    |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
    |> (fn th => first_assum(mp_tac o MATCH_MP th)))>>
  disch_then (Q.ISPECL_THEN [`menv`,`st`,`itenv`] mp_tac)>>
  discharge_hyps>-
    fs[check_env_def]>>
  rw[]>>
  fs[PULL_EXISTS]>>
  fs[GSYM AND_IMP_INTRO]>>
  first_x_assum(fn th => first_x_assum (mp_tac o MATCH_MP th))>>
  qmatch_assum_abbrev_tac`type_ds _ _ _ tenv' ds _ _ _ _` >>
  `tenv_ctor_ok tenv'.c` by
    (fs[tenv_ctor_ok_merge,Abbr`tenv'`]>>
    imp_res_tac type_d_ctMap_ok >>
    match_mp_tac ctMap_ok_tenvC_ok >> rfs[] >>
    metis_tac[MAP_REVERSE,ALL_DISTINCT_REVERSE])>>
  `tenv_tabbrev_ok tenv'.t` by
    (fs[Abbr`tenv'`]>>
     match_mp_tac tenv_tabbrev_ok_merge>>
    fs[typeSoundInvariantsTheory.tenv_tabbrev_ok_def]>>
    simp[FEVERY_FEMPTY] >>
    imp_res_tac (REWRITE_RULE[GSYM AND_IMP_INTRO]type_d_tenvT_ok) >> rfs[])>>
  fs[GSYM bind_var_list2_append]>>
  FULL_SIMP_TAC bool_ss [UNION_APPEND,union_decls_def] >>
  `tenv_alpha (itenv'++itenv) (bind_var_list2 (tenv''++tenv_v) Empty)` by
     metis_tac[tenv_alpha_bind_var_list2]>>
  `check_env {} (itenv'++itenv)` by
    fs[check_env_def]>>
  `tenv_val_ok (bind_var_list2 (tenv''++tenv_v) Empty)` by
    (fs[bind_var_list2_append]>>
    match_mp_tac tenv_val_ok_bvl2>>
    fs[typeSoundInvariantsTheory.tenv_val_ok_def,tenv_val_ok_bind_var_list2]>>
    match_mp_tac (INST_TYPE [alpha|->``:'a->bool``,beta|->alpha] type_d_tenv_ok)>>
    first_assum (match_exists_tac o concl)>>
    first_assum (match_exists_tac o concl)>>
    fs[num_tvs_bvl2,num_tvs_def])>>
  `tenv' = tenv' with v := bind_var_list2 (tenv'' ++ tenv_v) Empty` by simp[Abbr`tenv'`] >>
  rator_x_assum`type_ds`mp_tac >> pop_assum SUBST1_TAC >> strip_tac >>
  `tenv_mod_ok tenv'.m` by simp[Abbr`tenv'`] >>
  `menv_alpha menv tenv'.m` by simp[Abbr`tenv'`] >>
  rpt (qpat_assum`set _ = _`(mp_tac o SYM)) >> ntac 3 strip_tac >>
  fs[] >> FULL_SIMP_TAC bool_ss [UNION_APPEND] >>
  rpt
   (disch_then (fn th => first_x_assum (mp_tac o MATCH_MP th)))>>
  disch_then (qspec_then `st'` strip_assume_tac)>>
  fs[append_decls_def]>>
  fs[Abbr`tenv'`,check_env_def]>>
  metis_tac[tenv_alpha_bind_var_list2])

(*TODO move to miscLib*)
fun any_match_mp impth th =
  let
    val h = impth |> concl |> strip_forall |>snd |> dest_imp |> fst |>strip_conj
    val c = first(can (C match_term (concl th))) h
    val th2 = impth
      |> CONV_RULE (STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv (equal c))))
      |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
  in
    MATCH_MP th2 th  end

(* TODO: move? *)
val check_freevars_t_to_freevars = store_thm("check_freevars_t_to_freevars",
  ``(∀t fvs (st:'a). check_freevars 0 fvs t ⇒
      ∃fvs' st'. t_to_freevars t st = (Success fvs', st') ∧ set fvs' ⊆ set fvs) ∧
    (∀ts fvs (st:'a). EVERY (check_freevars 0 fvs) ts ⇒
      ∃fvs' st'. ts_to_freevars ts st = (Success fvs', st') ∧ set fvs' ⊆ set fvs)``,
  Induct >> simp[check_freevars_def,t_to_freevars_def,PULL_EXISTS,success_eqns] >>
  simp_tac(srw_ss()++boolSimps.ETA_ss)[] >> simp[] >> metis_tac[])

val infer_type_subst_nil = store_thm("infer_type_subst_nil",
  ``(∀t. check_freevars n [] t ⇒ infer_type_subst [] t = unconvert_t t) ∧
    (∀ts. EVERY (check_freevars n []) ts ⇒ MAP (infer_type_subst []) ts = MAP unconvert_t ts)``,
  ho_match_mp_tac(TypeBase.induction_of(``:t``)) >>
  rw[infer_type_subst_def,convert_t_def,unconvert_t_def,check_freevars_def] >>
  fsrw_tac[boolSimps.ETA_ss][])

val check_freevars_more = store_thm("check_freevars_more",
  ``∀a b c. check_freevars a b c ⇒ ∀b'. set b ⊆ set b' ⇒ check_freevars a b' c``,
  ho_match_mp_tac check_freevars_ind >>
  rw[check_freevars_def] >-
    fs[SUBSET_DEF] >>
  fs[EVERY_MEM])
(* -- *)

val t_ind = t_induction
  |> Q.SPECL[`P`,`EVERY P`]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) []
  |> Q.GEN`P`

val rename_lemma = store_thm("rename_lemma",
  ``∀t fvs fvs'.
    check_freevars 0 fvs' t ∧
    set fvs' ⊆ set fvs ∧
    ALL_DISTINCT fvs'
    ⇒
    deBruijn_subst 0 (MAP (λfv. the (Tapp [] ARB) (OPTION_MAP Tvar_db (find_index fv fvs' 0))) fvs)
      (type_subst (alist_to_fmap (ZIP (fvs, MAP Tvar_db (GENLIST I (LENGTH fvs))))) t) =
    convert_t
      (infer_type_subst
        (ZIP (fvs', MAP Infer_Tvar_db (GENLIST I (LENGTH fvs')))) t)``,
  ho_match_mp_tac t_ind >>
  conj_tac >- (
    simp[check_freevars_def,infer_type_subst_def,type_subst_def] >>
    rw[] >>
    CASE_TAC >- (
      imp_res_tac ALOOKUP_FAILS >>
      pop_assum mp_tac >>
      simp[MEM_ZIP] >>
      fs[MEM_EL,SUBSET_DEF] >>
      metis_tac[] ) >>
    CASE_TAC >- (
      imp_res_tac ALOOKUP_FAILS >>
      pop_assum mp_tac >>
      simp[MEM_ZIP] >>
      fs[MEM_EL,SUBSET_DEF] >>
      metis_tac[] ) >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_ZIP] >> rw[] >>
    simp[EL_MAP] >>
    simp[convert_t_def,deBruijn_subst_def] >>
    simp[EL_MAP,the_def] ) >>
  conj_tac >- (
    simp[check_freevars_def,infer_type_subst_def] ) >>
  rw[infer_type_subst_def,deBruijn_subst_def,type_subst_def,convert_t_def] >>
  simp[MAP_MAP_o] >>
  simp[MAP_EQ_f] >>
  fs[EVERY_MEM,check_freevars_def])

val rename_lemma2 = store_thm("rename_lemma2",
  ``∀t fvs fvs'.
    check_freevars 0 fvs' t ∧
    set fvs' ⊆ set fvs ∧
    ALL_DISTINCT fvs'
    ⇒
    infer_deBruijn_subst (MAP (λfv. Infer_Tvar_db (THE (find_index fv fvs 0))) fvs')
      (infer_type_subst (ZIP (fvs', MAP Infer_Tvar_db (GENLIST I (LENGTH fvs')))) t) =
    unconvert_t
      (type_subst
        (alist_to_fmap (ZIP (fvs, MAP Tvar_db (GENLIST I (LENGTH fvs))))) t)``,
  ho_match_mp_tac t_ind >>
  conj_tac >- (
    simp[check_freevars_def,infer_type_subst_def,type_subst_def] >>
    rw[] >>
    CASE_TAC >- (
      imp_res_tac ALOOKUP_FAILS >>
      pop_assum mp_tac >>
      simp[MEM_ZIP] >>
      fs[MEM_EL,SUBSET_DEF] >>
      metis_tac[] ) >>
    CASE_TAC >- (
      imp_res_tac ALOOKUP_FAILS >>
      pop_assum mp_tac >>
      simp[MEM_ZIP] >>
      fs[MEM_EL,SUBSET_DEF] >>
      metis_tac[] ) >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_ZIP] >> rw[] >>
    simp[EL_MAP] >>
    simp[unconvert_t_def,infer_deBruijn_subst_def] >>
    simp[EL_MAP] >>
    imp_res_tac ALOOKUP_find_index_SOME >>
    rfs[EL_MAP] >>
    fs[MAP_ZIP] >>
    rfs[EL_ZIP] >>
    rfs[EL_MAP]) >>
  conj_tac >- (
    simp[check_freevars_def,infer_type_subst_def] ) >>
  rw[type_subst_def,infer_deBruijn_subst_def,infer_type_subst_def,unconvert_t_def] >>
  simp[MAP_MAP_o] >>
  simp[MAP_EQ_f] >>
  fs[EVERY_MEM,check_freevars_def])

val check_specs_complete = store_thm("check_specs_complete",
  ``∀mn tenvT specs decls tenvT'' cenv'' env''.
    type_specs mn tenvT specs decls tenvT'' cenv'' env'' ⇒
    tenv_tabbrev_ok tenvT ⇒
    ∀mdecls tdecls edecls itenvT icenv env st.
    ∃decls' env' st'.
    check_specs mn tenvT (mdecls,tdecls,edecls) itenvT icenv env specs st =
      (Success (decls',tenvT'' ⊌ itenvT,cenv'' ++ icenv,env'++env),st') ∧
    tenv_alpha env' (bind_var_list2 env'' Empty) ∧
    set(MAP FST env') = set(MAP FST env'') ∧
    set (FST decls') = decls.defined_mods ∪ set mdecls ∧
    set (FST(SND decls')) = decls.defined_types ∪ set tdecls ∧
    set (SND(SND decls')) = decls.defined_exns ∪ set edecls``,
  ho_match_mp_tac type_specs_strongind >>
  conj_tac >- (
    simp[check_specs_def,success_eqns,tenv_alpha_empty,empty_decls_def] ) >>
  conj_tac >- (
    simp[check_specs_def,success_eqns,PULL_EXISTS] >> rw[] >>
    imp_res_tac (check_freevars_t_to_freevars) >>
    pop_assum(qspec_then`st`strip_assume_tac) >> simp[] >>
    fs[]>>
    (fn g =>
      let
        val t1 = (snd g) |> strip_exists |> snd |> dest_conj |> fst |> lhs
        val (vs,b) = el 4 (fst g) |> strip_forall
        val t2 = b |> strip_exists |> snd |> dest_conj |> fst |> lhs
        val (s,_) = match_term t2 t1
      in first_x_assum(strip_assume_tac o SPECL(map (subst s) vs)) end
      g) >>
    simp[] >>
    match_mp_tac tenv_alpha_bind_var_list2 >>
    simp[] >>
    simp[bind_var_list2_def] >>
    simp[tenv_alpha_def] >>
    conj_tac >- (
      simp[tenv_inv_def,lookup_tenv_val_def,t_walkstar_FEMPTY] >>
      reverse IF_CASES_TAC >- (
        `F` suffices_by rw[] >>
        pop_assum mp_tac >> simp[] >>
        imp_res_tac t_to_freevars_check>>
        imp_res_tac check_freevars_type_name_subst>>
        Cases_on`nub fvs' = []` >- (
          fs[COUNT_LIST_def]>>
          metis_tac[infer_type_subst_empty_check,nub_eq_nil])>>
        match_mp_tac check_t_infer_type_subst_dbs >>
        first_assum(match_exists_tac o concl) >> simp[] ) >>
      simp[deBruijn_inc0] >>
      imp_res_tac check_t_to_check_freevars >>
      qspecl_then[`type_name_subst tenvT t`,`fvs`,`nub fvs'`]mp_tac rename_lemma >>
      discharge_hyps >- (
        imp_res_tac t_to_freevars_check >>
        simp[all_distinct_nub] >>
        imp_res_tac check_freevars_type_name_subst>>
        match_mp_tac (MP_CANON check_freevars_more) >>
        last_assum(match_exists_tac o concl) >>
        simp[]) >>
      qpat_abbrev_tac2`subst = MAP XX fvs` >>
      strip_tac >>fs[]>>
      reverse conj_tac >- (
        qexists_tac`subst` >>
        simp[Abbr`subst`] >>
        qpat_abbrev_tac2`I' = λx. x` >>
        `I' = I` by simp[Abbr`I'`,FUN_EQ_THM] >>
        simp[COUNT_LIST_GENLIST] >>
        simp[EVERY_MAP,EVERY_MEM] >>
        rw[] >>
        Cases_on`find_index fv (nub fvs') 0` >> rw[the_def,check_freevars_def] >>
        imp_res_tac find_index_LESS_LENGTH >> fs[] ) >>
      match_mp_tac check_freevars_subst_single>>
      fs[EVERY_MAP,EVERY_GENLIST,check_freevars_def]>>
      imp_res_tac check_freevars_type_name_subst>>
      imp_res_tac check_freevars_add>>
      `LENGTH fvs ≥ 0` by DECIDE_TAC>>
      fs[])>>
    simp[tenv_invC_def,lookup_tenv_val_def,deBruijn_inc0] >>
    conj_tac >- (
      qexists_tac`LENGTH fvs` >>
      match_mp_tac check_freevars_subst_single>>
      fs[EVERY_GENLIST,check_freevars_def,EVERY_MAP]>>
      imp_res_tac check_freevars_type_name_subst>>
      imp_res_tac check_freevars_add>>
      `LENGTH fvs ≥ 0` by DECIDE_TAC>>
      fs[])>>
    reverse IF_CASES_TAC >- (
        `F` suffices_by rw[] >>
        pop_assum mp_tac >> simp[] >>
        imp_res_tac t_to_freevars_check>>
        imp_res_tac check_freevars_type_name_subst>>
        Cases_on`nub fvs' = []` >- (
          fs[COUNT_LIST_def]>>
          metis_tac[infer_type_subst_empty_check,nub_eq_nil])>>
        match_mp_tac check_t_infer_type_subst_dbs >>
        first_assum(match_exists_tac o concl) >> simp[] )>>
    qspecl_then[`type_name_subst tenvT t`,`fvs`,`nub fvs'`]mp_tac rename_lemma2 >>
    discharge_hyps >- (
        imp_res_tac t_to_freevars_check >>
        simp[all_distinct_nub] >>
        imp_res_tac check_freevars_type_name_subst>>
        match_mp_tac (MP_CANON check_freevars_more) >>
        last_assum(match_exists_tac o concl) >>
        simp[])>>
    qpat_abbrev_tac2`subst = MAP XX fvs` >>
    strip_tac >>
    qexists_tac`subst` >>
    qpat_abbrev_tac2`I' = λx. x` >>
    `I' = I` by simp[Abbr`I'`,FUN_EQ_THM] >>
    simp[COUNT_LIST_GENLIST] >>
    simp[Abbr`subst`,EVERY_MAP,check_t_def] >>
    simp[EVERY_MEM] >>
    rw[] >>
    Cases_on`find_index fv fvs 0` >- (
      fs[GSYM find_index_NOT_MEM] >>
      fs[SUBSET_DEF] >> metis_tac[] ) >>
    imp_res_tac find_index_LESS_LENGTH >>
    fs[]) >>
  conj_tac >- (
    simp[check_specs_def,success_eqns,PULL_EXISTS] >> rw[] >>
    qpat_abbrev_tac`itenvT2:flat_tenv_tabbrev = FEMPTY |++ Z` >>
    REWRITE_TAC[GSYM FUNION_ASSOC] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    qpat_abbrev_tac`icenv2 = X ++ icenv` >>
    simp[union_decls_def]>>
    `tenv_tabbrev_ok (merge_mod_env (FEMPTY,itenvT2) tenvT)` by
      (match_mp_tac tenv_tabbrev_ok_merge>>
      fs[typeSoundInvariantsTheory.tenv_tabbrev_ok_def,FEVERY_FEMPTY,typeSoundInvariantsTheory.flat_tenv_tabbrev_ok_def,Abbr`itenvT2`]>>
      fs[FEVERY_ALL_FLOOKUP,flookup_update_list_some]>>rw[]>>
      imp_res_tac ALOOKUP_MEM>>
      fs[MEM_MAP]>>PairCases_on`y`>>
      fs[check_freevars_def,EVERY_MAP,EVERY_MEM])>>
    fs[]>>
    (fn g =>
      let
        val t1 = (snd g) |> strip_exists |> snd |> dest_conj |> fst |> lhs
        val (vs,b) = el 5 (fst g) |> strip_forall
        val t2 = b |> strip_exists |> snd |> dest_conj |> fst |> lhs
        val (s,_) = match_term t2 t1
      in first_x_assum(strip_assume_tac o SPECL(map (subst s) vs)) end
      g) >>
    simp[] >>
    simp[EXTENSION,MEM_MAP,UNCURRY] >>
    metis_tac[]) >>
  conj_tac >- (
    rw[check_specs_def,success_eqns] >>
    REWRITE_TAC[GSYM FUNION_ASSOC] >>
    qpat_assum `A⇒ B` mp_tac>>
    discharge_hyps>-
      (match_mp_tac tenv_tabbrev_ok_merge>>fs[typeSoundInvariantsTheory.tenv_tabbrev_ok_def,FEVERY_FEMPTY,typeSoundInvariantsTheory.flat_tenv_tabbrev_ok_def,FEVERY_FUPDATE]>>
      metis_tac[check_freevars_type_name_subst])>>
    metis_tac[FUPDATE_EQ_FUNION]) >>
  conj_tac >- (
    simp[check_specs_def,success_eqns,PULL_EXISTS] >> rw[] >>
    fs[union_decls_def]>>
    (fn g =>
      let
        val t1 = (snd g) |> strip_exists |> snd |> dest_conj |> fst |> lhs
        val (vs,b) = el 3 (fst g) |> strip_forall
        val t2 = b |> strip_exists |> snd |> dest_conj |> fst |> lhs
        val (s,_) = match_term t2 t1
      in first_x_assum(strip_assume_tac o SPECL(map (subst s) vs)) end
      g) >>
    simp[] >> simp_tac(srw_ss()++boolSimps.ETA_ss)[] >>
    simp[EXTENSION] >> metis_tac[]) >>
  simp[check_specs_def,success_eqns] >> rw[] >>
  simp[RIGHT_EXISTS_AND_THM,GSYM CONJ_ASSOC] >>
  fs[union_decls_def]>>
  qpat_assum`A ⇒ B` mp_tac>>discharge_hyps>-
    (match_mp_tac tenv_tabbrev_ok_merge>>fs[typeSoundInvariantsTheory.tenv_tabbrev_ok_def,FEVERY_FEMPTY,typeSoundInvariantsTheory.flat_tenv_tabbrev_ok_def,FEVERY_FUPDATE,check_freevars_def,EVERY_MAP,EVERY_MEM])>>
  strip_tac>>
  (fn g =>
    let
      val t1 = (snd g) |> strip_exists |> snd |> dest_conj |> fst |> lhs
      val (vs,b) = el 1 (fst g) |> strip_forall
      val t2 = b |> strip_exists |> snd |> dest_conj |> fst |> lhs
      val (s,_) = match_term t2 t1
    in first_x_assum(strip_assume_tac o SPECL(map (subst s) vs)) end
    g) >>
  simp[Once FUPDATE_EQ_FUNION,FUNION_ASSOC] >>
  simp[EXTENSION] >> metis_tac[])

val check_flat_weakT_complete = store_thm("check_flat_weakT_complete",
  ``∀mn tenvT1 tenvT2.
    flat_weakT mn tenvT1 tenvT2 ⇒
    check_flat_weakT mn tenvT1 tenvT2``,
  simp[flat_weakT_def,check_flat_weakT_def,FEVERY_ALL_FLOOKUP,FORALL_PROD] >>
  rw[] >> first_x_assum(qspec_then`k`strip_assume_tac) >> rfs[])

val check_flat_weakC_complete = store_thm("check_flat_weakC_complete",
  ``∀tenvC1 tenvC2.
    flat_weakC tenvC1 tenvC2 ⇒
    check_flat_weakC tenvC1 (anub tenvC2 [])``,
  simp[flat_weakC_def,check_flat_weakC_def] >> rw[] >>
  match_mp_tac EVERY_anub_suff >> rw[] >>
  first_x_assum(qspec_then`x`mp_tac) >> rw[] >>
  BasicProvers.EVERY_CASE_TAC  >> fs[])

val weakE_anub_rev = store_thm("weakE_anub_rev",
  ``∀env1 env2. weakE env1 env2 ⇒ weakE env1 (anub env2 [])``,
  rw[weakE_def] >>
  fs[Once ALOOKUP_anub])

val deBruijn_subst_unconvert = prove(``
  (∀t.
  check_freevars n [] t ⇒
  unconvert_t (deBruijn_subst 0 subst t) =
  infer_deBruijn_subst (MAP unconvert_t subst) (unconvert_t t) ) ∧
  (∀ts.
  EVERY (check_freevars n []) ts ⇒
  MAP (unconvert_t o (deBruijn_subst 0 subst)) ts
  =
  MAP ((infer_deBruijn_subst (MAP unconvert_t subst)) o unconvert_t) ts)``,
  Induct>>fs[check_freevars_def]>>rw[]>>
  fs[deBruijn_subst_def,unconvert_t_def,infer_deBruijn_subst_def]
  >-
    (IF_CASES_TAC>>fs[EL_MAP,unconvert_t_def])
  >>
    fs[MAP_MAP_o,EVERY_MEM,MAP_EQ_f])

(*This might have been proven elsewhere...*)
val infer_deBruijn_subst_twice = prove(``
  (∀t.
  check_t (LENGTH subst2) {} t ⇒
  (infer_deBruijn_subst subst1 (infer_deBruijn_subst subst2 t) =
  infer_deBruijn_subst (MAP (infer_deBruijn_subst subst1) subst2) t)) ∧
  (∀ts.
  EVERY (check_t (LENGTH subst2) {}) ts ⇒
  MAP ((infer_deBruijn_subst subst1) o (infer_deBruijn_subst subst2)) ts =
  MAP (infer_deBruijn_subst(MAP(infer_deBruijn_subst subst1) subst2)) ts)``,
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[check_t_def,infer_deBruijn_subst_def]>>
  simp[EL_MAP]>>
  fs[MAP_MAP_o,EVERY_MEM,MAP_EQ_f])

val t_walkstar_infer_deBruijn_subst = prove(``
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
  MAP ((t_walkstar s) o (infer_deBruijn_subst (GENLIST Infer_Tuvar tvs))) ts))``,
  strip_tac>>ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[check_t_def,infer_deBruijn_subst_def]>>
  fs[EVERY_MEM,MEM_EL]
  >-
    metis_tac[t_walkstar_no_vars]
  >>
    fs[t_walkstar_eqn1,MAP_MAP_o,MAP_EQ_f])

(*Definitely proved before somewhere*)
val infer_deBruijn_subst_check_t = prove(``
  EVERY (check_t tvs {}) ls
  ⇒
  (∀t.
  check_t (LENGTH ls) {} t
  ⇒
  check_t tvs {} (infer_deBruijn_subst ls t)) ∧
  (∀ts.
  EVERY (check_t (LENGTH ls) {}) ts
  ⇒
  EVERY (check_t tvs {}) (MAP (infer_deBruijn_subst ls) ts))``,
  strip_tac>>ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[check_t_def,infer_deBruijn_subst_def]>>
  fs[EVERY_MEM,MEM_EL]>>
  metis_tac[])

val check_weakE_complete = store_thm("check_weakE_complete",
  ``∀itenv1 itenv2 st tenv1 tenv2.
    weakE tenv1 tenv2 ∧
    check_env {} itenv1 ∧
    check_env {} itenv2 ∧
    tenv_alpha itenv1 (bind_var_list2 tenv1 Empty) ∧
    tenv_alpha itenv2 (bind_var_list2 tenv2 Empty)
  ⇒
    ∃st'.
    check_weakE itenv1 (anub itenv2 []) st = (Success(),st')``,
  rw[check_weakE_EVERY]>>
  imp_res_tac weakE_anub_rev>>
  last_x_assum kall_tac>>
  fs[weakE_def,EVERY_MEM]>>rw[]>>
  PairCases_on`e`>>
  fs[tenv_alpha_def,tenv_inv_def]>>
  (*Go from itenv2 to tenv2*)
  `ALOOKUP itenv2 e0 = SOME(e1,e2)` by
    metis_tac[MEM_anub_ALOOKUP]>>
  first_x_assum(qspecl_then[`e0`,`e1`,`e2`] assume_tac)>>rfs[]>>
  fs[tenv_alpha_def,tenv_invC_def,lookup_bvl2,lookup_tenv_val_def]>>
  (*Go from tenv2 to tenv1*)
  Cases_on`ALOOKUP tenv2 e0`>>fs[]>>
  Cases_on`x`>>fs[deBruijn_inc0]>>
  `ALOOKUP (anub tenv2 []) e0 = SOME(q,r)` by
    (Q.ISPECL_THEN [`tenv2`,`e0`,`[]:tvarN list`] assume_tac (GEN_ALL ALOOKUP_anub)>>
    fs[])>>
  first_x_assum(qspec_then`e0` assume_tac)>>rfs[]>>
  Cases_on`ALOOKUP tenv1 e0`>>fs[]>>PairCases_on`x`>>fs[]>>
  (*Go from tenv1 to itenv1*)
  last_x_assum(qspecl_then[`e0`,`x0`,`x1`] assume_tac)>>rfs[]>>
  fs[markerTheory.Abbrev_def]>>
  (*Go from itenv1 back to tenv1*)
  last_x_assum(qspecl_then[`e0`,`tvs''`,`t''`] assume_tac)>>rfs[]>>
  imp_res_tac ALOOKUP_MEM>>
  fs[check_env_def,EVERY_MEM]>>
  res_tac>>fs[]>>rfs[]>>
  rpt var_eq_tac>>
  (*change e2 into something nicer*)
  qpat_assum`A=convert_t e2` (mp_tac o Q.AP_TERM`unconvert_t`)>>
  `unconvert_t (convert_t e2) = e2` by
    metis_tac[check_t_empty_unconvert_convert_id]>>
  pop_assum (SUBST1_TAC)>>
  disch_then (SUBST_ALL_TAC o SYM)>>
  qspec_then `x1` assume_tac (deBruijn_subst_unconvert|>CONJUNCT1)>>rfs[]>>
  `check_freevars (LENGTH subst') [] (deBruijn_subst 0 subst x1)` by
    (match_mp_tac deBruijn_subst_check_freevars2>>
    fs[EVERY_MEM])>>
  imp_res_tac deBruijn_subst_unconvert>>
  pop_assum(qspec_then`subst'` mp_tac)>>pop_assum kall_tac>>
  strip_tac>>fs[]>>
  qpat_assum`A=unconvert_t x1` (SUBST_ALL_TAC o SYM)>>
  imp_res_tac check_freevars_to_check_t>>
  simp[infer_deBruijn_subst_twice]>>
  (*Now we have 1 big infer_deBruijn_subst*)
  qpat_abbrev_tac`ls = MAP (infer_deBruijn_subst A) B`>>
  `EVERY (check_t e1 {}) ls` by
    (fs[Abbr`ls`,EVERY_MAP,MAP_MAP_o,EVERY_MEM]>>
    rw[]>>
    let val tac =  match_mp_tac (infer_deBruijn_subst_check_t|>UNDISCH|>CONJUNCT1|>DISCH_ALL|>GEN_ALL|>(SIMP_RULE (srw_ss()) [PULL_FORALL,AND_IMP_INTRO]))
    in
    tac>>CONJ_TAC>-
      (fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
      metis_tac[check_freevars_to_check_t])>>
    tac>>
    fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
    metis_tac[check_freevars_to_check_t] end)>>
  Q.ISPECL_THEN [`init_infer_state`,`[]:(infer_t,infer_t) alist`,`FEMPTY:num|->infer_t`,`MAP convert_t ls`,`e1`] mp_tac extend_multi_props>>
  discharge_hyps_keep>-
       (fs[init_infer_state_def,t_wfs_def,pure_add_constraints_def,count_def]>>
       fs[EVERY_MAP,Abbr`ls`,EVERY_MEM]>>rw[]>>
       metis_tac[check_t_to_check_freevars])>>
   BasicProvers.LET_ELIM_TAC>>fs[init_infer_state_def]>>
   `targs = ls` by
     (fs[Abbr`targs`,MAP_MAP_o,MAP_EQ_ID]>>
     metis_tac[check_t_empty_unconvert_convert_id,EVERY_MEM])>>fs[]>>
   imp_res_tac (t_walkstar_infer_deBruijn_subst)>>
   pop_assum kall_tac>>
   pop_assum mp_tac>>
   ntac 14 (pop_assum kall_tac)>>
   simp[]>>disch_then (qspec_then`t''` mp_tac)>>
   fs[markerTheory.Abbrev_def]>>
   strip_tac>>
   metis_tac[IS_SOME_EXISTS,SUBMAP_t_compat,t_compat_eqs_t_unify])

val check_weak_decls_complete = store_thm("check_weak_decls_complete",
  ``(FST decls1) = (FST decls2) ∧
    weak_decls (convert_decls decls1) (convert_decls decls2) ⇒
    check_weak_decls decls1 decls2``,
  PairCases_on`decls1`>>
  PairCases_on`decls2`>>
  rw[weak_decls_def,convert_decls_def,check_weak_decls_def,list_subset_def] >>
  fs[EXTENSION,SUBSET_DEF,EVERY_MEM])

(* TODO: move *)
val type_top_tenv_ok = store_thm("type_top_tenv_ok",
  ``∀ch decls tenv top decls' tenvT' menv' cenv' tenv'.
    type_top ch decls tenv top decls' tenvT' menv' cenv' tenv' ⇒
      num_tvs tenv.v = 0 ⇒
      tenv_tabbrev_ok tenv.t ⇒
      tenv_val_ok (bind_var_list2 tenv' Empty) ∧
      FEVERY (λ(mn,tenv). tenv_val_ok (bind_var_list2 tenv Empty)) menv'``,
  ho_match_mp_tac type_top_ind >>
  rw[FEVERY_FEMPTY,FEVERY_FUPDATE,bind_var_list2_def,
     typeSoundInvariantsTheory.tenv_val_ok_def] >>
  imp_res_tac type_d_tenv_ok >>
  fs[check_signature_cases] >>
  imp_res_tac type_ds_tenv_ok >>
  imp_res_tac type_specs_tenv_ok)
(* -- *)

val infer_top_complete = Q.store_thm("infer_top_complete",
`!top mdecls tdecls edecls tenvT menv cenv decls' tenvT' cenv' tenv tenv' menv' st itenv tenvM'.
  check_menv menv ∧
  tenv_mod_ok tenv.m ∧
  tenv_val_ok (bind_var_list2 tenv_v Empty) ∧
  check_env ∅ itenv ∧
  tenv_ctor_ok tenv.c ∧
  tenv_tabbrev_ok tenv.t ∧
  (*check_env ∅ tenv' ∧ *)
  type_top T <| defined_mods := set mdecls; defined_types := set tdecls; defined_exns := set edecls |>
    (tenv with v:= bind_var_list2 tenv_v Empty) top decls' tenvT' tenvM' cenv' tenv' ∧
  tenv_alpha itenv (bind_var_list2 tenv_v Empty) ∧
  menv_alpha menv tenv.m
  ⇒
  ?st' mdecls'' tdecls'' edecls'' itenv' menv'.
    set mdecls'' = decls'.defined_mods ∧
    set tdecls'' = decls'.defined_types ∧
    set edecls'' = decls'.defined_exns ∧
    infer_top (mdecls,tdecls,edecls) tenv.t menv tenv.c itenv top st =
      (Success ((mdecls'',tdecls'',edecls''), tenvT', menv', cenv', itenv'), st') ∧
    (*for induction*)
    tenv_alpha itenv' (bind_var_list2 tenv' Empty) ∧
    menv_alpha menv' tenvM' ∧
    MAP FST itenv' = MAP FST tenv' ∧
    (*maybe implied as well*)
    check_env ∅ itenv'`,
  rw [Once type_top_cases]>>
  fs[infer_top_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def,empty_decls_def,check_env_def]
  >-
    (first_assum (mp_tac o (any_match_mp (INST_TYPE [alpha|->``:tvarN``] infer_d_complete)))>>
    rpt (disch_then(fn th => first_assum (mp_tac o (any_match_mp th)))) >>
    disch_then (qspecl_then [`st`] mp_tac)>>
    rw[check_env_def]>>fs[PULL_EXISTS]>>
    fs[menv_alpha_def])
  >>
    first_assum (mp_tac o (any_match_mp (INST_TYPE [alpha|->``:tvarN``] infer_ds_complete)))>>
    rpt (disch_then(fn th => first_assum (mp_tac o (any_match_mp th)))) >>
    disch_then (qspecl_then [`st`] mp_tac)>>
    rw[check_env_def]>>fs[PULL_EXISTS] >>
    fs[check_signature_cases]
    >-
      (fs[check_signature_def,success_eqns,EXTENSION,tenv_alpha_empty]>>
      fs[menv_alpha_def]>>
      rpt(conj_tac >- rw[union_decls_def]) >>
      match_mp_tac fmap_rel_FUPDATE_same>>
      fs[])
    >>
      fs[check_signature_def,success_eqns]>>
      simp[GSYM INSERT_SING_UNION,PULL_EXISTS,tenv_alpha_empty] >>
      imp_res_tac type_specs_no_mod >> fs[] >>
      imp_res_tac (INST_TYPE[alpha|->``:(num|->infer_t)infer_st``]check_specs_complete) >>
      first_x_assum(qspecl_then[`[]`,`st'`,`[]`,`FEMPTY`,`[]`,`[]`,`[]`]strip_assume_tac) >>
      simp[success_eqns] >> fs[] >>
      PairCases_on`decls'`>>fs[] >>
      simp[menv_alpha_def,fmap_rel_FUPDATE_same] >>
      imp_res_tac check_flat_weakT_complete >>
      imp_res_tac check_flat_weakC_complete >>
      Q.ISPECL_THEN[`(decls'0,decls'1,decls'2)`,`mdecls'',tdecls'',edecls''`]mp_tac (GEN_ALL check_weak_decls_complete) >>
      simp[convert_decls_def] >> fs[weak_decls_def] >>
      `check_env {} env'` by
        (imp_res_tac check_specs_check>>
        pop_assum mp_tac>>
        ntac 26 (pop_assum kall_tac)>>
        simp[check_env_def,check_flat_cenv_def,typeSoundInvariantsTheory.flat_tenv_tabbrev_ok_def,FEVERY_FEMPTY])>>
      simp[union_decls_def] >> rfs[] >>
      metis_tac[check_weakE_complete,check_env_def,check_specs_check])

val infer_prog_complete = Q.store_thm("infer_prog_complete",
`!prog mdecls tdecls edecls menv decls' tenvT' cenv' tenv_v tenv tenv' menv' st itenv tenvM tenvM'.
  check_menv menv ∧
  tenv_mod_ok tenv.m ∧
  tenv_val_ok (bind_var_list2 tenv_v Empty) ∧
  check_env ∅ itenv ∧
  tenv_ctor_ok tenv.c ∧
  tenv_tabbrev_ok tenv.t ∧
  type_prog T <|defined_mods := set mdecls; defined_types := set tdecls; defined_exns := set edecls|>
    (tenv with v := bind_var_list2 tenv_v Empty) prog decls' tenvT' tenvM' cenv' tenv' ∧
  tenv_alpha itenv (bind_var_list2 tenv_v Empty) ∧
  menv_alpha menv tenv.m
  ⇒
  ?st' mdecls'' tdecls'' edecls'' itenv' menv'.
    set mdecls'' = decls'.defined_mods ∧
    set tdecls'' = decls'.defined_types ∧
    set edecls'' = decls'.defined_exns ∧
    infer_prog (mdecls,tdecls,edecls) tenv.t menv tenv.c itenv prog st =
      (Success ((mdecls'',tdecls'',edecls''), tenvT', menv', cenv', itenv'), st') ∧
    (*for induction*)
    tenv_alpha itenv' (bind_var_list2 tenv' Empty) ∧
    menv_alpha menv' tenvM' ∧
    MAP FST itenv' = MAP FST tenv' ∧
    (*maybe implied as well*)
    check_env ∅ itenv'`,

  Induct>-
  (rw [Once type_prog_cases, infer_prog_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def,empty_decls_def,check_env_def]>>
  fs[tenv_alpha_empty,menv_alpha_def])
  >>
  rw [Once type_prog_cases, infer_prog_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def,empty_decls_def]>>
  fs[]>>
  first_assum (mp_tac o (any_match_mp (infer_top_complete|>REWRITE_RULE[GSYM AND_IMP_INTRO])))>>
  rpt (disch_then(fn th => first_assum (mp_tac o (any_match_mp th)))) >>
  disch_then (qspecl_then [`st`] mp_tac)>>
  rw[]>>
  `check_cenv tenv.c` by fs[check_cenv_tenvC_ok]>>
  qpat_assum`check_env {} itenv` mp_tac>>strip_tac>>
  first_assum (mp_tac o (any_match_mp infer_top_invariant))>>
  rpt (disch_then (fn th => first_assum (mp_tac o (any_match_mp th))))>>
  strip_tac>>
  fs[PULL_EXISTS]>>
  fs[GSYM bind_var_list2_append]>>
  fs[union_decls_def] >>
  rpt(qpat_assum`set _ = _`(assume_tac o SYM)) >>
  qmatch_assum_abbrev_tac`type_prog _ _ tenv1 _ _ _ _ _ _` >>
  `∃tenv_v2 tenv2. tenv1 = tenv2 with v := bind_var_list2 (tenv_v2 ++ tenv_v) Empty` by (
    srw_tac[QUANT_INST_ss[record_default_qp]][Abbr`tenv1`] ) >>
  fs[Abbr`tenv1`] >>
  FULL_SIMP_TAC bool_ss [UNION_APPEND] >>
  first_x_assum(fn th => first_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]
    (CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(same_const``type_prog`` o fst o strip_comb))))th)))) >>
  pop_assum (mp_tac o SYM) >>
  simp[Once type_environment_component_equality] >> strip_tac >>
  disch_then(qspecl_then[`FUNION menv''' menv`,`st'`,`itenv'++itenv`]mp_tac) >>
  simp[AND_IMP_INTRO] >>
  discharge_hyps>-
    (rw[]
    >-
      metis_tac[tenv_alpha_bind_var_list2]
    >-
      fs[menv_alpha_def,fmap_rel_FUNION_rels]
    >-
      fs[tenv_tabbrev_ok_merge]
    >-
      fs[tenv_ctor_ok_merge,check_cenv_tenvC_ok]
    >-
      fs[check_env_def]
    >- (
      simp[bind_var_list2_append] >>
      match_mp_tac tenv_val_ok_bvl2 >> simp[] >>
      imp_res_tac type_top_tenv_ok >>
      fs [num_tvs_bvl2, num_tvs_def])
    >-
      (fs[typeSoundInvariantsTheory.tenv_mod_ok_def]>>
       match_mp_tac fevery_funion >> simp[] >>
       imp_res_tac type_top_tenv_ok >>
       fs [num_tvs_bvl2, num_tvs_def])
    >-
      metis_tac[check_menv_def,fevery_funion])
  >>
  rw[]>>
  fs[append_decls_def]>>
  fs[check_env_def]>>
  metis_tac[tenv_alpha_bind_var_list2,menv_alpha_def,fmap_rel_FUNION_rels])

val _ = export_theory ();
