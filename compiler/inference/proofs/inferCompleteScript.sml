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

(* this might be totally wrong

val generalise_uvars = Q.prove(
  `(∀t m n s u d. FINITE u ∧ check_t d u t ⇒ FST(generalise m n s t) ≤ n + CARD (u DIFF (FDOM s))) ∧
    (∀ts m n s u d. FINITE u ∧ EVERY (check_t d u) ts ⇒ FST(generalise_list m n s ts) ≤ CARD (u DIFF (FDOM s)))`,
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

(*
val tenv_inv_letrec_merge2 = Q.prove(`
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
     tenv_inv s tenv''' tenv''`,
    rw[]>>
    imp_res_tac (INST_TYPE [alpha|->``:tvarN``,beta|->``:exp``,delta|->``:num|->infer_t``] tenv_inv_letrec_merge)>>
    pop_assum(qspecl_then [`<|subst:=FEMPTY;next_uvar:=0|>`,`funs`] assume_tac)>>
    fs[]);

val infer_d_complete = Q.store_thm ("infer_d_complete",
`!mn decls d decls' tenvT' cenv' tenv tenv' st ienv idecls.
  type_d T mn decls tenv d decls' (tenvT',cenv',tenv') ∧
  (*Related environments*)
  env_rel tenv ienv ∧
  (*Invariant for decls*)
  convert_decls idecls = decls
  ⇒
  ?st' idecls'' itenv'.
    convert_decls idecls'' = decls' ∧
    infer_d mn idecls ienv d st =
      (Success (idecls'', tenvT', cenv', itenv'), st') ∧
    tenv_alpha itenv' (bind_var_list2 tenv' Empty) ∧
    MAP FST itenv' = MAP FST tenv' ∧
    check_env {} itenv'`,
 fs[env_rel_def,GSYM check_cenv_tenvC_ok,tenv_bvl_def]>>rfs[PULL_EXISTS]>>
 rw [type_d_cases] >>
 rw [infer_d_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def] >>
 fs [empty_decls_def,check_env_def,convert_decls_def,empty_inf_decls_def]
 (* Let generalisation case *)
 >-
   (
   rw[PULL_EXISTS] >>
   (infer_pe_complete
    |> (CONV_RULE(LAND_CONV(move_conj_left(can(match_term``type_e h i j``)))))
    |> REWRITE_RULE[GSYM AND_IMP_INTRO] |> GEN_ALL
    |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
   simp [bind_tvar_rewrites, num_tvs_bvl2, num_tvs_def] >>
   simp[AND_IMP_INTRO, GSYM type_p_tenvV_indep] >>
   disch_then(drule o
     CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(equal"type_p" o #1 o dest_const o #1 o strip_comb))))) >>
   disch_then(qspecl_then[`ienv`]mp_tac) >>
   simp[GSYM AND_IMP_INTRO] >>
   impl_keep_tac >- simp[check_env_def] >>
   impl_tac >- (
     fs[tenv_alpha_def,tenv_invC_def,bind_tvar_rewrites,check_env_def] >>
     rpt gen_tac >> strip_tac >>
     qmatch_assum_abbrev_tac`lookup_tenv x tvs tenvx = SOME y` >>
     `num_tvs tenvx = 0` by
       simp[Abbr`tenvx`,num_tvs_bvl2,num_tvs_def] >>
     qspecl_then[`tvs`,`FST y`,`tenvx`,`x`]mp_tac lookup_tenv_val_inc_tvs >>
     simp[Abbr`y`] >>rfs[]>>
     disch_then(qspec_then`t'`mp_tac) >> simp[] >>
     disch_then(fn th => first_x_assum(mp_tac o C MATCH_MP th)) >>
     strip_tac >>
     metis_tac[])
     (* conj_tac >- metis_tac[] >> simp[] >> *)
   (*   reverse IF_CASES_TAC >- metis_tac[] >> fs[] >> *)
   (*   first_assum(match_exists_tac o concl) >> simp[] >> *)
   (*   fs[Abbr`tenvx`,num_tvs_bvl2,num_tvs_def] >> *)
   (*   `tvs = tvs + 0` by simp[] >> pop_assum SUBST1_TAC >> *)
   (*   match_mp_tac(MP_CANON(CONJUNCT2 check_t_more2)) >> *)
   (*   first_assum ACCEPT_TAC *) >>
   strip_tac >> simp[] >>
   imp_res_tac infer_p_bindings >> fs[] >>
   qho_match_abbrev_tac`∃a b c. tr = (a,b,c) ∧ Q a b c` >>
   `∃a b c. tr = (a,b,c)` by metis_tac[pair_CASES] >> simp[] >> fs[Abbr`Q`,Abbr`tr`] >>
   fs[init_infer_state_def] >>
   qspecl_then[`0`,`s`,`MAP SND new_bindings`]mp_tac generalise_complete >> simp[] >>
   disch_then(qspec_then`st'.next_uvar`mp_tac) >>
   impl_tac >- (
     conj_tac >- (
       match_mp_tac t_unify_check_s >>
       CONV_TAC(STRIP_QUANT_CONV(move_conj_left(same_const``t_unify`` o fst o strip_comb o lhs))) >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       fs[GSYM init_infer_state_def] >>
       `t_wfs (init_infer_state.subst)` by rw[init_infer_state_def,t_wfs_def] >>
       `t_wfs st.subst` by imp_res_tac infer_e_wfs >>
       `t_wfs st'.subst` by imp_res_tac infer_p_wfs >>
       imp_res_tac infer_p_check_t >> simp[] >>
       imp_res_tac(CONJUNCT1 infer_e_check_t) >>
       reverse conj_tac >- (
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
     `tenv_inv last_sub ienv.inf_v (bind_tvar a (bind_var_list2 tenv_v Empty))` by metis_tac [tenv_inv_empty_to,tenv_inv_extend_tvar_empty_subst] >>
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
     `type_p a tenv p (convert_t (t_walkstar last_sub t'')) (convert_env last_sub new_bindings)` by
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
   Q.ISPECL_THEN [`tvs`,`s'`] mp_tac (GEN_ALL generalise_subst_exist)>>impl_tac
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
     pop_assum (qspecl_then[`MAP (t_walkstar s) (MAP SND new_bindings)`,`[]`,`FEMPTY`,`a`,`b`,`MAP (t_walkstar last_sub) (MAP SND new_bindings)`] mp_tac)>>
     impl_keep_tac
     >-
       (fs[]>>
       imp_res_tac (infer_e_check_t |>CONJUNCT1)>>
       fs[check_env_def]>>rfs[]>>
       first_assum (mp_tac o (MATCH_MP (infer_e_check_s|>CONJUNCT1|>ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO])))>>
       simp[t_wfs_def]>>
       disch_then (qspec_then`0` mp_tac)>>
       impl_tac>-
         fs[check_env_def,check_s_def,check_cenv_tenvC_ok]>>
       strip_tac>>fs[check_s_def]>>
       imp_res_tac (infer_p_check_t |> CONJUNCT1)>>
       first_assum (mp_tac o (MATCH_MP (infer_p_check_s|>CONJUNCT1|>ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO])))>>
       disch_then(qspec_then`0` mp_tac)>>
       impl_tac>-
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
       CONV_TAC (STRIP_QUANT_CONV (move_conj_left is_eq)) >>
       first_assum (match_exists_tac o concl)>>
       fs[]>>reverse CONJ_TAC>-
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
       impl_tac>-
         (fs[SUBSET_DEF]>>
         rw[]>>
         fs[IN_FRANGE]>>
         metis_tac[pure_add_constraints_wfs])>>
       rw[]>>
       pop_assum kall_tac>>
       pop_assum(qspec_then `t_walkstar s t''''` mp_tac)>>
       impl_tac>-
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
 >- (simp[PULL_EXISTS] >>
     (infer_pe_complete
      |> CONV_RULE(LAND_CONV(move_conj_left(same_const``type_e`` o fst o strip_comb)))
      |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
      |> GEN_ALL
      |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
     rfs[]>>
     simp[num_tvs_bvl2,num_tvs_def] >>
     disch_then(drule o
       CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(equal"type_p" o #1 o dest_const o #1 o strip_comb))))) >>
     disch_then(qspecl_then[`ienv`] mp_tac)>>
     impl_tac >- (
       fs[tenv_alpha_def,check_env_def]) >>
     strip_tac >> simp[] >>
     imp_res_tac infer_p_bindings >>
     pop_assum (qspecl_then [`[]`] assume_tac) >>
     fs [] >>
     (type_pe_determ_infer_e
      |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(same_const``type_pe_determ`` o fst o strip_comb))))
      |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
      |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
     simp[num_tvs_bvl2,num_tvs_def] >>
     simp[GSYM AND_IMP_INTRO] >>
     disch_then (fn th => first_assum(mp_tac o MATCH_MP th)) >>
     disch_then (fn th => first_assum(mp_tac o MATCH_MP th)) >>
     disch_then (fn th => first_assum(mp_tac o MATCH_MP th)) >>
     simp[check_env_def] >>
     impl_tac >- fs[tenv_alpha_def] >>
     strip_tac >>
     `EVERY (check_t 0 {}) (MAP (t_walkstar s) (MAP SND new_bindings))` by (
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
       qpat_x_assum `unconvert_t t = B` (assume_tac o Q.AP_TERM `convert_t`) >>
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
     qpat_x_assum `unconvert_t _ = _` (assume_tac o Q.AP_TERM `convert_t`) >>
     imp_res_tac t_walkstar_SUBMAP>>
     first_x_assum(qspec_then `t''''` SUBST_ALL_TAC)>>
     metis_tac[check_freevars_empty_convert_unconvert_id,t_walkstar_no_vars])
 (* generalised letrec *)
 >- (
   simp[PULL_EXISTS] >>rfs[]>>
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
     |> CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(is_eq))))
     |> REWRITE_RULE[GSYM AND_IMP_INTRO])) >>
   disch_then(qspec_then`st'.next_uvar`mp_tac) >>
   simp[AND_IMP_INTRO] >>
   impl_tac >- (
     fs[check_s_def]>>
     simp[EVERY_MAP,check_t_def] >>
     simp[EVERY_MEM,MEM_COUNT_LIST] >>
     imp_res_tac (last(CONJUNCTS infer_e_next_uvar_mono)) >>
     fs[]>>rw[]>>
     `t_wfs FEMPTY` by fs[t_wfs_def]>>
     imp_res_tac infer_e_wfs>>
     rfs[]>>
     metis_tac[pure_add_constraints_wfs]) >>
   strip_tac >>
   rw[]
   >-
     (qpat_x_assum `pure_add_constraints st.subst A st'.subst` mp_tac>>
     qpat_abbrev_tac `ls:(infer_t,infer_t)alist = ZIP (A,B)`>>
     strip_tac>>
     qabbrev_tac`tenv_new = bind_var_list 0 (MAP2 (λ(f,x,e) t. (f,t)) funs (MAP
     (convert_t o (t_walkstar last_sub) o Infer_Tuvar) (COUNT_LIST (LENGTH funs)))) (bind_tvar a (bind_var_list2 tenv_v Empty))`>>
     `tenv.c = (tenv with v := tenv_new).c` by rw [] >>
     full_simp_tac (std_ss) [] >>
     first_assum (mp_tac o MATCH_MP (infer_e_sound |> CONJUNCTS |> last |> SIMP_RULE (srw_ss()) [Once (GSYM AND_IMP_INTRO)]))>>
     fs[check_cenv_tenvC_ok]>>
     disch_then (qspecl_then [`tenv with v:=tenv_new`,`ls++ec1`,`last_sub`] mp_tac)>>
     impl_tac>-
      (
      fs[sub_completion_def,num_tvs_bind_var_list,bind_tvar_rewrites,num_tvs_bvl2,num_tvs_def,check_env_def]>>
      rw[]
      >-
        (fs[MAP2_MAP,LENGTH_COUNT_LIST,EVERY_MAP,EVERY_MEM,MEM_MAP,MEM_ZIP,PULL_EXISTS,EL_MAP,EL_COUNT_LIST,UNCURRY]>>
        rw[check_t_def])
      >-
        (fs[EVERY_MEM]>>rw[]>>res_tac>>PairCases_on`e`>>fs[]>>
        metis_tac[check_t_more])
      >-
        fs[t_wfs_def]
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
         pop_assum mp_tac >> impl_tac >- simp[t_wfs_def] >>
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
    impl_tac >- simp[] >>
    qpat_x_assum`MAP  FST X = Y`kall_tac >>
    simp[EL_MAP] >>
    metis_tac[FST,PAIR,PAIR_EQ])
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
   impl_tac >-
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
     mp_tac o MATCH_MP(ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO](CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(can(match_term``X = (a,b,c)``)))))th))))) >>
   simp[LENGTH_NIL] >>
   `t_wfs st'.subst` by
     (imp_res_tac infer_e_wfs>>
        fs[]>>
        pop_assum mp_tac>>impl_tac>-fs[t_wfs_def]>>
        metis_tac[pure_add_constraints_wfs])>>
   impl_keep_tac >-
      (reverse CONJ_ASM2_TAC>-
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
     impl_tac>-
       (fs[SUBSET_DEF]>>
       rw[]>>
       fs[IN_FRANGE]>>
       metis_tac[pure_add_constraints_wfs])
     >>
     rw[]>>
     pop_assum kall_tac>>
     pop_assum(qspec_then `t_walkstar st'.subst (Infer_Tuvar p3)` mp_tac)>>
     impl_tac>-
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
       qpat_x_assum` A = EL n B` mp_tac>>
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
     qpat_x_assum`MAP A B = MAP C D` mp_tac>>
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
 >- (rw [PULL_EXISTS,convert_decls_def,empty_inf_decls_def] >>
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
 >- fs[tenv_alpha_empty]
 >- metis_tac []
 >- fs[tenv_alpha_empty]);
 *)

 (*
val t_to_freevars_type_name_subst = Q.store_thm ("t_to_freevars_type_name_subst",

  `(!t. check_type_names tenvT t ⇒ t_to_freevars (type_name_subst tenvT t) st1 = t_to_freevars t st1) ∧
   (!ts. EVERY (check_type_names tenvT) ts ⇒ ts_to_freevars (MAP (type_name_subst tenvT) ts) st1 = ts_to_freevars ts st1)`,

  Induct >>
  rw [t_to_freevars_def, success_eqns, type_name_subst_def, check_type_names_def] >>
  fs [] >>
  rw []
  >- (
    every_case_tac >>
    rw [t_to_freevars_def]
    metis_tac []

    *)

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
      asm_simp_tac std_ss [] >>
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
        cheat)
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
        cheat)
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
      cheat
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



(*
val infer_ds_complete = Q.prove(`
!ds mn decls decls' tenvT' cenv' tenv tenv' st ienv idecls.
  type_ds T mn decls tenv ds decls' (tenvT',cenv',tenv') ∧
  env_rel tenv ienv ∧
  convert_decls idecls = decls
  ⇒
  ?st' idecls'' itenv'.
    convert_decls idecls'' = decls' ∧
    infer_ds mn idecls ienv ds st =
      (Success (idecls'', tenvT', cenv', itenv'), st') ∧
    (*for induction*)
    tenv_alpha itenv' (bind_var_list2 tenv' Empty) ∧
    MAP FST itenv' = MAP FST tenv' ∧
    (*maybe implied as well*)
    check_env ∅ itenv'`,
  fs[env_rel_def,GSYM check_cenv_tenvC_ok,tenv_bvl_def]>>rfs[]>>
  Induct>-
  (rw [Once type_ds_cases, infer_ds_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def,empty_decls_def,check_env_def,convert_decls_def,empty_inf_decls_def]>>
  fs[tenv_alpha_def,bind_var_list2_def,tenv_invC_def,lookup_tenv_val_def,tenv_inv_def])
  >>
  rw [Once type_ds_cases, infer_ds_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def]>>
  fs[]>>rfs[]>>
    (infer_d_complete|>REWRITE_RULE[env_rel_def,GSYM check_cenv_tenvC_ok,tenv_bvl_def]|>
      CONV_RULE(
        STRIP_QUANT_CONV(LAND_CONV(
          move_conj_left(same_const``type_d`` o fst o strip_comb))))
    |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
    |> (fn th => first_assum(mp_tac o MATCH_MP th)))>>
  disch_then (Q.ISPECL_THEN [`st`,`ienv`,`idecls`] mp_tac)>>
  impl_tac>-
    metis_tac[check_env_def,convert_decls_def]>>
  rw[]>>
  fs[PULL_EXISTS,extend_env_new_decs_def]>>
  fs[GSYM convert_append_decls,GSYM bind_var_list2_append]>>
  qmatch_assum_abbrev_tac`type_ds _ _ _ tenv'' ds _ _` >>
  qpat_x_assum`type_ds _ _ _ _ _ _ _ ` mp_tac>>
  `tenv'' = tenv'' with v := bind_var_list2 (p_2 ++ tenv_v) Empty` by simp[Abbr`tenv''`] >>
  pop_assum SUBST1_TAC>>fs[]>>
  fs[GSYM AND_IMP_INTRO]>>
  first_x_assum (fn th => disch_then (mp_tac o MATCH_MP th))>>
  qpat_abbrev_tac`ienv' = ienv with <|inf_c:=A;inf_v:=B;inf_t:=C|>`>>
  disch_then(qspecl_then[`st'`,`ienv'`,`p_2++tenv_v`] mp_tac)>>
  fs[AND_IMP_INTRO]>>
  impl_tac>-
    (rw[Abbr`tenv''`,Abbr`ienv'`]>>fs[]
    >- (
      fs[bind_var_list2_append]>>
      match_mp_tac tenv_val_ok_bvl2>> fs[] >>
      drule type_d_tenv_val_ok >>
      fs[num_tvs_bvl2,num_tvs_def])
    >- (
      fs[tenv_ctor_ok_merge]>>
      drule typeSysPropsTheory.type_d_tenv_ok >>
      impl_tac >> fs[typeSoundInvariantsTheory.tenv_ok_def] >>
      fs[extend_env_new_decs_def,tenv_ctor_ok_merge]
      )
    >-
      (match_mp_tac tenv_tabbrev_ok_merge>>
      fs[typeSoundInvariantsTheory.tenv_tabbrev_ok_def]>>
      simp[FEVERY_FEMPTY] >>
      imp_res_tac (REWRITE_RULE[GSYM AND_IMP_INTRO]type_d_tenvT_ok) >> rfs[])
    >-
      fs[check_env_def]
    >-
      metis_tac[tenv_alpha_bind_var_list2])>>
  rw[]>>
  fs[convert_append_decls,append_new_dec_tenv_def,tenv_alpha_bind_var_list2,check_env_def]);

val rename_lemma = Q.store_thm("rename_lemma",
  `∀t fvs fvs'.
    check_freevars 0 fvs' t ∧
    set fvs' ⊆ set fvs ∧
    ALL_DISTINCT fvs'
    ⇒
    deBruijn_subst 0 (MAP (λfv. the (Tapp [] ARB) (OPTION_MAP Tvar_db (find_index fv fvs' 0))) fvs)
      (type_subst (alist_to_fmap (ZIP (fvs, MAP Tvar_db (GENLIST I (LENGTH fvs))))) t) =
    convert_t
      (infer_type_subst
        (ZIP (fvs', MAP Infer_Tvar_db (GENLIST I (LENGTH fvs')))) t)`,
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

val rename_lemma2 = Q.store_thm("rename_lemma2",
  `∀t fvs fvs'.
    check_freevars 0 fvs' t ∧
    set fvs' ⊆ set fvs ∧
    ALL_DISTINCT fvs'
    ⇒
    infer_deBruijn_subst (MAP (λfv. Infer_Tvar_db (THE (find_index fv fvs 0))) fvs')
      (infer_type_subst (ZIP (fvs', MAP Infer_Tvar_db (GENLIST I (LENGTH fvs')))) t) =
    unconvert_t
      (type_subst
        (alist_to_fmap (ZIP (fvs, MAP Tvar_db (GENLIST I (LENGTH fvs))))) t)`,
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

val check_specs_complete = Q.store_thm("check_specs_complete",
  `∀mn tenvT specs decls new_tenv.
    type_specs mn tenvT specs decls new_tenv ⇒
    tenv_tabbrev_ok tenvT ⇒
    ∀tenv cenv venv.
    new_tenv = (tenv,cenv,venv) ⇒
    ∀idecls itenvT icenv env st.
    ∃idecls' env' tenvT'' cenv'' st'.
    check_specs mn tenvT idecls itenvT icenv env specs st =
      (Success (idecls',tenv ⊌ itenvT,cenv ++ icenv,env'++env),st') ∧
    tenv_alpha env' (bind_var_list2 venv Empty) ∧
    set(MAP FST env') = set(MAP FST venv) ∧
    convert_decls idecls' = union_decls decls (convert_decls idecls)`,
  ho_match_mp_tac type_specs_strongind >>
  conj_tac >- (
    simp[check_specs_def,success_eqns,tenv_alpha_empty,empty_decls_def,union_decls_def,convert_decls_def] ) >>
  conj_tac >- (
    simp[check_specs_def,success_eqns,PULL_EXISTS] >> rw[] >>
    imp_res_tac (check_freevars_t_to_freevars) >>
    pop_assum(qspec_then`st`strip_assume_tac) >> simp[] >>
    PairCases_on`new_tenv`>>
    fs[append_new_dec_tenv_def]>>
    qpat_abbrev_tac`env' = A::env`>>
    first_x_assum(qspecl_then[`idecls`,`itenvT`,`icenv`,`env'`,`st'`] assume_tac)>>
    fs[]>>
    qpat_x_assum`A=venv` (SUBST_ALL_TAC o SYM)>>fs[Abbr`env'`]>>
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
      impl_tac >- (
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
    impl_tac >- (
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
    PairCases_on`new_tenv`>>
    fs[]>>
    qpat_abbrev_tac`idecls' = idecls with inf_defined_types:=A`>>
    qpat_abbrev_tac`itenvT' = FUNION itenvT2 itenvT`>>
    first_x_assum(qspecl_then[`idecls'`,`itenvT'`,`icenv2`,`env`,`st`] assume_tac)>>
    fs[append_new_dec_tenv_def,union_decls_def,convert_decls_def,Abbr`idecls'`]>>
    rfs[Abbr`icenv2`,Abbr`itenvT'`]>>
    fs[FUNION_ASSOC,EXTENSION]>>rw[]>>
    metis_tac[])>>
  conj_tac >- (
    rw[check_specs_def,success_eqns] >>
    qpat_x_assum `A⇒ B` mp_tac>>
    impl_tac>-
      (match_mp_tac tenv_tabbrev_ok_merge>>fs[typeSoundInvariantsTheory.tenv_tabbrev_ok_def,FEVERY_FEMPTY,typeSoundInvariantsTheory.flat_tenv_tabbrev_ok_def,FEVERY_FUPDATE]>>
      metis_tac[check_freevars_type_name_subst])>>
    PairCases_on`new_tenv`>>fs[append_new_dec_tenv_def]>>
    metis_tac[FUPDATE_EQ_FUNION,FUNION_ASSOC])>>
  conj_tac >- (
    simp[check_specs_def,success_eqns,PULL_EXISTS] >> rw[] >>
    PairCases_on`new_tenv`>>
    fs[union_decls_def]>>
    qpat_abbrev_tac`idecls' = idecls with inf_defined_exns := A`>>
    qpat_abbrev_tac`icenv' = A::icenv`>>
    first_x_assum(qspecl_then[`idecls'`,`itenvT`,`icenv'`,`env`,`st`] assume_tac)>>
    fs[convert_decls_def,append_new_dec_tenv_def,Abbr`idecls'`,Abbr`icenv'`]>>
    fs[Once INSERT_SING_UNION]>>
    simp[EXTENSION]>>
    metis_tac[])>>
  simp[check_specs_def,success_eqns] >> rw[] >>
  simp[RIGHT_EXISTS_AND_THM,GSYM CONJ_ASSOC] >>
  fs[union_decls_def]>>
  qpat_x_assum`A ⇒ B` mp_tac>>impl_tac>-
    (match_mp_tac tenv_tabbrev_ok_merge>>fs[typeSoundInvariantsTheory.tenv_tabbrev_ok_def,FEVERY_FEMPTY,typeSoundInvariantsTheory.flat_tenv_tabbrev_ok_def,FEVERY_FUPDATE,check_freevars_def,EVERY_MAP,EVERY_MEM])>>
  strip_tac>>
  PairCases_on`new_tenv`>>fs[]>>
  qpat_abbrev_tac`idecls' = idecls with inf_defined_types := A`>>
  qpat_abbrev_tac `itenvT' = itenvT |+ A`>>
  first_x_assum(qspecl_then[`idecls'`,`itenvT'`,`icenv`,`env`,`st`] assume_tac)>>
  fs[convert_decls_def,Abbr`itenvT'`,Abbr`idecls'`,append_new_dec_tenv_def]>>
  fs[Once INSERT_SING_UNION]>>
  simp[EXTENSION]>>
  metis_tac[FUPDATE_EQ_FUNION,FUNION_ASSOC])

val check_flat_weakT_complete = Q.store_thm("check_flat_weakT_complete",
  `∀mn tenvT1 tenvT2.
    flat_weakT mn tenvT1 tenvT2 ⇒
    check_flat_weakT mn tenvT1 tenvT2`,
  simp[flat_weakT_def,check_flat_weakT_def,FEVERY_ALL_FLOOKUP,FORALL_PROD] >>
  rw[] >> first_x_assum(qspec_then`k`strip_assume_tac) >> rfs[])

val check_flat_weakC_complete = Q.store_thm("check_flat_weakC_complete",
  `∀tenvC1 tenvC2.
    flat_weakC tenvC1 tenvC2 ⇒
    check_flat_weakC tenvC1 (anub tenvC2 [])`,
  simp[flat_weakC_def,check_flat_weakC_def] >> rw[] >>
  match_mp_tac EVERY_anub_suff >> rw[] >>
  first_x_assum(qspec_then`x`mp_tac) >> rw[] >>
  BasicProvers.EVERY_CASE_TAC  >> fs[])

val weakE_anub_rev = Q.store_thm("weakE_anub_rev",
  `∀env1 env2. weakE env1 env2 ⇒ weakE env1 (anub env2 [])`,
  rw[weakE_def] >>
  fs[Once ALOOKUP_anub])

val deBruijn_subst_unconvert = Q.prove(`
  (∀t.
  check_freevars n [] t ⇒
  unconvert_t (deBruijn_subst 0 subst t) =
  infer_deBruijn_subst (MAP unconvert_t subst) (unconvert_t t) ) ∧
  (∀ts.
  EVERY (check_freevars n []) ts ⇒
  MAP (unconvert_t o (deBruijn_subst 0 subst)) ts
  =
  MAP ((infer_deBruijn_subst (MAP unconvert_t subst)) o unconvert_t) ts)`,
  Induct>>fs[check_freevars_def]>>rw[]>>
  fs[deBruijn_subst_def,unconvert_t_def,infer_deBruijn_subst_def]
  >-
    (IF_CASES_TAC>>fs[EL_MAP,unconvert_t_def])
  >>
    fs[MAP_MAP_o,EVERY_MEM,MAP_EQ_f])

(*This might have been proven elsewhere...*)
val infer_deBruijn_subst_twice = Q.prove(`
  (∀t.
  check_t (LENGTH subst2) {} t ⇒
  (infer_deBruijn_subst subst1 (infer_deBruijn_subst subst2 t) =
  infer_deBruijn_subst (MAP (infer_deBruijn_subst subst1) subst2) t)) ∧
  (∀ts.
  EVERY (check_t (LENGTH subst2) {}) ts ⇒
  MAP ((infer_deBruijn_subst subst1) o (infer_deBruijn_subst subst2)) ts =
  MAP (infer_deBruijn_subst(MAP(infer_deBruijn_subst subst1) subst2)) ts)`,
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[check_t_def,infer_deBruijn_subst_def]>>
  simp[EL_MAP]>>
  fs[MAP_MAP_o,EVERY_MEM,MAP_EQ_f])

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
    fs[t_walkstar_eqn1,MAP_MAP_o,MAP_EQ_f])

(*Definitely proved before somewhere*)
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
  metis_tac[])

val check_weakE_complete = Q.store_thm("check_weakE_complete",
  `∀itenv1 itenv2 st tenv1 tenv2.
    weakE tenv1 tenv2 ∧
    check_env {} itenv1 ∧
    check_env {} itenv2 ∧
    tenv_alpha itenv1 (bind_var_list2 tenv1 Empty) ∧
    tenv_alpha itenv2 (bind_var_list2 tenv2 Empty)
  ⇒
    ∃st'.
    check_weakE itenv1 (anub itenv2 []) st = (Success(),st')`,
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
  qpat_x_assum`A=convert_t e2` (mp_tac o Q.AP_TERM`unconvert_t`)>>
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
  qpat_x_assum`A=unconvert_t x1` (SUBST_ALL_TAC o SYM)>>
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
  impl_keep_tac>-
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

val check_weak_decls_complete = Q.store_thm("check_weak_decls_complete",
  `decls1.inf_defined_mods = decls2.inf_defined_mods ∧
    weak_decls (convert_decls decls1) (convert_decls decls2) ⇒
    check_weak_decls decls1 decls2`,
  rw[weak_decls_def,convert_decls_def,check_weak_decls_def,list_subset_def] >>
  fs[EXTENSION,SUBSET_DEF,EVERY_MEM]);

val infer_top_complete = Q.store_thm("infer_top_complete",
`!top decls decls' tenvT' cenv' tenv tenv' menv' st ienv idecls tenvM'.
  type_top T decls tenv top decls' (tenvT',tenvM',cenv',tenv') ∧
  env_rel tenv ienv ∧
  convert_decls idecls = decls
  ⇒
  ?st' idecls'' itenv' menv'.
    convert_decls idecls'' = decls' ∧
    infer_top idecls ienv top st =
      (Success (idecls'', tenvT', menv', cenv', itenv'), st') ∧
    (*for induction*)
    tenv_alpha itenv' (bind_var_list2 tenv' Empty) ∧
    menv_alpha menv' tenvM' ∧
    MAP FST itenv' = MAP FST tenv' ∧
    (*maybe implied as well*)
    check_env ∅ itenv'`,
  fs[env_rel_def,GSYM check_cenv_tenvC_ok,tenv_bvl_def]>>rfs[PULL_EXISTS]>>
  rw [Once type_top_cases]>>
  fs[infer_top_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def,empty_decls_def]
  >-
    (first_assum (mp_tac o (any_match_mp (INST_TYPE [alpha|->``:tvarN``] (infer_d_complete|>REWRITE_RULE [env_rel_def,GSYM check_cenv_tenvC_ok]))))>>
    PairCases_on`new_tenv`>>fs[]>>
    rpt (disch_then(fn th => first_assum (mp_tac o (any_match_mp th)))) >>
    simp[PULL_FORALL]>>
    disch_then (qspecl_then [`st`] mp_tac)>>
    fs[tenv_bvl_def]>>impl_tac>- metis_tac[]>>
    rw[]>>fs[check_env_def,lift_new_dec_tenv_def]>>fs[PULL_EXISTS]>>
    fs[menv_alpha_def])
  >>
    first_assum (mp_tac o (any_match_mp (INST_TYPE [alpha|->``:tvarN``] (infer_ds_complete|>REWRITE_RULE [env_rel_def,GSYM check_cenv_tenvC_ok,tenv_bvl_def]))))>>
    PairCases_on`new_tenv1`>>fs[]>>
    rpt (disch_then(fn th => first_assum (mp_tac o (any_match_mp th)))) >>
    disch_then (qspec_then`st` mp_tac)>>impl_tac>- metis_tac[]>>
    strip_tac>>
    simp[PULL_EXISTS]>>
    fs[check_signature_cases]
    >-
      (fs[mod_lift_new_dec_tenv_def,check_signature_def,success_eqns,EXTENSION,tenv_alpha_empty,check_env_def,convert_decls_def,menv_alpha_def]>>
      CONJ_TAC
      >-
        (qpat_x_assum`A=decls''` (SUBST_ALL_TAC o SYM)>>
        fs[union_decls_def]>>
        metis_tac[INSERT_SING_UNION])
      >>
      match_mp_tac fmap_rel_FUPDATE_same>>
      fs[])
    >>
    fs[check_signature_def,success_eqns]>>
    simp[GSYM INSERT_SING_UNION,PULL_EXISTS,tenv_alpha_empty] >>
    PairCases_on`new_tenv2`>>
    imp_res_tac (INST_TYPE[alpha|->``:(num|->infer_t)infer_st``]check_specs_complete) >>fs[]>>
    first_x_assum(qspecl_then[`st'`,`FEMPTY`,`empty_inf_decls`,`[]`,`[]`]strip_assume_tac) >>
    simp[success_eqns]>>
    imp_res_tac type_specs_no_mod>>
    fs[weak_new_dec_tenv_def]>>
    imp_res_tac check_flat_weakT_complete >>
    imp_res_tac check_flat_weakC_complete >>
    fs[mod_lift_new_dec_tenv_def,check_env_def,tenv_alpha_empty,GSYM PULL_EXISTS]>>
    rw[]
    >-
      fs[convert_decls_def,union_decls_def,empty_inf_decls_def]
    >-
      fs[convert_decls_def]
    >-
      (match_mp_tac check_weakE_complete>>
      first_assum (match_exists_tac o concl)>>
      CONJ_TAC>-fs[check_env_def]>>
      imp_res_tac check_specs_check>>
      pop_assum mp_tac>>
      ntac 26 (pop_assum kall_tac)>>
      fs[check_env_def,check_flat_cenv_def,typeSoundInvariantsTheory.flat_tenv_tabbrev_ok_def,FEVERY_FEMPTY])
    >-
      (match_mp_tac check_weak_decls_complete>>
      fs[weak_decls_def,convert_decls_def,union_decls_def,empty_inf_decls_def])
    >>
      fs[menv_alpha_def,fmap_rel_FUPDATE_same])

val infer_prog_complete = Q.store_thm("infer_prog_complete",
`!prog decls decls' tenvT' cenv' tenv tenv' menv' st ienv idecls tenvM'.
  type_prog T decls tenv prog decls' (tenvT',tenvM',cenv',tenv') ∧
  env_rel tenv ienv ∧
  convert_decls idecls = decls
  ⇒
  ?st' idecls'' itenv' menv'.
    convert_decls idecls'' = decls' ∧
    infer_prog idecls ienv prog st =
      (Success (idecls'', tenvT', menv', cenv', itenv'), st') ∧
    (*for induction*)
    tenv_alpha itenv' (bind_var_list2 tenv' Empty) ∧
    menv_alpha menv' tenvM' ∧
    MAP FST itenv' = MAP FST tenv' ∧
    (*maybe implied as well*)
    check_env ∅ itenv'`,
  fs[env_rel_def,check_cenv_tenvC_ok,tenv_bvl_def,PULL_EXISTS]>>
  Induct>-
  (rw [Once type_prog_cases, infer_prog_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def,empty_decls_def,check_env_def,convert_decls_def,empty_inf_decls_def]>>
  fs[tenv_alpha_empty,menv_alpha_def])
  >>
  rw [Once type_prog_cases, infer_prog_def, success_eqns, LAMBDA_PROD, EXISTS_PROD, init_state_def,empty_decls_def]>>
  fs[]>>
  first_assum (mp_tac o (any_match_mp (infer_top_complete|>REWRITE_RULE[GSYM AND_IMP_INTRO,env_rel_def,check_cenv_tenvC_ok])))>>
  `tenv_bvl tenv.v` by metis_tac[tenv_bvl_def]>>
  rpt (disch_then(fn th => first_assum (mp_tac o (any_match_mp th)))) >>
  disch_then (qspecl_then [`st`,`idecls`] mp_tac)>>
  rw[]>>
  fs[PULL_EXISTS,extend_env_new_decs_def]>>
  fs[GSYM convert_append_decls,GSYM bind_var_list2_append,extend_env_new_tops_def]>>
  `check_cenv ienv.inf_c` by fs[check_cenv_tenvC_ok]>>
  first_assum (mp_tac o (any_match_mp infer_top_invariant))>>
  rpt (disch_then (fn th => first_assum (mp_tac o (any_match_mp th))))>>
  strip_tac>>
  qmatch_assum_abbrev_tac`type_prog _ _ tenv'' ds _ _` >>
  qpat_x_assum`type_prog _ _ _ _ _ _ ` mp_tac>>
  `tenv'' = tenv'' with v := bind_var_list2 (p_2'' ++ tenv_v) Empty` by simp[Abbr`tenv''`] >>
  pop_assum SUBST1_TAC>>fs[]>>
  fs[GSYM AND_IMP_INTRO]>>
  first_x_assum (fn th => disch_then (mp_tac o MATCH_MP th))>>
  qpat_abbrev_tac`ienv' = <|inf_m:=D;inf_c:=A;inf_v:=B;inf_t:=C|>`>>
  disch_then(qspecl_then[`st'`,`ienv'`,`p_2''++tenv_v`] mp_tac)>>
  fs[AND_IMP_INTRO]>>rfs[]>>
  impl_tac>-
    (unabbrev_all_tac>>fs[]>>rw[]
    >- (
      simp[bind_var_list2_append] >>
      match_mp_tac tenv_val_ok_bvl2 >> simp[] >>
      imp_res_tac type_top_tenv_val_ok >> rfs[] >>
      fs [num_tvs_bvl2, num_tvs_def])
    >- (
       fs[typeSoundInvariantsTheory.tenv_mod_ok_def]>>
       match_mp_tac fevery_funion >> simp[] >>
       imp_res_tac type_top_tenv_val_ok >>
       fs [num_tvs_bvl2, num_tvs_def])
    >- metis_tac[check_menv_def,fevery_funion]
    >- fs[menv_alpha_def,fmap_rel_FUNION_rels]
    >- metis_tac[tenv_ctor_ok_merge,check_cenv_tenvC_ok]
    >- fs[tenv_tabbrev_ok_merge]
    >-  fs[check_env_def]
    >-
      metis_tac[tenv_alpha_bind_var_list2])>>
  rw[]>>fs[convert_append_decls,append_new_top_tenv_def]>>
  fs[check_env_def]>>
  metis_tac[tenv_alpha_bind_var_list2,menv_alpha_def,fmap_rel_FUNION_rels])
  *)

val _ = export_theory ();
