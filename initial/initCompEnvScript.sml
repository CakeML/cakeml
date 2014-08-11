open preamble miscLib;
open astTheory bigStepTheory initialProgramTheory interpTheory inferTheory typeSystemTheory modLangTheory conLangTheory bytecodeTheory bytecodeExtraTheory;
open bigClockTheory untypedSafetyTheory inferSoundTheory initSemEnvTheory modLangProofTheory conLangProofTheory typeSoundInvariantsTheory typeSoundTheory;
open terminationTheory;
open bytecodeLabelsTheory bytecodeEvalTheory;
open compute_bytecodeLib compute_interpLib compute_inferenceLib compute_compilerLib compute_free_varsLib;

val _ = new_theory "initCompEnv";

val _ = ParseExtras.temp_tight_equality ();

val _ = Hol_datatype `
  comp_environment = <| inf_mdecls : modN list;
                        inf_tdecls : typeN id list;
                        inf_edecls : conN id list;
                        inf_tenvT : tenvT;
                        inf_tenvM : (tvarN, (tvarN, num # infer_t) alist) alist;
                        inf_tenvC : tenvC;
                        inf_tenvE : (tvarN, num # infer_t) alist;
                        comp_rs : compiler_state |>`;

val code_executes_ok'_def = Define `
code_executes_ok' s1 ⇔
  (∃s2. bc_next^* s1 s2 ∧ bc_fetch s2 = NONE ∧ s2.pc = next_addr s1.inst_length s1.code)`;

val init_code_executes_ok_def = Define `
init_code_executes_ok s1 ⇔
  (∃s2. bc_next^* s1 s2 ∧ bc_fetch s2 = SOME (Stop T))`;

val code_labels_ok_local_to_all = store_thm("code_labels_ok_local_to_all",
  ``∀code. code_labels_ok (local_labels code) ∧ MEM (Label VfromListLab) code ⇒ code_labels_ok code``,
  rw[compilerProofTheory.local_labels_def,code_labels_ok_def,
     uses_label_thm,EXISTS_MEM,PULL_EXISTS,MEM_FILTER] >>
  Cases_on`inst_uses_label VfromListLab e` >- (
    Cases_on`e` >> fs[inst_uses_label_def] >>
    Cases_on`l'`>> fs[inst_uses_label_def] ) >>
  metis_tac[])

val contains_primitives_MEM_Label_VfromListLab = store_thm("contains_primitives_MEM_Label_VfromListLab",
  ``∀code. contains_primitives code ⇒ MEM (Label VfromListLab) code``,
  EVAL_TAC >> rw[] >> rw[])

val invariant'_def = Define `
invariant' se ce bs ⇔
  ?genv gtagenv rd count s tids mdecls.
    se.sem_store = ((count,s),tids,mdecls) ∧
    type_sound_invariants (NONE : (v,v) result option)
                          (convert_decls (ce.inf_mdecls, ce.inf_tdecls, ce.inf_edecls),
                           ce.inf_tenvT,
                           convert_menv ce.inf_tenvM,
                           ce.inf_tenvC,
                           bind_var_list2 (convert_env2 ce.inf_tenvE) Empty,
                           tids,
                           se.sem_envM,
                           se.sem_envC,
                           se.sem_envE,
                           s) ∧
    infer_sound_invariant ce.inf_tenvT ce.inf_tenvM ce.inf_tenvC ce.inf_tenvE ∧
    mdecls = set ce.inf_mdecls ∧
    env_rs (se.sem_envM, se.sem_envC, se.sem_envE) se.sem_store (genv,gtagenv,rd) ce.comp_rs bs ∧
    bs.clock = NONE ∧ code_labels_ok (local_labels bs.code) ∧ code_executes_ok' bs`;

(* Same as invariant', but with code_executes_ok *)
val invariant_def = Define `
invariant se ce bs ⇔
  ?genv gtagenv rd count s tids mdecls.
    se.sem_store = ((count,s),tids,mdecls) ∧
    type_sound_invariants (NONE : (v,v) result option)
                          (convert_decls (ce.inf_mdecls, ce.inf_tdecls, ce.inf_edecls),
                           ce.inf_tenvT,
                           convert_menv ce.inf_tenvM,
                           ce.inf_tenvC,
                           bind_var_list2 (convert_env2 ce.inf_tenvE) Empty,
                           tids,
                           se.sem_envM,
                           se.sem_envC,
                           se.sem_envE,
                           s) ∧
    infer_sound_invariant ce.inf_tenvT ce.inf_tenvM ce.inf_tenvC ce.inf_tenvE ∧
    mdecls = set ce.inf_mdecls ∧
    env_rs (se.sem_envM, se.sem_envC, se.sem_envE) se.sem_store (genv,gtagenv,rd) ce.comp_rs bs ∧
    bs.clock = NONE ∧ code_labels_ok (local_labels bs.code) ∧ init_code_executes_ok bs`;

val add_to_env_def = Define `
add_to_env e prog =
  let inf_env = infer_prog (e.inf_mdecls,e.inf_tdecls,e.inf_edecls) e.inf_tenvT e.inf_tenvM e.inf_tenvC e.inf_tenvE prog init_infer_state in
  let (rs',code) = compile_initial_prog e.comp_rs prog in
    case inf_env of
      | (Success ((mdecls',tdecls',edecls'), tenvT', tenvM', tenvC', tenvE'), st) =>
            SOME
             (<| inf_mdecls := mdecls' ++ e.inf_mdecls;
                 inf_tdecls := tdecls' ++ e.inf_tdecls;
                 inf_edecls := edecls' ++ e.inf_edecls;
                 inf_tenvT := merge_tenvT tenvT' e.inf_tenvT;
                 inf_tenvM := tenvM' ++ e.inf_tenvM;
                 inf_tenvC := merge_tenvC tenvC' e.inf_tenvC;
                 inf_tenvE := tenvE' ++ e.inf_tenvE;
                 comp_rs := rs' |>,
              code)
      | _ => NONE`;

val compile_thm =
  SIMP_RULE (srw_ss()++boolSimps.DNF_ss) [AND_IMP_INTRO, evaluate_whole_prog_def] compilerProofTheory.compile_initial_prog_thm;

val empty_bc_state_def = Define `
empty_bc_state = <|
      stack := [];
      code := [];
      pc := 0;
      refs := FEMPTY;
      globals := [];
      handler := 0;
      output := "";
      inst_length := real_inst_length;
      clock := NONE |>`;

val initial_bc_state_def = Define`
  initial_bc_state = empty_bc_state with code := VfromListCode`

val install_code_def = Define `
  install_code code bs =
    bs with <| code   := bs.code ++ REVERSE code
             ; pc     := next_addr bs.inst_length bs.code
             ; output := ""
             |>`;

val add_to_env_invariant'_lem = Q.prove (
`!envM envC envE cnt s tids prog cnt' s' envM' envC' envE' tids' mdecls' e e' code code' bs.
  closed_prog prog ∧
  evaluate_whole_prog T (envM,envC,envE) ((cnt,s),tids,set e.inf_mdecls) prog (((cnt',s'),tids',mdecls'),envC',Rval (envM',envE')) ∧
  bc_eval (install_code code initial_bc_state) = SOME bs ∧
  invariant' <| sem_envM := envM; sem_envC := envC; sem_envE := envE; sem_store := ((cnt,s),tids,set e.inf_mdecls) |>
            e
            bs ∧
  add_to_env e prog = SOME (e',code')
  ⇒
  ?bs'.
  bc_eval (install_code (code'++code) initial_bc_state) = SOME bs' ∧
  invariant' <| sem_envM := envM' ++ envM;
               sem_envC := merge_envC envC' envC;
               sem_envE := envE' ++ envE;
               sem_store := ((cnt',s'),tids',mdecls') |>
            e' bs'`,
 rw [add_to_env_def, LET_THM] >>
 every_case_tac >>
 fs [] >>
 `?rs' code. compile_initial_prog e.comp_rs prog = (rs',code)` by metis_tac [pair_CASES] >>
 fs [] >>
 rw [] >>
 fs [invariant'_def] >>
 imp_res_tac infer_prog_sound >>
 simp [] >>
 `evaluate_prog F (envM,envC,envE) ((0,s),tids,set e.inf_mdecls) prog (((0,s'),tids',mdecls'),envC',Rval (envM',envE'))`
          by (rw [prog_clocked_unclocked_equiv] >>
              fs [evaluate_whole_prog_def] >>
              imp_res_tac prog_clocked_min_counter >>
              fs [] >>
              metis_tac []) >>
 `~prog_diverges (envM,envC,envE) (s,tids,set e.inf_mdecls) prog` by metis_tac [untyped_safety_prog] >>
 imp_res_tac prog_type_soundness >>
 fs [convert_decls_def] >>
 ntac 2 (pop_assum (fn _ => all_tac)) >>
 res_tac >>
 pop_assum mp_tac >>
 pop_assum (fn _ => all_tac) >>
 rw [] >>
 pop_assum (qspec_then `0` assume_tac) >>
 fs [typeSoundInvariantsTheory.update_type_sound_inv_def, evaluate_whole_prog_def] >>
 imp_res_tac determTheory.prog_determ >>
 fs [] >>
 rw [] >>
 fs [union_decls_def, convert_menv_def, typeSysPropsTheory.bvl2_append, convert_env2_def] >>
 rw [] >>
 qabbrev_tac `bs1 = bs with <| clock := SOME cnt; code := bs.code++REVERSE code'; pc := next_addr bs.inst_length bs.code |>` >>
 qabbrev_tac `bc0 = bs.code` >>
 `env_rs (envM,envC,envE) ((cnt,s),tids,set e.inf_mdecls) (genv,gtagenv,rd) e.comp_rs (bs1 with code := bc0)`
             by (UNABBREV_ALL_TAC >>
                 rw [bc_state_fn_updates] >>
                 match_mp_tac compilerProofTheory.env_rs_with_bs_irr >>
                 qexists_tac`bs with clock := SOME cnt` >> simp[] >>
                 match_mp_tac compilerProofTheory.env_rs_change_clock >>
                 first_assum(match_exists_tac o concl) >>
                 simp[bc_state_component_equality]) >>
 `bs1.code = bc0 ++ REVERSE code'`
             by (UNABBREV_ALL_TAC >>
                 rw [bc_state_fn_updates]) >>
 `IS_SOME bs1.clock`
             by (UNABBREV_ALL_TAC >>
                 rw [bc_state_fn_updates]) >>
 `bs1.pc = next_addr bs1.inst_length bc0` by simp[Abbr`bc0`,Abbr`bs1`] >>
 `?bs'' grd''.
    bc_next^* bs1 bs'' ∧ bc_fetch bs'' = NONE ∧ bs''.pc = next_addr bs1.inst_length bs1.code ∧
    bs''.output = bs1.output ∧
    env_rs (envM' ++ FST (envM,envC,envE),merge_envC cenv2 (FST (SND (envM,envC,envE))), envE' ++ SND (SND (envM,envC,envE))) ((cnt',s'),decls2',set q'''' ∪ set e.inf_mdecls) grd'' rs' bs''`
               by metis_tac [compile_thm] >>
 fs [] >>
 pop_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] compilerProofTheory.env_rs_change_clock)) >>
 simp[] >> disch_then(qspecl_then[`cnt'`,`NONE`]mp_tac) >> simp[] >> strip_tac >>
 unabbrev_all_tac >>
 fs [] >>
 imp_res_tac RTC_bc_next_preserves >>
 fs [] >>
 qexists_tac `bs'' with clock := NONE` >>
 rw []
 >- (imp_res_tac bc_eval_SOME_RTC_bc_next >>
     FIRST_ASSUM (strip_assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [AND_IMP_INTRO] RTC_bc_next_append_code)) >>
     pop_assum (qspecl_then [`REVERSE code'`] assume_tac) >>
     fs [install_code_def, code_executes_ok'_def] >>
     `bs = s2` by fs [Once RTC_CASES1] >>
     rw [] >>
     `(bs with code := bs.code ++ REVERSE code') = (bs with <|code := bs.code ++ REVERSE code'; pc := next_addr bs.inst_length bs.code |>)` 
                  by rw [bc_state_component_equality] >>
     fs [] >>
     rw [REVERSE_APPEND] >>
     imp_res_tac bytecodeClockTheory.RTC_bc_next_can_be_unclocked >>
     match_mp_tac (SIMP_RULE (srw_ss()) [AND_IMP_INTRO] RTC_bc_next_bc_eval) >>
     rw []
     >- (fs [initial_bc_state_def,empty_bc_state_def] >>
         metis_tac [transitive_RTC, transitive_def]) >>
     rw [bc_next_cases, bytecodeClockTheory.bc_fetch_with_clock]) >>
 MAP_EVERY qexists_tac [`FST grd''`, `FST (SND grd'')`, `SND (SND grd'')`] >>
 rw []
 >- (imp_res_tac compilerProofTheory.compile_initial_prog_code_labels_ok >>
     fs [install_code_def] >>
     match_mp_tac code_labels_ok_append >>
     fs [initial_bc_state_def,empty_bc_state_def])
 >- (simp[code_executes_ok'_def] >>
     qexists_tac `(bs'' with clock := NONE)` >>
     rw [] >>
     metis_tac[bytecodeClockTheory.bc_fetch_with_clock,RTC_REFL]));

val invariant_clock_0 = Q.prove (
`invariant'
    <| sem_envM := envM; 
       sem_envC := envC;
       sem_envE := envE;
       sem_store := ((cnt',s'),tids',mdecls')|> e' bs'
 ⇔
 invariant'
    <| sem_envM := envM; 
       sem_envC := envC;
       sem_envE := envE;
       sem_store := ((0,s'),tids',mdecls')|> e' bs'`,
 rw [invariant'_def] >>
 eq_tac >>
 rw [] >>
 MAP_EVERY qexists_tac [`genv`, `gtagenv`, `rd`] >>
 match_mp_tac compilerProofTheory.env_rs_change_clock >>
 rw [bc_state_component_equality]
 >- (MAP_EVERY qexists_tac [`((cnt',s'),tids',LIST_TO_SET e'.inf_mdecls)`,
                            `bs'`] >>
     rw [])
 >- (MAP_EVERY qexists_tac [`((0,s'),tids',LIST_TO_SET e'.inf_mdecls)`,
                            `bs'`] >>
     rw []));

val add_to_env_invariant' = Q.prove (
`!ck envM envC envE cnt s tids prog cnt' s' envM' envC' envE' tids' mdecls' e e' code code' bs.
  closed_prog prog ∧
  evaluate_whole_prog ck (envM,envC,envE) ((cnt,s),tids,set e.inf_mdecls) prog (((cnt',s'),tids',mdecls'),envC',Rval (envM',envE')) ∧
  bc_eval (install_code code initial_bc_state) = SOME bs ∧
  invariant' <| sem_envM := envM; sem_envC := envC; sem_envE := envE; sem_store := ((cnt,s),tids,set e.inf_mdecls) |> e bs ∧ 
  add_to_env e prog = SOME (e',code')
  ⇒ 
  ?bs'.
  bc_eval (install_code (code'++code) initial_bc_state) = SOME bs' ∧
  invariant' <| sem_envM := envM' ++ envM;
               sem_envC := merge_envC envC' envC;
               sem_envE := envE' ++ envE;
               sem_store := ((cnt',s'),tids',mdecls') |>
            e' bs'`,
 rw [] >>
 cases_on `ck`
 >- metis_tac [add_to_env_invariant'_lem] >>
 fs [evaluate_whole_prog_def] >>
 imp_res_tac bigClockTheory.prog_add_clock >>
 fs [] >>
 rw [invariant_clock_0] >>
 match_mp_tac add_to_env_invariant'_lem  >>
 rw [evaluate_whole_prog_def] >>
 MAP_EVERY Q.EXISTS_TAC [`count'`,`s`, `tids`, `prog`, `e`] >>
 fs [no_dup_mods_def, no_dup_top_types_def,invariant_clock_0]);

val prim_env_def = Define `
prim_env =
add_to_env <| inf_mdecls := [];
              inf_tdecls := [];
              inf_edecls := [];
              inf_tenvT := ([],[]);
              inf_tenvM := [];
              inf_tenvC := ([],[]);
              inf_tenvE := [];
              comp_rs := <| next_global := 0;
                            globals_env := (FEMPTY, FEMPTY);
                            contags_env := (1, (FEMPTY,FEMPTY), FEMPTY);
                            exh := FEMPTY;
                            rnext_label := VfromListLabs |> |>
        prim_types_program`;

val prim_bs_def = Define `
prim_bs = bc_eval (install_code (SND (THE prim_env)) initial_bc_state)`;

val the_compiler_compset = the_compiler_compset false

val prim_env_eq = save_thm ("prim_env_eq",
  ``prim_env``
  |> SIMP_CONV(srw_ss())[prim_env_def,add_to_env_def,LET_THM,prim_types_program_def,toBytecodeTheory.VfromListLabs_def]
  |> CONV_RULE(computeLib.CBV_CONV the_inference_compset)
  |> CONV_RULE(computeLib.CBV_CONV the_compiler_compset));

val cs = the_bytecode_compset()
val () = computeLib.add_thms[bc_fetch_def,bc_fetch_aux_def,is_Label_def,bc_find_loc_aux_def] cs
val () = computeLib.add_thms[toBytecodeTheory.VfromListCode_def |> CONV_RULE (RAND_CONV EVAL)] cs
val () = computeLib.add_datatype_info cs (valOf(TypeBase.fetch``:bc_inst``))
val () = computeLib.add_conv(``real_inst_length``,1,eval_real_inst_length) cs
val prim_bs_eq = save_thm("prim_bs_eq",
  ``prim_bs``
     |> SIMP_CONV (srw_ss()) [install_code_def, prim_bs_def, prim_env_eq, initial_bc_state_def, empty_bc_state_def, Once bc_eval_compute]
     |> CONV_RULE (computeLib.CBV_CONV cs))

val to_ctMap_list_def = Define `
to_ctMap_list tenvC =
  flat_to_ctMap_list (SND tenvC) ++ FLAT (MAP (\(mn, tenvC). flat_to_ctMap_list tenvC) (FST tenvC))`;

val to_ctMap_def = Define `
  to_ctMap tenvC = FEMPTY |++ REVERSE (to_ctMap_list tenvC)`;

val thms = [to_ctMap_def, to_ctMap_list_def, libTheory.emp_def, flat_to_ctMap_def, flat_to_ctMap_list_def, prim_env_eq];

val to_ctMap_prim_tenvC =
  SIMP_CONV (srw_ss()) thms ``to_ctMap (FST (THE prim_env)).inf_tenvC``;

val prim_env_inv = Q.store_thm ("prim_env_inv",
`?se e code bs.
  prim_env = SOME (e,code) ∧
  prim_sem_env = SOME se ∧
  prim_bs = SOME bs ∧
  invariant' se e bs`,
 rw [prim_bs_eq, prim_env_eq, prim_sem_env_eq, invariant'_def, GSYM PULL_EXISTS] >>
 rw []
 >- (rw [typeSoundInvariantsTheory.type_sound_invariants_def] >>
     MAP_EVERY qexists_tac [`to_ctMap (FST (THE prim_env)).inf_tenvC`,
                            `[]`,
                            `(set (FST (THE prim_env)).inf_mdecls, set (FST (THE prim_env)).inf_tdecls, set (FST (THE prim_env)).inf_edecls)`,
                            `[]`,
                            `(FST (THE prim_env)).inf_tenvC`] >>
     `consistent_con_env (to_ctMap (FST (THE prim_env)).inf_tenvC) (THE prim_sem_env).sem_envC (FST (THE prim_env)).inf_tenvC`
         by (rw [to_ctMap_prim_tenvC] >>
             rw [consistent_con_env_def, libTheory.emp_def, tenvC_ok_def, prim_env_eq, prim_sem_env_eq,
                 flat_tenvC_ok_def, check_freevars_def, ctMap_ok_def, miscTheory.FEVERY_ALL_FLOOKUP,
                 miscTheory.flookup_fupdate_list, semanticPrimitivesTheory.lookup_con_id_def]
             >- rw [check_freevars_def, type_subst_def]
             >- (every_case_tac >>
                 rw [] >>
                 rw [check_freevars_def, type_subst_def])
             >- (Cases_on `cn` >>
                 fs [id_to_n_def] >>
                 every_case_tac >>
                 fs [])
             >- (Cases_on `cn` >>
                 fs [id_to_n_def] >>
                 every_case_tac >>
                 fs [])) >>
     rw []
     >- (rw [consistent_decls_def, prim_env_eq, prim_sem_env_eq, RES_FORALL] >>
         every_case_tac >>
         fs [])
     >- (rw [consistent_ctMap_def, to_ctMap_prim_tenvC, prim_env_eq, prim_sem_env_eq, RES_FORALL] >>
         PairCases_on `x` >>
         fs [] >>
         every_case_tac >>
         fs [FDOM_FUPDATE_LIST])
     >- rw [ctMap_has_exns_def, to_ctMap_prim_tenvC, miscTheory.flookup_fupdate_list]
     >- rw [ctMap_has_lists_def, to_ctMap_prim_tenvC, miscTheory.flookup_fupdate_list, type_subst_def]
     >- (rw [tenvM_ok_def,tenvT_ok_def,flat_tenvT_ok_def,check_freevars_def])
     >- rw [tenvM_ok_def, convert_menv_def]
     >- rw [tenvM_ok_def, convert_menv_def]
     >- rw [Once type_v_cases]
     >- fs [prim_sem_env_eq]
     >- rw [to_ctMap_prim_tenvC, convert_env2_def, bind_var_list2_def,
            Once type_v_cases, libTheory.emp_def]
     >- rw [type_s_def, semanticPrimitivesTheory.store_lookup_def]
     >- rw [weakM_def, convert_menv_def]
     >- rw [weakeningTheory.weakC_refl, prim_env_eq]
     >- rw [decls_ok_def, prim_env_eq, decls_to_mods_def, SUBSET_DEF, GSPECIFICATION]
     >- (rw [prim_env_eq, convert_decls_def] >>
         metis_tac [weakeningTheory.weak_decls_refl])
     >- rw [prim_env_eq, weak_decls_only_mods_def, convert_decls_def])
 >- rw [tenvT_ok_def, flat_tenvT_ok_def, infer_sound_invariant_def,check_menv_def,
        check_cenv_def,check_flat_cenv_def,check_freevars_def,
        check_env_def, check_freevars_def, type_subst_def]
 >- (simp[compilerProofTheory.env_rs_def,LENGTH_NIL_SYM] >>
     qexists_tac`
      FEMPTY |++ [(("NONE",TypeId (Short "option")), (none_tag, 0));
              (("SOME",TypeId (Short "option")), (some_tag, 1));
              (("nil",TypeId (Short "list")), (nil_tag, 0:num));
              (("::",TypeId (Short "list")), (cons_tag, 2));
              (("Bind",TypeExn (Short "Bind")), (bind_tag,0));
              (("Div",TypeExn (Short "Div")), (div_tag,0));
              (("Eq",TypeExn (Short "Eq")), (eq_tag,0));
              (("Subscript",TypeExn(Short"Subscript")),(subscript_tag,0))]` >>
     simp[Once RIGHT_EXISTS_AND_THM] >>
     conj_tac >- EVAL_TAC >>
     simp[PULL_EXISTS] >>
     CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`[]` >> simp[RIGHT_EXISTS_AND_THM] >>
     simp[RIGHT_EXISTS_AND_THM,GSYM CONJ_ASSOC] >>
     conj_tac >- ( EVAL_TAC >> qexists_tac`[]` >> simp[] ) >>
     conj_tac >- (EVAL_TAC >> simp[s_to_i1_cases] >> simp[Once v_to_i1_cases] >> simp[Once v_to_i1_cases]) >>
     CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`[]` >>
     CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`[]` >>
     simp[RIGHT_EXISTS_AND_THM] >>
     conj_tac >- (
       EVAL_TAC >> simp[s_to_i2_cases] >>
       conj_tac >- (
         conj_tac >- (
           rpt gen_tac >>
           BasicProvers.CASE_TAC >>
           IF_CASES_TAC >- rw[FLOOKUP_UPDATE,FLOOKUP_FUNION] >>
           IF_CASES_TAC >- (rw[FLOOKUP_UPDATE,FLOOKUP_FUNION] >> simp[]) >>
           IF_CASES_TAC >- (rw[FLOOKUP_UPDATE,FLOOKUP_FUNION] >> simp[]) >>
           IF_CASES_TAC >- (rw[FLOOKUP_UPDATE,FLOOKUP_FUNION] >> simp[]) >>
           IF_CASES_TAC >- (rw[FLOOKUP_UPDATE,FLOOKUP_FUNION] >> simp[]) >>
           IF_CASES_TAC >- (rw[FLOOKUP_UPDATE,FLOOKUP_FUNION] >> simp[]) >>
           IF_CASES_TAC >- (rw[FLOOKUP_UPDATE,FLOOKUP_FUNION] >> simp[]) >>
           IF_CASES_TAC >- (rw[FLOOKUP_UPDATE,FLOOKUP_FUNION] >> simp[]) >>
           simp[] ) >>
         conj_tac >- (
           simp[miscTheory.IN_FRANGE_FLOOKUP,FLOOKUP_UPDATE,FLOOKUP_FUNION] >>
           rw[] >> every_case_tac >> fs[] >> rw[] >>
           EVAL_TAC ) >>
         conj_tac >- rw[] >>
         rpt gen_tac >>
         rw[] >> fs[] ) >>
       rpt gen_tac >>
       rw[] >> simp[] ) >>
     EVAL_TAC >> rw[] >>
     qexists_tac`<|cls:=FEMPTY;sm:=[]|>` >>
     simp[miscTheory.FEVERY_ALL_FLOOKUP] >>
     disj1_tac >>
     srw_tac[boolSimps.DNF_ss][Once RTC_CASES1])
 >- (CONV_TAC(RAND_CONV EVAL) >>
     fs [bytecodeLabelsTheory.code_labels_ok_def, bytecodeLabelsTheory.uses_label_def] >>
     rw[] )
 >- (
   REWRITE_TAC[code_executes_ok'_def] >>
   CONV_TAC(QUANT_CONV(RAND_CONV (RAND_CONV EVAL))) >>
   qho_match_abbrev_tac`∃s2. bc_next^* s1 s2 ∧ P s2` >>
   qsuff_tac`∃s2. bc_eval s1 = SOME s2 ∧ P s2` >-
     metis_tac[bc_eval_SOME_RTC_bc_next] >>
   qunabbrev_tac`s1` >>
   CONV_TAC(QUANT_CONV(LAND_CONV(computeLib.CBV_CONV cs))) >>
   simp[Abbr`P`] >>
   CONV_TAC(computeLib.CBV_CONV cs)))

val basis_env_def = Define `
basis_env =
add_to_env (FST (THE prim_env)) basis_program`;

val basis_env_eq = save_thm ("basis_env_eq",
  ``basis_env``
  |> SIMP_CONV(srw_ss())[basis_env_def,add_to_env_def,LET_THM,basis_program_def, prim_env_eq,
                         mk_binop_def, mk_unop_def]
  |> CONV_RULE(computeLib.CBV_CONV the_inference_compset)
  |> CONV_RULE(computeLib.CBV_CONV the_compiler_compset));

val eval_fvs = computeLib.CBV_CONV (the_free_vars_compset())

val basis_env_inv = Q.store_thm ("basis_env_inv",
`?se e code bs.
  basis_env = SOME (e,code) ∧
  basis_sem_env = SOME se ∧
  bc_eval (install_code (code ++ SND (THE prim_env)) initial_bc_state) = SOME bs ∧
  invariant' se e bs`,
 rw [basis_env_def] >>
 strip_assume_tac prim_env_inv >>
 rfs[prim_bs_def] >>
 `?e' code. basis_env = SOME (e',code)` by rw [basis_env_eq] >>
 fs [basis_env_def] >>
 `?se'. add_to_sem_env se basis_program = SOME se'` by metis_tac [optionTheory.THE_DEF, basis_sem_env_SOME, basis_sem_env_def] >>
 rw [] >>
 fs [LET_THM, add_to_sem_env_def, basis_sem_env_def] >>
 every_case_tac >>
 fs [] >>
 fs [] >>
 rw [] >>
 rfs[] >>
 `?cnt s tids mdecls. se.sem_store = ((cnt,s),tids,mdecls)` by metis_tac [pair_CASES] >>
 `?cnt' s' tids' mdecls'. q = ((cnt',s'),tids',mdecls')` by metis_tac [pair_CASES] >>
 rw [] >>
 match_mp_tac add_to_env_invariant' >>
 rw [evaluate_whole_prog_def] >>
 MAP_EVERY qexists_tac [`F`, `cnt`, `s`, `tids`, `basis_program`, `e`] >>
 rw []
 >- (
   rw[basis_program_def] >>
   CONV_TAC(eval_fvs) >>
   rw[mk_binop_def,mk_unop_def] >>
   CONV_TAC(eval_fvs))
 >- (
   rw[basis_program_def] >>
   CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   fs[prim_env_eq] >> rw[] )
 >- (
   rw[basis_program_def] >>
   CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   rw[mk_binop_def,mk_unop_def] )
 >- (`?x. {res |
         evaluate_whole_prog F (se.sem_envM,se.sem_envC,se.sem_envE)
           se.sem_store basis_program res}
      =
      {x}`
            by (fs [EXTENSION] >>
                metis_tac [determTheory.whole_prog_determ]) >>
     fs [EXTENSION] >>
     pop_assum (qspecl_then [`x`] mp_tac) >>
     rw [evaluate_whole_prog_def] >>
     fs [invariant'_def] >>
     metis_tac [])
 >- (fs [invariant'_def] >>
     metis_tac []));

val add_stop_invariant = Q.store_thm ("add_stop_invariant",
`!e se bs code.
  bc_eval (install_code code initial_bc_state) = SOME bs ∧
  invariant' e se bs
  ⇒
  ?bs'.
    bc_eval (install_code (Stop T :: code) initial_bc_state) = SOME bs' ∧
    invariant e se bs'`,
 rw [invariant'_def, invariant_def, GSYM PULL_EXISTS, code_executes_ok'_def] >>
 imp_res_tac bytecodeEvalTheory.bc_eval_SOME_RTC_bc_next  >>
 `s2 = bs` by fs [Once RTC_CASES1] >>
 rw [] >>
 FIRST_ASSUM (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [AND_IMP_INTRO] RTC_bc_next_append_code)) >>
 pop_assum (qspecl_then [`[Stop T]`] strip_assume_tac) >>
 fs [install_code_def, empty_bc_state_def, initial_bc_state_def] >>
 `bc_fetch (bs with code := bs.code ++ [Stop T]) = SOME (Stop T)`
            by (match_mp_tac bc_fetch_next_addr >>
                MAP_EVERY qexists_tac [`bs.code`, `[]`] >>
                rw []) >>
 qexists_tac `bs with <| code := bs.code ++ [Stop T] |>` >>
 rw [GSYM PULL_EXISTS]
 >- (match_mp_tac (SIMP_RULE (srw_ss()) [AND_IMP_INTRO] bytecodeEvalTheory.RTC_bc_next_bc_eval) >>
     rw [] >>
     rw [bc_next_cases])
 >- (MAP_EVERY qexists_tac [`genv`,`gtagenv`,`rd`] >>
     match_mp_tac compilerProofTheory.env_rs_append_code >>
     rw [] >>
     MAP_EVERY qexists_tac [`se.comp_rs`, `bs`, `[Stop T]`] >>
     rw [GSYM PULL_EXISTS]
     >- metis_tac [] >>
     qexists_tac `se.comp_rs.rnext_label` >>
     rw [compilerTheory.compiler_state_component_equality, good_labels_def, FILTER_APPEND_DISTRIB] >>
     qabbrev_tac `x = e.sem_store` >>
     rw [] >>
     fs [compilerProofTheory.env_rs_def, good_labels_def])
 >- (match_mp_tac code_labels_ok_append >>
     rw [] >>
     rw [code_labels_ok_def, compilerProofTheory.local_labels_def, uses_label_def])
 >- (fs [init_code_executes_ok_def, code_executes_ok'_def] >>
     metis_tac [RTC_REFL]));

val code_length_VfromListCode = save_thm("code_length_VfromListCode",
  ``code_length real_inst_length VfromListCode`` |> EVAL)

val collect_labels_VfromListCode = save_thm("collect_labels_VfromListCode",
  ``collect_labels VfromListCode 0 real_inst_length`` |> EVAL)

val _ = export_theory();
