open preamble miscLib;
open astTheory bigStepTheory initialEnvTheory interpTheory inferTheory typeSystemTheory modLangTheory conLangTheory bytecodeTheory bytecodeExtraTheory;
open bigClockTheory untypedSafetyTheory inferSoundTheory modLangProofTheory conLangProofTheory typeSoundTheory;
open compute_bytecodeLib compute_interpLib compute_inferenceLib compute_compilerLib;

val _ = new_theory "initialProgram";

val _ = ParseExtras.temp_tight_equality ();

val _ = Hol_datatype `
  comp_environment = <| inf_mdecls : modN list;
                        inf_tdecls : typeN id list;
                        inf_edecls : conN id list;
                        inf_tenvM : (tvarN, (tvarN, num # infer_t) alist) alist;
                        inf_tenvC : tenvC;
                        inf_tenvE : (tvarN, num # infer_t) alist;
                        comp_rs : compiler_state |>`;

val _ = Hol_datatype `
  sem_environment = <| sem_envM : envM;
                       sem_envC : envC;
                       sem_envE : envE;
                       sem_s : v store;
                       sem_tids : tid_or_exn set;
                       sem_mdecls : modN set |>`;

val invariant_def = Define `
invariant se ce bs ⇔
  ?genv gtagenv rd.
    type_sound_invariants (NONE : (v,v) result option)
                          (convert_decls (ce.inf_mdecls, ce.inf_tdecls, ce.inf_edecls),
                           convert_menv ce.inf_tenvM,
                           ce.inf_tenvC,
                           bind_var_list2 (convert_env2 ce.inf_tenvE) Empty,
                           se.sem_tids,
                           se.sem_envM,
                           se.sem_envC,
                           se.sem_envE,
                           se.sem_s) ∧
    infer_sound_invariant ce.inf_tenvM ce.inf_tenvC ce.inf_tenvE ∧
    se.sem_mdecls = set ce.inf_mdecls ∧
    env_rs (se.sem_envM, se.sem_envC, se.sem_envE) ((0,se.sem_s),se.sem_tids,se.sem_mdecls) (genv,gtagenv,rd) ce.comp_rs bs ∧
    bs.clock = NONE ∧ code_labels_ok bs.code ∧ code_executes_ok bs`;

val add_to_env_def = Define `
add_to_env e prog =
  let inf_env = infer_prog (e.inf_mdecls,e.inf_tdecls,e.inf_edecls) e.inf_tenvM e.inf_tenvC e.inf_tenvE prog init_infer_state in
  let (rs',code) = compile_initial_prog e.comp_rs prog in
    case inf_env of
      | (Success ((mdecls',tdecls',edecls'), tenvM', tenvC', tenvE'), st) =>
            SOME
             (<| inf_mdecls := mdecls' ++ e.inf_mdecls;
                 inf_tdecls := tdecls' ++ e.inf_tdecls;
                 inf_edecls := edecls' ++ e.inf_edecls;
                 inf_tenvM := tenvM' ++ e.inf_tenvM;
                 inf_tenvC := merge_tenvC tenvC' e.inf_tenvC;
                 inf_tenvE := tenvE' ++ e.inf_tenvE;
                 comp_rs := rs' |>,
              code)
      | _ => NONE`;

val add_to_sem_env_def = Define `
add_to_sem_env se prog =
  case run_eval_prog (se.sem_envM,se.sem_envC,se.sem_envE) ((10000,se.sem_s),se.sem_tids,se.sem_mdecls) prog of
     | (((cnt,s),tids,mdecls),envC,Rval (envM,envE)) =>
         SOME 
         <| sem_envM := envM ++ se.sem_envM;
            sem_envC := merge_envC envC se.sem_envC;
            sem_envE := envE ++ se.sem_envE;
            sem_s := s;
            sem_tids := tids;
            sem_mdecls := mdecls |>
     | _ => NONE`;

val compile_thm =
  SIMP_RULE (srw_ss()++boolSimps.DNF_ss) [AND_IMP_INTRO, evaluate_whole_prog_def] compilerProofTheory.compile_initial_prog_thm;

val add_to_env_invariant_lem = Q.prove (
`!envM envC envE cnt s tids prog cnt' s' envM' envC' envE' tids' mdecls' e e' code bs bs'.
  closed_prog prog ∧
  evaluate_whole_prog T (envM,envC,envE) ((cnt,s),tids,set e.inf_mdecls) prog (((cnt',s'),tids',mdecls'),envC',Rval (envM',envE')) ∧
  invariant <| sem_envM := envM; sem_envC := envC; sem_envE := envE; sem_s := s; sem_tids := tids; sem_mdecls := set e.inf_mdecls |> e bs ∧
  SOME (e',code) = add_to_env e prog ∧
  SOME bs' = bc_eval (bs with <| code   := bs.code ++ REVERSE code
                               ; pc     := next_addr bs.inst_length bs.code |>)
  ⇒
  invariant <| sem_envM := envM' ++ envM;
               sem_envC := merge_envC envC' envC;
               sem_envE := envE' ++ envE;
               sem_s := s';
               sem_tids := tids';
               sem_mdecls := mdecls' |>
            e' (bs' with clock := NONE)`,
 rw [add_to_env_def, LET_THM] >>
 every_case_tac >>
 fs [] >>
 `?rs' code. compile_initial_prog e.comp_rs prog = (rs',code)` by metis_tac [pair_CASES] >>
 fs [] >>
 rw [] >>
 fs [invariant_def] >>
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
 qabbrev_tac `bs1 = bs with <| clock := SOME cnt; code := bs.code++REVERSE code; pc := next_addr bs.inst_length bs.code |>` >>
 qabbrev_tac `bc0 = bs.code` >>
 `env_rs (envM,envC,envE) ((cnt,s),tids,set e.inf_mdecls) (genv,gtagenv,rd) e.comp_rs (bs1 with code := bc0)`
             by (UNABBREV_ALL_TAC >>
                 rw [bc_state_fn_updates] >>
                 match_mp_tac compilerProofTheory.env_rs_with_bs_irr >>
                 qexists_tac`bs with clock := SOME cnt` >> simp[] >>
                 match_mp_tac compilerProofTheory.env_rs_change_clock >>
                 first_assum(match_exists_tac o concl) >>
                 simp[bc_state_component_equality]) >>
 `bs1.code = bc0 ++ REVERSE code`
             by (UNABBREV_ALL_TAC >>
                 rw [bc_state_fn_updates]) >>
 `IS_SOME bs1.clock`
             by (UNABBREV_ALL_TAC >>
                 rw [bc_state_fn_updates]) >>
 `bs1.pc = next_addr bs1.inst_length bc0` by simp[Abbr`bc0`,Abbr`bs1`] >>
 `?bs'' grd''.
    bc_next^* bs1 bs'' ∧ bc_fetch bs'' = SOME (Stop T) ∧
    bs''.output = bs1.output ∧
    env_rs (envM' ++ FST (envM,envC,envE),merge_envC cenv2 (FST (SND (envM,envC,envE))), envE' ++ SND (SND (envM,envC,envE))) ((cnt',s'),decls2',set q''' ∪ set e.inf_mdecls) grd'' rs' bs''`
               by metis_tac [compile_thm] >>
 fs [] >>
 pop_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] compilerProofTheory.env_rs_change_clock)) >>
 simp[] >> disch_then(qspecl_then[`0`,`NONE`]mp_tac) >> simp[] >> strip_tac >>
 `bc_next^* (bs with <| code := bc0 ++ REVERSE code; pc := next_addr bs.inst_length bc0 |>) bs' ∧
  ¬?s3. bc_next bs' s3`
            by metis_tac [bytecodeEvalTheory.bc_eval_SOME_RTC_bc_next] >>
 `bs' = bs''` by cheat >>
 unabbrev_all_tac >>
 fs [] >>
 imp_res_tac RTC_bc_next_preserves >>
 fs [] >>
 MAP_EVERY qexists_tac [`FST grd''`, `FST (SND grd'')`, `SND (SND grd'')`] >>
 rw []
 >- (imp_res_tac compilerProofTheory.compile_initial_prog_code_labels_ok >>
     match_mp_tac bytecodeLabelsTheory.code_labels_ok_append >> 
     simp[])
 >- (simp[code_executes_ok_def] >> disj1_tac >>
     metis_tac[bytecodeClockTheory.bc_fetch_with_clock,RTC_REFL]));

val add_to_env_invariant = Q.prove (
`!ck envM envC envE cnt s tids prog cnt' s' envM' envC' envE' tids' mdecls' e e' code bs bs'.
  closed_prog prog ∧
  evaluate_whole_prog ck (envM,envC,envE) ((cnt,s),tids,set e.inf_mdecls) prog (((cnt',s'),tids',mdecls'),envC',Rval (envM',envE')) ∧
  invariant <| sem_envM := envM; sem_envC := envC; sem_envE := envE; sem_s := s; sem_tids := tids; sem_mdecls := set e.inf_mdecls |> e bs ∧ 
  SOME (e',code) = add_to_env e prog ∧
  SOME bs' = bc_eval (bs with <| code   := bs.code ++ REVERSE code
                               ; pc     := next_addr bs.inst_length bs.code |>)
  ⇒ 
  invariant <| sem_envM := envM' ++ envM;
               sem_envC := merge_envC envC' envC;
               sem_envE := envE' ++ envE;
               sem_s := s';
               sem_tids := tids';
               sem_mdecls := mdecls' |>
            e' (bs' with clock := NONE)`,
 rw [] >>
 cases_on `ck`
 >- metis_tac [add_to_env_invariant_lem] >>
 fs [evaluate_whole_prog_def] >>
 imp_res_tac bigClockTheory.prog_add_clock >>
 fs [] >>
 match_mp_tac add_to_env_invariant_lem  >>
 rw [evaluate_whole_prog_def] >>
 MAP_EVERY Q.EXISTS_TAC [`count'`,`s`, `tids`, `prog`, `0`, `e`, `code`, `bs`] >>
 fs [no_dup_mods_def, no_dup_top_types_def]);

val prim_env_def = Define `
prim_env =
add_to_env <| inf_mdecls := [];
              inf_tdecls := [];
              inf_edecls := [];
              inf_tenvM := [];
              inf_tenvC := ([],[]);
              inf_tenvE := [];
              comp_rs := <| next_global := 0;
                            globals_env := (FEMPTY, FEMPTY);
                            contags_env := (1, (FEMPTY,FEMPTY), FEMPTY);
                            exh := FEMPTY;
                            rnext_label := 0 |> |>
        prim_types_program`;

val prim_sem_env_def = Define `
prim_sem_env =
add_to_sem_env <| sem_envM := []; sem_envC := ([],[]); sem_envE := []; sem_s := []; sem_tids := {}; sem_mdecls := {} |> prim_types_program`;

val empty_bc_state_def = Define `
empty_bc_state = <| 
      stack := [];
      code := [];
      pc := 0;
      refs := FEMPTY;
      globals := [];
      handler := 0;
      output := "";
      inst_length := K 0;
      clock := NONE |>`;

val prim_bs_def = Define `
prim_bs = bc_eval (empty_bc_state 
                   with <| code   := empty_bc_state.code ++ REVERSE (SND (THE prim_env))
                         ; pc     := next_addr empty_bc_state.inst_length empty_bc_state.code |>)`

val the_compiler_compset = the_compiler_compset false

val prim_env_eq = save_thm ("prim_env_eq",
  ``prim_env``
  |> SIMP_CONV(srw_ss())[prim_env_def,add_to_env_def,LET_THM,prim_types_program_def]
  |> CONV_RULE(computeLib.CBV_CONV the_inference_compset)
  |> CONV_RULE(computeLib.CBV_CONV the_compiler_compset));

val prim_sem_env_eq = save_thm ("prim_sem_env_eq",
  ``prim_sem_env``
  |> SIMP_CONV(srw_ss())[prim_sem_env_def,add_to_sem_env_def,prim_types_program_def]
  |> CONV_RULE(computeLib.CBV_CONV the_interp_compset));

val prim_bs_eq = save_thm ("prim_bs_eq",
  ``prim_bs``
  |> SIMP_CONV(srw_ss())[prim_bs_def, empty_bc_state_def, prim_env_eq, 
                         Once bytecodeEvalTheory.bc_eval_compute]
  |> CONV_RULE(computeLib.CBV_CONV the_bytecode_compset));

val prim_env_inv = Q.store_thm ("prim_env_inv",
`?se e code bs.
  prim_env = SOME (e,code) ∧
  prim_sem_env = SOME se ∧
  prim_bs = SOME bs ∧
  invariant se e bs`,
 simp [prim_env_eq, prim_sem_env_eq, invariant_def, prim_bs_eq] >>
 simp[convert_decls_def,convert_menv_def,convert_env2_def,bind_var_list2_def,RIGHT_EXISTS_AND_THM] >>
 conj_tac >- (
   simp[typeSoundInvariantsTheory.type_sound_invariants_def] >>
   qexists_tac`
     FEMPTY |++
     [(("Bind",TypeExn(Short"Bind")),([],[]))
     ;(("Div",TypeExn(Short"Div")),([],[]))
     ;(("Eq",TypeExn(Short"Eq")),([],[]))
     ;(("Subscript",TypeExn(Short"Subscript")),([],[]))
     ;(("::",TypeId(Short"list")),(["'a"],[Tvar"'a";Tapp[Tvar"'a"](TC_name(Short"list"))]))
     ;(("nil",TypeId(Short"list")),(["'a"],[]))
     ;(("SOME",TypeId(Short"option")),(["'a"],[Tvar"'a"]))
     ;(("NONE",TypeId(Short"option")),(["'a"],[]))
     ]` >>
   simp[FUPDATE_LIST_THM,typeSoundInvariantsTheory.ctMap_has_exns_def,FLOOKUP_UPDATE,
        typeSoundInvariantsTheory.consistent_con_env_def,
        typeSoundInvariantsTheory.consistent_ctMap_def,
        semanticPrimitivesTheory.lookup_con_id_def,
        typeSoundInvariantsTheory.ctMap_ok_def
        ] >>
   simp[Once typeSoundInvariantsTheory.type_v_cases,
        typeSoundInvariantsTheory.weakM_def,
        typeSoundInvariantsTheory.tenvM_ok_def] >>
   simp[Once typeSoundInvariantsTheory.type_v_cases,libTheory.emp_def] >>
   qexists_tac`[]` >> simp[typeSoundInvariantsTheory.type_s_def] >>
   qexists_tac`({},{Short"list";Short"option"},{Short "Eq";Short"Div";Short"Bind";Short"Subscript"})` >>
   simp[typeSoundInvariantsTheory.consistent_ctMap_def,
        typeSoundInvariantsTheory.consistent_decls_def,
        RES_FORALL,RIGHT_EXISTS_AND_THM] >>
   conj_tac >- (rw[] >> rw[]) >>
   conj_tac >- (rw[] >> rw[]) >>
   simp[typeSoundInvariantsTheory.decls_ok_def,
        typeSoundInvariantsTheory.decls_to_mods_def,
        weak_decls_def,
        typeSoundInvariantsTheory.weak_decls_only_mods_def,
        semanticPrimitivesTheory.store_lookup_def] >>
   qexists_tac`([],[
     ("Bind",([],[],TypeExn(Short"Bind")));
     ("Div",([],[],TypeExn(Short"Div")));
     ("Eq",([],[],TypeExn(Short"Eq")));
     ("Subscript",([],[],TypeExn(Short"Subscript")));
     ("::",(["'a"],[Tvar"'a";Tapp[Tvar"'a"](TC_name(Short"list"))],TypeId(Short"list")));
     ("nil",(["'a"],[],TypeId(Short"list")));
     ("SOME",(["'a"],[Tvar"'a"],TypeId(Short"option")));
     ("NONE",(["'a"],[],TypeId(Short"option")))])` >>
   simp[typeSoundInvariantsTheory.tenvC_ok_def,
        typeSoundInvariantsTheory.flat_tenvC_ok_def,
        miscTheory.FEVERY_ALL_FLOOKUP,FLOOKUP_UPDATE,
        typeSoundInvariantsTheory.weakC_def,
        flat_weakC_def] >>
   conj_tac >- rw[terminationTheory.check_freevars_def] >>
   conj_tac >- (
     rw[] >> rw[terminationTheory.check_freevars_def] ) >>
   conj_tac >- (
     rpt gen_tac >>
     BasicProvers.CASE_TAC >>
     simp[semanticPrimitivesTheory.lookup_con_id_def,id_to_n_def] >>
     IF_CASES_TAC >- rw[] >>
     IF_CASES_TAC >- rw[] >>
     IF_CASES_TAC >- rw[] >>
     IF_CASES_TAC >- rw[] >>
     IF_CASES_TAC >- rw[] >>
     IF_CASES_TAC >- rw[] >>
     IF_CASES_TAC >- rw[] >>
     IF_CASES_TAC >- rw[] >>
     simp[]) >>
   conj_tac >- (
     rw[] >>
     Cases_on`cn`>>fs[id_to_n_def]>>
     rw[semanticPrimitivesTheory.lookup_con_id_def] ) >>
   conj_tac >- rw[] >>
   rw[SUBSET_DEF,GSPECIFICATION]) >>
 conj_tac >- (
   simp[infer_sound_invariant_def,check_menv_def,check_cenv_def,check_flat_cenv_def,terminationTheory.check_freevars_def,check_env_def]) >>
 simp[compilerProofTheory.env_rs_def,LENGTH_NIL_SYM] >>
 qexists_tac`
  FEMPTY |++ [(("NONE",TypeId (Short "option")), (none_tag, 0));
              (("SOME",TypeId (Short "option")), (some_tag, 1));
              (("nil",TypeId (Short "list")), (nil_tag, 0:num));
              (("::",TypeId (Short "list")), (cons_tag, 2));
              (("Bind",TypeExn (Short "Bind")), (bind_tag,0));
              (("Div",TypeExn (Short "Div")), (div_tag,0));
              (("Eq",TypeExn (Short "Eq")), (eq_tag,0));
              (("Subscript",TypeExn(Short"Subscript")),(subscript_tag,0))]` >>
 CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`<|stack:=[];code:=[Stop T];pc:=0;clock:=NONE;globals:=[]|>` >>
 simp[Once RIGHT_EXISTS_AND_THM] >>
 conj_tac >- simp[bytecodeExtraTheory.good_labels_def] >>
 simp[PULL_EXISTS] >>
 CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`[]` >> simp[RIGHT_EXISTS_AND_THM] >>
 simp[RIGHT_EXISTS_AND_THM,GSYM CONJ_ASSOC] >>
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
 srw_tac[boolSimps.DNF_ss][Once RTC_CASES1]);

val basis_env_def = Define `
basis_env =
add_to_env (FST (THE prim_env)) basis_program`;

val basis_sem_env_def = Define `
basis_sem_env =
add_to_sem_env (THE prim_sem_env) basis_program`;

val basis_env_inv = Q.store_thm ("basis_env_inv",
`?se e.
  basis_env = SOME e ∧
  basis_sem_env = SOME se ∧
  invariant se e`,
 rw [basis_env_def, basis_sem_env_def] >>
 strip_assume_tac prim_env_inv >>
 `?e'. add_to_env e basis_program = SOME e'` by (
   fs[prim_env_eq] >> rw[] >>
   simp[add_to_env_def] >>
   rpt BasicProvers.CASE_TAC >- simp[UNCURRY] >>
   qsuff_tac`F`>-rw[]>>pop_assum mp_tac>>
   simp[basis_program_def,mk_binop_def,mk_unop_def] >>
   CONV_TAC(computeLib.CBV_CONV the_inference_compset)) >>
 `?se'. add_to_sem_env se basis_program = SOME se'` by (
   fs[prim_sem_env_eq] >> rw[] >>
   simp[add_to_sem_env_def] >>
   rpt BasicProvers.CASE_TAC >>
   pop_assum mp_tac >>
   simp[basis_program_def] >>
   REWRITE_TAC[Once mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   Q.PAT_ABBREV_TAC`cl1 = ("+",Closure X Y Z)` >>
   REWRITE_TAC[Once mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   Q.PAT_ABBREV_TAC`cl2 = ("-",Closure X Y Z)` >>
   REWRITE_TAC[Once mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   Q.PAT_ABBREV_TAC`cl3 = ("*",Closure X Y Z)` >>
   REWRITE_TAC[Once mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   Q.PAT_ABBREV_TAC`cl4 = ("div",Closure X Y Z)` >>
   REWRITE_TAC[Once mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   Q.PAT_ABBREV_TAC`cl5 = ("mod",Closure X Y Z)` >>
   REWRITE_TAC[Once mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   Q.PAT_ABBREV_TAC`cl6 = ("<",Closure X Y Z)` >>
   REWRITE_TAC[Once mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   Q.PAT_ABBREV_TAC`cl7 = (">",Closure X Y Z)` >>
   REWRITE_TAC[Once mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   Q.PAT_ABBREV_TAC`cl8 = ("<=",Closure X Y Z)` >>
   REWRITE_TAC[Once mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   Q.PAT_ABBREV_TAC`cl9 = (">=",Closure X Y Z)` >>
   REWRITE_TAC[Once mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   Q.PAT_ABBREV_TAC`cl10 = ("=",Closure X Y Z)` >>
   REWRITE_TAC[Once mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   Q.PAT_ABBREV_TAC`cl11 = (":=",Closure X Y Z)` >>
   Q.PAT_ABBREV_TAC`cl12 = ("~",Closure X Y Z)` >>
   REWRITE_TAC[mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   REWRITE_TAC[mk_unop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   rw[]) >>
 rw [] >>
 fs [add_to_sem_env_def] >>
 every_case_tac >>
 fs [] >>
 imp_res_tac run_eval_prog_spec >>
 fs [] >>
 rw [] >>
 match_mp_tac add_to_env_invariant >>
 rw [evaluate_whole_prog_def] >>
 MAP_EVERY qexists_tac [`T`, `10000`, `se.sem_s`, `se.sem_tids`, `basis_program`, `q`, `e`] >>
 rw []
 >- (
   rw[basis_program_def] >>
   CONV_TAC(computeLib.CBV_CONV the_free_vars_compset) >>
   rw[mk_binop_def,mk_unop_def] >>
   CONV_TAC(computeLib.CBV_CONV the_free_vars_compset))
 >- (
   rw[basis_program_def] >>
   CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   fs[prim_env_eq] >> rw[] )
 >- (
   rw[basis_program_def] >>
   CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
   rw[mk_binop_def,mk_unop_def] )
 >- (fs [invariant_def] >>
     metis_tac [])
 >- (fs [invariant_def] >>
     metis_tac []));

(*
val prim_type_sound_inv = Q.prove (
`case (prim_types_env, prim_sem_env) of
   | ((decls1,tenvM,tenvC,tenv), ((envM, envC, envE), decls2, mods)) =>
       type_sound_invariants (decls1,tenvM,tenvC,tenv,decls2,envM,envC,envE,[])`,
cheat);

val prim_type_inf_inv = Q.prove (
`case prim_types_inf_env of
   | (decls,menv,cenv,env) =>
       infer_sound_invariant menv cenv env`,
cheat);

val prim_comp_invs = Q.prove (
`case (prim_comp_env,prim_sem_env) of
   | ((next_global, mods, tops, tagenv_st, exh_env),
      ((envM, envC, envE), tids, mod_names)) => 
        ?genv genv_i2 gtagenv.
          to_i1_invariant genv mods tops envM envE (ckl1,[]) (clk2,[]) mod_names ∧
          to_i2_invariant mod_names tids envC exh_env tagenv_st gtagenv (clk3,[]) (clk4,[]) genv genv_i2`,
cheat);



(* From type inference *)

val init_infer_decls_def = Define `
init_infer_decls = ([],[Short "option"; Short "list"],[Short "Bind"; Short "Div"; Short "Eq"])`;

val infer_init_thm = Q.store_thm ("infer_init_thm",
`infer_sound_invariant [] ([],[]) init_type_env ∧
 (convert_decls init_infer_decls = init_decls) ∧
 (convert_menv [] = []) ∧
 (bind_var_list2 (convert_env2 init_type_env) Empty = init_tenv)`,
rw [check_t_def, check_menv_def, check_cenv_def, check_env_def, init_type_env_def,
    Infer_Tfn_def, Infer_Tint_def, Infer_Tbool_def, Infer_Tunit_def, 
    Infer_Tref_def, init_tenv_def, bind_var_list2_def, convert_env2_def,
    convert_t_def, convert_menv_def, bind_tenv_def, check_flat_cenv_def,
    infer_sound_invariant_def, init_decls_def, init_infer_decls_def, 
    convert_decls_def]);

(* ----------------- *)

(* from type soundness *)

val to_ctMap_list_def = Define `
to_ctMap_list tenvC =  
  flat_to_ctMap_list (SND tenvC) ++ FLAT (MAP (\(mn, tenvC). flat_to_ctMap_list tenvC) (FST tenvC))`;

val to_ctMap_def = Define `
  to_ctMap tenvC = FEMPTY |++ REVERSE (to_ctMap_list tenvC)`;
 
val thms = [to_ctMap_def, to_ctMap_list_def, init_tenvC_def, emp_def, flat_to_ctMap_def, flat_to_ctMap_list_def]; 

val to_ctMap_init_tenvC = 
  SIMP_CONV (srw_ss()) thms ``to_ctMap init_tenvC``;

val type_check_v_tac = 
 rw [Once type_v_cases, type_env_eqn2] >>
 MAP_EVERY qexists_tac [`[]`, `init_tenvC`, `Empty`] >>
 rw [tenvM_ok_def, type_env_eqn2, check_freevars_def, Once consistent_mod_cases] >>
 NTAC 10 (rw [Once type_e_cases, num_tvs_def, bind_tvar_def,
              t_lookup_var_id_def, check_freevars_def, lookup_tenv_def, bind_tenv_def,
              deBruijn_inc_def, deBruijn_subst_def,
              METIS_PROVE [] ``(?x. P ∧ Q x) = (P ∧ ?x. Q x)``,
              LENGTH_NIL_SYM, type_op_cases, type_uop_cases]);

val initial_type_sound_invariants = Q.store_thm ("initial_type_sound_invariant",
`type_sound_invariants (init_decls,[],init_tenvC,init_tenv,init_type_decs,[],init_envC,init_env,[])`,
 rw [type_sound_invariants_def] >>
 MAP_EVERY qexists_tac [`to_ctMap init_tenvC`, `[]`, `init_decls`, `[]`, `init_tenvC`] >>
 `consistent_con_env (to_ctMap init_tenvC) init_envC init_tenvC`
         by (rw [to_ctMap_init_tenvC] >>
             rw [consistent_con_env_def, init_envC_def, init_tenvC_def, emp_def, tenvC_ok_def, 
                 flat_tenvC_ok_def, check_freevars_def, ctMap_ok_def, FEVERY_ALL_FLOOKUP,
                 flookup_fupdate_list, lookup_con_id_def]
             >- (every_case_tac >>
                 fs [] >>
                 rw [check_freevars_def])
             >- (Cases_on `cn` >>
                 fs [id_to_n_def] >>
                 every_case_tac >>
                 fs [])
             >- (Cases_on `cn` >>
                 fs [id_to_n_def] >>
                 every_case_tac >>
                 fs [])) >>
 rw []
 >- (rw [consistent_decls_def, init_type_decs_def, init_decls_def, RES_FORALL] >>
     every_case_tac >>
     fs [])
 >- (rw [consistent_ctMap_def, to_ctMap_init_tenvC, init_decls_def, RES_FORALL] >>
     PairCases_on `x` >>
     fs [] >>
     every_case_tac >>
     fs [FDOM_FUPDATE_LIST])
 >- rw [ctMap_has_exns_def, to_ctMap_init_tenvC, flookup_fupdate_list]
 >- rw [tenvM_ok_def]
 >- rw [tenvM_ok_def]
 >- rw [Once type_v_cases]
 >- (rw [init_env_def, emp_def, init_tenv_def, type_env_eqn2] >>
     type_check_v_tac)
 >- rw [type_s_def, store_lookup_def] 
 >- rw [weakM_def]
 >- rw [weakC_refl]
 >- rw [decls_ok_def, init_decls_def, decls_to_mods_def, SUBSET_DEF, GSPECIFICATION]
 >- metis_tac [weak_decls_refl]
 >- rw [init_decls_def, weak_decls_only_mods_def]);

(* ------------------- *)

(* from conLang *)

val init_tagenv_state : (nat * tag_env * map nat (conN * tid_or_exn))
let init_tagenv_state =
  (8,
   (Map.empty,
    Map.fromList [("Div", (div_tag, Just (TypeExn (Short "Div")))); 
                  ("Bind", (bind_tag,Just (TypeExn (Short "Bind")))); 
                  ("Eq", (eq_tag, Just (TypeExn (Short "Eq")))); 
                  ("::", (cons_tag, Just (TypeId (Short "list"))));
                  ("nil", (nil_tag, Just (TypeId (Short "list"))));
                  ("SOME", (some_tag, Just (TypeId (Short "option"))));
                  ("NONE", (none_tag, Just (TypeId (Short "option"))))]),
   Map.fromList [(div_tag, ("Div", TypeExn (Short "Div"))); 
                 (bind_tag, ("Bind", TypeExn (Short "Bind"))); 
                 (eq_tag, ("Eq", TypeExn (Short "Eq"))); 
                 (cons_tag, ("::", TypeId (Short "list")));
                 (nil_tag, ("nil", TypeId (Short "list")));
                 (some_tag, ("SOME", TypeId (Short "option")));
                 (none_tag, ("NONE", TypeId (Short "option")))])

val init_exh : exh_ctors_env
let init_exh =
  Map.fromList
    [(Short "list", nat_set_from_list [cons_tag; nil_tag]);
     (Short "option", nat_set_from_list [some_tag; none_tag])]

(* ----------------- *)

(* from compiler.lem *)

let init_compiler_state =
  <| next_global = 0
   ; globals_env = (Map.empty, Map.empty)
   ; contags_env = init_tagenv_state
   ; exh = init_exh
   ; rnext_label = 0
   |>

(* ----------------- *)

(* from modLangProof *)

val init_mods_def = Define `
  init_mods = FEMPTY`;

val init_tops_def = Define `
  init_tops = FEMPTY |++ alloc_defs 0 (MAP FST init_env)`;

val init_genv_def = Define `
  init_genv =
    MAP (\(x,v).
           case v of
             | Closure _ x e => SOME (Closure_i1 (init_envC,[]) x (exp_to_i1 init_mods (init_tops\\x) e)))
        init_env`;

val initial_i1_invariant = Q.prove (
`global_env_inv init_genv init_mods init_tops [] {} init_env ∧
 s_to_i1' init_genv [] []`,
 rw [last (CONJUNCTS v_to_i1_eqns)]
 >- (rw [v_to_i1_eqns, init_tops_def] >>
     fs [init_env_def, alloc_defs_def] >>
     rpt (full_case_tac
          >- (rw [] >>
              rw [flookup_fupdate_list] >>
              rw [init_genv_def, Once v_to_i1_cases] >>
              rw [v_to_i1_eqns] >>
              rw [init_env_def, DRESTRICT_UNIV] >>
              metis_tac [])) >>
     fs [])
 >- rw [v_to_i1_eqns, s_to_i1'_cases]);

val init_to_i1_invariant = Q.store_thm ("init_to_i1_invariant",
`!count. to_i1_invariant init_genv init_mods init_tops [] init_env (count,[]) (count,[]) {}`,
 rw [to_i1_invariant_def, s_to_i1_cases] >>
 metis_tac [initial_i1_invariant]);

(* ----------------- *)

(* from conLangProof *)
val init_gtagenv_def = Define `
init_gtagenv =
  FEMPTY |++ [(("NONE",TypeId (Short "option")), (none_tag, 0));
              (("SOME",TypeId (Short "option")), (some_tag, 1));
              (("nil",TypeId (Short "list")), (nil_tag, 0:num));
              (("::",TypeId (Short "list")), (cons_tag, 2));
              (("Bind",TypeExn (Short "Bind")), (bind_tag,0));
              (("Div",TypeExn (Short "Div")), (div_tag,0));
              (("Eq",TypeExn (Short "Eq")), (eq_tag,0))]`;

val initial_i2_invariant = Q.store_thm ("initial_i2_invariant",
`!ck.
  to_i2_invariant
    {}
    (IMAGE SND (FDOM init_gtagenv))
    init_envC
    init_exh
    init_tagenv_state
    init_gtagenv
    (ck,[]) (ck,[])
    [] []`,
 rw [to_i2_invariant_def, s_to_i2_cases, v_to_i2_eqns, s_to_i2'_cases]
 >- EVAL_TAC
 >- (simp[EXISTS_PROD] >>
     pop_assum mp_tac >> EVAL_TAC >> simp[] >>
     metis_tac[] )
 >- EVAL_TAC
 >- (rw [cenv_inv_def, envC_tagged_def, exhaustive_env_correct_def]
     >- (fs [initialEnvTheory.init_envC_def] >>
         cases_on `cn` >>
         fs [id_to_n_def] >>
         fs [lookup_con_id_def, emp_def, nil_tag_def, emp_def, cons_tag_def,
             bind_tag_def, div_tag_def, eq_tag_def] >>
         EVAL_TAC >> rw[] >> fs[])
     >- (
       fs[init_exh_def,IN_FRANGE_FLOOKUP,flookup_fupdate_list] >>
       every_case_tac >> fs[] >> rw[] >>
       rw[nat_set_from_list_def] >>
       rpt (match_mp_tac sptreeTheory.wf_insert) >>
       rw[sptreeTheory.wf_def] )
     >- (fs [FDOM_FUPDATE_LIST, init_exh_def, init_gtagenv_def] >>
         rw [flookup_fupdate_list] >>
         every_case_tac >>
         rw[nat_set_from_list_def,domain_nat_set_from_list])
     >- (rw [gtagenv_wf_def, has_exns_def, init_gtagenv_def, flookup_fupdate_list] >>
         rw[nil_tag_def,cons_tag_def,eq_tag_def,tuple_tag_def,bind_tag_def,div_tag_def,none_tag_def,some_tag_def] >>
         pop_assum mp_tac >>
         rw[nil_tag_def,cons_tag_def,eq_tag_def,tuple_tag_def,bind_tag_def,div_tag_def,none_tag_def,some_tag_def] >>
         pop_assum mp_tac >>
         rw[nil_tag_def,cons_tag_def,eq_tag_def,tuple_tag_def,bind_tag_def,div_tag_def,none_tag_def,some_tag_def]))
 >- (rw [alloc_tags_invariant_def, init_gtagenv_def, FDOM_FUPDATE_LIST, get_next_def,
         tuple_tag_def, init_tagenv_state_def, flookup_fupdate_list, get_tagacc_def] >>
     pop_assum mp_tac >>
     srw_tac [ARITH_ss] [nil_tag_def,cons_tag_def,eq_tag_def,tuple_tag_def, bind_tag_def, div_tag_def,none_tag_def,some_tag_def]));
(* ----------------- *)

(* from compilerProof *)
val env_rs_empty = store_thm("env_rs_empty",
  ``∀envs s cs genv rd grd bs ck.
    bs.stack = [] ∧ bs.globals = [] ∧ FILTER is_Label bs.code = [] ∧
    (∀n. bs.clock = SOME n ⇒ n = ck) ∧ envs = ([],init_envC,[]) ∧
    s = ((ck,[]),IMAGE SND (FDOM init_gtagenv),{}) ∧
    grd = ([],init_gtagenv,rd) ∧
    rd.sm = [] ∧ rd.cls = FEMPTY ∧ cs = init_compiler_state ⇒
    env_rs envs s grd cs bs``,
  rpt gen_tac >>
  simp[env_rs_def,to_i1_invariant_def,to_i2_invariant_def] >>
  strip_tac >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  rw[init_compiler_state_def,get_tagenv_def,cenv_inv_def] >>
  rw[Once v_to_i1_cases] >> rw[Once v_to_i1_cases] >>
  rw[Once s_to_i1_cases] >> rw[Once v_to_i1_cases] >>
  simp[Once s_to_i2_cases] >> simp[Once v_to_i2_cases] >>
  simp[Cenv_bs_def,env_renv_def,s_refs_def,good_rd_def,FEVERY_ALL_FLOOKUP] >>
  simp[all_vlabs_csg_def,vlabs_csg_def,closed_vlabs_def] >>
  simp[store_vs_def] >>
  conj_tac >- EVAL_TAC >>
  Q.ISPEC_THEN`ck`assume_tac initial_i2_invariant >>
  fs[to_i2_invariant_def] >>
  fs[cenv_inv_def])


(* ----------------- *)

val empty_bc_state_def = Define `
  empty_bc_state = <| stack := []; code := []; pc := 0; refs := FEMPTY;
                      handler := 0; clock := NONE; output := "";
                      globals := []; inst_length := real_inst_length |>`;
                      *)
val _ = export_theory()
