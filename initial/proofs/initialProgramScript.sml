open HolKernel boolLib bossLib Parse
open astTheory initialEnvTheory inferTheory inferProofTheory;

val _ = new_theory"initialProgram"

(* From type inference *)

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
  rw[Once s_to_i1_cases] >> rw[Once s_to_i1'_cases] >> rw[Once v_to_i1_cases] >>
  simp[Once s_to_i2_cases] >> simp[Once s_to_i2'_cases] >> simp[Once v_to_i2_cases] >>
  simp[Cenv_bs_def,env_renv_def,s_refs_def,good_rd_def,FEVERY_ALL_FLOOKUP] >>
  simp[all_vlabs_csg_def,vlabs_csg_def,closed_vlabs_def] >>
  conj_tac >- EVAL_TAC >>
  Q.ISPEC_THEN`ck`assume_tac initial_i2_invariant >>
  fs[to_i2_invariant_def] >>
  fs[cenv_inv_def])

(* ----------------- *)

val empty_bc_state_def = Define `
  empty_bc_state = <| stack := []; code := []; pc := 0; refs := FEMPTY;
                      handler := 0; clock := NONE; output := "";
                      globals := []; inst_length := real_inst_length |>`;

val _ = export_theory()
