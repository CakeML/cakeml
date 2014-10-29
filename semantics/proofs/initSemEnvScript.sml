open preamble;
open libTheory astTheory bigStepTheory semanticPrimitivesTheory initialProgramTheory;
open terminationTheory evalPropsTheory determTheory bigClockTheory interpTheory;
open compute_interpLib;
open miscLib boolSimps;

val _ = new_theory "initSemEnv";

val interp_add_to_sem_env_def = Define `
interp_add_to_sem_env se prog =
  case run_eval_whole_prog (se.sem_envM,se.sem_envC,se.sem_envE) (set_counter 100000 se.sem_store) prog of
     | (store,envC,Rval (envM,envE)) =>
         SOME 
         <| sem_envM := envM ++ se.sem_envM;
            sem_envC := merge_alist_mod_env envC se.sem_envC;
            sem_envE := envE ++ se.sem_envE;
            sem_store := set_counter (FST (FST (se.sem_store))) store |>
     | _ => NONE`;

val interp_add_to_sem_env_thm = Q.store_thm ("interp_add_to_sem_env_thm",
`!se prog se'.
  interp_add_to_sem_env se prog = SOME se'
  ⇒
  add_to_sem_env se prog = SOME se'`,
 simp [LET_THM, interp_add_to_sem_env_def, add_to_sem_env_def] >>
 rpt gen_tac >>
 `?count' s' tids' mdecls' cenv res. 
    run_eval_whole_prog (se.sem_envM,se.sem_envC,se.sem_envE) (set_counter 100000 se.sem_store) prog
    =
    (((count',s'),tids',mdecls'),cenv,res)` 
             by metis_tac [pair_CASES] >>
 full_case_tac >>
 fs [] >>
 `?count s tids mdecls. se.sem_store = ((count,s),tids,mdecls)` by metis_tac [pair_CASES] >>
 fs [set_counter_def] >>
 imp_res_tac run_eval_whole_prog_spec >>
 cases_on `¬?envM envE. res = Rval (envM, envE)`
 >- (rw [] >>
     every_case_tac >>
     fs []) >>
 fs [] >>
 `evaluate_whole_prog F (se.sem_envM,se.sem_envC,se.sem_envE) ((count'',s),tids,mdecls) prog (((count'',s'),tids',mdecls'),cenv,res)`
        by (fs [evaluate_whole_prog_def, no_dup_mods_def, no_dup_top_types_def] >>
            every_case_tac >>
            rw [] >>
            fs [] >>
            match_mp_tac (SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO] prog_unclocked_ignore) >>
            fs [] >>
            metis_tac []) >>
 strip_tac >>
 fs [] >>
 rw [EXTENSION]
 >- metis_tac [] >>
 `{res | evaluate_whole_prog F (se.sem_envM,se.sem_envC,se.sem_envE) ((count'',s),tids,mdecls) prog res}
  =
  {(((count'',s'),tids',mdecls'),cenv,Rval (envM,envE))}`
            by (rw [EXTENSION] >>
                eq_tac >>
                rw [] >>
                imp_res_tac whole_prog_determ) >>
 rw [CHOICE_SING]);

val prim_sem_env_eq = save_thm ("prim_sem_env_eq",
  ``interp_add_to_sem_env
     <|sem_envM := []; sem_envC := ([],[]); sem_envE := [];
       sem_store := ((0,[]),∅,∅)|> prim_types_program``
  |> SIMP_CONV(srw_ss())[interp_add_to_sem_env_def,prim_types_program_def]
  |> CONV_RULE(computeLib.CBV_CONV the_interp_compset) 
  |> MATCH_MP interp_add_to_sem_env_thm
  |> SIMP_RULE (srw_ss()) [GSYM prim_sem_env_def]);


(* Too big to evaluate in a reasonable timely was due to exponential explosion in closure envs 
val basis_sem_env_eq = save_thm ("basis_sem_env_eq",
  ``basis_sem_env``
  |> SIMP_CONV(srw_ss())[basis_sem_env_def,add_to_sem_env_def,basis_program_def, mk_binop_def, mk_unop_def, prim_sem_env_eq]
  |> CONV_RULE(computeLib.CBV_CONV the_interp_compset));
  *)

val basis_sem_env_SOME = Q.store_thm ("basis_sem_env_SOME",
`?se. basis_sem_env = SOME se`,
 simp [basis_sem_env_def] >>
 cases_on `?se. interp_add_to_sem_env (THE prim_sem_env) basis_program = SOME se`
 >- metis_tac [interp_add_to_sem_env_thm] >>
 pop_assum mp_tac >>
 match_mp_tac (METIS_PROVE [] ``~x ⇒ (x ⇒ y)``) >>
 rw [] >>
 fs[prim_sem_env_eq] >> rw[] >>
 simp[interp_add_to_sem_env_def] >>
 rpt BasicProvers.CASE_TAC >>
 pop_assum mp_tac >>
 simp[basis_program_def, run_eval_whole_prog_def] >>
 rw []
 >- (REWRITE_TAC[Once mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
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
     REWRITE_TAC[Once mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     REWRITE_TAC[Once mk_unop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     Q.PAT_ABBREV_TAC`cl13 = ("!",Closure X Y Z)` >>
     REWRITE_TAC[Once mk_unop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     Q.PAT_ABBREV_TAC`cl14 = ("ref",Closure X Y Z)` >>
     REWRITE_TAC[Once mk_unop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     REWRITE_TAC[Once mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     REWRITE_TAC[Once mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     Q.PAT_ABBREV_TAC`cl15 = ("array",Closure X Y Z)` >>
     REWRITE_TAC[Once mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     REWRITE_TAC[Once mk_unop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     Q.PAT_ABBREV_TAC`cl16 = ("sub",Closure X Y Z)` >>
     Q.PAT_ABBREV_TAC`cl17 = ("length",Closure X Y Z)` >>
     Q.PAT_ABBREV_TAC`cl18 = ("update",Closure X Y Z)` >>
     REWRITE_TAC[mk_binop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     REWRITE_TAC[Once mk_unop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     REWRITE_TAC[Once mk_unop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     CHANGED_TAC(REWRITE_TAC[Once mk_unop_def]) >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     Q.PAT_ABBREV_TAC`cl19 = ("fromList",Closure X Y Z)` >>
     CHANGED_TAC(REWRITE_TAC[Once mk_unop_def]) >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     Q.PAT_ABBREV_TAC`cl20 = ("length",Closure X Y Z)` >>
     Q.PAT_ABBREV_TAC`cl21 = ("sub",Closure X Y Z)` >>
     Q.PAT_ABBREV_TAC`cl22 = ("array",Closure X Y Z)` >>
     CHANGED_TAC(REWRITE_TAC[Once mk_unop_def]) >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     Q.PAT_ABBREV_TAC`cl23 = ("sub",Closure X Y Z)` >>
     CHANGED_TAC(REWRITE_TAC[Once mk_unop_def]) >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     Q.PAT_ABBREV_TAC`cl24 = ("length",Closure X Y Z)` >>
     Q.PAT_ABBREV_TAC`cl25 = ("update",Closure X Y Z)` >>
     CHANGED_TAC(REWRITE_TAC[Once mk_unop_def]) >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     CHANGED_TAC(REWRITE_TAC[Once mk_unop_def]) >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     CHANGED_TAC(REWRITE_TAC[Once mk_unop_def]) >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     Q.PAT_ABBREV_TAC`cl26 = ("ord",Closure X Y Z)` >>
     REWRITE_TAC[mk_unop_def] >> CONV_TAC(computeLib.CBV_CONV the_interp_compset) >>
     rw[]) >>
 fs [] >>
 pop_assum mp_tac >>
 match_mp_tac (METIS_PROVE [] ``~x ⇒ (x ⇒ y)``) >>
 rw [mk_binop_def, mk_unop_def] >>
 CONV_TAC(computeLib.CBV_CONV the_interp_compset));

val _ = export_theory ();
