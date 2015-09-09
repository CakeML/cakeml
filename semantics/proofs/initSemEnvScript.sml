open preamble;
open libTheory astTheory bigStepTheory semanticPrimitivesTheory initialProgramTheory;
open terminationTheory evalPropsTheory determTheory bigClockTheory interpTheory;
open compute_interpLib;
open boolSimps;

val _ = new_theory "initSemEnv";

val interp_add_to_sem_env_def = Define `
interp_add_to_sem_env se prog =
  case run_eval_whole_prog <| m := se.sem_envM; c := se.sem_envC; v := se.sem_envE |> (set_counter 100000 se.sem_store) prog of
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
    run_eval_whole_prog <| m := se.sem_envM; c := se.sem_envC; v := se.sem_envE |> (set_counter 100000 se.sem_store) prog
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
 `evaluate_whole_prog F <| m := se.sem_envM; c := se.sem_envC; v := se.sem_envE |> ((count'',s),tids,mdecls) prog (((count'',s'),tids',mdecls'),cenv,res)`
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
 `{res | evaluate_whole_prog F <| m := se.sem_envM; c := se.sem_envC; v := se.sem_envE |> ((count'',s),tids,mdecls) prog res}
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
       sem_store := ((0,([],SOME LNIL)),∅,∅)|> prim_types_program``
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


(* recursively decend into the test position of case expressions and apply to conversion to the inner-most *)
fun CASE_CONV conv tm =
let 
  fun CASE_CONV0 tm =
    if TypeBase.is_case tm then
      let
        val (case_const, (test::rest)) = strip_comb tm
      in
        List.foldl (fn (a,th) => AP_THM th a) (AP_TERM case_const (CASE_CONV0 test)) rest
      end
    else
      conv tm
in
  if TypeBase.is_case tm then
    CASE_CONV0 tm
  else
    raise UNCHANGED
end;

fun do1_tac t = 
  (REWRITE_TAC [Once run_eval_prog_def, run_eval_top_def, Once run_eval_decs_def, run_eval_dec_def] >>
   CONV_TAC (RAND_CONV (LAND_CONV (CASE_CONV (computeLib.CBV_CONV the_interp_compset)))) >>
   simp [combine_dec_result_def, all_env_to_menv_def, merge_alist_mod_env_def,pmatch_def, all_env_to_cenv_def, all_env_to_env_def, pat_bindings_def]) t;

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
 >- (pop_assum kall_tac >>
     pop_assum kall_tac >>
     simp ([mk_ffi_def, mk_binop_def, mk_unop_def, Once run_eval_prog_def, run_eval_top_def, set_counter_def, run_eval_dec_def,
            all_env_to_menv_def, merge_alist_mod_env_def,pmatch_def, all_env_to_cenv_def, all_env_to_env_def, pat_bindings_def]) >>
     rpt (do1_tac >> TRY (Q.PAT_ABBREV_TAC`cl = (X0,Closure X Y Z)`)))
 >- (fs [] >>
     pop_assum mp_tac >>
     match_mp_tac (METIS_PROVE [] ``~x ⇒ (x ⇒ y)``) >>
     rw [mk_binop_def, mk_unop_def] >>
     CONV_TAC(computeLib.CBV_CONV the_interp_compset)));

val _ = export_theory ();
