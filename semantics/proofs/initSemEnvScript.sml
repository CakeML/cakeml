open preamble;
open libTheory astTheory bigStepTheory semanticPrimitivesTheory initialProgramTheory;
open evalPropsTheory determTheory bigClockTheory interpTheory;
open interpComputeLib;
open terminationTheory;
open boolSimps;

val _ = new_theory "initSemEnv";

val interp_add_to_sem_env_def = Define `
interp_add_to_sem_env (st,env) prog =
  case run_eval_whole_prog env st prog of
  | (st', new_ctors, Rval (new_mods, new_vals)) =>
    SOME (st' with clock := st.clock, extend_top_env new_mods new_vals new_ctors env)
  | _ => NONE`;

val interp_add_to_sem_env_thm = Q.store_thm ("interp_add_to_sem_env_thm",
`!st env prog st' env'.
  interp_add_to_sem_env (st,env) prog = SOME (st',env')
  ⇒
  add_to_sem_env (st,env) prog = SOME (st',env')`,
 simp [LET_THM, interp_add_to_sem_env_def, add_to_sem_env_def] >>
 rpt gen_tac >>
 every_case_tac >>
 fs [] >>
 imp_res_tac run_eval_whole_prog_spec >>
 `evaluate_whole_prog F env st prog (q with clock:= st.clock,q',Rval (q'',r))`
        by (fs [evaluate_whole_prog_def, no_dup_mods_def, no_dup_top_types_def] >>
            simp [Once (Q.prove (`st = st with clock := st.clock`, rw [state_component_equality]))] >>
            match_mp_tac (SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO] prog_unclocked_ignore) >>
            fs [] >>
            metis_tac []) >>
 `{res | evaluate_whole_prog F env st prog res}
  =
  {q with clock := st.clock,q',Rval (q'',r)}`
            by (rw [EXTENSION] >>
                eq_tac >>
                rw [] >>
                imp_res_tac whole_prog_determ) >>
 fs [EXTENSION, state_component_equality, CHOICE_SING]);

val prim_sem_env_eq = save_thm ("prim_sem_env_eq",
``interp_add_to_sem_env (<| clock := 0; ffi := ffi; refs := []; defined_types := {}; defined_mods := {} |>,
                         <| m := []; c := ([],[]); v := [] |>)
                        prim_types_program``
  |> SIMP_CONV(srw_ss())[interp_add_to_sem_env_def,prim_types_program_def]
  |> CONV_RULE interp_conv
  |> MATCH_MP interp_add_to_sem_env_thm
  |> (fn th => let
        val pth = SPEC_ALL prim_sem_env_def
        val th1 = mk_eq(rhs(concl pth),lhs(concl th)) |> EVAL |> EQT_ELIM
        in TRANS (TRANS pth th1) th end));

(* Too big to evaluate in a reasonable timely was due to exponential explosion in closure envs
val basis_sem_env_eq = save_thm ("basis_sem_env_eq",
  ``basis_sem_env``
  |> SIMP_CONV(srw_ss())[basis_sem_env_def,add_to_sem_env_def,basis_program_def, mk_binop_def, mk_unop_def, prim_sem_env_eq]
  |> CONV_RULE interp_conv);
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
   CONV_TAC (RAND_CONV (LAND_CONV (CASE_CONV interp_conv))) >>
   simp [extend_top_env_def, extend_dec_env_def, combine_dec_result_def, merge_alist_mod_env_def,pmatch_def, pat_bindings_def]) t;

val basis_sem_env_SOME = Q.store_thm ("basis_sem_env_SOME",
`?se. basis_sem_env ffi = SOME se`,
 simp [basis_sem_env_def] >>
 cases_on `?se. interp_add_to_sem_env (THE (prim_sem_env ffi)) basis_program = SOME se`
 >- metis_tac [interp_add_to_sem_env_thm, PAIR] >>
 pop_assum mp_tac >>
 match_mp_tac (METIS_PROVE [] ``~x ⇒ (x ⇒ y)``) >>
 fs[prim_sem_env_eq] >> rw[] >>
 simp[interp_add_to_sem_env_def] >>
 rpt BasicProvers.CASE_TAC >>
 pop_assum mp_tac >>
 simp[basis_program_def, run_eval_whole_prog_def] >>
 rw []
 >- (ntac 2 (pop_assum kall_tac) >>
     simp ([mk_ffi_def, mk_binop_def, mk_unop_def, Once run_eval_prog_def, run_eval_top_def, run_eval_dec_def,
            merge_alist_mod_env_def,pmatch_def, pat_bindings_def]) >>
     rpt (do1_tac >> TRY (Q.PAT_ABBREV_TAC`cl = (X0,Closure X Y Z)`)))
 >- (fs [] >>
     pop_assum mp_tac >>
     match_mp_tac (METIS_PROVE [] ``~x ⇒ (x ⇒ y)``) >>
     rw [mk_binop_def, mk_unop_def] >>
     CONV_TAC interp_conv));

val _ = export_theory ();
