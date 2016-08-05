open preamble;
open primTypesTheory bigClockTheory determTheory interpComputeLib;
open terminationTheory;

val _ = new_theory "primSemEnv";

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

val prim_tdecs_def = Define
  `prim_tdecs =
    <|defined_mods := {};
      defined_exns :=
        {Short"Subscript"
        ;Short"Div"
        ;Short"Chr"
        ;Short"Bind"};
      defined_types :=
        {Short"option"
        ;Short"list"
        ;Short"bool"}|>`;

val prim_tenv_def = Define`
  prim_tenv = <|c := ([],[]); m := FEMPTY; v := Empty; t := (FEMPTY,FEMPTY)|>`;

(* TODO: rename semantics and call semantics_init semantics instead? *)
open semanticsTheory
val semantics_init_def = Define`
  semantics_init ffi =
    semantics <| sem_st := FST(THE (prim_sem_env ffi));
                 sem_env := SND(THE (prim_sem_env ffi));
                 tdecs := prim_tdecs;
                 tenv := prim_tenv |>`;

val _ = export_theory ();
