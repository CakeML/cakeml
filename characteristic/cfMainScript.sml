open preamble
     semanticPrimitivesTheory
     ml_translatorTheory ml_translatorLib ml_progLib
     cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib
     semanticsLib

val _ = new_theory "cfMain";

(*The following section culminates in call_main_thm2 which takes a spec and some aspects
  of the current state, and proves a Semantics_prog statement. It also proves call_FFI_rel^*
  between the initial state, and the state after creating the prog and then calling the main
  function - this is useful for theorizing about the output of the program  *)

fun mk_main_call s =
(* TODO: don't use the parser so much here? *)
  ``Dlet unknown_loc (Pcon NONE []) (App Opapp [Var (Short ^s); Con NONE []])``;
val fname = mk_var("fname",``:string``);
val main_call = mk_main_call fname;

val call_main_thm1 = Q.store_thm("call_main_thm1",
`ML_code env1 st1 prog NONE env2 st2 ==> (* get this from the current ML prog state *)
 lookup_var fname env2 = SOME fv ==> (* get this by EVAL *)
  app p fv [Conv NONE []] P (POSTv uv. &UNIT_TYPE () uv * Q) ==> (* this should be the CF spec you prove for the "main" function *)
    SPLIT (st2heap p st2) (h1,h2) /\ P h1 ==>  (* this might need simplification, but some of it may need to stay on the final theorem *)
    ∃st3.
    Decls env1 st1 (SNOC ^main_call prog) env2 st3 /\
    (?h3 h4. SPLIT3 (st2heap p st3) (h3,h2,h4) /\ Q h3)`,
  rw[ml_progTheory.ML_code_def,SNOC_APPEND,ml_progTheory.Decls_APPEND,PULL_EXISTS]
  \\ asm_exists_tac \\ fs[]
  \\ simp[ml_progTheory.Decls_def]
  \\ ONCE_REWRITE_TAC [bigStepTheory.evaluate_dec_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [bigStepTheory.evaluate_dec_cases |> CONJUNCT2] \\ SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [astTheory.pat_bindings_def,ALL_DISTINCT,MEM,
       pmatch_def, Once bigStepTheory.evaluate_dec_cases,combine_dec_result_def]
  \\ fs[PULL_EXISTS]
  \\ fs[app_def,app_basic_def]
  \\ first_x_assum drule \\ rw[]
  \\ rw[Once bigStepTheory.evaluate_cases]
  \\ rw[Once bigStepTheory.evaluate_cases]
  \\ rw[Once bigStepTheory.evaluate_cases]
  \\ rw[Once bigStepTheory.evaluate_cases]
  \\ rw[Once bigStepTheory.evaluate_cases]
  \\ rw[Once bigStepTheory.evaluate_cases]
  \\ rw[Once bigStepTheory.evaluate_cases]
  \\ rw[PULL_EXISTS]
  \\ CONV_TAC(STRIP_QUANT_CONV(LAND_CONV (LAND_CONV EVAL))) \\ simp[]
  \\ CONV_TAC(STRIP_QUANT_CONV(LAND_CONV (LAND_CONV EVAL))) \\ simp[]
  \\ CONV_TAC(STRIP_QUANT_CONV(LAND_CONV (LAND_CONV EVAL))) \\ simp[]
  \\ fs[ml_progTheory.lookup_var_def,ALOOKUP_APPEND]
  \\ reverse every_case_tac >- fs[cond_def] \\ fs[]
  \\ fs[evaluate_ck_def,funBigStepEquivTheory.functional_evaluate_list]
  \\ fs[Once (CONJUNCT2 bigStepTheory.evaluate_cases)]
  \\ fs[Once (CONJUNCT2 bigStepTheory.evaluate_cases)]
  \\ imp_res_tac cfAppTheory.big_remove_clock \\ fs[]
  \\ first_x_assum(qspec_then`st2.clock`mp_tac)
  \\ simp[semanticPrimitivesPropsTheory.with_same_clock]
  \\ strip_tac
  \\ simp[build_conv_def,do_con_check_def,ml_progTheory.nsLookup_merge_env]
  \\ asm_exists_tac \\ simp[]
  \\ fs[STAR_def,cond_def,UNIT_TYPE_def]
  \\ CONV_TAC(STRIP_QUANT_CONV(LAND_CONV (LAND_CONV EVAL))) \\ simp[]
  \\ srw_tac[QI_ss][ml_progTheory.merge_env_def,sem_env_component_equality,cfStoreTheory.st2heap_clock]
  \\ asm_exists_tac \\ fs[cfHeapsBaseTheory.SPLIT_emp1] \\ rw[]
);

val evaluate_prog_RTC_call_FFI_rel = Q.store_thm("evaluate_prog_RTC_call_FFI_rel",
  `evaluate_decs F env st prog (st',res) ==>
    RTC call_FFI_rel st.ffi st'.ffi`,
  cheat (*
  rw[bigClockTheory.dec_clocked_unclocked_equiv]
  \\ (funBigStepEquivTheory.functional_evaluate_tops
      |> CONV_RULE(LAND_CONV SYM_CONV) |> LET_INTRO
      |> Q.GENL[`env`,`s`,`tops`]
      |> qspecl_then[`env`,`st with clock := c`,`prog`]mp_tac)
  \\ rw[] \\ pairarg_tac \\ fs[]
  \\ drule evaluatePropsTheory.evaluate_tops_call_FFI_rel_imp
  \\ imp_res_tac determTheory.prog_determ
  \\ fs[] \\ rw[] *));

(*
val evaluate_prog_rel_IMP_evaluate_prog_fun = Q.store_thm(
   "evaluate_prog_rel_IMP_evaluate_prog_fun",
  `bigStep$evaluate_whole_prog F env st prog (st',Rval r) ==>
    ?k. evaluate$evaluate_prog (st with clock := k) env prog =
          (st',Rval r)`,
  rw[bigClockTheory.prog_clocked_unclocked_equiv,bigStepTheory.evaluate_whole_prog_def]
  \\ qexists_tac`c + st.clock`
  \\ (funBigStepEquivTheory.functional_evaluate_prog
      |> CONV_RULE(LAND_CONV SYM_CONV) |> LET_INTRO |> GEN_ALL
      |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s","env","prog"]))
      |> qspecl_then[`st with clock := c + st.clock`,`env`,`prog`]mp_tac)
  \\ rw[] \\ pairarg_tac \\ fs[]
  \\ fs[bigStepTheory.evaluate_whole_prog_def]
  \\ drule bigClockTheory.prog_add_to_counter \\ simp[]
  \\ disch_then(qspec_then`st.clock`strip_assume_tac)
  \\ drule determTheory.prog_determ
  \\ every_case_tac \\ fs[]
  \\ TRY (disch_then drule \\ rw[])
  \\ fs[semanticPrimitivesTheory.state_component_equality]);
*)

val prog_to_semantics_prog = Q.prove(
    `!init_env inp prog st c r env2 s2.
    Decls init_env inp prog env2 s2 /\
    s2.ffi.final_event = NONE (*This will comes from FFI_outcomes*) ==>
    (semantics_prog  inp init_env prog (Terminate Success s2.ffi.io_events))`,
  cheat (*
    rw[ml_progTheory.Decls_def] \\
    `evaluate_whole_prog F init_env' inp prog (s2,Rval env2)`
           by simp[bigStepTheory.evaluate_whole_prog_def]
    \\ imp_res_tac evaluate_prog_rel_IMP_evaluate_prog_fun
    \\ fs[semanticsTheory.semantics_prog_def,PULL_EXISTS]
    \\ fs[semanticsTheory.evaluate_prog_with_clock_def]
    \\ qexists_tac `k` \\ fs[]
    \\ rw[] \\ pairarg_tac \\ fs[]
    \\ pop_assum mp_tac
    \\ drule evaluatePropsTheory.evaluate_prog_clock_determ
    \\ ntac 2 strip_tac \\ first_x_assum drule
    \\ fs[] \\ rpt (CASE_TAC \\ fs[]) *)
);

val FFI_part_hprop_def = Define`
  FFI_part_hprop Q =
   (!h. Q h ==> (?s u ns us. FFI_part s u ns us IN h))`;

val FFI_part_hprop_STAR = Q.store_thm("FFI_part_hprop_STAR",
  `FFI_part_hprop P \/ FFI_part_hprop Q ==> FFI_part_hprop (P * Q)`,
  rw[FFI_part_hprop_def]
  \\ fs[set_sepTheory.STAR_def,SPLIT_def] \\ rw[]
  \\ metis_tac[]);

val FFI_part_hprop_SEP_EXISTS = Q.store_thm("FFI_part_hprop_SEP_EXISTS",
  `(∀x. FFI_part_hprop (P x)) ⇒ FFI_part_hprop (SEP_EXISTS x. P x)`,
  rw[FFI_part_hprop_def,SEP_EXISTS_THM] \\ res_tac);

val call_main_thm2 = Q.store_thm("call_main_thm2",
  `ML_code env1 st1 prog NONE env2 st2 ==>
   lookup_var fname env2 = SOME fv ==>
  app (proj1, proj2) fv [Conv NONE []] P (POSTv uv. &UNIT_TYPE () uv * Q) ==>
  FFI_part_hprop Q ==>
  SPLIT (st2heap (proj1, proj2) st2) (h1,h2) /\ P h1
  ==>
    ∃st3.
    semantics_prog st1 env1  (SNOC ^main_call prog) (Terminate Success st3.ffi.io_events) /\
    (?h3 h4. SPLIT3 (st2heap (proj1, proj2) st3) (h3,h2,h4) /\ Q h3) /\
    call_FFI_rel^* st1.ffi st3.ffi`,
  rw[]
  \\ qho_match_abbrev_tac`?st3. A st3 /\ B st3 /\ C st1 st3`
  \\ `?st3. Decls env1 st1 (SNOC ^main_call prog) env2 st3 ∧ st3.ffi.final_event = NONE /\ B st3 /\ C st1 st3`
  suffices_by metis_tac[prog_to_semantics_prog]
  \\ `?st3. Decls env1 st1 (SNOC ^main_call prog) env2 st3 ∧ st3.ffi.final_event = NONE /\ B st3`
  suffices_by metis_tac[ml_progTheory.Decls_def, evaluate_prog_RTC_call_FFI_rel]
  \\ simp[Abbr`A`,Abbr`B`]
  \\ drule (GEN_ALL call_main_thm1)
  \\ rpt (disch_then drule)
  \\ simp[] \\ strip_tac
  \\ asm_exists_tac \\ simp[]
  \\ reverse conj_tac >- metis_tac[]
  \\ Cases_on `parts_ok st3.ffi (proj1, proj2)`
  >-(`st3.ffi.final_event = NONE` by fs[cfStoreTheory.parts_ok_def]
    \\ imp_res_tac prog_to_semantics_prog \\ rfs[])
  \\ fs[ml_progTheory.Decls_def]
  \\ fs[cfStoreTheory.st2heap_def, cfStoreTheory.ffi2heap_def,cfHeapsBaseTheory.SPLIT3_def]
  \\ `h3 <> {}` by metis_tac[FFI_part_hprop_def,MEMBER_NOT_EMPTY]
  \\ fs[FFI_part_hprop_def]
  \\ first_x_assum drule \\ strip_tac
  \\ fs[EXTENSION]
  \\ last_x_assum(qspec_then`FFI_part s u ns us`mp_tac)
  \\ simp[FFI_part_NOT_IN_store2heap]
);

val _ = export_theory()
