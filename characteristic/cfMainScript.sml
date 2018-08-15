open preamble
     semanticPrimitivesTheory
     ml_translatorTheory ml_translatorLib ml_progLib
     cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib
     semanticsLib evaluatePropsTheory

val _ = new_theory "cfMain";

(*
   The following section culminates in call_main_thm2 which takes a
   spec and some aspects of the current state, and proves a
   Semantics_prog statement. It also proves call_FFI_rel^* between the
   initial state, and the state after creating the prog and then
   calling the main function - this is useful for theorizing about the
   output of the program
*)

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
  \\ simp[ml_progTheory.Decls_def]
  \\ fs [terminationTheory.evaluate_decs_def,PULL_EXISTS,
         EVAL ``(pat_bindings (Pcon NONE []) [])``,pair_case_eq,result_case_eq]
  \\ fs [terminationTheory.evaluate_def,PULL_EXISTS,pair_case_eq,
         result_case_eq,do_con_check_def,build_conv_def,bool_case_eq,
         ml_progTheory.lookup_var_def,option_case_eq,match_result_case_eq,
         EVAL ``nsLookup (merge_env env2 env1).v (Short fname)``,app_def,
         app_basic_def]
  \\ first_x_assum drule \\ fs [] \\ strip_tac \\ fs []
  \\ fs [cfHeapsBaseTheory.POSTv_def]
  \\ Cases_on `r` \\ fs [cond_STAR] \\ fs [cond_def]
  \\ fs [UNIT_TYPE_def] \\ rveq \\ fs []
  \\ fs [ml_progTheory.Decls_def,evaluate_ck_def]
  \\ drule evaluate_add_to_clock
  \\ disch_then (qspec_then `ck2` mp_tac) \\ simp []
  \\ qpat_x_assum `_ env1 prog = _` assume_tac
  \\ drule evaluate_decs_add_to_clock
  \\ disch_then (qspec_then `ck` mp_tac) \\ simp []
  \\ rpt strip_tac
  \\ once_rewrite_tac [CONJ_COMM]
  \\ `evaluate_decs (st1 with clock := ck + ck1) env1 prog =
         (st2 with clock := ck + ck2,Rval env2)` by fs []
  \\ asm_exists_tac \\ fs []
  \\ once_rewrite_tac [CONJ_COMM] \\ rewrite_tac [GSYM CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM] \\ rewrite_tac [GSYM CONJ_ASSOC]
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ fs [evaluateTheory.dec_clock_def]
  \\ `evaluate (st2 with clock := (ck + ck2 + 1) - 1) env [exp] =
        ((st' with clock := st2.clock) with clock := ck2 + st'.clock,
         Rval [Conv NONE []])` by fs []
  \\ asm_exists_tac \\ fs [terminationTheory.pmatch_def]
  \\ fs [ml_progTheory.merge_env_def]
  \\ fs [cfStoreTheory.st2heap_clock]
  \\ asm_exists_tac \\ fs []);

val prog_to_semantics_prog = Q.prove(
  `!init_env inp prog st c r env2 s2.
     Decls init_env inp prog env2 s2 ==>
     (semantics_prog  inp init_env prog (Terminate Success s2.ffi.io_events))`,
  rw[ml_progTheory.Decls_def]
  \\ fs[semanticsTheory.semantics_prog_def,PULL_EXISTS]
  \\ fs[semanticsTheory.evaluate_prog_with_clock_def]
  \\ qexists_tac `ck1` \\ fs []
  \\ CCONTR_TAC \\ fs []
  \\ pairarg_tac \\ fs [] \\ rveq
  \\ drule evaluate_decs_add_to_clock
  \\ disch_then (qspec_then `ck1` mp_tac)
  \\ qpat_x_assum `_ = (_,Rval _)` assume_tac
  \\ drule evaluate_decs_add_to_clock
  \\ disch_then (qspec_then `k` mp_tac)
  \\ rpt strip_tac \\ fs []);

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
  \\ `?st3. Decls env1 st1 (SNOC ^main_call prog) env2 st3
            /\ B st3 /\ C st1 st3`
         suffices_by metis_tac[prog_to_semantics_prog]
  \\ reverse (sg `?st3. Decls env1 st1 (SNOC ^main_call prog) env2 st3 ∧ B st3`)
  THEN1 (asm_exists_tac \\ fs [Abbr`C`]
         \\ fs [ml_progTheory.ML_code_def,ml_progTheory.Decls_def]
         \\ imp_res_tac evaluate_decs_call_FFI_rel_imp \\ fs [])
  \\ simp[Abbr`A`,Abbr`B`]
  \\ drule (GEN_ALL call_main_thm1)
  \\ rpt (disch_then drule)
  \\ simp[] \\ strip_tac
  \\ asm_exists_tac \\ simp[]);

val _ = export_theory()
