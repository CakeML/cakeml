open preamble
     semanticPrimitivesTheory
     ml_translatorTheory ml_translatorLib ml_progLib
     cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib
     mlcommandLineProgTheory basisFunctionsLib
     semanticsLib ioProgTheory mlcharioProgTheory
 

val _ = new_theory "echoProg";

val _ = translation_extends"mlcommandLineProg";

val echo = process_topdecs
  `fun echo u = 
      let 
        val cl = Commandline.arguments ()
        val cls = String.concatwith " " cl
        val ok = print cls
      in CharIO.write (Word8.fromInt 10) end`

val res = ml_prog_update(ml_progLib.add_prog echo pick_name)

val st = get_ml_prog_state()

val echo_spec = Q.store_thm("echo_spec",
  `!ls b bv. cl <> [] /\ EVERY validArg cl /\
   LENGTH (MAP ((n2w:num -> word8) o ORD) (FLAT (MAP (\s. (s) ++ [CHR 0]) (cl)))) < 257 ==>
   app (p:'ffi ffi_proj) ^(fetch_v "echo" st) [Conv NONE []]
   (STDOUT output * COMMANDLINE cl)
   (POSTv uv. &UNIT_TYPE () uv * (STDOUT (output ++ (CONCAT_WITH " " (TL cl)) ++ [CHR 10]) * COMMANDLINE cl))`,
    xcf "echo" st
    \\ xlet `POSTv zv. & UNIT_TYPE () zv * STDOUT output * COMMANDLINE cl` 
    >-(xcon \\ xsimpl)
    \\ xlet `POSTv argv. & LIST_TYPE STRING_TYPE (TL (MAP implode cl)) argv * STDOUT output
      * COMMANDLINE cl`
    >-(xapp \\ instantiate \\ qexists_tac `STDOUT output` \\ xsimpl)
    \\ xlet `POSTv clv. STDOUT output * COMMANDLINE cl * & STRING_TYPE (implode (CONCAT_WITH " " (TL cl))) clv`
    >-(xapp \\ xsimpl \\ instantiate
      \\ rw[mlstringTheory.concatWith_CONCAT_WITH, mlstringTheory.implode_explode, Once mlstringTheory.implode_def]
      \\ Cases_on `cl` \\ fs[mlstringTheory.implode_def])
    \\ xlet `POSTv xv. &UNIT_TYPE () xv * STDOUT (output ++ (CONCAT_WITH " " (TL cl))) * COMMANDLINE cl`
    >-(xapp \\ qexists_tac `COMMANDLINE cl` \\ xsimpl \\ qexists_tac `implode (CONCAT_WITH " " (TL cl))` \\ qexists_tac `output`
      \\ rw[mlstringTheory.explode_implode] \\ xsimpl)
    \\ xlet `POSTv u. STDOUT (output ++ (CONCAT_WITH " " (TL cl))) * COMMANDLINE cl * & WORD (n2w 10:word8) u`
    >-(xapp \\ xsimpl)
    \\ xapp \\ map_every qexists_tac [`COMMANDLINE cl`, `output ++ (CONCAT_WITH " " (TL cl))`, `n2w 10`] \\ xsimpl
);

(*-------------------------------------------------------------------------------------------------*)
(* GENERALISED FFI *)

val basis_ffi_oracle_def = Define `
  basis_ffi_oracle =
    \name (inp, out,cls) bytes.
     if name = "putChar" then
       case ffi_putChar bytes out of
       | SOME (bytes,out) => Oracle_return (inp,out,cls) bytes
       | _ => Oracle_fail else
     if name = "getChar" then
       case ffi_getChar bytes inp of
       | SOME (bytes,inp) => Oracle_return (inp,out,cls) bytes
       | _ => Oracle_fail else
     if name = "getArgs" then
       case ffi_getArgs bytes cls of
       | SOME (bytes,cls) => Oracle_return (inp,out,cls) bytes
       | _ => Oracle_fail else
     Oracle_fail`


(*Output is always empty to start *)
val basis_ffi_def = Define `
  basis_ffi (inp: string) (cls: string list) = 
    <| oracle := basis_ffi_oracle
     ; ffi_state := (inp, [], cls)
     ; final_event := NONE
     ; io_events := [] |>`; 
 
val basis_proj1_def = Define `
  basis_proj1 = (\(inp, out, cls).
    FEMPTY |++ [("putChar", Str out);("getChar",Str inp);("getArgs", List (MAP Str cls))])`;

val basis_proj2_def = Define `
  basis_proj2 = [(["putChar"],stdout_fun);(["getChar"],stdin_fun); (["getArgs"], commandLine_fun)]`;

(*-------------------------------------------------------------------------------------------------*)

(* TODO: move to where these are defined *)
(*
val valid_ffi_def = Define`
  valid_ffi f 
  preserves length
  anything else?
  *)
val ffi_getArgs_length = Q.store_thm("ffi_getArgs_length",
  `ffi_getArgs bytes cls = SOME (bytes',cls') ==> LENGTH bytes' = LENGTH bytes`,
  EVAL_TAC \\ rw[] \\ rw[]);

val stdout_fun_length = Q.store_thm("stdout_fun_length",
  `stdout_fun m bytes w = SOME (bytes',w') ==> LENGTH bytes' = LENGTH bytes`,
  EVAL_TAC \\ every_case_tac \\ rw[] \\ Cases_on`bytes` \\ fs[]
  \\ fs[ffi_putChar_def] \\ Cases_on `t`  \\ fs[]
  \\ var_eq_tac \\ fs[] \\ rw[] 
  );

val OPT_MMAP_MAP_o = Q.store_thm("OPT_MMAP_MAP_o",
  `!ls. OPT_MMAP f (MAP g ls) = OPT_MMAP (f o g) ls`,
  Induct \\ rw[OPT_MMAP_def]);

val destStr_o_Str = Q.store_thm("destStr_o_Str[simp]",
  `destStr o Str = SOME`, rw[FUN_EQ_THM]);

val OPT_MMAP_SOME = Q.store_thm("OPT_MMAP_SOME[simp]",
  `OPT_MMAP SOME ls = SOME ls`,
  Induct_on`ls` \\ rw[OPT_MMAP_def]);


(* TODO: Generalise the heap requirements for STDOUT, COMMANDLINE, etc. so that the assumptions can be discharged in the proof 
val STDOUT_precond = Q.store_thm("STDOUT_precond",
  `MEM (["putChar"], stdout_fun) parts /\ FLOOKUP (proj h.ffi.ffi_state) "putChar" = SOME (Str (MAP (CHR ∘ w2n) output)) /\ 
    Mem 1 (W8array x) ∈ store2heap h.refs /\ LENGTH x = 1 /\ parts_ok h.ffi (proj, parts) ==>
    (STDOUT output) (store2heap h.refs ∪ ffi2heap (proj, parts) h.ffi)`, 
    rw[STDOUT_def, cfHeapsBaseTheory.IO_def] 
    \\ rw[STDOUT_def, cfHeapsBaseTheory.IO_def,
          set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
            EVAL ``write_state_loc``,
            cfHeapsBaseTheory.W8ARRAY_def,
            cfHeapsBaseTheory.cell_def]
  \\ fs[GSYM set_sepTheory.STAR_ASSOC,set_sepTheory.one_STAR]       
  \\ fs[Once set_sepTheory.STAR_COMM]
  \\ fs[GSYM set_sepTheory.STAR_ASSOC,set_sepTheory.one_STAR]
  \\ fs [cfStoreTheory.FFI_part_NOT_IN_store2heap]
  \\ fs[cfStoreTheory.ffi2heap_def] \\ rw[] \\ rw[] 
  \\ fs[set_sepTheory.cond_def] \\ fs[LENGTH_EQ_NUM_compute]
);
*)

(*-------------------------------------------------------------------------------------------------*)

(*The following section culminates in call_main_thm2 which takes a spec and some aspects
  of the current state, and proves a Semantics_prog statement. It also proves call_FFI_rel^*
  between the initial state, and the state after creating the prog and then calling the main
  function - this is useful for theorizing about the output of the program  *)

fun mk_main_call s =
(* TODO: don't use the parser so much here? *)
  ``Tdec (Dlet (Pcon NONE []) (App Opapp [Var (Short ^s); Con NONE []]))``;

val fname = mk_var("fname",``:string``);
val main_call = mk_main_call fname;

val call_main_thm1 = Q.store_thm("call_main_thm1",
`ML_code env1 st1 prog NONE env2 st2 ==> (* get this from the current ML prog state *)
 lookup_var fname env2 = SOME fv ==> (* get this by EVAL *)
  app p fv [Conv NONE []] P (POSTv uv. &UNIT_TYPE () uv * Q) ==> (* this should be the CF spec you prove for the "main" function *)  
    SPLIT (st2heap p st2) (h1,h2) /\ P h1 ==>  (* this might need simplification, but some of it may need to stay on the final theorem *) 
    ∃st3.
    Prog env1 st1 (SNOC ^main_call prog) env2 st3 /\
    (?h3 h4. SPLIT3 (st2heap p st3) (h3,h2,h4) /\ Q h3)`,
  rw[ml_progTheory.ML_code_def,SNOC_APPEND,ml_progTheory.Prog_APPEND,ml_progTheory.Prog_Tdec,PULL_EXISTS]
  \\ asm_exists_tac \\ fs[]
  \\ simp[ml_progTheory.Decls_def]
  \\ ONCE_REWRITE_TAC [bigStepTheory.evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ONCE_REWRITE_TAC [bigStepTheory.evaluate_decs_cases] \\ SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC (srw_ss()) [astTheory.pat_bindings_def,ALL_DISTINCT,MEM,
       pmatch_def, bigStepTheory.evaluate_dec_cases,combine_dec_result_def]
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
  \\ fs[lookup_var_def,ALOOKUP_APPEND]
  \\ reverse every_case_tac >- fs[cond_def] \\ fs[]
  \\ fs[evaluate_ck_def,funBigStepEquivTheory.functional_evaluate_list]
  \\ fs[Once (CONJUNCT2 bigStepTheory.evaluate_cases)]
  \\ fs[Once (CONJUNCT2 bigStepTheory.evaluate_cases)]
  \\ imp_res_tac cfAppTheory.big_remove_clock \\ fs[]
  \\ first_x_assum(qspec_then`st2.clock`mp_tac)
  \\ simp[semanticPrimitivesPropsTheory.with_same_clock]
  \\ strip_tac \\ asm_exists_tac \\ simp[]
  \\ fs[STAR_def,cond_def,UNIT_TYPE_def]
  \\ CONV_TAC(STRIP_QUANT_CONV(LAND_CONV (LAND_CONV EVAL))) \\ simp[]
  \\ srw_tac[QI_ss][ml_progTheory.merge_env_def,environment_component_equality,cfStoreTheory.st2heap_clock]
  \\ asm_exists_tac \\ fs[cfHeapsBaseTheory.SPLIT_emp1] \\ rw[]
);

val prog_to_semantics_prog = Q.prove(
    `!init_env inp prog st c r env2 s2. 
    no_dup_mods prog inp.defined_mods /\ 
    no_dup_top_types prog inp.defined_types /\ 
    Prog init_env inp prog env2 s2 /\ 
    s2.ffi.final_event = NONE (*This will comes from FFI_outcomes*) ==>
    (semantics_prog  inp init_env prog (Terminate Success s2.ffi.io_events))`,
    rw[ml_progTheory.Prog_def] \\ 
    `evaluate_whole_prog F init_env' inp prog (s2,env2.c,Rval (env2.m,env2.v))` by simp[bigStepTheory.evaluate_whole_prog_def]
    \\ imp_res_tac evaluate_prog_rel_IMP_evaluate_prog_fun 
    \\ fs[semanticsTheory.semantics_prog_def,PULL_EXISTS]
    \\ fs[semanticsTheory.evaluate_prog_with_clock_def]
    \\ qexists_tac `k` \\ fs[]
    \\ rw[] \\ pairarg_tac \\ fs[]
    \\ pop_assum mp_tac
    \\ drule evaluatePropsTheory.evaluate_prog_clock_determ
    \\ ntac 2 strip_tac \\ first_x_assum drule
    \\ fs[] \\ rpt (CASE_TAC \\ fs[])    
);

val FFI_part_hprop_def = Define`
  FFI_part_hprop Q =
   (!h. Q h ==> (?s u ns us. FFI_part s u ns us IN h))`;

val FFI_part_hprop_STAR = Q.store_thm("FFI_part_hprop_STAR",
  `FFI_part_hprop P \/ FFI_part_hprop Q ==> FFI_part_hprop (P * Q)`,
  rw[FFI_part_hprop_def]
  \\ fs[set_sepTheory.STAR_def,SPLIT_def] \\ rw[]
  \\ metis_tac[]);

val STDOUT_FFI_part_hprop = Q.store_thm("STDOUT_FFI_part_hprop",
  `FFI_part_hprop (STDOUT x)`,
  rw [STDIN_def,STDOUT_def,cfHeapsBaseTheory.IO_def,FFI_part_hprop_def,
    set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
    EVAL ``read_state_loc``,
    EVAL ``write_state_loc``,
    cfHeapsBaseTheory.W8ARRAY_def,
    cfHeapsBaseTheory.cell_def]
  \\ fs[set_sepTheory.one_STAR]
  \\ metis_tac[]);



val STDIN_FFI_part_hprop = Q.store_thm("STDIN_FFI_part_hprop",
  `FFI_part_hprop (STDIN b x)`,
  rw [STDIN_def,STDOUT_def,cfHeapsBaseTheory.IO_def,FFI_part_hprop_def,
    set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
    EVAL ``read_state_loc``,
    EVAL ``write_state_loc``,
    cfHeapsBaseTheory.W8ARRAY_def,
    cfHeapsBaseTheory.cell_def]
  \\ fs[set_sepTheory.one_STAR]
  \\ metis_tac[]);

val COMMANDLINE_FFI_part_hprop = Q.store_thm("COMMANDLINE_FFI_part_hprop",
  `FFI_part_hprop (COMMANDLINE x)`,
  rw [COMMANDLINE_def,cfHeapsBaseTheory.IO_def,FFI_part_hprop_def,
    set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM]
  \\ fs[set_sepTheory.one_def]);


val call_main_thm2 = Q.store_thm("call_main_thm2",
  `ML_code env1 st1 prog NONE env2 st2 ==> 
   lookup_var fname env2 = SOME fv ==> 
  app (proj1, proj2) fv [Conv NONE []] P (POSTv uv. &UNIT_TYPE () uv * Q) ==>     
  FFI_part_hprop Q ==>
  no_dup_mods (SNOC ^main_call prog) st1.defined_mods /\ 
  no_dup_top_types (SNOC ^main_call prog) st1.defined_types ==>
  SPLIT (st2heap (proj1, proj2) st2) (h1,h2) /\ P h1 
  ==>  
    ∃st3.
    semantics_prog st1 env1  (SNOC ^main_call prog) (Terminate Success st3.ffi.io_events) /\
    (?h3 h4. SPLIT3 (st2heap (proj1, proj2) st3) (h3,h2,h4) /\ Q h3) /\
    call_FFI_rel^* st1.ffi st3.ffi`,
  rw[]
  \\ qho_match_abbrev_tac`?st3. A st3 /\ B st3 /\ C st1 st3`
  \\ `?st3. Prog env1 st1 (SNOC ^main_call prog) env2 st3 ∧ st3.ffi.final_event = NONE /\ B st3 /\ C st1 st3`
  suffices_by metis_tac[prog_to_semantics_prog]
  \\ `?st3. Prog env1 st1 (SNOC ^main_call prog) env2 st3 ∧ st3.ffi.final_event = NONE /\ B st3`
  suffices_by metis_tac[ml_progTheory.Prog_def, evaluate_prog_RTC_call_FFI_rel]
  \\ simp[Abbr`A`,Abbr`B`]
  \\ drule (GEN_ALL call_main_thm1)
  \\ rpt (disch_then drule)
  \\ simp[] \\ strip_tac
  \\ asm_exists_tac \\ simp[]
  \\ reverse conj_tac >- metis_tac[]
  \\ Cases_on `parts_ok st3.ffi (proj1, proj2)`
  >-(`st3.ffi.final_event = NONE` by fs[cfStoreTheory.parts_ok_def]
    \\ imp_res_tac prog_to_semantics_prog \\ rfs[])
  \\ fs[ml_progTheory.Prog_def]
  \\ fs[cfStoreTheory.st2heap_def, cfStoreTheory.ffi2heap_def,cfHeapsBaseTheory.SPLIT3_def]
  \\ `h3 <> {}` by metis_tac[FFI_part_hprop_def,MEMBER_NOT_EMPTY]
  \\ fs[FFI_part_hprop_def]
  \\ first_x_assum drule \\ strip_tac
  \\ fs[EXTENSION]
  \\ last_x_assum(qspec_then`FFI_part s u ns us`mp_tac)
  \\ simp[FFI_part_NOT_IN_store2heap]
);


(*-------------------------------------------------------------------------------------------------*)
(*These theorems are the theorems necessary if you use a projs, oracle and ffi that aren't
  basis_ffi*)

(*RTC_call_FFI_rel_IMP_basis_events show that extracting output from two ffi_states will use the 
  same function if the two states are related by a series of FFI_calls. If this is the case for
  your oracle (and projs), then this proof should be relatively similar. Note
  that to make the subsequent proofs similar one should show an equivalence between
  extract_output and proj1  *)

val RTC_call_FFI_rel_IMP_basis_events = Q.store_thm ("RTC_call_FFI_rel_IMP_basis_events",
  `!st st'. call_FFI_rel^* st st' ==>
  st.oracle = basis_ffi_oracle /\ 
  extract_output st.io_events = SOME (MAP (n2w o ORD) (THE (destStr (basis_proj1 st.ffi_state ' "putChar")))) ==>
  extract_output st'.io_events = SOME (MAP (n2w o ORD) (THE (destStr (basis_proj1 st'.ffi_state ' "putChar"))))`,
  HO_MATCH_MP_TAC RTC_INDUCT \\ rw [] \\ fs []
  \\ fs [evaluatePropsTheory.call_FFI_rel_def]
  \\ fs [ffiTheory.call_FFI_def]
  \\ Cases_on `st.final_event = NONE` \\ fs [] \\ rw []
  \\ FULL_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ FULL_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ Cases_on `f` \\ fs []
  \\ reverse (Cases_on `n = "putChar"`) \\ fs []
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ fs [extract_output_APPEND,extract_output_def, basis_proj1_def] \\ rfs []
  \\ (rpt (pairarg_tac \\ fs[])
    \\ fs[FUPDATE_LIST_THM, FAPPLY_FUPDATE_THM]
    \\ Cases_on `st.ffi_state` \\ fs[]
    \\ fs [basis_ffi_oracle_def]
    \\ every_case_tac \\ fs[])    
  \\ fs[ffi_putChar_def] \\ every_case_tac \\ fs[] 
  \\ rw[] \\ fs[]
  \\ first_x_assum match_mp_tac 
  \\ simp[n2w_ORD_CHR_w2n |> SIMP_RULE(srw_ss())[o_THM,FUN_EQ_THM]]
);


(*extract_output_basis_ffi shows that the first condition for the previous theorem holds for the 
  init_state ffi  *)

val extract_output_basis_ffi = Q.store_thm ("extract_output_basis_ffi",
  `extract_output (init_state (basis_ffi inp cls)).ffi.io_events = SOME (MAP (n2w o ORD) (THE (destStr (basis_proj1 (init_state (basis_ffi inp cls)).ffi.ffi_state ' "putChar"))))`,
  rw[ml_progTheory.init_state_def, extract_output_def, basis_ffi_def, basis_proj1_def, cfHeapsBaseTheory.destStr_def, FUPDATE_LIST_THM, FAPPLY_FUPDATE_THM]
);


(*call_main_thm_basis uses call_main_thm2 to get Semantics_prog, and then uses the previous two
  theorems to prove the outcome of extract_output. If RTC_call_FFI_rel_IMP* uses proj1, after
  showing that post-condition which gives effects your programs output is an FFI_part and 
  assuming that parts_ok is satisfied, an assumption about proj1 and the ffi_state should be
  derived which should fit the function on some st.ffi_state which returns extract_output on 
  st.io_events  *) 

val call_main_thm_basis = Q.store_thm("call_main_thm_basis",
`ML_code env1 (init_state (basis_ffi inp cls)) prog NONE env2 st2 ==> 
   lookup_var fname env2 = SOME fv ==> 
  app (basis_proj1, basis_proj2) fv [Conv NONE []] P (POSTv uv. &UNIT_TYPE () uv * (STDOUT x * Q)) ==>     
  no_dup_mods (SNOC ^main_call prog) (init_state (basis_ffi inp cls)).defined_mods /\
  no_dup_top_types (SNOC ^main_call prog) (init_state (basis_ffi inp cls)).defined_types ==>
  SPLIT (st2heap (basis_proj1, basis_proj2) st2) (h1,h2) /\ P h1 
  ==>  
    ∃(st3:(tvarN # tvarN # tvarN list) semanticPrimitives$state).
    semantics_prog (init_state (basis_ffi inp cls)) env1  (SNOC ^main_call prog) (Terminate Success st3.ffi.io_events) /\
    extract_output st3.ffi.io_events = SOME (MAP (n2w o ORD) x)`,
    rw[]
    \\ drule (GEN_ALL call_main_thm2)
    \\ rpt(disch_then drule)
    \\ simp[] \\ strip_tac
    \\ `FFI_part_hprop (STDOUT x * Q)` by metis_tac[FFI_part_hprop_def, STDOUT_FFI_part_hprop, FFI_part_hprop_STAR]
    \\ first_x_assum (qspecl_then [`h2`, `h1`] mp_tac) \\ rw[] \\ fs[]
    \\ qexists_tac `st3` \\ rw[]
    \\ `(THE (destStr (basis_proj1 st3.ffi.ffi_state ' "putChar"))) = x` suffices_by 
      (imp_res_tac RTC_call_FFI_rel_IMP_basis_events 
      \\ fs[extract_output_basis_ffi, ml_progTheory.init_state_def, basis_ffi_def]
      \\ qexists_tac `st3` 
      \\ rw[basis_proj1_def, cfHeapsBaseTheory.destStr_def, FUPDATE_LIST_THM, FAPPLY_FUPDATE_THM])
    \\ fs[STDOUT_def, cfHeapsBaseTheory.IO_def, set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM]
    \\ fs[GSYM set_sepTheory.STAR_ASSOC,set_sepTheory.one_STAR]
    \\ `FFI_part (Str x)
         stdout_fun ["putChar"] events ∈ (st2heap (basis_proj1,basis_proj2) st3)` by cfHeapsBaseLib.SPLIT_TAC
    \\ fs [cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap]
    \\ fs [cfStoreTheory.ffi2heap_def]
    \\ Cases_on `parts_ok st3.ffi (basis_proj1, basis_proj2)`
    \\ fs[FLOOKUP_DEF, MAP_MAP_o, n2w_ORD_CHR_w2n]
);


(*-------------------------------------------------------------------------------------------------*)

(*This should stay here - it is the expected workflow for getting the semantics and the output of
  a program using basis_projs, basis_oracle and basis_ffi*)

val ML_code_thm = get_ml_prog_state() |> remove_snocs |> get_thm
val env = init_state |> remove_snocs |> get_env
val state = init_state |> remove_snocs |> get_state
val prog =  ML_code_thm |> SPEC_ALL |> concl |> rator |> rator |> rator |> rand 

val echo_dlet = mk_main_call (stringSyntax.fromMLstring "echo");
val echo_prog_tm = listSyntax.mk_snoc(echo_dlet,prog);
val echo_prog_def = Define`
  echo_prog = ^echo_prog_tm`;

val no_dup_mods_echo = Q.store_thm("no_dup_mods_echo",
  `no_dup_mods ^echo_prog_tm ^state.defined_mods`,
  CONV_TAC(RAND_CONV EVAL)
  \\ CONV_TAC(RATOR_CONV(RAND_CONV EVAL)) (* this is only for the snoc *)
  \\ CONV_TAC(no_dup_mods_conv)
);  

val no_dup_tops_types_echo = Q.store_thm ("no_dup_tops_types_echo",
  `no_dup_top_types ^echo_prog_tm ^state.defined_types`,
  CONV_TAC(RAND_CONV EVAL)
  \\ CONV_TAC(RATOR_CONV(RAND_CONV EVAL)) (* this is only for the snoc *)
  \\ CONV_TAC(no_dup_top_types_conv)
);

val call_thm_echo =
  call_main_thm_basis
  |> C MATCH_MP (ML_code_thm |> Q.GEN `ffi` |> ISPEC ``basis_ffi inp cls``)
  |> Q.GENL[`fv`,`fname`] |> Q.SPEC`"echo"`
  |> CONV_RULE(QUANT_CONV(LAND_CONV(LAND_CONV EVAL THENC SIMP_CONV std_ss [])))
  |> CONV_RULE(HO_REWR_CONV UNWIND_FORALL_THM1)
  |> C MATCH_MP (
    echo_spec |> SPEC_ALL |> UNDISCH |> Q.GEN`p` |> Q.ISPEC`(basis_proj1, basis_proj2):(string#string#string list) ffi_proj` 
  )
  |> CONV_RULE(LAND_CONV(REWRITE_CONV[EQT_INTRO no_dup_mods_echo, EQT_INTRO no_dup_tops_types_echo]))
  |> C MATCH_MP TRUTH

(*-------------------------------------------------------------------------------------------------*)

(* TODO: Move these to somewhere relevant *) 
val extract_output_not_putChar = Q.prove(
    `!xs name bytes. name <> "putChar" ==>
      extract_output (xs ++ [IO_event name bytes]) = extract_output xs`,
      rw[extract_output_APPEND, extract_output_def] \\ Cases_on `extract_output xs` \\ rw[]
);

val extract_output_FILTER = Q.store_thm("extract_output_FILTER",
  `!st. extract_output st.ffi.io_events = extract_output (FILTER (ffi_has_index_in ["putChar"]) st.ffi.io_events)`,
  Cases_on `st` \\ Cases_on `f` \\ Induct_on `l'` \\ fs[]
  \\ simp_tac std_ss [Once CONS_APPEND, extract_output_APPEND]
  \\ fs[] \\ rw[extract_output_def] \\ full_case_tac 
  \\ Cases_on `extract_output (FILTER (ffi_has_index_in ["putChar"]) l')` \\ fs[]
  \\ simp_tac std_ss [Once CONS_APPEND, extract_output_APPEND] \\ fs[]
  \\ Cases_on `h` \\ Cases_on `s = "putChar"` \\ fs[cfStoreTheory.ffi_has_index_in_def, extract_output_def]
);


val _ = export_theory();
