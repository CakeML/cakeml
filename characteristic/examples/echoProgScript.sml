open preamble
     semanticPrimitivesTheory
     ml_translatorTheory ml_translatorLib ml_progLib
     cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib
     mlcommandLineProgTheory basisFunctionsLib
     semanticsLib ioProgTheory mlcharioProgTheory
 

val _ = new_theory "echoProg";

val _ = translation_extends"mlcommandLineProg";

(*TODO: update this to include Char.fromByte and move to a more appropriate location*)
val print = process_topdecs
  `fun print s =
    let 
      val l = String.explode s
      val nl = List.map_1 (Char.ord) l
      val bl = List.map_1 (Word8.fromInt) nl
    in write_list bl end`

val res = ml_prog_update(ml_progLib.add_prog print pick_name)

val echo = process_topdecs
  `fun echo u = 
      let 
        val cl = Commandline.arguments ()
        val cls = String.concatwith " " cl
      in print cls end`

val res = ml_prog_update(ml_progLib.add_prog echo pick_name)

val st = get_ml_prog_state()


(*TODO fix the use of map_1 instead of map *)
val map_1_v_thm = fetch "mllistProg" "map_1_v_thm";
val string_map_v_thm = save_thm("string_map_v_thm",
  map_1_v_thm |> INST_TYPE [alpha |-> ``:char``, beta|->``:num``])
val byte_map_v_thm = save_thm("byte_map_v_thm",
  map_1_v_thm |> INST_TYPE [alpha |-> ``:num``, beta|->``:word8``])


val print_spec = Q.store_thm("print_spec",
  `!s sv. STRING_TYPE s sv ==>
   app (p:'ffi ffi_proj) ^(fetch_v "print" st) [sv]
   (STDOUT output)
   (POSTv uv. &UNIT_TYPE () uv * STDOUT (output ++ MAP (n2w o ORD) (explode s)))`,  
    xcf "print" st
    \\ xlet `POSTv lv. & LIST_TYPE CHAR (explode s) lv * STDOUT output`
    >-(xapp \\ xsimpl \\ instantiate)
    \\ xlet `POSTv nlv. & LIST_TYPE NUM (MAP ORD (explode s)) nlv * STDOUT output`
    >-(xapp_spec string_map_v_thm \\ xsimpl \\ Cases_on `s` \\ fs[mlstringTheory.explode_thm]
      \\ instantiate \\ qexists_tac `ORD` \\ qexists_tac `NUM`  \\ rw[mlcharProgTheory.char_ord_v_thm])
    \\ xlet `POSTv blv. & LIST_TYPE (WORD:word8 -> v -> bool) (MAP n2w (MAP ORD (explode s))) blv * STDOUT output`    
    >-(xapp_spec byte_map_v_thm \\ xsimpl \\ Cases_on `s` \\ fs[mlstringTheory.explode_thm]
      \\ instantiate \\ qexists_tac `n2w` \\ qexists_tac `WORD` \\ rw[mlword8ProgTheory.word8_fromint_v_thm])
    \\ xapp \\ fs[MAP_MAP_o] 
);

val echo_spec = Q.store_thm("echo_spec",
  `!ls. cl <> [] /\ EVERY validArg cl /\
   LENGTH (MAP ((n2w:num -> word8) o ORD) (FLAT (MAP (\s. (s) ++ [CHR 0]) (cl)))) < 257 ==>
   app (p:'ffi ffi_proj) ^(fetch_v "echo" st) [Conv NONE []]
   (STDOUT output * COMMANDLINE cl)
   (POSTv uv. &UNIT_TYPE () uv * (STDOUT (output ++ MAP (n2w o ORD) (CONCAT_WITH " " (TL cl))) * COMMANDLINE cl))`,
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
    \\ xapp \\ qexists_tac `COMMANDLINE cl` \\ xsimpl \\ qexists_tac `implode (CONCAT_WITH " " (TL cl))` \\ qexists_tac `output`
    \\ rw[mlstringTheory.explode_implode] \\ xsimpl 
);

val echo_ffi_oracle_def = Define `
  (echo_ffi_oracle:((string list) # (word8 list)) oracle) = 
    \name (cls, out) bytes.
      if name = "putChar" then
        case bytes of
        | [b] => Oracle_return (cls, out ++ [b]) [b]
        | _ => Oracle_fail
      else if name = "getArgs" then
        case ffi_getArgs bytes cls of
          | SOME(bytes, cls) => Oracle_return (cls, out) bytes
          | NONE => Oracle_fail
      else Oracle_fail`

val echo_ffi_def = Define `
  echo_ffi (cls: string list) =
    <| oracle := echo_ffi_oracle
     ; ffi_state := (cls, [])
     ; final_event := NONE
     ; io_events := [] |>`;  


val echo_proj1_def = Define`
  echo_proj1 = (\(cl:string list, out:word8 list).
    FEMPTY |++ [("getArgs", List (MAP Str cl));("putChar", Str (MAP (CHR o w2n) out))])`

val echo_proj2_def = Define`
  echo_proj2 = [(["getArgs"], commandLine_fun);(["putChar"], stdout_fun)]`;

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
  EVAL_TAC \\ every_case_tac \\ rw[] \\ Cases_on`bytes` \\ fs[]);

val OPT_MMAP_MAP_o = Q.store_thm("OPT_MMAP_MAP_o",
  `!ls. OPT_MMAP f (MAP g ls) = OPT_MMAP (f o g) ls`,
  Induct \\ rw[OPT_MMAP_def]);

val destStr_o_Str = Q.store_thm("destStr_o_Str[simp]",
  `destStr o Str = SOME`, rw[FUN_EQ_THM]);

val OPT_MMAP_SOME = Q.store_thm("OPT_MMAP_SOME[simp]",
  `OPT_MMAP SOME ls = SOME ls`,
  Induct_on`ls` \\ rw[OPT_MMAP_def]);

(* -- *)

val parts_ok_echo_proj = Q.store_thm("parts_ok_echo_proj",
  `parts_ok (echo_ffi cls) (echo_proj1, echo_proj2)`,
  rw[cfStoreTheory.parts_ok_def,echo_proj2_def,echo_ffi_def,echo_proj1_def,FUPDATE_LIST_THM,FLOOKUP_UPDATE]
  \\ rw[] \\ fs[commandLine_fun_def]
  \\ rpt(pairarg_tac \\ fs[]) \\ rw[]
  \\ imp_res_tac ffi_getArgs_length
  \\ imp_res_tac stdout_fun_length \\ fs[]
  \\ fs[FAPPLY_FUPDATE_THM]
  \\ rw[echo_ffi_oracle_def]
  \\ fs[decode_def,cfHeapsBaseTheory.decode_list_def,OPT_MMAP_MAP_o,FUPDATE_LIST_THM,encode_def,cfHeapsBaseTheory.encode_list_def,FUPDATE_COMMUTES]
  \\ every_case_tac \\ fs[stdout_fun_def,FUPDATE_COMMUTES]);



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

(*----------------------------------------------------------------------------------------*)
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

(*TODO: Need to generalize this to not just STDOUT x by changing STDOUT x to Q, and having some assumption about Q e.g. Q h1 ==> A IN ffi_part h1 ==> A = STDOUT, COMMANDLINE, STDIN *)
val call_main_thm2 = Q.store_thm("call_main_thm2",
`ML_code env1 st1 prog NONE env2 st2 ==> 
   lookup_var fname env2 = SOME fv ==> 
  app (proj1, proj2) fv [Conv NONE []] P (POSTv uv. &UNIT_TYPE () uv * STDOUT x) ==>     
  SPLIT (st2heap (proj1, proj2) st2) (h1,h2) /\ P h1  /\
  no_dup_mods (SNOC ^main_call prog) st1.defined_mods /\ 
  no_dup_top_types (SNOC ^main_call prog) st1.defined_types /\
  parts_ok st2.ffi (proj1, proj2) 
  ==>  
    ∃st3.
    semantics_prog st1 env1  (SNOC ^main_call prog) (Terminate Success st3.ffi.io_events) /\
    (?h3 h4. SPLIT3 (st2heap (proj1, proj2) st3) (h3,h2,h4) /\ (STDOUT x) h3)`,
  rw[]
  \\ imp_res_tac call_main_thm1 \\ fs[]
  (*gets rid of extra assumptions *)
  \\ first_x_assum(fn th => rw[th])
  \\ first_x_assum(fn th => rw[th])
  \\ first_x_assum(fn th => rw[th])
  \\ qexists_tac `st3`
  \\ reverse conj_tac >-(qexists_tac `h3` \\ qexists_tac `h4` \\ fs[]) 
  \\ Cases_on `parts_ok st3.ffi (proj1, proj2)`
  >-(`st3.ffi.final_event = NONE` by fs[cfStoreTheory.parts_ok_def]
    \\ imp_res_tac prog_to_semantics_prog \\ rfs[])
  \\ fs[ml_progTheory.Prog_def]
  \\ fs[STDOUT_def, cfHeapsBaseTheory.IO_def, set_sepTheory.SEP_EXISTS_THM, set_sepTheory.SEP_CLAUSES] 
  \\ fs[set_sepTheory.one_STAR] 
  \\ `FFI_part (Str (MAP (CHR ∘ w2n) x)) stdout_fun ["putChar"] events IN (st2heap (proj1, proj2) st3)`
        by cfHeapsBaseLib.SPLIT_TAC  
  \\ fs[cfStoreTheory.st2heap_def, cfStoreTheory.FFI_part_NOT_IN_store2heap]
  \\ rfs[cfStoreTheory.ffi2heap_def]
);

val ML_code_thm = get_ml_prog_state() |> remove_snocs |> get_thm
val env = init_state |> remove_snocs |> get_env
val state = init_state |> remove_snocs |> get_state
val prog =  ML_code_thm |> SPEC_ALL |> concl |> rator |> rator |> rator |> rand 

val echo_dlet = mk_main_call (stringSyntax.fromMLstring "echo");
val echo_prog_tm = listSyntax.mk_snoc(echo_dlet,prog);
val echo_prog_def = Define`
  echo_prog = ^echo_prog_tm`;

Q.store_thm("no_dup_mods_echo",
  `no_dup_mods ^echo_prog_tm ^state.defined_mods`,
  CONV_TAC(RAND_CONV EVAL)
  \\ CONV_TAC(RATOR_CONV(RAND_CONV EVAL)) (* this is only for the snoc *)
  \\ CONV_TAC(no_dup_mods_conv)
);  

Q.store_thm ("no_dup_tops_types_echo",
  `no_dup_top_types ^echo_prog_tm ^state.defined_types`,
  CONV_TAC(RAND_CONV EVAL)
  \\ CONV_TAC(RATOR_CONV(RAND_CONV EVAL)) (* this is only for the snoc *)
  \\ CONV_TAC(no_dup_top_types_conv)
);


(*TODO:  Fix call_main_thm2 and apply in this fashion *)
val call_thm_instantiated1 =
  call_main_thm1
  |> C MATCH_MP ML_code_thm
  |> Q.GENL[`fv`,`fname`] |> Q.SPEC`"echo"`
  |> CONV_RULE(QUANT_CONV(LAND_CONV(LAND_CONV EVAL THENC SIMP_CONV std_ss [])))
  |> CONV_RULE(HO_REWR_CONV UNWIND_FORALL_THM1)
  |> C MATCH_MP (echo_spec |> SPEC_ALL |> UNDISCH)
  |> Q.GEN `ffi` |> ISPEC ``echo_ffi cls``
  |> Q.INST [`p`|->`(echo_proj1,echo_proj2)`]
  |> UNDISCH



(* May need to do something with this to change reasoning about h1
  |> CONV_RULE(LAND_CONV(SIMP_CONV(srw_ss())[STAR_def,STDOUT_def,COMMANDLINE_def,PULL_EXISTS])) *)

(*----------------------------------------------------------------------------------------*)
(*SOME USEFUL LEMMAS*)



(* TODO: Fix this attempt to specify what the output of a program is on an abstract level


val extract_output_not_putChar = Q.prove(
    `!xs name bytes. name <> "putChar" ==>
      extract_output (xs ++ [IO_event name bytes]) = extract_output xs`,
      rw[extract_output_APPEND, extract_output_def] \\ Cases_on `extract_output xs` \\ rw[]
);


val RTC_call_FFI_rel_IMP = Q.store_thm("RTC_call_FFI_rel_IMP",
  `!st st'.
    call_FFI_rel^* st.ffi st'.ffi ==>
    extract_output st.ffi.io_events = SOME(SND(st.ffi.ffi_state)) ==>
    extract_output st'.ffi.io_events = SOME(SND(st'.ffi.ffi_state))`,
    cheat
);

val extract_output_STDOUT = Q.prove(
    `!env1 s1 prog env2 s2 proj1 proj2 h1 x. 
      Prog env1 s1 prog env2 s2 /\
      SPLIT3 (st2heap (proj1, proj2) s2) (h1, h2, h3) /\
     (STDOUT x) h1 ==>
(* these should be assumptions in the proof - they just mean the oracle is correctly constructed *)
         extract_output s1.ffi.io_events = 
             SOME ((MAP (n2w o ORD))(THE(destStr (proj1 (s1.ffi.ffi_state) ' "putChar")))) ==>  
    extract_output s2.ffi.io_events = SOME (x) /\
    destStr (proj1 (s2.ffi.ffi_state) ' "putChar") = SOME (MAP (CHR o w2n) x)`,
    simp[ml_progTheory.Prog_def] \\
    rpt gen_tac \\ strip_tac \\
    imp_res_tac evaluate_prog_RTC_call_FFI_rel
(*a generalised version of RTC_call_FFI_rel_IMP_io_events needs to be made *) 
    \\ qho_match_abbrev_tac`extract_output _ = SOME (getOutput s1.ffi.ffi_state) ==> _`
    \\ strip_tac
    \\ drule RTC_call_FFI_rel_IMP (*this is cheated *)
    \\ simp[]
    \\ strip_tac
    \\ fs [STDOUT_def,cfHeapsBaseTheory.IO_def,
            set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM]
    \\ fs[set_sepTheory.one_STAR, cfStoreTheory.st2heap_def]
    \\ `FFI_part (Str (MAP (CHR o w2n) x)) stdout_fun ["putChar"] events IN
            (store2heap s2.refs ∪ ffi2heap (proj1, proj2) s2.ffi)` by cfHeapsBaseLib.SPLIT_TAC
    \\ fs[cfStoreTheory.FFI_part_NOT_IN_store2heap]
    \\ rfs[cfStoreTheory.ffi2heap_def, Abbr `getOutput`, FLOOKUP_DEF]
    \\ Cases_on `parts_ok s2.ffi (proj1, proj2)` \\ fs[]
    \\ rw[MAP_MAP_o, n2w_ORD_CHR_w2n] 
);


val ffi_outcomes = Q.prove(
  `!proj1 proj2 h1 h2 h3. 
  SPLIT3 (st2heap (proj1, proj2) s2) (h1, h2, h3) /\ (STDOUT x) h1 /\
  Prog init_env s1 prog env2 s2 /\
  parts_ok s2.ffi (proj1, proj2) /\  
  extract_output s1.ffi.io_events = 
             SOME ((MAP (n2w o ORD))(THE(destStr (proj1 (s1.ffi.ffi_state) ' "putChar")))) 
  ==>
  Prog init_env s1 prog env2 s2 /\
  s2.ffi.final_event = NONE /\  (*this allows us to use prog_to_semantics_prog*)
  extract_output s2.ffi.io_events = SOME (x)`,
  (*this should suffice to prove the overall goal *)
  rw[] >- fs[cfStoreTheory.parts_ok_def] 
  \\ drule extract_output_STDOUT
  \\ strip_tac
  \\ first_x_assum (qspecl_then [`proj1`, `proj2`, `h1`, `x`] mp_tac) \\ rw[]
);

*)


val _ = export_theory();
