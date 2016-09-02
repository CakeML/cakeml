open HolKernel Parse boolLib bossLib;
open preamble;
open ioProgTheory ml_translatorLib;

val _ = new_theory "compileProg"

val _ = translation_extends "ioProg";

val compile_def = Define `
  compile str =
    MAP (\c. n2w (ORD c)) ("  Hello world!  " ++ REVERSE str) :word8 list`;

val res = translate compile_def




open cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib ml_progLib

val main = parse_topdecl
  ("fun main u = let             " ^
   "  val u = []                 " ^
   "  val input = read_all u     " ^
   "  val bytes = compile input  " ^
   "  in write_list bytes end    ")

val _ = ml_prog_update (ml_progLib.add_prog main pick_name);

fun basis_st () = get_ml_prog_state ()

val main_spec = store_thm ("main_spec",
  ``!cv input output.
      app (p:'ffi ffi_proj) ^(fetch_v "main" (basis_st()))
        [cv]
        (CHAR_IO * STDIN input * STDOUT [])
        (\uv. CHAR_IO * STDIN "" * STDOUT (compile input))``,
  xcf "main" (basis_st())
  \\ xlet `\v. CHAR_IO * STDIN input * STDOUT [] * &(LIST_TYPE CHAR "" v)`
  THEN1 (xcon \\ fs [] \\ xsimpl \\ EVAL_TAC)
  \\ xlet `\x. CHAR_IO * STDIN "" * STDOUT [] * &(LIST_TYPE CHAR input x)`
  THEN1
   (xapp \\ instantiate \\ xsimpl
    \\ qexists_tac `STDOUT []` \\ xsimpl \\ qexists_tac `input` \\ xsimpl)
  \\ xlet `\y. CHAR_IO * STDIN "" * STDOUT [] *
               &(LIST_TYPE WORD (compile input) y)`
  THEN1 (xapp \\ instantiate \\ xsimpl)
  \\ xapp \\ instantiate \\ fs []
  \\ xsimpl \\ qexists_tac `STDIN ""` \\ qexists_tac `[]` \\ xsimpl);

(* prove final eval thm *)

val main_applied = let
  val e = ``Apps [Var (Short "main"); Lit (IntLit 0)] ``
          |> EVAL |> concl |> rand
  val th = get_ml_prog_state () |> get_thm
  val th = MATCH_MP ml_progTheory.ML_code_NONE_Dlet_var th
           handle HOL_ERR _ =>
           MATCH_MP ml_progTheory.ML_code_SOME_Dlet_var th
  val goal = th |> SPEC e |> SPEC_ALL |> concl |> dest_imp |> fst
  val th = goal |> NCONV 6 (SIMP_CONV (srw_ss())
                    [Once bigStepTheory.evaluate_cases,PULL_EXISTS])
  val p = find_term (can (match_term ``lookup_var_id _ _ = SOME _``)) (concl th)
  val th = th |> SIMP_RULE std_ss [EVAL p]
  val exists_lemma = METIS_PROVE []
    ``(?x1 x2 x3 x4 x5 x6. P x1 x2 x3 x4 x5 x6) <=>
      (?x3 x4 x5 x6 x1 x2. P x1 x2 x3 x4 x5 x6)``
  val st = goal |> rator |> rator |> rand
  val th =
    main_spec |> SPEC_ALL |> Q.INST_TYPE [`:'ffi`|->`:'a`]
     |> REWRITE_RULE [cfAppTheory.app_basic_def,cfAppTheory.app_def]
     |> Q.SPEC `st2heap (p:'a ffi_proj) ^st`
     |> Q.SPEC `{}`
     |> Q.SPEC `^st`
     |> SIMP_RULE std_ss [cfHeapsBaseTheory.SPLIT_emp2]
     |> Q.INST [`cv`|->`Litv (IntLit 0)`]
     |> SIMP_RULE std_ss [Once exists_lemma]
     |> SIMP_RULE std_ss [GSYM PULL_EXISTS,GSYM th]
  in th end

val raw_evaluate_prog = let
  val th = get_ml_prog_state () |> get_thm
  val th = MATCH_MP ml_progTheory.ML_code_NONE_Dlet_var th
  val th = th |> SPEC_ALL |> UNDISCH |> Q.SPEC `"_"` |> DISCH_ALL |> GEN_ALL
  val th = ConseqConv.WEAKEN_CONSEQ_CONV_RULE
             (ConseqConv.CONSEQ_REWRITE_CONV ([],[],[th])) main_applied
  val tm = th |> concl |> find_term (listSyntax.is_snoc)
  val entire_program_def = Define `entire_program = ^tm`
  val th = th |> SIMP_RULE std_ss [GSYM entire_program_def,PULL_EXISTS,
                   ml_progTheory.ML_code_def,ml_progTheory.Prog_def]
  in th end

(* next we instantiate the ffi and projection to remove the separation logic *)

val evaluate_prog = let
  val th = raw_evaluate_prog |> Q.GEN `ffi` |> ISPEC ``io_ffi input``
             |> Q.INST [`p`|->`(io_proj1,io_proj2)`]
             |> REWRITE_RULE [cfStoreTheory.st2heap_def]
             |> SIMP_RULE std_ss [Once cfStoreTheory.ffi2heap_def]
  val lemma1 = EVAL (find_term (can (match_term ``store2heap _``)) (concl th))
  val tm = find_term (can (match_term ``_.ffi``)) (concl th)
  val (x,y) = dest_comb (tm |> rand)
  val pat = mk_comb(rator tm,mk_comb(x,mk_var("ffi",type_of y)))
  val lemma2 = EVAL pat
  val th = th |> REWRITE_RULE [lemma1,lemma2]
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
   fs [cfStoreTheory.st2heap_def]
   \\ reverse IF_CASES_TAC THEN1
    (`F` by all_tac \\ fs [] \\ pop_assum mp_tac \\ fs []
     \\ fs [cfStoreTheory.parts_ok_def]
     \\ rw [] \\ TRY (EVAL_TAC \\ NO_TAC)
     \\ fs [io_proj2_def] \\ rw [] \\ fs [MEM] \\ rw []
     \\ fs [stdout_fun_def,stdin_fun_def,io_proj1_def,FUPDATE_LIST]
     \\ Cases_on `x` \\ fs [FAPPLY_FUPDATE_THM]
     \\ every_case_tac \\ fs [] \\ rw []
     \\ fs [io_ffi_def,io_ffi_oracle_def,FAPPLY_FUPDATE_THM]
     \\ fs [GSYM fmap_EQ,FUN_EQ_THM,FAPPLY_FUPDATE_THM]
     \\ rw [] \\ fs [])
   \\ fs [CHAR_IO_def,STDIN_def,STDOUT_def,cfHeapsBaseTheory.IO_def,
          set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
          EVAL ``write_loc``,cfHeapsBaseTheory.W8ARRAY_def,
          cfHeapsBaseTheory.cell_def]
   \\ rewrite_tac [GSYM set_sepTheory.STAR_ASSOC,set_sepTheory.cond_STAR]
   \\ fs [set_sepTheory.one_STAR]
   \\ simp [set_sepTheory.one_def]
   \\ rw [] \\ TRY (EVAL_TAC \\ NO_TAC)
   \\ fs [EXTENSION] \\ rpt strip_tac \\ EQ_TAC \\ rw [] \\ rw []
   \\ TRY (EVAL_TAC \\ NO_TAC)
   \\ fs [io_proj2_def] \\ rw [] \\ fs []
   \\ fs [io_proj1_def,io_ffi_def,FLOOKUP_DEF,FUPDATE_LIST,FAPPLY_FUPDATE_THM])
  val th = MP th lemma
  val lhs = th |> concl |> repeat (snd o dest_exists)
  val eval_tm = lhs |> helperLib.list_dest dest_conj |> last
  val rhs = ``^eval_tm /\
              st'.ffi.final_event = NONE /\
              st'.ffi.ffi_state = ([],compile input) /\
              extract_output st'.ffi.io_events = SOME (compile input)``
  val goal = mk_imp(lhs,rhs)
  val lemma = prove(goal,
    rw []
    \\ `(STDIN [] * STDOUT (compile input) * CHAR_IO) h'` by
           (fs [AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM] \\ NO_TAC)
    \\ fs [STDIN_def,STDOUT_def,cfHeapsBaseTheory.IO_def,
           GSYM set_sepTheory.STAR_ASSOC,set_sepTheory.one_STAR]
    \\ `FFI_part (Str []) stdin_fun [1; 2] IN
          (store2heap st'.refs ∪ ffi2heap (io_proj1,io_proj2) st'.ffi) /\
        FFI_part (Str (MAP (CHR o w2n) (compile input))) stdout_fun [0] IN
          (store2heap st'.refs ∪ ffi2heap (io_proj1,io_proj2) st'.ffi)` by
           cfHeapsBaseLib.SPLIT_TAC
    \\ fs [cfStoreTheory.FFI_part_NOT_IN_store2heap]
    \\ NTAC 2 (pop_assum mp_tac)
    \\ rfs [cfStoreTheory.ffi2heap_def]
    \\ IF_CASES_TAC \\ fs [io_proj1_def,FLOOKUP_DEF]
    \\ fs [cfStoreTheory.parts_ok_def]
    \\ Cases_on `st'.ffi.ffi_state` \\ fs [FAPPLY_FUPDATE_THM,FUPDATE_LIST]
    \\ rw [] \\ drule evaluate_prog_RTC_call_FFI_rel
    \\ strip_tac
    \\ `compile input = SND (st'.ffi.ffi_state)` by fs []
    \\ fs [MAP_CHR_w2n_11]
    \\ pop_assum (fn th => rewrite_tac[th])
    \\ match_mp_tac (RTC_call_FFI_rel_IMP_io_events |> MP_CANON |> SPEC_ALL
          |> Q.INST [`ys`|->`[]`]
          |> SIMP_RULE std_ss[APPEND] |> GEN_ALL)
    \\ asm_exists_tac \\ fs []
    \\ fs [EVAL ``(init_state (io_ffi input))``] \\ EVAL_TAC)
  val th = ConseqConv.WEAKEN_CONSEQ_CONV_RULE
             (ConseqConv.CONSEQ_REWRITE_CONV ([],[],[GEN_ALL lemma])) (DISCH T th)
           |> REWRITE_RULE []
  in th end

val evaluate_prog_rel_IMP_evaluate_prog_fun = prove(
  ``bigStep$evaluate_whole_prog F env st prog (st',new_tds,Rval r) ==>
    ?k. funBigStep$evaluate_prog (st with clock := k) env prog =
          (st',new_tds,Rval r)``,
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

val semantics_prog_entire_program = store_thm("semantics_prog_entire_program",
  ``?io_list.
      semantics_prog (init_state (io_ffi input)) init_env entire_program
        (Terminate Success io_list) /\
      extract_output io_list = SOME (compile input)``,
  fs[semanticsTheory.semantics_prog_def,PULL_EXISTS]
  \\ strip_assume_tac evaluate_prog
  \\ fs[semanticsTheory.evaluate_prog_with_clock_def]
  \\ qmatch_assum_abbrev_tac`evaluate_prog F init_env inp prog res`
  \\ `evaluate_whole_prog F init_env inp prog res`
  by (
    simp[bigStepTheory.evaluate_whole_prog_def,Abbr`res`]
    \\ simp[Abbr`inp`,Abbr`prog`]
    \\ EVAL_TAC )
  \\ unabbrev_all_tac
  \\ drule evaluate_prog_rel_IMP_evaluate_prog_fun
  \\ strip_tac \\ qexists_tac `k` \\ fs []);

val _ = export_theory();
