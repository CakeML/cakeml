structure ioProgLib =
struct

local

open preamble;
open mlcharioProgTheory ioProgTheory ml_translatorLib ml_progLib;
open cfHeapsTheory cfTheory cfTacticsBaseLib cfTacticsLib;
open semanticsLib;

val state_accessors = fetch "semanticPrimitives" "state_accessors"

in

fun append_main_call compile_str compile_tm = let

(*
val compile_str  = "compile"
val compile_tm = ``compile``
*)

  val compile = compile_tm

  val main = parse_topdecs
    `fun main u = let
       val u = []
       val input = read_all u
       val bytes = ^compile_str input
     in write_list bytes end`

  val _ = ml_prog_update (ml_progLib.add_prog main pick_name);

  fun basis_st () = get_ml_prog_state ()

  val main_spec = Q.prove(
    `!cv input output.
        app (p:'ffi ffi_proj) ^(fetch_v "main" (basis_st()))
          [cv]
          (one FFI_split * STDIN input read_failed * STDOUT [] * frame)
          (POSTv uv. one FFI_split * STDIN "" T * STDOUT (^compile input) * frame)`,
    xcf "main" (basis_st())
    \\ xlet `POSTv v. one FFI_split * STDIN input read_failed * STDOUT [] * &(LIST_TYPE CHAR "" v) * frame`
    THEN1 (xcon \\ fs [] \\ xsimpl \\ EVAL_TAC)
    \\ xlet `POSTv x. one FFI_split * STDIN "" T * STDOUT [] * &(LIST_TYPE CHAR input x) * frame`
    THEN1
     (xapp \\ instantiate \\ xsimpl
      \\ qexists_tac `one FFI_split * STDOUT [] * frame`
      \\ xsimpl \\ qexists_tac`read_failed` \\ qexists_tac `input` \\ xsimpl)
    \\ xlet `POSTv y. one FFI_split * STDIN "" T * STDOUT [] *
                 &(LIST_TYPE WORD (^compile input) y) * frame`
    THEN1 (xapp \\ instantiate \\ xsimpl)
    \\ xapp \\ instantiate \\ fs []
    \\ xsimpl \\ qexists_tac `one FFI_split * STDIN "" T * frame`
    \\ qexists_tac `[]` \\ xsimpl);

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
       |> REWRITE_RULE [cfAppTheory.app_basic_rel,cfAppTheory.app_def]
       |> Q.SPEC `st2heap (p:'a ffi_proj) ^st`
       |> Q.SPEC `{}`
       |> Q.SPEC `^st`
       |> SIMP_RULE std_ss [PULL_EXISTS,
            cfHeapsBaseTheory.res_case_def,
            cfHeapsBaseTheory.POSTv_ignore,
            cfHeapsBaseTheory.SPLIT3_emp3,
            cfHeapsBaseTheory.SPLIT_emp2]
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

  val init_state_eq = EVAL ``(init_state (io_ffi input))``

  val evaluate_prog = let
    val th = raw_evaluate_prog |> Q.GEN `ffi` |> ISPEC ``io_ffi input``
               |> Q.GEN`read_failed` |> SPEC ``F``
               |> Q.INST [`p`|->`(io_proj1,io_proj2)`]
               |> REWRITE_RULE [cfStoreTheory.st2heap_def]
               |> SIMP_RULE std_ss [Once cfStoreTheory.ffi2heap_def]
    val lemma1 = EVAL (find_term (can (match_term ``store2heap _``)) (concl th))
    val tm = find_term (can (match_term ``_.ffi``)) (concl th)
    val (x,y) = dest_comb (tm |> rand)
    val pat = mk_comb(rator tm,mk_comb(x,mk_var("ffi",type_of y)))
    val lemma2 = EVAL pat
    val th = th |> REWRITE_RULE [lemma1,lemma2] |> Q.INST[`frame`|->`K T`]
    val goal = th |> concl |> dest_imp |> fst
    val lemma = prove(goal,
     fs [cfStoreTheory.st2heap_def,parts_ok_io_ffi]
     \\ fs [STDIN_def,STDOUT_def,cfHeapsBaseTheory.IO_def,
            set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
            EVAL ``read_state_loc``,
            EVAL ``write_state_loc``,
            cfHeapsBaseTheory.W8ARRAY_def,
            cfHeapsBaseTheory.cell_def]
     \\ rewrite_tac [GSYM set_sepTheory.STAR_ASSOC,set_sepTheory.cond_STAR]
     \\ fs [set_sepTheory.one_STAR,set_sepTheory.cond_STAR]
     \\ simp [set_sepTheory.one_def]
     \\ TRY(qexists_tac`0w`) \\ fs[cfStoreTheory.FFI_part_NOT_IN_store2heap_aux]
     \\ rw [] \\ TRY (EVAL_TAC \\ NO_TAC)
     \\ TRY (EVAL_TAC \\ qexists_tac`0w` \\ rw[] \\ NO_TAC)
     \\ fs [EXTENSION] \\ rpt strip_tac \\ EQ_TAC \\ rw [] \\ rw []
     \\ TRY (EVAL_TAC \\ NO_TAC)
     \\ fs [io_proj2_def] \\ rw [] \\ fs []
     \\ fs [io_proj1_def,io_ffi_def,FLOOKUP_DEF,FUPDATE_LIST,FAPPLY_FUPDATE_THM])
    val th = MP th lemma
    val lhs = th |> concl |> repeat (snd o dest_exists)
    val eval_tm = lhs |> helperLib.list_dest dest_conj |> last
    val rhs = ``^eval_tm /\
                st'.ffi.final_event = NONE /\
                st'.ffi.ffi_state = ([],^compile input) /\
                extract_output st'.ffi.io_events = SOME (^compile input)``
    val goal = mk_imp(lhs,rhs)
    val lemma = prove(goal,
      strip_tac
      \\ rename1 `(one FFI_split * STDIN _ _ * STDOUT _ * _) h_f`
      \\ `(STDIN [] T * one FFI_split * STDOUT (^compile input) * K T) h_f` by
             (fs [AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM] \\ NO_TAC)
      \\ fs[STDIN_def,STDOUT_def,cfHeapsBaseTheory.IO_def,
            set_sepTheory.SEP_EXISTS_THM,set_sepTheory.SEP_CLAUSES]
      \\ fs[GSYM set_sepTheory.STAR_ASSOC,set_sepTheory.one_STAR]
      \\ fs[Once set_sepTheory.STAR_COMM]
      \\ fs[GSYM set_sepTheory.STAR_ASSOC,set_sepTheory.one_STAR]
      \\ `FFI_part (Str []) stdin_fun ["getChar"] events'' IN
            (store2heap st'.refs ∪ ffi2heap (io_proj1,io_proj2) st'.ffi) /\
          FFI_part (Str (MAP (CHR o w2n) (^compile input))) stdout_fun ["putChar"] events''' IN
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
      \\ `^compile input = SND (st'.ffi.ffi_state)` by fs []
      \\ fs [MAP_CHR_w2n_11]
      \\ pop_assum (fn th => rewrite_tac[th])
      \\ match_mp_tac (RTC_call_FFI_rel_IMP_io_events |> MP_CANON |> SPEC_ALL
            |> Q.INST [`ys`|->`[]`]
            |> SIMP_RULE std_ss[APPEND] |> GEN_ALL)
      \\ asm_exists_tac \\ fs []
      \\ fs [init_state_eq] \\ EVAL_TAC
      \\ rw[])
    val th = ConseqConv.WEAKEN_CONSEQ_CONV_RULE
               (ConseqConv.CONSEQ_REWRITE_CONV ([],[],[GEN_ALL lemma])) (DISCH T th)
             |> REWRITE_RULE []
    in th end

  val semantics_prog_entire_program = Q.store_thm("semantics_prog_entire_program",
    `?io_list.
        semantics_prog (init_state (io_ffi input)) init_env entire_program
          (Terminate Success io_list) /\
        extract_output io_list = SOME (^compile input)`,
    fs[semanticsTheory.semantics_prog_def,PULL_EXISTS]
    \\ strip_assume_tac evaluate_prog
    \\ fs[semanticsTheory.evaluate_prog_with_clock_def]
    \\ qmatch_assum_abbrev_tac`evaluate_prog F init_env inp prog res`
    \\ `evaluate_whole_prog F init_env inp prog res`
    by (
      simp[bigStepTheory.evaluate_whole_prog_def,Abbr`res`]
      \\ simp[Abbr`inp`,Abbr`prog`,init_state_eq,state_accessors]
      \\ PURE_REWRITE_TAC [definition "entire_program_def",SNOC]
      \\ CONV_TAC(FORK_CONV(no_dup_mods_conv,no_dup_top_types_conv))
      \\ EVAL_TAC )
    \\ unabbrev_all_tac
    \\ drule evaluate_prog_rel_IMP_evaluate_prog_fun
    \\ strip_tac \\ qexists_tac `k` \\ fs []
    \\ rw[] \\ pairarg_tac \\ fs[]
    \\ pop_assum mp_tac
    \\ drule evaluatePropsTheory.evaluate_prog_clock_determ
    \\ ntac 2 strip_tac \\ first_x_assum drule
    \\ fs[] \\ rpt (CASE_TAC \\ fs[]));

  in semantics_prog_entire_program end;
end;
end
