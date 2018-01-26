open preamble basis
     ml_monadBaseLib ml_monadStoreLib
     TextIOProofTheory CommandLineProofTheory
     readerSharedTheory readerIOTheory
     ml_translatorTheory ml_monad_translatorTheory ml_monad_translatorBaseTheory
     bigStepTheory ml_monadBaseTheory
     ml_monad_translatorLib
     cfMonadLib
     readerIOProofTheory

val _ = new_theory "readerIOProg"
val _ = m_translation_extends "readerShared";

(* ------------------------------------------------------------------------- *)
(* Translate things in the same monad as the reader                          *)
(* ------------------------------------------------------------------------- *)

val r = m_translate readLine_wrap_def

(* ------------------------------------------------------------------------- *)
(* Set up translation to 'resume' from readerShared                          *)
(* ------------------------------------------------------------------------- *)

val refs_init_list = [] : (string * thm * thm * thm) list;
val rarrays_init_list = [] : (string * thm * thm * thm * thm * thm * thm * thm) list;
val farrays_init_list = [] : (string * (int * thm) * thm * thm * thm * thm * thm) list;
val store_hprop_name = "STATE_STORE";
val state_type = ``:state_refs``;
val type_theories = [] : string list;
val store_pinv_opt = NONE : (thm * thm) option;
val extra_hprop =
  SOME ``COMMANDLINE s.cl * MONAD_IO s.stdio * HOL_STORE s.holrefs``;
val exn_ri_def = ml_hol_kernelProgTheory.HOL_EXN_TYPE_def

val (monad_parameters, store_translation, exn_specs) =
    start_static_init_fixed_store_translation refs_init_list
                                              rarrays_init_list
                                              farrays_init_list
                                              store_hprop_name
                                              state_type
                                              exn_ri_def
                                              []
                                              type_theories
                                              store_pinv_opt
                                              extra_hprop;

(* ------------------------------------------------------------------------- *)
(* Prove some theorems about the monadic functions                           *)
(* ------------------------------------------------------------------------- *)

val IMP_STAR_GC = store_thm("IMP_STAR_GC", (* TODO: move *)
  ``(STAR a x) s /\ (y = GC) ==> (STAR a y) s``,
  fs [set_sepTheory.STAR_def]
  \\ rw[] \\ asm_exists_tac \\ fs []
  \\ EVAL_TAC
  \\ fs [set_sepTheory.SEP_EXISTS_THM]
  \\ qexists_tac `K T` \\ fs []);

(* TODO move *)
val stdio_INTRO = prove(
  ``(!st. EvalM ro env st exp
            (MONAD UNIT_TYPE exc_ty f)
            (MONAD_IO,p:'ffi ffi_proj)) ==>
    (!st. EvalM ro env st exp
            (MONAD UNIT_TYPE exc_ty (stdio f))
            (STATE_STORE,p:'ffi ffi_proj))``,
  fs [ml_monad_translatorTheory.EvalM_def] \\ rw []
  \\ first_x_assum (qspecl_then [`st.stdio`,`s`] mp_tac)
  \\ impl_tac
  THEN1 (fs [ml_monad_translatorBaseTheory.REFS_PRED_def]
         \\ fs [fetch "-" "STATE_STORE_def"]
         \\ qabbrev_tac `a = MONAD_IO st.stdio`
         \\ qabbrev_tac `b = GC`
         \\ fs [AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
         \\ last_x_assum mp_tac
         \\ metis_tac [IMP_STAR_GC])
  \\ disch_then (qspec_then `junk` strip_assume_tac)
  \\ asm_exists_tac \\ fs []
  \\ fs [ml_monad_translatorBaseTheory.REFS_PRED_FRAME_def,
        semanticPrimitivesTheory.state_component_equality]
  \\ rveq \\ fs [ml_monad_translatorTheory.MONAD_def]
  \\ Cases_on `f st.stdio` \\ fs []
  \\ every_case_tac
  \\ rveq \\ fs []
  \\ fs [fetch "-" "STATE_STORE_def"] \\ rw []
  \\ first_x_assum (qspec_then `F' * COMMANDLINE st.cl * HOL_STORE st.holrefs` mp_tac)
  \\ fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC]
  \\ fs [ml_monadBaseTheory.liftM_def] \\ rw []
  \\ fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC]);

(* TODO move *)
val commandline_INTRO = prove(
  ``(!st. EvalM ro env st exp
            (MONAD ret_ty exc_ty f)
            (COMMANDLINE,p:'ffi ffi_proj)) ==>
    (!st. EvalM ro env st exp
            (MONAD ret_ty exc_ty (commandline f))
            (STATE_STORE,p:'ffi ffi_proj))``,
  fs [ml_monad_translatorTheory.EvalM_def] \\ rw []
  \\ first_x_assum (qspecl_then [`st.cl`,`s`] mp_tac)
  \\ impl_tac
  THEN1 (fs [ml_monad_translatorBaseTheory.REFS_PRED_def]
         \\ fs [fetch "-" "STATE_STORE_def"]
         \\ qabbrev_tac `a = COMMANDLINE st.cl`
         \\ qabbrev_tac `b = GC`
         \\ fs [AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
         \\ last_x_assum mp_tac
         \\ metis_tac [IMP_STAR_GC])
  \\ disch_then (qspec_then `junk` strip_assume_tac)
  \\ asm_exists_tac \\ fs []
  \\ fs [ml_monad_translatorBaseTheory.REFS_PRED_FRAME_def,
        semanticPrimitivesTheory.state_component_equality]
  \\ rveq \\ fs [ml_monad_translatorTheory.MONAD_def]
  \\ Cases_on `f st.cl` \\ fs []
  \\ every_case_tac \\ rveq \\ fs []
  \\ fs [fetch "-" "STATE_STORE_def"] \\ rw []
  \\ first_x_assum (qspec_then `MONAD_IO st.stdio * HOL_STORE st.holrefs * F'` mp_tac)
  \\ fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC]
  \\ fs [ml_monadBaseTheory.liftM_def] \\ rw []);

val holrefs_INTRO = prove(
  ``(!st. EvalM ro env st exp
            (MONAD ret_ty exc_ty f)
            (HOL_STORE,p:'ffi ffi_proj)) ==>
    (!st. EvalM ro env st exp
            (MONAD ret_ty exc_ty (holrefs f))
            (STATE_STORE,p:'ffi ffi_proj))``,
  fs [ml_monad_translatorTheory.EvalM_def] \\ rw []
  \\ first_x_assum (qspecl_then [`st.holrefs`,`s`] mp_tac)
  \\ impl_tac
  THEN1 (fs [ml_monad_translatorBaseTheory.REFS_PRED_def]
         \\ fs [fetch "-" "STATE_STORE_def"]
         \\ qabbrev_tac `a = HOL_STORE st.holrefs`
         \\ qabbrev_tac `b = GC`
         \\ fs [AC set_sepTheory.STAR_ASSOC set_sepTheory.STAR_COMM]
         \\ last_x_assum mp_tac
         \\ metis_tac [IMP_STAR_GC])
  \\ disch_then (qspec_then `junk` strip_assume_tac)
  \\ asm_exists_tac \\ fs []
  \\ fs [ml_monad_translatorBaseTheory.REFS_PRED_FRAME_def,
        semanticPrimitivesTheory.state_component_equality]
  \\ rveq \\ fs [ml_monad_translatorTheory.MONAD_def]
  \\ Cases_on `f st.holrefs` \\ fs []
  \\ every_case_tac \\ rveq \\ fs []
  \\ fs [fetch "-" "STATE_STORE_def"] \\ rw []
  \\ first_x_assum (qspec_then `MONAD_IO st.stdio * COMMANDLINE st.cl * F'` mp_tac)
  \\ fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC]
  \\ fs [ml_monadBaseTheory.liftM_def] \\ rw []
  \\ fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC]);

val EvalM_stdio_print = prove(
  ``Eval env exp (STRING_TYPE x) /\
    (nsLookup env.v (Short "print") = SOME TextIO_print_v) ==>
    EvalM F env st (App Opapp [Var (Short "print"); exp])
      (MONAD UNIT_TYPE HOL_EXN_TYPE (stdio (print x)))
      (STATE_STORE,p:'ffi ffi_proj)``,
  metis_tac [stdio_INTRO,EvalM_print]);

val EvalM_stdio_print_err = prove(
  ``Eval env exp (STRING_TYPE x) /\
    (nsLookup env.v (Long "TextIO" (Short "print_err")) = SOME TextIO_print_err_v) ==>
    EvalM F env st (App Opapp [Var (Long "TextIO" (Short "print_err")); exp])
      (MONAD UNIT_TYPE HOL_EXN_TYPE (stdio (print_err x)))
      (STATE_STORE,p:'ffi ffi_proj)``,
  metis_tac [stdio_INTRO,EvalM_print_err]);

val EvalM_stdio_inputLinesFrom = prove(
  ``Eval env exp (STRING_TYPE f) /\
    ¬MEM #"\^@" (explode f) ∧ strlen f < 256 * 256 /\
    (nsLookup env.v (Long "TextIO" (Short "inputLinesFrom")) = SOME TextIO_inputLinesFrom_v) ==>
    EvalM F env st (App Opapp [Var (Long "TextIO" (Short "inputLinesFrom")); exp])
      (MONAD (OPTION_TYPE (LIST_TYPE STRING_TYPE)) HOL_EXN_TYPE (stdio (inputLinesFrom f)))
      (STATE_STORE,p:'ffi ffi_proj)``,
  cheat (* TODO *)
  (*
  strip_tac
  \\ assume_tac (GEN_ALL EvalM_inputLinesFrom)
  \\ mp_tac (INST_TYPE [``:'a``|->``:hol_exn``] (GEN_ALL stdio_INTRO))
  \\ disch_then (qspec_then `F` mp_tac)
  \\ first_x_assum drule
  \\ disch_then (qspec_then `p` mp_tac)
  \\ disch_then (qspec_then `inputLinesFrom f` mp_tac)
  \\ disch_then (qspec_then `F` mp_tac)
  metis_tac [stdio_INTRO,EvalM_inputLinesFrom]
  *)
  );

val EvalM_commandline_arguments = prove(
  ``Eval env exp (UNIT_TYPE x) /\
    (nsLookup env.v (Long "CommandLine" (Short "arguments")) =
       SOME CommandLine_arguments_v) ==>
    EvalM F env st (App Opapp [Var (Long "CommandLine" (Short "arguments")); exp])
      (MONAD (LIST_TYPE STRING_TYPE) HOL_EXN_TYPE (commandline (arguments x)))
      (STATE_STORE,p:'ffi ffi_proj)``,
  metis_tac [commandline_INTRO,EvalM_arguments]);

(* TODO *)

val EvalM_readline_wrap = Q.prove (
 `nsLookup env.v (Short "readline_wrap") = SOME readline_wrap_v /\
  Eval env lv (STRING_TYPE ln) /\
  Eval env rv (READER_STATE_TYPE rs)
  ==>
  EvalM ro env st
    (App Opapp [App Opapp [Var (Short "readline_wrap"); lv]; rv])
    (MONAD (SUM_TYPE STRING_TYPE READER_STATE_TYPE) HOL_EXN_TYPE
       (readLine_wrap ln rs)) (HOL_STORE, p:'ffi ffi_proj)`,
  rw [EvalM_def]
  \\ simp [MONAD_def]
  \\ rw [Once evaluate_cases, PULL_EXISTS]
  \\ ntac 10 (rw [Once (el 2 (CONJUNCTS evaluate_cases)), PULL_EXISTS])
  \\ fs [Eval_def]
  \\ first_x_assum (qspec_then `s.refs++junk` strip_assume_tac)
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ mp_tac ((Q.SPEC `s with refs := s.refs++junk` o
              CONV_RULE SWAP_FORALL_CONV o GEN_ALL)
             evaluate_empty_state_IMP) \\ fs []
  \\ disch_then drule \\ rw []
  \\ Cases_on `readLine_wrap ln rs st` \\ fs []
  \\ Cases_on `q` \\ fs []
  \\ CONV_TAC (RESORT_EXISTS_CONV rev)
  \\ qexists_tac `r` \\ fs []
  \\ qpat_x_assum `evaluate _ _ _ rv _` mp_tac
  \\ qpat_x_assum `evaluate _ _ _ rv _` kall_tac
  \\ strip_tac
  \\ first_x_assum (qspec_then `s.refs++junk++refs'` strip_assume_tac)
  \\ mp_tac ((Q.SPEC `s with refs := s.refs++junk++refs'` o
              CONV_RULE SWAP_FORALL_CONV o GEN_ALL)
             evaluate_empty_state_IMP) \\ fs []
  \\ disch_then drule \\ rw []
  \\ qpat_x_assum `evaluate _ _ _ lv _` mp_tac
  \\ qpat_x_assum `evaluate _ _ _ lv _` kall_tac \\ strip_tac
  \\ fs [PULL_EXISTS]
  \\ cheat);

val EvalM_set_reader_ctxt = Q.prove (
 `nsLookup env.v (Short "set_reader_ctxt") = SOME set_reader_ctxt_v /\
  Eval env uv (UNIT_TYPE u)
  ==>
  EvalM ro env st
    (App Opapp [Var (Short "set_reader_ctxt"); uv])
    (MONAD UNIT_TYPE HOL_EXN_TYPE
       (set_reader_ctxt u)) (HOL_STORE, p:'ffi ffi_proj)`,
  cheat (* TODO *)
  );

val EvalM_holrefs_readline_wrap = Q.prove (
 `nsLookup env.v (Short "readline_wrap") = SOME readline_wrap_v /\
  Eval env lv (STRING_TYPE ln) /\
  Eval env rv (READER_STATE_TYPE rs)
  ==>
  EvalM ro env st
    (App Opapp [App Opapp [Var (Short "readline_wrap"); lv]; rv])
    (MONAD (SUM_TYPE STRING_TYPE READER_STATE_TYPE) HOL_EXN_TYPE
       (holrefs (readLine_wrap ln rs))) (STATE_STORE, p:'ffi ffi_proj)`,
  rw []
  \\ drule (GEN_ALL EvalM_readline_wrap)
  \\ disch_then drule
  \\ disch_then (qspec_then `st.holrefs` drule)
  \\ disch_then (qspecl_then [`ro`,`p`] mp_tac)
  \\ rw [MONAD_def, EvalM_def]
  \\ first_x_assum (qspec_then `s` mp_tac)
  \\ impl_keep_tac
  >-
   (fs [REFS_PRED_def, fetch "-" "STATE_STORE_def"]
    \\ qpat_abbrev_tac `a = HOL_STORE st.holrefs`
    \\ qpat_abbrev_tac `b = GC`
    \\ fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC]
    \\ metis_tac [IMP_STAR_GC])
  \\ disch_then (qspec_then `junk` strip_assume_tac)
  \\ simp [liftM_def]
  \\ Cases_on `readLine_wrap ln rs st.holrefs` \\ fs []
  \\ reverse (Cases_on `q`) \\ fs []
  \\ every_case_tac \\ fs [] \\ rw []
  \\ asm_exists_tac \\ fs []
  \\ fs [REFS_PRED_FRAME_def] \\ rw []
  \\ fs [fetch "-" "STATE_STORE_def"]
  \\ first_x_assum
    (qspec_then `COMMANDLINE st.cl * MONAD_IO st.stdio * F'` assume_tac)
  \\ fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC]);

val EvalM_holrefs_set_reader_ctxt = Q.prove (
 `nsLookup env.v (Short "set_reader_ctxt") = SOME set_reader_ctxt_v /\
  Eval env uv (UNIT_TYPE u)
  ==>
  EvalM ro env st
    (App Opapp [Var (Short "set_reader_ctxt"); uv])
    (MONAD UNIT_TYPE HOL_EXN_TYPE
       (holrefs (set_reader_ctxt u))) (STATE_STORE, p:'ffi ffi_proj)`,
  rw []
  \\ drule (GEN_ALL EvalM_set_reader_ctxt)
  \\ disch_then drule
  \\ disch_then (qspec_then `st.holrefs` mp_tac)
  \\ disch_then (qspecl_then [`ro`,`p`] mp_tac)
  \\ rw [MONAD_def, EvalM_def]
  \\ first_x_assum (qspec_then `s` mp_tac)
  \\ impl_keep_tac
  >-
   (fs [REFS_PRED_def, fetch "-" "STATE_STORE_def"]
    \\ qpat_abbrev_tac `a = HOL_STORE st.holrefs`
    \\ qpat_abbrev_tac `b = GC`
    \\ fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC]
    \\ metis_tac [IMP_STAR_GC])
  \\ disch_then (qspec_then `junk` strip_assume_tac)
  \\ simp [liftM_def]
  \\ Cases_on `set_reader_ctxt () st.holrefs`
  \\ reverse (Cases_on `q`) \\ fs []
  \\ every_case_tac \\ fs [] \\ rw []
  \\ asm_exists_tac \\ fs []
  \\ fs [REFS_PRED_FRAME_def] \\ rw []
  \\ fs [fetch "-" "STATE_STORE_def"]
  \\ first_x_assum
    (qspec_then `COMMANDLINE st.cl * MONAD_IO st.stdio * F'` assume_tac)
  \\ fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC]);

val _ = add_access_pattern EvalM_stdio_print;
val _ = add_access_pattern EvalM_stdio_print_err;
val _ = add_access_pattern EvalM_commandline_arguments;
val _ = add_access_pattern EvalM_holrefs_readline_wrap;
val _ = add_access_pattern EvalM_holrefs_set_reader_ctxt;
val _ = add_access_pattern EvalM_stdio_inputLinesFrom;

val _ = ignore_type ``:IO_fs``;
val _ = ignore_type ``:hol_refs``

(* ------------------------------------------------------------------------- *)
(* Translate monad-IO reader                                                 *)
(* ------------------------------------------------------------------------- *)

val r = m_translate readLines_def
val r = m_translate readFile_def
val r = m_translate readMain_def

val EVERY_TL = Q.store_thm("EVERY_TL",
  `!xs. EVERY P xs /\ xs <> [] ==> EVERY P (TL xs)`,
  Induct \\ rw []);

val readMain_side = Q.prove (
  `wfcl st.cl ==> readmain_side st v`, (* wfcl on st.cl *)
  rw [fetch "-" "readmain_side_def", fetch "-" "readfile_side_def", wfcl_def,
      arguments_def, liftM_def]
  \\ imp_res_tac EVERY_TL \\ rfs [clFFITheory.validArg_def])
  |> update_precondition;

val readMain_spec = save_thm ("readMain_spec",
  cfMonadLib.mk_app_of_ArrowP (theorem "readmain_v_thm"));

val readMain_spec_wp = Q.store_thm("readMain_spec_wp",
  `wfcl st.cl ==>
   app (p:'ffi ffi_proj) readmain_v [Conv NONE []]
     (STATE_STORE st)
     (POSTv uv.
       &UNIT_TYPE () uv *
       STDIO (reader_main st.stdio st.holrefs (TL st.cl)) *
       COMMANDLINE st.cl)`, cheat)

(* ------------------------------------------------------------------------- *)
(* Custom whole_prog_spec                                                    *)
(* ------------------------------------------------------------------------- *)

open alt_basisLib alt_basisTheory (* basis does not do what I want here *)

val monadreader_wps = Q.store_thm("monadreader_wps",
  `hasFreeFD st.stdio /\ wfcl st.cl /\
   st.holrefs = init_refs
   ==>
   whole_prog_spec_extra ^(fetch_v "readmain" (get_ml_prog_state()))
     st.cl st.stdio STATE_STORE st
     ((=) (reader_main st.stdio st.holrefs (TL st.cl)))`,
  rw [whole_prog_spec_extra_def]
  \\ qmatch_goalsub_abbrev_tac `fs1 = _ with numchars := _`
  \\ qexists_tac `fs1` \\ fs [Abbr`fs1`]
  \\ reverse conj_tac
  >-
   (fs [readerProofTheory.reader_main_def,
        readerProofTheory.read_file_def]
    \\ every_case_tac
    \\ fs [GSYM add_stdo_with_numchars, with_same_numchars])
  \\ match_mp_tac (GEN_ALL (MP_CANON (MATCH_MP app_wgframe (UNDISCH readMain_spec_wp))))
  \\ xsimpl);

(* TODO: need one of these *)
(* val _ = set_user_heap_thm STATE_STORE_init_precond; *)

(* ------------------------------------------------------------------------- *)

val st = get_ml_prog_state ();
val name = "readmain";
val spec = UNDISCH monadreader_wps;
(* TODO need the set_user_heap_thm first for whole_prog_thm *)
val prog_tm = whole_prog_term st name spec
val readerIO_prog_def = Define `readerIO_prog = ^prog_tm`

val _ = export_theory ();

