(*
  Applying the monadic translator to OpenTheory article reader
  expressed using a basis-compatible IO monad.
*)
open preamble basis
     ml_monadBaseLib ml_monadStoreLib
     TextIOProofTheory CommandLineProofTheory
     reader_commonProgTheory readerIOTheory reader_initTheory
     ml_translatorTheory ml_monad_translatorTheory ml_monad_translatorBaseTheory
     ml_monadBaseTheory
     ml_monad_translatorLib
     cfMonadLib
     readerIOProofTheory reader_initTheory

val _ = new_theory "readerIOProg"
val _ = m_translation_extends "reader_commonProg"

(* ------------------------------------------------------------------------- *)
(* Translate things in the same monad as the reader                          *)
(* ------------------------------------------------------------------------- *)

val r = m_translate readLine_wrap_def
val r = m_translate init_reader_wrap_def

val init_reader_wrap_spec = save_thm ("init_reader_wrap_spec",
  mk_app_of_ArrowP (theorem "init_reader_wrap_v_thm"));

val readline_wrap_spec = save_thm ("readline_wrap_spec",
  mk_app_of_ArrowP (theorem "readline_wrap_v_thm"));

(* ------------------------------------------------------------------------- *)
(* Set up translation to 'resume' from reader_commonProg                     *)
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
            (MONAD ret_ty exc_ty f)
            (MONAD_IO,p:'ffi ffi_proj)) ==>
    (!st. EvalM ro env st exp
            (MONAD ret_ty exc_ty (stdio f))
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
  \\ rw [] \\ asm_exists_tac \\ fs []
  \\ fs [ml_monad_translatorBaseTheory.REFS_PRED_FRAME_def,
        semanticPrimitivesTheory.state_component_equality]
  \\ rveq \\ fs [ml_monad_translatorTheory.MONAD_def]
  \\ fs [liftM_def, UNCURRY]
  \\ Cases_on `f st.stdio` \\ fs []
  \\ every_case_tac \\ rveq \\ fs []
  \\ fs [fetch "-" "STATE_STORE_def"] \\ rw []
  \\ first_x_assum (qspec_then `F' * COMMANDLINE st.cl * HOL_STORE st.holrefs` mp_tac)
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
  \\ rw [] \\ asm_exists_tac \\ fs []
  \\ fs [ml_monad_translatorBaseTheory.REFS_PRED_FRAME_def,
        semanticPrimitivesTheory.state_component_equality]
  \\ rveq \\ fs [ml_monad_translatorTheory.MONAD_def]
  \\ fs [liftM_def, UNCURRY]
  \\ Cases_on `f st.cl` \\ fs []
  \\ every_case_tac \\ rveq \\ fs []
  \\ fs [fetch "-" "STATE_STORE_def"] \\ rw []
  \\ first_x_assum (qspec_then `MONAD_IO st.stdio * HOL_STORE st.holrefs * F'` mp_tac)
  \\ fs [AC set_sepTheory.STAR_COMM set_sepTheory.STAR_ASSOC]);

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
  \\ rw [] \\ asm_exists_tac \\ fs []
  \\ fs [ml_monad_translatorBaseTheory.REFS_PRED_FRAME_def,
        semanticPrimitivesTheory.state_component_equality]
  \\ rveq \\ fs [ml_monad_translatorTheory.MONAD_def]
  \\ fs [liftM_def, UNCURRY]
  \\ Cases_on `f st.holrefs` \\ fs []
  \\ every_case_tac \\ rveq \\ fs []
  \\ fs [fetch "-" "STATE_STORE_def"] \\ rw []
  \\ first_x_assum (qspec_then `MONAD_IO st.stdio * COMMANDLINE st.cl * F'` mp_tac)
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
  ``Eval env exp (FILENAME f) /\
    (nsLookup env.v (Long "TextIO" (Short "inputLinesFrom")) = SOME TextIO_inputLinesFrom_v) ==>
    EvalM F env st (App Opapp [Var (Long "TextIO" (Short "inputLinesFrom")); exp])
      (MONAD (OPTION_TYPE (LIST_TYPE STRING_TYPE)) HOL_EXN_TYPE (stdio (inputLinesFrom f)))
      (STATE_STORE,p:'ffi ffi_proj)``,
  metis_tac [stdio_INTRO, EvalM_inputLinesFrom]);

(* Translator coughs up STRING_TYPE twice unless we remove FILENAME *)
val EvalM_stdio_inputLinesFrom_STRING = prove(
  ``Eval env exp (STRING_TYPE f) /\
    ~MEM #"\^@" (explode f) /\ strlen f < 256 * 256 /\
    (nsLookup env.v (Long "TextIO" (Short "inputLinesFrom")) = SOME TextIO_inputLinesFrom_v) ==>
    EvalM F env st (App Opapp [Var (Long "TextIO" (Short "inputLinesFrom")); exp])
      (MONAD (OPTION_TYPE (LIST_TYPE STRING_TYPE)) HOL_EXN_TYPE (stdio (inputLinesFrom f)))
      (STATE_STORE,p:'ffi ffi_proj)``,
  rw [] \\ assume_tac (GEN_ALL EvalM_stdio_inputLinesFrom)
  \\ fs [Eval_def, FILENAME_def]);

val EvalM_commandline_arguments = prove(
  ``Eval env exp (UNIT_TYPE x) /\
    (nsLookup env.v (Long "CommandLine" (Short "arguments")) =
       SOME CommandLine_arguments_v) ==>
    EvalM F env st (App Opapp [Var (Long "CommandLine" (Short "arguments")); exp])
      (MONAD (LIST_TYPE STRING_TYPE) HOL_EXN_TYPE (commandline (arguments x)))
      (STATE_STORE,p:'ffi ffi_proj)``,
  metis_tac [commandline_INTRO,EvalM_arguments]);

Theorem EvalM_init_reader_wrap:
   Eval env exp (UNIT_TYPE u) /\
    (nsLookup env.v (Short "init_reader_wrap") = SOME init_reader_wrap_v) ==>
    EvalM F env st (App Opapp [Var (Short "init_reader_wrap"); exp])
      (MONAD (SUM_TYPE STRING_TYPE UNIT_TYPE) exc_ty (init_reader_wrap u))
      (HOL_STORE,p:'ffi ffi_proj)
Proof
  ho_match_mp_tac EvalM_from_app \\ rw []
  >-
   (fs [init_reader_wrap_def, st_ex_bind_def, holKernelTheory.handle_Fail_def,
        st_ex_return_def]
    \\ every_case_tac \\ fs [] \\ rw [])
  \\ xapp_spec init_reader_wrap_spec
  \\ xsimpl
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `s` \\ xsimpl
QED

Theorem EvalM_holrefs_init_reader_wrap:
   Eval env exp (UNIT_TYPE u) /\
   nsLookup env.v (Short "init_reader_wrap") = SOME init_reader_wrap_v
   ==>
   EvalM F env st
     (App Opapp [Var (Short "init_reader_wrap"); exp])
     (MONAD (SUM_TYPE STRING_TYPE UNIT_TYPE) HOL_EXN_TYPE
       (holrefs (init_reader_wrap u))) (STATE_STORE, p:'ffi ffi_proj)
Proof
  metis_tac [holrefs_INTRO, EvalM_init_reader_wrap]
QED

val EvalM_readline_wrap = Q.prove (
 `Eval env xv (PAIR_TYPE STRING_TYPE READER_STATE_TYPE x) /\
  nsLookup env.v (Short "readline_wrap") = SOME readline_wrap_v
  ==>
  EvalM F env st
    (App Opapp [Var (Short "readline_wrap"); xv])
    (MONAD (SUM_TYPE STRING_TYPE READER_STATE_TYPE) HOL_EXN_TYPE
       (readLine_wrap x)) (HOL_STORE, p:'ffi ffi_proj)`,
  ho_match_mp_tac EvalM_from_app \\ rw []
  >-
   (PairCases_on `x`
    \\ fs [readLine_wrap_def, holKernelTheory.handle_Fail_def,
           st_ex_bind_def, st_ex_return_def]
    \\ every_case_tac \\ fs [] \\ rw [])
  \\ xapp_spec readline_wrap_spec
  \\ xsimpl
  \\ asm_exists_tac \\ fs []
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `s`
  \\ xsimpl);

val EvalM_holrefs_readline_wrap = Q.prove (
 `Eval env xv (PAIR_TYPE STRING_TYPE READER_STATE_TYPE x) /\
  nsLookup env.v (Short "readline_wrap") = SOME readline_wrap_v
  ==>
  EvalM F env st
    (App Opapp [Var (Short "readline_wrap"); xv])
    (MONAD (SUM_TYPE STRING_TYPE READER_STATE_TYPE) HOL_EXN_TYPE
       (holrefs (readLine_wrap x))) (STATE_STORE, p:'ffi ffi_proj)`,
  metis_tac [holrefs_INTRO, EvalM_readline_wrap]);

Theorem EvalM_context:
   Eval env uv (UNIT_TYPE u) /\
   nsLookup env.v (Long "Kernel" (Short "context")) = SOME context_v
   ==>
   EvalM F env st (App Opapp [Var (Long "Kernel" (Short "context")); uv])
     (MONAD (LIST_TYPE UPDATE_TYPE) HOL_EXN_TYPE (context u))
     (HOL_STORE, p:'ffi ffi_proj)
Proof
  ho_match_mp_tac EvalM_from_app
  \\ rw []
  >- (EVAL_TAC \\ fs [])
  \\ xapp_spec context_spec
  \\ xsimpl
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `s`
  \\ xsimpl
QED

Theorem EvalM_holrefs_context:
   Eval env uv (UNIT_TYPE u) /\
   nsLookup env.v (Long "Kernel" (Short "context")) = SOME context_v
   ==>
   EvalM F env st (App Opapp [Var (Long "Kernel" (Short "context")); uv])
     (MONAD (LIST_TYPE UPDATE_TYPE) HOL_EXN_TYPE (holrefs (context u)))
     (STATE_STORE, p:'ffi ffi_proj)
Proof
  metis_tac [holrefs_INTRO, EvalM_context]
QED

(* ------------------------------------------------------------------------- *)
(* Add access patterns                                                       *)
(* ------------------------------------------------------------------------- *)

val _ = add_access_pattern EvalM_stdio_print;
val _ = add_access_pattern EvalM_stdio_print_err;
val _ = add_access_pattern EvalM_commandline_arguments;
val _ = add_access_pattern EvalM_holrefs_readline_wrap;
val _ = add_access_pattern EvalM_holrefs_init_reader_wrap;
val _ = add_access_pattern EvalM_stdio_inputLinesFrom_STRING;
val _ = add_access_pattern EvalM_holrefs_context;

val _ = ignore_type ``:IO_fs``;
val _ = ignore_type ``:hol_refs``

(* ------------------------------------------------------------------------- *)
(* Translate monad-IO reader                                                 *)
(* ------------------------------------------------------------------------- *)

val r = m_translate ffi_msg_def
val r = m_translate readLines_def
val r = m_translate readFile_def
val r = m_translate readMain_def

Theorem EVERY_TL:
   !xs. EVERY P xs /\ xs <> [] ==> EVERY P (TL xs)
Proof
  Induct \\ rw []
QED

val readMain_side = Q.prove (
  `wfcl st.cl ==> readmain_side st v`, (* wfcl on st.cl *)
  rw [fetch "-" "readmain_side_def", fetch "-" "readfile_side_def", wfcl_def,
      arguments_def, liftM_def]
  \\ imp_res_tac EVERY_TL \\ rfs [clFFITheory.validArg_def])
  |> update_precondition;

val readMain_spec = save_thm ("readMain_spec",
  cfMonadLib.mk_app_of_ArrowP (theorem "readmain_v_thm"));

Theorem readMain_spec_wp:
   wfcl st.cl /\
   st.holrefs = init_refs ==>
   app (p:'ffi ffi_proj) readmain_v [Conv NONE []]
     (HOL_STORE st.holrefs * COMMANDLINE st.cl * MONAD_IO st.stdio)
     (POSTv uv.
       &UNIT_TYPE () uv *
       STDIO (FST (SND (reader_main st.stdio st.holrefs (TL st.cl)))))
Proof
  rw [] \\ xapp \\ xsimpl
  \\ simp [definition"STATE_STORE_def"]
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `st` \\ xsimpl
  \\ conj_tac
  >- (imp_res_tac readMain_side \\ fs [])
  \\ reverse conj_tac
  >-
   (rw []
    \\ Q.SPECL_THEN [`Failure x'`,`x`,`st`] assume_tac (GEN_ALL readMain_thm)
    \\ `st with holrefs := init_refs = st`
      by fs [state_refs_component_equality]
    \\ fs [])
  \\ rw [MONAD_IO_def]
  \\ xsimpl \\ rw []
  \\ Cases_on `reader_main st.stdio st.holrefs (TL st.cl)`
  \\ PairCases_on `r`
  \\ imp_res_tac readMain_correct \\ fs []
  \\ qpat_x_assum `_ = init_refs` (assume_tac o GSYM) \\ fs []
  \\ xsimpl
QED

(* ------------------------------------------------------------------------- *)
(* whole_prog_spec                                                           *)
(* ------------------------------------------------------------------------- *)

Theorem monadreader_wps:
   hasFreeFD fs /\
   wfcl cl
   ==>
   whole_prog_spec ^(fetch_v "readmain" (get_ml_prog_state()))
     cl fs (SOME (HOL_STORE init_refs))
     ((=) (FST (SND (reader_main fs init_refs (TL cl)))))
Proof
  rw [whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac `fs1 = _ with numchars := _`
  \\ qexists_tac `fs1` \\ fs [Abbr`fs1`]
  \\ reverse conj_tac
  >-
   (fs [readerProofTheory.reader_main_def,
        readerProofTheory.read_file_def]
    \\ every_case_tac
    \\ fs [GSYM add_stdo_with_numchars, with_same_numchars])
  \\ irule
    (DISCH_ALL
      (GEN_ALL (MP_CANON (MATCH_MP app_wgframe (UNDISCH readMain_spec_wp)))))
  \\ xsimpl
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `<| stdio := fs; cl := cl; holrefs := init_refs |>`
  \\ fs [MONAD_IO_def]
  \\ xsimpl
QED

val _ = add_user_heap_thm HOL_STORE_init_precond;

val st = get_ml_prog_state ();
val name = "readmain";
val spec = (UNDISCH monadreader_wps);
val (sem_thm,prog_tm) = whole_prog_thm st name spec
val readerIO_prog_def = Define `readerIO_prog = ^prog_tm`

val semantics_readerIO_prog =
  sem_thm
  |> REWRITE_RULE[GSYM readerIO_prog_def]
  |> DISCH_ALL
  |> ONCE_REWRITE_RULE [AND_IMP_INTRO]
  |> ONCE_REWRITE_RULE (* hasFreeFD gets simplified away in wps and its ugly *)
    [EVAL ``hasFreeFD fs``
     |> CONV_RULE (RHS_CONV (SIMP_CONV std_ss []))
     |> ONCE_REWRITE_RULE [CONJ_COMM] |> GSYM]
  |> REWRITE_RULE [AND_IMP_INTRO, GSYM CONJ_ASSOC]
  |> curry save_thm "semantics_readerIO_prog";

val _ = export_theory ();
