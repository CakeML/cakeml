open preamble basisProgTheory
     ml_monadBaseLib ml_monadStoreLib ml_monad_translatorLib
     TextIOProofTheory CommandLineProofTheory
     readerSharedTheory readerIOTheory

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

val EvalM_commandline_arguments = prove(
  ``Eval env exp (UNIT_TYPE x) /\
    (nsLookup env.v (Long "CommandLine" (Short "arguments")) =
       SOME CommandLine_arguments_v) ==>
    EvalM F env st (App Opapp [Var (Long "CommandLine" (Short "arguments")); exp])
      (MONAD (LIST_TYPE STRING_TYPE) HOL_EXN_TYPE (commandline (arguments x)))
      (STATE_STORE,p:'ffi ffi_proj)``,
  metis_tac [commandline_INTRO,EvalM_arguments]);
val _ = add_access_pattern EvalM_stdio_print;
val _ = add_access_pattern EvalM_stdio_print_err;
val _ = add_access_pattern EvalM_commandline_arguments
val _ = add_access_pattern EvalM_holrefs
val _ = ignore_type ``:IO_fs``;
val _ = ignore_type ``:hol_refs``

(* ------------------------------------------------------------------------- *)
(* Translate monad-IO reader                                                 *)
(* ------------------------------------------------------------------------- *)

m2deep ``holrefs (readLine_wrap (strlit"x") init_state)``

(* TODO need theorem for lifting readline_wrap *)
(*
val r = m_translate readLines_def
*)

val _ = export_theory ();
