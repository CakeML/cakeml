(*
  Deeply embedded CakeML program that implements an OpenTheory article
  checker.
*)
Theory readerProg
Ancestors
  ml_monadBase cfMonad holKernel holKernelProof ml_hol_kernelProg
  ml_hol_kernel_funsProg reader readerProof pretty
  reader_commonProg reader_init basis_ffi
Libs
  preamble basis ml_monad_translatorLib cfMonadLib

val _ = m_translation_extends "reader_commonProg"

(* -------------------------------------------------------------------------
 * Translation
 * ------------------------------------------------------------------------- *)

val r = translate is_newline_def;

Quote add_cakeml:
  fun read_from inp =
    case TextIO.inputAllTokensFrom #"\n" inp is_newline tokenize of
      None =>
        (* Can only happen if the input is a file *)
        TextIO.output TextIO.stdErr (msg_bad_name (Option.valOf inp))
    | Some ls =>
        let
          val st = fst (readlines init_state (List.concat ls))
        in
          print_app_list (msg_success st (Kernel.context ()))
        end
        handle Failure e => TextIO.output TextIO.stdErr e;
End

Quote add_cakeml:
  fun reader_main u =
    let
      val _ = init_reader ()
    in
      case CommandLine.arguments () of
        [] => read_from None
      | [file] => read_from (Some file)
      | _ => TextIO.output TextIO.stdErr msg_usage
      end
End

(* -------------------------------------------------------------------------
 * Proofs
 * ------------------------------------------------------------------------- *)


Theorem POSTve_POSTv[local]:
  ∀Q. POSTve Q (λx. SEP_F) = $POSTv Q
Proof
  rw [SEP_CLAUSES, POSTv_def, POSTve_def]
QED

Theorem context_spec =
  context_spec
  |> Q.SPEC ‘()’
  |> SIMP_RULE (srw_ss())
    [context_def, get_the_context_def, SEP_CLAUSES, POSTve_POSTv];

Theorem inputAllTokensFrom_SOME_specialized:
  OPTION_TYPE FILENAME (SOME fn) fnv ∧ hasFreeFD fs
  ⇒
  app (p: 'ffi ffi_proj) TextIO_inputAllTokensFrom_v
    [Litv (Char #"\n") ; fnv; is_newline_v; tokenize_v]
    (STDIO fs)
    (POSTv sv.
      &OPTION_TYPE (LIST_TYPE (LIST_TYPE READER_COMMAND_TYPE))
        (if inFS_fname fs fn then
          SOME (MAP (MAP tokenize ∘ tokens is_newline)
                    (all_lines_file fs fn))
         else
           NONE) sv *
      STDIO fs)
Proof
  strip_tac
  \\ rewrite_tac [GSYM all_lines_file_gen_all_lines_file]
  \\ irule inputAllTokensFrom_SOME
  \\ simp [theorem "is_newline_v_thm", tokenize_v_thm, is_newline_def]
QED

Theorem read_from_SOME:
  OPTION_TYPE FILENAME (SOME fn) fnv ∧ hasFreeFD fs ∧ inFS_fname fs fn
  ⇒
  app (p: 'ffi ffi_proj) read_from_v [fnv]
    (STDIO fs * HOL_STORE refs)
    (POSTv u.
      &UNIT_TYPE () u *
      STDIO (FST (read_from fs refs (SOME fn))) *
      HOL_STORE (FST (SND (read_from fs refs (SOME fn)))))
Proof
  rpt strip_tac
  \\ xcf_with_def (fetch "-" "read_from_v_def")
  \\ assume_tac init_state_v_thm
  \\ xlet ‘POSTv sv.
             &OPTION_TYPE (LIST_TYPE (LIST_TYPE READER_COMMAND_TYPE))
               (SOME (MAP (MAP tokenize ∘ tokens is_newline)
                   (all_lines_file fs fn))) sv *
             STDIO fs * HOL_STORE refs’
  >-
   (xapp_spec inputAllTokensFrom_SOME_specialized
    \\ qexistsl [‘HOL_STORE refs’, ‘fs’, ‘fn’] \\ simp [] \\ xsimpl)
  \\ fs [OPTION_TYPE_def]
  \\ xmatch
  \\ simp [read_from_def]
  \\ CASE_TAC \\ fs [all_lines_from_def]
  \\ CASE_TAC \\ CASE_TAC \\ fs []
 >-
   (qmatch_goalsub_abbrev_tac ‘$POSTv Q’
    \\ xhandle ‘$POSTv Q’ \\ xsimpl
    \\ qunabbrev_tac ‘Q’
    \\ xlet_auto >- xsimpl
    \\ xlet_auto \\ xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xcon \\ xsimpl)
    \\ rveq \\ fs []
    \\ rename1 ‘(M_success _, refs1)’
    \\ drule_then (qspecl_then [‘p’, ‘refs1’] strip_assume_tac) context_spec
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ rveq \\ fs []
    \\ xapp
    \\ instantiate
    \\ qexistsl [‘HOL_STORE refs'’, ‘fs’]
    \\ xsimpl)
  \\ xhandle ‘POSTe ev.
                &HOL_EXN_TYPE (Failure m) ev *
                HOL_STORE r *
                STDIO fs’
  >- (xlet_auto \\ xsimpl \\ xlet_auto \\ xsimpl)
  \\ fs [HOL_EXN_TYPE_def]
  \\ xcases
  \\ xapp_spec output_stderr_spec
  \\ instantiate
  \\ qexistsl [‘HOL_STORE r’, ‘fs’]
  \\ xsimpl
QED

Theorem read_from_SOME_fail:
  OPTION_TYPE FILENAME (SOME fn) fnv ∧ hasFreeFD fs ∧ ¬inFS_fname fs fn
  ⇒
  app (p: 'ffi ffi_proj) read_from_v [fnv]
    (STDIO fs * HOL_STORE refs)
    (POSTv u.
      &UNIT_TYPE () u *
      STDIO (FST (add_stderr fs (msg_bad_name fn), refs, NONE)))
Proof
  rpt strip_tac
  \\ xcf_with_def (fetch "-" "read_from_v_def")
  \\ assume_tac init_state_v_thm
  \\ xlet ‘POSTv sv.
             &OPTION_TYPE (LIST_TYPE (LIST_TYPE READER_COMMAND_TYPE))
               NONE sv * STDIO fs * HOL_STORE refs’
  >-
   (xapp_spec inputAllTokensFrom_SOME_specialized
    \\ qexistsl [‘HOL_STORE refs’, ‘fs’, ‘fn’] \\ simp [] \\ xsimpl)
  \\ pop_assum $ assume_tac o SRULE [OPTION_TYPE_def]
  \\ xmatch
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ xapp_spec output_stderr_spec
  \\ instantiate
  \\ qexistsl [‘HOL_STORE refs’, ‘fs’]
  \\ xsimpl
QED

Theorem inputAllTokensFrom_NONE_specialized:
  OPTION_TYPE FILENAME NONE fnv ∧ stdin_content fs = SOME text
  ⇒
  app (p: 'ffi ffi_proj) TextIO_inputAllTokensFrom_v
    [Litv (Char #"\n") ; fnv; is_newline_v; tokenize_v]
    (STDIO fs)
    (POSTv sv.
       STDIO (fastForwardFD fs 0) *
       &OPTION_TYPE (LIST_TYPE (LIST_TYPE READER_COMMAND_TYPE))
          (SOME (MAP (MAP tokenize ∘ tokens is_newline)
                     (lines_of (implode text)))) sv)
Proof
  strip_tac
  \\ rewrite_tac [GSYM lines_of_gen_lines_of]
  \\ irule inputAllTokensFrom_NONE
  \\ simp [theorem "is_newline_v_thm", tokenize_v_thm, is_newline_def]
QED

(* TODO Move? *)
Theorem all_lines_stdin_lines_of:
  stdin_content fs = SOME text ⇒ all_lines_stdin fs = lines_of (implode text)
Proof
  simp [stdin_content_def, all_lines_stdin_def, lines_of_def]
QED

Theorem read_from_NONE:
  OPTION_TYPE FILENAME NONE fnv ∧ stdin_content fs = SOME text
  ⇒
  app (p: 'ffi ffi_proj) read_from_v [fnv]
    (STDIO fs * HOL_STORE refs)
    (POSTv u.
      &UNIT_TYPE () u *
      STDIO (FST (read_from fs refs NONE)) *
      HOL_STORE (FST (SND (read_from fs refs NONE))))
Proof
  rpt strip_tac
  \\ xcf_with_def (fetch "-" "read_from_v_def")
  \\ assume_tac init_state_v_thm
  (* For using add_stdout_fastForwardFD *)
  \\ reverse (Cases_on ‘STD_streams fs’) >- (fs [STDIO_def] \\ xpull)
  \\ xlet ‘POSTv sv.
             &OPTION_TYPE (LIST_TYPE (LIST_TYPE READER_COMMAND_TYPE))
              (SOME (MAP (MAP tokenize ∘ tokens is_newline)
                         (lines_of (implode text)))) sv *
             STDIO (fastForwardFD fs 0) * HOL_STORE refs’
  >-
   (xapp_spec inputAllTokensFrom_NONE_specialized
    \\ first_assum $ irule_at (Pos hd) \\ simp []
    \\ qexists ‘HOL_STORE refs’ \\ xsimpl)
  \\ fs [OPTION_TYPE_def]
  \\ xmatch
  \\ IF_CASES_TAC >- (pop_assum mp_tac \\ EVAL_TAC)
  \\ reverse conj_tac >- (EVAL_TAC \\ fs [])
  \\ simp [read_from_def]
  \\ CASE_TAC \\ fs [all_lines_from_def]
  \\ drule_all_then assume_tac all_lines_stdin_lines_of \\ fs []
  \\ CASE_TAC \\ CASE_TAC \\ fs []
 >-
   (qmatch_goalsub_abbrev_tac ‘$POSTv Q’
    \\ xhandle ‘$POSTv Q’ \\ xsimpl
    \\ qunabbrev_tac ‘Q’
    \\ xlet_auto >- xsimpl
    \\ xlet_auto \\ xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xcon \\ xsimpl)
    \\ rveq \\ fs []
    \\ rename1 ‘(M_success _, refs1)’
    \\ drule_then (qspecl_then [‘p’, ‘refs1’] strip_assume_tac) context_spec
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ rveq \\ fs []
    \\ xapp
    \\ instantiate
    \\ qexistsl [‘HOL_STORE refs'’, ‘fastForwardFD fs 0’]
    \\ simp [add_stdout_fastForwardFD]
    \\ xsimpl)
  \\ xhandle ‘POSTe ev.
                &HOL_EXN_TYPE (Failure m) ev *
                HOL_STORE r *
                STDIO (fastForwardFD fs 0)’
  >- (xlet_auto \\ xsimpl \\ xlet_auto \\ xsimpl)
  \\ fs [HOL_EXN_TYPE_def]
  \\ xcases
  \\ xapp_spec output_stderr_spec
  \\ instantiate
  \\ qexistsl [‘HOL_STORE r’, ‘fastForwardFD fs 0’]
  \\ simp [add_stderr_fastForwardFD]
  \\ xsimpl
QED

Theorem init_reader_spec:
  ∀uv state.
    (∃s. init_reader () refs = (M_success (), s)) ∧
    UNIT_TYPE () uv ⇒
      app (p: 'ffi ffi_proj) init_reader_v [uv]
        (HOL_STORE refs)
        (POSTv rv.
          SEP_EXISTS refs'.
            HOL_STORE refs' *
            &(init_reader () refs = (M_success (),refs')) *
            &UNIT_TYPE () rv)
Proof
  rw []
  \\ drule_then (qspecl_then [‘p’, ‘refs’] assume_tac) init_reader_spec
  \\ rfs [POSTve_POSTv, SEP_CLAUSES]
QED

Theorem reader_main_spec:
  (∃s. init_reader () refs = (M_success (), s)) ∧
  input_exists fs cl ⇒
    app (p:'ffi ffi_proj) reader_main_v
      [Conv NONE []]
      (COMMANDLINE cl * STDIO fs * HOL_STORE refs)
      (POSTv u.
        &UNIT_TYPE () u *
        STDIO (FST (reader_main fs refs (TL cl))))
Proof
  strip_tac
  \\ xcf_with_def (fetch "-" "reader_main_v_def")
  \\ reverse (Cases_on ‘wfcl cl’)
  >- (simp [COMMANDLINE_def] \\ xpull)
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto_spec (SOME CommandLine_arguments_spec)
  >- xsimpl
  \\ fs [input_exists_def]
  \\ simp [reader_main_def]
  \\ rename [‘init_reader _ _ = (_, refs')’]
  \\ CASE_TAC \\ fs []
  >-
   (fs [LIST_TYPE_def]
    \\ xmatch
    \\ xlet_auto >- (xcon \\ xsimpl)
    \\ xapp \\ simp [PULL_EXISTS]
    \\ qexistsl [‘COMMANDLINE cl’, ‘refs'’, ‘fs’, ‘inp’]
    \\ fs [stdin_def, stdin_content_def, OPTION_TYPE_def]
    \\ xsimpl)
  \\ rename [‘TL _ = h::t’]
  \\ Cases_on `t` \\ fs [LIST_TYPE_def]
  >-
   (Cases_on ‘h’ \\ fs [STRING_TYPE_def] \\ rveq
    \\ Cases_on ‘cl’ \\ fs [] \\ rveq
    \\ xmatch
    \\ IF_CASES_TAC >- (pop_assum mp_tac \\ EVAL_TAC)
    \\ reverse conj_tac >- (EVAL_TAC \\ fs [])
    \\ xlet_auto >- (xcon \\ xsimpl)
    \\ IF_CASES_TAC
    >-
     (xapp_spec read_from_SOME_fail
      \\ first_assum $ irule_at (Pos hd)
      \\ fs [OPTION_TYPE_def, FILENAME_def, wfcl_def, validArg_def]
      \\ qmatch_goalsub_abbrev_tac ‘COMMANDLINE cl’
      \\ qexistsl [‘refs'’, ‘COMMANDLINE cl’]
      \\ xsimpl)
    \\ fs []
    \\ xapp_spec read_from_SOME
    \\ qpat_assum ‘inFS_fname _ _’ $ irule_at Any
    \\ fs [OPTION_TYPE_def, FILENAME_def, wfcl_def, validArg_def]
    \\ qmatch_goalsub_abbrev_tac ‘COMMANDLINE cl’
    \\ qexistsl [‘refs'’, ‘COMMANDLINE cl’]
    \\ xsimpl)
  \\ rveq \\ fs []
  \\ rename1 ‘TL cl = x1::x2::x3’
  \\ Cases_on `x1` \\ Cases_on `x2` \\ fs [STRING_TYPE_def]
  \\ xmatch
  \\ IF_CASES_TAC >- (pop_assum mp_tac \\ EVAL_TAC)
  \\ reverse conj_tac >- (EVAL_TAC \\ fs [])
  \\ reverse conj_tac >- (EVAL_TAC \\ fs [])
  \\ xapp_spec output_stderr_spec
  \\ Q.LIST_EXISTS_TAC [‘COMMANDLINE cl * HOL_STORE refs'’, ‘msg_usage’, ‘fs’]
  \\ xsimpl
  \\ simp [msg_usage_v_thm]
QED

(* ------------------------------------------------------------------------- *)
(* whole_prog_spec                                                           *)
(* ------------------------------------------------------------------------- *)

Theorem reader_whole_prog_spec:
  input_exists fs cl ⇒
    whole_prog_spec reader_main_v cl fs (SOME (HOL_STORE init_refs))
      ((=) (FST (reader_main fs init_refs (TL cl))))
Proof
  rw [whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac ‘fs1 = _ with numchars := _’
  \\ qexists_tac ‘fs1’ \\ qunabbrev_tac ‘fs1’
  \\ reverse conj_tac
  >-
   (fs [reader_main_def, read_from_def]
    \\ rpt (PURE_CASE_TAC \\ fs [])
    \\ fs [GSYM add_stdo_with_numchars, with_same_numchars,
           GSYM fastForwardFD_with_numchars])
  \\ irule reader_main_spec
  \\ Cases_on `init_reader () init_refs`
  \\ drule init_reader_success \\ rw []
QED

val _ = add_user_heap_thm HOL_STORE_init_precond;

val st = get_ml_prog_state ();
val name = "reader_main";
val spec = UNDISCH reader_whole_prog_spec;
val (sem_thm,prog_tm) = whole_prog_thm st name spec
Definition reader_prog_def:
  reader_prog = ^prog_tm
End

Theorem reader_semantics =
  sem_thm
  |> REWRITE_RULE[GSYM reader_prog_def]
  |> DISCH_ALL
  |> ONCE_REWRITE_RULE [AND_IMP_INTRO]
  |> REWRITE_RULE
    [EVAL ``hasFreeFD fs``
     |> CONV_RULE (RHS_CONV (SIMP_CONV std_ss []))
     |> ONCE_REWRITE_RULE [CONJ_COMM] |> GSYM
     |> CONV_RULE (LHS_CONV (ONCE_REWRITE_CONV [CONJ_COMM]))]
  |> REWRITE_RULE [AND_IMP_INTRO, GSYM CONJ_ASSOC]
