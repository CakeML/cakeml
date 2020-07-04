(*
  Deeply embedded CakeML program that implements an OpenTheory article
  checker.
*)
open preamble basis
     ml_monadBaseTheory ml_monad_translatorLib cfMonadTheory cfMonadLib
     holKernelTheory holKernelProofTheory ml_hol_kernelProgTheory readerTheory
     readerProofTheory prettyTheory
     reader_commonProgTheory reader_initTheory

val _ = new_theory "readerProg"
val _ = m_translation_extends "reader_commonProg"

(* TODO: move *)
Theorem fastForwardFD_ADELKEY_same[simp]:
  forwardFD fs fd n with infds updated_by ADELKEY fd =
  fs with infds updated_by ADELKEY fd
Proof
  fs [forwardFD_def, IO_fs_component_equality]
QED

(* TODO: move *)
Theorem validFileFD_forwardFD:
  validFileFD fd (forwardFD fs x y).infds ⇔ validFileFD fd fs.infds
Proof
  rw [forwardFD_def, validFileFD_def, AFUPDKEY_ALOOKUP]
  \\ PURE_TOP_CASE_TAC \\ fs []
  \\ rename1 ‘_ = SOME xx’ \\ PairCases_on ‘xx’ \\ rw []
QED

(* -------------------------------------------------------------------------
 * Reading lines into commands
 * ------------------------------------------------------------------------- *)

val r = translate is_newline_def;

(*
 * Obtain a list of commands from an instream. Avoids keeping the entire
 * string in memory by calling inputLine repeatedly.
 *
 * This can be used with input from stdin, since there are no buffered
 * instreams for stdin (yet).
 *)

val _ = (append_prog o process_topdecs) ‘
  fun l2c_aux acc ins =
    case TextIO.inputLine ins of
      None => List.rev acc
    | Some ln => l2c_aux (tokenize (str_prefix ln)::acc) ins;
  ’;

Definition l2c_aux_sem_def:
  (l2c_aux_sem acc [] = REVERSE acc) ∧
  (l2c_aux_sem acc (h::t) =
    l2c_aux_sem (tokenize (implode (str_prefix h))::acc) t)
End

Theorem l2c_aux_sem_MAP:
  ∀acc ls.
    l2c_aux_sem acc ls =
    REVERSE acc ++ MAP (tokenize o str_prefix o implode) ls
Proof
  Induct_on ‘ls’
  \\ rw [l2c_aux_sem_def]
QED

Theorem l2c_aux_spec:
  ∀n fs fd fdv ls lsv.
    INSTREAM fd fdv ∧
    get_file_content fs fd = SOME (content, n) ∧
    get_mode fs fd = SOME ReadMode ⇒
    LIST_TYPE READER_COMMAND_TYPE ls lsv ⇒
      app (p: 'ffi ffi_proj) l2c_aux_v
        [lsv; fdv]
        (STDIO fs)
        (POSTv v.
          &LIST_TYPE READER_COMMAND_TYPE (l2c_aux_sem ls (linesFD fs fd)) v *
          STDIO (fastForwardFD fs fd))
Proof
  Induct_on ‘linesFD fs fd’
  >-
   (rpt strip_tac
    \\ qpat_x_assum ‘[] = _’ (assume_tac o SYM)
    \\ xcf "l2c_aux" (get_ml_prog_state ())
    \\ ‘IS_SOME (get_file_content fs fd)’
      by fs []
    \\ ‘lineFD fs fd = NONE’
      by fs [linesFD_nil_lineFD_NONE]
    \\ xlet_auto
    >- xsimpl
    \\ fs [OPTION_TYPE_def, l2c_aux_sem_def]
    \\ xmatch
    \\ xapp_spec (INST_TYPE [alpha |-> “:command”]
                            ListProgTheory.reverse_v_thm)
    \\ instantiate
    \\ simp [lineFD_NONE_lineForwardFD_fastForwardFD]
    \\ xsimpl)
  \\ rpt strip_tac
  \\ xcf "l2c_aux" (get_ml_prog_state ())
  \\ qpat_x_assum ‘_::_ = _’ (assume_tac o SYM)
  \\ drule linesFD_cons_imp
  \\ strip_tac \\ rveq \\ fs []
  \\ xlet_auto >- xsimpl
  \\ fs [OPTION_TYPE_def, l2c_aux_sem_MAP]
  \\ xmatch
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xapp
  \\ qexists_tac ‘emp’
  \\ xsimpl
  \\ Q.REFINE_EXISTS_TAC ‘x::xs’
  \\ simp [LIST_TYPE_def]
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
  \\ Q.LIST_EXISTS_TAC [‘lineForwardFD fs fd’, ‘fd’] \\ simp []
  \\ drule get_file_content_lineForwardFD_forwardFD \\ rw []
  \\ xsimpl
  \\ metis_tac [APPEND_ASSOC, CONS_APPEND]
QED

val _ = (append_prog o process_topdecs) ‘
  fun l2c ins = l2c_aux [] ins;
  ’;

Theorem l2c_spec:
  INSTREAM fd fdv ∧
  get_file_content fs fd = SOME (content, n) ∧
  get_mode fs fd = SOME ReadMode ⇒
    app (p: 'ffi ffi_proj) l2c_v
      [fdv]
      (STDIO fs)
      (POSTv v.
        &LIST_TYPE READER_COMMAND_TYPE
          (MAP (tokenize o str_prefix o implode) (linesFD fs fd)) v *
        STDIO (fastForwardFD fs fd))
Proof
  strip_tac
  \\ xcf "l2c" (get_ml_prog_state ())
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xapp
  \\ Q.LIST_EXISTS_TAC [‘emp’, ‘[]’]
  \\ instantiate
  \\ simp [l2c_aux_sem_MAP, PULL_EXISTS, LIST_TYPE_def]
  \\ xsimpl
QED

val _ = (append_prog o process_topdecs) ‘
  fun l2c_from fnm =
    let
      val ins = TextIO.openIn fnm
      val cmds = l2c ins
      val _ = TextIO.closeIn ins
    in
      Some cmds
    end
    handle TextIO.BadFileName => None
  ’;

(*
 * This is the drop-in replacement for b_inputAllTokensFrom for
 * stdin operation. Now, readLines (from readerTheory) can be used
 * both for stdin, buffered I/O, and with the monadIO version.
 *)

Theorem l2c_from_spec:
  FILENAME f fv ∧
  hasFreeFD fs ⇒
    app (p: 'ffi ffi_proj) l2c_from_v
      [fv]
      (STDIO fs)
      (POSTv sv.
        &OPTION_TYPE (LIST_TYPE READER_COMMAND_TYPE)
          (if inFS_fname fs f then
             SOME (MAP (tokenize o str_prefix) (all_lines fs f))
           else
             NONE) sv *
        STDIO fs)
Proof
  strip_tac
  \\ xcf "l2c_from" (get_ml_prog_state ())
  \\ ‘CARD (set (MAP FST fs.infds)) < fs.maxFD’
    by fs []
  \\ reverse (Cases_on ‘STD_streams fs’)
  >-
   (fs [STDIO_def]
    \\ xpull)
  \\ reverse (Cases_on ‘consistentFS fs’)
  >-
   (fs [STDIO_def, IOFS_def, wfFS_def]
    \\ xpull
    \\ fsrw_tac [SATISFY_ss] [consistentFS_def])
  \\ reverse IF_CASES_TAC
  >-
   (xhandle ‘POSTe ev.
              &BadFileName_exn ev *
              &(¬inFS_fname fs f) *
              STDIO fs’
    >- (xlet_auto_spec (SOME openIn_STDIO_spec) \\ xsimpl)
    \\ fs [BadFileName_exn_def]
    \\ xcases
    \\ xcon
    \\ simp [OPTION_TYPE_def]
    \\ xsimpl)
  \\ qmatch_goalsub_abbrev_tac ‘$POSTv Q’
  \\ xhandle ‘$POSTv Q’ \\ xsimpl
  \\ qunabbrev_tac ‘Q’
  \\ xlet_auto_spec (SOME openIn_STDIO_spec) \\ xsimpl
  \\ imp_res_tac nextFD_ltX
  \\ progress inFS_fname_ALOOKUP_EXISTS
  \\ progress ALOOKUP_inFS_fname_openFileFS_nextFD
  \\ rfs[]
  \\ pop_assum (qspec_then ‘0’ strip_assume_tac)
  \\ qmatch_assum_abbrev_tac ‘validFD fd fso’
  \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS
  \\ ‘∃c. get_file_content fso fd = SOME (c, 0)’
    by fs [get_file_content_def, validFD_def, Abbr ‘fso’, openFileFS_inode_tbl]
  \\ ‘get_mode fso fd = SOME ReadMode’
  by fs [Abbr ‘fso’, openFileFS_def, get_mode_def, get_file_content_fsupdate]
  \\ xlet_auto
  >- xsimpl
  \\ xlet_auto_spec (SOME closeIn_STDIO_spec)
  >-
   (xsimpl
    \\ ‘¬(fd = 0 ∨ fd = 1 ∨ fd = 2)’
      suffices_by fs []
    \\ fs [STD_streams_def]
    \\ metis_tac [nextFD_NOT_MEM, ALOOKUP_MEM])
  >-
   (xsimpl
    \\ simp [validFileFD_def]
    \\ drule ALOOKUP_inFS_fname_openFileFS_nextFD
    \\ rfs[]
    \\ fsrw_tac [SATISFY_ss] [Abbr ‘fso’])
  \\ xcon
  \\ simp [OPTION_TYPE_def]
  \\ fs [get_file_content_def, Abbr ‘fso’, openFileFS_inode_tbl]
  \\ imp_res_tac linesFD_openFileFS_nextFD \\ rfs []
  \\ first_x_assum (qspec_then ‘ReadMode’ mp_tac) \\ strip_tac \\ fs []
  \\ fs [MAP_MAP_o]
  \\ xsimpl
  \\ fsrw_tac [ETA_ss] [o_DEF, implode_explode]
  \\ qmatch_goalsub_abbrev_tac ‘STDIO fs'’
  \\ ‘fs' = fs’
    suffices_by (rw [] \\ xsimpl)
  \\ unabbrev_all_tac
  \\ fs [openFileFS_ADELKEY_nextFD]
QED

(* -------------------------------------------------------------------------
 * CakeML wrapper
 * ------------------------------------------------------------------------- *)

(*
 * Read all input from stdin.
 *)

val _ = (append_prog o process_topdecs) `
  fun read_stdin () =
    let
      val st = fst (readlines init_state (l2c TextIO.stdIn))
    in
      TextIO.print (msg_success st (Kernel.context ()))
    end
    handle Kernel.Fail e => TextIO.output TextIO.stdErr e;
  `;

(*
 * Read all input from file.
 * Uses the regular (unbuffered) I/O.
 *)

val _ = (append_prog o process_topdecs) `
  fun read_file file =
    case l2c_from file of
      None =>
        TextIO.output TextIO.stdErr (msg_bad_name file)
    | Some ls =>
        let
          val st = fst (readlines init_state ls)
        in
          TextIO.print (msg_success st (Kernel.context ()))
        end
        handle Kernel.Fail e => TextIO.output TextIO.stdErr e;
  `;

(*
 * Read all input from file.
 * Uses the buffered I/O.
 *)

val _ = (append_prog o process_topdecs) `
  fun read_file_buffered file =
    case TextIO.b_inputAllTokensFrom file is_newline tokenize of
      None =>
        TextIO.output TextIO.stdErr (msg_bad_name file)
    | Some ls =>
        let
          val st = fst (readlines init_state (List.concat ls))
        in
          TextIO.print (msg_success st (Kernel.context ()))
        end
        handle Kernel.Fail e => TextIO.output TextIO.stdErr e;
  `;

Theorem read_stdin_spec:
  UNIT_TYPE () uv ∧
  (∃inp. stdin fs inp 0) ⇒
    app (p: 'ffi ffi_proj) read_stdin_v [uv]
      (STDIO fs * HOL_STORE refs)
      (POSTv u.
        &UNIT_TYPE () u *
        STDIO (FST (read_stdin fs refs)) *
        HOL_STORE (FST (SND (read_stdin fs refs))))
Proof
  xcf "read_stdin" (get_ml_prog_state ())
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def] \\ xpull)
  \\ fs [UNIT_TYPE_def]
  \\ simp [read_stdin_def]
  \\ assume_tac INSTREAM_stdin
  \\ drule stdin_get_file_content \\ strip_tac
  \\ drule STD_streams_get_mode \\ strip_tac
  \\ assume_tac init_state_v_thm
  \\ xmatch
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  >-
   (CASE_TAC \\ fs []
    \\ qmatch_goalsub_abbrev_tac ‘$POSTv Q’
    \\ xhandle ‘$POSTv Q’ \\ xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto
    >- xsimpl
    >-
     (xsimpl
      \\ rpt gen_tac
      \\ strip_tac
      \\ drule linesFD_splitlines_get_stdin
      \\ disch_then (assume_tac o SYM)
      \\ drule stdin_get_stdin \\ strip_tac \\ fs []
      \\ fs [lines_of_def, MAP_MAP_o, stdin_def, o_DEF]
      \\ rfs []
      \\ fs [strcat_thm])
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xcon \\ xsimpl)
    \\ rename1 ‘(Success st1p, refs1)’
    \\ drule context_spec
    \\ disch_then (qspecl_then [‘p’, ‘refs1’] mp_tac)
    \\ simp [context_def, get_the_context_def, SEP_CLAUSES]
    \\ ‘∀Q. POSTve Q (λx. SEP_F) = $POSTv Q’
      by rw [POSTve_def, POSTv_def, SEP_CLAUSES]
    \\ simp []
    \\ strip_tac
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xapp
    \\ qunabbrev_tac ‘Q’
    \\ instantiate
    \\ xsimpl
    \\ drule linesFD_splitlines_get_stdin
    \\ disch_then (assume_tac o SYM)
    \\ drule stdin_get_stdin \\ strip_tac \\ fs []
    \\ fs [lines_of_def, MAP_MAP_o, stdin_def, o_DEF]
    \\ rfs []
    \\ fs [strcat_thm]
    \\ rveq \\ fs []
    \\ Q.LIST_EXISTS_TAC [‘HOL_STORE r’, ‘fastForwardFD fs 0’]
    \\ simp [add_stdout_fastForwardFD]
    \\ xsimpl
    \\ rw [UNIT_TYPE_def])
  \\ CASE_TAC \\ fs []
  \\ xhandle ‘POSTe ev.
                &HOL_EXN_TYPE (Fail m) ev *
                HOL_STORE r *
                STDIO (fastForwardFD fs 0)’
  >-
   (xlet_auto >- xsimpl
    \\ xlet_auto
    >- xsimpl
    >-
     (xsimpl
      \\ rpt gen_tac
      \\ strip_tac
      \\ drule linesFD_splitlines_get_stdin
      \\ disch_then (assume_tac o SYM)
      \\ drule stdin_get_stdin \\ strip_tac \\ fs []
      \\ fs [lines_of_def, MAP_MAP_o, stdin_def, o_DEF]
      \\ rfs []
      \\ fs [strcat_thm]
      \\ xsimpl)
    \\ drule linesFD_splitlines_get_stdin
    \\ disch_then (assume_tac o SYM)
    \\ drule stdin_get_stdin \\ strip_tac \\ fs []
    \\ fs [lines_of_def, MAP_MAP_o, stdin_def, o_DEF]
    \\ rfs []
    \\ fs [strcat_thm])
  \\ fs [HOL_EXN_TYPE_def]
  \\ xcases
  \\ xapp_spec output_stderr_spec
  \\ instantiate
  \\ Q.LIST_EXISTS_TAC [‘HOL_STORE r’, ‘fastForwardFD fs 0’]
  \\ xsimpl
  \\ rw [UNIT_TYPE_def]
QED

Theorem read_file_spec:
  FILENAME fnm fnv ∧
  hasFreeFD fs ⇒
    app (p: 'ffi ffi_proj) read_file_v [fnv]
      (STDIO fs * HOL_STORE refs)
      (POSTv u.
        &UNIT_TYPE () u *
        STDIO (FST (read_file fs refs fnm)) *
        HOL_STORE (FST (SND (read_file fs refs fnm))))
Proof
  xcf "read_file" (get_ml_prog_state())
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def] \\ xpull)
  \\ reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[])
  \\ xlet_auto >- xsimpl
  \\ simp[read_file_def]
  \\ reverse IF_CASES_TAC \\ fs [OPTION_TYPE_def]
  >-
   (xmatch
    \\ xlet_auto >- xsimpl
    \\ xapp_spec output_stderr_spec
    \\ instantiate
    \\ Q.LIST_EXISTS_TAC [‘HOL_STORE refs’, ‘fs’]
    \\ xsimpl)
  \\ xmatch
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  >-
   (CASE_TAC \\ fs []
    \\ qmatch_goalsub_abbrev_tac ‘$POSTv Q’
    \\ xhandle ‘$POSTv Q’ \\ xsimpl
    \\ qunabbrev_tac ‘Q’
    \\ assume_tac init_state_v_thm
    \\ xlet_auto
    >- xsimpl
    >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xcon \\ xsimpl)
    \\ rename1 ‘(Success (st1,_), refs1)’
    \\ drule context_spec
    \\ disch_then (qspecl_then [‘p’, ‘refs1’] mp_tac)
    \\ simp [context_def, get_the_context_def, SEP_CLAUSES]
    \\ ‘∀Q. POSTve Q (λx. SEP_F) = $POSTv Q’
      by rw [POSTve_def, POSTv_def, SEP_CLAUSES]
    \\ simp []
    \\ strip_tac
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xapp
    \\ instantiate
    \\ rveq \\ fs []
    \\ Q.LIST_EXISTS_TAC [‘HOL_STORE refs'’, ‘fs’]
    \\ xsimpl)
  \\ CASE_TAC \\ fs []
  \\ xhandle ‘POSTe ev.
                &HOL_EXN_TYPE (Fail m) ev *
                HOL_STORE r *
                STDIO fs’
  >-
   (assume_tac init_state_v_thm
    \\ xlet_auto \\ xsimpl)
  \\ fs [HOL_EXN_TYPE_def]
  \\ xcases
  \\ xapp_spec output_stderr_spec
  \\ instantiate
  \\ Q.LIST_EXISTS_TAC [‘HOL_STORE r’, ‘fs’]
  \\ xsimpl
QED


Theorem b_inputAllTokensFrom_spec2 =
  GEN_ALL b_inputAllTokensFrom_spec |>
  Q.ISPECL [
    ‘p: 'ffi ffi_proj’,
    ‘tokenize_v’,
    ‘tokenize’,
    ‘is_newline_v’,
    ‘fs: IO_fs’,
    ‘fnamev: v’,
    ‘fname: mlstring’,
    ‘is_newline’,
    ‘READER_COMMAND_TYPE’
  ] |>
  SIMP_RULE bool_ss
    [theorem "is_newline_v_thm", tokenize_v_thm, is_newline_def];

Theorem read_file_buffered_spec:
  FILENAME fnm fnv ∧
  hasFreeFD fs ⇒
    app (p: 'ffi ffi_proj) read_file_buffered_v [fnv]
      (STDIO fs * HOL_STORE refs)
      (POSTv u.
        &UNIT_TYPE () u *
        STDIO (FST (read_file_buffered fs refs fnm)) *
        HOL_STORE (FST (SND (read_file_buffered fs refs fnm))))
Proof
  xcf "read_file_buffered" (get_ml_prog_state())
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def] \\ xpull)
  \\ reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[])
  \\ xlet ‘POSTv sv.
             &OPTION_TYPE (LIST_TYPE (LIST_TYPE READER_COMMAND_TYPE))
               (if inFS_fname fs fnm then
                  SOME (MAP (MAP tokenize ∘ tokens is_newline)
                            (all_lines fs fnm))
                else
                  NONE) sv *
             STDIO fs *
             HOL_STORE refs’
  >-
   (xapp_spec b_inputAllTokensFrom_spec2
    \\ instantiate
    \\ xsimpl)
  \\ simp [read_file_buffered_def]
  \\ reverse IF_CASES_TAC \\ fs [OPTION_TYPE_def]
  >-
   (xmatch
    \\ xlet_auto >- xsimpl
    \\ xapp_spec output_stderr_spec
    \\ instantiate
    \\ Q.LIST_EXISTS_TAC [‘HOL_STORE refs’, ‘fs’]
    \\ xsimpl)
  \\ xmatch
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ CASE_TAC \\ fs []
  >-
   (qmatch_goalsub_abbrev_tac ‘$POSTv Q’
    \\ xhandle ‘$POSTv Q’ \\ xsimpl
    \\ qunabbrev_tac ‘Q’
    \\ xlet_auto >- xsimpl
    \\ assume_tac init_state_v_thm
    \\ xlet_auto
    >- xsimpl
    >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- (xcon \\ xsimpl)
    \\ rveq \\ fs []
    \\ rename1 ‘(Success _, refs1)’
    \\ drule context_spec
    \\ disch_then (qspecl_then [‘p’, ‘refs1’] mp_tac)
    \\ simp [context_def, get_the_context_def, SEP_CLAUSES]
    \\ ‘∀Q. POSTve Q (λx. SEP_F) = $POSTv Q’
      by rw [POSTve_def, POSTv_def, SEP_CLAUSES]
    \\ simp []
    \\ strip_tac
    \\ xlet_auto >- xsimpl
    \\ rveq \\ fs []
    \\ xlet_auto >- xsimpl
    \\ xapp
    \\ instantiate
    \\ Q.LIST_EXISTS_TAC [‘HOL_STORE refs'’, ‘fs’]
    \\ xsimpl)
  \\ xhandle ‘POSTe ev.
                &HOL_EXN_TYPE (Fail m) ev *
                HOL_STORE r *
                STDIO fs’
  >-
   (xlet_auto >- xsimpl
    \\ assume_tac init_state_v_thm
    \\ xlet_auto \\ xsimpl)
  \\ fs [HOL_EXN_TYPE_def]
  \\ xcases
  \\ xapp_spec output_stderr_spec
  \\ instantiate
  \\ Q.LIST_EXISTS_TAC [‘HOL_STORE r’, ‘fs’]
  \\ xsimpl
QED

(* TODO
 * - Tidy up! All of these theorems are basically the same copy-paste
 *   over and over.
 *)

val _ = (append_prog o process_topdecs) `
  fun reader_main u =
    let
      val _ = init_reader ()
    in
      case CommandLine.arguments () of
        [] => read_stdin ()
      | ["--nobuf", file] => read_file file
      | [file] => read_file_buffered file
      | _ => TextIO.output TextIO.stdErr msg_usage
      end
  `;

(* TODO:
 * Awful everything, fix
 *)
Theorem reader_main_spec:
  (∃s. init_reader () refs = (Success (), s)) ∧
  input_exists fs cl ⇒
    app (p:'ffi ffi_proj) reader_main_v
      [Conv NONE []]
      (COMMANDLINE cl * STDIO fs * HOL_STORE refs)
      (POSTv u.
        &UNIT_TYPE () u *
        STDIO (FST (reader_main fs refs (TL cl))))
Proof
  cheat (* Probably true but way too annoying with the pattern match *)
        (* on the string literal ... *)
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
  \\ qmatch_goalsub_abbrev_tac `fs1 = _ with numchars := _`
  \\ qexists_tac `fs1` \\ fs [Abbr`fs1`]
  \\ reverse conj_tac
  >- cheat (* TODO this theorem too becomes annoying *) (*
   (fs [reader_main_def, read_file_def, read_stdin_def, read_file_buffered_def]
    \\ rpt (PURE_CASE_TAC \\ fs [])
    \\ fs [GSYM add_stdo_with_numchars, with_same_numchars]
    \\ metis_tac [fastForwardFD_with_numchars, with_same_numchars]) *)
  \\ irule (reader_main_spec
            |> UNDISCH |> MATCH_MP app_wgframe
            |> MP_CANON |> DISCH_ALL
            |> SIMP_RULE (srw_ss()) [])
  \\ xsimpl \\ instantiate
  \\ xsimpl
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `init_refs` \\ xsimpl
  \\ Cases_on `init_reader () init_refs`
  \\ drule init_reader_success \\ rw []
QED

val _ = add_user_heap_thm HOL_STORE_init_precond;

val st = get_ml_prog_state ();
val name = "reader_main";
val spec = UNDISCH reader_whole_prog_spec;
val (sem_thm,prog_tm) = whole_prog_thm st name spec
val reader_prog_def = Define `reader_prog = ^prog_tm`

val reader_semantics =
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
  |> curry save_thm "reader_semantics";

val _ = export_theory ();

