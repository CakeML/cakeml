(*
  Simple wordcount program, to demonstrate use of CF.

  The implementation is very far from optimal efficiency: it reads in all the
  lines from the file, then splits them into words, then takes the lengths of
  those word lists. A more efficient implementation is possible even in CakeML.
*)

open preamble basis
     splitwordsTheory

val _ = new_theory"wordcountProg";

val _ = translation_extends"basisProg";

val wc_lines_def = Define`
  wc_lines lines = SUM (MAP (LENGTH o splitwords) lines)`;

val res = translate splitwords_def;
val res = translate wc_lines_def;

(* TODO: move *)
val inputLinesFromAny = process_topdecs`
  fun inputLinesFromAny fnameopt =
    case fnameopt of
      None => Some (TextIO.inputLines (TextIO.stdIn))
    | Some fname => TextIO.inputLinesFrom fname`;

val () = append_prog inputLinesFromAny;

Theorem inputLinesFromAny_spec:
   OPTION_TYPE FILENAME fo fov ∧ (IS_SOME fo ⇒ hasFreeFD fs) ∧
  (IS_NONE fo ⇒ (ALOOKUP fs.infds 0 = SOME (UStream(strlit"stdin"),ReadMode,0)))
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "inputLinesFromAny" (get_ml_prog_state()))
    [fov] (STDIO fs)
    (POSTv sv. &OPTION_TYPE (LIST_TYPE STRING_TYPE)
      (if IS_SOME fo ⇒ inFS_fname fs (THE fo)
       then SOME (case fo of NONE => all_lines_inode fs (UStream(strlit"stdin"))
                           | SOME f => all_lines fs f)
       else NONE) sv * STDIO (if IS_SOME fo then fs else fastForwardFD fs 0))
Proof
  xcf"inputLinesFromAny"(get_ml_prog_state())
  \\ reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull )
  \\ reverse(Cases_on`∃ll. wfFS (fs with numchars := ll)`) >- (fs[STDIO_def,IOFS_def] \\ xpull)
  \\ xmatch
  \\ Cases_on`fo` \\ fs[OPTION_TYPE_def]
  \\ (reverse conj_tac >- (EVAL_TAC \\ rw[]))
  >- (
    `∃cnt. get_file_content fs 0 = SOME (cnt,0)`
    by (
      simp[get_file_content_def, PULL_EXISTS]
      \\ fs[STD_streams_def]
      \\ last_x_assum(qspecl_then[`0`,`ReadMode`,`inp`]mp_tac)
      \\ simp[] \\ strip_tac
      \\ fs[wfFS_def]
      \\ imp_res_tac ALOOKUP_MEM
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD]
      \\ disch_then drule \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac`ALOOKUP aa bb = SOME _`
      \\ Cases_on`ALOOKUP aa bb` \\ fs[Abbr`aa`,Abbr`bb`]
      \\ imp_res_tac ALOOKUP_FAILS \\ fs[])
    \\ reverse xlet_auto
    >- (
      xcon
      \\ xsimpl
      \\ simp[all_lines_def]
      \\ fs[get_file_content_def]
      \\ fs[STD_streams_def]
      \\ last_x_assum(qspecl_then[`0`,`ReadMode`,`inp`]mp_tac)
      \\ rw[]
      \\ pairarg_tac \\ fs[]
      \\ fs[lines_of_def] )
    \\ qexists_tac`emp`
    \\ xsimpl
    \\ mp_tac stdin_v_thm
    \\ drule STD_streams_get_mode
    \\ simp[stdIn_def]
    \\ EVAL_TAC )
  \\ (reverse conj_tac >- (EVAL_TAC \\ rw[]))
  \\ xapp
  \\ fs[]
QED
(* -- *)

val wordcount = process_topdecs`
  fun wordcount u =
      case inputLinesFromAny
             (case CommandLine.arguments() of [fname] => Some fname | _ => None)
      of Some lines =>
        (TextIO.print (Int.toString (wc_lines lines)); TextIO.output1 TextIO.stdOut #" ";
         TextIO.print (Int.toString (List.length lines)); TextIO.output1 TextIO.stdOut #"\n")`;
val _ = append_prog wordcount;

val wordcount_precond_def = Define`
  wordcount_precond cl fs contents fs' ⇔
    case cl of
      [_; fname] =>
        hasFreeFD fs ∧
        ∃ ino. ALOOKUP fs.files fname = SOME ino ∧
        ALOOKUP fs.inode_tbl (File ino) = SOME contents ∧
        fs' = fs
    | _ =>
      ALOOKUP fs.infds 0 = SOME (UStream(strlit"stdin"),ReadMode,0) ∧
      ALOOKUP fs.inode_tbl (UStream (strlit"stdin")) = SOME contents ∧
      fs' = fastForwardFD fs 0`;

Theorem wordcount_precond_numchars:
   wordcount_precond cl fs contens fs' ⇒ fs'.numchars = fs.numchars
Proof
  rw[wordcount_precond_def]
  \\ every_case_tac \\ fs[]
QED

Theorem wordcount_spec:
   wordcount_precond cl fs contents fs'
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "wordcount" (get_ml_prog_state()))
     [uv] (STDIO fs * COMMANDLINE cl)
     (POSTv uv. &UNIT_TYPE () uv *
                 STDIO (add_stdout fs'
                   (concat [mlint$toString (&(LENGTH (TOKENS isSpace contents)));
                            strlit " ";
                            mlint$toString (&(LENGTH (splitlines contents)));
                            strlit "\n"]))
                * COMMANDLINE cl)
Proof
  simp [concat_def] \\
  strip_tac \\
  xcf "wordcount" (get_ml_prog_state()) \\
  xlet_auto >- (xcon \\ xsimpl) \\
  xlet_auto >- xsimpl \\
  (* we will need to know wfcl cl to prove that fname is a valid filename.
     this comes from the COMMANDLINE precondition.
     `wfcl cl` by ... wouldn't work because the current goal is needed to do the xpull on *)
  reverse(Cases_on`wfcl cl`) >- (rfs[COMMANDLINE_def] \\ xpull) \\
  (* similarly we will later want to know STD_streams fs *)
  reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull) \\
  xlet`POSTv fov. &OPTION_TYPE FILENAME (case TL cl of [fname] => SOME fname | _ => NONE) fov * COMMANDLINE cl * STDIO fs`
  >- (
    xmatch
    \\ fs[wfcl_def]
    \\ Cases_on`cl` \\ fs[]
    \\ Cases_on`t` \\ fs[LIST_TYPE_def]
    >- (
      reverse conj_tac >- (EVAL_TAC \\ rw[])
      \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
      \\ xcon \\ xsimpl
      \\ EVAL_TAC )
    \\ Cases_on`t'` \\ fs[LIST_TYPE_def]
    >- (
      reverse conj_tac >- (EVAL_TAC \\ rw[])
      \\ xcon
      \\ xsimpl
      \\ rw[OPTION_TYPE_def]
      \\ rw[FILENAME_def]
      \\ fs[validArg_def] )
    \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
    \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
    \\ xcon
    \\ xsimpl
    \\ rw[OPTION_TYPE_def] )
  \\ xlet_auto
  >- (
    xsimpl
    \\ fs[wordcount_precond_def, wfcl_def]
    \\ Cases_on`cl` \\ fs[]
    \\ Cases_on`t` \\ fs[]
    \\ Cases_on`t'` \\ fs[] )
  \\ qmatch_asmsub_abbrev_tac`OPTION_TYPE _ fo fov`
  \\ qmatch_asmsub_abbrev_tac`OPTION_TYPE _ so sv`
  \\ `∃lines. so = SOME lines`
  by (
    fs[wordcount_precond_def, wfcl_def]
    \\ Cases_on`cl` \\ fs[]
    \\ simp[Abbr`so`]
    \\ simp[IS_SOME_EXISTS]
    \\ simp[Abbr`fo`]
    \\ simp[CaseEq"list"]
    \\ strip_tac \\ fs[]
    \\ simp[inFS_fname_def]
    \\ imp_res_tac ALOOKUP_MEM
    \\ simp[MEM_MAP, EXISTS_PROD]
    \\ asm_exists_tac \\ rw[] )
  \\ fs[Abbr`so`]
  \\ xmatch \\ fs[OPTION_TYPE_def] \\
  reverse conj_tac >- (EVAL_TAC \\ fs[]) \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  (* TODO: xlet_auto fails *)
  qmatch_goalsub_abbrev_tac`STDIO fs''` \\
  xlet_auto_spec(SOME (Q.SPEC`fs''` (Q.GEN`fs`output1_stdout_spec))) >- xsimpl \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  xapp_spec output1_stdout_spec \\ xsimpl \\
  (* TODO: STDIO prevents xapp/xsimpl instantiating this already *)
  qunabbrev_tac`fs''` \\
  CONV_TAC SWAP_EXISTS_CONV \\
  qmatch_goalsub_abbrev_tac`STDIO fs''` \\
  qexists_tac`fs''` \\ xsimpl \\
  simp[Abbr`fs''`] \\
  DEP_REWRITE_TAC[GEN_ALL add_stdo_o] \\
  rpt(conj_tac >-
    metis_tac[STD_streams_add_stdout,STD_streams_stdout,
              STD_streams_fastForwardFD,DECIDE``0n ≠ 1 ∧0n ≠ 2``]) \\
  qmatch_goalsub_abbrev_tac`STDIO (_ output) ==>> STDIO (_ output') * GC` \\
  `output = output'` suffices_by (
    fs[wordcount_precond_def, Abbr`fo`,IS_SOME_EXISTS,CaseEq"list"]
    \\ Cases_on`cl` \\ fs[wfcl_def]
    \\ rw[] \\ fs[] \\ rveq \\ xsimpl
    \\ Cases_on`t` \\ fs[] \\ xsimpl
    \\ Cases_on`t'` \\ fs[] \\ xsimpl ) \\
  simp[Abbr`output`,Abbr`output'`] \\
  fs [mlintTheory.toString_thm,implode_def,strcat_def,concat_def] \\
  simp[wc_lines_def,str_def,implode_def] \\
  qmatch_abbrev_tac`s1 ++ " " ++ s2 = t1 ++ " " ++ t2` \\
  `s1 = t1 ∧ s2 = t2` suffices_by rw[] \\
  simp[Abbr`s1`,Abbr`t1`,Abbr`s2`,Abbr`t2`] \\
  simp[mlintTheory.toString_thm,integerTheory.INT_ABS_NUM] \\
  rveq \\
  reverse conj_tac >- (
    simp[all_lines_def,lines_of_def] \\
    fs[Abbr`fo`]
    \\ fs[wordcount_precond_def]
    \\ Cases_on`cl` \\ fs[wfcl_def]
    \\ Cases_on`t` \\ fs[]
    \\ Cases_on`t'` \\ fs[] )

  \\ simp[GSYM MAP_MAP_o,GSYM LENGTH_FLAT]
  \\ fs[Abbr`fo`]
  \\ fs[wordcount_precond_def]
  \\ Cases_on`cl` \\ fs[wfcl_def]
  \\ Cases_on`t` \\ fs[]
  \\ TRY (Cases_on`t'` \\ fs[])
  \\ simp[all_lines_def,splitwords_lines_of,splitwords_def, mlstringTheory.TOKENS_eq_tokens_sym]
QED

Theorem wordcount_whole_prog_spec:
   wordcount_precond cl fs contents fs'
   ⇒
   whole_prog_spec ^(fetch_v "wordcount" (get_ml_prog_state())) cl fs NONE
   ((=)
     (add_stdout fs'
       (concat [mlint$toString (&(LENGTH (TOKENS isSpace contents)));
                strlit " ";
                mlint$toString (&(LENGTH (splitlines contents)));
                strlit "\n"])))
Proof
  disch_then assume_tac
  \\ imp_res_tac wordcount_precond_numchars
  \\ pop_assum(assume_tac o SYM)
  \\ simp[whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac`fs1`
  \\ simp[Abbr`fs1`,GSYM add_stdo_with_numchars,with_same_numchars]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe (UNDISCH wordcount_spec)))
  \\ xsimpl
QED

val spec = wordcount_whole_prog_spec |> UNDISCH_ALL
val (sem_thm,prog_tm) = whole_prog_thm (get_ml_prog_state()) "wordcount" spec
val wordcount_prog_def = mk_abbrev"wordcount_prog" prog_tm;

val wordcount_semantics = save_thm("wordcount_semantics",
  sem_thm |> PURE_REWRITE_RULE[GSYM wordcount_prog_def]
  |> DISCH_ALL
  |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC,LENGTH]
  |> SIMP_RULE (srw_ss()) []);

val _ = export_theory();
