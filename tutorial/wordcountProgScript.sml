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

val wordcount = process_topdecs`
  fun wordcount u =
    case TextIO.inputLinesFrom (List.hd (CommandLine.arguments()))
    of SOME lines =>
      (TextIO.print_string (Int.toString (wc_lines lines)); TextIO.print_string " ";
       TextIO.print_string (Int.toString (List.length lines)); TextIO.print_newline())`;
val _ = append_prog wordcount;

val wordcount_spec = Q.store_thm("wordcount_spec",
  `hasFreeFD fs ∧ inFS_fname fs (File fname) ∧
   cl = [explode pname; explode fname] ∧
   contents = THE (ALOOKUP fs.files (File fname))
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "wordcount" (get_ml_prog_state()))
     [uv] (STDIO fs * COMMANDLINE cl)
     (POSTv uv. &UNIT_TYPE () uv *
                 STDIO (add_stdout fs
                   ((toString (LENGTH (TOKENS isSpace contents))) ++ " " ++
                    (toString (LENGTH (splitlines contents)) ++ "\n")))
                * COMMANDLINE cl)`,
  strip_tac \\
  xcf "wordcount" (get_ml_prog_state()) \\
  xlet_auto >- (xcon \\ xsimpl) \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  (* we will need to know wfcl cl to prove that fname is a valid filename.
     this comes from the COMMANDLINE precondition.
     `wfcl cl` by ... wouldn't work because the current goal is needed to do the xpull on *)
  reverse(Cases_on`wfcl cl`) >- (rfs[COMMANDLINE_def] \\ xpull) \\
  (* similarly we will later want to know STD_streams fs *)
  reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull) \\
  (* TODO: xlet_auto doesn't work *)
  xlet_auto_spec(SOME inputLinesFrom_spec) >- (
    xsimpl \\
    rfs[wfcl_def,validArg_def,EVERY_MEM,GSYM LENGTH_explode] ) \\
  xmatch \\ fs[OPTION_TYPE_def] \\
  reverse conj_tac >- (EVAL_TAC \\ fs[]) \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  (* TODO: xlet_auto fails *)
  xlet_auto_spec(SOME (SPEC_ALL print_string_spec)) >- xsimpl \\
  (* TODO: xlet_auto fails *)
  qmatch_goalsub_abbrev_tac`STDIO fs'` \\
  xlet_auto_spec(SOME (Q.SPEC`fs'` print_string_spec)) >- xsimpl \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  (* TODO: xlet_auto fails *)
  qunabbrev_tac`fs'` \\
  qmatch_goalsub_abbrev_tac`STDIO fs'` \\
  xlet_auto_spec(SOME (Q.SPEC`fs'` print_string_spec)) >- xsimpl \\
  xlet_auto >- ( xcon \\ xsimpl ) \\
  xapp \\ xsimpl \\
  (* TODO: STDIO prevents xapp/xsimpl instantiating this already *)
  qunabbrev_tac`fs'` \\
  CONV_TAC SWAP_EXISTS_CONV \\
  qmatch_goalsub_abbrev_tac`STDIO fs'` \\
  qexists_tac`fs'` \\ xsimpl \\
  simp[Abbr`fs'`] \\
  DEP_REWRITE_TAC[GEN_ALL add_stdo_o] \\
  rpt(conj_tac >- metis_tac[STD_streams_add_stdout,STD_streams_stdout]) \\
  qmatch_goalsub_abbrev_tac`STDIO (_ output) ==>> STDIO (_ output') * GC` \\
  `output = output'` suffices_by xsimpl \\
  simp[Abbr`output`,Abbr`output'`] \\
  simp[wc_lines_def] \\
  qmatch_abbrev_tac`s1 ++ " " ++ s2 = t1 ++ " " ++ t2` \\
  `s1 = t1 ∧ s2 = t2` suffices_by rw[] \\
  simp[Abbr`s1`,Abbr`t1`,Abbr`s2`,Abbr`t2`] \\
  simp[mlintTheory.toString_thm,integerTheory.INT_ABS_NUM] \\
  reverse conj_tac >- simp[all_lines_def] \\
  simp[GSYM MAP_MAP_o,GSYM LENGTH_FLAT,splitwords_all_lines] \\
  simp[splitwords_def,mlstringTheory.TOKENS_eq_tokens_sym]);

val spec = wordcount_spec |> UNDISCH_ALL
           |> SIMP_RULE (srw_ss()) [STDIO_def] |> add_basis_proj
val name = "wordcount" (* TODO: call_thm is not robust to reordering the precondition conjuncts etc. *)
val (sem_thm,prog_tm) = call_thm (get_ml_prog_state()) name spec

val wordcount_prog_def = mk_abbrev"wordcount_prog" prog_tm;

val wordcount_semantics = save_thm("wordcount_semantics",
  sem_thm
  |> PURE_REWRITE_RULE[GSYM wordcount_prog_def]
  |> DISCH_ALL
  |> Q.GENL[`cls`,`contents`]
  |> SIMP_RULE(srw_ss())[STD_streams_add_stdout]
  |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]);

val _ = export_theory();
