(*
  I/O wrapper for the OCaml parser.
 *)

open preamble;
open caml_parserProgTheory cfLib basis ml_translatorLib ml_translatorTheory;

val _ = new_theory "camlProg";

val _ = translation_extends "caml_parserProg";

val main = process_topdecs ‘
  fun main u =
    case run_main (TextIO.inputAll TextIO.stdIn) of
      Inl err => TextIO.output TextIO.stdErr (err ^ "\n")
    | Inr out => TextIO.print (out ^ "\n");
  ’;

val res = append_prog main;

val main_v_def = fetch "-" "main_v_def";

Definition caml_parse_def:
  caml_parse inp fs =
    case run_main inp of
      INL err => add_stderr (fastForwardFD fs 0) (err ^ «\n»)
    | INR out => add_stdout (fastForwardFD fs 0) (implode out ^ «\n»)
End

Theorem main_spec:
   app (p:'ffi ffi_proj) main_v
     [Conv NONE []] (STDIO fs * COMMANDLINE cl)
     (POSTv uv.
       &UNIT_TYPE () uv
       * STDIO (caml_parse (get_stdin fs) fs)
       * COMMANDLINE cl)
Proof
  xcf_with_def "main" main_v_def
  \\ simp [caml_parse_def]
  \\ reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull)
  \\ reverse(Cases_on`∃inp pos. stdin fs inp pos`)
  >- (
    fs[STDIO_def,IOFS_def] \\ xpull \\ fs[stdin_def]
    \\ `F` suffices_by fs[]
    \\ fs[wfFS_def,STD_streams_def,MEM_MAP,Once EXISTS_PROD,PULL_EXISTS]
    \\ fs[EXISTS_PROD]
    \\ metis_tac[ALOOKUP_FAILS,ALOOKUP_MEM,NOT_SOME_NONE,SOME_11,PAIR_EQ,option_CASES] )
  \\ fs[get_stdin_def]
  \\ SELECT_ELIM_TAC
  \\ simp[FORALL_PROD,EXISTS_PROD, SF SFY_ss]
  \\ imp_res_tac stdin_11 \\ rw[]
  \\ imp_res_tac stdin_get_file_content \\ gvs []
  \\ xlet_auto >- (xsimpl \\ fs[INSTREAM_stdin, STD_streams_get_mode])
  \\ rename1 ‘DROP pos inp’
  \\ ‘HOL_STRING_TYPE (DROP pos inp) sv’
    by gs [HOL_STRING_TYPE_def]
  \\ xlet_auto >- xsimpl
  \\ Cases_on ‘run_main (DROP pos inp)’ \\ gs [SUM_TYPE_def] \\ xmatch
  >- (
    xlet_auto >- xsimpl
    \\ xapp_spec output_stderr_spec
    \\ xsimpl
    \\ first_assum (irule_at Any)
    \\ qexists_tac ‘fastForwardFD fs 0’
    \\ xsimpl)
  \\ rename1 ‘HOL_STRING_TYPE ys vs’
  \\ ‘STRING_TYPE (implode ys) vs’
    by gs [HOL_STRING_TYPE_def]
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ xsimpl
  \\ first_assum (irule_at Any)
  \\ qexists_tac ‘fastForwardFD fs 0’
  \\ xsimpl
QED

Theorem main_whole_prog_spec:
   whole_prog_spec main_v cl fs NONE
    ((=) (caml_parse (get_stdin fs) fs))
Proof
  simp[whole_prog_spec_def,UNCURRY]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac`fs1`
  \\ reverse conj_tac >- (
    gs [Abbr ‘fs1’, caml_parse_def]
    \\ CASE_TAC \\ gs []
    \\ rw [GSYM fastForwardFD_with_numchars,
           GSYM add_stdo_with_numchars, with_same_numchars])
  \\ simp [SEP_CLAUSES]
  \\ match_mp_tac(MP_CANON(MATCH_MP app_wgframe main_spec))
  \\ xsimpl
QED

val (semantics_thm,prog_tm) =
  whole_prog_thm (get_ml_prog_state()) "main" main_whole_prog_spec;

val caml_parse_prog_def = Define`caml_parse_prog = ^prog_tm`;

val semantics_caml_parse_prog =
  semantics_thm
  |> PURE_ONCE_REWRITE_RULE[GSYM caml_parse_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  |> curry save_thm "semantics_caml_parse_prog";

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory();

