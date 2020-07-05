(*
  Ramsey number 4 example:
  cake_ramsey foo.lpr
*)
open preamble basis parsingTheory ramseyTheory lpr_commonProgTheory;

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "ramseyProg"

val _ = translation_extends"lpr_commonProg";

val usage_string_def = Define`
  usage_string = strlit"Usage: cake_ramsey <Optional: LPR proof file for proof checking>\n"`;

val r = translate usage_string_def;

val res = translate choose_def;
(* val res = translate index_edge_def; *)
val res = translate clique_edges_def;
val res = translate build_fml_def;
val res = translate (COUNT_LIST_GENLIST);
val res = translate transpose_def;
val res = translate miscTheory.enumerate_def;
val res = translate encoder_def;
val res = translate ramsey_lpr_def;

val _ = (append_prog o process_topdecs) `
  fun check_ramsey u =
    case CommandLine.arguments () of
        (f1::[]) =>
          check_unsat' (ramsey_lpr 4 18) f1
      |  [] =>
         TextIO.print_list (print_dimacs (ramsey_lpr 4 18))
      | _ => TextIO.output TextIO.stdErr usage_string`;

val check_ramsey_sem_def = Define`
  check_ramsey_sem cl fs =
  if (LENGTH cl = 2) then
    if inFS_fname fs (EL 1 cl) then
      (case parse_lpr (all_lines fs (EL 1 cl)) of
        SOME lpr =>
          if check_lpr_unsat lpr (ramsey_lpr 4 18) then
            add_stdout fs (strlit "s VERIFIED UNSAT\n")
          else
            add_stderr fs nocheck_string
       | NONE => add_stderr fs nocheck_string)
     else
       add_stderr fs (notfound_string (EL 1 cl))
  else if (LENGTH cl = 1) then
    add_stdout fs (concat (print_dimacs (ramsey_lpr 4 18)))
  else
    add_stderr fs usage_string`;

Theorem check_ramsey_spec:
   hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"check_ramsey"(get_ml_prog_state()))
     [Conv NONE []]
     (COMMANDLINE cl * STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv *
     COMMANDLINE cl * STDIO (check_ramsey_sem cl fs))
Proof
  xcf"check_ramsey"(get_ml_prog_state())>>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse (Cases_on`consistentFS fs`) >-
    (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[]) >>
  xlet_auto >- (xcon >> xsimpl)>>
  xlet_auto >- (qexists_tac`STDIO fs` >> xsimpl)>>
  Cases_on `cl` >- fs[wfcl_def] >>
  Cases_on `t` \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (
    simp[check_ramsey_sem_def]>>
    xmatch \\
    xlet_auto >- xsimpl>>
    xlet_auto >- xsimpl>>
    xapp_spec print_list_spec \\ xsimpl >>
    asm_exists_tac>> xsimpl>>
    qexists_tac`COMMANDLINE [h]`>>qexists_tac`fs`>>xsimpl)>>
  reverse (Cases_on`t'`) \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (
    simp[check_ramsey_sem_def]>>
    xmatch \\ xapp_spec output_stderr_spec \\ xsimpl
     \\ CONV_TAC SWAP_EXISTS_CONV
     \\ qexists_tac `usage_string` \\ simp [theorem "usage_string_v_thm"]
     \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs` \\ xsimpl) >>
  xmatch>>
  xlet_auto >- xsimpl>>
  xapp_spec check_unsat'_spec>>
  xsimpl>>
  CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs` >>
  xsimpl>>
  qexists_tac`ramsey_lpr 4 18`>>
  qexists_tac`h'`>>
  fs[FILENAME_def,validArg_def,check_ramsey_sem_def,wfcl_def] >>
  rw[]>>simp[]>>
  xsimpl
QED

val st = get_ml_prog_state();

Theorem check_ramsey_whole_prog_spec:
   hasFreeFD fs ⇒
   whole_prog_spec ^(fetch_v"check_ramsey"st) cl fs NONE ((=) (check_ramsey_sem cl fs))
Proof
  rw[whole_prog_spec_def]
  \\ qexists_tac`check_ramsey_sem cl fs`
  \\ reverse conj_tac
  >- (
    rw[check_ramsey_sem_def]>>
    every_case_tac>>simp[GSYM add_stdo_with_numchars,with_same_numchars])
  \\ match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH check_ramsey_spec))))
  \\ xsimpl
QED

val name = "check_ramsey"
val (sem_thm,prog_tm) = whole_prog_thm st name (UNDISCH check_ramsey_whole_prog_spec)
val check_ramsey_prog_def = Define`check_ramsey_prog = ^prog_tm`;

val check_ramsey_semantics = save_thm("check_ramsey_semantics",
  sem_thm |> REWRITE_RULE[GSYM check_ramsey_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[GSYM CONJ_ASSOC,AND_IMP_INTRO]);

val _ = export_theory();
