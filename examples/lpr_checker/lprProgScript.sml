(*
  lpr program example: takes two file names from command line
  cake_lpr foo.cnf foo.lpr
*)
open preamble basis parsingTheory lpr_commonProgTheory;

val _ = new_theory "lprProg"

val _ = translation_extends"lpr_commonProg";

(* Pure translation of parsing things *)
val _ = translate parse_header_line_def;

val parse_header_line_side = Q.prove(`
   ∀x. parse_header_line_side x= T`,
  rw[definition"parse_header_line_side_def"]>>
  intLib.ARITH_TAC)
  |> update_precondition;

val _ = translate parse_clause_aux_def;
val _ = translate parse_clause_def;

(* NOTE: inefficient-ish version that reads all lines at once *)
val _ = translate parsingTheory.build_fml_def;
val _ = translate nocomment_line_def;
val _ = translate parse_dimacs_toks_def;
val _ = translate parse_dimacs_def;

val usage_string_def = Define`
  usage_string = strlit"Usage: cake_lpr <DIMCAS formula file> <Optional: LPR proof file for proof checking>\n"`;

val r = translate usage_string_def;

val _ = (append_prog o process_topdecs) `
  fun check_unsat u =
    case CommandLine.arguments () of
        (f1::f2::[]) =>
          (case TextIO.inputLinesFrom f1 of
            None => TextIO.output TextIO.stdErr (notfound_string f1)
          | Some lines1 =>
            (case parse_dimacs lines1 of
              None => TextIO.output TextIO.stdErr (noparse_string f1 "DIMACS")
            | Some (mv,fml) =>
              check_unsat' fml f2))
      |  (f1::[]) =>
          (case TextIO.inputLinesFrom f1 of
            None => TextIO.output TextIO.stdErr (notfound_string f1)
          | Some lines1 =>
            (case parse_dimacs lines1 of
              None => TextIO.output TextIO.stdErr (noparse_string f1 "DIMACS")
            | Some (mv,fml) => TextIO.print_list (print_dimacs fml)))
      | _ => TextIO.output TextIO.stdErr usage_string`;

val check_unsat_sem_def = Define`
  check_unsat_sem cl fs =
  if (LENGTH cl = 3) then
    if inFS_fname fs (EL 1 cl) then
      case parse_dimacs (all_lines fs (EL 1 cl)) of
        SOME (mv,fml) =>
        if inFS_fname fs (EL 2 cl) then
          (case parse_lpr (all_lines fs (EL 2 cl)) of
            SOME lpr =>
              if check_lpr_unsat lpr fml then
                add_stdout fs (strlit "s UNSATISFIABLE\n")
              else
                add_stderr fs nocheck_string
           | NONE => add_stderr fs nocheck_string)
         else
           add_stderr fs (notfound_string (EL 2 cl))
       | NONE => add_stderr fs (noparse_string (EL 1 cl) (strlit "DIMACS"))
     else
       add_stderr fs (notfound_string (EL 1 cl))
  else if (LENGTH cl = 2) then
    if inFS_fname fs (EL 1 cl) then
      case parse_dimacs (all_lines fs (EL 1 cl)) of
        SOME (mv,fml) =>
          add_stdout fs (concat (print_dimacs fml ))
      | NONE => add_stderr fs (noparse_string (EL 1 cl) (strlit "DIMACS"))
    else
       add_stderr fs (notfound_string (EL 1 cl))
  else
    add_stderr fs usage_string`;

Theorem check_unsat_spec:
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat"(get_ml_prog_state()))
    [Conv NONE []]
    (COMMANDLINE cl * STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    COMMANDLINE cl * STDIO (check_unsat_sem cl fs))
Proof
  xcf"check_unsat"(get_ml_prog_state())>>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse (Cases_on`consistentFS fs`) >-
    (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[]) >>
  xlet_auto >- (xcon >> xsimpl)>>
  xlet_auto >- (qexists_tac`STDIO fs` >> xsimpl)>>
  Cases_on `cl` >- fs[wfcl_def] >>
  Cases_on `t` \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (
    simp[check_unsat_sem_def]>>
    xmatch \\ xapp_spec output_stderr_spec \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `usage_string` \\ simp [theorem "usage_string_v_thm"]
    \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs` \\ xsimpl) >>
  Cases_on `t'` \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (
    (* Only 1 argument on command line: prints the parsed formula *)
    xmatch>>
    xlet_auto_spec(SOME inputLinesFrom_spec) >-
      (xsimpl>>fs[wfcl_def,validArg_def])>>
    simp[check_unsat_sem_def]>>
    reverse IF_CASES_TAC >>
    xmatch >> fs[]
    >- (
      fs[OPTION_TYPE_def]>>
      reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
      xlet_auto >- xsimpl>>
      xapp_spec output_stderr_spec \\ xsimpl>>
      asm_exists_tac>>xsimpl>>
      qexists_tac`COMMANDLINE [h;h']`>> qexists_tac`fs`>>
      xsimpl)>>
    fs[OPTION_TYPE_def]>>
    reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
    reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
    xlet_auto >- xsimpl>>
    Cases_on `parse_dimacs (all_lines fs h')`
    >- (
      xmatch >>
      fs[OPTION_TYPE_def]>>
      reverse conj_tac >-
        (strip_tac >> EVAL_TAC)>>
      xlet_auto >- xsimpl>>
      xapp_spec output_stderr_spec  >> xsimpl>>
      asm_exists_tac>>xsimpl>>
      qexists_tac`COMMANDLINE [h;h']`>> qexists_tac`fs`>>
      xsimpl)
    >>
    Cases_on`x`>>
    fs[OPTION_TYPE_def,PAIR_TYPE_def]>>
    xmatch>>fs[]>>
    xlet_auto>- xsimpl>>
    xapp_spec print_list_spec>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`COMMANDLINE [h;h']`>> qexists_tac`fs`>>
    xsimpl)>>
  reverse (Cases_on`t`) \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (
    simp[check_unsat_sem_def]>>
    xmatch \\ xapp_spec output_stderr_spec \\ xsimpl
     \\ CONV_TAC SWAP_EXISTS_CONV
     \\ qexists_tac `usage_string` \\ simp [theorem "usage_string_v_thm"]
     \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs` \\ xsimpl) >>
  (* 2 arguments on command line *)
  xmatch>>
  xlet_auto_spec(SOME inputLinesFrom_spec) >-
    (xsimpl>>fs[wfcl_def,validArg_def])>>
  simp[check_unsat_sem_def]>>
  reverse IF_CASES_TAC >>
  xmatch >> fs[]
  >- (
    fs[OPTION_TYPE_def]>>
    reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
    xlet_auto >- xsimpl>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`COMMANDLINE [h;h';h'']`>> qexists_tac`fs`>>
    xsimpl)>>
  fs[OPTION_TYPE_def]>>
  reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
  reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
  xlet_auto >- xsimpl>>
  Cases_on `parse_dimacs (all_lines fs h')`
  >- (
    xmatch >>
    fs[OPTION_TYPE_def]>>
    reverse conj_tac >-
      (strip_tac >> EVAL_TAC)>>
    xlet_auto >- xsimpl>>
    xapp_spec output_stderr_spec  >> xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`COMMANDLINE [h;h';h'']`>> qexists_tac`fs`>>
    xsimpl)>>
  Cases_on`x`>>
  fs[OPTION_TYPE_def,PAIR_TYPE_def]>>
  xmatch >>
  xapp_spec check_unsat'_spec>>
  CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs` >>
  xsimpl>>
  qexists_tac`r`>>
  qexists_tac`h''`>>
  fs[FILENAME_def,validArg_def,check_unsat_sem_def,wfcl_def] >>
  rw[]>>simp[]>>
  xsimpl
QED

val st = get_ml_prog_state();

Theorem check_unsat_whole_prog_spec:
   hasFreeFD fs ⇒
   whole_prog_spec ^(fetch_v"check_unsat"st) cl fs NONE ((=) (check_unsat_sem cl fs))
Proof
  rw[whole_prog_spec_def]
  \\ qexists_tac`check_unsat_sem cl fs`
  \\ reverse conj_tac
  >- (
    rw[check_unsat_sem_def]>>
    every_case_tac>>simp[GSYM add_stdo_with_numchars,with_same_numchars])
  \\ match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH check_unsat_spec))))
  \\ xsimpl
QED

val name = "check_unsat"
val (sem_thm,prog_tm) = whole_prog_thm st name (UNDISCH check_unsat_whole_prog_spec)
val check_unsat_prog_def = Define`check_unsat_prog = ^prog_tm`;

val check_unsat_semantics = save_thm("check_unsat_semantics",
  sem_thm |> REWRITE_RULE[GSYM check_unsat_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[GSYM CONJ_ASSOC,AND_IMP_INTRO]);

val _ = export_theory();
