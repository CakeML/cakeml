(*
  Common translation for lpr and ramsey

  This translates all of the LPR parsing machinery
*)
open preamble basis lprTheory parsingTheory;

val _ = new_theory "lpr_commonProg"

val _ = translation_extends"basisProg";

(* Pure translation of LPR checker *)
val _ = register_type``:lprstep``;
val _ = register_type``:'a spt``;

val _ = translate mk_BS_def;
val _ = translate mk_BN_def;
val _ = translate delete_def;
val _ = translate lookup_def;
val _ = translate lrnext_def;
val _ = translate foldi_def;
val _ = translate toAList_def;
val _ = translate insert_def;

val _ = translate (delete_literals_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO]);
val _ = translate is_AT_def;

val _ = translate (check_overlap_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO]);
val _ = translate flip_def;
val _ = translate overlap_assignment_def;
val _ = translate check_RAT_def;
(* val _ = translate guard_def; *)
val _ = translate check_PR_def;
val _ = translate is_PR_def;

val _ = translate check_lpr_step_def;
val _ = translate (is_unsat_def |> SIMP_RULE (srw_ss()) [LET_DEF,MEMBER_INTRO]);

val _ = translate blanks_def;
val _ = translate parse_until_zero_def;
val _ = translate parse_until_nn_def;

val parse_until_nn_side_def = theorem "parse_until_nn_side_def"

val parse_until_nn_side = Q.prove(`
  !x y. parse_until_nn_side x y ⇔ T`,
  Induct>>
  simp[parse_until_nn_def,Once parse_until_nn_side_def]>>
  rw[]>>fs[]>>
  intLib.ARITH_TAC) |> update_precondition

val _ = translate parse_until_k_def;
val _ = translate parse_clause_witness_def;

val _ = translate parse_PR_hint_def;
val _ = translate lit_from_int_def;

val lit_from_int_side_def = fetch "-" "lit_from_int_side_def"

val lit_from_int_side = Q.prove(`
  !x. lit_from_int_side x ⇔ T`,
  rw[lit_from_int_side_def]>>
  intLib.ARITH_TAC) |> update_precondition

val _ = translate parse_lprstep_def;

val parse_and_run_def = Define`
  parse_and_run fml l =
  (* let _ = empty_ffi l in *)
  case parse_lprstep (tokens blanks l) of
    NONE => NONE
  | SOME lpr =>
    check_lpr_step lpr fml`

val _ = translate parse_and_run_def;

val notfound_string_def = Define`
  notfound_string f = concat[strlit"cake_lpr: ";f;strlit": No such file or directory\n"]`;

val r = translate notfound_string_def;

val noparse_string_def = Define`
  noparse_string f s = concat[strlit"cake_lpr: ";f;strlit": Unable to parse in format:"; s;strlit"\n"]`;

val r = translate noparse_string_def;

val nocheck_string_def = Define`
  nocheck_string = strlit "cake_lpr: Checking failed."`;

val r = translate nocheck_string_def;

val check_unsat'' = process_topdecs `
  fun check_unsat'' fd fml =
    case TextIO.inputLine fd of
      None => (Some fml)
    | Some l =>
    case parse_and_run fml l of
      None => (TextIO.output TextIO.stdErr nocheck_string;None)
    | Some fml' => check_unsat'' fd fml'` |> append_prog;

val check_unsat''_def = Define`
  (check_unsat'' fd fml fs [] =
    STDIO (fastForwardFD fs fd)) ∧
  (check_unsat'' fd fml fs (ln::ls) =
   case parse_and_run fml ln of
    NONE =>
      STDIO (add_stderr (lineForwardFD fs fd) nocheck_string)
   | SOME fml' =>
      check_unsat'' fd fml' (lineForwardFD fs fd) ls)`

val parse_and_run_file_def = Define`
  (parse_and_run_file [] fml = SOME fml) ∧
  (parse_and_run_file (x::xs) fml =
    case parse_and_run fml x of
      NONE => NONE
    | SOME fml' => parse_and_run_file xs fml')`

(* parse and run just divides up the lpr file slightly differently *)
Theorem parse_and_run_file_eq:
  ∀ls fml.
  parse_and_run_file ls fml =
  case parse_lpr ls of
    NONE => NONE
  | SOME lpr => check_lpr lpr fml
Proof
  Induct>>fs[parse_and_run_def,parse_lpr_def,parse_and_run_file_def,check_lpr_def]>>
  rw[]>>
  every_case_tac>>fs[]>>
  simp[check_lpr_def]
QED

Theorem check_unsat''_eq:
∀ls fd fml fs.
∃n.
  check_unsat'' fd fml fs ls =
  case parse_and_run_file ls fml of
   NONE => STDIO (add_stderr (forwardFD fs fd n) nocheck_string)
 | SOME fml' =>
   STDIO (fastForwardFD fs fd)
Proof
  Induct>>rw[check_unsat''_def,parse_and_run_file_def]>>
  TOP_CASE_TAC>>fs[]
  >-
    metis_tac[lineForwardFD_forwardFD]>>
  first_x_assum(qspecl_then[`fd`,`x`,`lineForwardFD fs fd`] strip_assume_tac)>>
  simp[]>>
  TOP_CASE_TAC>>fs[]>>
  qspecl_then [`fs`,`fd`] strip_assume_tac lineForwardFD_forwardFD>>
  simp[forwardFD_o]>>
  metis_tac[]
QED

Theorem linesFD_cons:
  lineFD fs fd = SOME x ⇒
  linesFD fs fd = x::linesFD (lineForwardFD fs fd) fd
Proof
  Cases_on`linesFD fs fd`>>
  fs[linesFD_nil_lineFD_NONE]>>
  drule linesFD_cons_imp>>
  fs[]
QED

Theorem check_unsat''_spec:
  !fs fd fd_v fml fml_v.
  INSTREAM fd fd_v ∧
  IS_SOME (get_file_content fs fd) ∧ get_mode fs fd = SOME ReadMode ∧
  (SPTREE_SPT_TYPE (LIST_TYPE INT)) fml fml_v
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat''" (get_ml_prog_state()))
    [fd_v; fml_v]
    (STDIO fs)
    (POSTv res.
      check_unsat'' fd fml fs (MAP implode (linesFD fs fd)) *
      &(OPTION_TYPE  (SPTREE_SPT_TYPE (LIST_TYPE INT))
          (parse_and_run_file (MAP implode (linesFD fs fd)) fml) res))
Proof
  ntac 2 strip_tac >>
  completeInduct_on `LENGTH (linesFD fs fd)` >>
  rw [] >>
  xcf "check_unsat''" (get_ml_prog_state ()) >>
  `validFD fd fs` by metis_tac[get_file_content_validFD,IS_SOME_EXISTS,PAIR] \\
  xlet_auto >- xsimpl \\
  Cases_on `lineFD fs fd` >>
  fs [OPTION_TYPE_def] >>
  xmatch
  >- (
    xcon>>xsimpl>>
    drule lineFD_NONE_lineForwardFD_fastForwardFD>> strip_tac>>
    fs[GSYM linesFD_nil_lineFD_NONE,parse_and_run_file_def,OPTION_TYPE_def,check_unsat''_def]>>
    xsimpl)>>
  xlet_auto >- xsimpl>>
  Cases_on`parse_and_run fml (implode x)`>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    drule linesFD_cons>>strip_tac>>
    pop_assum SUBST_ALL_TAC>>fs[parse_and_run_file_def,check_unsat''_def,OPTION_TYPE_def]>>
    xlet `POSTv u. STDIO (add_stderr (lineForwardFD fs fd) nocheck_string)`
    >-
      (xapp_spec output_stderr_spec>>xsimpl>>
      qexists_tac`emp`>>qexists_tac`nocheck_string`>>
      qexists_tac`lineForwardFD fs fd`>>
      xsimpl>>
      fs[fetch "-" "nocheck_string_v_thm"])
    >>
    xcon>>
    xsimpl)>>
  drule linesFD_cons>>strip_tac>>
  xapp>>
  `IS_SOME (get_file_content (lineForwardFD fs fd) fd)` by
    fs[IS_SOME_get_file_content_lineForwardFD]>>
  asm_exists_tac>>simp[]>>
  asm_exists_tac>>simp[]>>
  xsimpl>>
  rw[] >- simp[parse_and_run_file_def] >>
  simp[check_unsat''_def]>>
  xsimpl
QED

val check_unsat' = process_topdecs `
  fun check_unsat' fml fname =
  let
    val fd = TextIO.openIn fname
    val chk = check_unsat'' fd fml
    val cls = TextIO.closeIn fd;
  in
    case chk of
      None => ()
    | Some fml' =>
      if is_unsat fml' then
        TextIO.print "UNSATISFIABLE\n"
      else
        TextIO.output TextIO.stdErr nocheck_string
  end
  handle TextIO.BadFileName =>
  TextIO.output TextIO.stdErr (notfound_string fname)` |> append_prog;

(* TODO: COPIED from readerProg, should be moved *)
Theorem fastForwardFD_ADELKEY_same[simp]:
   forwardFD fs fd n with infds updated_by ADELKEY fd =
   fs with infds updated_by ADELKEY fd
Proof
  fs [forwardFD_def, IO_fs_component_equality]
QED

(* TODO: COPIED from readerProg, should be moved *)
Theorem validFileFD_forwardFD:
   validFileFD fd (forwardFD fs x y).infds <=> validFileFD fd fs.infds
Proof
  rw [forwardFD_def, validFileFD_def, AFUPDKEY_ALOOKUP]
  \\ PURE_TOP_CASE_TAC \\ fs []
  \\ rename1 `_ = SOME xx` \\ PairCases_on `xx` \\ rw []
QED

Theorem check_unsat'_spec:
  (SPTREE_SPT_TYPE (LIST_TYPE INT)) fml fmlv ∧
  FILENAME f fv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat'"(get_ml_prog_state()))
  [fmlv; fv]
  (STDIO fs)
  (POSTv uv.
  &UNIT_TYPE () uv *
  STDIO (
    if inFS_fname fs f then
      (case parse_lpr (all_lines fs f) of
       SOME lpr =>
         if check_lpr_unsat lpr fml then
           add_stdout fs (strlit "UNSATISFIABLE\n")
         else
           add_stderr fs nocheck_string
      | NONE => add_stderr fs nocheck_string)
    else
     add_stderr fs (notfound_string f)))
Proof
  xcf"check_unsat'"(get_ml_prog_state())
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def] \\ xpull)
  \\ reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[]) >>
  reverse IF_CASES_TAC
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs f) *
      STDIO fs`
    >-
      (xlet_auto_spec (SOME openIn_STDIO_spec) \\ xsimpl)
    >>
      fs[BadFileName_exn_def]>>
      xcases>>rw[]>>
      xlet_auto>>xsimpl>>
      xapp_spec output_stderr_spec  >> xsimpl)
  >>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval` \\ xsimpl >>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec (SOME openIn_STDIO_spec) \\ xsimpl >>
  (* bunch of useful stuff to know about f *)
  drule ALOOKUP_inFS_fname_openFileFS_nextFD>>
  disch_then drule>>
  fs[inFS_fname_def]>>
  disch_then(qspecl_then [`0`,`ReadMode`] mp_tac)>>fs[]>>
  impl_tac >-
    (match_mp_tac nextFD_leX>>
    fs[])>>
  strip_tac>>
  `inFS_fname fs f ∧ nextFD fs ≤ fs.maxFD` by
    (conj_tac >-
      fs[inFS_fname_def]>>
    match_mp_tac nextFD_leX>> fs[])>>
  imp_res_tac STD_streams_nextFD>>
  xlet_auto >-
    (rw[]
    >- (
      match_mp_tac IS_SOME_get_file_content_openFileFS_nextFD>>
      fs[inFS_fname_def]>>
      match_mp_tac nextFD_leX>>
      fs[]) >>
    simp[get_mode_def])>>
  qmatch_goalsub_abbrev_tac`check_unsat'' a _ b c`>>
  qspecl_then [`c`,`a`,`fml`,`b`] strip_assume_tac check_unsat''_eq>>
  simp[]>>
  unabbrev_all_tac>>
  qmatch_asmsub_abbrev_tac`parse_and_run_file ls fml`>>
  `ls = all_lines fs f` by
    (simp[Abbr`ls`]>>
    drule linesFD_openFileFS_nextFD>>
    rpt (disch_then drule)>>
    disch_then (qspec_then`ReadMode` assume_tac)>>
    simp[MAP_MAP_o,o_DEF])>>
  `openFileFS f fs ReadMode 0 with infds updated_by ADELKEY (nextFD fs) = fs` by
    metis_tac[openFileFS_ADELKEY_nextFD]>>
  TOP_CASE_TAC>>fs[]
  >- (
    xlet_auto_spec (SOME closeIn_STDIO_spec)>>xsimpl
    >-
      (rw[]>>simp[validFileFD_forwardFD]>>
      simp[validFileFD_def])
    >>
    xmatch>>fs[OPTION_TYPE_def]>>
    reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
    conj_tac >- (EVAL_TAC \\ simp [] \\ EVAL_TAC)>>
    xcon>> xsimpl>>
    fs[parse_and_run_file_eq]>>
    TOP_CASE_TAC>>fs[]
    >-
      (qmatch_goalsub_abbrev_tac`STDIO a ==>> STDIO b * GC`>>
      qsuff_tac`a=b` >- xsimpl>>
      unabbrev_all_tac>>
      qmatch_goalsub_abbrev_tac`add_stderr fs' _ with infds updated_by _`>>
      `2 ≠ nextFD fs` by fs []>>
      drule (GEN_ALL add_stdo_ADELKEY)>>
      disch_then
        (qspecl_then [`nocheck_string`,`"stderr"`,`fs'`] sym_sub_tac)>>
      simp[Abbr`fs'`])
    >>
      rfs[]>>fs[]>>
      simp[check_lpr_unsat_def]>>
      qmatch_goalsub_abbrev_tac`STDIO a ==>> STDIO b * GC`>>
      qsuff_tac`a=b` >- xsimpl>>
      unabbrev_all_tac>>
      qmatch_goalsub_abbrev_tac`add_stderr fs' _ with infds updated_by _`>>
      `2 ≠ nextFD fs` by fs []>>
      drule (GEN_ALL add_stdo_ADELKEY)>>
      disch_then
        (qspecl_then [`nocheck_string`,`"stderr"`,`fs'`] sym_sub_tac)>>
      simp[Abbr`fs'`])
  >>
    (* TODO: why does xlet_auto find a weird instance here?? *)
    xlet`
      (POSTv u.
       STDIO
         ((fastForwardFD (openFileFS f fs ReadMode 0) (nextFD fs))
           with infds updated_by ADELKEY (nextFD fs)) *
       &(UNIT_TYPE () u))`
    >-
      (xapp_spec closeIn_STDIO_spec>>xsimpl>>
      qmatch_goalsub_abbrev_tac`STDIO fs'`>>
      qexists_tac`emp`>>qexists_tac`fs'`>>
      qexists_tac`nextFD fs`>>simp[Abbr`fs'`]>>xsimpl>>
      simp[validFileFD_def])
    >>
    fs[parse_and_run_file_eq]>>
    TOP_CASE_TAC>>rfs[]>>fs[]>>
    xmatch>>fs[OPTION_TYPE_def]>>
    reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
    reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
    xlet_auto
    >-
      (xsimpl>>simp[EqualityType_NUM_BOOL])
    >>
    xif>>fs[check_lpr_unsat_def]
    >-
      (xapp_spec print_spec >> xsimpl)
    >>
      xapp_spec output_stderr_spec \\ xsimpl >>
      fs[fetch "-" "nocheck_string_v_thm"]
QED

Theorem abs_compute:
  ABS (i:int) = if i < 0 then -i else i
Proof
  intLib.ARITH_TAC
QED

val _ = translate abs_compute;

val _ = translate max_lit_def;
val _ = translate print_line_def;

val _ = translate spt_center_def;
val _ = translate spt_centers_def;
val _ = translate spt_right_def;
val _ = translate spt_left_def;
val _ = translate aux_alist_def;
val _ = translate toSortedAList_def;

val _ = translate print_dimacs_def;

val _ = export_theory();
