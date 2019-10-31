(*
  lrat program example: takes two file names from command line
  cml_lrat foo.cnf foo.lrat

  does stuff
*)
open preamble basis lratTheory parsingTheory;

val _ = new_theory "lratProg"

val _ = translation_extends"basisProg";

(* Pure translation of LRAT checker *)
val _ = register_type``:lratstep``;
val _ = register_type``:'a spt``;

val _ = translate mk_BS_def;
val _ = translate mk_BN_def;
val _ = translate delete_def;
val _ = translate lookup_def;
val _ = translate lrnext_def;
val _ = translate foldi_def;
val _ = translate toAList_def;
val _ = translate insert_def;
val _ = translate union_def;

val _ = translate list_delete_def;

val _ = translate insert_literal_def;
val _ = translate delete_literals_def;
val _ = translate (is_AT_def |> REWRITE_RULE [MEMBER_INTRO]);

val _ = translate has_literal_def;
val _ = translate has_neg_literal_def;
val _ = translate delete_neg_literal_def;

val _ = translate find_exists_def;
val _ = translate find_tauto_def;
val _ = translate cclause_union_def;

val _ = translate is_RAT_aux_def;
val _ = translate is_RAT_def;

(* val _ = translate (wf_clause_def |> REWRITE_RULE [MEMBER_INTRO]); *)
val _ = translate check_lrat_def;

val _ = translate (check_lrat_unsat_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO,LET_DEF]);

(* Pure translation of parsing things *)
val _ = translate blanks_def;
val _ = translate parse_header_line_def;
val _ = translate parse_clause_def;

(* NOTE: inefficient-ish version that reads all lines at once *)
val _ = translate build_fml_def;
val _ = translate parse_dimacs_def;

val _ = translate parse_until_zero_def;
val _ = translate parse_until_nn_def;

val parse_until_nn_side_def = theorem "parse_until_nn_side_def"

val parse_until_nn_side = Q.prove(`
  !x y. parse_until_nn_side x y ⇔ T`,
  Induct>>
  simp[parse_until_nn_def,Once parse_until_nn_side_def]>>
  rw[]>>fs[]>>
  intLib.ARITH_TAC) |> update_precondition

val _ = translate parse_RAT_hint_def;
val _ = translate cclause_from_list_def;
val _ = translate lit_from_int_def;

val lit_from_int_side_def = fetch "-" "lit_from_int_side_def"

val lit_from_int_side = Q.prove(`
  !x. lit_from_int_side x ⇔ T`,
  rw[lit_from_int_side_def]>>
  intLib.ARITH_TAC) |> update_precondition

val _ = translate parse_lratstep_def;

val _ = translate parse_lrat_aux_def;
val _ = translate parse_lrat_def;

val notfound_string_def = Define`
  notfound_string f = concat[strlit"cake_lrat: ";f;strlit": No such file or directory\n"]`;

val r = translate notfound_string_def;

val noparse_string_def = Define`
  noparse_string f s = concat[strlit"cake_lrat: ";f;strlit": Unable to parse in format:"; s;strlit"\n"]`;

val r = translate noparse_string_def;

val _ = process_topdecs `
  fun check_unsat' fname1 fname2 =
    case TextIO.inputLinesFrom fname1 of
      None => TextIO.output TextIO.stdErr (notfound_string fname1)
    | Some lines1 =>
    case parse_dimacs lines1 of
      None => TextIO.output TextIO.stdErr (noparse_string fname1 "DIMACS")
    | Some fml =>
    case TextIO.inputLinesFrom fname2 of
        None => TextIO.output TextIO.stdErr (notfound_string fname2)
    | Some lines2 =>
    case parse_lrat lines2 of
      None => TextIO.output TextIO.stdErr (noparse_string fname2 "LRAT")
    | Some lrat =>
      if check_lrat_unsat lrat fml then
        TextIO.print "UNSATISFIABLE"
      else
        TextIO.print "Proof checking failed."` |> append_prog;

Theorem check_unsat'_spec:
   FILENAME f1 fv1 ∧ FILENAME f2 fv2 /\
   hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"check_unsat'"(get_ml_prog_state()))
     [fv1; fv2]
     (STDIO fs)
     (POSTv uv.
       &UNIT_TYPE () uv *
       SEP_EXISTS ls.
       (&
         (if ls = strlit "UNSATISFIABLE"
         then ∃fml. parse_dimacs (all_lines fs f1) = SOME fml ∧ unsatsfiable fml
         else ls = strlit "Proof checking failed.")
        ) *
       STDIO (
         if inFS_fname fs f1 then
         if inFS_fname fs f2 then
           add_stdout fs ls
         else add_stderr fs (notfound_string f2)
         else add_stderr fs (notfound_string f1)))
Proof
  xcf"check_unsat'" (get_ml_prog_state())
  \\ xlet_auto_spec(SOME inputLinesFrom_spec)
  >- xsimpl
  \\ cheat
QED

val usage_string_def = Define`
  usage_string = strlit"Usage: cake_lrat <DIMCAS formula file> <LRAT proof file>\n"`;

val r = translate usage_string_def;

val _ = (append_prog o process_topdecs) `
  fun check_unsat u =
    case CommandLine.arguments () of
        (f1::f2::[]) => check_unsat' f1 f2
      | _ => TextIO.output TextIO.stdErr usage_string`;

val check_unsat_sem_def = Define`
  check_unsat_sem cl fs =
    if (LENGTH cl = 3) then
    if inFS_fname fs (EL 1 cl) then
    if inFS_fname fs (EL 2 cl) then
    add_stdout fs (
      strlit "TODO"
    )
    else add_stderr fs (notfound_string (EL 2 cl))
    else add_stderr fs (notfound_string (EL 1 cl))
    else add_stderr fs usage_string`;

Theorem check_unsat_spec:
   hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"check_unsat"(get_ml_prog_state()))
     [Conv NONE []]
     (STDIO fs * COMMANDLINE cl)
     (POSTv uv. &UNIT_TYPE () uv *
                STDIO (check_unsat_sem cl fs) * (COMMANDLINE cl))
Proof
  cheat
QED

val st = get_ml_prog_state();

Theorem check_unsat_whole_prog_spec:
   hasFreeFD fs ⇒
   whole_prog_spec ^(fetch_v"check_unsat"st) cl fs NONE ((=) (check_unsat_sem cl fs))
Proof
  rw[whole_prog_spec_def]
  \\ qexists_tac`check_unsat_sem cl fs`
  \\ reverse conj_tac
  >- ( rw[check_unsat_sem_def,GSYM add_stdo_with_numchars,with_same_numchars] )
  \\ simp [SEP_CLAUSES]
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
