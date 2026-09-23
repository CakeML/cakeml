(*
  Multi-objective OPB frontend: parse an OPB file with several objectives,
  then either print it back or check a PB proof of its nondominated set
*)
Theory npbc_mo_fullProg
Ancestors
  basis_ffi pb_parse pbc_mo pbc_normalise npbc_parseProg npbc_mo_arrayProg
Libs
  preamble basis

val _ = translation_extends"npbc_mo_arrayProg";

(* Translation for parsing a multi-objective OPB file *)
val r = translate nocomment_line_def;

val r = translate parse_constraint_def;
val r = translate parse_annot_def;
val r = translate parse_annot_constraint_def;
val r = translate parse_constraints_def;

val r = translate parse_obj_def;
val r = translate parse_objs_maybe_def;
val r = translate parse_mo_pbf_toks_def;

Definition noparse_string_def:
  noparse_string f s = concat[«c Input file: »;f;« unable to parse in format: »; s;«\n»]
End

val r = translate noparse_string_def;

Quote add_cakeml:
  fun parse_mo_pbf_full f =
  (case TextIO.inputAllTokensFile #"\n" f blanks tokenize of
    None => Inl (notfound_string f)
  | Some lines =>
  (case parse_mo_pbf_toks lines of
    None => Inl (noparse_string f "OPB")
  | Some res => Inr res
  ))
End

val inputAllTokensFile_spec_specialize =
  inputAllTokensFile_spec
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> REWRITE_RULE [blanks_v_thm,tokenize_v_thm] ;

Definition get_mo_fml_def:
  get_mo_fml fs f =
  if inFS_fname fs f then
    parse_mo_pbf (all_lines_file fs f)
  else NONE
End

Theorem parse_mo_pbf_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_mo_pbf_full"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. (SUM_TYPE STRING_TYPE mo_prob_TYPE)
    (case get_mo_fml fs f of
      NONE => INL err
    | SOME res => INR res) v) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_mo_pbf_full"(get_ml_prog_state())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse (Cases_on`consistentFS fs`) >- (
    fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def]
    \\ xpull \\ metis_tac[]) >>
  xlet`(POSTv sv. &OPTION_TYPE (LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
            (if inFS_fname fs f then
               SOME(MAP (MAP tokenize o tokens blanks) (all_lines_file fs f))
             else NONE) sv * STDIO fs)`
  >- (
    xapp_spec inputAllTokensFile_spec_specialize >>
    xsimpl>>
    simp[pb_parseTheory.blanks_def]>>
    fs[FILENAME_def,validArg_def,blanks_v_thm]>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    qexists_tac`emp`>>xsimpl)>>
  simp[get_mo_fml_def]>>
  IF_CASES_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    xlet_autop>>
    `toks = (MAP tokenize ∘ tokens blanks)` by
      metis_tac[toks_def,ETA_AX,o_DEF]>>
    rw[parse_mo_pbf_def]>>
    qmatch_goalsub_abbrev_tac`option_CASE AAA`>>
    Cases_on`AAA`>>
    fs[OPTION_TYPE_def]
    >- (
      xmatch >>
      xlet_autop>>
      xcon>>xsimpl>>
      simp[SUM_TYPE_def]>>metis_tac[])>>
    xmatch>>
    xcon>>
    xsimpl>>
    simp[SUM_TYPE_def])>>
  xlet_autop>>
  xcon>>xsimpl>>
  simp[SUM_TYPE_def]>>metis_tac[]
QED

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 out ⇔
  case get_mo_fml fs f1 of
    SOME mprob => out = concat (print_mo_prob mprob)
  | NONE => out = «»
End

Quote add_cakeml:
  fun check_unsat_2 f1 =
  case parse_mo_pbf_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr mprob =>
    TextIO.print_list (print_mo_prob mprob)
End

Theorem check_unsat_2_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_2"(get_ml_prog_state()))
    [f1v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(check_unsat_2_sem fs f1 out))
Proof
  rw[check_unsat_2_sem_def]>>
  xcf "check_unsat_2" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  xlet_autop>>
  pop_assum mp_tac>>
  TOP_CASE_TAC
  >- (
    simp[SUM_TYPE_def]>>rw[]>>
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`err`>>xsimpl>>rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  simp[SUM_TYPE_def]>>rw[]>>
  xmatch>>
  xlet_autop>>
  xapp_spec print_list_spec>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`«»`>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl
QED

Definition check_unsat_3_sem_def:
  check_unsat_3_sem fs ord f1 out ⇔
  (out ≠ «» ⇒
  ∃objs fml vs.
    get_mo_fml fs f1 = SOME (objs,fml) ∧
    out = print_front_str ord vs ∧
    is_front ord vs (pbc_mo$nondom_set ord (set fml) objs))
End

Quote add_cakeml:
  fun check_unsat_3 ord f1 f2 =
  case parse_mo_pbf_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr mprob =>
    (case map_front_to_string ord (check_unsat_mo_top_norm ord mprob f2) of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr s => TextIO.print s)
End

Theorem check_unsat_3_spec:
  PBC_MO_MO_ORD_TYPE ord ordv ∧
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  STRING_TYPE f2 f2v ∧ validArg f2 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_3"(get_ml_prog_state()))
    [ordv; f1v; f2v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(check_unsat_3_sem fs ord f1 out))
Proof
  rw[check_unsat_3_sem_def]>>
  xcf "check_unsat_3" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  xlet_autop>>
  pop_assum mp_tac>>
  TOP_CASE_TAC
  >- (
    simp[SUM_TYPE_def]>>rw[]>>
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`err`>>xsimpl>>rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  simp[SUM_TYPE_def]>>rw[]>>
  xmatch>>
  drule check_unsat_mo_top_norm_spec>>
  strip_tac>>
  xlet_auto
  >- (
    xsimpl>>
    fs[validArg_def]>>
    metis_tac[])>>
  xlet_autop>>
  every_case_tac>>gvs[SUM_TYPE_def]
  >- (
    fs[map_front_to_string_def,SUM_TYPE_def]>>
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`«»`>>
    rename1`add_stderr _ err`>>
    qexists_tac`err`>>xsimpl>>rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  fs[map_front_to_string_def,SUM_TYPE_def]>>
  xmatch>>
  xapp>>xsimpl>>
  asm_exists_tac>>simp[]>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  rename1`vomap_TYPE (print_front_str ord vs) _`>>
  qexists_tac`print_front_str ord vs`>>simp[]>>
  qexists_tac`«»`>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl>>
  rw[]>>
  rename1`get_mo_fml _ _ = SOME mprob`>>
  qexists_tac`FST mprob`>>qexists_tac`SND mprob`>>qexists_tac`vs`>>
  simp[]
QED

Definition usage_string_def:
  usage_string = «Usage: cake_pb_mo <ordering: pareto> <OPB file> <optional: PB proof file>\n»
End

val r = translate usage_string_def;

Quote add_cakeml:
  fun main u =
  case CommandLine.arguments () of
    [ords,f1] =>
      (case parse_mo_ord ords of
        None => TextIO.output TextIO.stdErr (mk_usage_string usage_string)
      | Some ord => check_unsat_2 f1)
  | [ords,f1,f2] =>
      (case parse_mo_ord ords of
        None => TextIO.output TextIO.stdErr (mk_usage_string usage_string)
      | Some ord => check_unsat_3 ord f1 f2)
  | _ => TextIO.output TextIO.stdErr (mk_usage_string usage_string)
End

Definition main_sem_def:
  main_sem fs cl out =
  if LENGTH cl = 3 then
    (case parse_mo_ord (EL 1 cl) of
      NONE => out = «»
    | SOME ord => check_unsat_2_sem fs (EL 2 cl) out)
  else if LENGTH cl = 4 then
    (case parse_mo_ord (EL 1 cl) of
      NONE => out = «»
    | SOME ord => check_unsat_3_sem fs ord (EL 2 cl) out)
  else out = «»
End

Theorem STDIO_refl:
  STDIO A ==>>
  STDIO A * GC
Proof
  xsimpl
QED

Theorem main_spec:
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"main"(get_ml_prog_state()))
    [Conv NONE []]
    (COMMANDLINE cl * STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    COMMANDLINE cl *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(main_sem fs cl out))
Proof
  rw[main_sem_def]>>
  xcf"main"(get_ml_prog_state())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)>>
  rpt xlet_autop >>
  Cases_on `cl` >- fs[wfcl_def] >>
  rename1`wfcl (_::args)`>>
  Cases_on`args`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    assume_tac (theorem "usage_string_v_thm")>>
    xlet_autop>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    rename1`COMMANDLINE cl`>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `mk_usage_string usage_string` >>
    simp [] >>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    metis_tac[STDIO_refl])>>
  rename1`wfcl (_::ords::args)`>>
  Cases_on`args`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    assume_tac (theorem "usage_string_v_thm")>>
    xlet_autop>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    rename1`COMMANDLINE cl`>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `mk_usage_string usage_string` >>
    simp [] >>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    metis_tac[STDIO_refl])>>
  rename1`wfcl (_::ords::f1::args)`>>
  Cases_on`args`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    Cases_on`parse_mo_ord ords`>>fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      assume_tac (theorem "usage_string_v_thm")>>
      xlet_autop>>
      xapp_spec output_stderr_spec \\ xsimpl>>
      rename1`COMMANDLINE cl`>>
      qexists_tac`COMMANDLINE cl`>>xsimpl>>
      qexists_tac `mk_usage_string usage_string` >>
      simp [] >>
      qexists_tac`fs`>>xsimpl>>
      rw[]>>
      fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
      metis_tac[STDIO_refl])>>
    xapp>>rw[]>>
    rpt(first_x_assum (irule_at Any)>>xsimpl)>>
    fs[wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>>
  rename1`wfcl (_::ords::f1::f2::args)`>>
  Cases_on`args`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    Cases_on`parse_mo_ord ords`>>fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      assume_tac (theorem "usage_string_v_thm")>>
      xlet_autop>>
      xapp_spec output_stderr_spec \\ xsimpl>>
      rename1`COMMANDLINE cl`>>
      qexists_tac`COMMANDLINE cl`>>xsimpl>>
      qexists_tac `mk_usage_string usage_string` >>
      simp [] >>
      qexists_tac`fs`>>xsimpl>>
      rw[]>>
      fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
      metis_tac[STDIO_refl])>>
    xapp>>rw[]>>
    rpt(first_x_assum (irule_at Any)>>xsimpl)>>
    fs[wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>>
  xmatch>>
  assume_tac (theorem "usage_string_v_thm")>>
  xlet_autop>>
  xapp_spec output_stderr_spec \\ xsimpl>>
  rename1`COMMANDLINE cl`>>
  qexists_tac`COMMANDLINE cl`>>xsimpl>>
  qexists_tac `mk_usage_string usage_string` >>
  simp [] >>
  qexists_tac`fs`>>xsimpl>>
  rw[]>>
  fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  metis_tac[STDIO_refl]
QED

Theorem main_whole_prog_spec2:
   hasFreeFD fs ⇒
   whole_prog_spec2 main_v cl fs NONE
     (λfs'. ∃out err.
        fs' = add_stdout (add_stderr fs err) out ∧
        main_sem fs cl out)
Proof
  rw[basis_ffiTheory.whole_prog_spec2_def]
  \\ match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH main_spec))))
  \\ xsimpl
  \\ rw[PULL_EXISTS]
  \\ qexists_tac`add_stdout (add_stderr fs x') x`
  \\ xsimpl
  \\ qexists_tac`x`
  \\ qexists_tac`x'`
  \\ xsimpl
  \\ simp[GSYM add_stdo_with_numchars,with_same_numchars]
QED

Theorem main_semantics =
  prove_sem_thm "main"
                "main_prog"
                main_whole_prog_spec2;
