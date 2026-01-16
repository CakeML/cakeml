(*
  Add PBF parsing and wrap around the PBP parser
*)
Theory npbc_fullProg
Ancestors
  basis_ffi pb_parse pbc_normalise npbc_parseProg
Libs
  preamble basis

val _ = translation_extends"npbc_parseProg";

(* Translation for parsing an OPB file *)
val r = translate nocomment_line_def;

val r = translate parse_op_def;
val r = translate parse_constraint_def;
val r = translate parse_annot_def;
val r = translate parse_annot_constraint_def;
val r = translate parse_constraints_def;

val r = translate parse_obj_def;
val r = translate parse_obj_maybe_def;
val r = translate parse_var_raw_def;
val r = translate parse_vars_raw_def;
val r = translate parse_pres_def;
val r = translate parse_pres_maybe_def;
val r = translate parse_obj_pres_maybe_def;
val r = translate parse_pbf_toks_def;

Definition noparse_string_def:
  noparse_string f s = concat[strlit"c Input file: ";f;strlit" unable to parse in format: "; s;strlit"\n"]
End

val r = translate noparse_string_def;

Quote add_cakeml:
  fun parse_pbf_full f =
  (case TextIO.inputAllTokensFile #"\n" f blanks tokenize of
    None => Inl (notfound_string f)
  | Some lines =>
  (case parse_pbf_toks lines of
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

Definition get_annot_fml_def:
  get_annot_fml fs f =
  if inFS_fname fs f then
    parse_pbf (all_lines_file fs f)
  else NONE
End

Theorem parse_pbf_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_pbf_full"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. (SUM_TYPE STRING_TYPE annot_prob_TYPE)
    (case get_annot_fml fs f of
      NONE => INL err
    | SOME res => INR res) v) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_pbf_full"(get_ml_prog_state())>>
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
  simp[get_annot_fml_def]>>
  IF_CASES_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    xlet_autop>>
    `toks = (MAP tokenize ∘ tokens blanks)` by
      metis_tac[toks_def,ETA_AX,o_DEF]>>
    rw[parse_pbf_def]>>
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

Definition int_inf_to_string_def:
  (int_inf_to_string NONE = strlit "INF") ∧
  (int_inf_to_string (SOME (i:int)) =
    toString i)
End

Definition concl_to_string_def:
  (concl_to_string NoConcl = strlit "s VERIFIED NO CONCLUSION\n") ∧
  (concl_to_string DSat = strlit "s VERIFIED SATISFIABLE\n") ∧
  (concl_to_string DUnsat = strlit "s VERIFIED UNSATISFIABLE\n") ∧
  (concl_to_string (OBounds lbi ubi) =
    let lbs = int_inf_to_string lbi in
    let ubs = int_inf_to_string ubi in
    strlit "s VERIFIED BOUNDS " ^ lbs ^ strlit " <= obj <= " ^ ubs ^ strlit"\n")
End

Definition get_fml_def:
  get_fml fs f =
  OPTION_MAP strip_annot_prob (get_annot_fml fs f)
End

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 out ⇔
  (out ≠ strlit"" ⇒
  ∃pres obj fml.
    get_fml fs f1 = SOME (pres,obj,fml) ∧
    ∃concl.
      out = concl_to_string concl ∧
      pbc$sem_concl (set fml) obj concl)
End

(* Ignoring output section for 2-arg version *)
Definition map_concl_to_string_def:
  (map_concl_to_string (INL s) = (INL s)) ∧
  (map_concl_to_string (INR (out,bnd,c)) = (INR (concl_to_string c)))
End

val res = translate int_inf_to_string_def;
val res = translate concl_to_string_def;
val res = translate map_concl_to_string_def;

Quote add_cakeml:
  fun check_unsat_2 f1 f2 =
  case parse_pbf_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr prob =>
    let
      val prob = strip_annot_prob prob
      val probt = default_prob in
      (case
        map_concl_to_string
          (check_unsat_top_norm False prob probt f2) of
        Inl err => TextIO.output TextIO.stdErr err
      | Inr s => TextIO.print s)
    end
End

Theorem check_unsat_2_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  STRING_TYPE f2 f2v ∧ validArg f2 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_2"(get_ml_prog_state()))
    [f1v; f2v]
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
  gvs[get_fml_def]>>
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
  `∃pres obj fml. strip_annot_prob x = (pres,obj,fml)` by metis_tac[PAIR]>>
  assume_tac default_prob_v_thm>>
  xlet`POSTv v.
    STDIO fs *
    &prob_TYPE default_prob v`
  >-
    (xvar>>xsimpl)>>
  xlet`POSTv v. STDIO fs * &BOOL F v`
  >-
    (xcon>>xsimpl)>>
  xlet`(POSTv v.
     STDIO fs *
     SEP_EXISTS res.
     &(
       SUM_TYPE STRING_TYPE
         (PAIR_TYPE PBC_OUTPUT_TYPE
           (PAIR_TYPE (OPTION_TYPE INT) PBC_CONCL_TYPE))
         res v ∧
       case res of
         INR (output,bound,concl) =>
         sem_concl (set fml) obj concl
      | INL l => T))`
  >- (
    xapp>>xsimpl>>
    fs[validArg_def]>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    simp[]>>
    qexists_tac`f2`>>simp[FILENAME_def,validArg_def]>>
    qexists_tac`emp`>>xsimpl>>
    rw[]>>
    first_x_assum (irule_at Any)>>
    simp[]>>
    every_case_tac>>gvs[])>>
  xlet_autop>>
  Cases_on`res`>>fs[map_concl_to_string_def,SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`strlit ""`>>
    rename1`add_stderr _ err`>>
    qexists_tac`err`>>xsimpl>>rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  PairCases_on`y`>>fs[SUM_TYPE_def,map_concl_to_string_def]>>
  xmatch>>
  xapp>>asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`concl_to_string y2`>>simp[]>>
  qexists_tac`strlit ""`>>
  rw[]>>simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl>>
  fs[get_fml_def]>>
  metis_tac[]
QED

Definition check_unsat_1_sem_def:
  check_unsat_1_sem fs f1 out ⇔
  case get_annot_fml fs f1 of
    SOME prob => out = concat (print_annot_prob prob)
  | NONE => out = strlit ""
End

Quote add_cakeml:
  fun check_unsat_1 f1 =
  case parse_pbf_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr prob =>
    TextIO.print_list (print_annot_prob prob)
End

Theorem check_unsat_1_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_1"(get_ml_prog_state()))
    [f1v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(check_unsat_1_sem fs f1 out))
Proof
  rw[check_unsat_1_sem_def]>>
  xcf "check_unsat_1" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  xlet_autop>>
  TOP_CASE_TAC>>fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    rw[]>>
    qexists_tac`err`>>xsimpl)>>
  xmatch>>
  xlet_autop>>
  xapp_spec print_list_spec>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`strlit ""`>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl
QED

Definition output_to_string_def:
  (output_to_string bound NoOutput =
    strlit "s VERIFIED NO OUTPUT GUARANTEE\n") ∧
  (output_to_string bound Derivable =
    strlit "s VERIFIED OUTPUT DERIVABLE\n") ∧
  (output_to_string bound Equisatisfiable =
    strlit "s VERIFIED OUTPUT EQUISATISFIABLE\n") ∧
  (output_to_string bound Equioptimal =
    strlit "s VERIFIED OUTPUT EQUIOPTIMAL FOR obj < " ^ int_inf_to_string bound ^ strlit"\n") ∧
  (output_to_string bound Equisolvable =
    strlit "s VERIFIED OUTPUT EQUISOLVABLE FOR obj < " ^ int_inf_to_string bound ^ strlit"\n")
End

Definition check_unsat_3_sem_def:
  check_unsat_3_sem fs f1 f3 out ⇔
  (out ≠ strlit"" ⇒
  ∃pres obj fml prest objt fmlt.
    get_fml fs f1 = SOME (pres,obj,fml) ∧
    get_fml fs f3 = SOME (prest,objt,fmlt) ∧
    ∃output bound concl.
      out =
        (concl_to_string concl ^
        output_to_string bound output) ∧
      pbc$sem_concl (set fml) obj concl ∧
      pbc$sem_output (set fml) obj (pres_set_list pres) bound
        (set fmlt) objt (pres_set_list prest) output
  )
End

(* Ignoring output section for 2-arg version *)
Definition map_out_concl_to_string_def:
  (map_out_concl_to_string (INL s) = (INL s)) ∧
  (map_out_concl_to_string (INR (out,bnd,c)) =
    (INR (concl_to_string c ^ output_to_string bnd out)))
End

val res = translate output_to_string_def;
val res = translate map_out_concl_to_string_def;

Quote add_cakeml:
  fun check_unsat_3 f1 f2 f3 =
  case parse_pbf_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr prob =>
  (case parse_pbf_full f3 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr probt =>
    (case
      map_out_concl_to_string
        (check_unsat_top_norm True
          (strip_annot_prob prob) (strip_annot_prob probt) f2) of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr s => TextIO.print s))
End

Theorem check_unsat_3_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  STRING_TYPE f2 f2v ∧ validArg f2 ∧
  STRING_TYPE f3 f3v ∧ validArg f3 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_3"(get_ml_prog_state()))
    [f1v; f2v; f3v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(check_unsat_3_sem fs f1 f3 out))
Proof
  rw[check_unsat_3_sem_def]>>
  xcf "check_unsat_3" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  xlet_autop>>
  gvs[get_fml_def]>>
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
  xlet_autop>>
  xlet`POSTv v. STDIO fs * &BOOL T v`
  >-
    (xcon>>xsimpl)>>
  `∃pres obj fml. strip_annot_prob x = (pres,obj,fml)` by metis_tac[PAIR]>>
  `∃prest objt fmlt. strip_annot_prob x' = (prest, objt,fmlt)` by metis_tac[PAIR]>>
  xlet`(POSTv v.
     STDIO fs *
     SEP_EXISTS res.
     &(
       SUM_TYPE STRING_TYPE
         (PAIR_TYPE PBC_OUTPUT_TYPE
           (PAIR_TYPE (OPTION_TYPE INT) PBC_CONCL_TYPE))
         res v ∧
       case res of
         INR (output,bound,concl) =>
         sem_concl (set fml) obj concl ∧
         sem_output (set fml) obj (pres_set_list pres) bound
          (set fmlt) objt (pres_set_list prest) output
       | INL l => T))`
  >- (
    xapp>>xsimpl>>
    fs[validArg_def]>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    simp[PAIR_TYPE_def]>>
    qexists_tac`f2`>>simp[FILENAME_def,validArg_def]>>
    qexists_tac`emp`>>xsimpl>>
    rw[]>>
    first_x_assum (irule_at Any)>>
    simp[])>>
  xlet_auto
  >- xsimpl>>
  Cases_on`res`>>fs[map_out_concl_to_string_def,SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`strlit ""`>>
    rename1`add_stderr _ err`>>
    qexists_tac`err`>>xsimpl>>rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  PairCases_on`y`>>fs[SUM_TYPE_def,map_out_concl_to_string_def]>>
  xmatch>>
  xapp>>asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`concl_to_string y2 ^ output_to_string y1 y0`>>simp[]>>
  qexists_tac`strlit ""`>>
  rw[]>>simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl>>
  fs[get_fml_def]>>
  metis_tac[]
QED

Definition usage_string_def:
  usage_string = strlit "Usage: cake_pb <OPB file> <optional: PB proof file> <optional: output OPB file>\n"
End

val r = translate usage_string_def;

Quote add_cakeml:
  fun main u =
  case CommandLine.arguments () of
    [f1] => check_unsat_1 f1
  | [f1,f2] => check_unsat_2 f1 f2
  | [f1,f2,f3] => check_unsat_3 f1 f2 f3
  | _ => TextIO.output TextIO.stdErr (mk_usage_string usage_string)
End

Definition main_sem_def:
  main_sem fs cl out =
  if LENGTH cl = 2 then
    check_unsat_1_sem fs (EL 1 cl) out
  else if LENGTH cl = 3 then
    check_unsat_2_sem fs (EL 1 cl) out
  else if LENGTH cl = 4 then
    check_unsat_3_sem fs (EL 1 cl) (EL 3 cl) out
  else out = strlit ""
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
  Cases_on`t`>>fs[LIST_TYPE_def]
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
  Cases_on`t'`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>rw[]>>
    rpt(first_x_assum (irule_at Any)>>xsimpl)>>
    fs[wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>>
  Cases_on`t`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>rw[]>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
    fs[wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>>
  Cases_on`t'`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>rw[]>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
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

local

val name = "main"
val (sem_thm,prog_tm) =
  whole_prog_thm (get_ml_prog_state()) name (UNDISCH main_whole_prog_spec2)
Definition main_prog_def:
  main_prog = ^prog_tm
End

in

Theorem main_semantics =
  sem_thm
  |> REWRITE_RULE[GSYM main_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[GSYM CONJ_ASSOC,AND_IMP_INTRO];

end
