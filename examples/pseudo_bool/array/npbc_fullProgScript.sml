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
  noparse_string f s = concat[«c Input file: »;f;« unable to parse in format: »; s;«\n»]
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
  (int_inf_to_string NONE = «INF») ∧
  (int_inf_to_string (SOME (i:int)) =
    toString i)
End

Definition concl_to_string_def:
  (concl_to_string NoConcl = «s VERIFIED NO CONCLUSION\n») ∧
  (concl_to_string DSat = «s VERIFIED SATISFIABLE\n») ∧
  (concl_to_string DUnsat = «s VERIFIED UNSATISFIABLE\n») ∧
  (concl_to_string (OBounds lbi ubi) =
    let lbs = int_inf_to_string lbi in
    let ubs = int_inf_to_string ubi in
    «s VERIFIED BOUNDS » ^ lbs ^ « <= obj <= » ^ ubs ^ «\n») ∧
  (concl_to_string (EEnum n b) =
    if b
    then
      «s VERIFIED COMPLETE ENUMERATION OF » ^ toString n ^ « SOLUTIONS\n»
    else
      «s VERIFIED PARTIAL ENUMERATION OF » ^ toString n ^ « SOLUTIONS\n»)
End

Definition get_fml_def:
  get_fml fs f =
  OPTION_MAP strip_annot_prob (get_annot_fml fs f)
End

(* Parsing an OPB file one line at a time, numbering and normalising each
  constraint as it is read *)
val r = translate skip_annot_def;
val r = translate parse_constraint_front_def;
val r = translate parse_cmp_deg_def;
val r = translate parse_constraint_ns_def;
val r = translate parse_norm_line_def;
val r = translate parse_norm_lines_def;
val r = translate parse_norm_header_def;

Definition noparse_line_string_def:
  noparse_line_string f (lno:num) =
  noparse_string f («OPB, line » ^ toString lno)
End

val r = translate noparse_line_string_def;

val inputLineTokens_specialize =
  inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_v_thm,tokenize_v_thm,blanks_def] ;

Overload "ntn_TYPE" = ``PBC_NORMALISE_NAME_TO_NUM_STATE_TYPE STRING_TYPE``

Overload "nprob_TYPE" = ``
  PAIR_TYPE pres_TYPE (PAIR_TYPE obj_TYPE (LIST_TYPE constraint_TYPE))``

(* lno counts the lines read so far *)
Quote add_cakeml:
  fun next_nocomment_arr lno fd =
  case TextIO.inputLineTokens #"\n" fd blanks tokenize of
    None => (lno, None)
  | Some l =>
    if nocomment_line l then (lno+1, Some l)
    else next_nocomment_arr (lno+1) fd
End

Theorem next_nocomment_arr_spec:
  ∀lines fd fdv fs lno lnov.
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "next_nocomment_arr" (get_ml_prog_state()))
    [lnov; fdv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      SEP_EXISTS k lines' lno'.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
        &(PAIR_TYPE NUM (OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
            (lno',oHD (FILTER nocomment_line (MAP toks lines))) v ∧
          FILTER nocomment_line (MAP toks lines') =
          DROP 1 (FILTER nocomment_line (MAP toks lines))))
Proof
  Induct>>
  simp[]>>
  rpt strip_tac>>
  xcf "next_nocomment_arr" (get_ml_prog_state ())
  >- (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    >- (
      xapp_spec inputLineTokens_specialize>>
      qexistsl_tac [`emp`,‘[]’,‘fs’]>>
      qexists_tac ‘fd’>>xsimpl>>fs [])>>
    gvs[OPTION_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    xcon>>xsimpl>>
    qexistsl_tac [‘k’,`[]`,`lno`]>>
    xsimpl>>
    simp[PAIR_TYPE_def,OPTION_TYPE_def])>>
  xlet ‘(POSTv v.
          SEP_EXISTS k.
              STDIO (forwardFD fs fd k) *
              INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
              & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
                  (SOME (toks h)) v)’
  >- (
    xapp_spec inputLineTokens_specialize>>
    qexistsl_tac [`emp`,‘h::lines’,‘fs’]>>
    qexists_tac ‘fd’>>xsimpl>>fs []>>
    rw []>>qexists_tac ‘x’>>xsimpl>>
    simp[toks_def])>>
  gvs[OPTION_TYPE_def]>>
  xmatch>>fs []>>
  xlet_autop>>
  reverse IF_CASES_TAC
  >- (
    xif>>asm_exists_tac>>xsimpl>>
    xlet_autop>>
    xapp>>xsimpl>>
    first_x_assum (irule_at Any)>>
    qexistsl_tac [`forwardFD fs fd k`,`fd`]>>
    xsimpl>>
    rw[]>>
    simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  xif>>asm_exists_tac>>simp[]>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  qexistsl_tac [`k`,`lines`,`lno+1`]>>
  xsimpl>>
  simp[PAIR_TYPE_def,OPTION_TYPE_def]
QED

Quote add_cakeml:
  fun parse_norm_body_arr lno fd s acc =
  case TextIO.inputLineTokens #"\n" fd blanks tokenize of
    None => Inr (acc, s)
  | Some l =>
    if nocomment_line l then
      (case parse_norm_line l s acc of
        None => Inl (lno+1)
      | Some res => case res of (acc1,s1) =>
        parse_norm_body_arr (lno+1) fd s1 acc1)
    else parse_norm_body_arr (lno+1) fd s acc
End

Theorem parse_norm_body_arr_spec:
  ∀lines fd fdv fs s sv acc accv lno lnov.
  NUM lno lnov ∧
  ntn_TYPE s sv ∧
  LIST_TYPE constraint_TYPE acc accv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_norm_body_arr" (get_ml_prog_state()))
    [lnov; fdv; sv; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      &(∃n.
        SUM_TYPE NUM (PAIR_TYPE (LIST_TYPE constraint_TYPE) ntn_TYPE)
          (case parse_norm_lines (MAP toks lines) s acc of
            NONE => INL n
          | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))
Proof
  Induct>>
  simp[parse_norm_lines_def]>>
  rpt strip_tac>>
  xcf "parse_norm_body_arr" (get_ml_prog_state ())
  >- (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    >- (
      xapp_spec inputLineTokens_specialize>>
      qexistsl_tac [`emp`,‘[]’,‘fs’]>>
      qexists_tac ‘fd’>>xsimpl>>fs [])>>
    gvs[OPTION_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def,PAIR_TYPE_def]>>
    qexistsl_tac [‘k’,`[]`]>>
    xsimpl)>>
  xlet ‘(POSTv v.
          SEP_EXISTS k.
              STDIO (forwardFD fs fd k) *
              INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
              & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
                  (SOME (toks h)) v)’
  >- (
    xapp_spec inputLineTokens_specialize>>
    qexistsl_tac [`emp`,‘h::lines’,‘fs’]>>
    qexists_tac ‘fd’>>xsimpl>>fs []>>
    rw []>>qexists_tac ‘x’>>xsimpl>>
    simp[toks_def])>>
  gvs[OPTION_TYPE_def]>>
  xmatch>>fs []>>
  xlet_autop>>
  reverse IF_CASES_TAC
  >- (
    xif>>asm_exists_tac>>xsimpl>>
    xlet_autop>>
    xapp>>xsimpl>>
    rpt (first_x_assum (irule_at Any))>>
    qexistsl_tac [`forwardFD fs fd k`,`fd`]>>
    xsimpl>>
    rw[]>>
    simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  xif>>asm_exists_tac>>simp[]>>
  xlet_autop>>
  Cases_on`parse_norm_line (toks h) s acc`>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>
    xsimpl>>
    qexistsl_tac [`k`,`lines`]>>
    xsimpl>>
    simp[SUM_TYPE_def]>>
    metis_tac[])>>
  rename1`parse_norm_line (toks h) s acc = SOME res`>>
  PairCases_on`res`>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xmatch>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  rpt (first_x_assum (irule_at Any))>>
  qexistsl_tac [`forwardFD fs fd k`,`fd`]>>
  xsimpl>>
  rw[]>>
  simp[forwardFD_o]>>
  metis_tac[STDIO_INSTREAM_LINES_refl_gc]
QED

Quote add_cakeml:
  fun parse_norm_toks_arr fd s =
  case next_nocomment_arr 0 fd of (lno1,l1) =>
  case next_nocomment_arr lno1 fd of (lno2,l2) =>
  case parse_norm_header l1 l2 s of
    None => Inl lno2
  | Some res => case res of (pres,(obj,(acc,s1))) =>
    (case parse_norm_body_arr lno2 fd s1 acc of
      Inl n => Inl n
    | Inr res => case res of (acc1,t) =>
      Inr ((pres,(obj,List.rev acc1)),t))
End

Theorem parse_norm_toks_arr_spec:
  ntn_TYPE s sv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_norm_toks_arr" (get_ml_prog_state()))
    [fdv; sv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      &(∃n.
        SUM_TYPE NUM (PAIR_TYPE nprob_TYPE ntn_TYPE)
          (case parse_norm_pbf_toks (MAP toks lines) s of
            NONE => INL n
          | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))
Proof
  rw[]>>
  xcf "parse_norm_toks_arr" (get_ml_prog_state ())>>
  qabbrev_tac`fl = FILTER nocomment_line (MAP toks lines)`>>
  xlet`(POSTv v.
      SEP_EXISTS k1 lines1 lno1.
        STDIO (forwardFD fs fd k1) *
        INSTREAM_LINES #"\n" fd fdv lines1 (forwardFD fs fd k1) *
        &(PAIR_TYPE NUM (OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
            (lno1,oHD fl) v ∧
          FILTER nocomment_line (MAP toks lines1) = DROP 1 fl))`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac [`emp`,`lines`,`fs`,`fd`]>>
    xsimpl>>
    rw[Abbr`fl`]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet`(POSTv v.
      SEP_EXISTS k2 lines2 lno2.
        STDIO (forwardFD fs fd k2) *
        INSTREAM_LINES #"\n" fd fdv lines2 (forwardFD fs fd k2) *
        &(PAIR_TYPE NUM (OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
            (lno2,oHD (DROP 1 fl)) v ∧
          FILTER nocomment_line (MAP toks lines2) = DROP 2 fl))`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac [`emp`,`lines1`,`forwardFD fs fd k1`,`fd`,`lno1`]>>
    xsimpl>>
    rw[]>>
    fs[forwardFD_o,DROP_DROP_T]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  gvs[Abbr`fl`,parse_norm_pbf_toks_def]>>
  qmatch_asmsub_abbrev_tac`parse_norm_header l1 l2 s`>>
  Cases_on`parse_norm_header l1 l2 s`>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xcon>>
    xsimpl>>
    qexistsl_tac [`k2`,`lines2`]>>
    xsimpl>>
    simp[SUM_TYPE_def]>>
    metis_tac[])>>
  rename1`parse_norm_header l1 l2 s = SOME hdr`>>
  PairCases_on`hdr`>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xmatch>>
  xlet`(POSTv v.
      &(∃n.
        SUM_TYPE NUM (PAIR_TYPE (LIST_TYPE constraint_TYPE) ntn_TYPE)
          (case parse_norm_lines (MAP toks lines2) hdr3 hdr2 of
            NONE => INL n
          | SOME x => INR x) v) *
      SEP_EXISTS k3 lines3.
        STDIO (forwardFD fs fd k3) *
        INSTREAM_LINES #"\n" fd fdv lines3 (forwardFD fs fd k3))`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac [`emp`,`hdr3`,`lines2`,`forwardFD fs fd k2`,`fd`,`hdr2`,
      `lno2`]>>
    xsimpl>>
    rw[]>>
    fs[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  `parse_norm_lines (DROP 2 (FILTER nocomment_line (MAP toks lines)))
     hdr3 hdr2 = parse_norm_lines (MAP toks lines2) hdr3 hdr2` by
    metis_tac[parse_norm_lines_FILTER]>>
  simp[]>>
  Cases_on`parse_norm_lines (MAP toks lines2) hdr3 hdr2`>>
  fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xcon>>
    xsimpl>>
    qexistsl_tac [`k3`,`lines3`]>>
    xsimpl>>
    simp[SUM_TYPE_def]>>
    metis_tac[])>>
  rename1`parse_norm_lines _ hdr3 hdr2 = SOME body`>>
  PairCases_on`body`>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  qexistsl_tac [`k3`,`lines3`]>>
  xsimpl>>
  simp[SUM_TYPE_def,PAIR_TYPE_def]
QED

Quote add_cakeml:
  fun parse_norm_pbf_full f s =
  let
    val fd = TextIO.openIn f
    val res = parse_norm_toks_arr fd s
    val close = TextIO.closeIn fd
  in
    case res of
      Inl n => Inl (noparse_line_string f n)
    | Inr x => Inr x
  end
  handle TextIO.BadFileName => Inl (notfound_string f)
End

Theorem parse_norm_pbf_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs ∧
  ntn_TYPE s sv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_norm_pbf_full"(get_ml_prog_state()))
    [fv; sv]
    (STDIO fs)
    (POSTv v.
    & (∃err. SUM_TYPE STRING_TYPE (PAIR_TYPE nprob_TYPE ntn_TYPE)
    (case get_fml fs f of
      NONE => INL err
    | SOME prob => INR (name_norm_prob prob s)) v) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_norm_pbf_full"(get_ml_prog_state()) >>
  fs[validArg_def]>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def]>>xpull) >>
  reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def]>>xpull>>metis_tac[]) >>
  simp[get_fml_def,get_annot_fml_def]>>
  reverse (Cases_on `inFS_fname fs f`) >> simp[]
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs f) *
      STDIO fs`
    >-
      (xlet_auto_spec (SOME openIn_STDIO_spec)>>xsimpl)
    >>
      fs[BadFileName_exn_def]>>
      xcases>>rw[]>>
      xlet_auto>>xsimpl>>
      xcon>>xsimpl>>
      simp[SUM_TYPE_def]>>metis_tac[])>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval`>>xsimpl>>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec (SOME (openIn_spec_lines |> Q.GEN `c0` |> Q.SPEC `#"\n"`))>>xsimpl>>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES _ fdd fddv lines fss`>>
  xlet`(POSTv v.
      &(∃n.
        SUM_TYPE NUM (PAIR_TYPE nprob_TYPE ntn_TYPE)
          (case parse_norm_pbf_toks (MAP toks lines) s of
            NONE => INL n
          | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fss fdd k) *
         INSTREAM_LINES #"\n" fdd fddv lines' (forwardFD fss fdd k))`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac [`emp`,`s`,`lines`,`fss`,`fdd`]>>
    xsimpl>>
    rw[]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  xlet `POSTv v. STDIO fs`
  >- (
    xapp_spec closeIn_spec_lines >>
    qexistsl_tac [`emp`,`lines'`,`forwardFD fss fdd k`,`fdd`,`#"\n"`]>>
    conj_tac >-
     (unabbrev_all_tac>>
      imp_res_tac fsFFIPropsTheory.nextFD_ltX>>fs []>>
      imp_res_tac fsFFIPropsTheory.STD_streams_nextFD>>fs []) >>
    xsimpl>>
    `validFileFD fdd (forwardFD fss fdd k).infds` by
      (unabbrev_all_tac>> simp[validFileFD_forwardFD]>>
       imp_res_tac fsFFIPropsTheory.nextFD_ltX>>fs []>>
       match_mp_tac validFileFD_nextFD>>fs []) >>
    xsimpl >> rw [] >>
    unabbrev_all_tac>>xsimpl>>
    simp[forwardFD_ADELKEY_same]>>
    DEP_REWRITE_TAC [fsFFIPropsTheory.openFileFS_ADELKEY_nextFD]>>
    xsimpl>>
    imp_res_tac (DECIDE ``n<m:num ==> n <= m``) >>
    imp_res_tac fsFFIPropsTheory.nextFD_leX>>fs [])>>
  fs[parse_norm_pbf_toks_thm,parse_pbf_def]>>
  Cases_on`parse_pbf_toks (MAP toks lines)`>>
  fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>
    xsimpl>>
    simp[SUM_TYPE_def]>>
    metis_tac[])>>
  xmatch>>
  xcon>>
  xsimpl>>
  simp[SUM_TYPE_def]
QED

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 out ⇔
  (out ≠ «» ⇒
  ∃pres obj fml.
    get_fml fs f1 = SOME (pres,obj,fml) ∧
    ∃concl.
      out = concl_to_string concl ∧
      pbc$sem_concl (set fml) obj (pres_set_list pres) concl)
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
  case parse_norm_pbf_full f1 init_ntn of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr res => case res of ((pres,(obj,fml)),t) =>
    (case
      map_concl_to_string
        (check_unsat_top False (name_to_num_var_nf,t)
          fml pres obj [] None None f2) of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr s => TextIO.print s)
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
  assume_tac init_ntn_v_thm>>
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
  rename1`get_fml fs f1 = SOME prob`>>
  PairCases_on`prob`>>
  `∃pres obj fml t.
    name_norm_prob (prob0,prob1,prob2) init_ntn = ((pres,obj,fml),t)` by
    metis_tac[PAIR]>>
  simp[SUM_TYPE_def,PAIR_TYPE_def]>>rw[]>>
  xmatch>>
  xmatch>>
  ntac 5 xlet_autop>>
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
         npbc$sem_concl (set fml) obj (pres_set_spt pres) concl
      | INL l => T))`
  >- (
    xapp_spec (check_unsat_top_spec
      |> INST_TYPE[alpha|->``:mlstring name_to_num_state``])>>
    xsimpl>>
    qexistsl_tac [`emp`,`NONE`,`pres`,`NONE`,`obj`,`fs`,`[]`,`fml`,`F`,`f2`,
      `ntn_TYPE`,`(name_to_num_var_nf,t)`]>>
    xsimpl>>
    fs[validArg_def,FILENAME_def,LIST_TYPE_def,OPTION_TYPE_def,
      PAIR_TYPE_def]>>
    CONJ_TAC
    >- simp[name_to_num_var_nf_v_thm]>>
    rw[]>>
    asm_exists_tac>>
    simp[]>>
    rpt (TOP_CASE_TAC>>gvs[]))>>
  xlet_autop>>
  Cases_on`res`>>fs[map_concl_to_string_def,SUM_TYPE_def]
  >- (
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
  PairCases_on`y`>>fs[SUM_TYPE_def,map_concl_to_string_def]>>
  xmatch>>
  xapp>>asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`concl_to_string y2`>>simp[]>>
  qexists_tac`«»`>>
  rw[]>>simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl>>
  qexists_tac`y2`>>
  simp[]>>
  drule name_norm_prob_sem_concl>>
  impl_tac
  >- (
    simp[init_ntn_def]>>
    match_mp_tac init_state_ok>>
    fs[TotOrd_compare])>>
  simp[]
QED

Definition check_unsat_1_sem_def:
  check_unsat_1_sem fs f1 out ⇔
  case get_annot_fml fs f1 of
    SOME prob => out = concat (print_annot_prob prob)
  | NONE => out = «»
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
  qexists_tac`«»`>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl
QED

Definition output_to_string_def:
  (output_to_string bound NoOutput =
    «s VERIFIED NO OUTPUT GUARANTEE\n») ∧
  (output_to_string bound Derivable =
    «s VERIFIED OUTPUT DERIVABLE\n») ∧
  (output_to_string bound Equisatisfiable =
    «s VERIFIED OUTPUT EQUISATISFIABLE\n») ∧
  (output_to_string bound Equioptimal =
    «s VERIFIED OUTPUT EQUIOPTIMAL FOR obj < » ^ int_inf_to_string bound ^ «\n») ∧
  (output_to_string bound Equisolvable =
    «s VERIFIED OUTPUT EQUISOLVABLE FOR obj < » ^ int_inf_to_string bound ^ «\n»)
End

Definition check_unsat_3_sem_def:
  check_unsat_3_sem fs f1 f3 out ⇔
  (out ≠ «» ⇒
  ∃pres obj fml prest objt fmlt.
    get_fml fs f1 = SOME (pres,obj,fml) ∧
    get_fml fs f3 = SOME (prest,objt,fmlt) ∧
    ∃output bound concl.
      out =
        (concl_to_string concl ^
        output_to_string bound output) ∧
      pbc$sem_concl (set fml) obj (pres_set_list pres) concl ∧
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
  case parse_norm_pbf_full f1 init_ntn of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr res => case res of ((pres,(obj,fml)),t) =>
  (case parse_norm_pbf_full f3 t of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr rest => case rest of ((prest,(objt,fmlt)),u) =>
    (case
      map_out_concl_to_string
        (check_unsat_top True (name_to_num_var_nf,u)
          fml pres obj fmlt prest objt f2) of
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
  assume_tac init_ntn_v_thm>>
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
  rename1`get_fml fs f1 = SOME prob`>>
  PairCases_on`prob`>>
  `∃pres obj fml t.
    name_norm_prob (prob0,prob1,prob2) init_ntn = ((pres,obj,fml),t)` by
    metis_tac[PAIR]>>
  simp[SUM_TYPE_def,PAIR_TYPE_def]>>rw[]>>
  xmatch>>
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
  rename1`get_fml fs f3 = SOME probt`>>
  PairCases_on`probt`>>
  `∃prest objt fmlt u.
    name_norm_prob (probt0,probt1,probt2) t = ((prest,objt,fmlt),u)` by
    metis_tac[PAIR]>>
  simp[SUM_TYPE_def,PAIR_TYPE_def]>>rw[]>>
  xmatch>>
  xmatch>>
  ntac 2 xlet_autop>>
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
         npbc$sem_concl (set fml) obj (pres_set_spt pres) concl ∧
         npbc$sem_output (set fml) obj (pres_set_spt pres) bound
          (set fmlt) objt (pres_set_spt prest) output
       | INL l => T))`
  >- (
    xapp_spec (check_unsat_top_spec
      |> INST_TYPE[alpha|->``:mlstring name_to_num_state``])>>
    xsimpl>>
    rw[]
    >- (
      qexists_tac`T`>>
      EVAL_TAC)
    >- (
      qexists_tac`f2`>>
      fs[FILENAME_def,validArg_def])>>
    qexistsl_tac [`ntn_TYPE`,`(name_to_num_var_nf,u)`]>>
    simp[PAIR_TYPE_def,name_to_num_var_nf_v_thm])>>
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
    qexists_tac`«»`>>
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
  qexists_tac`«»`>>
  rw[]>>simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl>>
  qexistsl_tac [`y0`,`y1`,`y2`]>>
  simp[]>>
  `name_to_num_state_ok init_ntn` by (
    simp[init_ntn_def]>>
    match_mp_tac init_state_ok>>
    fs[TotOrd_compare])>>
  `name_to_num_state_ok t` by
    metis_tac[name_to_num_state_ok_name_norm_prob]>>
  CONJ_TAC
  >- (
    qpat_assum`name_norm_prob _ init_ntn = _`
      (mp_then (Pos hd) mp_tac name_norm_prob_sem_concl)>>
    simp[])>>
  `sem_output (set prob2) prob1 (pres_set_list prob0) y1
     (set probt2) probt1 (pres_set_list probt0) y0 ⇔
   sem_output (set fml) obj (pres_set_spt pres) y1
     (set fmlt) objt (pres_set_spt prest) y0` by (
    irule name_norm_prob_sem_output>>
    metis_tac[])>>
  simp[]
QED

Definition usage_string_def:
  usage_string = «Usage: cake_pb <OPB file> <optional: PB proof file> <optional: output OPB file>\n»
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

Theorem main_semantics =
  prove_sem_thm "main"
                "main_prog"
                main_whole_prog_spec2;
