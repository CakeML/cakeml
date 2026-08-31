(*
  CNF encoder and checker
*)
Theory cnfProg
Ancestors
  basis_ffi cnf syntax_helper dimacs cnf_to_pb npbc_parseProg
Libs
  preamble basis cfLib basisFunctionsLib

val _ = translation_extends "npbc_parseProg";
(* TODO: COPIED from lpr_arrayFullProgScript.sml *)
Theorem fastForwardFD_ADELKEY_same[simp]:
   forwardFD fs fd n with infds updated_by ADELKEY fd =
   fs with infds updated_by ADELKEY fd
Proof
  fs [forwardFD_def, IO_fs_component_equality]
QED

(* npbc_parseProg already translated pb_parse's own blanks/tokenize, so
  syntax_helper's get the _1 suffix here *)
val _ = translate syntax_helperTheory.blanks_def;
val _ = translate syntax_helperTheory.tokenize_def;

val blanks_1_v_thm = theorem "blanks_1_v_thm";
val tokenize_1_v_thm = theorem "tokenize_1_v_thm";

val _ = translate parse_header_line_def;

val parse_header_line_side = Q.prove(`
   ∀x. parse_header_line_side x= T`,
  rw[definition"parse_header_line_side_def"]>>
  intLib.ARITH_TAC)
  |> update_precondition;

val _ = translate var_lit_def;
val _ = translate mk_lit_def;
val _ = translate parse_until_zero_aux_def;
val _ = translate parse_until_zero_def;
val _ = translate check_maxvar_def;
val _ = translate parse_lits_def;
val _ = translate keep_line_def;

Overload "CFML_TYPE" = ``LIST_TYPE (LIST_TYPE (CNF_LIT_TYPE NUM))``

Definition format_dimacs_failure_def:
  format_dimacs_failure (lno:num) s =
  «c DIMACS parse failed at line: » ^ toString lno ^ «. Reason: » ^ s ^ «\n»
End

val _ = translate format_dimacs_failure_def;

val inputLineTokens_specialize =
  inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`syntax_helper$blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_1_v`
  |> Q.GEN `g` |> Q.ISPEC`syntax_helper$tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_1_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_1_v_thm,tokenize_1_v_thm,blanks_def] ;

(* The DIMACS body is read one line at a time, tokenizing during input *)
Quote add_cakeml:
  fun parse_dimacs_body_arr lno maxvar fd acc =
  case TextIO.inputLineTokens #"\n" fd blanks_1 tokenize_1 of
    None => Inr (List.rev acc)
  | Some l =>
    if keep_line l then
      (case parse_lits maxvar l of
        None => Inl (format_dimacs_failure lno "failed to parse line")
      | Some cl =>
        parse_dimacs_body_arr (lno+1) maxvar fd (cl::acc))
    else parse_dimacs_body_arr (lno+1) maxvar fd acc
End

Theorem parse_dimacs_body_arr_spec:
  !lines fd fdv fs maxvar maxvarv acc accv lno lnov.
  NUM lno lnov ∧
  NUM maxvar maxvarv ∧
  CFML_TYPE acc accv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_dimacs_body_arr" (get_ml_prog_state()))
    [lnov; maxvarv; fdv; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      &
      (∃err.
      SUM_TYPE STRING_TYPE CFML_TYPE
        (case parse_body_gen parse_lits maxvar
          (FILTER keep_line (MAP syntax_helper$toks lines)) acc of
          NONE => INL err
        | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))
Proof
  Induct>>
  simp []>>
  rpt strip_tac>>
  xcf "parse_dimacs_body_arr" (get_ml_prog_state ())
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
    simp[parse_body_gen_def]>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def]>>
    qexists_tac ‘k’>>xsimpl>>
    qexists_tac `[]`>>xsimpl)>>
  xlet ‘(POSTv v.
          SEP_EXISTS k.
              STDIO (forwardFD fs fd k) *
              INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
              & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
                  (SOME (syntax_helper$toks h)) v)’
  >- (
    xapp_spec inputLineTokens_specialize>>
    qexistsl_tac [`emp`,‘h::lines’,‘fs’]>>
    qexists_tac ‘fd’>>xsimpl>>fs []>>
    rw []>>qexists_tac ‘x’>>xsimpl>>
    simp[syntax_helperTheory.toks_def])>>
  gvs[OPTION_TYPE_def]>>
  xmatch>>fs []>>
  xlet_autop>>
  reverse IF_CASES_TAC
  >- (
    xif >> asm_exists_tac>>xsimpl>>
    xlet_autop>>
    xapp>> xsimpl>>
    rpt(first_x_assum (irule_at Any))>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>xsimpl>>
    rw[]>>
    qexists_tac`k+x`>>
    simp[GSYM fsFFIPropsTheory.forwardFD_o]>>
    qexists_tac`x'`>>xsimpl>>
    metis_tac[])>>
  xif>> asm_exists_tac>>simp[]>>
  xlet_autop>>
  simp[parse_body_gen_def]>>
  Cases_on`parse_lits maxvar (syntax_helper$toks h)`>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>
    xsimpl>>
    qexists_tac`k`>> qexists_tac`lines`>>xsimpl>>
    simp[SUM_TYPE_def]>>
    metis_tac[])>>
  rename1`parse_lits maxvar (syntax_helper$toks h) = SOME cl`>>
  xmatch>>
  xlet_autop>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  rpt(first_x_assum (irule_at Any))>>
  qexistsl_tac [`forwardFD fs fd k`,`fd`]>>
  xsimpl>>
  simp[LIST_TYPE_def,forwardFD_o]>>rw[]>>
  qexists_tac`cl::acc`>>
  simp[LIST_TYPE_def]>>
  rw[]>>
  qexistsl_tac [`k+x`,`x'`]>>
  xsimpl>>
  metis_tac[]
QED

Quote add_cakeml:
  fun parse_dimacs_toks_arr lno fd =
  case TextIO.inputLineTokens #"\n" fd blanks_1 tokenize_1 of
    None => Inl (format_dimacs_failure lno "failed to find header")
  | Some l =>
    if keep_line l then
      (case parse_header_line l of
        None => Inl (format_dimacs_failure lno "failed to parse header")
      | Some res => case res of (vars,ncl) =>
        (case parse_dimacs_body_arr lno vars fd [] of
          Inl fail => Inl fail
        | Inr acc =>
          if List.length acc = ncl then
            Inr (vars,(ncl,acc))
          else
            Inl (format_dimacs_failure lno "incorrect number of clauses")))
    else parse_dimacs_toks_arr (lno+1) fd
End

Theorem parse_dimacs_toks_arr_spec:
  !lines fd fdv fs lno lnov.
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_dimacs_toks_arr" (get_ml_prog_state()))
    [lnov; fdv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE
        (PAIR_TYPE NUM (PAIR_TYPE NUM CFML_TYPE))
      (case parse_cnf_toks (MAP syntax_helper$toks lines) of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))
Proof
  Induct>>
  simp []>>
  rpt strip_tac>>
  xcf "parse_dimacs_toks_arr" (get_ml_prog_state ())
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
    gvs [OPTION_TYPE_def]>>
    xmatch>>fs []>>
    simp[parse_cnf_toks_def,parse_dimacs_toks_gen_def]>>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def]>>
    qexists_tac ‘k’>>xsimpl>>
    qexists_tac `[]`>>xsimpl>>
    metis_tac[])>>
  xlet ‘(POSTv v.
          SEP_EXISTS k.
              STDIO (forwardFD fs fd k) *
              INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
              & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (syntax_helper$toks h)) v)’
  >- (
    xapp_spec inputLineTokens_specialize>>
    qexistsl_tac [`emp`,‘h::lines’,‘fs’]>>
    qexists_tac ‘fd’>>xsimpl>>fs []>>
    rw []>>qexists_tac ‘x’>>xsimpl>>
    simp[syntax_helperTheory.toks_def])>>
  gvs [OPTION_TYPE_def]>>
  xmatch>>fs []>>
  xlet_autop>>
  simp[parse_cnf_toks_def,parse_dimacs_toks_gen_def]>>
  reverse IF_CASES_TAC
  >- (
    xif >> asm_exists_tac>>xsimpl>>
    xlet_autop>>
    xapp>> xsimpl>>
    asm_exists_tac>> simp[]>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>xsimpl>>
    rw[]>>
    fs[parse_cnf_toks_def,parse_dimacs_toks_gen_def]>>
    qexists_tac`k+x`>>
    simp[GSYM fsFFIPropsTheory.forwardFD_o]>>
    qexists_tac`x'`>>xsimpl>>
    metis_tac[])>>
  xif>> asm_exists_tac>>simp[]>>
  xlet_autop>>
  Cases_on`parse_header_line (syntax_helper$toks h)`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>
    xsimpl>>
    qexists_tac`k`>> qexists_tac`lines`>>xsimpl>>
    simp[SUM_TYPE_def]>>
    metis_tac[])>>
  xmatch>>
  rename1`parse_header_line (syntax_helper$toks h) = SOME hdr`>>
  PairCases_on`hdr`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xlet `(POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE CFML_TYPE
      (case parse_body_gen parse_lits hdr0
        (FILTER keep_line (MAP syntax_helper$toks lines)) [] of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac [`emp`,`hdr0`,`lines`,`forwardFD fs fd k`,`fd`,`[]`,
      `lno`]>>
    xsimpl>>
    simp[LIST_TYPE_def]>>
    rw[]>>
    qexists_tac`k+x`>>
    simp[GSYM fsFFIPropsTheory.forwardFD_o]>>
    qexists_tac`x'`>>xsimpl>>
    metis_tac[])>>
  pop_assum mp_tac>> TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    rw[]>>fs[SUM_TYPE_def]>>
    xmatch>>
    xcon>>
    xsimpl>>
    qexists_tac`k`>>qexists_tac`lines'`>>xsimpl>>
    metis_tac[])>>
  strip_tac>>fs[SUM_TYPE_def]>>
  xmatch>>
  drule LENGTH_parse_body_gen>>
  strip_tac>>gvs[]>>
  rpt xlet_autop>>
  rw[]>>xif
  >- (
    asm_exists_tac>>simp[]>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def,PAIR_TYPE_def]>>
    qexists_tac`k`>>qexists_tac`lines'`>>xsimpl)>>
  asm_exists_tac>>simp[]>>
  xlet_autop>>
  xcon>>
  xsimpl>>
  qexistsl_tac [`k`,`lines'`]>>
  simp[SUM_TYPE_def]>>
  xsimpl>>
  metis_tac[]
QED

(* parse_dimacs_toks with simple wrapper *)
Quote add_cakeml:
  fun parse_dimacs_full fname =
  let
    val fd = TextIO.openIn fname
    val res = parse_dimacs_toks_arr 0 fd
    val close = TextIO.closeIn fd;
  in
    res
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)
End

Theorem parse_dimacs_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_dimacs_full"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. (SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM CFML_TYPE))
    (if inFS_fname fs f then
    (case parse_cnf_toks (MAP syntax_helper$toks (all_lines_file fs f)) of
      NONE => INL err
    | SOME x => INR x)
    else INL err) v)) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_dimacs_full"(get_ml_prog_state()) >>
  fs[validArg_def]>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def]>>xpull) >>
  reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def]>>xpull>>metis_tac[]) >>
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
      & (∃err. SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM CFML_TYPE))
      (case parse_cnf_toks (MAP syntax_helper$toks lines) of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fss fdd k) * INSTREAM_LINES #"\n" fdd fddv lines' (forwardFD fss fdd k))`
  >- (
    xapp>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`lines`>>
    qexists_tac`fss`>>qexists_tac`fdd`>>xsimpl>>
    rw[]>>
    qexists_tac`x`>>qexists_tac`x'`>>xsimpl>>
    metis_tac[])>>
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
    imp_res_tac (DECIDE ``n<m:num ==> n <= m``) >>
    imp_res_tac fsFFIPropsTheory.nextFD_leX>>fs [] >>
    drule fsFFIPropsTheory.openFileFS_ADELKEY_nextFD >>
    fs [Abbr`fss`]>>xsimpl)>>
  xvar>>
  xsimpl>>
  metis_tac[]
QED

(* Translate the encoder *)
val res = translate lit_le_def;
val res = translate sorted_nub_aux_def;
val res = translate sorted_nub_def;
val res = translate canon_clause_def;
val res = translate to_pblit_def;
val res = translate clause_to_pbc_def;
val res = translate fml_to_pbf_def;

(* parse input from f1 and run encoder into npbc *)
Quote add_cakeml:
  fun parse_and_enc f1 =
  case parse_dimacs_full f1 of
    Inl err => Inl err
  | Inr (a,(b,fml)) =>
    Inr (fml_to_pbf fml,(a,b))
End

Definition get_fml_def:
  get_fml fs f =
  if inFS_fname fs f then
    parse_cnf (all_lines_file fs f)
  else NONE
End

Theorem parse_and_enc_spec:
  STRING_TYPE f1 f1v ∧
  validArg f1 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_and_enc"(get_ml_prog_state()))
    [f1v]
    (STDIO fs)
    (POSTv v.
    STDIO fs *
    & ∃res.
       SUM_TYPE STRING_TYPE
         (PAIR_TYPE
          (LIST_TYPE constraint_TYPE)
          (PAIR_TYPE NUM NUM)) res v ∧
      case res of
        INL err =>
          get_fml fs f1 = NONE
      | INR (pbf,nvars,ncl) =>
        ∃fml.
        get_fml fs f1 = SOME fml ∧
        fml_to_pbf fml = pbf)
Proof
  rw[]>>
  xcf"parse_and_enc"(get_ml_prog_state())>>
  xlet_autop>>
  pop_assum mp_tac>>
  reverse IF_CASES_TAC
  >- (
    rw[SUM_TYPE_def]>>
    xmatch>>
    xcon>>
    xsimpl>>
    qexists_tac`INL err`>>
    simp[SUM_TYPE_def]>>
    fs[get_fml_def])>>
  TOP_CASE_TAC
  >- (
    rw[SUM_TYPE_def]>>
    xmatch>>
    xcon>>
    xsimpl>>
    qexists_tac`INL err`>>
    simp[SUM_TYPE_def]>>
    fs[get_fml_def,parse_cnf_def])>>
  rw[SUM_TYPE_def]>>
  PairCases_on`x`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  qexists_tac`INR (fml_to_pbf x2,x0,x1)`>>
  fs[SUM_TYPE_def,PAIR_TYPE_def]>>
  simp[get_fml_def,parse_cnf_def]
QED

(* NOTE: Reuse infrastructure from pbc_normalise *)

(* Variables x1 ... xl maps to 1 ... l respectively
  everything else uses the mapping *)
Definition plainLim_nf_def:
  plainLim_nf l s nhm =
  if strlen s ≥ 1 ∧ strsub s 0 = #"x" then
    case mlint$fromNatString (substring s 1 (strlen s - 1)) of
      NONE => NONE
    | SOME n =>
      if n ≤ l then SOME (n,nhm)
      else SOME(name_to_num_var s nhm)
  else
    SOME(name_to_num_var s nhm)
End

val res = translate plainLim_nf_def;

val res = translate pbc_normaliseTheory.mk_map_def;
val res = translate pbc_normaliseTheory.name_to_num_var_def;

Definition cnf_init_state_def:
  cnf_init_state n =
  <| to_num := LN; to_str := LN; hash_fun := hash_str; cmp_name := compare; next_num := n+1 |>
End

Definition plainLim_ns_def:
  plainLim_ns n = (plainLim_nf n,
    cnf_init_state n)
End

val res = translate cnf_init_state_def;
val res = translate plainLim_ns_def;

Definition UNSAT_string_def:
  UNSAT_string = «s VERIFIED UNSAT\n»
End

Definition SAT_string_def:
  SAT_string = «s VERIFIED SAT\n»
End

Definition NO_CONCLUSION_string_def:
  NO_CONCLUSION_string = «s VERIFIED NO CONCLUSION\n»
End

(* And empty formula *)
Definition default_nobjf_def:
  default_nobjf = (NONE,[]):((int # num) list # int) option # npbc list
End

val res = translate default_nobjf_def;

(* Turn result into string *)
Definition ores_to_string_def:
  (ores_to_string (INL s) = INL s) ∧
  (ores_to_string (INR (out,bnd,h)) =
    if out ≠ NoOutput then INL «c Unexpected output section.\n»
    else
    case h of
      DUnsat => INR UNSAT_string
    | DSat => INR SAT_string
    | DNoConcl => INR NO_CONCLUSION_string
    | _ => INL «c Unexpected conclusion for decision problem.\n»)
End

val res = translate (ores_to_string_def |> SIMP_RULE std_ss [UNSAT_string_def,SAT_string_def,NO_CONCLUSION_string_def]);

Quote add_cakeml:
  fun check_unsat_2 f1 f2 =
  case parse_and_enc f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (fml,(nv,nc)) =>
    let val n = None in
    (case
      ores_to_string (
        check_unsat_top False (plainlim_ns nv) fml n n [] n n f2) of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr s => TextIO.print s)
    end
End

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 out ⇔
  (out ≠ «» ⇒
  ∃fml.
    get_fml fs f1 = SOME fml ∧
    (
    out = UNSAT_string ∧ unsatisfiable_cnf (set fml) ∨
    out = SAT_string ∧ satisfiable_cnf (set fml) ∨
    out = NO_CONCLUSION_string))
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
  Cases_on`res`
  >- (
    fs[SUM_TYPE_def]>>
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`x`>>
    xsimpl>>rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  fs[SUM_TYPE_def]>>
  PairCases_on`y`>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xlet_autop>>
  xlet_autop>>
  xlet`POSTv v. STDIO fs * &BOOL F v`
  >-
    (xcon>>xsimpl)>>
  xlet`POSTv v.
    STDIO fs *
    SEP_EXISTS res.
     &(
        SUM_TYPE STRING_TYPE
         (PAIR_TYPE PBC_OUTPUT_TYPE
           (PAIR_TYPE (OPTION_TYPE INT) PBC_CONCL_TYPE))
          res v ∧
        case res of
         INR (output,bound,concl) =>
           sem_concl (set (fml_to_pbf fml)) NONE {} concl
        | INL l => T)`
  >- (
    drule_at (Pos (el 2)) check_unsat_top_spec>>
    disch_then drule>>
    strip_tac>>
    xapp>>
    xsimpl>>
    fs[FILENAME_def,validArg_def,OPTION_TYPE_def]>>
    rpt (first_x_assum (irule_at Any))>>
    qexists_tac`NONE`>>qexists_tac`NONE`>>
    qexists_tac`NONE`>>qexists_tac`NONE`>>
    qexists_tac`[]`>>
    xsimpl>>
    simp[OPTION_TYPE_def,LIST_TYPE_def]>>
    rw[]>> asm_exists_tac>>simp[]>>
    every_case_tac>>fs[npbcTheory.pres_set_spt_def])>>
  xlet_autop>>
  Cases_on`ores_to_string res`>>fs[SUM_TYPE_def]>>
  xmatch
  >- (
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`«»`>>
    simp[]>>
    qexists_tac`x`>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  xapp>>asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`y`>>
  qexists_tac`«»`>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  reverse CONJ_TAC>- xsimpl>>
  rw[]>>
  every_case_tac>>fs[ores_to_string_def,SUM_TYPE_def]>>
  gvs[AllCaseEqs(),npbc_checkTheory.hconcl_concl_def,npbcTheory.sem_concl_def]
  >- (
    DISJ2_TAC>>
    fs[get_fml_def]>>
    fs[npbcTheory.unsatisfiable_def,npbcTheory.satisfiable_def,
      unsatisfiable_cnf_def,satisfiable_cnf_def]>>
    metis_tac[fml_to_pbf_sound])>>
  DISJ1_TAC>>
  fs[get_fml_def]>>
  fs[npbcTheory.unsatisfiable_def,npbcTheory.satisfiable_def,
    unsatisfiable_cnf_def,satisfiable_cnf_def]>>
  metis_tac[fml_to_pbf_sound]
QED

Definition print_npbf_def:
  print_npbf fml = MAP npbc_string fml
End

val res = translate print_npbf_def;

Quote add_cakeml:
  fun check_unsat_1 f1 =
  case parse_and_enc f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (fml,(nv,nc)) =>
    TextIO.print_list (print_npbf fml)
End

Definition check_unsat_1_sem_def:
  check_unsat_1_sem fs f1 out ⇔
  (out ≠ «» ⇒
  ∃fml.
    get_fml fs f1 = SOME fml ∧
    out = concat (print_npbf (fml_to_pbf fml)))
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
  pop_assum mp_tac>>
  every_case_tac>>fs[SUM_TYPE_def,PAIR_TYPE_def]>>rw[]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    rw[]>>
    qexists_tac`x`>>xsimpl)>>
  Cases_on`r`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xapp_spec print_list_spec>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`concat(print_npbf(fml_to_pbf fml))`>>
  qexists_tac`«»`>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl
QED

Definition usage_string_def:
  usage_string = «Usage: cake_pb_cnf <DIMACS CNF file> <optional: PB proof file>\n»
End

val r = translate usage_string_def;

Quote add_cakeml:
  fun main u =
  case CommandLine.arguments () of
    [f1] => check_unsat_1 f1
  | [f1,f2] => check_unsat_2 f1 f2
  | _ => TextIO.output TextIO.stdErr (mk_usage_string usage_string)
End

Definition main_sem_def:
  main_sem fs cl out =
  if LENGTH cl = 2 then
    check_unsat_1_sem fs (EL 1 cl) out
  else if LENGTH cl = 3 then
    check_unsat_2_sem fs (EL 1 cl) out
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
