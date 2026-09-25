(*
  This builds the cake_lrup proof checker
*)
Theory lrup_arrayFullProg
Ancestors
  misc UnsafeProof cnf ccnf ccnf_list ccnf_arrayProg ccnf_parseProg
  syntax_helper dimacs lrup lrup_list lrup_arrayProg
  basis_ffi
Libs
  preamble basis

val _ = translation_extends"lrup_arrayProg";

val _ = translate parse_header_line_def;

Theorem parse_header_line_side_thm[local]:
  ∀x. parse_header_line_side x ⇔ T
Proof
  rw[definition"parse_header_line_side_def"]>>
  intLib.ARITH_TAC
QED

val _ = parse_header_line_side_thm |> update_precondition;

val _ = translate var_lit_def;
val _ = translate parse_vclause_def;
val _ = translate keep_line_def;

val blanks_v_thm = fetch "ccnf_parseProg" "blanks_v_thm";
val tokenize_v_thm = fetch "ccnf_parseProg" "tokenize_v_thm";

val inputLineTokens_specialize =
  inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_v_thm,tokenize_v_thm,blanks_def] ;

Overload "VCFML_TYPE" = ``LIST_TYPE vcclause_TYPE``

(* The DIMACS body is read one line at a time, tokenizing during input *)
Quote add_cakeml:
  fun parse_body_arr lno maxvar fd acc =
  case TextIO.inputLineTokens #"\n" fd blanks tokenize of
    None => Inr (List.rev acc)
  | Some l =>
    if keep_line l then
      (case parse_vclause maxvar l of
        None => Inl (format_dimacs_failure lno "failed to parse line")
      | Some cl =>
        parse_body_arr (lno+1) maxvar fd (cl::acc))
    else parse_body_arr (lno+1) maxvar fd acc
End

Theorem parse_body_arr_spec:
  !lines fd fdv fs maxvar maxvarv acc accv lno lnov.
  NUM lno lnov ∧
  NUM maxvar maxvarv ∧
  VCFML_TYPE acc accv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_body_arr" (get_ml_prog_state()))
    [lnov; maxvarv; fdv; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      &
      (∃err.
      SUM_TYPE STRING_TYPE VCFML_TYPE
        (case parse_body_gen parse_vclause maxvar
          (FILTER keep_line (MAP toks lines)) acc of
          NONE => INL err
        | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))
Proof
  Induct>>
  simp []>>
  rpt strip_tac>>
  xcf "parse_body_arr" (get_ml_prog_state ())
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
              & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks h)) v)’
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
  Cases_on`parse_vclause maxvar (toks h)`>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>
    xsimpl>>
    qexists_tac`k`>> qexists_tac`lines`>>xsimpl>>
    simp[SUM_TYPE_def]>>
    metis_tac[])>>
  rename1`parse_vclause maxvar (toks h) = SOME cl`>>
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
  fun parse_vcnf_toks_arr lno fd =
  case TextIO.inputLineTokens #"\n" fd blanks tokenize of
    None => Inl (format_dimacs_failure lno "failed to find header")
  | Some l =>
    if keep_line l then
      (case parse_header_line l of
        None => Inl (format_dimacs_failure lno "failed to parse header")
      | Some res => case res of (vars,ncl) =>
        (case parse_body_arr lno vars fd [] of
          Inl fail => Inl fail
        | Inr acc =>
          if List.length acc = ncl then
            Inr (vars,(ncl,acc))
          else
            Inl (format_dimacs_failure lno "incorrect number of clauses")))
    else parse_vcnf_toks_arr (lno+1) fd
End

Theorem parse_vcnf_toks_arr_spec:
  !lines fd fdv fs lno lnov.
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_vcnf_toks_arr" (get_ml_prog_state()))
    [lnov; fdv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE
        (PAIR_TYPE NUM (PAIR_TYPE NUM VCFML_TYPE))
      (case parse_vcnf_toks (MAP toks lines) of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))
Proof
  Induct>>
  simp []>>
  rpt strip_tac>>
  xcf "parse_vcnf_toks_arr" (get_ml_prog_state ())
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
    simp[parse_vcnf_toks_def,parse_dimacs_toks_gen_def]>>
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
              & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks h)) v)’
  >- (
    xapp_spec inputLineTokens_specialize>>
    qexistsl_tac [`emp`,‘h::lines’,‘fs’]>>
    qexists_tac ‘fd’>>xsimpl>>fs []>>
    rw []>>qexists_tac ‘x’>>xsimpl>>
    simp[toks_def])>>
  gvs [OPTION_TYPE_def]>>
  xmatch>>fs []>>
  xlet_autop>>
  simp[parse_vcnf_toks_def,parse_dimacs_toks_gen_def]>>
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
    fs[parse_vcnf_toks_def,parse_dimacs_toks_gen_def]>>
    qexists_tac`k+x`>>
    simp[GSYM fsFFIPropsTheory.forwardFD_o]>>
    qexists_tac`x'`>>xsimpl>>
    metis_tac[])>>
  xif>> asm_exists_tac>>simp[]>>
  xlet_autop>>
  Cases_on`parse_header_line (toks h)`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>
    xsimpl>>
    qexists_tac`k`>> qexists_tac`lines`>>xsimpl>>
    simp[SUM_TYPE_def]>>
    metis_tac[])>>
  xmatch>>
  rename1`parse_header_line (toks h) = SOME hdr`>>
  PairCases_on`hdr`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xlet `(POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE VCFML_TYPE
      (case parse_body_gen parse_vclause hdr0
        (FILTER keep_line (MAP toks lines)) [] of
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

(* parse_vcnf_toks with simple wrapper *)
Quote add_cakeml:
  fun parse_full fname =
  let
    val fd = TextIO.openIn fname
    val res = parse_vcnf_toks_arr 0 fd
    val close = TextIO.closeIn fd;
  in
    res
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)
End

Theorem parse_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_full"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. (SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM VCFML_TYPE))
    (if inFS_fname fs f then
    (case parse_vcnf_toks (MAP toks (all_lines_file fs f)) of
      NONE => INL err
    | SOME x => INR x)
    else INL err) v)) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_full"(get_ml_prog_state()) >>
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
      & (∃err. SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM VCFML_TYPE))
      (case parse_vcnf_toks (MAP toks lines) of
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

val usage_string = ‘

Usage:  cake_lrup <CNF formula file> <optional: compressed LRUP proof file>

Run LRUP unsatisfiability proof checking (if proof is given)

’

fun drop_until p [] = []
  | drop_until p (x::xs) = if p x then x::xs else drop_until p xs;

val usage_string_tm =
  usage_string |> hd |> (fn QUOTE s => s) |> explode
  |> drop_until (fn c => c = #"\n") |> tl |> implode
  |> stringSyntax.fromMLstring;

Definition usage_string_def:
  usage_string = strlit ^usage_string_tm
End

val r = translate usage_string_def;

(* == Build info =========================================================== *)

val current_version_tm = mlstring_from_proc "git" ["rev-parse", "HEAD"]
val poly_version_tm = mlstring_from_proc "poly" ["-v"]
val hol_version_tm = mlstring_from_proc "git" ["-C", Globals.HOLDIR, "rev-parse", "HEAD"]

val date_str = Date.toString (Date.fromTimeUniv (Time.now ())) ^ " UTC\n"
val date_tm = Term `strlit^(stringSyntax.fromMLstring date_str)`

Definition print_option_def:
  print_option h x =
    case x of
      NONE => «»
    | SOME y => h ^ « » ^ y ^ «\n»
End

val current_build_info_str_tm = EVAL ``
    let commit = print_option «CakeML:» ^current_version_tm in
    let hol    = print_option «HOL4:  » ^hol_version_tm in
    let poly   = print_option «PolyML:» ^poly_version_tm in
      concat
        [ «cake_lrup\n\n»
        ; «Version details:\n»
        ; ^date_tm; «\n»
        ; commit; hol; poly ]``
  |> concl |> rhs

Definition current_build_info_str_def:
  current_build_info_str = ^current_build_info_str_tm
End

val res = translate current_build_info_str_def;

Definition mk_usage_string_def:
  mk_usage_string s = current_build_info_str ^ «\n\n» ^ s
End

val res = translate mk_usage_string_def;

(*
  Checker takes up to 2 arguments:
  2 args (CNF file, proof file):
    parse CNF, run proof, report UNSAT (or error)

  The RUP assignment array is indexed by the ORIGINAL variable, so mv+1
  slots suffice for the initial formula (every literal satisfies
  var_lit l ≤ mv by check_maxvar). It grows on demand thereafter.
*)
Quote add_cakeml:
  fun check_unsat_2 f1 f2 =
  case parse_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv,(ncl,vcfml)) =>
    (case check_unsat' vcfml f2 (mv+1) (2*ncl) of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr b =>
      if b then
        TextIO.print "s VERIFIED UNSAT\n"
      else
        TextIO.output TextIO.stdErr "c empty clause not derived at end of proof\n")
End

val _ = translate print_lit_def;
val _ = translate print_lits_def;
val _ = translate max_list_def;
val _ = translate max_cnf_def;
val _ = translate print_header_line_def;
val _ = translate print_cnf_def;
val _ = translate unconv_cfml_def;

Quote add_cakeml:
  fun check_unsat_1 f1 =
  case parse_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv,(ncl,vcfml)) => TextIO.print_list (print_cnf (unconv_cfml vcfml))
End

(* The formula a run of the checker is about: the contents of the input
  file, when it exists and parses *)
Definition get_cnf_def:
  get_cnf fs f =
  if inFS_fname fs f
  then parse_cnf (all_lines_file fs f)
  else NONE
End

Definition check_unsat_1_sem_def:
  check_unsat_1_sem fs f1 out ⇔
  case get_cnf fs f1 of
    SOME fml => out = concat (print_cnf fml)
  | NONE => out = «»
End

(* Every failure path prints nothing on stdout and reports err on stderr.
  out_tac supplies the empty stdout witness on the paths where the output
  predicate does not already pin it. *)
fun err_tac out_tac =
  xapp_spec output_stderr_spec>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>out_tac>>
  qexists_tac`err`>>
  fs[STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
  xsimpl;

val no_out = qexists_tac`«»`;

Theorem check_unsat_1_spec:
  STRING_TYPE f1 f1v ∧
  validArg f1 ∧
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
  rw[]>>
  xcf "check_unsat_1" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def]>>xpull)>>
  xlet_autop>>
  simp[check_unsat_1_sem_def,get_cnf_def,parse_cnf_def]>>
  reverse (Cases_on`inFS_fname fs f1`)>>fs[SUM_TYPE_def,parse_vcnf_toks]
  >- (xmatch>>err_tac all_tac)>>
  Cases_on`parse_cnf_toks (MAP toks (all_lines_file fs f1))`>>
  fs[SUM_TYPE_def]
  >- (xmatch>>err_tac all_tac)>>
  PairCases_on`x`>>
  gvs[PAIR_TYPE_def]>>
  rename1`parse_cnf_toks _ = SOME (mv,ncl,fml)`>>
  xmatch>>
  xlet_autop>>
  `unconv_cfml (conv_cfml fml) = fml` by
    metis_tac[unconv_cfml_conv_cfml,parse_cnf_toks_nz_lit]>>
  gvs[]>>
  xlet_autop>>
  xapp_spec print_list_spec>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`«»`>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl
QED

Quote add_cakeml:
  fun check_unsat u =
  case CommandLine.arguments () of
    [f1] => check_unsat_1 f1
  | [f1,f2] => check_unsat_2 f1 f2
  | _ => TextIO.output TextIO.stdErr (mk_usage_string usage_string)
End

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 out ⇔
  (out ≠ «» ⇒
    out = «s VERIFIED UNSAT\n» ∧
    ∃fml. get_cnf fs f1 = SOME fml ∧ unsatisfiable_cnf (set fml))
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
  rw[]>>
  xcf "check_unsat_2" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def]>>xpull)>>
  xlet_autop>>
  simp[check_unsat_2_sem_def,get_cnf_def,parse_cnf_def]>>
  reverse (Cases_on`inFS_fname fs f1`)>>fs[SUM_TYPE_def,parse_vcnf_toks]
  >- (xmatch>>err_tac all_tac)>>
  Cases_on`parse_cnf_toks (MAP toks (all_lines_file fs f1))`>>
  fs[SUM_TYPE_def]
  >- (xmatch>>err_tac all_tac)>>
  qmatch_asmsub_rename_tac`parse_cnf_toks _ = SOME res`>>
  PairCases_on`res`>>
  gvs[SUM_TYPE_def,PAIR_TYPE_def]>>
  rename1`parse_cnf_toks _ = SOME (mv,ncl,cfml)`>>
  xmatch>>
  rpt xlet_autop>>
  xlet`POSTv v.
    STDIO fs *
    SEP_EXISTS res.
      &(SUM_TYPE STRING_TYPE BOOL res v ∧
        (res = INR T ⇒ unsatisfiable_cnf (set cfml)))`
  >- (
    xapp>>
    rw[]
    >- metis_tac[parse_cnf_toks_nz_lit]
    >- (
      qexists_tac`f2`>>
      fs[FILENAME_def,validArg_def])
    >- (
      qexists_tac`mv+1`>>simp[]>>
      drule parse_cnf_toks_bound>>
      rw[EVERY_MEM]>>res_tac>>simp[])>>
    qexists_tac`2*ncl`>>simp[])>>
  namedCases_on`res` ["err","b"]>>fs[SUM_TYPE_def]
  >- (
    xmatch>>err_tac no_out)>>
  xmatch>>
  xif
  >- (
    xapp_spec print_spec>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexistsl_tac [`«s VERIFIED UNSAT\n»`,`«»`]>>
    simp[STD_streams_stderr,add_stdo_nil]>>
    xsimpl)>>
  xapp_spec output_stderr_spec>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexistsl_tac [`«»`,`«c empty clause not derived at end of proof\n»`]>>
  fs[STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
  xsimpl
QED

Definition check_unsat_sem_def:
  check_unsat_sem fs cl out ⇔
  if LENGTH cl = 2 then check_unsat_1_sem fs (EL 1 cl) out
  else if LENGTH cl = 3 then check_unsat_2_sem fs (EL 1 cl) out
  else out = «»
End

Theorem STDIO_refl:
  STDIO A ==>>
  STDIO A * GC
Proof
  xsimpl
QED

Theorem check_unsat_spec:
   hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"check_unsat"(get_ml_prog_state()))
     [Conv NONE []]
     (COMMANDLINE cl * STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv *
     COMMANDLINE cl *
     SEP_EXISTS out err.
       STDIO (add_stdout (add_stderr fs err) out) *
       &(check_unsat_sem fs cl out))
Proof
  rw[check_unsat_sem_def]>>
  xcf"check_unsat"(get_ml_prog_state())>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def]>>xpull)>>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def]>>xpull)>>
  rpt xlet_autop >>
  Cases_on `cl` >- fs[wfcl_def] >>
  Cases_on`t`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    assume_tac (theorem "usage_string_v_thm")>>
    xlet_autop>>
    xapp_spec output_stderr_spec>>xsimpl>>
    rename1`COMMANDLINE cl`>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac`mk_usage_string usage_string`>>
    simp[]>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    fs[STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
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
    rpt(first_x_assum (irule_at Any)>>xsimpl)>>
    fs[wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>>
  xmatch>>
  assume_tac (theorem "usage_string_v_thm")>>
  xlet_autop>>
  xapp_spec output_stderr_spec>>xsimpl>>
  rename1`COMMANDLINE cl`>>
  qexists_tac`COMMANDLINE cl`>>xsimpl>>
  qexists_tac`mk_usage_string usage_string`>>
  simp[]>>
  qexists_tac`fs`>>xsimpl>>
  rw[]>>
  fs[STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
  metis_tac[STDIO_refl]
QED

Theorem check_unsat_whole_prog_spec2:
   hasFreeFD fs ⇒
   whole_prog_spec2 check_unsat_v cl fs NONE
     (λfs'. ∃out err.
        fs' = add_stdout (add_stderr fs err) out ∧
        check_unsat_sem fs cl out)
Proof
  rw[basis_ffiTheory.whole_prog_spec2_def]>>
  match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH check_unsat_spec))))>>
  xsimpl>>
  rw[PULL_EXISTS]>>
  qexists_tac`add_stdout (add_stderr fs x') x`>>
  xsimpl>>
  qexistsl_tac [`x`,`x'`]>>
  xsimpl>>
  simp[GSYM add_stdo_with_numchars,with_same_numchars]
QED

Theorem check_unsat_semantics =
  prove_sem_thm "check_unsat"
                "check_unsat_prog"
                check_unsat_whole_prog_spec2;
