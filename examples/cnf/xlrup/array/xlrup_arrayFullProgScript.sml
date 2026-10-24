(*
  This builds the cake_xlrup proof checker
*)
Theory xlrup_arrayFullProg
Ancestors
  misc UnsafeProof cnf ccnf ccnf_list ccnf_arrayProg ccnf_parseProg
  syntax_helper dimacs xor xlrup xlrup_cnf xlrup_list xlrup_parsing
  xlrup_arrayProg
  basis_ffi
Libs
  preamble basis

val _ = translation_extends"xlrup_arrayProg";

val _ = translate check_maxvar_def;
val _ = translate parse_lits_def;
val _ = translate fix_hd_def;
val _ = translate parse_xor_def;
val _ = translate parse_line_def;
val _ = translate split_cnf_ext_def;

Overload "LL_LIT_TYPE" = ``LIST_TYPE (LIST_TYPE (CNF_LIT_TYPE NUM))``
Overload "EXT_TYPE" = ``LIST_TYPE XLRUP_CNF_CNF_EXT_TYPE``

Quote add_cakeml:
  fun parse_body_arr lno maxvar fd acc =
  case TextIO.inputLineTokens #"\n" fd blanks tokenize of
    None => Inr (List.rev acc)
  | Some l =>
    if keep_line l then
      (case parse_line maxvar l of
        None => Inl (format_dimacs_failure lno "failed to parse line")
      | Some cx =>
        parse_body_arr (lno+1) maxvar fd (cx::acc))
    else parse_body_arr (lno+1) maxvar fd acc
End

Theorem parse_body_arr_spec:
  !lines fd fdv fs maxvar maxvarv acc accv lno lnov.
  NUM lno lnov ∧
  NUM maxvar maxvarv ∧
  EXT_TYPE acc accv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_body_arr" (get_ml_prog_state()))
    [lnov; maxvarv; fdv; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      &
      (∃err.
      SUM_TYPE STRING_TYPE EXT_TYPE
        (case parse_body_gen parse_line maxvar
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
      qexists_tac `emp`>>
      qexists_tac ‘[]’>>
      qexists_tac ‘fs’>>
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
    qexists_tac `emp`>>
    qexists_tac ‘h::lines’>>
    qexists_tac ‘fs’>>
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
  Cases_on`parse_line maxvar (toks h)`>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>
    xsimpl>>
    qexists_tac`k`>> qexists_tac`lines`>>xsimpl>>
    simp[SUM_TYPE_def]>>
    metis_tac[])>>
  rename1`parse_line maxvar (toks h) = SOME cx`>>
  xmatch>>
  xlet_autop>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  rpt(first_x_assum (irule_at Any))>>
  qexists_tac`forwardFD fs fd k`>>
  qexists_tac`fd`>>
  xsimpl>>
  simp[LIST_TYPE_def,forwardFD_o]>>rw[]>>
  qexists_tac`cx::acc`>>
  simp[LIST_TYPE_def]>>
  rw[]>>
  qexists_tac`k+x`>>
  qexists_tac`x'`>>
  xsimpl>>
  metis_tac[]
QED

Quote add_cakeml:
  fun parse_cnf_ext_toks_arr lno fd =
  case TextIO.inputLineTokens #"\n" fd blanks tokenize of
    None => Inl (format_dimacs_failure lno "failed to find header")
  | Some l =>
    if keep_line l then
      (case parse_header_line l of
        None => Inl (format_dimacs_failure lno "failed to parse header")
      | Some res => case res of (vars,ncx) =>
        (case parse_body_arr lno vars fd [] of
          Inl fail => Inl fail
        | Inr acc =>
          if List.length acc = ncx then
            (case split_cnf_ext acc of (cs,xs) =>
              Inr (vars,(ncx,(cs,xs))))
          else
            Inl (format_dimacs_failure lno "incorrect number of clauses / xors")))
    else parse_cnf_ext_toks_arr (lno+1) fd
End

Theorem parse_cnf_ext_toks_arr_spec:
  !lines fd fdv fs lno lnov.
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_cnf_ext_toks_arr" (get_ml_prog_state()))
    [lnov; fdv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE
        (PAIR_TYPE NUM (PAIR_TYPE NUM
          (PAIR_TYPE LL_LIT_TYPE LL_LIT_TYPE)))
      (case parse_cnf_ext_toks (MAP toks lines) of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))
Proof
  Induct>>
  simp []>>
  rpt strip_tac>>
  xcf "parse_cnf_ext_toks_arr" (get_ml_prog_state ())
  >- (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    >- (
      xapp_spec inputLineTokens_specialize>>
      qexists_tac `emp`>>
      qexists_tac ‘[]’>>
      qexists_tac ‘fs’>>
      qexists_tac ‘fd’>>xsimpl>>fs [])>>
    gvs [OPTION_TYPE_def]>>
    xmatch>>fs []>>
    simp[parse_cnf_ext_toks_def,parse_dimacs_toks_gen_def]>>
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
    qexists_tac `emp`>>
    qexists_tac ‘h::lines’>>
    qexists_tac ‘fs’>>
    qexists_tac ‘fd’>>xsimpl>>fs []>>
    rw []>>qexists_tac ‘x’>>xsimpl>>
    simp[toks_def])>>
  gvs [OPTION_TYPE_def]>>
  xmatch>>fs []>>
  xlet_autop>>
  simp[parse_cnf_ext_toks_def,parse_dimacs_toks_gen_def]>>
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
    fs[parse_cnf_ext_toks_def,parse_dimacs_toks_gen_def]>>
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
      & (∃err. SUM_TYPE STRING_TYPE EXT_TYPE
      (case parse_body_gen parse_line hdr0
        (FILTER keep_line (MAP toks lines)) [] of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))`
  >- (
    xapp>>xsimpl>>
    qexists_tac`emp`>>
    qexists_tac`hdr0`>>
    qexists_tac`lines`>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>
    qexists_tac`[]`>>
    qexists_tac`lno`>>
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
    xlet_autop>>
    pairarg_tac>>gvs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def,PAIR_TYPE_def]>>
    qexists_tac`k`>>qexists_tac`lines'`>>xsimpl)>>
  asm_exists_tac>>simp[]>>
  xlet_autop>>
  xcon>>
  xsimpl>>
  qexists_tac`k`>>
  qexists_tac`lines'`>>
  simp[SUM_TYPE_def]>>
  xsimpl>>
  metis_tac[]
QED

(* parse_cnf_ext_toks with simple wrapper *)
Quote add_cakeml:
  fun parse_full fname =
  let
    val fd = TextIO.openIn fname
    val res = parse_cnf_ext_toks_arr 0 fd
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
    & (∃err. (SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM
        (PAIR_TYPE LL_LIT_TYPE LL_LIT_TYPE)))
    (if inFS_fname fs f then
    (case parse_cnf_ext_toks (MAP toks (all_lines_file fs f)) of
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
      & (∃err. SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM
        (PAIR_TYPE LL_LIT_TYPE LL_LIT_TYPE)))
      (case parse_cnf_ext_toks (MAP toks lines) of
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
    qexists_tac `emp`>>
    qexists_tac `lines'` >>
    qexists_tac `forwardFD fss fdd k` >>
    qexists_tac `fdd` >>
    qexists_tac `#"\n"` >>
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

Usage:  cake_xlrup [--binary|--no-binary] [--] <CNF-XOR formula file> <optional: XLRUP proof file>
        cake_xlrup --dump [--] <CNF-XOR formula file>

Run XLRUP unsatisfiability proof checking.
The proof is read from the proof file if one is given, and from standard input otherwise.
The proof is read in binary format unless --no-binary is given.
--dump parses the formula file and prints the formula.

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
        [ «cake_xlrup\n\n»
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

val r = translate to_cclause_def;
val r = translate conv_cfml_def;

(*
  Checker takes up to 2 file arguments:
  --dump and 1 file (CNF XOR file): parse and print the formula
  1 file (CNF XOR file): as for 2 files, reading the proof from stdin
  2 files (CNF XOR file, proof file):
    parse CNF XOR, run proof, report UNSAT (or error);
    b selects the binary (T) or text (F) proof format

  The RUP assignment array is indexed by the ORIGINAL variable, so mv+1
  slots suffice for the initial formula (every literal satisfies
  var_lit l ≤ mv by check_maxvar). It grows on demand thereafter.
*)
Quote add_cakeml:
  fun check_unsat_2 f1 f2 b =
  case parse_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv,(ncx,(cfml,xfml))) =>
  let val cfml = conv_cfml cfml
      val carr = build_cfml_arr (2*ncx) 1 cfml
      val xarr = Array.array ncx None
      val tn = (Array.array 0 0, 1)
      val bnd = mv + 1
  in
    case check_unsat' xfml carr xarr tn 0 f2 bnd b of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr b =>
      if b then
        TextIO.print "s VERIFIED UNSAT\n"
      else
        TextIO.output TextIO.stdErr "c empty clause not derived at end of proof\n"
  end
End

Quote add_cakeml:
  fun check_unsat_stdin f1 b =
  case parse_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv,(ncx,(cfml,xfml))) =>
  let val cfml = conv_cfml cfml
      val carr = build_cfml_arr (2*ncx) 1 cfml
      val xarr = Array.array ncx None
      val tn = (Array.array 0 0, 1)
      val bnd = mv + 1
  in
    case check_unsat_stdin' xfml carr xarr tn 0 bnd b of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr b =>
      if b then
        TextIO.print "s VERIFIED UNSAT\n"
      else
        TextIO.output TextIO.stdErr "c empty clause not derived at end of proof\n"
  end
End

val _ = translate print_xor_def;
val _ = translate max_cnf_def;
val _ = translate max_cnf_ext_def;
val _ = translate print_cnf_ext_def;

Quote add_cakeml:
  fun check_unsat_1 f1 =
  case parse_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv,(ncl,fml)) => TextIO.print_list (print_cnf_ext fml)
End

(* The formula a run of the checker is about: the contents of the input
  file, when it exists and parses *)
Definition get_cnf_ext_def:
  get_cnf_ext fs f =
  if inFS_fname fs f
  then parse_cnf_ext (all_lines_file fs f)
  else NONE
End

Definition check_unsat_1_sem_def:
  check_unsat_1_sem fs f1 out ⇔
  case get_cnf_ext fs f1 of
    SOME fml => out = concat (print_cnf_ext fml)
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
  simp[check_unsat_1_sem_def,get_cnf_ext_def,parse_cnf_ext_def]>>
  reverse (Cases_on`inFS_fname fs f1`)>>fs[SUM_TYPE_def]
  >- (xmatch>>err_tac all_tac)>>
  Cases_on`parse_cnf_ext_toks (MAP toks (all_lines_file fs f1))`>>
  fs[SUM_TYPE_def]
  >- (xmatch>>err_tac all_tac)>>
  qmatch_asmsub_rename_tac`parse_cnf_ext_toks _ = SOME res`>>
  `∃mv ncl fml. res = (mv,ncl,fml)` by metis_tac[PAIR]>>
  gvs[SUM_TYPE_def,PAIR_TYPE_def]>>
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

(* Separates the options from the file names. b is the binary option,
  set by --binary and cleared by --no-binary; the last one given wins.
  d is set by --dump. A bare -- ends the options; any other argument
  starting with -- before it is unknown and gives NONE. *)
Definition split_flags_def:
  split_flags (b,d) [] = (SOME (b,d), []) ∧
  split_flags (b,d) (a::as) =
    if a = «--» then (SOME (b,d), as)
    else if a = «--binary» then split_flags (T,d) as
    else if a = «--no-binary» then split_flags (F,d) as
    else if a = «--dump» then split_flags (b,T) as
    else if isPrefix «--» a then (NONE, [])
    else
      case split_flags (b,d) as of (r, ps) => (r, a::ps)
End

val _ = translate split_flags_def;

Theorem split_flags_MEM:
  ∀as bd r ps x. split_flags bd as = (r, ps) ∧ MEM x ps ⇒ MEM x as
Proof
  Induct>>
  rpt gen_tac>>
  PairCases_on`bd`>>
  rw[split_flags_def]>>
  gvs[]
  >~ [`¬isPrefix _ _`]
  >- (
    Cases_on`split_flags (bd0,bd1) as`>>
    gvs[]>>
    qpat_x_assum`∀bd r ps x. _`drule_all>>
    simp[])>>
  qpat_x_assum`∀bd r ps x. _`drule_all>>
  simp[]
QED

Quote add_cakeml:
  fun check_unsat u =
  case split_flags (True,False) (CommandLine.arguments ()) of
    (Some (b,True), [f1]) => check_unsat_1 f1
  | (Some (b,False), [f1]) => check_unsat_stdin f1 b
  | (Some (b,False), [f1,f2]) => check_unsat_2 f1 f2 b
  | _ => TextIO.output TextIO.stdErr (mk_usage_string usage_string)
End

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 out ⇔
  (out ≠ «» ⇒
    out = «s VERIFIED UNSAT\n» ∧
    ∃fml. get_cnf_ext fs f1 = SOME fml ∧ sols fml = {})
End

Theorem run_xlrup_lines_sound:
  parse_cnf_ext_toks (MAP toks ls) = SOME (mv,ncl,cfml,xfml) ∧
  run_xlrup_lines b (build_xorig_map xfml)
    (build_cfml_list 1 (conv_cfml cfml) (2*ncl))
    (REPLICATE ncl NONE) ([],1) 0 (REPLICATE (mv+1) 0) 1 lines =
    SOME (cfml',xfml') ∧
  contains_emp_list cfml' ⇒
  sols (cfml,xfml) = {}
Proof
  rw[]>>
  Cases_on`b`>>
  gvs[run_xlrup_lines_def,parse_and_run_file_list_b_eq,
    parse_and_run_file_list_eq,AllCaseEqs()]>>
  qmatch_asmsub_rename_tac`check_xlrups_list _ _ _ _ _ _ _ _ = SOME res`>>
  PairCases_on`res`>>gvs[]>>
  imp_res_tac parse_xlrupsb_wf>>
  imp_res_tac parse_xlrups_wf>>
  `EVERY (EVERY nz_lit) cfml` by metis_tac[parse_cnf_ext_toks_nz_lit]>>
  irule check_xlrups_unsat_list_sound>>
  simp[check_xlrups_unsat_list_def]>>
  qexistsl_tac
    [`0`,`1`,`mv+1`,`2*ncl`,`ncl`,`xlrups`,`build_xorig_map xfml`]>>
  simp[FDOM_build_xorig_map]
QED

Theorem check_unsat_2_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  STRING_TYPE f2 f2v ∧ validArg f2 ∧
  BOOL b bv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_2"(get_ml_prog_state()))
    [f1v; f2v; bv]
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
  simp[check_unsat_2_sem_def,get_cnf_ext_def,parse_cnf_ext_def]>>
  reverse (Cases_on`inFS_fname fs f1`)>>fs[SUM_TYPE_def]
  >- (
    xmatch>>err_tac all_tac)>>
  Cases_on`parse_cnf_ext_toks (MAP toks (all_lines_file fs f1))`>>
  fs[SUM_TYPE_def]
  >- (
    xmatch>>err_tac all_tac)>>
  qmatch_asmsub_rename_tac`parse_cnf_ext_toks _ = SOME res`>>
  PairCases_on`res`>>
  gvs[SUM_TYPE_def,PAIR_TYPE_def]>>
  rename1`parse_cnf_ext_toks _ = SOME (mv,ncl,cfml,xfml)`>>
  xmatch>>
  rpt xlet_autop>>
  xlet`POSTv v.
    STDIO fs *
    SEP_EXISTS res.
      &(SUM_TYPE STRING_TYPE BOOL res v ∧
        (res = INR T ⇒ sols (cfml,xfml) = {}))`
  >- (
    xapp>>
    xsimpl>>
    qmatch_asmsub_rename_tac`_ = Conv NONE [tna; _]`>>
    qexistsl_tac
      [`emp`,`xfml`,`REPLICATE ncl NONE`,`1`,`[]`,`[]`,`tna`,`mv+1`,`fs`,`f2`,
       `build_cfml_list 1 (conv_cfml cfml) (2*ncl)`,`b`]>>
    xsimpl>>
    fs[FILENAME_def,validArg_def]>>
    rpt CONJ_TAC
    >- (
      irule bnd_fml_build_cfml_list>>
      irule bnd_clause_conv_cfml>>
      drule parse_cnf_ext_toks_bound>>
      rw[EVERY_MEM]>>res_tac>>simp[])
    >- metis_tac[LIST_REL_REPLICATE_same,OPTION_TYPE_def]
    >- (simp[PAIR_TYPE_def]>>EVAL_TAC)>>
    rw[]>>
    first_x_assum (irule_at Any)>>
    rw[]>>
    gvs[AllCaseEqs(),run_xlrup_file_lines]>>
    irule run_xlrup_lines_sound>>
    metis_tac[])>>
  namedCases_on`res` ["err","r"]>>fs[SUM_TYPE_def]
  >- (
    xmatch>>err_tac no_out)>>
  xmatch>>
  xif
  >- (
    xapp_spec print_spec>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`«s VERIFIED UNSAT\n»`>>
    qexists_tac`«»`>>
    simp[STD_streams_stderr,add_stdo_nil]>>
    xsimpl)>>
  xapp_spec output_stderr_spec>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`«»`>>
  qexists_tac`«c empty clause not derived at end of proof\n»`>>
  fs[STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
  xsimpl
QED

Theorem check_unsat_stdin_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  BOOL b bv ∧
  hasFreeFD fs ∧
  stdin_content fs = SOME text
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_stdin"(get_ml_prog_state()))
    [f1v; bv]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS k out err.
      STDIO (add_stdout (add_stderr (forwardFD fs 0 k) err) out) *
      &(check_unsat_2_sem fs f1 out))
Proof
  rw[]>>
  xcf "check_unsat_stdin" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def]>>xpull)>>
  xlet_autop>>
  simp[check_unsat_2_sem_def,get_cnf_ext_def,parse_cnf_ext_def]>>
  reverse (Cases_on`inFS_fname fs f1`)>>fs[SUM_TYPE_def]
  >- (
    xmatch>>err_tac (qexists_tac`0`))>>
  Cases_on`parse_cnf_ext_toks (MAP toks (all_lines_file fs f1))`>>
  fs[SUM_TYPE_def]
  >- (
    xmatch>>err_tac (qexists_tac`0`))>>
  qmatch_asmsub_rename_tac`parse_cnf_ext_toks _ = SOME res`>>
  PairCases_on`res`>>
  gvs[SUM_TYPE_def,PAIR_TYPE_def]>>
  rename1`parse_cnf_ext_toks _ = SOME (mv,ncl,cfml,xfml)`>>
  xmatch>>
  rpt xlet_autop>>
  xlet`POSTv v.
    SEP_EXISTS k res.
      STDIO (forwardFD fs 0 k) *
      &(SUM_TYPE STRING_TYPE BOOL res v ∧
        (res = INR T ⇒ sols (cfml,xfml) = {}))`
  >- (
    xapp_spec check_unsat_stdin'_spec>>
    xsimpl>>
    qmatch_asmsub_rename_tac`_ = Conv NONE [tna; _]`>>
    qexistsl_tac
      [`emp`,`xfml`,`REPLICATE ncl NONE`,`1`,`[]`,`[]`,`tna`,`text`,`mv+1`,
       `fs`,`build_cfml_list 1 (conv_cfml cfml) (2*ncl)`,`b`]>>
    xsimpl>>
    rpt CONJ_TAC
    >- (
      irule bnd_fml_build_cfml_list>>
      irule bnd_clause_conv_cfml>>
      drule parse_cnf_ext_toks_bound>>
      rw[EVERY_MEM]>>res_tac>>simp[])
    >- metis_tac[LIST_REL_REPLICATE_same,OPTION_TYPE_def]
    >- (simp[PAIR_TYPE_def]>>EVAL_TAC)>>
    rpt strip_tac>>
    qmatch_goalsub_rename_tac`STDIO (forwardFD fs 0 kk) ==>> _`>>
    qexists_tac`kk`>>
    first_assum (irule_at Any)>>
    xsimpl>>
    rw[AllCaseEqs()]>>
    irule run_xlrup_lines_sound>>
    metis_tac[])>>
  `STD_streams (forwardFD fs 0 k)` by simp[STD_streams_forwardFD]>>
  namedCases_on`res` ["err","r"]>>fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexistsl_tac[`emp`,`forwardFD fs 0 k`]>>xsimpl>>
    rw[]>>
    qexistsl_tac[`k`,`«»`,`err`]>>
    fs[STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  xmatch>>
  xif
  >- (
    xapp_spec print_spec>>xsimpl>>
    qexistsl_tac[`emp`,`forwardFD fs 0 k`]>>xsimpl>>
    rw[]>>
    qexistsl_tac[`k`,`«s VERIFIED UNSAT\n»`,`«»`]>>
    simp[STD_streams_stderr,add_stdo_nil]>>
    xsimpl)>>
  xapp_spec output_stderr_spec>>xsimpl>>
  qexistsl_tac[`emp`,`forwardFD fs 0 k`]>>xsimpl>>
  rw[]>>
  qexistsl_tac[`k`,`«»`,`«c empty clause not derived at end of proof\n»`]>>
  fs[STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
  xsimpl
QED

Definition check_unsat_sem_def:
  check_unsat_sem fs cl out ⇔
  case split_flags (T,F) (TL cl) of
    (SOME (b,T), [f1]) => check_unsat_1_sem fs f1 out
  | (SOME (b,F), [f1]) => check_unsat_2_sem fs f1 out
  | (SOME (b,F), [f1; f2]) => check_unsat_2_sem fs f1 out
  | _ => out = «»
End

(* The command lines on which the proof is read from stdin *)
Definition reads_stdin_def:
  reads_stdin cl ⇔ ∃b f1. split_flags (T,F) (TL cl) = (SOME (b,F), [f1])
End

Theorem BOOL_T_F_eq[local]:
  (BOOL T v ⇔ v = Conv (SOME (TypeStamp «True» 0)) []) ∧
  (BOOL F v ⇔ v = Conv (SOME (TypeStamp «False» 0)) [])
Proof
  simp[BOOL_def,semanticPrimitivesTheory.Boolv_def,
    semanticPrimitivesTheory.bool_type_num_def]
QED

Theorem check_unsat_spec:
   hasFreeFD fs ∧
   (reads_stdin cl ⇒ stdin_content fs ≠ NONE)
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"check_unsat"(get_ml_prog_state()))
     [Conv NONE []]
     (COMMANDLINE cl * STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv *
     COMMANDLINE cl *
     SEP_EXISTS k out err.
       STDIO (add_stdout (add_stderr (forwardFD fs 0 k) err) out) *
       &(check_unsat_sem fs cl out))
Proof
  rw[check_unsat_sem_def]>>
  xcf"check_unsat"(get_ml_prog_state())>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def]>>xpull)>>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def]>>xpull)>>
  rpt xlet_autop>>
  qmatch_asmsub_rename_tac`pv = Conv NONE [_; _]`>>
  `PAIR_TYPE BOOL BOOL (T,F) pv` by
    simp[PAIR_TYPE_def,BOOL_def,semanticPrimitivesTheory.Boolv_def,
      semanticPrimitivesTheory.bool_type_num_def]>>
  xlet_autop>>
  Cases_on`split_flags (T,F) (TL cl)`>>
  rename1`split_flags (T,F) (TL cl) = (fl,ps)`>>
  `∀x. MEM x ps ⇒ validArg x` by (
    rw[]>>
    drule_all split_flags_MEM>>
    Cases_on`cl`>>gvs[wfcl_def,EVERY_MEM])>>
  `ps = [] ∨ (∃f1. ps = [f1]) ∨ (∃f1 f2. ps = [f1; f2]) ∨
   (∃f1 f2 f3 rest. ps = f1::f2::f3::rest)` by (
    namedCases_on`ps` ["","f1 t1"]>>simp[]>>
    namedCases_on`t1` ["","f2 t2"]>>simp[]>>
    namedCases_on`t2` ["","f3 t3"]>>simp[])>>
  `fl = NONE ∨ (∃b. fl = SOME (b,T)) ∨ (∃b. fl = SOME (b,F))` by (
    namedCases_on`fl` ["","bd"]>>simp[]>>
    PairCases_on`bd`>>Cases_on`bd1`>>simp[])>>
  gvs[PAIR_TYPE_def,OPTION_TYPE_def,LIST_TYPE_def,BOOL_T_F_eq]>>
  xmatch
  >~ [`check_unsat_1_sem`]
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac [`COMMANDLINE cl`,`fs`,`f1`]>>
    xsimpl>>
    rw[]>>
    first_x_assum (irule_at Any)>>
    qmatch_goalsub_rename_tac`STDIO (add_stdout (add_stderr fs err) _) ==>> _`>>
    qexistsl_tac [`err`,`0`]>>
    simp[forwardFD_0]>>
    xsimpl)
  >~ [`split_flags _ _ = (SOME _, [_])`]
  >- (
    `reads_stdin cl` by (simp[reads_stdin_def]>>metis_tac[])>>
    `∃text. stdin_content fs = SOME text` by (Cases_on`stdin_content fs`>>gvs[])>>
    xapp>>
    xsimpl>>
    qexistsl_tac [`COMMANDLINE cl`,`fs`,`f1`,`text`,`b`]>>
    xsimpl>>
    rw[]>>
    first_x_assum (irule_at Any)>>
    qmatch_goalsub_rename_tac
      `STDIO (add_stdout (add_stderr (forwardFD fs 0 kk) ee) _) ==>> _`>>
    qexistsl_tac [`ee`,`kk`]>>
    xsimpl)
  >~ [`check_unsat_2_sem`]
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac [`COMMANDLINE cl`,`fs`,`f1`,`b`,`f2`]>>
    xsimpl>>
    rw[]>>
    first_x_assum (irule_at Any)>>
    qmatch_goalsub_rename_tac`STDIO (add_stdout (add_stderr fs err) _) ==>> _`>>
    qexistsl_tac [`err`,`0`]>>
    simp[forwardFD_0]>>
    xsimpl)>>
  assume_tac (theorem "usage_string_v_thm")>>
  xlet_autop>>
  xapp_spec output_stderr_spec>>xsimpl>>
  qexists_tac`COMMANDLINE cl`>>xsimpl>>
  qexists_tac`mk_usage_string usage_string`>>
  simp[]>>
  qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexistsl_tac [`0`,`mk_usage_string usage_string`]>>
  fs[forwardFD_0,STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
  xsimpl
QED

Theorem check_unsat_whole_prog_spec2:
   hasFreeFD fs ∧
   (reads_stdin cl ⇒ stdin_content fs ≠ NONE) ⇒
   whole_prog_spec2 check_unsat_v cl fs NONE
     (λfs'. ∃k out err.
        fs' = add_stdout (add_stderr (forwardFD fs 0 k) err) out ∧
        check_unsat_sem fs cl out)
Proof
  rw[basis_ffiTheory.whole_prog_spec2_def]>>
  match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH check_unsat_spec))))>>
  xsimpl>>
  rw[PULL_EXISTS]>>
  qmatch_goalsub_rename_tac
    `STDIO (add_stdout (add_stderr (forwardFD fs 0 kk) ee) oo)`>>
  qexistsl_tac [`add_stdout (add_stderr (forwardFD fs 0 kk) ee) oo`,
    `kk`,`oo`,`ee`]>>
  xsimpl>>
  simp[GSYM add_stdo_with_numchars,GSYM forwardFD_numchars,
    with_same_numchars]
QED

Theorem check_unsat_semantics =
  prove_sem_thm "check_unsat"
                "check_unsat_prog"
                check_unsat_whole_prog_spec2;
