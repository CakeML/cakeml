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

val _ = translate max_cnf_def;
val _ = translate print_cnf_def;
val _ = translate unconv_cfml_def;

Quote add_cakeml:
  fun check_unsat_1 f1 =
  case parse_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv,(ncl,vcfml)) =>
    let val f = unconv_cfml vcfml in
      TextIO.print_list (print_cnf (max_cnf f) f)
    end
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
    SOME fml => out = concat (print_cnf (max_cnf fml) fml)
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
