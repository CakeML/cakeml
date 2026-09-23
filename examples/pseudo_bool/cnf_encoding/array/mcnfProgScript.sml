(*
  MCNF (multi-objective MaxSAT) encoder and checker
*)
Theory mcnfProg
Ancestors
  basis_ffi cnf syntax_helper pbc_mo wcnf_to_pb mcnf_to_pb npbc_mo_arrayProg
Libs
  preamble basis cfLib basisFunctionsLib

val _ = translation_extends "npbc_mo_arrayProg";

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

val _ = translate mk_lit_def;
val _ = translate parse_until_zero_aux_def;
val _ = translate parse_until_zero_def;

Overload "mcclause_TYPE" = ``
  PAIR_TYPE NUM (PAIR_TYPE NUM (LIST_TYPE (CNF_LIT_TYPE NUM)))``

val _ = translate parse_mclause_def;

val parse_mclause_side = Q.prove(`
  parse_mclause_side x ⇔ T`,
  EVAL_TAC>>
  rw[]>>intLib.ARITH_TAC) |> update_precondition;

val _ = translate wnocomment_line_def;

Definition format_mcnf_failure_def:
  format_mcnf_failure (lno:num) s =
  «c mcnf parse failed at line: » ^ toString lno ^ «. Reason: » ^ s ^ «\n»
End

val _ = translate format_mcnf_failure_def;

val inputLineTokens_specialize =
  inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`syntax_helper$blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_1_v`
  |> Q.GEN `g` |> Q.ISPEC`syntax_helper$tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_1_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_1_v_thm,tokenize_1_v_thm,blanks_def] ;

Quote add_cakeml:
  fun parse_mcnf_toks_arr lno fd acc =
  case TextIO.inputLineTokens #"\n" fd blanks_1 tokenize_1 of
    None => Inr (List.rev acc)
  | Some l =>
    if wnocomment_line l then
      (case parse_mclause l of
        None => Inl (format_mcnf_failure lno "failed to parse line")
      | Some cl => parse_mcnf_toks_arr (lno+1) fd (cl::acc))
    else parse_mcnf_toks_arr (lno+1) fd acc
End

Theorem parse_mcnf_toks_arr_spec:
  !lines fd fdv fs acc accv lno lnov.
  NUM lno lnov ∧
  LIST_TYPE mcclause_TYPE acc accv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_mcnf_toks_arr" (get_ml_prog_state()))
    [lnov; fdv; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE (LIST_TYPE mcclause_TYPE)
      (case parse_mcnf_toks (MAP syntax_helper$toks lines) acc of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))
Proof
  Induct
  \\ simp []
  \\ rw[]
  \\ xcf "parse_mcnf_toks_arr" (get_ml_prog_state ())
  THEN1 (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    THEN1 (
      xapp_spec inputLineTokens_specialize
      \\ qexists_tac `emp`
      \\ qexists_tac ‘[]’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs [])
    \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
    \\ xmatch \\ fs []
    \\ simp[parse_mcnf_toks_def]
    \\ xlet_autop
    \\ xcon \\ xsimpl
    \\ simp[SUM_TYPE_def]
    \\ qexists_tac ‘k’ \\ xsimpl
    \\ qexists_tac `[]` \\ xsimpl)
  \\ xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
                & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (syntax_helper$toks h)) v)’
    THEN1 (
      xapp_spec inputLineTokens_specialize
      \\ qexists_tac `emp`
      \\ qexists_tac ‘h::lines’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
      \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
      \\ simp[syntax_helperTheory.toks_def])
  \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
  \\ xmatch \\ fs []
  \\ xlet_auto
  >-
    xsimpl
  \\ simp[parse_mcnf_toks_def]
  \\ reverse xif
  >- (
    xlet_autop>>
    xapp>> xsimpl>>
    asm_exists_tac>> simp[]>>
    asm_exists_tac>> simp[]>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>xsimpl>>
    rw[]>>
    qexists_tac`k+x`>>
    simp[GSYM fsFFIPropsTheory.forwardFD_o]>>
    qexists_tac`x'`>>xsimpl>>
    metis_tac[])>>
  simp[]>>
  xlet_autop>>
  Cases_on`parse_mclause (syntax_helper$toks h)`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>
    xsimpl>>
    qexists_tac`k`>> qexists_tac`lines`>>xsimpl>>
    simp[SUM_TYPE_def]>>
    metis_tac[])>>
  xmatch>>
  xlet_autop>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  asm_exists_tac>>simp[]>>
  qexists_tac`emp`>>
  qexists_tac`forwardFD fs fd k`>>
  qexists_tac`fd`>>
  qexists_tac`x::acc`>>
  xsimpl>>
  simp[LIST_TYPE_def]>>rw[]>>
  qexists_tac`k+x'`>>
  qexists_tac`x''`>>
  simp[GSYM fsFFIPropsTheory.forwardFD_o]>>
  xsimpl>>
  metis_tac[]
QED

Quote add_cakeml:
  fun parse_mcnf_full fname =
  let
    val fd = TextIO.openIn fname
    val res = parse_mcnf_toks_arr 1 fd []
    val close = TextIO.closeIn fd;
  in
    res
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)
End

Theorem parse_mcnf_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_mcnf_full"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. (SUM_TYPE STRING_TYPE
      (LIST_TYPE mcclause_TYPE)
    (if inFS_fname fs f then
    (case parse_mcnf (all_lines_file fs f) of
      NONE => INL err
    | SOME x => INR x)
    else INL err) v)) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_mcnf_full"(get_ml_prog_state()) >>
  fs[validArg_def]>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[]) >>
  reverse (Cases_on `inFS_fname fs f`) >> simp[]
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
      xcon>>xsimpl>>
      simp[SUM_TYPE_def]>>metis_tac[])>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval` \\ xsimpl >>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec (SOME (openIn_spec_lines |> Q.GEN `c0` |> Q.SPEC `#"\n"`)) \\ xsimpl >>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" fdd fddv lines fss`>>
  xlet_autop>>
  xlet`(POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE (LIST_TYPE mcclause_TYPE)
      (case parse_mcnf_toks (MAP syntax_helper$toks lines) [] of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fss fdd k) * INSTREAM_LINES #"\n" fdd fddv lines' (forwardFD fss fdd k))`
  >- (
    xapp>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`lines`>>
    qexists_tac`fss`>>qexists_tac`fdd`>>xsimpl>>
    qexists_tac`[]`>>rw[LIST_TYPE_def]>>
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
    conj_tac THEN1
     (unabbrev_all_tac
      \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
      \\ imp_res_tac fsFFIPropsTheory.STD_streams_nextFD \\ fs []) >>
    xsimpl>>
    `validFileFD fdd (forwardFD fss fdd k).infds` by
      (unabbrev_all_tac>> simp[validFileFD_forwardFD]
       \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
       \\ match_mp_tac validFileFD_nextFD \\ fs []) >>
    xsimpl >> rw [] >>
    imp_res_tac (DECIDE ``n<m:num ==> n <= m``) >>
    imp_res_tac fsFFIPropsTheory.nextFD_leX \\ fs [] >>
    drule fsFFIPropsTheory.openFileFS_ADELKEY_nextFD >>
    fs [Abbr`fss`]>>
    xsimpl)>>
  xvar>>
  xsimpl>>
  fs[parse_mcnf_def]>>
  metis_tac[]
QED

(* Translate the encoder *)
val res = translate enc_lit_def;
val res = translate enc_clause_def;
val res = translate pbcTheory.negate_def;
val res = translate lit_le_def;
val res = translate sorted_nub_aux_def;
val res = translate sorted_nub_def;
val res = translate canon_clause_def;
val res = translate miscTheory.enumerate_def;
val res = translate enc_string_def;

val res = translate mclause_cs_def;
val res = translate mclause_obj_def;

Theorem mclause_obj_side[local]:
  ∀x y. mclause_obj_side x y ⇔ T
Proof
  simp[fetch "-" "mclause_obj_side_def"]>>
  rw[]>>
  CCONTR_TAC>>
  `canon_clause [] = []` by simp[]>>
  gvs[]
QED

val _ = mclause_obj_side |> update_precondition;

val res = translate num_objs_def;
val res = translate pbc_moTheory.map_objs_def;
val res = translate (mfml_to_pbf_def |> SIMP_RULE std_ss [SUC_LEMMA]);
val res = translate full_encode_mcnf_def;

(* parse input from f1 and run the encoder into npbc *)
Quote add_cakeml:
  fun parse_and_enc f1 =
  case parse_mcnf_full f1 of
    Inl err => Inl err
  | Inr mfml =>
    Inr (full_encode_mcnf mfml)
End

Definition get_mfml_def:
  get_mfml fs f =
  if inFS_fname fs f then
    parse_mcnf (all_lines_file fs f)
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
       SUM_TYPE STRING_TYPE mo_prob_TYPE res v ∧
       case res of
        INL err =>
          get_mfml fs f1 = NONE
      | INR mprob =>
        ∃mfml.
        get_mfml fs f1 = SOME mfml ∧
        full_encode_mcnf mfml = mprob)
Proof
  rw[]>>
  xcf"parse_and_enc"(get_ml_prog_state())>>
  xlet_autop>>
  reverse (pop_assum mp_tac>>rw[])>>
  fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl>>
    qexists_tac`INL err`>>
    simp[SUM_TYPE_def]>>
    fs[get_mfml_def])>>
  every_case_tac>>fs[SUM_TYPE_def]>>xmatch
  >- (
    xcon>>xsimpl>>
    qexists_tac`INL err`>>
    simp[SUM_TYPE_def]>>
    fs[get_mfml_def])>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  rename1`_ (full_encode_mcnf ff)`>>
  qexists_tac`INR (full_encode_mcnf ff)`>>
  simp[SUM_TYPE_def,PAIR_TYPE_def,get_mfml_def]
QED

Definition mcnf_sem_def:
  mcnf_sem ord mfml vs ⇔ is_front ord vs (nondom_costs ord mfml)
End

Definition check_unsat_3_sem_def:
  check_unsat_3_sem fs ord f1 out ⇔
  (out ≠ «» ⇒
  ∃mfml vs.
    get_mfml fs f1 = SOME mfml ∧
    out = print_front_str ord vs ∧
    mcnf_sem ord mfml vs)
End

Quote add_cakeml:
  fun check_unsat_3 ord f1 f2 =
  case parse_and_enc f1 of
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
  Cases_on`res`>>fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`x`>>xsimpl>>rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
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
  qexists_tac`vs`>>
  simp[mcnf_sem_def]>>
  metis_tac[full_encode_mcnf_nondom,is_front_set_equiv,PAIR]
QED

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 out ⇔
  case get_mfml fs f1 of
    NONE => out = «»
  | SOME mfml =>
    out = concat (print_mo_prob (full_encode_mcnf mfml))
End

Quote add_cakeml:
  fun check_unsat_2 f1 =
  case parse_and_enc f1 of
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
  Cases_on`res`>>fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    rw[]>>
    qexists_tac`x`>>xsimpl)>>
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

Definition usage_string_def:
  usage_string = «Usage: cake_pb_mcnf <ordering: pareto> <mcnf file> <optional: PB proof file>\n»
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
  rename1`wfcl (prog::args)`>>
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
  rename1`wfcl (prog::ords::args)`>>
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
  rename1`wfcl (prog::ords::f1::args)`>>
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
  rename1`wfcl (prog::ords::f1::f2::args)`>>
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
