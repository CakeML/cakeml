(*
  WCNF encoder and checker
*)
open preamble basis lpr_parsingTheory wcnf_to_pbTheory npbc_parseProgTheory;
open cfLib basisFunctionsLib;

val _ = new_theory "wcnfProg";

val _ = translation_extends "npbc_parseProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

(* TODO: COPIED from lpr_arrayFullProgScript.sml *)
Theorem fastForwardFD_ADELKEY_same[simp]:
   forwardFD fs fd n with infds updated_by ADELKEY fd =
   fs with infds updated_by ADELKEY fd
Proof
  fs [forwardFD_def, IO_fs_component_equality]
QED

val _ = translate lpr_parsingTheory.blanks_def;
val _ = translate lpr_parsingTheory.tokenize_def;

val blanks_1_v_thm = theorem "blanks_1_v_thm";
val tokenize_v_thm = theorem "tokenize_v_thm";

val _ = translate parse_wclause_aux_def;
val _ = translate parse_wclause_def;

val parse_wclause_side = Q.prove(`
  parse_wclause_side x ⇔ T`,
  EVAL_TAC>>
  rw[]>>intLib.ARITH_TAC) |> update_precondition;

val _ = translate lpr_parsingTheory.nocomment_line_def;

val format_wcnf_failure_def = Define`
  format_wcnf_failure (lno:num) s =
  strlit "c wcnf parse failed at line: " ^ toString lno ^ strlit ". Reason: " ^ s ^ strlit"\n"`

val _ = translate format_wcnf_failure_def;

val b_inputLineTokens_specialize =
  b_inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`lpr_parsing$blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_1_v`
  |> Q.GEN `g` |> Q.ISPEC`lpr_parsing$tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_1_v_thm,tokenize_v_thm,blanks_def] ;

val parse_wcnf_toks_arr = process_topdecs`
  fun parse_wcnf_toks_arr lno fd acc =
  case TextIO.b_inputLineTokens fd blanks_1 tokenize of
    None => Inr (List.rev acc)
  | Some l =>
    if nocomment_line l then
      (case parse_wclause l of
        None => Inl (format_wcnf_failure lno "failed to parse line")
      | Some cl => parse_wcnf_toks_arr (lno+1) fd (cl::acc))
    else parse_wcnf_toks_arr (lno+1) fd acc` |> append_prog;

Theorem parse_wcnf_toks_arr_spec:
  !lines fd fdv fs acc accv lno lnov.
  NUM lno lnov ∧
  LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT)) acc accv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_wcnf_toks_arr" (get_ml_prog_state()))
    [lnov; fdv; accv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE (LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT)))
      (case parse_wcnf_toks (MAP lpr_parsing$toks lines) acc of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k))
Proof
  Induct
  \\ simp []
  \\ xcf "parse_wcnf_toks_arr" (get_ml_prog_state ())
  THEN1 (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac `emp`
      \\ qexists_tac ‘[]’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs [])
    \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
    \\ xmatch \\ fs []
    \\ simp[parse_wcnf_toks_def]
    \\ xlet_autop
    \\ xcon \\ xsimpl
    \\ simp[SUM_TYPE_def]
    \\ qexists_tac ‘k’ \\ xsimpl
    \\ qexists_tac `[]` \\ xsimpl)
  \\ xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES fd fdv lines (forwardFD fs fd k) *
                & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (lpr_parsing$toks h)) v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac `emp`
      \\ qexists_tac ‘h::lines’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
      \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
      \\ simp[lpr_parsingTheory.toks_def])
  \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
  \\ xmatch \\ fs []
  \\ xlet_autop
  \\ simp[parse_wcnf_toks_def]
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
  Cases_on`parse_wclause (lpr_parsing$toks h)`>>fs[OPTION_TYPE_def]
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

(* parse_wcnf_toks with simple wrapper *)
val parse_wcnf_full = (append_prog o process_topdecs) `
  fun parse_wcnf_full fname =
  let
    val fd = TextIO.b_openIn fname
    val res = parse_wcnf_toks_arr 0 fd []
    val close = TextIO.b_closeIn fd;
  in
    res
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)`;

Theorem parse_wcnf_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_wcnf_full"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. (SUM_TYPE STRING_TYPE
      (LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT)))
    (if inFS_fname fs f then
    (case parse_wcnf (all_lines fs f) of
      NONE => INL err
    | SOME x => INR x)
    else INL err) v)) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_wcnf_full"(get_ml_prog_state()) >>
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
      (xlet_auto_spec (SOME b_openIn_STDIO_spec) \\ xsimpl)
    >>
      fs[BadFileName_exn_def]>>
      xcases>>rw[]>>
      xlet_auto>>xsimpl>>
      xcon>>xsimpl>>
      simp[SUM_TYPE_def]>>metis_tac[])>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval` \\ xsimpl >>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec (SOME b_openIn_spec_lines) \\ xsimpl >>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES fdd fddv lines fss`>>
  xlet_autop>>
  xlet`(POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE (LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT)))
      (case parse_wcnf_toks (MAP lpr_parsing$toks lines) [] of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fss fdd k) * INSTREAM_LINES fdd fddv lines' (forwardFD fss fdd k))`
  >- (
    xapp>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`lines`>>
    qexists_tac`fss`>>qexists_tac`fdd`>>xsimpl>>
    qexists_tac`[]`>>rw[LIST_TYPE_def]>>
    qexists_tac`x`>>qexists_tac`x'`>>xsimpl>>
    metis_tac[])>>
  xlet `POSTv v. STDIO fs`
  >- (
    xapp_spec b_closeIn_spec_lines >>
    qexists_tac `emp`>>
    qexists_tac `lines'` >>
    qexists_tac `forwardFD fss fdd k` >>
    qexists_tac `fdd` >>
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
  fs[parse_wcnf_def]>>
  metis_tac[]
QED

(* Translate the encoder *)
val res = translate enc_lit_def;
val res = translate enc_clause_def;
val res = translate pbcTheory.negate_def;
val res = translate wclause_to_pbc_def;

val wclause_to_pbc_side = Q.prove(`
  wclause_to_pbc_side x <=> T`,
  EVAL_TAC>>rw[]>>
  fs[quantHeuristicsTheory.LIST_LENGTH_1])|>update_precondition;

val res = translate miscTheory.enumerate_def;
val res = translate wfml_to_pbf_def;

val res = translate enc_string_def;

val _ = translate pbcTheory.map_obj_def;
val _ = translate full_encode_def;

Definition sum_fst_def:
  sum_fst ls = SUM (MAP FST ls)
End

val _ = translate sum_fst_def;

(* parse input from f1 and run encoder into npbc *)
val parse_and_enc = (append_prog o process_topdecs) `
  fun parse_and_enc f1 =
  case parse_wcnf_full f1 of
    Inl err => Inl err
  | Inr wfml =>
    Inr (sum_fst wfml, full_encode wfml)`

Definition get_fml_def:
  get_fml fs f =
  if inFS_fname fs f then
    parse_wcnf (all_lines fs f)
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
         (PAIR_TYPE NUM (PAIR_TYPE
            (OPTION_TYPE (PAIR_TYPE
              (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
            INT))
            (LIST_TYPE (PAIR_TYPE PBC_PBOP_TYPE (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE))) INT)))
            )) res v ∧
       case res of
        INL err =>
          get_fml fs f1 = NONE
      | INR (n,objf) =>
        ∃wfml.
        get_fml fs f1 = SOME wfml ∧
        full_encode wfml = objf ∧
        sum_fst wfml = n)
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
    fs[get_fml_def])>>
  every_case_tac>>fs[SUM_TYPE_def]>>xmatch
  >- (
    xcon>>xsimpl>>
    qexists_tac`INL err`>>
    simp[SUM_TYPE_def]>>
    fs[get_fml_def])>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  rename1`_ (full_encode ff)`>>
  qexists_tac`INR (sum_fst ff,full_encode ff)`>>
  simp[SUM_TYPE_def,PAIR_TYPE_def,get_fml_def]
QED

(* Printing answer *)
Definition int_inf_to_string_def:
  (int_inf_to_string NONE = strlit "-INF") ∧
  (int_inf_to_string (SOME (i:num)) =
    toString i)
End

Definition print_maxsat_bound_def:
  print_maxsat_bound (lbg:num option,ubg:num option) =
  case lbg of
    NONE =>
    strlit "s VERIFIED MAX SAT BOUND " ^ strlit "sum(weights) <= " ^ int_inf_to_string ubg ^ strlit"\n"
  | SOME l =>
    strlit "s VERIFIED MAX SAT BOUND " ^ toString l ^ strlit " <= sum(weights) <= " ^ int_inf_to_string ubg ^ strlit"\n"
End

Definition maxsat_sem_def:
  maxsat_sem wfml (lbg,ubg) ⇔
  (case ubg of
    NONE => unsatisfiable_hard wfml
  | SOME ub => (∀w. satisfies_hard w wfml ⇒ weight w wfml ≤ ub)) ∧
  (case lbg of
    NONE => T
  | SOME lb =>
    ∃w. satisfies_hard w wfml ∧ lb ≤ weight w wfml)
End

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 out ⇔
  (out ≠ strlit"" ⇒
  ∃wfml bounds.
    get_fml fs f1 = SOME wfml ∧
    out = print_maxsat_bound bounds ∧
    maxsat_sem wfml bounds)
End

Definition map_concl_to_string_def:
  (map_concl_to_string n (INL s) = (INL s)) ∧
  (map_concl_to_string n (INR c) =
    case conv_concl n c of
      SOME bounds => INR (print_maxsat_bound bounds)
    | NONE => INL (strlit "c Unexpected conclusion for MAX SAT problem.\n"))
End

val res = translate iMAX_def;
val res = translate conv_concl_def;

val conv_concl_side = Q.prove(
  `∀x y. conv_concl_side x y <=> T`,
  EVAL_TAC>>
  rw[]>>
  intLib.ARITH_TAC) |> update_precondition;

val res = translate int_inf_to_string_def;
val res = translate print_maxsat_bound_def;
val res = translate map_concl_to_string_def;

val check_unsat_2 = (append_prog o process_topdecs) `
  fun check_unsat_2 f1 f2 =
  case parse_and_enc f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (n,objf) =>
    (case
      map_concl_to_string n
        (check_unsat_top_norm objf f2) of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr s => TextIO.print s)`

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
  Cases_on`y`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto
  >- (
    xsimpl>>
    fs[validArg_def]>>
    metis_tac[])>>
  xlet_autop>>
  every_case_tac>>gvs[SUM_TYPE_def]
  >- (
    fs[map_concl_to_string_def,SUM_TYPE_def]>>
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
  fs[map_concl_to_string_def]>>
  every_case_tac>>fs[SUM_TYPE_def]>>xmatch
  >- (
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`strlit ""`>>
    rename1`add_stderr _ err`>>
    qexists_tac`err`>>xsimpl>>rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>simp[]>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`print_maxsat_bound x`>>simp[]>>
    qexists_tac`strlit ""`>>
    simp[STD_streams_stderr,add_stdo_nil]>>
    xsimpl>>
    rw[]>>
    (drule_at Any) full_encode_sem_concl>>
    fs[sum_fst_def]>>
    Cases_on`x`>>disch_then (drule_at Any)>>
    simp[]>>
    rw[]>>
    qexists_tac`(q,r)`>>
    simp[maxsat_sem_def])
QED

Definition check_unsat_1_sem_def:
  check_unsat_1_sem fs f1 out ⇔
  case get_fml fs f1 of
    NONE => out = strlit ""
  | SOME wfml =>
    out = concat (print_pbf (full_encode wfml))
End

val check_unsat_1 = (append_prog o process_topdecs) `
  fun check_unsat_1 f1 =
  case parse_and_enc f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (n,objf) =>
    TextIO.print_list (print_pbf objf)`

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
  Cases_on`res`>>fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    rw[]>>
    qexists_tac`x`>>xsimpl)>>
  Cases_on`y`>>gvs[PAIR_TYPE_def]>>
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

Definition usage_string_def:
  usage_string = strlit "Usage: cake_pb_wcnf <wcnf file> <optional: PB proof file>\n"
End

val r = translate usage_string_def;

val main = (append_prog o process_topdecs) `
  fun main u =
  case CommandLine.arguments () of
    [f1] => check_unsat_1 f1
  | [f1,f2] => check_unsat_2 f1 f2
  | _ => TextIO.output TextIO.stdErr usage_string`

Definition main_sem_def:
  main_sem fs cl out =
  if LENGTH cl = 2 then
    check_unsat_1_sem fs (EL 1 cl) out
  else if LENGTH cl = 3 then
    check_unsat_2_sem fs (EL 1 cl) out
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
    xapp_spec output_stderr_spec \\ xsimpl>>
    rename1`COMMANDLINE cl`>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `usage_string` >>
    simp [theorem "usage_string_v_thm"] >>
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
  xapp_spec output_stderr_spec \\ xsimpl>>
  rename1`COMMANDLINE cl`>>
  qexists_tac`COMMANDLINE cl`>>xsimpl>>
  qexists_tac `usage_string` >>
  simp [theorem "usage_string_v_thm"] >>
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
val main_prog_def = Define`main_prog = ^prog_tm`;

in

Theorem main_semantics =
  sem_thm
  |> REWRITE_RULE[GSYM main_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[GSYM CONJ_ASSOC,AND_IMP_INTRO];

end

val _ = export_theory();
