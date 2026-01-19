(*
  WCNF encoder and checker
*)
Theory wcnfProg
Ancestors
  basis_ffi lpr_parsing wcnf_to_pb npbc_parseProg
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

val _ = translate lpr_parsingTheory.blanks_def;
val _ = translate lpr_parsingTheory.tokenize_def;

val blanks_1_v_thm = theorem "blanks_1_v_thm";
val tokenize_1_v_thm = theorem "tokenize_1_v_thm";

val _ = translate parse_wclause_aux_def;
val _ = translate parse_wclause_def;

val parse_wclause_side = Q.prove(`
  parse_wclause_side x ⇔ T`,
  EVAL_TAC>>
  rw[]>>intLib.ARITH_TAC) |> update_precondition;

val _ = translate wnocomment_line_def;

Definition format_wcnf_failure_def:
  format_wcnf_failure (lno:num) s =
  strlit "c wcnf parse failed at line: " ^ toString lno ^ strlit ". Reason: " ^ s ^ strlit"\n"
End

val _ = translate format_wcnf_failure_def;

val inputLineTokens_specialize =
  inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`lpr_parsing$blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_1_v`
  |> Q.GEN `g` |> Q.ISPEC`lpr_parsing$tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_1_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_1_v_thm,tokenize_1_v_thm,blanks_def] ;

Quote add_cakeml:
  fun parse_wcnf_toks_arr lno fd acc =
  case TextIO.inputLineTokens #"\n" fd blanks_1 tokenize_1 of
    None => Inr (List.rev acc)
  | Some l =>
    if wnocomment_line l then
      (case parse_wclause l of
        None => Inl (format_wcnf_failure lno "failed to parse line")
      | Some cl => parse_wcnf_toks_arr (lno+1) fd (cl::acc))
    else parse_wcnf_toks_arr (lno+1) fd acc
End

Theorem parse_wcnf_toks_arr_spec:
  !lines fd fdv fs acc accv lno lnov.
  NUM lno lnov ∧
  LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT)) acc accv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_wcnf_toks_arr" (get_ml_prog_state()))
    [lnov; fdv; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE (LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT)))
      (case parse_wcnf_toks (MAP lpr_parsing$toks lines) acc of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))
Proof
  Induct
  \\ simp []
  \\ rw[]
  \\ xcf "parse_wcnf_toks_arr" (get_ml_prog_state ())
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
    \\ simp[parse_wcnf_toks_def]
    \\ xlet_autop
    \\ xcon \\ xsimpl
    \\ simp[SUM_TYPE_def]
    \\ qexists_tac ‘k’ \\ xsimpl
    \\ qexists_tac `[]` \\ xsimpl)
  \\ xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
                & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (lpr_parsing$toks h)) v)’
    THEN1 (
      xapp_spec inputLineTokens_specialize
      \\ qexists_tac `emp`
      \\ qexists_tac ‘h::lines’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
      \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
      \\ simp[lpr_parsingTheory.toks_def])
  \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
  \\ xmatch \\ fs []
  \\ xlet_auto
  >-
    xsimpl
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
Quote add_cakeml:
  fun parse_wcnf_full fname =
  let
    val fd = TextIO.openIn fname
    val res = parse_wcnf_toks_arr 1 fd []
    val close = TextIO.closeIn fd;
  in
    res
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)
End

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
    (case parse_wcnf (all_lines_file fs f) of
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
      & (∃err. SUM_TYPE STRING_TYPE (LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT)))
      (case parse_wcnf_toks (MAP lpr_parsing$toks lines) [] of
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
  fs[parse_wcnf_def]>>
  metis_tac[]
QED

(* Translate the encoder *)
val res = translate enc_lit_def;
val res = translate enc_clause_def;
val res = translate pbcTheory.negate_def;
val res = translate (nub_def |> SIMP_RULE std_ss [MEMBER_INTRO]);
val res = translate wclause_to_pbc_def;

val wclause_to_pbc_side = Q.prove(`
  wclause_to_pbc_side x <=> T`,
  EVAL_TAC>>rw[]>>
  CCONTR_TAC>>fs[]) |>update_precondition;

val res = translate miscTheory.enumerate_def;
val res = translate wfml_to_pbf_def;

val res = translate enc_string_def;

val _ = translate full_encode_def;

(* parse input from f1 and run encoder into npbc *)
Quote add_cakeml:
  fun parse_and_enc f1 =
  case parse_wcnf_full f1 of
    Inl err => Inl err
  | Inr wfml =>
    Inr (full_encode wfml)
End

Definition get_fml_def:
  get_fml fs f =
  if inFS_fname fs f then
    parse_wcnf (all_lines_file fs f)
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
            (OPTION_TYPE (PAIR_TYPE
              (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
            INT))
            (LIST_TYPE (PAIR_TYPE PBC_PBOP_TYPE (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE))) INT)))
            ) res v ∧
       case res of
        INL err =>
          get_fml fs f1 = NONE
      | INR objf =>
        ∃wfml.
        get_fml fs f1 = SOME wfml ∧
        full_encode wfml = objf)
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
  qexists_tac`INR (full_encode ff)`>>
  simp[SUM_TYPE_def,PAIR_TYPE_def,get_fml_def]
QED

(* For MAX SAT, we support a few conclusions:

  - NONE: no conclusion

  - ubg = NONE:
    the upper bound is -INF, i.e., hard clauses are unsatisfiable

  - ubg = lbg:
    the lower bound and upper bound are equal, i.e., an exact sol

  - no lower bound:
    only an upper bound was proved

  - lower ≤ upper:
    respective bounds on the max sat solution *)
Definition maxsat_sem_def:
  maxsat_sem wfml copt ⇔
  case copt of NONE => T
  | SOME (lbg,ubg) =>
  (case lbg of
    NONE => opt_cost wfml = NONE
  | SOME lb =>
    (case ubg of
      NONE => (∀w. sat_hard w wfml ⇒ lb ≤ cost w wfml)
    | SOME ub =>
      if lb = ub then
        opt_cost wfml = SOME lb
      else
      (∀w. sat_hard w wfml ⇒ lb ≤ cost w wfml) ∧
      (∃w. sat_hard w wfml ∧ cost w wfml ≤ ub)))
End

Definition print_maxsat_str_def:
  print_maxsat_str copt =
  case copt of NONE => strlit "s VERIFIED NO CONCLUSION\n"
  | SOME (lbg:num option,ubg:num option) =>
  (case ubg of
    NONE => strlit "s VERIFIED UNSATISFIABLE"
  | SOME ub =>
    (case lbg of
      NONE =>
        strlit "s VERIFIED BOUNDS " ^
        strlit "COST <= " ^ toString ub ^ strlit"\n"
    | SOME lb =>
      if lb = ub then
        strlit "s VERIFIED OPTIMAL COST = " ^
        toString ub ^ strlit"\n"
      else
        strlit "s VERIFIED " ^
        (toString lb) ^
        strlit " <= COST <= " ^ toString ub ^ strlit"\n"))
End

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 out ⇔
  (out ≠ strlit"" ⇒
  ∃wfml bounds.
    get_fml fs f1 = SOME wfml ∧
    out = print_maxsat_str bounds ∧
    maxsat_sem wfml bounds)
End

Definition map_concl_to_string_def:
  (map_concl_to_string (INL s) = (INL s)) ∧
  (map_concl_to_string (INR (out,bnd,c)) =
    case conv_concl c of
      SOME bounds => INR (print_maxsat_str bounds)
    | NONE => INL (strlit "c Unexpected conclusion type\n"))
End

val res = translate nn_int_def;
val res = translate conv_concl_def;

val conv_concl_side = Q.prove(
  `∀y. conv_concl_side y <=> T`,
  EVAL_TAC>>
  rw[]>>
  intLib.ARITH_TAC) |> update_precondition;

val res = translate print_maxsat_str_def;
val res = translate map_concl_to_string_def;

Definition mk_prob_def:
  mk_prob objf = (NONE,objf):mlstring list option #
    ((int # mlstring pbc$lit) list # int) option #
    (pbop # (int # mlstring pbc$lit) list # int) list
End

val res = translate mk_prob_def;

Quote add_cakeml:
  fun check_unsat_2 f1 f2 =
  case parse_and_enc f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr objf =>
    let val probt = default_prob in
      (case
        map_concl_to_string
        (check_unsat_top_norm False (mk_prob objf) probt f2) of
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
  assume_tac default_prob_v_thm>>
  xlet`POSTv v.
    STDIO fs *
    &prob_TYPE default_prob v`
  >-
    (xvar>>xsimpl)>>
  xlet_autop>>
  xlet`POSTv v. STDIO fs * &BOOL F v`
  >-
    (xcon>>xsimpl)>>
  drule npbc_parseProgTheory.check_unsat_top_norm_spec>>
  qpat_x_assum`prob_TYPE (mk_prob _) _`assume_tac>>
  disch_then drule>>
  qpat_x_assum`prob_TYPE default_prob _`assume_tac>>
  disch_then drule>>
  strip_tac>>
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
    qexists_tac`print_maxsat_str x`>>simp[]>>
    qexists_tac`strlit ""`>>
    simp[STD_streams_stderr,add_stdo_nil]>>
    xsimpl>>
    rw[]>>
    qexists_tac`x`>>simp[maxsat_sem_def]>>
    every_case_tac>>fs[mk_prob_def]
    >- (
      (drule_at Any) full_encode_sem_concl_opt_cost>>
      metis_tac[PAIR])
    >- (
      (drule_at Any) full_encode_sem_concl>>
      fs[]>>
      disch_then (drule_at Any)>>simp[])
    >- (
      (drule_at Any) full_encode_sem_concl_opt_cost>>
      metis_tac[PAIR])
    >- (
      (drule_at Any) full_encode_sem_concl_opt_cost>>
      metis_tac[PAIR])
    >- (
      (drule_at Any) full_encode_sem_concl>>
      fs[]>>
      disch_then (drule_at Any)>>simp[]))
QED

Definition check_unsat_1_sem_def:
  check_unsat_1_sem fs f1 out ⇔
  case get_fml fs f1 of
    NONE => out = strlit ""
  | SOME wfml =>
    out = concat (print_prob (mk_prob (full_encode wfml)))
End

Quote add_cakeml:
  fun check_unsat_1 f1 =
  case parse_and_enc f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr objf =>
    TextIO.print_list (print_prob (mk_prob objf))
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
  xlet_autop>>
  xapp_spec print_list_spec>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`strlit ""`>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl
QED

Definition maxsat_output_sem_def:
  maxsat_output_sem wfml wfml' iseqopt ⇔
  (iseqopt ⇒ opt_cost wfml = opt_cost wfml')
End

Definition print_maxsat_output_str_def:
  print_maxsat_output_str iseqopt =
  if iseqopt
  then strlit "s VERIFIED OUTPUT EQUIOPTIMAL\n"
  else strlit "s VERIFIED NO OUTPUT CLAIM\n"
End

Definition check_unsat_3_sem_def:
  check_unsat_3_sem fs f1 f3 out ⇔
  (out ≠ strlit"" ⇒
  ∃wfml wfmlt bounds iseqopt.
    get_fml fs f1 = SOME wfml ∧
    get_fml fs f3 = SOME wfmlt ∧
    out = print_maxsat_str bounds ^
          print_maxsat_output_str iseqopt ∧
    maxsat_sem wfml bounds ∧
    maxsat_output_sem wfml wfmlt iseqopt)
End

Definition map_out_concl_to_string_def:
  (map_out_concl_to_string (INL s) = (INL s)) ∧
  (map_out_concl_to_string (INR (out,bnd,c)) =
  case conv_concl c of
    NONE => INL (strlit "c Unexpected conclusion type\n")
  | SOME bounds =>
    (case conv_output bnd out of
      NONE => INL (strlit "c Unexpected output type\n")
    | SOME iseqopt =>
        INR (print_maxsat_str bounds ^
            print_maxsat_output_str iseqopt )))
End

val res = translate conv_output_def;
val res = translate print_maxsat_output_str_def;
val res = translate map_out_concl_to_string_def;

Quote add_cakeml:
  fun check_unsat_3 f1 f2 f3 =
  case parse_and_enc f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr objf =>
  (case parse_and_enc f3 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr objft =>
      (case
      map_out_concl_to_string
        (check_unsat_top_norm True (mk_prob objf) (mk_prob objft) f2) of
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
  xlet_autop>>
  xlet_autop>>
  xlet`POSTv v. STDIO fs * &BOOL T v`
  >-
    (xcon>>xsimpl)>>
  xlet_auto
  >- (
    xsimpl>>
    fs[validArg_def]>>
    metis_tac[])>>
  xlet_autop>>
  every_case_tac>>gvs[SUM_TYPE_def]
  >- (
    fs[map_out_concl_to_string_def,SUM_TYPE_def]>>
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
  fs[map_out_concl_to_string_def]>>
  qpat_x_assum`SUM_TYPE _ _ _ _` mp_tac>>
  TOP_CASE_TAC>>simp[SUM_TYPE_def]
  >- (
    rw[]>>xmatch>>
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
  TOP_CASE_TAC>>simp[SUM_TYPE_def]
  >- (
    rw[]>>xmatch>>
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
  rw[]>>xmatch>>
  xapp>>xsimpl>>
  asm_exists_tac>>simp[]>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`print_maxsat_str x ^ print_maxsat_output_str x'`>>
  simp[]>>
  qexists_tac`strlit ""`>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl>>
  rw[]>>
  qexists_tac`x`>>qexists_tac`x'`>>simp[maxsat_output_sem_def]>>
  CONJ_TAC >- (
    fs[maxsat_sem_def,mk_prob_def]>>
    every_case_tac>>fs[]
    >- (
      (drule_at Any) full_encode_sem_concl_opt_cost>>
      metis_tac[PAIR])
    >- (
      (drule_at Any) full_encode_sem_concl>>
      fs[]>>
      disch_then (drule_at Any)>>simp[])
    >- (
      (drule_at Any) full_encode_sem_concl_opt_cost>>
      metis_tac[PAIR])
    >- (
      (drule_at Any) full_encode_sem_concl_opt_cost>>
      metis_tac[PAIR])
    >- (
      (drule_at Any) full_encode_sem_concl>>
      fs[]>>
      disch_then (drule_at Any)>>simp[]))>>
  rw[]>>fs[mk_prob_def]>>
  (drule_at Any) full_encode_sem_output_opt_cost>>
  disch_then irule>>
  gvs[mk_prob_def,pbcTheory.pres_set_list_def]>>
  metis_tac[PAIR]
QED

Definition usage_string_def:
  usage_string = strlit "Usage: cake_pb_wcnf <wcnf file> <optional: PB proof file> <optional: wcnf output file>\n"
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
    rename1`wfcl [a1;a2;a3;a4]`>>
    qexists_tac`COMMANDLINE [a1; a2; a3; a4]`>>
    qexists_tac`fs`>>
    simp[PULL_EXISTS]>>
    qexists_tac`a4`>>qexists_tac`a2`>>qexists_tac`a3`>>
    fs[wfcl_def]>>xsimpl>>
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
