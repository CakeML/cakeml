(*
  This refines lrup_list to use arrays
*)
Theory lrup_arrayProg
Libs
  preamble basis
Ancestors
  ccnf_arrayProg lrup lrup_list syntax_helper fsFFIProps

val _ = hide_environments true;

val _ = translation_extends "ccnf_arrayProg";

val _ = register_type``:lrup``;

Quote add_cakeml:
  fun check_lrup_arr lno lrup fml carr b =
  case lrup of
    Skip => (fml,carr,b)
  | Del ls =>
      (delete_ids_arr fml ls; (fml,carr,b))
  | Lrup n v hints =>
      (case is_rup_arr lno fml carr b v hints of (dml,b) =>
      (Array.updateResize fml None n (Some v), dml,b))
  | _ =>
    raise Fail (format_failure lno ("vb not yet supported."))
End

val LRUP_LRUP_TYPE_def = fetch "-" "LRUP_LRUP_TYPE_def";

(* policy: throw away state (except STDIO-related) on exception *)
Theorem check_lrup_arr_spec:
  NUM lno lnov ∧
  LRUP_LRUP_TYPE lrup lrupv ∧
  LIST_REL (OPTION_TYPE vcclause_TYPE) fmlls fmllsv ∧
  WORD8 b bv ∧
  bnd_fml fmlls (LENGTH Clist)
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lrup_arr" (get_ml_prog_state()))
    [lnov; lrupv; fmlv; Carrv; bv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λres.
        SEP_EXISTS v1 v2 v3.
        SEP_EXISTS fmlls' fmllsv' b' Clist'.
        ARRAY v1 fmllsv' *
        W8ARRAY v2 Clist' *
        &(res = Conv NONE [v1; v2; v3] ∧
          LIST_REL (OPTION_TYPE vcclause_TYPE) fmlls' fmllsv' ∧
          WORD8 b' v3 ∧
          check_lrup_list lrup fmlls Clist b =
            SOME (fmlls', (Clist', b'))))
      (λe.
        &(Fail_exn e ∧ check_lrup_list lrup fmlls Clist b = NONE)))
Proof
  rw[check_lrup_list_def]>>
  xcf "check_lrup_arr" (get_ml_prog_state ())>>
  Cases_on`lrup`>>fs[LRUP_LRUP_TYPE_def]>>
  xmatch
  >- ( (* Skip *)
    xcon>>xsimpl)
  >- ( (* Del *)
    xlet_autop >>
    xcon>>xsimpl)
  >- ( (* Rup *)
    xlet `
      POSTve
        (λres.
             (SEP_EXISTS b' Carrv' Clist'.
                W8ARRAY Carrv' Clist' *
                &(PAIR_TYPE $= WORD8 (Carrv',b') res ∧
                 is_rup_list fmlls Clist b v l = (T,Clist',b'))) *
             ARRAY fmlv fmllsv)
        (λe.
            &(Fail_exn e ∧ ¬FST (is_rup_list fmlls Clist b v l)))`
    >- (
      xapp>>xsimpl>>
      rpt(first_x_assum (irule_at Any))>>
      simp[PAIR_TYPE_def]>>rw[]>>
      xsimpl)
    >- (
      xsimpl>>
      simp[AllCaseEqs()]>>
      Cases_on`is_rup_list fmlls Clist b v l`>>simp[])>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    irule LIST_REL_update_resize>>
    simp[OPTION_TYPE_def])
  >- (
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    metis_tac[W8ARRAY_refl,Fail_exn_def])
QED

(* Parser translation *)
val res = translate parse_rup_def;
val res = translate parse_lrup_def;

(* Uncompressed parsing.
  None = EOF
  Some line = proof step
  Exception = parse failure *)
Quote add_cakeml:
  fun parse_one_u lno fd =
  case TextIO.inputLineTokens #"\n" fd blanks tokenize_fast of
    None => None
  | Some l =>
      case parse_lrup l of
        None =>
          raise Fail (format_failure lno "failed to parse line (uncompressed format)")
      | Some lpr => Some lpr
End

val inputLineTokens_specialize =
inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize_fast`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_fast_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_v_thm,tokenize_fast_v_thm,blanks_def] ;

Theorem STDIO_INSTREAM_LINES_refl:
  STDIO A *
  INSTREAM_LINES c B C D E ==>>
  STDIO A *
  INSTREAM_LINES c B C D E ∧
  STDIO A *
  INSTREAM_LINES c B C D E ==>>
  STDIO A *
  INSTREAM_LINES c B C D E * GC
Proof
  xsimpl
QED

Theorem ARRAY_STDIO_INSTREAM_LINES_refl:
  ARRAY X Y *
  STDIO A *
  INSTREAM_LINES c B C D E ==>>
  STDIO A *
  INSTREAM_LINES c B C D E * ARRAY X Y
Proof
  xsimpl
QED

Theorem DW8ARRAY_STDIO_INSTREAM_LINES_refl:
  W8ARRAY X Y *
  STDIO A *
  INSTREAM_LINES c B C D E ==>>
  STDIO A *
  INSTREAM_LINES c B C D E * GC
Proof
  xsimpl
QED

Definition parse_one_u_def:
  parse_one_u lines =
  case lines of
    [] => SOME NONE
  | (x::xs) =>
    case parse_lrup (toks_fast x) of
      NONE => NONE
    | SOME l => SOME (SOME (l,xs))
End

Theorem parse_one_u_spec:
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
      ^(fetch_v "parse_one_u" (get_ml_prog_state()))
      [lnov; fdv]
      (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
      (POSTve
       (λv.
          SEP_EXISTS k lines' res.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
          &(parse_one_u lines = SOME res ∧
            OPTION_TYPE LRUP_LRUP_TYPE (OPTION_MAP FST res) v ∧
            (if res = NONE then lines' = [] else OPTION_MAP SND res = SOME lines')
          )
        )
       (λe.
          SEP_EXISTS k lines'.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
          &(Fail_exn e ∧ parse_one_u lines = NONE)))
Proof
  rw[parse_one_u_def]>>
  xcf "parse_one_u" (get_ml_prog_state ())>>
  Cases_on`lines`
  >- (
    xlet ‘(POSTv v.
           SEP_EXISTS k.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
           &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    THEN1 (
      xapp_spec inputLineTokens_specialize
      \\ qexists_tac ‘emp’
      \\ qexists_tac ‘[]’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs [])
    \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
    \\ xmatch \\ fs []
    \\ xcon \\ xsimpl
    \\ simp[oneline OPTION_TYPE_def,AllCasePreds()]
    \\ metis_tac[STDIO_INSTREAM_LINES_refl])
  \\ xlet ‘(POSTv v.
            SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES #"\n" fd fdv t (forwardFD fs fd k) *
            & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks_fast h)) v)’
  THEN1 (
    xapp_spec inputLineTokens_specialize
    \\ qexists_tac ‘emp’
    \\ qexists_tac ‘h::t’
    \\ qexists_tac ‘fs’
    \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
    \\ rw[toks_fast_def]
    \\ metis_tac[STDIO_INSTREAM_LINES_refl])
  \\ gvs[OPTION_TYPE_def]
  \\ xmatch
  \\ xlet_autop
  \\ Cases_on`parse_lrup (toks_fast h)`
  \\ gvs[OPTION_TYPE_def] \\ xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    gvs[Fail_exn_def]>>
    first_x_assum (irule_at Any)>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  xcon>>
  xsimpl>>
  simp[oneline OPTION_TYPE_def,AllCasePreds()]>>
  metis_tac[STDIO_INSTREAM_LINES_refl]
QED

(* Compressed parsing.
  None = EOF
  Some line = proof step
  Exception = parse failure *)
Definition c0_def:
  c0 = CHR 0
End

val c0_v_thm = translate c0_def;

Quote add_cakeml:
  fun parse_one_c lno fd =
  raise Fail (format_failure lno "TODO")
End

Definition parse_one_c_def:
  parse_one_c lines =
  case lines of
    [] => SOME NONE : (lrup # mlstring list) option option
  | (x::xs) => ARB
End

Theorem parse_one_c_spec:
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
      ^(fetch_v "parse_one_c" (get_ml_prog_state()))
      [lnov; fdv]
      (STDIO fs * INSTREAM_LINES c0 fd fdv lines fs)
      (POSTve
       (λv.
          SEP_EXISTS k lines' res.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES c0 fd fdv lines' (forwardFD fs fd k) *
          &(parse_one_c lines = SOME res ∧
            OPTION_TYPE LRUP_LRUP_TYPE (OPTION_MAP FST res) v ∧
            (if res = NONE then lines' = [] else OPTION_MAP SND res = SOME lines')
          )
        )
       (λe.
          SEP_EXISTS k lines'.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES c0 fd fdv lines' (forwardFD fs fd k) *
          &(Fail_exn e ∧ parse_one_c lines = NONE)))
Proof
  cheat
QED

Definition parse_one_def:
  parse_one b lines =
  if b
  then parse_one_c lines
  else parse_one_u lines
End

Quote add_cakeml:
  fun parse_one b lno fd =
  if b
  then parse_one_c lno fd
  else parse_one_u lno fd
End

Definition term_char_def:
  term_char b = (if b then c0 else #"\n")
End

Theorem parse_one_spec:
  BOOL b bv ∧
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
      ^(fetch_v "parse_one" (get_ml_prog_state()))
      [bv; lnov; fdv]
  (STDIO fs * INSTREAM_LINES (term_char b) fd fdv lines fs)
  (POSTve
   (λv.
      SEP_EXISTS k lines' res.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES (term_char b) fd fdv lines' (forwardFD fs fd k) *
      &(parse_one b lines = SOME res ∧
        OPTION_TYPE LRUP_LRUP_TYPE (OPTION_MAP FST res) v ∧
        (if res = NONE then lines' = [] else OPTION_MAP SND res = SOME lines')))
   (λe.
      SEP_EXISTS k lines'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES (term_char b) fd fdv lines' (forwardFD fs fd k) *
      &(Fail_exn e ∧ parse_one b lines = NONE)))
Proof
  rw[]>>
  xcf "parse_one" (get_ml_prog_state ())>>
  simp[term_char_def,parse_one_def]>>xif>>
  xapp>>
  rw[]>>xsimpl>>
  rpt (first_x_assum $ irule_at Any)>>
  irule_at Any (cj 2 STDIO_INSTREAM_LINES_refl)>>
  rw[]>>xsimpl>>
  metis_tac[STDIO_INSTREAM_LINES_refl]
QED

Theorem parse_one_less:
  parse_one b lines = SOME (SOME (fml, rest)) ⇒
  LENGTH rest < LENGTH lines
Proof
  rw[parse_one_def,parse_one_c_def,parse_one_u_def,AllCaseEqs()]>>
  simp[]>>
  cheat
QED

Definition run_checker_def:
  run_checker t lines fml Clist b =
  case parse_one t lines of
    NONE => NONE
  | SOME NONE => SOME fml
  | SOME (SOME (lrup,rest)) =>
      (case check_lrup_list lrup fml Clist b of
        NONE => NONE
      | SOME (fml', Clist', b') => run_checker t rest fml' Clist' b')
Termination
  WF_REL_TAC`measure (LENGTH o FST o SND)`>>
  rw[]>>
  metis_tac[parse_one_less]
End

(* The core checker loop *)
Quote add_cakeml:
  fun run_checker t fd lno fml carr b =
  case parse_one t lno fd of
    None => fml
  | Some lrup =>
    case check_lrup_arr lno lrup fml carr b of
      (fml',carr',b') =>
      run_checker t fd (lno+1) fml' carr' b'
End

(* Technically, we know that the checker will consume all
  lines *)
Theorem run_checker_spec:
  ∀t lines fmlls Clist b
    tv fmlv fmllsv lno lnov Carrv bv fs.
  BOOL t tv ∧
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE vcclause_TYPE) fmlls fmllsv ∧
  WORD8 b bv ∧
  bnd_fml fmlls (LENGTH Clist)
  ⇒
  app (p : 'ffi ffi_proj)
      ^(fetch_v "run_checker" (get_ml_prog_state()))
      [tv; fdv; lnov; fmlv; Carrv; bv]
  (STDIO fs * ARRAY fmlv fmllsv * W8ARRAY Carrv Clist *
    INSTREAM_LINES (term_char t) fd fdv lines fs)
  (POSTve
   (λv.
      SEP_EXISTS k lines'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES (term_char t) fd fdv lines' (forwardFD fs fd k) *
      SEP_EXISTS fmlls' fmllsv'.
        ARRAY v fmllsv' *
        &(run_checker t lines fmlls Clist b = SOME fmlls' ∧
          LIST_REL (OPTION_TYPE vcclause_TYPE) fmlls' fmllsv'))
   (λe.
      SEP_EXISTS k lines'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES (term_char t) fd fdv lines' (forwardFD fs fd k) *
      &(Fail_exn e ∧ run_checker t lines fmlls Clist b = NONE)))
Proof
  ho_match_mp_tac run_checker_ind>>rw[]>>
  xcf "run_checker" (get_ml_prog_state ())>>
  xlet`
    POSTve
   (λv.
      ARRAY fmlv fmllsv * W8ARRAY Carrv Clist *
      SEP_EXISTS k lines' res.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES (term_char t) fd fdv lines' (forwardFD fs fd k) *
      &(parse_one t lines = SOME res ∧
        OPTION_TYPE LRUP_LRUP_TYPE (OPTION_MAP FST res) v ∧
        (if res = NONE then lines' = [] else OPTION_MAP SND res = SOME lines')))
   (λe.
      SEP_EXISTS k lines'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES (term_char t) fd fdv lines' (forwardFD fs fd k) *
      &(Fail_exn e ∧ parse_one t lines = NONE))`
  >- (
    xapp>>xsimpl>>
    rpt (first_x_assum (irule_at Any))>>
    xsimpl>>
    qexists_tac`lines`>>
    qexists_tac`fs`>>
    qexists_tac`fd`>>
    qexists_tac`ARRAY fmlv fmllsv * W8ARRAY Carrv Clist`>>
    rw[]>>
    xsimpl
    >- metis_tac[STDIO_INSTREAM_LINES_refl]
    >- metis_tac[STDIO_INSTREAM_LINES_refl]>>
    qexists_tac`x`>>qexists_tac`x'`>>xsimpl)
  >- (
    xsimpl>>
    simp[Once run_checker_def]>>rw[]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  gvs[OPTION_TYPE_SPLIT]>>
  xmatch
  >- (
    simp[Once run_checker_def]>>
    xvar>>xsimpl
    >- metis_tac[DW8ARRAY_STDIO_INSTREAM_LINES_refl]
    >- simp[Once run_checker_def])>>
  xlet_autop
  >- (
    xsimpl>>
    simp[Once run_checker_def]>>
    TOP_CASE_TAC>>simp[]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  xmatch>>
  xlet_autop>>
  xapp>>xsimpl>>
  rpt(first_assum $ irule_at Any)>>
  Cases_on`z`>>gvs[]>>
  irule_at Any (cj 2 STDIO_INSTREAM_LINES_refl)>>
  xsimpl>>rw[]
  >-
    cheat>>
  simp[Once run_checker_def,fsFFIPropsTheory.forwardFD_o]>>
  metis_tac[STDIO_INSTREAM_LINES_refl]
QED

