(*
  Translation of the input lexer and the DIMACS helpers, and the readers
  that tokenize the lines of an input stream or file
*)
Theory input_lexProg
Ancestors
  UnsafeProg ccnf_arith input_lex mlint
Libs
  preamble basis

val _ = translation_extends "UnsafeProg";

(*** The lexer: toks through scan_toks ***)

val r = translate blanks_def;

val r = translate scan_end_def;

Theorem scan_end_side[local]:
  ∀s n j. n = strlen s ∧ j ≤ n ⇒ scan_end_side s n j
Proof
  ho_match_mp_tac scan_end_ind>>
  rpt gen_tac>>strip_tac>>
  rpt strip_tac>>
  `ORD (strsub s j) < 256` by simp[ORD_BOUND]>>
  simp[Once (fetch "-" "scan_end_side_def")]>>
  fs[smallnum_lt_str_def,smallnum_add_str_def,smallnum_eq_def,smallnum_lt_def,
     semanticPrimitivesTheory.index_in_bounds_def,
     mlstringTheory.strsub_unsafe_eq_strsub]
QED

val r = translate num_run_def;

Theorem num_run_side:
  ∀s e j acc k.
  e ≤ strlen s ∧ j ≤ e ∧ k ≤ 9 ∧ (k < 9 ⇒ acc < 10 ** k) ⇒
  num_run_side s e j acc k
Proof
  ho_match_mp_tac num_run_ind>>
  rpt gen_tac>>strip_tac>>
  rpt strip_tac>>
  `ORD (strsub s j) < 256` by simp[ORD_BOUND]>>
  `k < 9 ⇒ acc < 10 ** 8` by (
    strip_tac>>
    irule LESS_LESS_EQ_TRANS>>
    qexists_tac`10 ** k`>>
    simp[EXP_BASE_LE_MONO])>>
  simp[Once (fetch "-" "num_run_side_def")]>>
  fs[smallnum_lt_str_def,smallnum_add_str_def,smallnum_le_def,smallnum_lt_def,
     smallnum_add_def,smallnum_sub_def,smallnum_mul_def,
     semanticPrimitivesTheory.index_in_bounds_def,
     mlstringTheory.strsub_unsafe_eq_strsub]>>
  rw[]>>
  first_x_assum irule>>
  rw[EXP_ADD]
QED

val r = translate tok_val_def;

Theorem tok_val_side[local]:
  i < e ∧ e ≤ strlen s ⇒ tok_val_side s i e
Proof
  rw[fetch "-" "tok_val_side_def"]>>
  `ORD (strsub s i) < 256 ∧ ORD (strsub s (i + 1)) < 256` by simp[ORD_BOUND]>>
  fs[smallnum_lt_str_def,smallnum_add_str_def,smallnum_sub_str_def,
     smallnum_le_def,smallnum_eq_def,smallnum_sub_def,
     mlstringTheory.strsub_unsafe_eq_strsub]>>
  irule num_run_side>>
  simp[]
QED

val r = translate scan_toks_def;

Theorem scan_toks_side[local]:
  ∀s n j. n = strlen s ∧ j ≤ n ⇒ scan_toks_side s n j
Proof
  ho_match_mp_tac scan_toks_ind>>
  rpt gen_tac>>strip_tac>>
  rpt strip_tac>>
  `ORD (strsub s j) < 256` by simp[ORD_BOUND]>>
  simp[Once (fetch "-" "scan_toks_side_def")]>>
  fs[smallnum_lt_str_def,smallnum_add_str_def,smallnum_eq_def,smallnum_lt_def,
     semanticPrimitivesTheory.index_in_bounds_def,
     mlstringTheory.strsub_unsafe_eq_strsub]>>
  strip_tac>>
  qspecl_then[`s`,`strlen s`,`j + 1`,`scan_end s (strlen s) (j + 1)`] mp_tac
    scan_end_thm>>
  simp[]>>
  strip_tac>>
  rw[]
  >>~- ([`tok_val_side _ _ _`], irule tok_val_side>>simp[])
  >>~- ([`scan_end_side _ _ _`], irule scan_end_side>>simp[])>>
  first_x_assum irule>>
  simp[]
QED

val r = translate toks_scan_toks;

Theorem toks_side[local]:
  toks_side s ⇔ T
Proof
  rw[fetch "-" "toks_side_def"]>>
  irule scan_toks_side>>simp[]
QED

val _ = toks_side |> update_precondition;

(*** The DIMACS helpers ***)

val r = translate keep_line_def;

val r = translate parse_header_line_def;

Theorem parse_header_line_side_thm[local]:
  ∀x. parse_header_line_side x ⇔ T
Proof
  rw[definition"parse_header_line_side_def"]>>
  intLib.ARITH_TAC
QED

val _ = parse_header_line_side_thm |> update_precondition;

val r = translate parse_until_zero_aux_def;
val r = translate parse_until_zero_def;

(* Reported by the DIMACS readers when parsing fails at line lno *)
Definition format_dimacs_failure_def:
  format_dimacs_failure (lno:num) s =
  «c DIMACS parse failed at line: » ^ toString lno ^ «. Reason: » ^ s ^ «\n»
End

val r = translate format_dimacs_failure_def;

(* Reported by the file-level entry points *)
Definition notfound_string_def:
  notfound_string f =
  concat[«c Input file: »; f; « no such file or directory\n»]
End

val r = translate notfound_string_def;

(*** Reading tokenized lines ***)

(* Closing a file discards how far it had been read *)
Theorem fastForwardFD_ADELKEY_same[simp]:
  forwardFD fs fd n with infds updated_by ADELKEY fd =
  fs with infds updated_by ADELKEY fd
Proof
  fs [forwardFD_def, IO_fs_component_equality]
QED

Quote add_cakeml:
  fun input_toks fd =
    case TextIO.inputLineWith #"\n" fd of
      None => None
    | Some l => Some (toks l)
End

Theorem input_toks_spec:
  app (p:'ffi ffi_proj) ^(fetch_v "input_toks" (get_ml_prog_state())) [fdv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      SEP_EXISTS k.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES #"\n" fd fdv (TL lines) (forwardFD fs fd k) *
        &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
          (OPTION_MAP toks (oHD lines)) v)
Proof
  xcf "input_toks" (get_ml_prog_state ())>>
  xlet ‘(POSTv v.
          SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES #"\n" fd fdv (TL lines) (forwardFD fs fd k) *
            &OPTION_TYPE STRING_TYPE (oHD lines) v)’
  >- (
    xapp_spec inputLineWith_spec_lines>>
    EVAL_TAC)>>
  Cases_on`lines`>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xcon>>xsimpl>>
    qexists_tac`k`>>xsimpl)>>
  xlet_autop>>
  xcon>>xsimpl>>
  qexists_tac`k`>>xsimpl
QED

(* The tokens of the remaining lines *)
(* TMC *)
Quote add_cakeml:
  fun input_toks_all fd =
    case input_toks fd of
      None => []
    | Some l => l :: input_toks_all fd
End

Theorem input_toks_all_spec:
  ∀lines fs.
  app (p:'ffi ffi_proj) ^(fetch_v "input_toks_all" (get_ml_prog_state())) [fdv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      SEP_EXISTS k.
        STDIO (forwardFD fs fd k) *
        INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
        &LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (MAP toks lines) v)
Proof
  Induct>>
  rpt strip_tac>>
  xcf "input_toks_all" (get_ml_prog_state ())
  >- (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
              STDIO (forwardFD fs fd k) *
              INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
              &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    >- (
      xapp_spec input_toks_spec>>
      qexistsl_tac [‘emp’,‘[]’,‘fs’,‘fd’]>>
      xsimpl)>>
    gvs[OPTION_TYPE_def]>>
    xmatch>>
    xcon>>xsimpl>>
    simp[LIST_TYPE_def]>>
    qexists_tac`k`>>xsimpl)>>
  xlet ‘(POSTv v.
          SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
            &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
              (SOME (toks h)) v)’
  >- (
    xapp_spec input_toks_spec>>
    qexistsl_tac [‘emp’,‘h::lines’,‘fs’,‘fd’]>>
    xsimpl)>>
  gvs[OPTION_TYPE_def]>>
  xmatch>>
  xlet ‘(POSTv v.
          SEP_EXISTS k'.
            STDIO (forwardFD (forwardFD fs fd k) fd k') *
            INSTREAM_LINES #"\n" fd fdv []
              (forwardFD (forwardFD fs fd k) fd k') *
            &LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
              (MAP toks lines) v)’
  >- (xapp>>xsimpl)>>
  xcon>>xsimpl>>
  simp[LIST_TYPE_def,forwardFD_o]>>
  qexists_tac`k+k'`>>xsimpl
QED

(* The tokens of every line of the file fname, or None if it cannot be
  opened *)
Quote add_cakeml:
  fun input_toks_full fname =
    let
      val fd = TextIO.openIn fname
      val lines = input_toks_all fd
    in
      TextIO.closeIn fd; Some lines
    end handle TextIO.BadFileName => None
End

Theorem input_toks_full_spec:
  FILENAME f fv ∧ hasFreeFD fs ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "input_toks_full" (get_ml_prog_state())) [fv]
    (STDIO fs)
    (POSTv v.
      &OPTION_TYPE (LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
        (if inFS_fname fs f then SOME (MAP toks (all_lines_file fs f))
         else NONE) v * STDIO fs)
Proof
  rpt strip_tac>>
  xcf "input_toks_full" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [STDIO_def]>>xpull)>>
  reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def]>>xpull>>metis_tac[])>>
  reverse IF_CASES_TAC
  >- (
    xhandle`POSTe ev. &BadFileName_exn ev * STDIO fs`
    >- (xlet_auto_spec (SOME openIn_STDIO_spec)>>xsimpl)>>
    fs[BadFileName_exn_def]>>
    xcases>>rw[]>>
    xcon>>xsimpl>>
    fs[OPTION_TYPE_def])>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval`>>xsimpl>>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec (SOME (openIn_spec_lines |> Q.GEN `c0` |> Q.SPEC `#"\n"`))>>
  xsimpl>>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES _ fdd fddv lines fss`>>
  xlet`(POSTv v.
      SEP_EXISTS k.
        STDIO (forwardFD fss fdd k) *
        INSTREAM_LINES #"\n" fdd fddv [] (forwardFD fss fdd k) *
        &LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (MAP toks lines) v)`
  >- (
    xapp>>
    qexistsl_tac [`emp`,`lines`,`fss`,`fdd`]>>
    xsimpl>>
    rw[]>>
    qexists_tac`x`>>xsimpl)>>
  xlet `POSTv v. STDIO fs`
  >- (
    xapp_spec closeIn_spec_lines>>
    qexistsl_tac [`emp`,`[]`,`forwardFD fss fdd k`,`fdd`,`#"\n"`]>>
    conj_tac
    >- (
      unabbrev_all_tac>>
      imp_res_tac fsFFIPropsTheory.nextFD_ltX>>fs []>>
      imp_res_tac fsFFIPropsTheory.STD_streams_nextFD>>fs [])>>
    xsimpl>>
    `validFileFD fdd (forwardFD fss fdd k).infds` by (
      unabbrev_all_tac>>simp[validFileFD_forwardFD]>>
      imp_res_tac fsFFIPropsTheory.nextFD_ltX>>fs []>>
      match_mp_tac validFileFD_nextFD>>fs [])>>
    xsimpl>>rw []>>
    imp_res_tac (DECIDE ``n<m:num ==> n <= m``)>>
    imp_res_tac fsFFIPropsTheory.nextFD_leX>>fs []>>
    drule fsFFIPropsTheory.openFileFS_ADELKEY_nextFD>>
    fs [Abbr`fss`]>>xsimpl)>>
  xcon>>xsimpl>>
  fs[OPTION_TYPE_def,Abbr`lines`]
QED