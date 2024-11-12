(*
  This builds the cake_xlrup proof checker
*)
open preamble basis UnsafeProofTheory xlrupTheory xlrup_listTheory xlrup_parsingTheory xlrup_arrayProgTheory cnf_xorTheory;

val _ = new_theory "xlrup_arrayFullProg"

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = translation_extends"xlrup_arrayProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

val _ = translate parse_header_line_def;

val parse_header_line_side = Q.prove(`
   ∀x. parse_header_line_side x= T`,
  rw[definition"parse_header_line_side_def"]>>
  intLib.ARITH_TAC)
  |> update_precondition;

val _ = translate parse_lits_aux_def;
val _ = translate parse_clause_def;
val _ = translate parse_xvar_def;

val parse_xvar_side = Q.prove(`
   ∀x. parse_xvar_side x= T`,
  rw[definition"parse_xvar_side_def"])
  |> update_precondition;

val _ = translate parse_xor_def;
val _ = translate parse_line_def;

val _ = translate nocomment_line_def;

Definition format_dimacs_failure_def:
  format_dimacs_failure (lno:num) s =
  strlit "c DIMACS parse failed at line: " ^ toString lno ^ strlit ". Reason: " ^ s ^ strlit"\n"
End

val _ = translate format_dimacs_failure_def;

val b_inputLineTokens_specialize =
  b_inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_v_thm,tokenize_v_thm,blanks_def] ;

val parse_body_arr = process_topdecs`
  fun parse_body_arr lno maxvar fd cacc xacc =
  case TextIO.b_inputLineTokens #"\n" fd blanks tokenize of
    None => Inr (List.rev cacc, List.rev xacc)
  | Some l =>
    if nocomment_line l then
      (case parse_line maxvar l of
        None => Inl (format_dimacs_failure lno "failed to parse line")
      | Some (Inl cl) =>
        parse_body_arr (lno+1) maxvar fd (cl::cacc) xacc
      | Some (Inr xl) =>
        parse_body_arr (lno+1) maxvar fd cacc (xl::xacc)
      )
    else parse_body_arr (lno+1) maxvar fd cacc xacc` |> append_prog;

Overload "LL_LIT_TYPE" = ``LIST_TYPE (LIST_TYPE CNF_XOR_LIT_TYPE)``

Theorem parse_body_arr_spec:
  !lines fd fdv fs maxvar maxvarv cacc caccv xacc xaccv lno lnov.
  NUM lno lnov ∧
  NUM maxvar maxvarv ∧
  LL_LIT_TYPE cacc caccv ∧
  LL_LIT_TYPE xacc xaccv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_body_arr" (get_ml_prog_state()))
    [lnov; maxvarv; fdv; caccv; xaccv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      &
      (∃err. SUM_TYPE STRING_TYPE
        (PAIR_TYPE LL_LIT_TYPE LL_LIT_TYPE)
      (case parse_body maxvar
        (FILTER nocomment_line (MAP toks lines)) cacc xacc of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))
Proof
  Induct
  \\ simp []
  \\ rpt strip_tac
  \\ xcf "parse_body_arr" (get_ml_prog_state ())
  THEN1 (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac `emp`
      \\ qexists_tac ‘[]’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs [])
    \\ gvs[OPTION_TYPE_def]
    \\ xmatch
    \\ simp[parse_body_def]
    \\ rpt xlet_autop
    \\ xcon \\ xsimpl
    \\ simp[SUM_TYPE_def,PAIR_TYPE_def]
    \\ qexists_tac ‘k’ \\ xsimpl
    \\ qexists_tac `[]` \\ xsimpl)
  \\ xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
                & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks h)) v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac `emp`
      \\ qexists_tac ‘h::lines’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
      \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
      \\ simp[toks_def])
  \\ gvs[OPTION_TYPE_def]
  \\ xmatch \\ fs []
  \\ xlet_autop
  \\ reverse IF_CASES_TAC
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
  simp[parse_body_def]>>
  Cases_on`parse_line maxvar (toks h)`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>
    xsimpl>>
    qexists_tac`k`>> qexists_tac`lines`>>xsimpl>>
    simp[SUM_TYPE_def]>>
    metis_tac[])>>
  Cases_on`x`>>fs[SUM_TYPE_def]>>
  rename1`LIST_TYPE _ ll _`>>
  xmatch>>
  xlet_autop>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  rpt(first_x_assum (irule_at Any))
  >- (
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>
    qexists_tac`ll::cacc`>>
    xsimpl>>
    simp[LIST_TYPE_def,forwardFD_o]>>rw[]>>
    qexists_tac`k+x`>>
    qexists_tac`x'`>>
    xsimpl>>
    metis_tac[])
  >- (
    qexists_tac`ll::xacc`>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>
    xsimpl>>
    simp[LIST_TYPE_def,forwardFD_o]>>rw[]>>
    qexists_tac`k+x`>>
    qexists_tac`x'`>>
    xsimpl>>
    metis_tac[])
QED

val parse_cnf_xor_toks_arr = process_topdecs`
  fun parse_cnf_xor_toks_arr lno fd =
  case TextIO.b_inputLineTokens #"\n" fd blanks tokenize of
    None => Inl (format_dimacs_failure lno "failed to find header")
  | Some l =>
    if nocomment_line l then
      (case parse_header_line l of
        None => Inl (format_dimacs_failure lno "failed to parse header")
      | Some res => case res of (vars,ncx) =>
        (case parse_body_arr lno vars fd [] [] of
          Inl fail => Inl fail
        | Inr (cacc,xacc) =>
          if List.length cacc + List.length xacc = ncx then
            Inr (vars,(ncx,(cacc,xacc)))
          else
            Inl (format_dimacs_failure lno "incorrect number of clauses / xors")))
    else parse_cnf_xor_toks_arr (lno+1) fd` |> append_prog;

Theorem parse_cnf_xor_toks_arr_spec:
  !lines fd fdv fs lno lnov.
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_cnf_xor_toks_arr" (get_ml_prog_state()))
    [lnov; fdv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE
        (PAIR_TYPE NUM (PAIR_TYPE NUM
          (PAIR_TYPE LL_LIT_TYPE LL_LIT_TYPE)))
      (case parse_cnf_xor_toks (MAP toks lines) of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))
Proof
  Induct
  \\ simp []
  \\ rpt strip_tac
  \\ xcf "parse_cnf_xor_toks_arr" (get_ml_prog_state ())
  THEN1 (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac `emp`
      \\ qexists_tac ‘[]’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs [])
    \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
    \\ xmatch \\ fs []
    \\ simp[parse_cnf_xor_toks_def]
    \\ xlet_autop
    \\ xcon \\ xsimpl
    \\ simp[SUM_TYPE_def]
    \\ qexists_tac ‘k’ \\ xsimpl
    \\ qexists_tac `[]` \\ xsimpl
    \\ metis_tac[])
  \\ xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
                & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks h)) v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac `emp`
      \\ qexists_tac ‘h::lines’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
      \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
      \\ simp[toks_def])
  \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
  \\ xmatch \\ fs []
  \\ xlet_autop
  \\ simp[parse_cnf_xor_toks_def]
  \\ reverse IF_CASES_TAC
  >- (
    xif >> asm_exists_tac>>xsimpl>>
    xlet_autop>>
    xapp>> xsimpl>>
    asm_exists_tac>> simp[]>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>xsimpl>>
    rw[]>>
    fs[parse_cnf_xor_toks_def]>>
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
  Cases_on`x`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xlet `(POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE
        (PAIR_TYPE LL_LIT_TYPE LL_LIT_TYPE)
      (case parse_body q (FILTER nocomment_line (MAP toks lines)) [] [] of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))`
  >- (
    xapp>>xsimpl>>
    qexists_tac`emp`>>
    rpt(first_x_assum (irule_at Any))>>
    qexists_tac`[]`>>
    qexists_tac`lines`>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>xsimpl>>
    qexists_tac`[]`>>simp[LIST_TYPE_def]>>
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
  Cases_on`x`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  rw[]>> xif
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
  qexists_tac`k`>>
  qexists_tac`lines'`>>
  simp[SUM_TYPE_def,PAIR_TYPE_def]>>
  xsimpl>>
  metis_tac[]
QED

(* parse_cnf_xor_toks with simple wrapper *)
val parse_full = (append_prog o process_topdecs) `
  fun parse_full fname =
  let
    val fd = TextIO.b_openIn fname
    val res = parse_cnf_xor_toks_arr 0 fd
    val close = TextIO.b_closeIn fd;
  in
    res
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)`;

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
    (case parse_cnf_xor_toks (MAP toks (all_lines fs f)) of
      NONE => INL err
    | SOME x => INR x)
    else INL err) v)) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_full"(get_ml_prog_state()) >>
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
  xlet_auto_spec (SOME (b_openIn_spec_lines |> Q.GEN `c0` |> Q.SPEC `#"\n"`)) \\ xsimpl >>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES _ fdd fddv lines fss`>>
  xlet`(POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM
        (PAIR_TYPE LL_LIT_TYPE LL_LIT_TYPE)))
      (case parse_cnf_xor_toks (MAP toks lines) of
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
    xapp_spec b_closeIn_spec_lines >>
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
    fs [Abbr`fss`] \\ xsimpl)>>
  xvar>>
  xsimpl>>
  metis_tac[]
QED

val usage_string = ‘

Usage:  cake_xlrup <CNF XOR formula file> <optional: XLRUP proof file>

Run XLRUP unsatisfiability proof checking (if proof is given)

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

val r = translate conv_cfml_def;

val r = translate var_lit_def;
val r = translate max_list_def;
val r = translate max_var_xor_def;

(*
val map_conv_xor_arr = process_topdecs`
  fun map_conv_xor_arr mv xs =
  case xs of [] => []
  | (x::xs) =>
    conv_rawxor_arr mv (map_conv_lit x) ::
    map_conv_xor_arr mv xs` |> append_prog;

Theorem map_conv_xor_arr_spec:
  ∀xs xsv.
  NUM n nv ∧
  LL_LIT_TYPE xs xsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "map_conv_xor_arr" (get_ml_prog_state()))
    [nv; xsv]
    (emp)
    (POSTv v.
      &(LIST_TYPE STRING_TYPE (MAP (conv_rawxor_list n) (MAP map_conv_lit xs)) v))
Proof
  Induct>>
  xcf "map_conv_xor_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>xmatch
  >- (xcon>>xsimpl)>>
  first_x_assum drule>>
  rw[]>>
  rpt xlet_autop>>
  xcon>>xsimpl
QED

val conv_xfml_arr = process_topdecs`
  fun conv_xfml_arr xfml =
  let
    val mv = max_var_xor xfml
  in
    (map_conv_xor_arr mv xfml, mv)
  end` |> append_prog;

Theorem conv_xfml_arr_spec:
  LL_LIT_TYPE x xv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "conv_xfml_arr" (get_ml_prog_state()))
    [xv]
    (emp)
    (POSTv v.
      &(
      PAIR_TYPE (LIST_TYPE STRING_TYPE) NUM
      (conv_xfml (max_var_xor x) x,max_var_xor x) v))
Proof
  xcf "conv_xfml_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet_autop>>
  xcon>>
  xsimpl>>
  fs[PAIR_TYPE_def,conv_xfml_def]>>
  qmatch_asmsub_abbrev_tac`LIST_TYPE STRING_TYPE A _`>>
  qmatch_goalsub_abbrev_tac`LIST_TYPE STRING_TYPE B _`>>
  `A = B` by
    (unabbrev_all_tac>>fs[MAP_MAP_o,o_DEF,MAP_EQ_f]>>rw[]>>
    simp[conv_rawxor_list_conv_rawxor,conv_rawxor_def,conv_xor_def,map_conv_lit_def])>>
  fs[]
QED
*)

(*
  Checker takes up to 2 arguments:
  2 args (CNF XOR file, proof file):
    parse CNF XOR, run proof, report UNSAT (or error)
*)

val check_unsat_2 = (append_prog o process_topdecs) `
  fun check_unsat_2 f1 f2 =
  case parse_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv,(ncx,(cfml,xfml))) =>
  let val cfml = conv_cfml cfml
      val one = 1
      val carr = Array.array (2*ncx) None
      val carr = fill_arr carr one cfml
      val xarr = Array.array (2*ncx) None
      val tn = (Ln, 1)
      val bnd = 2*mv + 3
  in
    case check_unsat' xfml carr xarr tn 0 f2 bnd of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr b =>
      if b then
        TextIO.print "s VERIFIED UNSAT\n"
      else
        TextIO.output TextIO.stdErr "c empty clause not derived at end of proof\n"
  end`

val _ = translate print_lit_def;
val _ = translate print_clause_def;
val _ = translate print_xor_def;
val _ = translate print_header_line_def;
val _ = translate print_cnf_xor_def;

val check_unsat_1 = (append_prog o process_topdecs) `
  fun check_unsat_1 f1 =
  case parse_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv,(ncl,fml)) => TextIO.print_list (print_cnf_xor fml)`

Definition check_unsat_1_sem_def:
  check_unsat_1_sem fs f1 err =
  if inFS_fname fs f1 then
    (case parse_cnf_xor (all_lines fs f1) of
      NONE => add_stderr fs err
    | SOME fml => add_stdout fs (concat (print_cnf_xor fml)))
  else add_stderr fs err
End

Theorem check_unsat_1_spec:
  STRING_TYPE f1 f1v ∧
  validArg f1 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_1"(get_ml_prog_state()))
    [f1v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS err. STDIO (check_unsat_1_sem fs f1 err))
Proof
  rw[]>>
  xcf "check_unsat_1" (get_ml_prog_state ())>>
  xlet_autop>>
  simp[check_unsat_1_sem_def]>>
  TOP_CASE_TAC>>fs[]
  >- (
    simp[parse_cnf_xor_def]>>
    every_case_tac>>fs[SUM_TYPE_def,PAIR_TYPE_def]>>
    xmatch
    >- (
      xapp_spec output_stderr_spec \\ xsimpl>>
      asm_exists_tac>>xsimpl>>
      qexists_tac`emp`>>xsimpl>>
      qexists_tac`fs`>>xsimpl>>
      rw[]>>qexists_tac`err`>>xsimpl)>>
    xlet_autop>>
    xapp_spec print_list_spec>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl)>>
  fs[SUM_TYPE_def]>>
  xmatch>>
  xapp_spec output_stderr_spec \\ xsimpl>>
  asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>xsimpl>>
  qexists_tac`fs`>>xsimpl>>
  rw[]>>qexists_tac`err`>>xsimpl
QED

val check_unsat = (append_prog o process_topdecs) `
  fun check_unsat u =
  case CommandLine.arguments () of
    [f1] => check_unsat_1 f1
  | [f1,f2] => check_unsat_2 f1 f2
  | _ => TextIO.output TextIO.stdErr usage_string`

(* We verify each argument type separately *)
val b_inputAllTokensFrom_spec_specialize =
  b_inputAllTokensFrom_spec
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> REWRITE_RULE [blanks_v_thm,tokenize_v_thm,blanks_def] ;

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 f2 err =
  if inFS_fname fs f1 then
  (case parse_cnf_xor_toks (MAP toks (all_lines fs f1)) of
    NONE => add_stderr fs err
  | SOME (mv,ncl,cfml,xfml) =>
    let cfml = conv_cfml cfml in
    if inFS_fname fs f2 then
      case parse_xlrups (all_lines fs f2) of
        SOME xlrups =>
        let cfmlls = enumerate 1 cfml in
        let base = REPLICATE (2*ncl) NONE in
        let cupd = FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) base cfmlls in
        let base = REPLICATE (2*ncl) NONE in
        let tn = (LN,1) in
        let bnd = 2*mv+3 in
          if check_xlrups_unsat_list xfml xlrups cupd base tn
            0 (REPLICATE bnd w8z)
          then
            add_stdout fs (strlit "s VERIFIED UNSAT\n")
          else
            add_stderr fs err
      | NONE => add_stderr fs err
    else add_stderr fs err)
  else add_stderr fs err
End

val err_tac = xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>qexists_tac`err`>>xsimpl;

Definition bounded_lit_def:
  bounded_lit (vars:num) l =
    case l of
      Pos v => v ≤ vars
    | Neg v => v ≤ vars
End

Theorem parse_lits_aux_bound:
  ∀vars l acc c.
  parse_lits_aux vars l acc = SOME c ∧
  EVERY (bounded_lit vars) acc
  ⇒
  EVERY (bounded_lit vars) c
Proof
  ho_match_mp_tac parse_lits_aux_ind>>
  rw[parse_lits_aux_def]>>gvs[AllCaseEqs()]>>
  first_x_assum match_mp_tac>>
  rw[bounded_lit_def]
QED

Theorem parse_clause_bound:
  parse_clause vars l = SOME c ⇒
  EVERY (bounded_lit vars) c
Proof
  rw[parse_clause_def]>>
  match_mp_tac parse_lits_aux_bound>>
  first_x_assum (irule_at Any)>>
  simp[]
QED

Theorem parse_line_bound_INL:
  parse_line vars l = SOME (INL c) ⇒
  EVERY (bounded_lit vars) c
Proof
  rw[parse_line_def]>>
  gvs[AllCaseEqs()]>>
  metis_tac[parse_clause_bound]
QED

Theorem parse_body_bound_cacc:
  ∀ss vars cacc xacc cacc' xacc'.
  parse_body vars ss cacc xacc = SOME (cacc',xacc') ∧
  EVERY (EVERY (bounded_lit vars)) cacc
  ⇒
  EVERY (EVERY (bounded_lit vars)) cacc'
Proof
  Induct>>rw[parse_body_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum match_mp_tac>>
  last_x_assum (irule_at Any)>>
  fs[]>>
  metis_tac[parse_line_bound_INL]
QED

Theorem parse_cnf_xor_toks_bound:
  parse_cnf_xor_toks (MAP toks (all_lines fs f1)) =
    SOME (vars,ncx,cacc,xacc) ⇒
  EVERY (EVERY (bounded_lit vars)) cacc
Proof
  rw[parse_cnf_xor_toks_def]>>
  gvs[AllCaseEqs()]>>
  drule parse_body_bound_cacc>>
  simp[]
QED

Theorem LENGTH_FOLDR_update_resize2:
  ∀ll x.
  MEM x ll ⇒
  FST x < LENGTH (FOLDR (λx acc. (λ(i,v). update_resize acc NONE (SOME v) i) x) (REPLICATE n NONE) ll)
Proof
  Induct>>simp[FORALL_PROD]>>rw[]>>
  rw[Once update_resize_def]
  >- (
    first_x_assum drule>>
    simp[])>>
  first_x_assum drule>>simp[]
QED

Theorem FOLDL_update_resize_lookup:
  ∀ls.
  ALL_DISTINCT (MAP FST ls) ⇒
  ∀x.
  x < LENGTH (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) (REPLICATE n NONE) ls)
  ⇒
  EL x (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) (REPLICATE n NONE) ls)
  =
  ALOOKUP ls x
Proof
  simp[Once (GSYM EVERY_REVERSE), Once (GSYM MAP_REVERSE)]>>
  simp[FOLDL_FOLDR_REVERSE]>>
  simp[GSYM alookup_distinct_reverse]>>
  simp[Once all_distinct_map_fst_rev]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE ls`>>
  pop_assum kall_tac>>
  Induct_on`ll`>-
    simp[EL_REPLICATE]>>
  simp[FORALL_PROD]>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once update_resize_def]>>
  strip_tac>>
  simp[Once update_resize_def]>>
  IF_CASES_TAC>>fs[]
  >-
    (simp[EL_LUPDATE]>>
    IF_CASES_TAC>>simp[])>>
  simp[EL_LUPDATE]>>
  IF_CASES_TAC >> simp[]>>
  simp[EL_APPEND_EQN]>>rw[]>>
  simp[EL_REPLICATE]>>
  CCONTR_TAC>>fs[]>>
  Cases_on`ALOOKUP ll x`>>fs[]>>
  drule ALOOKUP_MEM>>
  strip_tac>>
  drule LENGTH_FOLDR_update_resize2>>
  simp[]>>
  metis_tac[]
QED

Theorem bounded_cfml_FOLDL_enumerate:
  EVERY (EVERY (bounded_lit vars)) ls ∧
  v > 2 * vars ⇒
  bounded_cfml v
    (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i)
     (REPLICATE n NONE) (enumerate k (conv_cfml ls)))
Proof
  rw[bounded_cfml_def]>>
  simp[Once EVERY_EL]>>rw[]>>
  `ALL_DISTINCT (MAP FST (enumerate k (conv_cfml ls)))` by
    metis_tac[ALL_DISTINCT_MAP_FST_enumerate]>>
  TOP_CASE_TAC>>simp[]>>
  drule FOLDL_update_resize_lookup>>
  disch_then drule>>
  disch_then (SUBST_ALL_TAC)>>
  drule ALOOKUP_MEM>>
  strip_tac>> drule MEM_enumerate_IMP>>
  fs[EVERY_MEM]>>
  simp[conv_cfml_def,MEM_MAP,PULL_EXISTS,EVERY_MEM]>>
  rw[]>>
  first_x_assum drule_all>>
  simp[bounded_lit_def]>>every_case_tac>>
  rw[conv_lit_def,index_def]
QED

Theorem check_unsat_2_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  STRING_TYPE f2 f2v ∧ validArg f2 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_2"(get_ml_prog_state()))
    [f1v; f2v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS err. STDIO (check_unsat_2_sem fs f1 f2 err))
Proof
  rw[]>>
  xcf "check_unsat_2" (get_ml_prog_state ())>>
  xlet_autop>>
  simp[check_unsat_2_sem_def]>>
  reverse TOP_CASE_TAC>>fs[]
  >- (
    fs[SUM_TYPE_def]>>xmatch>>
    err_tac)>>
  TOP_CASE_TAC>> fs[SUM_TYPE_def]
  >- (xmatch>> err_tac)>>
  PairCases_on`x`>>fs[SUM_TYPE_def,PAIR_TYPE_def]>>
  xmatch>>
  rename1`_ = SOME (_,_,cfml,xfml)`>>
  xlet_autop>>
  xlet`POSTv v. &NUM 1 v * STDIO fs` >- (xlit>>xsimpl)>>
  rw[]>>
  (drule_at (Pos (hd o tl))) fill_arr_spec>>
  (* help instantiate fill_arr_spec *)
  `LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (REPLICATE (2 * x1) NONE)
        (REPLICATE (2 * x1) (Conv (SOME (TypeStamp "None" 2)) []))` by
    simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
  qpat_x_assum`NUM 1 _` assume_tac>>
  disch_then drule>>
  disch_then drule>>
  rw[]>>rpt xlet_autop>>
  (*
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  (drule_at (Pos (hd o tl))) fill_arr_spec>>
  (* help instantiate fill_arr_spec *)
  `LIST_REL (OPTION_TYPE STRING_TYPE) (REPLICATE (2 * x1) NONE)
        (REPLICATE (2 * x1) (Conv (SOME (TypeStamp "None" 2)) []))` by
    simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
  qpat_x_assum`NUM 1 _` assume_tac>>
  disch_then drule>>
  disch_then drule>>
  rw[]>>
  rpt xlet_autop>> *)
  simp[check_xlrups_unsat_list_def]>>
  qmatch_goalsub_abbrev_tac`check_xlrups_list _ _ a b c d e`>>
  xlet`POSTv v.
    STDIO fs *
    SEP_EXISTS err.
     &SUM_TYPE STRING_TYPE BOOL
      (if inFS_fname fs f2 then
         (case parse_xlrups (all_lines fs f2) of
            NONE => INL err
          | SOME xlrups =>
            (case check_xlrups_list xfml xlrups a b c d e of
             NONE => INL err
           | SOME (cfml', xfml') =>
           INR (contains_emp_list cfml')))
       else INL err) v`
  >- (
    xapp_spec (GEN_ALL check_unsat'_spec)>>
    xsimpl>>
    asm_exists_tac>>simp[]>>
    fs[FILENAME_def,validArg_def]>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    qexists_tac`REPLICATE (2 * x1) NONE`>>
    qexists_tac`(LN,1)`>>
    xsimpl>>
    reverse CONJ_TAC >- (
      CONJ_TAC >-
        metis_tac[LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
      CONJ_TAC >- (
        simp[PAIR_TYPE_def,Abbr`c`]>>
        EVAL_TAC)>>
      rw[]>>metis_tac[])>>
    (* bounded_cfml *)
    drule parse_cnf_xor_toks_bound>>
    fs[Abbr`a`]>>
    strip_tac>>
    drule bounded_cfml_FOLDL_enumerate>>
    disch_then match_mp_tac>>
    simp[])>>
  reverse TOP_CASE_TAC>>simp[]
  >- (fs[SUM_TYPE_def]>>xmatch>>err_tac)>>
  TOP_CASE_TAC>>fs[SUM_TYPE_def]
  >- (xmatch>>err_tac)>>
  Cases_on`check_xlrups_list xfml x a b c d e`>>fs[SUM_TYPE_def]
  >- (xmatch>>err_tac)>>
  Cases_on`x'`>>fs[]>>
  fs[SUM_TYPE_def]>>
  xmatch>>
  xif
  >- (
    xapp_spec print_spec >> xsimpl
    \\ qexists_tac`emp`
    \\ qexists_tac`fs`>>xsimpl)
  >- (
    gs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS,OPTION_TYPE_def]>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qmatch_goalsub_abbrev_tac`_ _ err`>>
    qexists_tac`err`>>xsimpl)
QED

Definition check_unsat_sem_def:
  check_unsat_sem cl fs err =
  case TL cl of
  | [f1] => check_unsat_1_sem fs f1 err
  | [f1;f2] => check_unsat_2_sem fs f1 f2 err
  | _ => add_stderr fs err
End

Theorem check_unsat_spec:
   hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"check_unsat"(get_ml_prog_state()))
     [Conv NONE []]
     (COMMANDLINE cl * STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv *
     COMMANDLINE cl * SEP_EXISTS err. STDIO (check_unsat_sem cl fs err))
Proof
  rw[]>>
  xcf"check_unsat"(get_ml_prog_state())>>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)>>
  rpt xlet_autop >>
  Cases_on `cl` >- fs[wfcl_def] >>
  simp[check_unsat_sem_def]>>
  every_case_tac>>fs[LIST_TYPE_def]>>xmatch>>
  qmatch_asmsub_abbrev_tac`wfcl cl`
  >- (
    xapp_spec output_stderr_spec \\ xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `usage_string` >> simp [theorem "usage_string_v_thm"] >>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>qexists_tac`usage_string`>>xsimpl)
  >- (
    xapp>>xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac`fs`>>qexists_tac`h'`>>xsimpl>>
    fs[wfcl_def,Abbr`cl`]>>
    rw[]>>
    qexists_tac`x`>>xsimpl)
  >- (
    xapp>>xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    fs[wfcl_def,Abbr`cl`]>>
    qexists_tac`fs`>>
    qexists_tac`h''`>>
    qexists_tac`h'`>>
    xsimpl>>rw[]>>
    qexists_tac`x`>>xsimpl)
  >- (
    xapp_spec output_stderr_spec \\ xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `usage_string` >> simp [theorem "usage_string_v_thm"] >>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>qexists_tac`usage_string`>>xsimpl)
QED

Theorem check_unsat_whole_prog_spec2:
   hasFreeFD fs ⇒
   whole_prog_spec2 check_unsat_v cl fs NONE (λfs'. ∃err. fs' = check_unsat_sem cl fs err)
Proof
  rw[basis_ffiTheory.whole_prog_spec2_def]
  \\ match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH check_unsat_spec))))
  \\ xsimpl
  \\ rw[PULL_EXISTS]
  \\ qexists_tac`check_unsat_sem cl fs x`
  \\ qexists_tac`x`
  \\ xsimpl
  \\ rw[check_unsat_sem_def,check_unsat_1_sem_def,check_unsat_2_sem_def]
  \\ every_case_tac
  \\ simp[GSYM add_stdo_with_numchars,with_same_numchars]
QED

local

val name = "check_unsat"
val (sem_thm,prog_tm) =
  whole_prog_thm (get_ml_prog_state()) name (UNDISCH check_unsat_whole_prog_spec2)
Definition check_unsat_prog_def:
  check_unsat_prog = ^prog_tm
End

in

Theorem check_unsat_semantics =
  sem_thm
  |> REWRITE_RULE[GSYM check_unsat_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[GSYM CONJ_ASSOC,AND_IMP_INTRO];

end

val _ = export_theory();
