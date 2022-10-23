(*
  This builds the cake_lpr proof checker
*)
open preamble basis md5ProgTheory lpr_composeProgTheory UnsafeProofTheory lprTheory lpr_listTheory lpr_parsingTheory HashtableProofTheory lpr_arrayProgTheory;

val _ = new_theory "lpr_arrayFullProg"

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = translation_extends"lpr_arrayProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

val _ = translate parse_header_line_def;

val parse_header_line_side = Q.prove(`
   ∀x. parse_header_line_side x= T`,
  rw[definition"parse_header_line_side_def"]>>
  intLib.ARITH_TAC)
  |> update_precondition;

val _ = translate parse_clause_aux_def;
val _ = translate parse_clause_def;

val _ = translate nocomment_line_def;

val format_dimacs_failure_def = Define`
  format_dimacs_failure (lno:num) s =
  strlit "c DIMACS parse failed at line: " ^ toString lno ^ strlit ". Reason: " ^ s ^ strlit"\n"`

val _ = translate format_dimacs_failure_def;

val b_inputLineTokens_specialize =
  b_inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_v_thm,tokenize_v_thm,blanks_def] ;

val parse_dimacs_body_arr = process_topdecs`
  fun parse_dimacs_body_arr lno maxvar fd acc =
  case TextIO.b_inputLineTokens fd blanks tokenize of
    None => Inr (List.rev acc)
  | Some l =>
    if nocomment_line l then
      (case parse_clause maxvar l of
        None => Inl (format_dimacs_failure lno "failed to parse line")
      | Some cl => parse_dimacs_body_arr (lno+1) maxvar fd (cl::acc))
    else parse_dimacs_body_arr (lno+1) maxvar fd acc` |> append_prog;

Theorem parse_dimacs_body_arr_spec:
  !lines fd fdv fs maxvar maxvarv acc accv lno lnov.
  NUM lno lnov ∧
  NUM maxvar maxvarv ∧
  LIST_TYPE (LIST_TYPE INT) acc accv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_dimacs_body_arr" (get_ml_prog_state()))
    [lnov; maxvarv; fdv; accv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE (LIST_TYPE (LIST_TYPE INT))
      (case parse_dimacs_body maxvar (FILTER nocomment_line (MAP toks lines)) acc of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k))
Proof
  Induct
  \\ simp []
  \\ xcf "parse_dimacs_body_arr" (get_ml_prog_state ())
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
    \\ simp[parse_dimacs_body_def]
    \\ xlet_autop
    \\ xcon \\ xsimpl
    \\ simp[SUM_TYPE_def]
    \\ qexists_tac ‘k’ \\ xsimpl
    \\ qexists_tac `[]` \\ xsimpl)
  \\ xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES fd fdv lines (forwardFD fs fd k) *
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
  \\ reverse IF_CASES_TAC
  >- (
    xif >> asm_exists_tac>>xsimpl>>
    xlet_autop>>
    xapp>> xsimpl>>
    asm_exists_tac>> simp[]>>
    asm_exists_tac>> simp[]>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>xsimpl>>
    qexists_tac`acc`>>xsimpl>>
    rw[]>>
    qexists_tac`k+x`>>
    simp[GSYM fsFFIPropsTheory.forwardFD_o]>>
    qexists_tac`x'`>>xsimpl>>
    metis_tac[])>>
  xif>> asm_exists_tac>>simp[]>>
  xlet_autop>>
  simp[parse_dimacs_body_def]>>
  Cases_on`parse_clause maxvar (toks h)`>>fs[OPTION_TYPE_def]
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

val parse_dimacs_toks_arr = process_topdecs`
  fun parse_dimacs_toks_arr lno fd =
  case TextIO.b_inputLineTokens fd blanks tokenize of
    None => Inl (format_dimacs_failure lno "failed to find header")
  | Some l =>
    if nocomment_line l then
      (case parse_header_line l of
        None => Inl (format_dimacs_failure lno "failed to parse header")
      | Some res => case res of (vars,clauses) =>
        (case parse_dimacs_body_arr lno vars fd [] of
          Inl fail => Inl fail
        | Inr acc =>
          if List.length acc = clauses then
            Inr (vars,(clauses,acc))
          else
            Inl (format_dimacs_failure lno "incorrect number of clauses")))
    else parse_dimacs_toks_arr (lno+1) fd` |> append_prog;

Theorem parse_dimacs_toks_arr_spec:
  !lines fd fdv fs lno lnov.
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_dimacs_toks_arr" (get_ml_prog_state()))
    [lnov; fdv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM (LIST_TYPE (LIST_TYPE INT))))
      (case parse_dimacs_toks (MAP toks lines) of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k))
Proof
  Induct
  \\ simp []
  \\ xcf "parse_dimacs_toks_arr" (get_ml_prog_state ())
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
    \\ simp[parse_dimacs_toks_def]
    \\ xlet_autop
    \\ xcon \\ xsimpl
    \\ simp[SUM_TYPE_def]
    \\ qexists_tac ‘k’ \\ xsimpl
    \\ qexists_tac `[]` \\ xsimpl
    \\ metis_tac[])
  \\ xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES fd fdv lines (forwardFD fs fd k) *
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
  \\ simp[parse_dimacs_toks_def]
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
    fs[parse_dimacs_toks_def]>>
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
  xlet_autop>>
  xlet `(POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE (LIST_TYPE (LIST_TYPE INT))
      (case parse_dimacs_body q (FILTER nocomment_line (MAP toks lines)) [] of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k))`
  >- (
    xapp>>xsimpl>>
    qexists_tac`emp`>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
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
  xmatch>>
  xlet_autop>>
  xlet_autop>>
  drule LENGTH_parse_dimacs_body>>
  strip_tac>>fs[]>>
  rw[]>> xif
  >- (
    asm_exists_tac>>simp[]>>
    xlet_autop>>
    xlet_autop>>
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

(* parse_dimacs_toks with simple wrapper *)
val parse_dimacs_full = (append_prog o process_topdecs) `
  fun parse_dimacs_full fname =
  let
    val fd = TextIO.b_openIn fname
    val res = parse_dimacs_toks_arr 0 fd
    val close = TextIO.b_closeIn fd;
  in
    res
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)`;

Theorem parse_dimacs_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_dimacs_full"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. (SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM (LIST_TYPE (LIST_TYPE INT))))
    (if inFS_fname fs f then
    (case parse_dimacs_toks (MAP toks (all_lines fs f)) of
      NONE => INL err
    | SOME x => INR x)
    else INL err) v)) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_dimacs_full"(get_ml_prog_state()) >>
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
  xlet`(POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM (LIST_TYPE (LIST_TYPE INT))))
      (case parse_dimacs_toks (MAP toks lines) of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fss fdd k) * INSTREAM_LINES fdd fddv lines' (forwardFD fss fdd k))`
  >- (
    xapp>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`lines`>>
    qexists_tac`fss`>>qexists_tac`fdd`>>xsimpl>>
    rw[]>>
    qexists_tac`x`>>qexists_tac`x'`>>xsimpl>>
    metis_tac[])>>
  xlet `POSTv v. STDIO fs`
  >-
    (xapp_spec b_closeIn_spec_lines >>
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
    fs [Abbr`fss`] \\ xsimpl)>>
  xvar>>
  xsimpl>>
  metis_tac[]
QED

val usage_string = ‘

cake_lpr can be invoked in several ways from the command line.

Usage:  cake_lpr <DIMACS formula file>
Parses the DIMACS file and prints the parsed formula.

Usage:  cake_lpr <DIMACS formula file> <LPR proof file>
Run LPR unsatisfiability proof checking

Usage:  cake_lpr <DIMACS formula file> <LPR proof file> <DIMACS transformation file>
Run LPR transformation proof checking

Usage:  cake_lpr <DIMACS formula file> <summary proof file> i-j <LPR proof file>
Run two-level transformation proof checking for lines i-j

Usage:  cake_lpr <DIMACS formula file> <summary proof file> -check <output file>
Check that output intervals cover all lines of summary proof file

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

val _ = register_type``:step``;

val LPR_STEP_TYPE_def = fetch "-" "LPR_STEP_TYPE_def";

val run_proof_arr = (append_prog o process_topdecs) `
  fun run_proof_arr fml inds earr hm n mv steps =
  case steps of [] => (fml,inds,earr,n,mv)
  | step::rest =>
  (case step of
    Del c =>
    (case Hashtable.lookup hm c of
      None => run_proof_arr fml inds earr hm n mv rest
    | Some cls =>
       (list_delete_arr cls fml;
       Hashtable.delete hm c;
       run_proof_arr fml inds earr hm n mv rest))
  | Add c =>
    let val earr = update_earliest_arr earr n c
        val mv = max mv (list_max_index c + 1)
        val u = hash_ins hm c n
    in
      run_proof_arr (resize_update_arr (Some c) n fml)
        (sorted_insert n inds) earr hm (n+1) mv rest
    end)`

Theorem run_proof_arr_spec:
  ∀sts stsv ls lsv fmlls fmllsv earliest earliestv n nv fmlv Earrv h hv mv mvv.
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  LIST_REL (OPTION_TYPE NUM) earliest earliestv ∧
  NUM n nv ∧
  NUM mv mvv ∧
  (LIST_TYPE LPR_STEP_TYPE) sts stsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "run_proof_arr" (get_ml_prog_state()))
    [fmlv; lsv; Earrv; hv; nv; mvv; stsv]
    (ARRAY fmlv fmllsv * ARRAY Earrv earliestv *
    HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists h hv)
    (POSTv v.
      SEP_EXISTS v1 v2 v3 v4 v5.
      &(v = Conv NONE [v1; v2; v3; v4; v5]) *
      SEP_EXISTS fmllsv' earliestv'.
      let (fmlls',ls',earliest',h',n',mv') = run_proof_list (fmlls,ls,earliest,h,n,mv) sts in
      ARRAY v1 fmllsv' *
      ARRAY v3 earliestv' *
      HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists h' hv *
      &(LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls' fmllsv' ∧
        (LIST_TYPE NUM) ls' v2 ∧
        LIST_REL (OPTION_TYPE NUM) earliest' earliestv' ∧
        NUM n' v4 ∧
        NUM mv' v5
      )
    )
Proof
  simp[run_proof_list_def]>>
  Induct>>rw[]>>
  xcf "run_proof_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>
  xmatch
  >- (simp[]>>xcon>>xsimpl)>>
  Cases_on`h`>>fs[LPR_STEP_TYPE_def]>>
  xmatch>>simp[run_proof_step_list_def]
  >- (
    (* Del case *)
    xlet_auto >- (
      qexists_tac`ARRAY fmlv fmllsv * ARRAY Earrv earliestv`>>qexists_tac`h'`>>xsimpl)>>
    TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>xmatch
    >- (
      (* Key not present *)
      xapp>>
      xsimpl>>
      rpt(asm_exists_tac>>simp[])>>
      qexists_tac`emp`>>qexists_tac`h'`>>xsimpl>>
      pairarg_tac>>simp[]>>
      xsimpl)>>
    rpt xlet_autop>>
    xapp>>xsimpl>>
    rpt(asm_exists_tac>>simp[])>>
    qexists_tac`emp`>>qexists_tac`h' \\ l`>>xsimpl>>
    pairarg_tac>>simp[]>>
    xsimpl)>>
  (* "Add" case -- annoying... *)
  rpt xlet_autop>>
  xlet`POSTv uv.
       ARRAY fmlv fmllsv *
       ARRAY Earrv' earliestv' *
       HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists (hash_insert h' l n) hv`
  >- (
    xapp>>asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    qexists_tac`ARRAY Earrv' earliestv' * ARRAY fmlv fmllsv `>>
    qexists_tac`h'`>>
    xsimpl)>>
  rpt xlet_autop>>
  xlet`(POSTv resv.
      SEP_EXISTS fmllsv'.
      ARRAY resv fmllsv' * ARRAY Earrv' earliestv' *
      HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists (hash_insert h' l n) hv *
      & LIST_REL (OPTION_TYPE (LIST_TYPE INT))
              (resize_update_list fmlls NONE (SOME l) n) fmllsv')`
  >- (
    xapp_spec (resize_update_arr_spec |> Q.GEN `vty` |> ISPEC ``(LIST_TYPE INT)``)>>
    asm_exists_tac>>xsimpl>>
    asm_exists_tac>>simp[]>>
    qexists_tac`SOME l`>>simp[OPTION_TYPE_def])>>
  xapp>> xsimpl>>
  rpt(asm_exists_tac>>simp[])
QED

(* Only run proof on the hash table *)
val run_proof_hash_arr = (append_prog o process_topdecs) `
  fun run_proof_hash_arr hm n steps =
  case steps of [] => ()
  | step::rest =>
  (case step of
    Del c =>
      (Hashtable.delete hm c;
       run_proof_hash_arr hm n rest)
  | Add c =>
      (hash_ins hm c n;
      run_proof_hash_arr hm (n+1) rest))`

Theorem run_proof_hash_arr_spec:
  ∀sts stsv n nv h hv a b c d.
  NUM n nv ∧
  (LIST_TYPE LPR_STEP_TYPE) sts stsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "run_proof_hash_arr" (get_ml_prog_state()))
    [hv; nv; stsv]
    (HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists h hv)
    (POSTv uv.
      HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists
      (FST(SND(SND(SND(run_proof_list (a,b,c,h,n,d) sts)))))
      hv)
Proof
  simp[run_proof_list_def]>>
  Induct>>rw[]>>
  xcf "run_proof_hash_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>
  xmatch
  >- (simp[]>>xcon>>xsimpl)>>
  Cases_on`h`>>fs[LPR_STEP_TYPE_def]>>
  xmatch>>simp[run_proof_step_list_def]
  >- (
    (* Del case *)
    xlet_auto >- (
      qexists_tac`emp`>>qexists_tac`h'`>>xsimpl)>>
    xapp>>
    asm_exists_tac>>simp[]>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`h' \\l`>>xsimpl>>
    every_case_tac>>simp[]>>
    qmatch_goalsub_abbrev_tac`FOLDL _ (aa,bb,cc,_,_,dd)`>>
    map_every qexists_tac [`dd`,`cc`,`bb`,`aa`]>>
    xsimpl>>
    DEP_REWRITE_TAC[DOMSUB_NOT_IN_DOM]>>
    fs[FDOM_FLOOKUP]>>
    xsimpl)>>
  (* "Add" case -- annoying... *)
  xlet`POSTv uv.
       HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists (hash_insert h' l n) hv`
  >- (
    xapp>>asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    qexists_tac`emp`>>qexists_tac`h'`>>
    xsimpl)>>
  xlet_autop>>
  xapp>>simp[]
QED

val mapf_def = Define`
  mapf ls = MAP FST (ls: (int list # num list) list)`

val _ = translate mapf_def;

val check_lpr_range_arr = (append_prog o process_topdecs) `
  fun check_lpr_range_arr fname fml inds earr mv n pf i j =
  let
    val hm = (Hashtable.empty (2 * n) hash_func order_lists)
    val u = reindex_hash fml False inds hm
    val pfij = List.take pf j
    val pfi = List.take pfij i
    val pfj = List.drop pfij i
    val ri = run_proof_arr fml inds earr hm n mv pfi
  in
    case ri of (fml',inds',earr',n',mv') =>
    let val rj = run_proof_hash_arr hm n' pfj
        val cls = mapf (Hashtable.toAscList hm)
    in
      check_unsat' 0 fml' inds' earr' fname mv' cls
    end
  end`

Theorem bounded_fml_run_proof_list:
  ∀pf fmlls ls earliest fm n mv fmlls' ls' earliest' fm' n' mv'.
  run_proof_list (fmlls,ls,earliest,fm,n,mv) pf = (fmlls',ls',earliest',fm',n',mv') ∧
  bounded_fml mv fmlls ⇒
  bounded_fml mv' fmlls'
Proof
  Induct>>fs[run_proof_list_def]>>
  Cases>>rw[run_proof_step_list_def]>>
  every_case_tac>>fs[]>>
  first_x_assum drule>>
  disch_then match_mp_tac>>
  fs[bounded_fml_list_delete_list]>>
  DEP_REWRITE_TAC [bounded_fml_resize_update_list]>>
  CONJ_TAC>- (
    match_mp_tac (GEN_ALL bounded_fml_leq)>>
    asm_exists_tac>>simp[])>>
  match_mp_tac list_max_index_bounded_clause>>
  simp[]
QED

Theorem contains_clauses_list_eq:
  set (ls:int list list) = set ls' ⇒
  contains_clauses_list fml inds ls = contains_clauses_list fml inds ls'
Proof
  rw[contains_clauses_list_def]>>
  every_case_tac>>fs[EVERY_MEM,EXTENSION]
QED

Theorem check_lpr_range_arr_spec:
  FILENAME f fv ∧
  hasFreeFD fs ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  LIST_REL (OPTION_TYPE NUM) earliest earliestv ∧
  (LIST_TYPE NUM) ls lsv ∧
  (LIST_TYPE LPR_STEP_TYPE) sts stsv ∧
  NUM i iv ∧
  NUM j jv ∧
  NUM n nv ∧
  NUM mv mvv ∧
  i ≤ j ∧
  bounded_fml mv fmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lpr_range_arr" (get_ml_prog_state()))
    [fv; fmlv; lsv; Earrv; mvv; nv; stsv; iv; jv]
    (STDIO fs * ARRAY fmlv fmllsv * ARRAY Earrv earliestv)
    (POSTv v.
    STDIO fs *
    SEP_EXISTS err err2.
      &(SUM_TYPE STRING_TYPE (OPTION_TYPE (LIST_TYPE INT)))
      (if inFS_fname fs f then
        (case parse_lpr (all_lines fs f) of
          NONE => INL err
        | SOME lpr =>
          let fm = hash_clauses_list fmlls ls in
          let stsij = TAKE j sts in
          let stsi = TAKE i stsij in
          let stsj = DROP i stsij in
          let (fmlls',ls',earliest',fm',n',mv') = run_proof_list (fmlls,ls,earliest,fm,n,mv) stsi in
          let (fmlls'',ls'',earliest'',fm'',n'',mv'') = run_proof_list (fmlls',ls',earliest',fm',n',mv') stsj in
          let cls = MAP FST (fmap_to_alist fm'') in
          case check_lpr_list 0 lpr fmlls' ls' (REPLICATE mv' w8z) earliest' of
            NONE => INL err
          | SOME (fml',ls') =>
            if contains_clauses_list fml' ls' cls then INR NONE
            else INR (SOME err2))
      else
        INL err
      ) v)
Proof
  rw[]>>
  xcf "check_lpr_range_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xlet`POSTv v. HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists FEMPTY v * STDIO fs * ARRAY fmlv fmllsv * ARRAY Earrv earliestv`
  >- (
    xapp_spec (HashtableProofTheory.hashtable_empty_spec|>INST_TYPE[alpha|->``:int list``,beta |-> ``:num list``])>>
    assume_tac order_lists_TotOrd>>
    asm_exists_tac>>simp[]>>
    simp[PULL_EXISTS]>>
    asm_exists_tac>>simp[]>>
    assume_tac order_lists_v_thm>>
    asm_exists_tac>>simp[]>>
    qexists_tac`STDIO fs * ARRAY fmlv fmllsv * ARRAY Earrv earliestv`>>xsimpl>>
    qexists_tac`hash_func`>>
    qexists_tac`LIST_TYPE NUM`>>xsimpl>>
    simp[hash_func_v_thm])>>
  assume_tac (ListProgTheory.take_v_thm |> Q.GEN `a` |> Q.ISPEC `LPR_STEP_TYPE`)>>
  rpt xlet_autop>>
  xlet`(POSTv uv.
      &(UNIT_TYPE () uv) *
      HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists
       ((λ(xs,ys). hash_clauses_aux ys xs) (reindex fmlls ls) FEMPTY) v *
      STDIO fs * ARRAY fmlv fmllsv * ARRAY Earrv earliestv)`
  >- (
    xapp>>xsimpl>>
    qexists_tac`STDIO fs * ARRAY Earrv earliestv`>>xsimpl>>
    `BOOL F (Conv (SOME (TypeStamp "False" 0)) [])` by EVAL_TAC>>
    rpt (asm_exists_tac>>simp[])>>
    qexists_tac`FEMPTY`>>xsimpl)>>
  rpt xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>
    pairarg_tac>>simp[]>>
    xsimpl)>>
  simp[hash_clauses_list_def,mllistTheory.take_def]>>
  rpt(pairarg_tac>>fs[])>>rw[]>>
  xpull>>
  xmatch >>
  xlet`POSTv uv.
    ARRAY v1 fmllsv' * ARRAY v3 earliestv' *
           HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists
           (FST(SND(SND(SND(run_proof_list (fmlls',ls',earliest',fm',n',mv') (drop (take sts j) i)))))) v * STDIO fs`
  >- (
    xapp>>xsimpl >>
    rpt(asm_exists_tac>>simp[])>>
    qexists_tac` ARRAY v1 fmllsv' * ARRAY v3 earliestv' * STDIO fs`>>
    qexists_tac`fm'`>>
    xsimpl>>
    map_every qexists_tac [`mv'`,`earliest'`,`ls'`,`fmlls'`]>>
    xsimpl)>>
  fs[mllistTheory.drop_def,mllistTheory.take_def]>>
  xlet`POSTv listv. SEP_EXISTS bsalist asclist.
    &(LIST_TYPE (PAIR_TYPE (LIST_TYPE INT) (LIST_TYPE NUM)) bsalist listv ∧ FEMPTY |++ bsalist = fm'') *
    ARRAY v1 fmllsv' * ARRAY v3 earliestv' * STDIO fs`
  >- (
    xapp_spec (HashtableProofTheory.hashtable_toAscList_spec|>INST_TYPE[alpha|->``:int list``,beta |-> ``:num list``])>>
    qexists_tac`ARRAY v1 fmllsv' * ARRAY v3 earliestv' * STDIO fs`>>xsimpl>>
    metis_tac[SEP_IMP_REFL])>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  `bounded_fml mv' fmlls'` by
    metis_tac[bounded_fml_run_proof_list]>>
  rpt(asm_exists_tac>>simp[])>>
  qexists_tac`emp`>>xsimpl>>
  simp[mapf_def]>>rveq>>
  `set (MAP FST bsalist) = set (MAP FST (fmap_to_alist (FEMPTY |++ bsalist)))` by
    fs[EXTENSION,MEM_MAP,MEM_fmap_to_alist,EXISTS_PROD,FDOM_FUPDATE_LIST]>>
  drule contains_clauses_list_eq>>
  rw[]>>
  reverse TOP_CASE_TAC>>fs[]
  >-
    metis_tac[]>>
  TOP_CASE_TAC>>fs[]
  >-
    metis_tac[]>>
  TOP_CASE_TAC>>fs[]
  >-
    metis_tac[]>>
  pop_assum mp_tac>>TOP_CASE_TAC>>fs[]>>
  qpat_x_assum`!inds fml. _` (assume_tac o GSYM)>>
  simp[]>>
  strip_tac>>simp[contains_clauses_list_err]>>
  TOP_CASE_TAC>>simp[]>>
  fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]>>
  metis_tac[]
QED

(*
  Checker takes up to 4 arguments:
  1 arg (CNF file): parse and print the CNF
  2 args (CNF file, proof file): parse CNF, run proof, report UNSAT (or error)
  3 args (CNF file, proof file, CNF file (transformation)):
    parse CNF, run proof, check that the proof transforms the CNF correctly to the latter CNF
  4 args (CNF file, top-level proof, range a-b, LPR proof file)
*)

val _ = translate parse_proofstep_def;
val _ = translate parse_proof_toks_aux_def;
val _ = translate parse_proof_toks_def;

(* parse_proof with simple wrapper *)
val parse_proof_full = (append_prog o process_topdecs) `
  fun parse_proof_full f =
  (case TextIO.b_inputAllTokensFrom f blanks tokenize of
    None => Inl (notfound_string f)
  | Some lines =>
  (case parse_proof_toks lines of
    None => Inl (noparse_string f "Proof")
  | Some x => Inr x))`

val check_unsat_1 = (append_prog o process_topdecs) `
  fun check_unsat_1 f1 =
  case parse_dimacs_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv,(ncl,fml)) => TextIO.print_list (print_dimacs fml)`

val check_unsat_2 = (append_prog o process_topdecs) `
  fun check_unsat_2 f1 f2 =
  case parse_dimacs_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv,(ncl,fml)) =>
  let val one = 1
      val arr = Array.array (2*ncl) None
      val arr = fill_arr arr one fml
      val bnd = 2*mv + 3
      val earr = Array.array bnd None
      val earr = fill_earliest earr one fml
      val rls = rev_enum_full 1 fml
  in
    case check_unsat' 0 arr rls earr f2 bnd [[]] of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr None => TextIO.print "s VERIFIED UNSAT\n"
    | Inr (Some l) => TextIO.output TextIO.stdErr "c empty clause not derived at end of proof\n"
  end`

val transformation_err_def = Define`
  transformation_err cl =
  concat[strlit"c transformation clause: ";print_clause cl;strlit"c not derived at end of proof\n"]`;

val _ = translate transformation_err_def;

val check_unsat_3 = (append_prog o process_topdecs) `
  fun check_unsat_3 f1 f2 f3 =
  case parse_dimacs_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv,(ncl,fml)) =>
  case parse_dimacs_full f3 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv2,(ncl2,fml2)) =>
  let val one = 1
      val arr = Array.array (2*ncl) None
      val arr = fill_arr arr one fml
      val bnd = 2*mv + 3
      val earr = Array.array bnd None
      val earr = fill_earliest earr one fml
      val rls = rev_enum_full 1 fml
  in
    case check_unsat' 0 arr rls earr f2 bnd fml2 of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr None => TextIO.print "s VERIFIED TRANSFORMATION\n"
    | Inr (Some cl) => TextIO.output TextIO.stdErr (transformation_err cl)
  end`

val check_cond_def = Define`
  check_cond i j pf = (i ≤ j ∧ j ≤ LENGTH pf)`

val _ = translate check_cond_def;

val success_str_def = Define`
  success_str cnf_md5 proof_md5 rng = expected_prefix cnf_md5 proof_md5 ^ rng ^ strlit "\n"`

val _ = translate success_str_def;

val parse_rng_or_check_def = Define`
  parse_rng_or_check rngc =
  if rngc = strlit "-check" then SOME (INL ())
  else OPTION_MAP INR (parse_rng rngc)`

val _ = translate parse_rng_or_check_def;

val _ = translate print_rng_def;

val check_unsat_4 = (append_prog o process_topdecs) `
  fun check_unsat_4 f1 f2 rng f3 =
  case parse_dimacs_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv,(ncl,fml)) =>
  case parse_proof_full f2 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr pf =>
  case parse_rng_or_check rng of
    None => TextIO.output TextIO.stdErr "c Unable to parse range specification a-b\n"
  | Some (Inl u) =>
    check_compose f1 f2 f3
  | Some (Inr (i,j)) =>
    if check_cond i j pf
    then
    let val one = 1
        val arr = Array.array (2*ncl) None
        val arr = fill_arr arr one fml
        val bnd = 2*mv + 3
        val earr = Array.array bnd None
        val earr = fill_earliest earr one fml
        val rls = rev_enum_full 1 fml
    in
      case check_lpr_range_arr f3 arr rls earr bnd (ncl+1) pf i j of
        Inl err => TextIO.output TextIO.stdErr err
      | Inr None =>
          (case md5_of (Some f1) of
            None => TextIO.output TextIO.stdErr (notfound_string f1)
          | Some cnf_md5 =>
            case md5_of (Some f2) of
              None => TextIO.output TextIO.stdErr (notfound_string f2)
            | Some proof_md5 => TextIO.print (success_str cnf_md5 proof_md5 (print_rng i j)))
      | Inr (Some cl) => TextIO.output TextIO.stdErr (transformation_err cl)
    end
    else TextIO.output TextIO.stdErr "c Invalid range specification: range a-b must satisfy a <= b <= num lines in proof file\n"`

val check_unsat = (append_prog o process_topdecs) `
  fun check_unsat u =
  case CommandLine.arguments () of
    [f1] => check_unsat_1 f1
  | [f1,f2] => check_unsat_2 f1 f2
  | [f1,f2,f3] => check_unsat_3 f1 f2 f3
  | [f1,f2,rng,f3] => check_unsat_4 f1 f2 rng f3
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

val check_unsat_1_sem_def = Define`
  check_unsat_1_sem fs f1 err =
  if inFS_fname fs f1 then
    (case parse_dimacs (all_lines fs f1) of
      NONE => add_stderr fs err
    | SOME fml => add_stdout fs (concat (print_dimacs fml)))
  else add_stderr fs err`

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
    simp[parse_dimacs_def]>>
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

val check_unsat_2_sem_def = Define`
  check_unsat_2_sem fs f1 f2 err =
  if inFS_fname fs f1 then
  (case parse_dimacs_toks (MAP toks (all_lines fs f1)) of
    NONE => add_stderr fs err
  | SOME (mv,ncl,fml) =>
    if inFS_fname fs f2 then
      case parse_lpr (all_lines fs f2) of
        SOME lpr =>
        let fmlls = enumerate 1 fml in
        let base = REPLICATE (2*ncl) NONE in
        let bnd = 2*mv+3 in
        let upd = FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) base fmlls in
        let earliest = FOLDL (λacc (i,v). update_earliest acc i v) (REPLICATE bnd NONE) fmlls in
          if check_lpr_unsat_list lpr upd (REVERSE (MAP FST fmlls)) (REPLICATE bnd w8z) earliest then
            add_stdout fs (strlit "s VERIFIED UNSAT\n")
          else
            add_stderr fs err
      | NONE => add_stderr fs err
    else add_stderr fs err)
  else add_stderr fs err`

val err_tac = xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>qexists_tac`err`>>xsimpl;

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
  xlet`POSTv v. &NUM 1 v * STDIO fs` >- (xlit>>xsimpl)>>
  drule fill_arr_spec>>
  drule fill_earliest_spec>>
  rw[]>>
  rpt(xlet_autop)>>
  (* help instantiate fill_arr_spec *)
  `LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (REPLICATE (2 * x1) NONE)
        (REPLICATE (2 * x1) (Conv (SOME (TypeStamp "None" 2)) []))` by
    simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
  rpt (xlet_autop) >>
  (* help instantiate fill_earliest_spec *)
  `LIST_REL (OPTION_TYPE NUM) (REPLICATE (2 * x0 + 3) NONE)
          (REPLICATE (2 * x0 + 3) (Conv (SOME (TypeStamp "None" 2)) []))` by
    simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
  rpt xlet_autop>>
  simp[check_lpr_unsat_list_def]>>
  qmatch_goalsub_abbrev_tac`check_lpr_list _ _ a b c d`>>
  xlet`POSTv v.
    STDIO fs *
    SEP_EXISTS err.
     &SUM_TYPE STRING_TYPE (OPTION_TYPE (LIST_TYPE INT))
      (if inFS_fname fs f2 then
         (case parse_lpr (all_lines fs f2) of
            NONE => INL err
          | SOME lpr =>
            (case check_lpr_list 0 lpr a b c d of
             NONE => INL err
           | SOME (fml', inds') => INR (contains_clauses_list_err fml' inds' [[]])))
       else INL err) v`
  >- (
    xapp_spec (GEN_ALL check_unsat'_spec)>>
    xsimpl>>
    asm_exists_tac>>simp[]>>
    fs[FILENAME_def,validArg_def]>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    simp[Once (METIS_PROVE [] ``P ∧ Q ∧ C ⇔ Q ∧ C ∧ P``)]>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    simp[Once (METIS_PROVE [] ``P ∧ Q ∧ C ⇔ Q ∧ C ∧ P``)]>>
    asm_exists_tac>>simp[]>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`[[]]`>>simp[LIST_TYPE_def]>>
    reverse CONJ_TAC>- (
      fs[parse_dimacs_toks_def]>>every_case_tac>>fs[]>>
      drule parse_dimacs_body_bound>>rw[]>>
      fs[Abbr`a`]>>
      rw[bounded_fml_def,EVERY_EL]>>
      `ALL_DISTINCT (MAP FST (enumerate 1 x))` by
        metis_tac[ALL_DISTINCT_MAP_FST_enumerate]>>
      drule FOLDL_resize_update_list_lookup>>
      disch_then drule>>
      strip_tac>>simp[]>>
      TOP_CASE_TAC>>fs[]>>
      drule ALOOKUP_MEM>>
      strip_tac>> drule MEM_enumerate_IMP>>
      qpat_x_assum`EVERY _ x` mp_tac>>
      simp[Once EVERY_MEM,Once EVERY_EL]>>
      rw[]>>
      first_x_assum drule>>
      disch_then drule>>
      simp[index_def]>>rw[]>>
      intLib.ARITH_TAC)>>
    fs[LENGTH_enumerate,rev_enum_full_rev_enumerate]>>
    metis_tac[])>>
  reverse TOP_CASE_TAC>>simp[]
  >- (fs[SUM_TYPE_def]>>xmatch>>err_tac)>>
  TOP_CASE_TAC>>fs[SUM_TYPE_def]
  >- (xmatch>>err_tac)>>
  Cases_on` check_lpr_list 0 x a b c d `>>fs[SUM_TYPE_def]
  >- (xmatch>>err_tac)>>
  Cases_on`x'`>>fs[]>>
  fs[contains_clauses_list_err]>>
  TOP_CASE_TAC>>fs[SUM_TYPE_def,OPTION_TYPE_def]
  >- (
    xmatch>>
    xapp_spec print_spec >> xsimpl
    \\ qexists_tac`emp`
    \\ qexists_tac`fs`>>xsimpl)
  >- (
    gs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS,OPTION_TYPE_def]>>
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qmatch_goalsub_abbrev_tac`_ _ err`>>
    qexists_tac`err`>>xsimpl)
QED

val check_unsat_3_sem_def = Define`
  check_unsat_3_sem fs f1 f2 f3 err =
  if inFS_fname fs f1 then
  (case parse_dimacs_toks (MAP toks (all_lines fs f1)) of
    NONE => add_stderr fs err
  | SOME (mv,ncl,fml) =>
  if inFS_fname fs f3 then
  (case parse_dimacs_toks (MAP toks (all_lines fs f3)) of
    NONE => add_stderr fs err
  | SOME (mv2,ncl2,fml2) =>
    if inFS_fname fs f2 then
      case parse_lpr (all_lines fs f2) of
        SOME lpr =>
        let fmlls = enumerate 1 fml in
        let base = REPLICATE (2*ncl) NONE in
        let bnd = 2*mv+3 in
        let upd = FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) base fmlls in
        let earliest = FOLDL (λacc (i,v). update_earliest acc i v) (REPLICATE bnd NONE) fmlls in
          if check_lpr_sat_equiv_list lpr upd (REVERSE (MAP FST fmlls)) (REPLICATE bnd w8z) earliest 0 fml2 then
            add_stdout fs (strlit "s VERIFIED TRANSFORMATION\n")
          else
            add_stderr fs err
      | NONE => add_stderr fs err
    else add_stderr fs err)
  else add_stderr fs err)
  else add_stderr fs err`

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
    SEP_EXISTS err. STDIO (check_unsat_3_sem fs f1 f2 f3 err))
Proof
  rw[]>>
  xcf "check_unsat_3" (get_ml_prog_state ())>>
  xlet_autop>>
  simp[check_unsat_3_sem_def]>>
  reverse TOP_CASE_TAC>>fs[]
  >- (
    fs[SUM_TYPE_def]>>xmatch>>
    err_tac)>>
  TOP_CASE_TAC>> fs[SUM_TYPE_def]
  >- (xmatch>> err_tac)>>
  PairCases_on`x`>>fs[SUM_TYPE_def,PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  reverse TOP_CASE_TAC>>fs[]
  >- (
    fs[SUM_TYPE_def]>>xmatch>>
    err_tac)>>
  TOP_CASE_TAC>> fs[SUM_TYPE_def]
  >- (xmatch>> err_tac)>>
  PairCases_on`x`>>fs[SUM_TYPE_def,PAIR_TYPE_def]>>
  xmatch>>
  xlet`POSTv v. &NUM 1 v * STDIO fs` >- (xlit>>xsimpl)>>
  drule fill_arr_spec>>
  drule fill_earliest_spec>>
  rw[]>>
  rpt(xlet_autop)>>
  (* help instantiate fill_arr_spec *)
  `LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (REPLICATE (2 * x1) NONE)
        (REPLICATE (2 * x1) (Conv (SOME (TypeStamp "None" 2)) []))` by
    simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
  rpt (xlet_autop) >>
  (* help instantiate fill_earliest_spec *)
  `LIST_REL (OPTION_TYPE NUM) (REPLICATE (2 * x0 + 3) NONE)
          (REPLICATE (2 * x0 + 3) (Conv (SOME (TypeStamp "None" 2)) []))` by
    simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
  rpt xlet_autop>>
  simp[check_lpr_sat_equiv_list_def]>>
  qmatch_goalsub_abbrev_tac`check_lpr_list _ _ a b c d`>>
  xlet`POSTv v.
    STDIO fs *
    SEP_EXISTS err.
     &SUM_TYPE STRING_TYPE (OPTION_TYPE (LIST_TYPE INT))
      (if inFS_fname fs f2 then
         (case parse_lpr (all_lines fs f2) of
            NONE => INL err
          | SOME lpr =>
            (case check_lpr_list 0 lpr a b c d of
             NONE => INL err
           | SOME (fml', inds') => INR (contains_clauses_list_err fml' inds' x2')))
       else INL err) v`
  >- (
    xapp_spec (GEN_ALL check_unsat'_spec)>>
    xsimpl>>
    asm_exists_tac>>simp[]>>
    fs[FILENAME_def,validArg_def]>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    simp[Once (METIS_PROVE [] ``P ∧ Q ∧ C ⇔ Q ∧ C ∧ P``)]>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    simp[Once (METIS_PROVE [] ``P ∧ Q ∧ C ⇔ Q ∧ C ∧ P``)]>>
    asm_exists_tac>>simp[]>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`x2'`>>simp[LIST_TYPE_def]>>
    reverse CONJ_TAC>- (
      fs[parse_dimacs_toks_def]>>every_case_tac>>fs[]>>
      drule parse_dimacs_body_bound>>rw[]>>
      fs[Abbr`a`]>>
      rw[bounded_fml_def,EVERY_EL]>>
      `ALL_DISTINCT (MAP FST (enumerate 1 x'))` by
        metis_tac[ALL_DISTINCT_MAP_FST_enumerate]>>
      drule FOLDL_resize_update_list_lookup>>
      disch_then drule>>
      strip_tac>>simp[]>>
      TOP_CASE_TAC>>fs[]>>
      drule ALOOKUP_MEM>>
      strip_tac>> drule MEM_enumerate_IMP>>
      qpat_x_assum`EVERY _ x'` mp_tac>>
      simp[Once EVERY_MEM,Once EVERY_EL]>>
      rw[]>>
      first_x_assum drule>>
      disch_then drule>>
      simp[index_def]>>rw[]>>
      intLib.ARITH_TAC)>>
    fs[LENGTH_enumerate,rev_enum_full_rev_enumerate]>>
    metis_tac[])>>
  reverse TOP_CASE_TAC>>simp[]
  >- (fs[SUM_TYPE_def]>>xmatch>>err_tac)>>
  TOP_CASE_TAC>>fs[SUM_TYPE_def]
  >- (xmatch>>err_tac)>>
  Cases_on`check_lpr_list 0 x a b c d`>>gs[SUM_TYPE_def]
  >- (xmatch>>err_tac)>>
  Cases_on`x'`>>fs[SUM_TYPE_def]>>
  fs[contains_clauses_list_err,OPTION_TYPE_def]>>
  TOP_CASE_TAC>>fs[]
  >- (
    fs[OPTION_TYPE_def]>>xmatch>>
    xapp_spec print_spec >> xsimpl
    \\ qexists_tac`emp`
    \\ qexists_tac`fs`>>xsimpl)>>
  gs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS,OPTION_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xapp_spec output_stderr_spec \\ xsimpl>>
  qexists_tac`emp`>>xsimpl>>
  asm_exists_tac>>
  qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qmatch_goalsub_abbrev_tac`_ _ err`>>
  qexists_tac`err`>>xsimpl
QED

val check_unsat_4_sem_def = Define`
  check_unsat_4_sem fs f1 f2 rng f3 err =
  if inFS_fname fs f1 then
  (case parse_dimacs_toks (MAP toks (all_lines fs f1)) of
    NONE => add_stderr fs err
  | SOME (mv,ncl,fml) =>
  if inFS_fname fs f2 then
  (case parse_proof_toks (MAP toks (all_lines fs f2)) of
    NONE => add_stderr fs err
  | SOME pf =>
  (case parse_rng_or_check rng of
    NONE => add_stderr fs err
  | SOME (INL ()) =>
    if inFS_fname fs f3 then
      case check_lines (implode (md5 (THE (file_content fs f1)))) (implode (md5 (THE (file_content fs f2))))
        (all_lines fs f3) (LENGTH pf) of
        INL _ => add_stderr fs err
      | INR s => add_stdout fs s
    else
      add_stderr fs err
  | SOME (INR (i,j)) =>
    if i ≤ j ∧ j ≤ LENGTH pf ∧ inFS_fname fs f3 then
      case parse_lpr (all_lines fs f3) of
        SOME lpr =>
        let fmlls = enumerate 1 fml in
        let base = REPLICATE (2*ncl) NONE in
        let bnd = 2*mv+3 in
        let upd = FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) base fmlls in
        let earliest = FOLDL (λacc (i,v). update_earliest acc i v) (REPLICATE bnd NONE) fmlls in
          if check_lpr_range_list lpr upd (REVERSE (MAP FST fmlls)) earliest bnd (ncl+1) pf i j then
            add_stdout fs (success_str (implode (md5 (THE (file_content fs f1)))) (implode (md5 (THE (file_content fs f2)))) (print_rng i j))
          else
            add_stderr fs err
      | NONE => add_stderr fs err
    else add_stderr fs err))
  else add_stderr fs err)
  else add_stderr fs err`

Theorem parse_proof_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_proof_full"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. ((SUM_TYPE STRING_TYPE (LIST_TYPE LPR_STEP_TYPE))
    (if inFS_fname fs f then
    (case parse_proof_toks (MAP toks (all_lines fs f)) of
      NONE => INL err
    | SOME x => INR x)
    else INL err) v)) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_proof_full"(get_ml_prog_state())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse (Cases_on`consistentFS fs`) >- (
    fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def]
    \\ xpull \\ metis_tac[]) >>
  xlet`(POSTv sv. &OPTION_TYPE (LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
            (if inFS_fname fs f then
               SOME(MAP (MAP tokenize o tokens blanks) (all_lines fs f))
             else NONE) sv * STDIO fs)`
  >- (
    xapp_spec b_inputAllTokensFrom_spec_specialize >>
    xsimpl>>
    fs[FILENAME_def,validArg_def])>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    xlet_autop>>
    `toks = (MAP tokenize ∘ tokens blanks)` by
      metis_tac[toks_def,ETA_AX,o_DEF]>>
    rw[]>> TOP_CASE_TAC>>
    fs[OPTION_TYPE_def]
    >- (
      xmatch >>
      xlet_autop>>
      xcon>>xsimpl>>
      simp[SUM_TYPE_def]>>metis_tac[])>>
    xmatch>>xcon>>
    xsimpl>>
    simp[SUM_TYPE_def])
  >>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def]>>metis_tac[]
QED

Theorem inFS_fname_file_content:
  consistentFS fs ∧ inFS_fname fs f ⇒ ∃c. file_content fs f = SOME c
Proof
  rw[consistentFS_def,inFS_fname_def]>>simp[]>>
  first_x_assum drule>>simp[file_content_def]>>
  metis_tac[ALOOKUP_NONE,option_CASES]
QED

Theorem all_lines_lines_of:
  file_content fs f = SOME c ⇒
  all_lines fs f = lines_of (strlit c)
Proof
  fs[file_content_def]>>
  rw[all_lines_def,lines_of_def]>>
  every_case_tac>>fs[]
QED

Theorem parse_proof_toks_aux_LENGTH:
  ∀ls acc x.
  parse_proof_toks_aux ls acc = SOME x ⇒
  LENGTH x = LENGTH ls + LENGTH acc
Proof
  Induct>>simp[parse_proof_toks_aux_def]>>
  rw[]>>
  every_case_tac>>fs[]>>
  first_x_assum drule>>
  simp[]
QED

Theorem parse_proof_toks_LENGTH:
  parse_proof_toks ls = SOME x ⇒ LENGTH x = LENGTH ls
Proof
  rw[parse_proof_toks_def]>>
  drule parse_proof_toks_aux_LENGTH>>simp[]
QED

Theorem check_unsat_4_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  STRING_TYPE f2 f2v ∧ validArg f2 ∧
  STRING_TYPE f3 f3v ∧ validArg f3 ∧
  STRING_TYPE rng rngv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_4"(get_ml_prog_state()))
    [f1v; f2v; rngv; f3v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS err. STDIO (check_unsat_4_sem fs f1 f2 rng f3 err))
Proof
  rw[]>>
  xcf "check_unsat_4" (get_ml_prog_state ())>>
  reverse (Cases_on`consistentFS fs`)
    >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[]) >>
  xlet_autop>>
  simp[check_unsat_4_sem_def]>>
  reverse TOP_CASE_TAC>>fs[]
  >- (
    fs[SUM_TYPE_def]>>xmatch>>
    err_tac)>>
  TOP_CASE_TAC>> fs[SUM_TYPE_def]
  >- (xmatch>> err_tac)>>
  PairCases_on`x`>>fs[SUM_TYPE_def,PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  reverse TOP_CASE_TAC>>fs[]
  >- (
    fs[SUM_TYPE_def]>>xmatch>>
    err_tac)>>
  TOP_CASE_TAC>> fs[SUM_TYPE_def]
  >- (xmatch>> err_tac)>>
  xmatch>>
  xlet_autop>>
  TOP_CASE_TAC >> fs[OPTION_TYPE_def]
  >- (xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`strlit"c Unable to parse range specification a-b\n"`>>xsimpl)>>
  TOP_CASE_TAC >>fs[SUM_TYPE_def]
  >- (
    (* -check case *)
    xmatch>>
    reverse TOP_CASE_TAC
    >- (
      xapp_spec check_compose_spec_fail>>
      xsimpl>>
      fs[FILENAME_def,validArg_def]>>
      asm_exists_tac>>simp[]>>
      asm_exists_tac>>simp[]>>
      asm_exists_tac>>simp[]>>
      fs[file_content_def,inFS_fname_def]>>
      TOP_CASE_TAC>>fs[])>>
    xapp>>xsimpl>>fs[]>>
    asm_exists_tac>>simp[]>>
    imp_res_tac inFS_fname_file_content>>fs[]>>rw[]>>
    fs[FILENAME_def,validArg_def]>>
    asm_exists_tac>> simp[]>>
    qpat_x_assum`_ _ f3 = _` assume_tac>>
    asm_exists_tac>> simp[]>>
    qpat_x_assum`_ _ f2 = _` assume_tac>>
    asm_exists_tac>> simp[]>>
    qexists_tac`emp`>>xsimpl>>rw[]>>
    (* relate all_lines and lines_of *)
    imp_res_tac all_lines_lines_of>>simp[]>>
    gs[]>>
    drule parse_proof_toks_LENGTH>>
    simp[]>>
    TOP_CASE_TAC>>simp[]>>strip_tac
    >- (qexists_tac`x'`>>xsimpl)>>
    xsimpl)>>
  PairCases_on`y`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  fs[check_cond_def]>>
  reverse xif
  >- (
    fs[]>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`strlit"c Invalid range specification: range a-b must satisfy a <= b <= num lines in proof file\n"`>>xsimpl)>>
  xlet`POSTv v. &NUM 1 v * STDIO fs` >- (xlit>>xsimpl)>>
  drule fill_arr_spec>>
  drule fill_earliest_spec>>
  strip_tac >> strip_tac>>
  rpt(xlet_autop)>>
  (* help instantiate fill_arr_spec *)
  `LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (REPLICATE (2 * x1) NONE)
        (REPLICATE (2 * x1) (Conv (SOME (TypeStamp "None" 2)) []))` by
    simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
  rpt (xlet_autop) >>
  (* help instantiate fill_earliest_spec *)
  `LIST_REL (OPTION_TYPE NUM) (REPLICATE (2 * x0 + 3) NONE)
          (REPLICATE (2 * x0 + 3) (Conv (SOME (TypeStamp "None" 2)) []))` by
    simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
  rpt xlet_autop >>
  xlet_auto
  >- (
    xsimpl>>
    CONJ_TAC >-(
      fs[parse_dimacs_toks_def]>>every_case_tac>>fs[]>>
      drule parse_dimacs_body_bound>>rw[]>>
      rw[bounded_fml_def,EVERY_EL]>>
      fs[validArg_def]>>
      `ALL_DISTINCT (MAP FST (enumerate 1 x'))` by
        metis_tac[ALL_DISTINCT_MAP_FST_enumerate]>>
      drule FOLDL_resize_update_list_lookup>>
      disch_then drule>>
      strip_tac>>simp[]>>
      TOP_CASE_TAC>>fs[]>>
      drule ALOOKUP_MEM>>
      strip_tac>> drule MEM_enumerate_IMP>>
      qpat_x_assum`EVERY _ x'` mp_tac>>
      simp[Once EVERY_MEM,Once EVERY_EL]>>
      rw[]>>
      first_x_assum drule>>
      disch_then drule>>
      simp[index_def]>>rw[]>>
      intLib.ARITH_TAC)>>
    rw[]>>rpt(pairarg_tac>>fs[])>>
    metis_tac[])>>
  rpt (pairarg_tac>>fs[])>>
  qpat_x_assum`SUM_TYPE _ _ _ _` mp_tac>>
  reverse IF_CASES_TAC >-(
    simp[SUM_TYPE_def]>>strip_tac>>xmatch>>
    err_tac)>>
  TOP_CASE_TAC>>simp[] >-(
    simp[SUM_TYPE_def]>>strip_tac>>xmatch>>
    err_tac)>>
  TOP_CASE_TAC>>simp[] >-(
    simp[SUM_TYPE_def]>>strip_tac>>xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    asm_exists_tac>>simp[]>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    simp[check_lpr_range_list_def]>>fs[]>>
    simp[check_lpr_sat_equiv_list_def]>>
    qexists_tac`err`>>xsimpl>>
    fs[LENGTH_enumerate,rev_enum_full_rev_enumerate]>>
    xsimpl)>>
  TOP_CASE_TAC>>simp[check_lpr_range_list_def,check_lpr_sat_equiv_list_def]>>
  simp[SUM_TYPE_def]>>strip_tac>>
  fs[LENGTH_enumerate,rev_enum_full_rev_enumerate]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def,SUM_TYPE_def]>> xmatch
  >- (
    xlet_autop>>
    xlet ‘(POSTv retv. STDIO fs * &OPTION_TYPE STRING_TYPE
            (OPTION_MAP (implode ∘ md5) (file_content fs f1)) retv)’
    >-
      (xapp_spec md5_of_SOME \\ fs [std_preludeTheory.OPTION_TYPE_def, FILENAME_def,validArg_def])>>
    imp_res_tac inFS_fname_file_content>>fs[]>>rw[]>>
    gvs [std_preludeTheory.OPTION_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    xlet ‘(POSTv retv. STDIO fs * &OPTION_TYPE STRING_TYPE
            (OPTION_MAP (implode ∘ md5) (file_content fs f2)) retv)’
    >-
      (xapp_spec md5_of_SOME \\ fs [std_preludeTheory.OPTION_TYPE_def, FILENAME_def,validArg_def])>>
    gvs [std_preludeTheory.OPTION_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    xlet_autop>>
    xapp>>xsimpl>>
    qexists_tac`emp`>>
    asm_exists_tac>>
    qexists_tac`fs`>>xsimpl)>>
  xlet_autop>>
  xapp_spec output_stderr_spec \\ xsimpl>>
  qexists_tac`emp`>>xsimpl>>
  asm_exists_tac>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`transformation_err err2`>>xsimpl
QED

val check_unsat_sem_def = Define`
  check_unsat_sem cl fs err =
  case TL cl of
    [f1] => check_unsat_1_sem fs f1 err
  | [f1;f2] => check_unsat_2_sem fs f1 f2 err
  | [f1;f2;f3] => check_unsat_3_sem fs f1 f2 f3 err
  | [f1;f2;rng;f3] => check_unsat_4_sem fs f1 f2 rng f3 err
  | _ => add_stderr fs err`

Theorem check_unsat_spec:
   hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"check_unsat"(get_ml_prog_state()))
     [Conv NONE []]
     (COMMANDLINE cl * STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv *
     COMMANDLINE cl * SEP_EXISTS err. STDIO (check_unsat_sem cl fs err))
Proof
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
    fs[wfcl_def,Abbr`cl`]>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    xsimpl>>rw[]>>
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
    xapp>>xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    fs[wfcl_def,Abbr`cl`]>>
    qexists_tac`fs`>>
    qexists_tac`h'''`>>
    qexists_tac`h''`>>
    qexists_tac`h'`>>
    xsimpl>>rw[]>>
    qexists_tac`x`>>xsimpl)
  >- (
    xapp>>xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    fs[wfcl_def,Abbr`cl`]>>
    qexists_tac`h'''`>>
    qexists_tac`fs`>>
    qexists_tac`h''''`>>
    qexists_tac`h''`>>
    qexists_tac`h'`>>
    xsimpl>>rw[]>>
    qexists_tac`x`>>xsimpl)
  >> (
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
  \\ rw[check_unsat_sem_def,check_unsat_1_sem_def,check_unsat_2_sem_def,check_unsat_3_sem_def,check_unsat_4_sem_def]
  \\ every_case_tac
  \\ simp[GSYM add_stdo_with_numchars,with_same_numchars]
QED

local

val name = "check_unsat"
val (sem_thm,prog_tm) =
  whole_prog_thm (get_ml_prog_state()) name (UNDISCH check_unsat_whole_prog_spec2)
val check_unsat_prog_def = Define`check_unsat_prog = ^prog_tm`;

in

Theorem check_unsat_semantics =
  sem_thm
  |> REWRITE_RULE[GSYM check_unsat_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[GSYM CONJ_ASSOC,AND_IMP_INTRO];

end

Theorem fml_rel_check_lpr_list:
  ∀steps mindel fml fmlls inds fmlls' inds' Clist earliest.
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  SORTED $>= inds ∧
  EVERY ($= w8z) Clist ∧ wf_fml fml ∧
  earliest_rel fmlls earliest ∧
  EVERY wf_lpr steps ∧
  check_lpr_list mindel steps fmlls inds Clist earliest = SOME (fmlls', inds') ⇒
  ind_rel fmlls' inds' ∧
  ∃fml'. check_lpr mindel steps fml = SOME fml' ∧
    fml_rel fml' fmlls'
Proof
  Induct>>fs[check_lpr_list_def,check_lpr_def]>>
  ntac 9 strip_tac>>
  ntac 4 (TOP_CASE_TAC>>fs[])>>
  strip_tac>>
  drule  fml_rel_check_lpr_step_list>>
  rpt (disch_then drule)>>
  disch_then (qspecl_then [`h`,`mindel`] mp_tac)>> simp[]>>
  strip_tac>>
  simp[]>>
  first_x_assum match_mp_tac>>
  asm_exists_tac>>fs[]>>
  asm_exists_tac>>fs[]>>
  asm_exists_tac>>fs[]>>
  qexists_tac`r`>>fs[]>>
  match_mp_tac check_lpr_step_wf_fml>>
  metis_tac[]
QED

Theorem check_lpr_sat_equiv_list_sound:
  check_lpr_sat_equiv_list lpr
    (FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) (REPLICATE n NONE) (enumerate k fml))
    (REVERSE (MAP FST (enumerate k fml)))
    Clist
    (FOLDL (λacc (i,v). update_earliest acc i v) (REPLICATE bnd NONE) (enumerate k fml))
    0 fml2 ∧
  EVERY wf_clause fml ∧ EVERY wf_lpr lpr ∧ EVERY ($= w8z) Clist ⇒
  satisfiable (interp fml) ⇒
  satisfiable (interp fml2)
Proof
  rw[check_lpr_sat_equiv_list_def]>>
  every_case_tac>>fs[]>>
  assume_tac (fml_rel_FOLDL_resize_update_list |> INST_TYPE [alpha |-> ``:int list``])>>
  assume_tac (ind_rel_FOLDL_resize_update_list |> INST_TYPE [alpha |-> ``:int list``])>>
  assume_tac earliest_rel_FOLDL_resize_update_list>>
  drule fml_rel_check_lpr_list>>
  `SORTED $>= (REVERSE (MAP FST (enumerate k fml)))` by
    (DEP_REWRITE_TAC [SORTED_REVERSE]>>
    simp[transitive_def,MAP_FST_enumerate]>>
    match_mp_tac SORTED_weaken>>
    qexists_tac `$<`>>simp[]>>
    metis_tac[SORTED_GENLIST_PLUS])>>
  drule wf_fml_build_fml>>
  disch_then (qspec_then`k` assume_tac)>>
  simp[]>>
  rpt(disch_then drule)>>
  strip_tac>>
  match_mp_tac (check_lpr_sat_equiv_fml |> SIMP_RULE std_ss [AND_IMP_INTRO] |> GEN_ALL)>>
  simp[check_lpr_sat_equiv_def]>>
  asm_exists_tac>>simp[]>>
  asm_exists_tac>>simp[]>>
  qexists_tac`0`>>simp[]>>
  qexists_tac`k`>>simp[]>>
  metis_tac[fml_rel_contains_clauses_list]
QED

Theorem check_lpr_range_list_sound:
  check_lpr_range_list
    lpr
    (FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) (REPLICATE n NONE) (enumerate k fml))
    (REVERSE (MAP FST (enumerate k fml)))
    (FOLDL (λacc (i,v). update_earliest acc i v) (REPLICATE bnd NONE) (enumerate k fml))
    m (LENGTH fml + k) pf i j ∧
  EVERY wf_clause fml ∧ EVERY wf_lpr lpr ∧ EVERY wf_proof pf ⇒
  satisfiable (interp (run_proof fml (TAKE i pf))) ⇒
  satisfiable (interp (run_proof fml (TAKE j pf)))
Proof
  rw[]>>
  drule fml_rel_check_lpr_range_list>>
  assume_tac (fml_rel_FOLDL_resize_update_list |> INST_TYPE [alpha |-> ``:int list``])>>
  disch_then drule>>
  assume_tac (ind_rel_FOLDL_resize_update_list |> INST_TYPE [alpha |-> ``:int list``])>>
  assume_tac earliest_rel_FOLDL_resize_update_list>>
  simp[]>>
  impl_tac >-(
    simp[wf_fml_build_fml]>>
    simp[transitive_def,MAP_FST_enumerate]>>
    CONJ_TAC>-(
      `ALL_DISTINCT (MAP FST (enumerate k fml))` by
        fs[ALL_DISTINCT_MAP_FST_enumerate]>>
      drule FOLDL_resize_update_list_lookup>>
      simp[list_lookup_def]>>
      rw[]>>
      pop_assum mp_tac>>IF_CASES_TAC>>simp[]>>
      first_x_assum(qspecl_then [`n`,`x`] mp_tac)>>
      simp[]>>
      simp[ALOOKUP_enumerate]>>
      every_case_tac>>fs[])>>
    DEP_REWRITE_TAC [SORTED_REVERSE]>>
    simp[transitive_def,MAP_FST_enumerate]>>
    match_mp_tac SORTED_weaken>>
    qexists_tac `$<`>>simp[]>>
    metis_tac[SORTED_GENLIST_PLUS])>>
  strip_tac>>
  drule check_lpr_range_sound>>
  disch_then match_mp_tac>>
  asm_exists_tac>>simp[]>>
  simp[Once CONJ_COMM]>>
  asm_exists_tac>>simp[]>>
  simp[Once CONJ_COMM]>>
  asm_exists_tac>>simp[]
QED

val _ = export_theory();
