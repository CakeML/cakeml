(*
  Add PBF parsing and wrap around the PBP parser
*)
open preamble basis pb_parseTheory pbc_normaliseTheory npbc_parseProgTheory;

val _ = new_theory "npbc_fullProg"

val _ = translation_extends"npbc_parseProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

Definition usage_string_def:
  usage_string = strlit "Usage: cake_pb <OPB format formula file> <Proof file>\n"
End

val r = translate usage_string_def;

(* additional translation for .pbf parsing *)
val r = translate tokenize_def;
val r = translate nocomment_line_def;

val nocomment_line_side_def = definition"nocomment_line_side_def";
val nocomment_line_side = Q.prove(
  `∀x. nocomment_line_side x <=> T`,
  rw[nocomment_line_side_def])
  |> update_precondition;

val r = translate strip_terminator_def;

val strip_terminator_side_def = definition"strip_terminator_side_def";
val strip_terminator_side = Q.prove(
  `∀x. strip_terminator_side x <=> T`,
  rw[strip_terminator_side_def])
  |> update_precondition;

val r = translate flip_coeffs_def;
val r = translate pbc_ge_def;
val r = translate normalise_def;

val r = translate convert_pbf_def;
val r = translate full_normalise_def;

val r = translate parse_op_def;
val r = translate parse_constraint_def;
val r = translate parse_constraints_def;

val r = translate parse_pbf_toks_def;

Definition noparse_string_def:
  noparse_string f s = concat[strlit"c Input file: ";f;strlit" unable to parse in format: "; s;strlit"\n"]
End

val r = translate noparse_string_def;

Definition notfound_string_def:
  notfound_string f = concat[strlit"c Input file: ";f;strlit" no such file or directory\n"]
End

val r = translate notfound_string_def;

val parse_pbf_full = (append_prog o process_topdecs) `
  fun parse_pbf_full f =
  (case TextIO.b_inputAllTokensFrom f blanks tokenize of
    None => Inl (notfound_string f)
  | Some lines =>
  (case parse_pbf_toks lines of
    None => Inl (noparse_string f "OPB")
  | Some x => Inr x))`

val tokenize_v_thm = theorem "tokenize_v_thm";

val b_inputAllTokensFrom_spec_specialize =
  b_inputAllTokensFrom_spec
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> REWRITE_RULE [blanks_v_thm,tokenize_v_thm] ;

Theorem parse_pbf_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_pbf_full"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. (SUM_TYPE STRING_TYPE (LIST_TYPE (PAIR_TYPE PBC_PBOP_TYPE (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE))) INT)))
    (if inFS_fname fs f then
    (case parse_pbf_toks (MAP toks (all_lines fs f)) of
      NONE => INL err
    | SOME x => INR x)
    else INL err) v)) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_pbf_full"(get_ml_prog_state())>>
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
    fs[FILENAME_def,validArg_def]>>
    EVAL_TAC)>>
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
    simp[SUM_TYPE_def]) >>
  xlet_autop>>
  xcon>>xsimpl>>
  simp[SUM_TYPE_def]>>metis_tac[]
QED

Definition result_string_def:
  result_string b =
   if b
   then INR (strlit "Verified\n")
   else INL (strlit "Proof checking succeeded but did not derive contradiction\n")
End

val r = translate result_string_def;

val check_unsat' = process_topdecs `
  fun check_unsat' fml inds mindel id fname =
  let
    val fd = TextIO.b_openIn fname
    val u = (check_header fd;
      case check_unsat'' fd 1 fml inds mindel id of
        (fml', (b, (id',inds'))) => result_string b
      ) handle Fail s => Inl s
    val close = TextIO.b_closeIn fd;
  in
    u
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)` |> append_prog;

(*
Definition parse_pbp_def:
  parse_pbp strs =
  case MAP toks_fast strs of
    s::ss =>
    if parse_header_line_fast s then
      parse_tops ss
    else NONE
  | [] => NONE
End *)

(* Dummy spec *)
Theorem check_unsat'_spec:
  SPTREE_SPT_TYPE PB_CONSTRAINT_NPBC_TYPE fml fmlv ∧ NUM id idv ∧
  FILENAME f fv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat'"(get_ml_prog_state()))
  [fmlv; idv; fv]
  (STDIO fs)
  (POSTv v.
    STDIO fs *
    SEP_EXISTS err.
      &(SUM_TYPE STRING_TYPE (OPTION_TYPE (LIST_TYPE INT)))
      (if inFS_fname fs f then
        ARB
      else
        INL err
      ) v)
Proof
  cheat
  (*
  xcf"check_unsat'"(get_ml_prog_state()) >>
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
  xlet`POSTv resv.
        SEP_EXISTS k rest.
         STDIO (forwardFD fs (nextFD fs) k) *
         INSTREAM_LINES (nextFD fs) is rest (forwardFD fs (nextFD fs) k) *
         &(
           ARB
           (* case
             parse_and_run_file_list (all_lines fs f) mindel fmlls ls (REPLICATE n w8z) earliest
           of
             NONE => resv = Conv (SOME (TypeStamp "Inl" 23)) [v0] ∧ ∃s. STRING_TYPE s v0
           | SOME(fmlls',inds') =>
             resv = Conv (SOME (TypeStamp "Inr" 23)) [Conv NONE [v1; v2]] ∧
             v1 = fmlv' ∧
             LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls' fmllsv' ∧ LIST_TYPE NUM inds' v2 *)
         )`
  >-
    cheat
  >>
  cheat *)
QED

val _ = translate miscTheory.enumerate_def;

val fill_arr = process_topdecs`
  fun fill_arr arr ls =
    case ls of [] => arr
    | (x::xs) =>
    case x of (i,v) =>
      fill_arr (Array.updateResize arr None i (Some v)) xs` |> append_prog

(*
Theorem fill_arr_spec:
  ∀ls lsv arrv arrls arrlsv.
  LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT)) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) arrls arrlsv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"fill_arr"(get_ml_prog_state()))
  [arrv; lsv]
  (ARRAY arrv arrlsv)
  (POSTv resv.
  SEP_EXISTS arrlsv'. ARRAY resv arrlsv' *
    & LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FOLDL (λacc (i,v).  update_resize acc NONE (SOME v) i) arrls ls) arrlsv')
Proof
  Induct>>rw[]>>
  xcf "fill_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>
  xmatch
  >- (xvar>>xsimpl)>>
  Cases_on`h`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop >>
  xlet_auto >>
  xapp>>
  fs[]>>
  match_mp_tac LIST_REL_update_resize>>fs[]>>
  simp[OPTION_TYPE_def]
QED
val _ = translate build_fml_def;

Definition build_def:
  build pbf = build_fml 1 (full_normalise pbf) LN
End

val r = translate build_def;

val check_pbp = process_topdecs`
  fun check_pbp pbf fname =
    case build pbf of (fml,id) =>
    check_unsat' fml id fname` |> append_prog;
*)

val check_unsat_2 = (append_prog o process_topdecs) `
  fun check_unsat_2 f1 f2 =
  case parse_pbf_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr fml =>
  let val ls = enumerate 1 (full_normalise fml)
      val id = List.length ls + 1
      val arr = Array.array (2*id) None
      val arr = fill_arr arr ls
      val inds = []
      val mindel = 0
  in
    case check_unsat' arr inds mindel id f2 of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr s => TextIO.print s
  end`

val check_unsat_2_sem_def = Define`
  check_unsat_2_sem fs f1 f2 err =
  if inFS_fname fs f1 then
  (case parse_pbf_toks (MAP toks (all_lines fs f1)) of
    NONE => add_stderr fs err
  | SOME pbf =>
    if inFS_fname fs f2 then
      ARB (* case parse_pbp_toks (MAP toks (all_lines fs f2)) of
        SOME pbp =>
        ARB
        (* case check_pbp pbf pbp of
          INL _ => add_stderr fs err
        | INR succ => add_stdout fs succ *)
      | NONE => add_stderr fs err *)
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
  cheat
  (*
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
  xmatch>>
  xlet_autop>>
  reverse TOP_CASE_TAC>>fs[]
  >- (
    fs[SUM_TYPE_def]>>xmatch>>
    err_tac)>>
  TOP_CASE_TAC>> fs[SUM_TYPE_def]
  >- (xmatch>>err_tac)>>
  xmatch>>
  xlet_autop>>
  TOP_CASE_TAC >> fs[SUM_TYPE_def]
  >- (xmatch >>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>qexists_tac`x''`>>xsimpl)>>
  xmatch>>
  xapp_spec print_spec >> xsimpl
  \\ qexists_tac`emp`
  \\ asm_exists_tac \\ xsimpl
  \\ qexists_tac`fs`>>xsimpl*)
QED

val check_unsat = (append_prog o process_topdecs) `
  fun check_unsat u =
  case CommandLine.arguments () of
    [f1,f2] => check_unsat_2 f1 f2
  | _ => TextIO.output TextIO.stdErr usage_string`

val check_unsat_sem_def = Define`
  check_unsat_sem cl fs err =
  case TL cl of
  | [f1;f2] => check_unsat_2_sem fs f1 f2 err
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
    xapp_spec output_stderr_spec \\ xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `usage_string` >> simp [theorem "usage_string_v_thm"] >>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>qexists_tac`usage_string`>>xsimpl)
  >- (
    xapp>>xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    fs[wfcl_def,Abbr`cl`]>>
    qexists_tac`fs`>>xsimpl>>
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
  cheat
  (* rw[basis_ffiTheory.whole_prog_spec2_def]
  \\ match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH check_unsat_spec))))
  \\ xsimpl
  \\ rw[PULL_EXISTS]
  \\ qexists_tac`check_unsat_sem cl fs x`
  \\ qexists_tac`x`
  \\ xsimpl
  \\ rw[check_unsat_sem_def,check_unsat_2_sem_def]
  \\ every_case_tac
  \\ simp[GSYM add_stdo_with_numchars,with_same_numchars] *)
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

val _ = export_theory();
