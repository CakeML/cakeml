(*
  Subgraph isomorphism encoder and checker
*)
open preamble basis subgraph_isoTheory graph_basicTheory npbc_parseProgTheory;
open cfLib basisFunctionsLib;

val _ = new_theory "subgraph_isoProg";

val _ = translation_extends "npbc_parseProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

Definition notfound_string_def:
  notfound_string f = concat[strlit"c Input file: ";f;strlit" no such file or directory\n"]
End

val r = translate notfound_string_def;

val noparse_string_def = Define`
  noparse_string f s = concat[strlit"c Input file: ";f;strlit" unable to parse in format: "; s;strlit"\n"]`;

val r = translate noparse_string_def;

val _ = translate mlintTheory.fromNatString_def;
val _ = translate tokenize_num_def;

val _ = translate parse_num_list_def;
val _ = translate parse_edges_def;
val _ = translate parse_lad_toks_def;

val _ = translate lrnext_def;
val _ = translate foldi_def;
val _ = translate toAList_def;

Theorem check_good_edges_inner_thm:
  check_good_edges_inner u v es ⇔
       case lookup u es of NONE => F | SOME edges => MEMBER v edges
Proof
  fs[check_good_edges_inner_def,MEMBER_INTRO]>>
  metis_tac[]
QED

val _ = translate check_good_edges_inner_thm;

val _ = translate (check_good_edges_def |> SIMP_RULE std_ss [GSYM check_good_edges_inner_def]);
val _ = translate check_good_graph_def;

val parse_lad = (append_prog o process_topdecs) `
  fun parse_lad f =
  (case TextIO.b_inputAllTokensFrom f blanks tokenize_num of
    None => Inl (notfound_string f)
  | Some lines =>
  (case parse_lad_toks lines of
    None => Inl (noparse_string f "LAD")
  | Some x =>
    if check_good_graph x then
      Inr x
    else Inl ("Input graph file (" ^ f ^ ") fails undirectedness check\n")))`

val tokenize_num_v_thm = theorem "tokenize_num_v_thm";

val b_inputAllTokensFrom_spec_specialize =
  b_inputAllTokensFrom_spec
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`graph_basic$tokenize_num`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_num_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE NUM`
  |> REWRITE_RULE [blanks_v_thm,tokenize_num_v_thm] ;

Definition get_graph_def:
  get_graph fs f =
  if inFS_fname fs f then
    (case parse_lad (all_lines fs f) of
      NONE => NONE
    | SOME x =>
      if check_good_graph x then SOME x
      else NONE)
  else NONE
End

Theorem parse_lad_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_lad"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃res.
      SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (SPTREE_SPT_TYPE (LIST_TYPE NUM))) res v ∧
      case res of
        INR g => get_graph fs f = SOME g
      | INL err => get_graph fs f = NONE
      )
      * STDIO fs)
Proof
  rw[]>>
  xcf"parse_lad"(get_ml_prog_state())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse (Cases_on`consistentFS fs`) >- (
    fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def]
    \\ xpull \\ metis_tac[]) >>
  xlet`(POSTv sv. &OPTION_TYPE (LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE NUM)))
            (if inFS_fname fs f then
               SOME(MAP (MAP tokenize_num o tokens blanks) (all_lines fs f))
             else NONE) sv * STDIO fs)`
  >- (
    xapp_spec b_inputAllTokensFrom_spec_specialize >>
    xsimpl>>
    fs[FILENAME_def,validArg_def]>>
    EVAL_TAC)>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>
  fs[OPTION_TYPE_def]>>
  strip_tac>>
  xmatch
  >- (
    xlet_autop>>
    `toks_num = (MAP tokenize_num ∘ tokens blanks)` by
      metis_tac[toks_num_def,ETA_AX,o_DEF]>>
    simp[get_graph_def,parse_lad_def]>>
    TOP_CASE_TAC>>
    fs[OPTION_TYPE_def]
    >- (
      xmatch >>
      xlet_autop>>
      xcon>>xsimpl>>
      qmatch_asmsub_abbrev_tac`STRING_TYPE err _`>>
      qexists_tac`INL err`>>simp[SUM_TYPE_def])>>
    xmatch>>
    xlet_autop>>
    Cases_on`check_good_graph x`>>xif>>
    asm_exists_tac>>simp[]
    >- (
      xcon>>xsimpl>>
      qexists_tac`INR x`>>
      simp[SUM_TYPE_def])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    qmatch_asmsub_abbrev_tac`STRING_TYPE err _`>>
    qexists_tac`INL err`>>simp[SUM_TYPE_def])>>
  xlet_autop>>
  xcon>>xsimpl>>
  qmatch_asmsub_abbrev_tac`STRING_TYPE err _`>>
  qexists_tac`INL err`>>simp[SUM_TYPE_def]>>
  fs[get_graph_def]
QED

(* Translate the encoder *)
val _ = translate has_mapping_def;
val _ = translate all_has_mapping_def;

val _ = translate one_one_def;
val _ = translate all_one_one_def;

val _ = translate graph_basicTheory.neighbours_def;
val _ = translate edge_map_def;
val _ = translate all_edge_map_def;
val _ = translate encode_def;

(* Translate the string converter *)
val res = translate enc_string_def;

val _ = translate full_encode_def;

(* parse input from f1 f2 and run encoder *)
val parse_and_enc = (append_prog o process_topdecs) `
  fun parse_and_enc f1 f2 =
  case parse_lad f1 of
    Inl err => Inl err
  | Inr pattern =>
  (case parse_lad f2 of
    Inl err => Inl err
  | Inr target =>
    Inr (full_encode pattern target))`

Theorem parse_and_enc_spec:
  STRING_TYPE f1 f1v ∧
  STRING_TYPE f2 f2v ∧
  validArg f1 ∧
  validArg f2 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_and_enc"(get_ml_prog_state()))
    [f1v;f2v]
    (STDIO fs)
    (POSTv v.
    STDIO fs *
    & ∃res.
     SUM_TYPE STRING_TYPE
       (LIST_TYPE
       (PAIR_TYPE PBC_PBOP_TYPE
          (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE))) INT))) res v ∧
      case res of
        INL err =>
        get_graph fs f1 = NONE ∨ get_graph fs f2 = NONE
      | INR pbf =>
        ∃g1 g2.
        get_graph fs f1 = SOME g1 ∧
        get_graph fs f2 = SOME g2 ∧
        full_encode g1 g2 = pbf)
Proof
  rw[]>>
  xcf"parse_and_enc"(get_ml_prog_state())>>
  xlet_autop>>
  Cases_on`res`>>fs[SUM_TYPE_def]>>xmatch
  >- (
    xcon>>xsimpl>>
    qmatch_asmsub_abbrev_tac`STRING_TYPE err _`>>
    qexists_tac`INL err`>>simp[SUM_TYPE_def])>>
  xlet_autop>>
  Cases_on`res`>>fs[SUM_TYPE_def]>>xmatch
  >- (
    xcon>>xsimpl>>
    qmatch_asmsub_abbrev_tac`STRING_TYPE err _`>>
    qexists_tac`INL err`>>simp[SUM_TYPE_def])>>
  xlet_autop>>
  xcon>>
  xsimpl>>
  qexists_tac`INR (full_encode y y')`>>
  simp[SUM_TYPE_def]
QED

Definition success_string_def:
  success_string = strlit "Verified pattern graph NOT subgraph isomorphic to target graph\n"
End

val success_string_v_thm = translate success_string_def;

val check_unsat_3 = (append_prog o process_topdecs) `
  fun check_unsat_3 f1 f2 f3 =
  case parse_and_enc f1 f2 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr fml =>
    (case check_unsat_top success_string fml f3 of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr s => TextIO.print s)`

Theorem success_string_not_nil:
  strlit "" ≠ success_string
Proof
  EVAL_TAC
QED

Definition check_unsat_3_sem_def:
  check_unsat_3_sem fs f1 f2 out ⇔
  if out = success_string then
    ∃pattern target.
    get_graph fs f1 = SOME pattern ∧
    get_graph fs f2 = SOME target ∧
    ¬ has_subgraph_iso pattern target
  else out = strlit""
End

Theorem get_graph_good_graph:
  get_graph fs f = SOME g ⇒
  good_graph g
Proof
  rw[get_graph_def]>>
  every_case_tac>>
  fs[]>>
  metis_tac[check_good_graph,PAIR]
QED

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
      &(check_unsat_3_sem fs f1 f2 out))
Proof
  rw[check_unsat_3_sem_def]>>
  xcf "check_unsat_3" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  xlet_autop>>
  Cases_on`res`
  >- (
    fs[SUM_TYPE_def]>>
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`x`>>
    xsimpl>>rw[]>>
    fs[success_string_not_nil,STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  fs[SUM_TYPE_def]>>
  xmatch>>
  xlet`POSTv v.STDIO fs *
    SEP_EXISTS res.
    &(SUM_TYPE STRING_TYPE STRING_TYPE res v ∧
    ∀s. res = INR s ⇒ s = success_string ∧
      unsatisfiable (set (full_encode g1 g2)))`
  >- (
    xapp>>xsimpl>>
    rw[]>>fs[pbf_vars_full_encode,success_string_v_thm ]>>
    fs[FILENAME_def,validArg_def]>>
    metis_tac[])>>
  Cases_on`res`>>fs[SUM_TYPE_def]>>xmatch
  >- (
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`strlit ""`>>
    qexists_tac`x`>>
    xsimpl>>rw[]>>
    fs[success_string_not_nil,STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  xapp>>asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`success_string`>>simp[]>>
  qexists_tac`strlit ""`>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl>>
  metis_tac[get_graph_good_graph,full_encode_correct,pbcTheory.unsatisfiable_def]
QED

Definition print_pbf_def:
  print_pbf f = MAP pbc_string f
End

val res = translate pb_parseTheory.lit_string_def;
val res = translate pb_parseTheory.lhs_string_def;
val res = translate pb_parseTheory.op_string_def;
val res = translate pb_parseTheory.pbc_string_def;
val res = translate print_pbf_def;

val check_unsat_2 = (append_prog o process_topdecs) `
  fun check_unsat_2 f1 f2 =
    case parse_and_enc f1 f2 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr fml =>
    TextIO.print_list (print_pbf fml)`

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 f2 out ⇔
  case get_graph fs f1 of
    NONE => out = strlit ""
  | SOME pattern =>
  case get_graph fs f2 of
    NONE => out = strlit ""
  | SOME target =>
    out = concat (print_pbf (full_encode pattern target))
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
      &(check_unsat_2_sem fs f1 f2 out))
Proof
  rw[check_unsat_2_sem_def]>>
  xcf "check_unsat_2" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  xlet_autop>>
  Cases_on`res`
  >- (
    fs[SUM_TYPE_def]>>
    every_case_tac>>fs[]>>
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`x`>>
    xsimpl>>rw[]>>
    fs[success_string_not_nil,STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  fs[SUM_TYPE_def]>>
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
  usage_string = strlit "Usage: subgraph_iso_encode <LAD file (pattern)> <LAD file (target)> <optional: proof file>\n"
End

val r = translate usage_string_def;

val main = (append_prog o process_topdecs) `
  fun main u =
  case CommandLine.arguments () of
    [f1,f2] => check_unsat_2 f1 f2
  | [f1,f2,f3] => check_unsat_3 f1 f2 f3
  | _ => TextIO.output TextIO.stdErr usage_string`

Definition main_sem_def:
  main_sem fs cl out =
  if LENGTH cl = 3 then
    check_unsat_2_sem fs (EL 1 cl) (EL 2 cl) out
  else if LENGTH cl = 4 then
    check_unsat_3_sem fs (EL 1 cl) (EL 2 cl) out
  else out = strlit ""
End

Theorem STDIO_refl:
  (STDIO A ==>> STDIO A) ∧
  (STDIO A ==>>
  STDIO A * GC)
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
    fs[success_string_not_nil,STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    metis_tac[STDIO_refl])>>
  Cases_on`t'`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    rename1`COMMANDLINE cl`>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `usage_string` >>
    simp [theorem "usage_string_v_thm"] >>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    fs[success_string_not_nil,STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    metis_tac[STDIO_refl])>>
  Cases_on`t`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>fs[]>>
    rw[]>>
    fs[wfcl_def]>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
    rw[]>>
    metis_tac[STDIO_refl])>>
  Cases_on`t'`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>rw[]>>
    fs[wfcl_def]>>
    rename1`COMMANDLINE cl`>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    rw[]>>metis_tac[STDIO_refl])>>
  xmatch>>
  xapp_spec output_stderr_spec \\ xsimpl>>
  rename1`COMMANDLINE cl`>>
  qexists_tac`COMMANDLINE cl`>>xsimpl>>
  qexists_tac `usage_string` >>
  simp [theorem "usage_string_v_thm"] >>
  qexists_tac`fs`>>xsimpl>>
  rw[]>>
  fs[success_string_not_nil,STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
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
