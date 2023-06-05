(*
  Subgraph isomorphism encoder and checker
*)
open preamble basis pbc_normaliseTheory npbc_parseProgTheory subgraph_isoTheory graph_basicTheory;

val _ = new_theory "subgraph_isoProg";

val _ = translation_extends "npbc_parseProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

(* parsing
  TODO: duplicated code in mcisProg *)
val _ = translate graph_basicTheory.tokenize_num_def;

val _ = translate parse_num_list_def;
val _ = translate parse_edges_def;
val _ = translate parse_lad_toks_def;

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

val tokenize_num_v_thm = theorem "tokenize_num_v_thm";

val b_inputAllTokensFrom_spec_specialize =
  b_inputAllTokensFrom_spec
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize_num`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_num_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE NUM`
  |> REWRITE_RULE [blanks_v_thm,tokenize_num_v_thm] ;

val noparse_string_def = Define`
  noparse_string f s = concat[strlit"c Input file: ";f;strlit" unable to parse in format: "; s;strlit"\n"]`;

val r = translate noparse_string_def;

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
    else Inl ("c Input graph " ^ f ^ " fails undirectedness check\n")))`

Theorem blanks_eq[simp]:
  graph_basic$blanks = pb_parse$blanks
Proof
  rw[FUN_EQ_THM]>>
  simp[pb_parseTheory.blanks_def,blanks_def]
QED

Overload "graph_TYPE" = ``PAIR_TYPE NUM (SPTREE_SPT_TYPE (LIST_TYPE NUM))``;

(* get_graph *)
Definition get_graph_def:
  get_graph fs f =
  if inFS_fname fs f then
    case parse_lad (all_lines fs f) of
      NONE => NONE
    | SOME g =>
      if good_graph g then
        SOME g
      else NONE
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
    & (∃err. SUM_TYPE STRING_TYPE graph_TYPE
      (case get_graph fs f of
        NONE => INL err
      | SOME res => INR res) v) * STDIO fs)
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
    fs[FILENAME_def,validArg_def,blanks_v_thm]>>
    EVAL_TAC)>>
  simp[get_graph_def]>>
  reverse IF_CASES_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def]>>metis_tac[])>>
  xlet_autop>>
  `toks_num = (MAP tokenize_num ∘ tokens blanks)` by
    metis_tac[toks_num_def,ETA_AX,o_DEF]>>
  Cases_on`parse_lad (all_lines fs f)`>>
  gvs[parse_lad_def,OPTION_TYPE_def]
  >- (
    xmatch >>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def]>>metis_tac[])>>
  xmatch>>
  xlet_autop>>
  fs[check_good_graph_iff]>>
  xif
  >- (
    xcon>>xsimpl>>
    simp[SUM_TYPE_def])>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  simp[SUM_TYPE_def]>>
  metis_tac[]
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
  every_case_tac>>fs[SUM_TYPE_def]>>xmatch
  >- (
    xcon>>xsimpl>>
    qexists_tac`INL err`>>simp[SUM_TYPE_def])>>
  xlet_autop>>
  every_case_tac>>fs[SUM_TYPE_def]>>xmatch
  >- (
    xcon>>xsimpl>>
    qexists_tac`INL err`>>simp[SUM_TYPE_def])>>
  rpt xlet_autop>>
  xcon>>xsimpl >>
  rename1`_ (full_encode gpp gtt)`>>
  qexists_tac`INR (full_encode gpp gtt)`>>
  simp[SUM_TYPE_def,PAIR_TYPE_def]
QED

Definition UNSAT_string_def:
  UNSAT_string = strlit "s VERIFIED NOT SUBGRAPH ISOMORPHIC\n"
End

Definition SAT_string_def:
  SAT_string = strlit "s VERIFIED SUBGRAPH ISOMORPHIC\n"
End

Definition check_unsat_3_sem_def:
  check_unsat_3_sem fs f1 f2 out ⇔
  (out ≠ strlit"" ⇒
  ∃gp gt.
    get_graph fs f1 = SOME gp ∧
    get_graph fs f2 = SOME gt ∧
    (
    out = UNSAT_string ∧ ¬ has_subgraph_iso gp gt ∨
    out = SAT_string ∧ has_subgraph_iso gp gt
    ))
End

(* Turn result into string *)
Definition res_to_string_def:
  (res_to_string (INL s) = INL s) ∧
  (res_to_string (INR h) =
    case h of
      DUnsat => INR UNSAT_string
    | DSat => INR SAT_string
    | _ => INL (strlit "c Unexpected conclusion for subgraph isomorphism problem.\n"))
End

val res = translate (res_to_string_def |> SIMP_RULE std_ss [UNSAT_string_def,SAT_string_def]);

val check_unsat_3 = (append_prog o process_topdecs) `
  fun check_unsat_3 f1 f2 f3 =
  case parse_and_enc f1 f2 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr fml =>
    (case
        res_to_string (check_unsat_top_norm (None,fml) f3) of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr s => TextIO.print s)`

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
    xsimpl)
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
  rpt xlet_autop>>
  xlet`(POSTv v.
     STDIO fs *
     SEP_EXISTS res.
     &(
        SUM_TYPE STRING_TYPE PBC_CONCL_TYPE res v ∧
        case res of
          INR concl =>
            sem_concl (set y) NONE concl
        | INL l => T))`
  >- (
    xapp>>xsimpl>>
    fs[validArg_def]>>
    asm_exists_tac>>simp[]>>
    qexists_tac`emp`>>simp[]>>
    qexists_tac`(NONE,y)`>>
    simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
    qexists_tac`f3`>>fs[FILENAME_def]>>
    xsimpl>>
    metis_tac[])>>
  xlet_autop>>
  every_case_tac>>gvs[SUM_TYPE_def]
  >- (
    fs[res_to_string_def,SUM_TYPE_def]>>
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
  fs[res_to_string_def]>>
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
    qexists_tac`SAT_string`>>simp[]>>
    qexists_tac`strlit ""`>>
    simp[STD_streams_stderr,add_stdo_nil]>>
    xsimpl>>
    (drule_at Any) full_encode_sem_concl>>
    fs[]>>
    impl_tac >-
      (fs[get_graph_def]>>every_case_tac>>gvs[])>>
    simp[])
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>simp[]>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`UNSAT_string`>>simp[]>>
    qexists_tac`strlit ""`>>
    simp[STD_streams_stderr,add_stdo_nil]>>
    xsimpl>>
    (drule_at Any) full_encode_sem_concl>>
    fs[]>>
    impl_tac >-
      (fs[get_graph_def]>>every_case_tac>>gvs[])>>
    simp[])>>
  xapp_spec output_stderr_spec \\ xsimpl>>
  asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>xsimpl>>
  qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`strlit ""`>>
  rename1`add_stderr _ err`>>
  qexists_tac`err`>>xsimpl>>rw[]>>
  fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  xsimpl
QED

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 f2 out ⇔
  case get_graph fs f1 of
    NONE => out = strlit ""
  | SOME gpp =>
  case get_graph fs f2 of
    NONE => out = strlit ""
  | SOME gtt =>
    out = concat (print_pbf (NONE, full_encode gpp gtt))
End

val check_unsat_2 = (append_prog o process_topdecs) `
  fun check_unsat_2 f1 f2 =
  case parse_and_enc f1 f2 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr fml =>
    TextIO.print_list (print_pbf (None,fml))`

Theorem check_unsat_2_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  STRING_TYPE f2 f2v ∧ validArg f2 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_2"(get_ml_prog_state()))
    [f1v;f2v]
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
  Cases_on`res`>>fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    rw[]>>
    qexists_tac`x`>>xsimpl)
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
    every_case_tac>>xsimpl>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    rw[]>>
    qexists_tac`x`>>xsimpl)>>
  xmatch>>
  xlet_autop>>
  xlet_autop>>
  xlet`POSTv v. STDIO fs *
    &(LIST_TYPE STRING_TYPE (print_pbf (NONE,y)) v)`
  >- (
    xapp>>xsimpl>>
    qexists_tac`(NONE,y)`>>simp[PAIR_TYPE_def,OPTION_TYPE_def])>>
  xapp_spec print_list_spec>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`strlit ""`>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl
QED

Definition usage_string_def:
  usage_string = strlit "Usage: cake_pb_iso <LAD file (pattern)> <LAD file (target)> <optional: PB proof file>\n"
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
    xapp_spec output_stderr_spec \\ xsimpl>>
    rename1`COMMANDLINE cl`>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `usage_string` >>
    simp [theorem "usage_string_v_thm"] >>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    metis_tac[STDIO_refl])>>
  Cases_on`t`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>rw[]>>
    rpt(first_x_assum (irule_at Any)>>xsimpl)>>
    fs[wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>>
  Cases_on`t'`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>rw[]>>
    rpt(first_x_assum (irule_at Any)>>xsimpl)>>
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
