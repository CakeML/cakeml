(*
  Basic shared graph encoder definitions
*)
Theory graphProg
Ancestors
  npbc_parseProg graph_basic
Libs
  preamble basis

val _ = translation_extends"npbc_parseProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

Overload "graph_TYPE" = ``PAIR_TYPE NUM (SPTREE_SPT_TYPE (SPTREE_SPT_TYPE UNIT_TYPE))``;

val res = translate is_edge_def;
val res = translate check_good_edges_def;
val res = translate check_good_graph_def;

val res = translate neighbours_sp_def;
val res = translate neighbours_def;
val res = translate COUNT_LIST_AUX_def;
val res = translate COUNT_LIST_compute;
val res = translate not_neighbours_def;

(* shared parsing LAD and DIMACS
  TODO: blanks already translated using the copy in pb_parse *)
val _ = translate graph_basicTheory.tokenize_num_def;

(* LAD parser *)
val _ = translate parse_lad_num_list_def;
val _ = translate list_to_num_set_def;
val _ = translate parse_lad_edges_def;
val _ = translate parse_lad_toks_def;

val tokenize_num_v_thm = theorem "tokenize_num_v_thm";

val b_inputAllTokensFrom_spec_specialize =
  b_inputAllTokensFrom_spec
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize_num`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_num_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE NUM`
  |> REWRITE_RULE [blanks_v_thm,tokenize_num_v_thm] ;

Definition noparse_string_def:
  noparse_string f s = concat[strlit"c Input file: ";f;strlit" unable to parse in format: "; s;strlit"\n"]
End

val r = translate noparse_string_def;

val parse_lad = (append_prog o process_topdecs) `
  fun parse_lad f =
  (case TextIO.b_inputAllTokensFrom #"\n" f blanks tokenize_num of
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

(* get_graph_lad *)
Definition get_graph_lad_def:
  get_graph_lad fs f =
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
      (case get_graph_lad fs f of
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
    simp[pb_parseTheory.blanks_def]>>
    fs[FILENAME_def,validArg_def,blanks_v_thm]>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    qexists_tac`emp`>>xsimpl)>>
  simp[get_graph_lad_def]>>
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

(* DIMACS parser *)
val _ = translate parse_dimacs_header_def;
val _ = translate insert_dir_edge_def;
val _ = translate insert_edge_def;
val _ = translate parse_dimacs_edge_def;
val _ = translate parse_dimacs_edges_def;
val _ = translate nocomment_line_def;
val _ = translate parse_dimacs_toks_def;

val parse_dimacs = (append_prog o process_topdecs) `
  fun parse_dimacs f =
  (case TextIO.b_inputAllTokensFrom #"\n" f blanks tokenize_num of
    None => Inl (notfound_string f)
  | Some lines =>
  (case parse_dimacs_toks lines of
    None => Inl (noparse_string f "DIMACS")
  | Some x =>
      Inr x
    ))`

(* get_graph_dimacs *)
Definition get_graph_dimacs_def:
  get_graph_dimacs fs f =
  if inFS_fname fs f then
    parse_dimacs (all_lines fs f)
  else NONE
End

Theorem parse_dimacs_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_dimacs"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. SUM_TYPE STRING_TYPE graph_TYPE
      (case get_graph_dimacs fs f of
        NONE => INL err
      | SOME res => INR res) v) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_dimacs"(get_ml_prog_state())>>
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
    simp[pb_parseTheory.blanks_def]>>
    fs[FILENAME_def,validArg_def,blanks_v_thm]>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    qexists_tac`emp`>>xsimpl)>>
  simp[get_graph_dimacs_def]>>
  reverse IF_CASES_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def]>>metis_tac[])>>
  xlet_autop>>
  `toks_num = (MAP tokenize_num ∘ tokens blanks)` by
    metis_tac[toks_num_def,ETA_AX,o_DEF]>>
  Cases_on`parse_dimacs (all_lines fs f)`>>
  gvs[parse_dimacs_def,OPTION_TYPE_def]
  >- (
    xmatch >>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def]>>metis_tac[])>>
  xmatch>>
  xcon>>xsimpl>>
  simp[SUM_TYPE_def]
QED

