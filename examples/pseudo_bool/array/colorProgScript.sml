(*
  Color encode and checker
*)
Theory colorProg
Ancestors
  basis_ffi pbc_normalise graphProg color graph_basic
    npbc_parseProg pb_parse
Libs
  preamble basis

val _ = translation_extends"graphProg";

val res = translate enc_string_def;
val res = translate color_obj_def;
val res = translate FOLDN_def;
val res = translate annot_string_def;

val _ = use_sub_check true;

val res = translate gen_constraint_def;

val _ = use_sub_check false;

val res = translate full_encode_eq;

(* Translation for parsing an OPB file *)
val r = translate pb_parseTheory.nocomment_line_def;
val r = translate parse_op_def;
val r = translate parse_constraint_def;
val r = translate parse_annot_def;
val r = translate parse_annot_constraint_def;
val r = translate parse_constraints_def;

val r = translate parse_obj_def;
val r = translate parse_obj_maybe_def;
val r = translate parse_var_raw_def;
val r = translate parse_vars_raw_def;
val r = translate parse_pres_def;
val r = translate parse_pres_maybe_def;
val r = translate parse_obj_pres_maybe_def;
val r = translate parse_pbf_toks_def;

Quote add_cakeml:
  fun parse_pbf_full f =
  (case TextIO.inputAllTokensFile #"\n" f blanks tokenize of
    None => Inl (notfound_string f)
  | Some lines =>
  (case parse_pbf_toks lines of
    None => Inl (noparse_string f "OPB")
  | Some res => Inr res
  ))
End

val inputAllTokensFile_spec_specialize =
  inputAllTokensFile_spec
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> REWRITE_RULE [blanks_v_thm,tokenize_v_thm] ;

Definition get_annot_fml_def:
  get_annot_fml fs f =
  if inFS_fname fs f then
    parse_pbf (all_lines_file fs f)
  else NONE
End

Theorem parse_pbf_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_pbf_full"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. (SUM_TYPE STRING_TYPE annot_prob_TYPE)
    (case get_annot_fml fs f of
      NONE => INL err
    | SOME res => INR res) v) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_pbf_full"(get_ml_prog_state())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse (Cases_on`consistentFS fs`) >- (
    fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def]
    \\ xpull \\ metis_tac[]) >>
  xlet`(POSTv sv. &OPTION_TYPE (LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
            (if inFS_fname fs f then
               SOME(MAP (MAP tokenize o tokens blanks) (all_lines_file fs f))
             else NONE) sv * STDIO fs)`
  >- (
    xapp_spec inputAllTokensFile_spec_specialize >>
    xsimpl>>
    simp[pb_parseTheory.blanks_def]>>
    fs[FILENAME_def,validArg_def,blanks_v_thm]>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    qexists_tac`emp`>>xsimpl)>>
  simp[get_annot_fml_def]>>
  IF_CASES_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    xlet_autop>>
    `toks = (MAP tokenize ∘ tokens blanks)` by
      rw[FUN_EQ_THM,toks_def]>>
    rw[parse_pbf_def]>>
    qmatch_goalsub_abbrev_tac`option_CASE AAA`>>
    Cases_on`AAA`>>
    fs[OPTION_TYPE_def]
    >- (
      xmatch >>
      xlet_autop>>
      xcon>>xsimpl>>
      simp[SUM_TYPE_def]>>metis_tac[])>>
    xmatch>>
    xcon>>
    xsimpl>>
    simp[SUM_TYPE_def])>>
  xlet_autop>>
  xcon>>xsimpl>>
  simp[SUM_TYPE_def]>>metis_tac[]
QED

(* parse input from f and run encoder into pbc *)
Quote add_cakeml:
  fun parse_and_enc f =
  case parse_dimacs f of
    Inl err => Inl err
  | Inr g =>
    Inr (full_encode (fst g) g)
End

Theorem parse_and_enc_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_and_enc"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    STDIO fs *
    & ∃res.
       SUM_TYPE STRING_TYPE
         (PAIR_TYPE
            (OPTION_TYPE (PAIR_TYPE
              (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
            INT))
            (LIST_TYPE
              (PAIR_TYPE
              (OPTION_TYPE STRING_TYPE)
              (PAIR_TYPE PBC_PBOP_TYPE (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE))) INT))))
            ) res v ∧
       case res of
        INL err =>
          get_graph_dimacs fs f = NONE
      | INR objf =>
        ∃g.
          get_graph_dimacs fs f = SOME g ∧
          full_encode (FST g) g = objf)
Proof
  rw[]>>
  xcf"parse_and_enc"(get_ml_prog_state())>>
  xlet_autop>>
  every_case_tac>>fs[SUM_TYPE_def]>>xmatch
  >- (
    xcon>>xsimpl>>
    qexists_tac`INL err`>>simp[SUM_TYPE_def])>>
  rpt xlet_autop>>
  xcon>>xsimpl >>
  rename1`_ (full_encode _ g)`>>
  qexists_tac`INR (full_encode (FST g) g)`>>
  simp[SUM_TYPE_def,PAIR_TYPE_def]
QED

Definition mk_prob_def:
  mk_prob objf = (NONE,objf):mlstring list option #
    ((int # mlstring pbc$lit) list # int) option #
    (mlstring option # (pbop # (int # mlstring pbc$lit) list # int)) list
End

val res = translate mk_prob_def;

Definition check_unsat_1_sem_def:
  check_unsat_1_sem fs f1 out ⇔
  case get_graph_dimacs fs f1 of
    NONE => out = strlit ""
  | SOME g =>
    out = concat (print_annot_prob (mk_prob (full_encode (FST g) g)))
End

Quote add_cakeml:
  fun check_unsat_1 f1 =
  case parse_and_enc f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr objf =>
    TextIO.print_list (print_annot_prob (mk_prob objf))
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

val _ = translate parse_col_header_def;
val _ = translate strip_num_def;
val _ = translate parse_col_line_def;
val _ = translate parse_col_lines_def;
val _ = translate mk_col_def;
val _ = translate parse_col_toks_def;

Quote add_cakeml:
  fun parse_col f =
  (case TextIO.inputAllTokensFile #"\n" f blanks tokenize_num of
    None => Inl (notfound_string f)
  | Some lines =>
  (case parse_col_toks lines of
    None => Inl (noparse_string f "COLOR")
  | Some x =>
      Inr x
    ))
End

(* get_col *)
Definition get_col_def:
  get_col fs f =
  if inFS_fname fs f then
    parse_col (all_lines_file fs f)
  else NONE
End

val inputAllTokensFile_spec_specialize_num =
  inputAllTokensFile_spec
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize_num`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_num_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE NUM`
  |> REWRITE_RULE [blanks_v_thm,tokenize_num_v_thm] ;

Theorem parse_col_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_col"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (NUM --> NUM))
      (case get_col fs f of
        NONE => INL err
      | SOME res => INR res) v) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_col"(get_ml_prog_state())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse (Cases_on`consistentFS fs`) >- (
    fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def]
    \\ xpull \\ metis_tac[]) >>
  xlet`(POSTv sv. &OPTION_TYPE (LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE NUM)))
            (if inFS_fname fs f then
               SOME(MAP (MAP tokenize_num o tokens blanks) (all_lines_file fs f))
             else NONE) sv * STDIO fs)`
  >- (
    xapp_spec inputAllTokensFile_spec_specialize_num >>
    xsimpl>>
    simp[pb_parseTheory.blanks_def]>>
    fs[FILENAME_def,validArg_def,blanks_v_thm]>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    qexists_tac`emp`>>xsimpl)>>
  simp[get_col_def]>>
  reverse IF_CASES_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def]>>metis_tac[])>>
  xlet_autop>>
  `toks_num = (MAP tokenize_num ∘ tokens blanks)` by
    metis_tac[toks_num_def,ETA_AX,o_DEF]>>
  Cases_on`parse_col (all_lines_file fs f)`>>
  gvs[parse_col_def,OPTION_TYPE_def]
  >- (
    xmatch >>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def]>>metis_tac[])>>
  xmatch>>
  xcon>>xsimpl>>
  simp[SUM_TYPE_def]
QED

(* Pretty print conclusion *)
Definition color_eq_str_def:
  color_eq_str (n:num) =
  strlit "s VERIFIED CHROMATIC NUMBER = " ^
    toString n ^ strlit"\n"
End

Definition color_bound_str_def:
  color_bound_str (l:num) (u:num) =
  strlit "s VERIFIED CHROMATIC NUMBER BOUND "^
    toString l ^ strlit " <= NUM COL <= " ^
    toString u ^ strlit"\n"
End

Definition print_color_str_def:
  print_color_str lbg ubg =
  if lbg = ubg
  then color_eq_str ubg
  else color_bound_str lbg ubg
End

Definition color_sem_def:
  color_sem g lb k f ⇔
  is_k_color k f g ∧
  if lb = k then
    min_color_size g = k
  else
    (∀k f.
        is_k_color k f g ⇒ lb ≤ k)
End

Definition check_unsat_4_sem_def:
  check_unsat_4_sem fs fg fc out ⇔
  (out ≠ strlit"" ⇒
  ∃g lb k f.
    get_graph_dimacs fs fg = SOME g ∧
    good_graph g ∧
    get_col fs fc = SOME (k,f) ∧
    out = print_color_str lb k ∧
    color_sem g lb k f)
End

val _ = translate check_k_color_aux_def;
val _ = translate check_k_color_def;

val _ = translate MAX_LIST_def;
val _ = translate parse_cu_def;
val _ = translate guess_n_def;
val _ = translate mk_key_def;

Theorem mk_key_side[local]:
  mk_key_side x
Proof
  rw[fetch "-" "mk_key_side_def"]>>
  CCONTR_TAC>>fs[]
QED

val _ = mk_key_side |> update_precondition;

val _ = translate lazy_constraint_aux_def;
val _ = translate lazy_constraint_def;

val _ = translate lazy_encode_def;
val _ = translate lazy_color_obj_def;
val res = translate lazy_full_encode_def;

(* f1: graph, f2: opb, f3: proof, f4: coloring *)
Quote add_cakeml:
  fun parse_and_check f1 f2 f4 =
  case parse_dimacs f1 of
    Inl err => Inl err
  | Inr g =>
  case parse_col f4 of
    Inl err => Inl err
  | Inr (k,f) =>
  if check_k_color k f g
  then
    case parse_pbf_full f2 of
      Inl err => Inl err
    | Inr prob =>
      case lazy_full_encode g prob of
        None =>
        Inl "Input OPB not subset of encoding"
      | Some n => Inr (k, (n, prob))
  else
    Inl "Invalid coloring"
End

Definition parse_and_check_sem_def:
  parse_and_check_sem fs f1 f2 f4 res ⇔
  (∀k n prob.
    res = INR (k,n,prob) ⇒
    ∃g f.
      get_graph_dimacs fs f1 = SOME g ∧
      good_graph g ∧
      get_col fs f4 = SOME (k,f) ∧
      is_k_color k f g ∧
      lazy_full_encode g prob = SOME n)
End

Theorem parse_and_check_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  STRING_TYPE f2 f2v ∧ validArg f2 ∧
  STRING_TYPE f4 f4v ∧ validArg f4 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_and_check"(get_ml_prog_state()))
    [f1v; f2v; f4v]
    (STDIO fs)
    (POSTv v.
      STDIO fs *
      &(∃res.
        SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM annot_prob_TYPE)) res v ∧
        parse_and_check_sem fs f1 f2 f4 res))
Proof
  rw[parse_and_check_sem_def]>>
  xcf"parse_and_check"(get_ml_prog_state())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  xlet_autop>>
  Cases_on`get_graph_dimacs fs f1`>>
  fs[SUM_TYPE_def]>>
  xmatch
  >- (
    xcon>>xsimpl>>
    qexists_tac`INL err`>>
    simp[SUM_TYPE_def])>>
  xlet_autop>>
  Cases_on`get_col fs f4`>>
  fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl>>
    qexists_tac`INL err`>>
    simp[SUM_TYPE_def]
  )>>
  rename1`xx = (_,_)`>>
  Cases_on`xx`>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  reverse xif
  >- (
    xcon>>xsimpl>>
    qexists_tac`INL «Invalid coloring»`>>
    simp[SUM_TYPE_def])>>
  xlet_autop>>
  Cases_on`get_annot_fml fs f2`>>
  fs[SUM_TYPE_def]>>
  xmatch
  >- (
    xcon>>xsimpl>>
    qexists_tac`INL err`>>
    simp[SUM_TYPE_def])>>
  xlet_autop>>
  gvs[npbc_arrayProgTheory.OPTION_TYPE_SPLIT]>>
  xmatch
  >- (
    xcon>>xsimpl>>
    qexists_tac`INL «Input OPB not subset of encoding»`>>
    simp[SUM_TYPE_def])>>
  xlet_autop>>
  xlet_autop>>
  xcon>>
  xsimpl>>
  gvs[get_graph_dimacs_def,AllCaseEqs(),mk_prob_def,pb_parseTheory.strip_annot_prob_def]>>
  drule parse_dimacs_good_graph>>
  rw[]>>
  rename1`check_k_color k f g`>>
  rename1`lazy_full_encode _ prob = SOME n`>>
  qexists_tac`INR (k,n,prob)`>>
  simp[SUM_TYPE_def,PAIR_TYPE_def]>>
  metis_tac[check_k_color_is_k_color]
QED

Definition map_concl_to_string_def:
  (map_concl_to_string k n (INL s) = (INL s)) ∧
  (map_concl_to_string k n (INR (out,bnd,c)) =
    case conv_concl n c of
      SOME lb => INR (print_color_str lb k)
    | NONE => INL (strlit "c Unexpected conclusion type for min coloring problem.\n"))
End

val res = translate conv_concl_def;
val res = translate color_eq_str_def;
val res = translate color_bound_str_def;
val res = translate print_color_str_def;
val res = translate map_concl_to_string_def;

Quote add_cakeml:
  fun check_unsat_4 f1 f2 f3 f4 =
  case parse_and_check f1 f2 f4 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (k,(n,prob)) =>
    let
      val prob = strip_annot_prob prob
      val probt = default_prob in
      (case
        map_concl_to_string k n
          (check_unsat_top_norm False prob probt f3) of
        Inl err => TextIO.output TextIO.stdErr err
      | Inr s => TextIO.print s)
    end
End

Theorem check_unsat_4_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  STRING_TYPE f2 f2v ∧ validArg f2 ∧
  STRING_TYPE f3 f3v ∧ validArg f3 ∧
  STRING_TYPE f4 f4v ∧ validArg f4 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_4"(get_ml_prog_state()))
    [f1v; f2v; f3v; f4v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(check_unsat_4_sem fs f1 f4 out))
Proof
  rw[check_unsat_4_sem_def]>>
  xcf "check_unsat_4" (get_ml_prog_state ())>>
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
    qexists_tac`strlit""`>>xsimpl>>rw[]>>
    qexists_tac`x`>>xsimpl>>rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  `?k n prob. y = (k,n,prob)` by metis_tac[PAIR]>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  assume_tac npbc_parseProgTheory.default_prob_v_thm>>
  xlet`POSTv v.
    STDIO fs *
    &prob_TYPE default_prob v`
  >-
    (xvar>>xsimpl)>>
  xlet`POSTv v. STDIO fs * &BOOL F v`
  >-
    (xcon>>xsimpl)>>
  drule npbc_parseProgTheory.check_unsat_top_norm_spec>>
  qpat_x_assum`prob_TYPE (strip_annot_prob _) _`assume_tac>>
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
  gvs[AllCasePreds(),SUM_TYPE_def]
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
    qexists_tac`print_color_str x k`>>simp[]>>
    qexists_tac`strlit ""`>>
    rw[]>>simp[STD_streams_stderr,add_stdo_nil]>>
    xsimpl>>
    gvs[parse_and_check_sem_def,color_sem_def]>>
    rename1`print_color_str lb k`>>
    qexists_tac`lb`>>simp[]>>
    (drule_at Any) lazy_full_encode_sem_concl>>
    disch_then drule>>
    PairCases_on`prob`>>
    disch_then drule>>
    fs[strip_annot_prob_def]>>
    rw[]>>fs[]>>
    metis_tac[min_color_size_eq])
QED

Definition usage_string_def:
  usage_string = strlit "Usage: cake_pb_color <DIMACS graph file> <OPB file> <PB proof file> <coloring file>\n"
End

val r = translate usage_string_def;

Quote add_cakeml:
  fun main u =
  let
    val cl = CommandLine.arguments ()
    val l = List.length cl
  in
    if l = 1 then check_unsat_1 (el 0 cl)
    else if l = 4 then check_unsat_4 (el 0 cl) (el 1 cl) (el 2 cl) (el 3 cl)
    else TextIO.output TextIO.stdErr (mk_usage_string usage_string)
  end
End

Definition main_sem_def:
  main_sem fs cl out =
  if LENGTH cl = 2 then
    check_unsat_1_sem fs (EL 1 cl) out
  else if LENGTH cl = 5 then
    check_unsat_4_sem fs (EL 1 cl) (EL 4 cl) out
  else out = strlit ""
End

Theorem STDIO_refl:
  STDIO A ==>>
  STDIO A * GC
Proof
  xsimpl
QED

Theorem LENGTH_EQ_4:
  LENGTH ls = 4 ⇔
  ∃a b c d. ls = [a;b;c;d]
Proof
  Cases_on`ls`>>rw[]>>
  Cases_on`t`>>rw[]>>
  Cases_on`t'`>>rw[]>>
  Cases_on`t`>>rw[]>>
  rw[ADD1]
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
  fs[]>>xif
  >- (
    xlet_auto
    >- (
      xsimpl>>
      simp[npbc_arrayProgTheory.el_side_def]>>
      CCONTR_TAC>>gvs[])>>
    xapp>>xsimpl>>
    rpt(first_x_assum (irule_at Any)>>xsimpl)>>
    gvs[LENGTH_EQ_1,wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>>
  xlet_autop>>
  xif
  >- (
    rpt (xlet_auto
    >- (
      xsimpl>>
      simp[npbc_arrayProgTheory.el_side_def]>>
      rw[]>>gvs[ADD1]>>
      CCONTR_TAC>>gvs[quantHeuristicsTheory.CONS_EQ_REWRITE]))>>
    xapp>>xsimpl>>
    rpt(first_x_assum (irule_at Any)>>xsimpl)>>
    gvs[LENGTH_EQ_4,wfcl_def]>>
    rw[]>>metis_tac[STDIO_refl])>>
  simp[ADD1]>>
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
