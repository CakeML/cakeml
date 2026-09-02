(*
  This refines lrup_list to use arrays
*)
Theory lrup_arrayProg
Ancestors
  misc mllist UnsafeProof ccnf_arrayProg ccnf_parseProg cnf ccnf ccnf_list
  syntax_helper lrup lrup_list
  mlint mlvector
Libs
  preamble basis

val _ = hide_environments true;

val _ = translation_extends "ccnf_parseProg";

val _ = register_type``:lrup``;

Quote add_cakeml:
  fun check_lrup_arr lno lrup fml carr b =
  case lrup of
    Delvb s =>
      (delete_ids_vb_arr fml s 1 (String.size s); (fml, carr, b))
  | Lrupvb n c s =>
      (case is_rup_vb_arr lno fml carr b c s of (carr,b) =>
        (insert_clause_arr fml n c, carr, b))
End

val LRUP_LRUP_TYPE_def = fetch "-" "LRUP_LRUP_TYPE_def";

Theorem check_lrup_arr_spec:
  NUM lno lnov ∧
  LRUP_LRUP_TYPE lrup lrupv ∧
  LIST_REL vcclause_TYPE fmlls fmllsv ∧
  WORD8 b bv ∧
  bnd_fml fmlls (LENGTH Clist)
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lrup_arr" (get_ml_prog_state()))
    [lnov; lrupv; fmlv; Carrv; bv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λv.
        SEP_EXISTS v1 v2 v3.
          &(v = Conv NONE [v1; v2; v3]) *
          (SEP_EXISTS fmllsv' clist'.
            ARRAY v1 fmllsv' *
            W8ARRAY v2 clist' *
            &(
            case check_lrup_list lrup fmlls Clist b of
              NONE => F
            | SOME (fmlls', Clist', b') =>
                bnd_fml fmlls' (LENGTH Clist') ∧
                LIST_REL vcclause_TYPE fmlls' fmllsv' ∧
                WORD8 b' v3 ∧
                Clist' = clist'
            ))
      )
      (λe. ARRAY fmlv fmllsv *
        &(Fail_exn e ∧
        check_lrup_list lrup fmlls Clist b = NONE)))
Proof
  rw[check_lrup_list_def]>>
  xcf "check_lrup_arr" (get_ml_prog_state ())>>
  Cases_on`lrup`>>fs[LRUP_LRUP_TYPE_def]
  >- (
    (* Delvb *)
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    metis_tac[bnd_fml_delete_ids_vb_list])>>
  (* Lrupvb *)
  xmatch>>
  xlet `
    POSTve
      (λres.
           (SEP_EXISTS b' Carrv' Clist'.
              W8ARRAY Carrv' Clist' *
              &(PAIR_TYPE $= WORD8 (Carrv',b') res ∧
               is_rup_vb_list fmlls Clist b v m = (T,Clist',b'))) *
           ARRAY fmlv fmllsv)
      (λe.
          ARRAY fmlv fmllsv *
          &(Fail_exn e ∧ ¬FST (is_rup_vb_list fmlls Clist b v m)))`
  >- (
    xapp>>xsimpl>>
    rpt(first_x_assum (irule_at Any))>>
    simp[PAIR_TYPE_def]>>rw[]>>
    xsimpl)
  >- (
    xsimpl>>rw[]>>
    every_case_tac>>gvs[])>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet`POSTv resv.
    W8ARRAY Carrv' Clist' *
    SEP_EXISTS fmllsv'. ARRAY resv fmllsv' *
    &LIST_REL vcclause_TYPE (insert_vcc_list fmlls n v) fmllsv'`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac [`v`,`n`,`fmlls`]>>
    simp[])>>
  xcon>>xsimpl>>
  irule bnd_fml_insert_vcc_list>>
  metis_tac[bnd_fml_is_rup_vb_list]
QED

(*** Reading and checking a proof file, one record at a time ***)

Theorem SEP_IMP_REFL_gc[local]:
  p ==>> p * GC
Proof
  xsimpl
QED

(* Closes a separation-logic entailment whose two sides differ only by
  frame association and GC slack *)
val sep_triv = metis_tac[SEP_IMP_REFL_gc,SEP_IMP_REFL,STAR_ASSOC,STAR_COMM];

(* Records are terminated by a zero byte *)
Definition nulc_def:
  nulc = CHR 0
End

val nulc_v_thm = translate nulc_def;

val res = translate vb_ilit_def;
val res = translate parse_vb_ilits_def;

Theorem parse_vb_ilits_side[local]:
  ∀s i len acc.
  len ≤ strlen s ⇒ parse_vb_ilits_side s i len acc
Proof
  ho_match_mp_tac parse_vb_ilits_ind>>
  rw[]>>
  simp[Once (fetch "-" "parse_vb_ilits_side_def")]>>
  simp[fetch "ccnf_arrayProg" "parse_vb_num_side_def",parse_vb_num_aux_side]
QED

val _ = parse_vb_ilits_side |> update_precondition;

val res = translate parse_lrup_chunk_def;

Theorem parse_lrup_chunk_side[local]:
  ∀s. parse_lrup_chunk_side s
Proof
  rw[fetch "-" "parse_lrup_chunk_side_def"]>>
  simp[parse_vb_ilits_side,fetch "ccnf_arrayProg" "parse_vb_num_side_def",
    parse_vb_num_aux_side]
QED

val _ = parse_lrup_chunk_side |> update_precondition;

Quote add_cakeml:
  fun parse_lrup_one_arr lno fd =
  case TextIO.inputLineWith nulc fd of
    None => None
  | Some l =>
    (case parse_lrup_chunk l of
      None =>
        raise Fail (format_failure lno "failed to parse compressed LRUP record")
    | Some (Inl step) => Some step
    | Some (Inr idc) =>
      case idc of (id,c) =>
        (case TextIO.inputLineWith nulc fd of
          None =>
            raise Fail (format_failure lno "missing RUP hints")
        | Some h => Some (Lrupvb id c h)))
End

Theorem parse_lrup_one_arr_spec:
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_lrup_one_arr" (get_ml_prog_state()))
    [lnov; fdv]
    (STDIO fs * INSTREAM_LINES nulc fd fdv lines fs)
    (POSTve
      (λv.
        SEP_EXISTS k lines'.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES nulc fd fdv lines' (forwardFD fs fd k) *
          &(parse_lrup_one lines ≠ NONE ∧
            OPTION_TYPE LRUP_LRUP_TYPE
              (OPTION_MAP FST (THE (parse_lrup_one lines))) v ∧
            (case THE (parse_lrup_one lines) of
              NONE => lines' = []
            | SOME res => lines' = SND res)))
      (λe.
        SEP_EXISTS k lines'.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES nulc fd fdv lines' (forwardFD fs fd k) *
          &(Fail_exn e ∧ parse_lrup_one lines = NONE)))
Proof
  rw[]>>
  xcf "parse_lrup_one_arr" (get_ml_prog_state ())>>
  xlet `POSTv v.
    SEP_EXISTS k.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES nulc fd fdv (TL lines) (forwardFD fs fd k) *
      &OPTION_TYPE STRING_TYPE (oHD lines) v`
  >- (
    xapp>>
    simp[nulc_v_thm])>>
  simp[parse_lrup_one_def]>>
  Cases_on`lines`>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    xcon>>xsimpl>>
    sep_triv)>>
  xlet_autop>>
  Cases_on`parse_lrup_chunk h`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    gvs[Fail_exn_def]>>
    first_x_assum (irule_at Any)>>
    sep_triv)>>
  rename1`parse_lrup_chunk h = SOME res`>>
  Cases_on`res`>>fs[SUM_TYPE_def]>>xmatch
  >- (
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def]>>
    sep_triv)>>
  rename1`INSTREAM_LINES nulc fd fdv lines`>>
  rename1`parse_lrup_chunk h = SOME (INR idc)`>>
  Cases_on`idc`>>gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet `POSTv v.
    SEP_EXISTS k.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES nulc fd fdv (TL lines) (forwardFD fs fd k) *
      &OPTION_TYPE STRING_TYPE (oHD lines) v`
  >- (
    xapp>>
    irule_at Any nulc_v_thm>>xsimpl>>
    qexistsl_tac [`lines`,`forwardFD fs fd k`,`fd`]>>
    xsimpl>>
    simp[forwardFD_o]>>
    sep_triv)>>
  Cases_on`lines`>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    gvs[Fail_exn_def]>>
    first_x_assum (irule_at Any)>>
    sep_triv)>>
  xlet_autop>>
  xcon>>xsimpl>>
  simp[OPTION_TYPE_def,LRUP_LRUP_TYPE_def]>>
  qexists_tac`k`>>
  xsimpl
QED


Definition parse_and_run_file_list_def:
  parse_and_run_file_list lines fml Clist b =
  case parse_lrup_one lines of
    NONE => NONE
  | SOME NONE => SOME fml
  | SOME (SOME (step,rest)) =>
    (case check_lrup_list step fml Clist b of
      NONE => NONE
    | SOME (fml', Clist', b') =>
      parse_and_run_file_list rest fml' Clist' b')
Termination
  WF_REL_TAC` measure (LENGTH o FST)`>>
  rw[]>>
  drule parse_lrup_one_LENGTH>>
  simp[]
End

Theorem parse_and_run_file_list_eq:
  ∀lines fml Clist b.
  parse_and_run_file_list lines fml Clist b =
  case parse_lrups lines of
    NONE => NONE
  | SOME lrups => check_lrups_list lrups fml Clist b
Proof
  ho_match_mp_tac parse_and_run_file_list_ind>>
  rw[]>>
  simp[Once parse_and_run_file_list_def,Once parse_lrups_def]>>
  every_case_tac>>
  gvs[check_lrups_list_def]
QED

Quote add_cakeml:
  fun check_unsat'' fd lno fml carr b =
  case parse_lrup_one_arr lno fd of
    None => fml
  | Some step =>
    (case check_lrup_arr lno step fml carr b of
      (fml',carr',b') => check_unsat'' fd (lno+1) fml' carr' b')
End

Theorem check_unsat''_spec:
  ∀lines fmlls Clist b fs fmlv fmllsv Carrv lno lnov bv.
  NUM lno lnov ∧
  LIST_REL vcclause_TYPE fmlls fmllsv ∧
  WORD8 b bv ∧
  bnd_fml fmlls (LENGTH Clist)
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat''" (get_ml_prog_state()))
    [fdv; lnov; fmlv; Carrv; bv]
    (STDIO fs * ARRAY fmlv fmllsv *
      W8ARRAY Carrv Clist * INSTREAM_LINES nulc fd fdv lines fs)
    (POSTve
      (λv.
        SEP_EXISTS k fmllsv'.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES nulc fd fdv [] (forwardFD fs fd k) *
          ARRAY v fmllsv' *
          &(unwrap_TYPE
            (LIST_REL vcclause_TYPE)
            (parse_and_run_file_list lines fmlls Clist b) fmllsv'))
      (λe.
        SEP_EXISTS k fmlv' fmllsv' lines'.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES nulc fd fdv lines' (forwardFD fs fd k) *
          ARRAY fmlv' fmllsv' *
          &(Fail_exn e ∧
            parse_and_run_file_list lines fmlls Clist b = NONE)))
Proof
  ho_match_mp_tac parse_and_run_file_list_ind>>
  rpt strip_tac>>
  xcf "check_unsat''" (get_ml_prog_state ())>>
  simp[Once parse_and_run_file_list_def]>>
  xlet `
    POSTve
      (λv.
        SEP_EXISTS k lines'.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES nulc fd fdv lines' (forwardFD fs fd k) *
          ARRAY fmlv fmllsv * W8ARRAY Carrv Clist *
          &(parse_lrup_one lines ≠ NONE ∧
            OPTION_TYPE LRUP_LRUP_TYPE
              (OPTION_MAP FST (THE (parse_lrup_one lines))) v ∧
            (case THE (parse_lrup_one lines) of
              NONE => lines' = []
            | SOME res => lines' = SND res)))
      (λe.
        SEP_EXISTS k lines'.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES nulc fd fdv lines' (forwardFD fs fd k) *
          ARRAY fmlv fmllsv *
          &(Fail_exn e ∧ parse_lrup_one lines = NONE))`
  >- (
    xapp>>
    qexistsl_tac [`ARRAY fmlv fmllsv * W8ARRAY Carrv Clist`,`lines`,`fs`,
      `fd`]>>
    xsimpl>>
    qexists_tac`lno`>>simp[]>>
    rw[]>>
    qexistsl_tac [`x`,`x'`]>>
    xsimpl)
  >- (
    xsimpl>>rw[]>>
    qexistsl_tac [`x`,`fmlv`,`fmllsv`,`x'`]>>
    xsimpl>>
    simp[Once parse_and_run_file_list_def])>>
  Cases_on`parse_lrup_one lines`>>gvs[]>>
  rename1`parse_lrup_one lines = SOME res`>>
  Cases_on`res`>>gvs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xvar>>xsimpl>>
    simp[unwrap_TYPE_def]>>
    qexists_tac`k`>>xsimpl)>>
  rename1`parse_lrup_one lines = SOME (SOME stp)`>>
  Cases_on`stp`>>gvs[]>>
  rename1`parse_lrup_one lines = SOME (SOME (step,rest))`>>
  xmatch>>
  xlet_auto
  >- (
    xsimpl>>rw[]>>
    sep_triv)
  >- (
    xsimpl>>rw[]>>
    qexistsl_tac [`k`,`fmlv`,`fmllsv`,`rest`]>>
    xsimpl>>
    simp[Once parse_and_run_file_list_def])>>
  Cases_on`check_lrup_list step fmlls Clist b`>>gvs[]>>
  rename1`check_lrup_list step fmlls Clist b = SOME res`>>
  PairCases_on`res`>>gvs[]>>
  xmatch>>
  xlet_autop>>
  xapp>>xsimpl>>
  rpt(first_x_assum (irule_at Any))>>
  qexistsl_tac [`forwardFD fs fd k`,`emp`]>>
  xsimpl>>rw[]
  >- (
    simp[forwardFD_o]>>
    sep_triv)>>
  simp[forwardFD_o]>>
  simp[Once parse_and_run_file_list_def]>>
  xsimpl>>
  sep_triv
QED

(*** The file-level entry point.

  It takes the converted formula, so that its guarantee can be stated
  on the formula the DIMACS file denotes rather than on the checker's
  arrays.
 ***)

Quote add_cakeml:
  fun check_unsat' vcfml fname n nc =
  let
    val fd = TextIO.openIn fname
    val fml = build_cfml_arr nc 1 vcfml
    val carr = Word8Array.array n bw0
    val chk = Inr (check_unsat'' fd 1 fml carr bw1)
      handle Fail s => Inl s
    val close = TextIO.closeIn fd;
  in
    case chk of
      Inl s => Inl s
    | Inr fml' => Inr (contains_emp_arr fml')
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)
End

Theorem fastForwardFD_ADELKEY_same[simp]:
  forwardFD fs fd n with infds updated_by ADELKEY fd =
  fs with infds updated_by ADELKEY fd
Proof
  fs [forwardFD_def, IO_fs_component_equality]
QED

val bw0_v_thm = fetch "ccnf_arrayProg" "bw0_v_thm";
val bw1_v_thm = fetch "ccnf_arrayProg" "bw1_v_thm";

Theorem check_unsat'_spec:
  NUM n nv ∧
  NUM nc ncv ∧
  LIST_TYPE vcclause_TYPE (conv_cfml cfml) vcfmlv ∧
  FILENAME f fv ∧
  hasFreeFD fs ∧
  EVERY (EVERY nz_lit) cfml ∧
  EVERY (EVERY (λl. var_lit l < n)) cfml
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat'"(get_ml_prog_state()))
  [vcfmlv; fv; nv; ncv]
  (STDIO fs)
  (POSTv v.
    STDIO fs *
    SEP_EXISTS res.
      &(SUM_TYPE STRING_TYPE BOOL res v ∧
        (res = INR T ⇒ unsatisfiable_cnf (set cfml))))
Proof
  rw[]>>
  xcf"check_unsat'"(get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def]>>xpull)>>
  reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def]>>xpull>>metis_tac[])>>
  reverse (Cases_on `inFS_fname fs f`)>>simp[]
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs f) *
      STDIO fs`
    >- (xlet_auto_spec (SOME openIn_STDIO_spec)>>xsimpl)>>
    fs[BadFileName_exn_def]>>
    xcases>>rw[]>>
    xlet_auto>>xsimpl>>
    xcon>>xsimpl>>
    qexists_tac`INL (notfound_string f)`>>
    simp[SUM_TYPE_def])>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval`>>xsimpl>>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec
    (SOME (openIn_spec_lines |> Q.GEN `c0` |> Q.SPEC `nulc`))>>xsimpl>>
  assume_tac bw0_v_thm>>
  assume_tac bw1_v_thm>>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  xlet_autop>>
  xlet_autop>>
  qabbrev_tac`fmlls = build_cfml_list 1 (conv_cfml cfml) nc`>>
  qabbrev_tac`Clist = REPLICATE n (0w:word8)`>>
  `bnd_fml fmlls (LENGTH Clist)` by (
    simp[Abbr`fmlls`,Abbr`Clist`]>>
    irule bnd_fml_build_cfml_list>>
    irule bnd_clause_conv_cfml>>
    fs[])>>
  qabbrev_tac`lines = all_lines_file_gen nulc fs f`>>
  xlet`POSTv resv.
    SEP_EXISTS v0 fmllsv' fmlv' k rest.
      STDIO (forwardFD fss (nextFD fs) k) *
      INSTREAM_LINES nulc (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
      ARRAY fmlv' fmllsv' *
      &(
      case parse_and_run_file_list lines fmlls Clist 1w of
        NONE => resv = Conv (SOME (TypeStamp «Inl» 4)) [v0] ∧ ∃s. STRING_TYPE s v0
      | SOME fmlls'' =>
        resv = Conv (SOME (TypeStamp «Inr» 4)) [fmlv'] ∧
        LIST_REL vcclause_TYPE fmlls'' fmllsv'
      )`
  >- (
    simp[]>>
    TOP_CASE_TAC
    >- (
      xhandle`POSTe e.
        SEP_EXISTS fmlv' fmllsv' rest k.
          STDIO (forwardFD fss (nextFD fs) k) *
          INSTREAM_LINES nulc (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
          ARRAY fmlv' fmllsv' *
          &(Fail_exn e ∧
            parse_and_run_file_list lines fmlls Clist 1w = NONE)`
      >- (
        xlet`POSTe e.
          SEP_EXISTS k fmlv' fmllsv' lines'.
            STDIO (forwardFD fss (nextFD fs) k) *
            INSTREAM_LINES nulc (nextFD fs) is lines'
              (forwardFD fss (nextFD fs) k) *
            ARRAY fmlv' fmllsv' *
            &(Fail_exn e ∧
              parse_and_run_file_list lines fmlls Clist 1w = NONE)`
        >- (
          xapp_spec check_unsat''_spec>>
          xsimpl>>
          rpt(first_x_assum (irule_at Any))>>
          xsimpl>>
          qexistsl_tac [`lines`,`fss`,`nextFD fs`,`emp`]>>
          xsimpl>>
          simp[Abbr`Clist`]>>
          fs[unwrap_TYPE_def]>>
          rw[]>>
          sep_triv)>>
        xsimpl>>rw[]>>
        sep_triv)>>
      fs[Fail_exn_def]>>
      xcases>>
      xcon>>xsimpl>>
      simp[PULL_EXISTS]>>
      asm_exists_tac>>simp[]>>
      sep_triv)>>
    xhandle`POSTv v.
      SEP_EXISTS k rest fmllsv'.
        STDIO (forwardFD fss (nextFD fs) k) *
        INSTREAM_LINES nulc (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
        (SEP_EXISTS fmlv'.
          &(v = Conv (SOME (TypeStamp «Inr» 4)) [fmlv']) *
          ARRAY fmlv' fmllsv') *
        &(unwrap_TYPE
          (LIST_REL vcclause_TYPE)
          (parse_and_run_file_list lines fmlls Clist 1w) fmllsv')`
    >- (
      xlet`POSTv v.
        SEP_EXISTS k fmllsv'.
          STDIO (forwardFD fss (nextFD fs) k) *
          INSTREAM_LINES nulc (nextFD fs) is [] (forwardFD fss (nextFD fs) k) *
          ARRAY v fmllsv' *
          &(unwrap_TYPE
            (LIST_REL vcclause_TYPE)
            (parse_and_run_file_list lines fmlls Clist 1w) fmllsv')`
      >- (
        xapp_spec check_unsat''_spec>>
        xsimpl>>
        rpt(first_x_assum (irule_at Any))>>
        xsimpl>>
        qexistsl_tac [`lines`,`fss`,`nextFD fs`,`emp`]>>
        xsimpl>>
        simp[Abbr`Clist`]>>
        fs[unwrap_TYPE_def]>>
        rw[]>>
        sep_triv)>>
      xcon>>xsimpl>>
      sep_triv)>>
    xsimpl>>
    simp[unwrap_TYPE_def]>>
    rw[]>>
    sep_triv)>>
  qspecl_then [`lines`,`fmlls`,`Clist`,`1w`]
    strip_assume_tac parse_and_run_file_list_eq>>
  gs[]>>
  pop_assum kall_tac>>
  xlet `POSTv v. STDIO fs * ARRAY fmlv' fmllsv'`
  >- (
    xapp_spec closeIn_spec_lines>>
    rename [`ARRAY a1 a2`]>>
    qexistsl_tac [`ARRAY a1 a2`,`rest`,`forwardFD fss (nextFD fs) k`,
      `nextFD fs`,`nulc`]>>
    conj_tac >- (
      fs [forwardFD_def,Abbr`fss`]>>
      imp_res_tac fsFFIPropsTheory.nextFD_ltX>>fs []>>
      imp_res_tac fsFFIPropsTheory.STD_streams_nextFD>>fs [])>>
    `validFileFD (nextFD fs) (forwardFD fss (nextFD fs) k).infds` by (
      simp[validFileFD_forwardFD]>>simp[Abbr`fss`]>>
      imp_res_tac fsFFIPropsTheory.nextFD_ltX>>fs []>>
      match_mp_tac validFileFD_nextFD>>fs [])>>
    xsimpl>>rw []>>
    imp_res_tac (DECIDE ``n<m:num ==> n <= m``)>>
    imp_res_tac fsFFIPropsTheory.nextFD_leX>>fs []>>
    drule fsFFIPropsTheory.openFileFS_ADELKEY_nextFD>>
    fs [Abbr`fss`]>>xsimpl)>>
  Cases_on`parse_lrups lines`>>fs[]
  >- (
    xmatch>>
    xcon>>xsimpl>>
    qexists_tac`INL s`>>
    simp[SUM_TYPE_def])>>
  Cases_on`check_lrups_list x fmlls Clist 1w`>>fs[]
  >- (
    xmatch>>
    xcon>>xsimpl>>
    qexists_tac`INL s`>>
    simp[SUM_TYPE_def])>>
  xmatch>>
  xlet_autop>>
  xcon>>xsimpl>>
  qexists_tac`INR (contains_emp_list x')`>>
  simp[SUM_TYPE_def]>>
  rw[]>>
  irule check_lrups_unsat_list_sound>>
  simp[check_lrups_unsat_list_def]>>
  qexistsl_tac [`1`,`x`,`n`,`nc`]>>
  gvs[Abbr`fmlls`,Abbr`Clist`]
QED














