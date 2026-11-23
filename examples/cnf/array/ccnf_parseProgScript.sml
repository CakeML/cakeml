(*
  Adds file-level parsing and formula construction to ccnf_arrayProg
*)
Theory ccnf_parseProg
Ancestors
  cnf ccnf ccnf_list array_ofProof ccnf_arith ccnf_arrayProg mlint syntax_helper
  input_lex input_lexProg
Libs
  preamble basis

val _ = hide_environments true;

val _ = translation_extends"ccnf_arrayProg";

val res = translate mk_lit_def;

val res = translate parse_until_zero_nn_aux_def;
val res = translate parse_until_zero_nn_def;

val res = translate starts_with_def;

val res = translate var_lit_def;

(*** Printing back out in the DIMACS-style surface syntax ***)

val res = translate print_lit_def;
val res = translate print_lits_def;
val res = translate max_list_def;
val res = translate print_header_line_def;

Theorem STDIO_refl:
  STDIO A ==>>
  STDIO A * GC
Proof
  xsimpl
QED

(* Binary proof records are terminated by a zero byte *)
Definition nulc_def:
  nulc = CHR 0
End

val res = translate nulc_def;

(* The buffer size for reading proofs. TextIO's openInSetBufferSize and
  openStdInSetBufferSize allocate min 65535 (max (bsize + 4) 1028) bytes,
  so this is the largest buffer they give. *)
Definition proof_buffer_size_def:
  proof_buffer_size = 65531n
End

val res = translate proof_buffer_size_def;

Theorem EqualityType_CNF_LIT_TYPE:
  EqualityType (CNF_LIT_TYPE NUM)
Proof
  metis_tac(eq_lemmas())
QED

(*** Building the initial formula array ***)

Quote add_cakeml:
  fun fill_cfml_arr arr i ls =
    case ls of [] => arr
    | (v::vs) =>
      let val arr' = insert_clause_arr arr i v in
        fill_cfml_arr arr' (Unsafe.Arith.addWitness i 1 arr') vs
      end
End

Theorem fill_cfml_arr_spec:
  ∀ls lsv arrv arrls i iv.
  NUM i iv ∧
  LIST_TYPE vcclause_TYPE ls lsv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"fill_cfml_arr"(get_ml_prog_state()))
  [arrv; iv; lsv]
  (ARRAY_OF vcclause_TYPE arrv arrls)
  (POSTv resv.
    ARRAY_OF vcclause_TYPE resv
      (FOLDL (λacc (i,v). update_resize acc vcc_none v i)
        arrls (enumerate i ls)))
Proof
  Induct>>rw[]>>
  xcf "fill_cfml_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,miscTheory.enumerate_def]>>
  xmatch
  >- (xvar>>xsimpl)>>
  xlet`POSTv resv.
    ARRAY_OF vcclause_TYPE resv (insert_vcc_list arrls i h)`
  >- (xapp>>xsimpl)>>
  `i < LENGTH (insert_vcc_list arrls i h)` by
    rw[insert_vcc_list_def,update_resize_def]>>
  xlet_auto_spec (SOME (Q.ISPEC`vcclause_TYPE` num_add_arr_spec))
  >- xsimpl>>
  gvs[insert_vcc_list_def]>>
  xapp>>xsimpl
QED

Quote add_cakeml:
  fun build_cfml_arr n k ls =
    fill_cfml_arr (Array.array n vcc_none) k ls
End

Theorem build_cfml_arr_spec:
  NUM n nv ∧
  NUM k kv ∧
  LIST_TYPE vcclause_TYPE ls lsv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"build_cfml_arr"(get_ml_prog_state()))
  [nv; kv; lsv]
  emp
  (POSTv resv.
    ARRAY_OF vcclause_TYPE resv (build_cfml_list k ls n))
Proof
  rw[]>>
  xcf "build_cfml_arr" (get_ml_prog_state ())>>
  assume_tac vcc_none_v_thm>>
  xlet_auto_spec (SOME (Q.ISPEC`vcclause_TYPE` ARRAY_OF_alloc_spec))
  >- xsimpl>>
  xapp>>
  qexistsl_tac[`emp`,`ls`,`k`,`REPLICATE n vcc_none`]>>
  simp[build_cfml_list_def,build_fml_list_def]>>
  xsimpl
QED

(***
  The DIMACS front end shared by the checkers
 ***)

val _ = translate parse_vclause_def;

Overload "VCFML_TYPE" = ``LIST_TYPE vcclause_TYPE``

(* The DIMACS body is read one line at a time, tokenizing during input *)
Quote add_cakeml:
  fun parse_body_arr lno maxvar fd acc =
  case input_toks fd of
    None => Inr (List.rev acc)
  | Some l =>
    if keep_line l then
      (case parse_vclause maxvar l of
        None => Inl (format_dimacs_failure lno "failed to parse line")
      | Some cl =>
        parse_body_arr (lno+1) maxvar fd (cl::acc))
    else parse_body_arr (lno+1) maxvar fd acc
End

Theorem parse_body_arr_spec:
  !lines fd fdv fs maxvar maxvarv acc accv lno lnov.
  NUM lno lnov ∧
  NUM maxvar maxvarv ∧
  VCFML_TYPE acc accv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_body_arr" (get_ml_prog_state()))
    [lnov; maxvarv; fdv; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      &
      (∃err.
      SUM_TYPE STRING_TYPE VCFML_TYPE
        (case parse_body_gen parse_vclause maxvar
          (FILTER keep_line (MAP toks lines)) acc of
          NONE => INL err
        | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))
Proof
  Induct>>
  simp []>>
  rpt strip_tac>>
  xcf "parse_body_arr" (get_ml_prog_state ())
  >- (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    >- (
      xapp_spec input_toks_spec>>
      qexistsl_tac [`emp`,‘[]’,‘fs’]>>
      qexists_tac ‘fd’>>xsimpl>>fs [])>>
    gvs[OPTION_TYPE_def]>>
    xmatch>>
    simp[parse_body_gen_def]>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def]>>
    qexistsl_tac [‘k’,‘[]’]>>xsimpl)>>
  xlet ‘(POSTv v.
          SEP_EXISTS k.
              STDIO (forwardFD fs fd k) *
              INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
              & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks h)) v)’
  >- (
    xapp_spec input_toks_spec>>
    qexistsl_tac [`emp`,‘h::lines’,‘fs’]>>
    qexists_tac ‘fd’>>xsimpl>>fs []>>
    rw []>>qexists_tac ‘x’>>xsimpl)>>
  gvs[OPTION_TYPE_def]>>
  xmatch>>fs []>>
  xlet_autop>>
  reverse IF_CASES_TAC
  >- (
    xif >> asm_exists_tac>>xsimpl>>
    xlet_autop>>
    xapp>> xsimpl>>
    rpt(first_x_assum (irule_at Any))>>
    qexistsl_tac [`forwardFD fs fd k`,`fd`]>>xsimpl>>
    rw[]>>
    qexists_tac`k+x`>>
    simp[GSYM fsFFIPropsTheory.forwardFD_o]>>
    qexists_tac`x'`>>xsimpl>>
    metis_tac[])>>
  xif>> asm_exists_tac>>simp[]>>
  xlet_autop>>
  simp[parse_body_gen_def]>>
  Cases_on`parse_vclause maxvar (toks h)`>>
  fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>
    xsimpl>>
    qexists_tac`k`>> qexists_tac`lines`>>xsimpl>>
    simp[SUM_TYPE_def]>>
    metis_tac[])>>
  rename1`parse_vclause maxvar (toks h) = SOME cl`>>
  xmatch>>
  xlet_autop>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  rpt(first_x_assum (irule_at Any))>>
  qexistsl_tac [`forwardFD fs fd k`,`fd`]>>
  xsimpl>>
  simp[LIST_TYPE_def,forwardFD_o]>>rw[]>>
  qexists_tac`cl::acc`>>
  simp[LIST_TYPE_def]>>
  rw[]>>
  qexistsl_tac [`k+x`,`x'`]>>
  xsimpl>>
  metis_tac[]
QED

Quote add_cakeml:
  fun parse_vcnf_toks_arr lno fd =
  case input_toks fd of
    None => Inl (format_dimacs_failure lno "failed to find header")
  | Some l =>
    if keep_line l then
      (case parse_header_line l of
        None => Inl (format_dimacs_failure lno "failed to parse header")
      | Some res => case res of (vars,ncl) =>
        (case parse_body_arr lno vars fd [] of
          Inl fail => Inl fail
        | Inr acc =>
          if List.length acc = ncl then
            Inr (vars,(ncl,acc))
          else
            Inl (format_dimacs_failure lno "incorrect number of clauses")))
    else parse_vcnf_toks_arr (lno+1) fd
End

Theorem parse_vcnf_toks_arr_spec:
  !lines fd fdv fs lno lnov.
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_vcnf_toks_arr" (get_ml_prog_state()))
    [lnov; fdv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE
        (PAIR_TYPE NUM (PAIR_TYPE NUM VCFML_TYPE))
      (case parse_vcnf_toks (MAP toks lines) of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))
Proof
  Induct>>
  simp []>>
  rpt strip_tac>>
  xcf "parse_vcnf_toks_arr" (get_ml_prog_state ())
  >- (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    >- (
      xapp_spec input_toks_spec>>
      qexistsl_tac [`emp`,‘[]’,‘fs’]>>
      qexists_tac ‘fd’>>xsimpl>>fs [])>>
    gvs [OPTION_TYPE_def]>>
    xmatch>>fs []>>
    simp[parse_vcnf_toks_def,parse_dimacs_toks_gen_def]>>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def]>>
    qexistsl_tac [‘k’,‘[]’]>>xsimpl>>
    metis_tac[])>>
  xlet ‘(POSTv v.
          SEP_EXISTS k.
              STDIO (forwardFD fs fd k) *
              INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
              & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks h)) v)’
  >- (
    xapp_spec input_toks_spec>>
    qexistsl_tac [`emp`,‘h::lines’,‘fs’]>>
    qexists_tac ‘fd’>>xsimpl>>fs []>>
    rw []>>qexists_tac ‘x’>>xsimpl)>>
  gvs [OPTION_TYPE_def]>>
  xmatch>>fs []>>
  xlet_autop>>
  simp[parse_vcnf_toks_def,parse_dimacs_toks_gen_def]>>
  reverse IF_CASES_TAC
  >- (
    xif >> asm_exists_tac>>xsimpl>>
    xlet_autop>>
    xapp>> xsimpl>>
    asm_exists_tac>> simp[]>>
    qexists_tac`emp`>>xsimpl>>
    qexistsl_tac [`forwardFD fs fd k`,`fd`]>>xsimpl>>
    rw[]>>
    fs[parse_vcnf_toks_def,parse_dimacs_toks_gen_def]>>
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
  rename1`parse_header_line (toks h) = SOME hdr`>>
  PairCases_on`hdr`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xlet `(POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE VCFML_TYPE
      (case parse_body_gen parse_vclause hdr0
        (FILTER keep_line (MAP toks lines)) [] of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k))`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac [`emp`,`hdr0`,`lines`,`forwardFD fs fd k`,`fd`,`[]`,
      `lno`]>>
    xsimpl>>
    simp[LIST_TYPE_def]>>
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
  drule LENGTH_parse_body_gen>>
  strip_tac>>gvs[]>>
  rpt xlet_autop>>
  rw[]>>xif
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
  qexistsl_tac [`k`,`lines'`]>>
  simp[SUM_TYPE_def]>>
  xsimpl>>
  metis_tac[]
QED

(* parse_vcnf_toks_arr on the file named fname *)
Quote add_cakeml:
  fun parse_full fname =
  let
    val fd = TextIO.openIn fname
    val res = parse_vcnf_toks_arr 0 fd
    val close = TextIO.closeIn fd;
  in
    res
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)
End

Theorem parse_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_full"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. (SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM VCFML_TYPE))
    (if inFS_fname fs f then
    (case parse_vcnf_toks (MAP toks (all_lines_file fs f)) of
      NONE => INL err
    | SOME x => INR x)
    else INL err) v)) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_full"(get_ml_prog_state()) >>
  fs[validArg_def]>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def]>>xpull) >>
  reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def]>>xpull>>metis_tac[]) >>
  reverse (Cases_on `inFS_fname fs f`) >> simp[]
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs f) *
      STDIO fs`
    >-
      (xlet_auto_spec (SOME openIn_STDIO_spec)>>xsimpl)
    >>
      fs[BadFileName_exn_def]>>
      xcases>>rw[]>>
      xlet_auto>>xsimpl>>
      xcon>>xsimpl>>
      simp[SUM_TYPE_def]>>metis_tac[])>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval`>>xsimpl>>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec (SOME (openIn_spec_lines |> Q.GEN `c0` |> Q.SPEC `#"\n"`))>>xsimpl>>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES _ fdd fddv lines fss`>>
  xlet`(POSTv v.
      & (∃err. SUM_TYPE STRING_TYPE (PAIR_TYPE NUM (PAIR_TYPE NUM VCFML_TYPE))
      (case parse_vcnf_toks (MAP toks lines) of
        NONE => INL err
      | SOME x => INR x) v) *
      SEP_EXISTS k lines'.
         STDIO (forwardFD fss fdd k) * INSTREAM_LINES #"\n" fdd fddv lines' (forwardFD fss fdd k))`
  >- (
    xapp>>xsimpl>>
    qexistsl_tac [`emp`,`lines`,`fss`,`fdd`]>>xsimpl>>
    rw[]>>
    qexistsl_tac [`x`,`x'`]>>xsimpl>>
    metis_tac[])>>
  xlet `POSTv v. STDIO fs`
  >- (
    xapp_spec closeIn_spec_lines >>
    qexistsl_tac [`emp`,`lines'`,`forwardFD fss fdd k`,`fdd`,`#"\n"`]>>
    conj_tac >-
     (unabbrev_all_tac>>
      imp_res_tac fsFFIPropsTheory.nextFD_ltX>>fs []>>
      imp_res_tac fsFFIPropsTheory.STD_streams_nextFD>>fs []) >>
    xsimpl>>
    `validFileFD fdd (forwardFD fss fdd k).infds` by
      (unabbrev_all_tac>> simp[validFileFD_forwardFD]>>
       imp_res_tac fsFFIPropsTheory.nextFD_ltX>>fs []>>
       match_mp_tac validFileFD_nextFD>>fs []) >>
    xsimpl >> rw [] >>
    imp_res_tac (DECIDE ``n<m:num ==> n <= m``) >>
    imp_res_tac fsFFIPropsTheory.nextFD_leX>>fs [] >>
    drule fsFFIPropsTheory.openFileFS_ADELKEY_nextFD >>
    fs [Abbr`fss`]>>xsimpl)>>
  xvar>>
  xsimpl>>
  metis_tac[]
QED
