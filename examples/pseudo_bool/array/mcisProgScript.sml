(*
  MCIS (unconnected) encode and checker
*)
Theory mcisProg
Ancestors
  basis_ffi pbc_normalise graphProg mcis graph_basic
Libs
  preamble basis

val _ = translation_extends"graphProg";

(* The encoder *)
val res = translate enc_string_def;

val res = translate pbcTheory.map_obj_def;
val res = translate unmapped_obj_def;

val res = translate FOLDN_def;

val res = translate full_encode_mcis_eq;

(* parse input from f1 f2 and run encoder into pbc *)
val parse_and_enc = (append_prog o process_topdecs) `
  fun parse_and_enc f1 f2 =
  case parse_lad f1 of
    Inl err => Inl err
  | Inr gp =>
  (case parse_lad f2 of
    Inl err => Inl err
  | Inr gt =>
    Inr (fst gp, full_encode_mcis gp gt))`

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
         (PAIR_TYPE NUM (PAIR_TYPE
            (OPTION_TYPE (PAIR_TYPE
              (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
            INT))
            (LIST_TYPE (PAIR_TYPE PBC_PBOP_TYPE (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE))) INT)))
            )) res v ∧
       case res of
        INL err =>
          get_graph_lad fs f1 = NONE ∨
          get_graph_lad fs f2 = NONE
      | INR (n,objf) =>
        ∃gp gt.
        get_graph_lad fs f1 = SOME gp ∧
        get_graph_lad fs f2 = SOME gt ∧
        full_encode_mcis gp gt = objf ∧
        FST gp = n)
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
  rename1`_ (full_encode_mcis gpp gtt)`>>
  qexists_tac`INR (FST gpp,full_encode_mcis gpp gtt)`>>
  simp[SUM_TYPE_def,PAIR_TYPE_def]
QED

(* Pretty print conclusion *)
Definition mcis_eq_str_def:
  mcis_eq_str (n:num) =
  strlit "s VERIFIED MAX CIS SIZE |CIS| = " ^
    toString n ^ strlit"\n"
End

Definition mcis_bound_str_def:
  mcis_bound_str (l:num) (u:num) =
  strlit "s VERIFIED MAX CIS SIZE BOUND "^
    toString l ^ strlit " <= |CIS| <= " ^
    toString u ^ strlit"\n"
End

Definition print_mcis_str_def:
  print_mcis_str (lbg:num,ubg:num) =
  if lbg = ubg
  then mcis_eq_str ubg
  else mcis_bound_str lbg ubg
End

Definition mcis_sem_def:
  mcis_sem gp gt (lbg,ubg) ⇔
  if lbg = ubg then
    max_cis_size gp gt = ubg
  else
    (∀vs. is_cis vs gp gt ⇒ CARD vs ≤ ubg) ∧
    (∃vs. is_cis vs gp gt ∧ lbg ≤ CARD vs)
End

Definition check_unsat_3_sem_def:
  check_unsat_3_sem fs f1 f2 out ⇔
  (out ≠ strlit"" ⇒
  ∃gp gt bounds.
    get_graph_lad fs f1 = SOME gp ∧
    get_graph_lad fs f2 = SOME gt ∧
    out = print_mcis_str bounds ∧
    mcis_sem gp gt bounds)
End

Definition map_concl_to_string_def:
  (map_concl_to_string n (INL s) = (INL s)) ∧
  (map_concl_to_string n (INR (out,bnd,c)) =
    case conv_concl n c of
      SOME bounds => INR (print_mcis_str bounds)
    | NONE => INL (strlit "c Unexpected conclusion for MCIS problem.\n"))
End

val res = translate (conv_concl_def |> REWRITE_RULE [GSYM sub_check_def]) ;

val conv_concl_side = Q.prove(
  `∀x y. conv_concl_side x y <=> T`,
  EVAL_TAC>>
  rw[]>>
  intLib.ARITH_TAC) |> update_precondition;

val res = translate mcis_eq_str_def;
val res = translate mcis_bound_str_def;
val res = translate print_mcis_str_def;
val res = translate map_concl_to_string_def;

Definition mk_prob_def:
  mk_prob objf = (NONE,objf):mlstring list option #
    ((int # mlstring pbc$lit) list # int) option #
    (pbop # (int # mlstring pbc$lit) list # int) list
End

val res = translate mk_prob_def;

val check_unsat_3 = (append_prog o process_topdecs) `
  fun check_unsat_3 f1 f2 f3 =
  case parse_and_enc f1 f2 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (n,objf) =>
    let val probt = default_prob in
      (case
        map_concl_to_string n
        (check_unsat_top_norm False (mk_prob objf) probt f3) of
        Inl err => TextIO.output TextIO.stdErr err
      | Inr s => TextIO.print s)
    end`

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
  Cases_on`y`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  assume_tac npbc_parseProgTheory.default_prob_v_thm>>
  xlet`POSTv v.
    STDIO fs *
    &prob_TYPE default_prob v`
  >-
    (xvar>>xsimpl)>>
  xlet_autop>>
  xlet`POSTv v. STDIO fs * &BOOL F v`
  >-
    (xcon>>xsimpl)>>
  drule npbc_parseProgTheory.check_unsat_top_norm_spec>>
  qpat_x_assum`prob_TYPE (mk_prob _) _`assume_tac>>
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
  every_case_tac>>gvs[SUM_TYPE_def]
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
    qexists_tac`print_mcis_str x`>>simp[]>>
    qexists_tac`strlit ""`>>
    rw[]>>simp[STD_streams_stderr,add_stdo_nil]>>
    xsimpl>>
    (drule_at Any) full_encode_mcis_sem_concl>>
    fs[]>>
    Cases_on`x`>> disch_then (drule_at Any)>>
    disch_then(qspec_then`gt'` mp_tac)>>
    impl_tac>-
      fs[get_graph_lad_def,AllCaseEqs(),mk_prob_def]>>
    rw[]>>
    qexists_tac`(q,r)`>>
    simp[mcis_sem_def]>>
    metis_tac[])
QED

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 f2 out ⇔
  case get_graph_lad fs f1 of
    NONE => out = strlit ""
  | SOME gpp =>
  case get_graph_lad fs f2 of
    NONE => out = strlit ""
  | SOME gtt =>
    out = concat (print_prob
      (mk_prob (full_encode_mcis gpp gtt)))
End

val check_unsat_2 = (append_prog o process_topdecs) `
  fun check_unsat_2 f1 f2 =
  case parse_and_enc f1 f2 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (n,objf) =>
    TextIO.print_list (print_prob (mk_prob objf))`

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
  Cases_on`y`>>gvs[PAIR_TYPE_def]>>
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

Definition usage_string_def:
  usage_string = strlit "Usage: cake_pb_mcis <LAD file (pattern)> <LAD file (target)> <optional: PB proof file>\n"
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
