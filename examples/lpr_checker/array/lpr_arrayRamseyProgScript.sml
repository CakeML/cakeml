(*
  This builds a proof checker specialized to Ramsey number 4
*)
Theory lpr_arrayRamseyProg
Ancestors
  lpr_composeProg UnsafeProof lpr lpr_list lpr_parsing
  HashtableProof lpr_arrayProg lpr_arrayParsingProg ramsey
  basis_ffi
Libs
  preamble basis

val _ = temp_delsimps ["NORMEQ_CONV"] (*"*)
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = translation_extends"lpr_arrayParsingProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

(* This function is not specific to Ramsey, can take any encoder  *)

(* 0 arg *)
val check_unsat_0 = (append_prog o process_topdecs) `
  fun check_unsat_0 enc =
    TextIO.print_list (print_dimacs (enc ()))`

Definition check_unsat_0_sem_def:
  check_unsat_0_sem enc out =
    (out = concat (print_dimacs (enc ())))
End

Theorem check_unsat_0_spec:
  (UNIT_TYPE --> LIST_TYPE (LIST_TYPE INT)) enc encv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_0"(get_ml_prog_state()))
    [encv]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
      SEP_EXISTS out err.
        STDIO (add_stdout (add_stderr fs err) out) *
        &(check_unsat_0_sem enc out))
Proof
  rw[]>>
  xcf "check_unsat_0" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  rpt xlet_autop>>
  xapp_spec print_list_spec>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  simp[check_unsat_0_sem_def]>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>qexists_tac`strlit ""`>>
  simp[STD_streams_add_stdout,STD_streams_add_stderr, STD_streams_stdout,STD_streams_stderr,add_stdo_nil]>>
  xsimpl
QED

val res = translate miscTheory.enumerate_def;

(* 1 arg *)
Definition max_lit_fml_def:
  max_lit_fml fml = Num (max_lit 0 (MAP (max_lit 0) fml))
End

val res = translate max_lit_fml_def;

val max_lit_fml_side = Q.prove(
  `∀x. max_lit_fml_side x = T`,
  rw[definition"max_lit_fml_side_def"]>>
  `0 ≤ 0:int` by fs[]>> drule max_lit_max_1>>
  simp[])
  |> update_precondition;

val check_unsat_1 = (append_prog o process_topdecs) `
  fun check_unsat_1 enc f =
  let val fml = enc ()
      val one = 1
      val arr = Array.array (2*(List.length fml)) None
      val arr = fill_arr arr one fml
      val mv = max_lit_fml fml
      val bnd = 2*mv + 3
      val earr = Array.array bnd None
      val earr = fill_earliest earr one fml
      val rls = rev_enum_full 1 fml
  in
    case check_unsat' 0 arr rls earr f bnd [[]] of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr None => TextIO.print "s VERIFIED UNSAT\n"
    | Inr (Some l) => TextIO.output TextIO.stdErr "c empty clause not derived at end of proof\n"
  end`

Definition check_unsat_1_sem_def:
  check_unsat_1_sem fs enc f out =
  let fml = enc () in
    (out ≠ strlit"" ⇒
      ∃lpr.
        EVERY wf_lpr lpr ∧
        out = strlit "s VERIFIED UNSAT\n" ∧
        let fmlls = misc$enumerate 1 fml in
        let base = REPLICATE (2*LENGTH fmlls) NONE in
        let mv = max_lit_fml fml in
        let bnd = 2*mv+3 in
        let upd = FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) base fmlls in
        let earliest = FOLDL (λacc (i,v). update_earliest acc i v) (REPLICATE bnd NONE) fmlls in
        check_lpr_unsat_list lpr upd (REVERSE (MAP FST fmlls)) (REPLICATE bnd w8z) earliest)
End

val err_tac = xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>qexists_tac`err`>>xsimpl;

Theorem check_unsat_1_spec:
  (UNIT_TYPE --> LIST_TYPE (LIST_TYPE INT)) enc encv ∧
  STRING_TYPE f fv ∧ validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_1"(get_ml_prog_state()))
    [encv; fv]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
      SEP_EXISTS out err.
        STDIO (add_stdout (add_stderr fs err) out) *
        &(check_unsat_1_sem fs enc f out))
Proof
  rw[]>>
  xcf "check_unsat_1" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  rpt xlet_autop>>
  xlet`POSTv v. &NUM 1 v * STDIO fs` >- (xlit>>xsimpl)>>
  drule fill_arr_spec>>
  drule fill_earliest_spec>>
  rw[]>>
  rpt xlet_autop>>
  (* help instantiate fill_arr_spec *)
  qmatch_asmsub_abbrev_tac`NUM (LENGTH fmlls) nv`>>
  `LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (REPLICATE (2*(LENGTH fmlls)) NONE)
        (REPLICATE (2 * (LENGTH fmlls)) (Conv (SOME (TypeStamp "None" 2)) []))` by
    simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
  first_x_assum drule>>
  rpt (disch_then drule)>>
  strip_tac>>
  rpt xlet_autop>>
  simp [] >> rpt xlet_autop >>
  (* help instantiate fill_earliest_spec *)
  qmatch_asmsub_abbrev_tac`NUM (2 * mv) _`>>
  `LIST_REL (OPTION_TYPE NUM) (REPLICATE (2 * mv + 3) NONE)
          (REPLICATE (2 * mv + 3) (Conv (SOME (TypeStamp "None" 2)) []))` by
    simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
  first_x_assum drule>>
  disch_then drule>>
  strip_tac>>
  simp[Abbr`mv`]>>
  rpt xlet_autop >>
  simp[check_unsat_1_sem_def,check_lpr_unsat_list_def]>>
  qmatch_goalsub_abbrev_tac`check_lpr_list _ _ a b c d`>>
  xlet`POSTv v.
    STDIO fs *
    SEP_EXISTS res.
      &(SUM_TYPE STRING_TYPE (OPTION_TYPE (LIST_TYPE INT)) res v ∧
      case res of
        INL err => T
      | INR bb =>
        inFS_fname fs f ∧
        ∃lpr fml' inds'.
          EVERY wf_lpr lpr ∧
          check_lpr_list 0 lpr a b c d = SOME (fml', inds') ∧
          bb = contains_clauses_list_err fml' inds' [[]])`
  >- (
    xapp_spec (GEN_ALL check_unsat'_spec)>>
    rpt(first_x_assum (irule_at Any))>>
    xsimpl>>
    fs[FILENAME_def,validArg_def]>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    qexists_tac`[[]]`>>simp[LIST_TYPE_def]>>
    qexists_tac`emp`>>xsimpl>>
    CONJ_TAC>- (
      unabbrev_all_tac>>
      `EVERY (EVERY (λi. Num (ABS i) ≤ max_lit_fml (enc ()))) (enc ())` by
        (simp[max_lit_fml_def]>>
        metis_tac[max_lit_max_lit_max])>>
      rw[bounded_fml_def,EVERY_EL]>>
      `ALL_DISTINCT (MAP FST (enumerate 1 (enc())))` by
        metis_tac[ALL_DISTINCT_MAP_FST_enumerate]>>
      drule FOLDL_update_resize_lookup>>
      disch_then drule>>
      strip_tac>>simp[]>>
      TOP_CASE_TAC>>fs[]>>
      drule ALOOKUP_MEM>>
      strip_tac>> drule MEM_enumerate_IMP>>
      qpat_x_assum`EVERY _ (enc ())` mp_tac>>
      simp[Once EVERY_MEM,Once EVERY_EL]>>
      rw[]>>
      first_x_assum drule>>
      disch_then drule>>
      simp[index_def]>>rw[]>>
      intLib.ARITH_TAC)>>
    fs[LENGTH_enumerate,rev_enum_full_rev_enumerate]>>
    metis_tac[])>>
  every_case_tac>>gvs[SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`strlit""`>>xsimpl>>
    rename1`add_stderr fs err`>>
    qexists_tac`err`>>xsimpl>>
    simp[STD_streams_add_stdout,STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  Cases_on`contains_clauses_list_err fml' inds' [[]]`>>
  fs[contains_clauses_list_err]>>
  fs[SUM_TYPE_def,OPTION_TYPE_def]
  >- (
    xmatch>>
    xapp_spec print_spec >> xsimpl
    \\ qexists_tac`emp`
    \\ qexists_tac`fs`>>xsimpl \\ rw[]>>
    qexists_tac`«s VERIFIED UNSAT\n»`>>
    qexists_tac`strlit""`>>rw[]
    >-
      (qexists_tac`lpr`>>simp[])
    >>
      simp[STD_streams_add_stdout,STD_streams_add_stderr, STD_streams_stderr, STD_streams_stdout,add_stdo_nil]>>
      xsimpl)>>
  xmatch>>
  xapp_spec output_stderr_spec \\ xsimpl>>
  qexists_tac`emp`>>xsimpl>>
  qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`strlit""`>>xsimpl>>
  rename1`add_stderr fs err`>>
  qexists_tac`err`>>xsimpl>>
  simp[STD_streams_add_stdout,STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  xsimpl
QED

(* Translate the thunked enc call *)
Definition enc_def:
  enc () = ramsey_lpr 4 18
End

val res = translate choose_def;
val res = translate (COUNT_LIST_GENLIST);
val res = translate transpose_def;
val res = translate encoder_def;
val res = translate clique_edges_def;
val res = translate ramsey_lpr_def;
val res = translate enc_def;

val usage_string = ‘
Usage: ramsey_check <LPR proof files>

Checks a LPR proof for Ramsey number 4.

Prints the internal CNF representation of proof file is not given.
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

val check_unsat = (append_prog o process_topdecs) `
  fun check_unsat u =
  case CommandLine.arguments () of
    [] => check_unsat_0 enc
  | [f] => check_unsat_1 enc f
  | _ => TextIO.output TextIO.stdErr usage_string`

Definition check_unsat_sem_def:
  check_unsat_sem cl fs out =
  case TL cl of
    [] => check_unsat_0_sem enc out
  | [f] => check_unsat_1_sem fs enc f out
  | _ => out = strlit ""
End

Theorem check_unsat_spec:
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat"(get_ml_prog_state()))
    [Conv NONE []]
    (COMMANDLINE cl * STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    COMMANDLINE cl *
    SEP_EXISTS out err.
      STDIO (add_stdout (add_stderr fs err) out) *
      &(check_unsat_sem cl fs out))
Proof
  rw[]>>
  xcf"check_unsat"(get_ml_prog_state())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)>>
  rpt xlet_autop >>
  Cases_on `cl` >- fs[wfcl_def] >>
  simp[check_unsat_sem_def]>>
  every_case_tac>>fs[LIST_TYPE_def]>>xmatch>>
  qmatch_asmsub_abbrev_tac`wfcl cl`
  >- (
    xapp>>xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac`fs`>>qexists_tac`enc`>>xsimpl>>
    simp[theorem "enc_v_thm"]>>
    rw[]>>first_x_assum(irule_at Any)>>
    rename1`add_stderr fs err`>>
    qexists_tac`err`>>xsimpl)
  >- (
    xapp>>xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac`fs`>>
    first_x_assum (irule_at Any)>>
    xsimpl>>
    rw[]>>xsimpl>>
    qexists_tac`enc`>>xsimpl>>
    rw[]>>xsimpl>>
    simp[theorem "enc_v_thm"]
    >- fs[FILENAME_def,validArg_def,wfcl_def,Abbr`cl`]>>
    rename1`add_stdout (add_stderr fs err) out`>>
    qexists_tac`out`>>qexists_tac`err`>>
    xsimpl)>>
  xapp_spec output_stderr_spec \\ xsimpl>>
  qexists_tac`COMMANDLINE cl`>>xsimpl>>
  qexists_tac `usage_string` >>
  simp [theorem "usage_string_v_thm"] >>
  qexists_tac`fs`>>xsimpl>>
  rw[]>>qexists_tac`usage_string`>>xsimpl>>
  simp[STD_streams_add_stdout,STD_streams_add_stderr, STD_streams_stdout,STD_streams_stderr,add_stdo_nil]>>
  xsimpl
QED

Theorem check_unsat_whole_prog_spec2:
   hasFreeFD fs ⇒
   whole_prog_spec2 check_unsat_v cl fs NONE
    (λfs'. ∃out err.
        fs' = add_stdout (add_stderr fs err) out ∧
        check_unsat_sem cl fs out)
Proof
  rw[basis_ffiTheory.whole_prog_spec2_def]
  \\ match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH check_unsat_spec))))
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
