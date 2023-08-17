(*
  This builds a proof checker specialized to Ramsey number 4
*)
open preamble basis lpr_composeProgTheory UnsafeProofTheory lprTheory lpr_listTheory lpr_parsingTheory HashtableProofTheory lpr_arrayProgTheory ;

open ramseyTheory;

val _ = new_theory "lpr_arrayRamseyProg"

val _ = temp_delsimps ["NORMEQ_CONV"] (*"*)
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = translation_extends"lpr_arrayProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

(* This function is not specific to Ramsey, can take any encoder  *)

(* 0 arg *)
val check_unsat_0 = (append_prog o process_topdecs) `
  fun check_unsat_0 enc =
    TextIO.print_list (print_dimacs (enc ()))`

val check_unsat_0_sem_def = Define`
  check_unsat_0_sem fs enc =
    add_stdout fs (concat (print_dimacs (enc ())))`

Theorem check_unsat_0_spec:
  (UNIT_TYPE --> LIST_TYPE (LIST_TYPE INT)) enc encv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_0"(get_ml_prog_state()))
    [encv]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv * STDIO (check_unsat_0_sem fs enc))
Proof
  rw[]>>
  xcf "check_unsat_0" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xapp_spec print_list_spec>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  simp[check_unsat_0_sem_def]>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl
QED

val res = translate miscTheory.enumerate_def;

(* 1 arg *)
val max_lit_fml_def = Define`
  max_lit_fml fml = Num (max_lit 0 (MAP (max_lit 0) fml))`

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

val check_unsat_1_sem_def = Define`
  check_unsat_1_sem fs enc f err =
  let fml = enc () in
    if inFS_fname fs f then
      case parse_lpr (all_lines fs f) of
        SOME lpr =>
        let fmlls = misc$enumerate 1 fml in
        let base = REPLICATE (2*LENGTH fmlls) NONE in
        let mv = max_lit_fml fml in
        let bnd = 2*mv+3 in
        let upd = FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) base fmlls in
        let earliest = FOLDL (λacc (i,v). update_earliest acc i v) (REPLICATE bnd NONE) fmlls in
          if check_lpr_unsat_list lpr upd (REVERSE (MAP FST fmlls)) (REPLICATE bnd w8z) earliest then
            add_stdout fs (strlit "s VERIFIED UNSAT\n")
          else
            add_stderr fs err
      | NONE => add_stderr fs err
    else add_stderr fs err`

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
    SEP_EXISTS err. STDIO (check_unsat_1_sem fs enc f err))
Proof
  rw[]>>
  xcf "check_unsat_1" (get_ml_prog_state ())>>
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
    SEP_EXISTS err.
     &SUM_TYPE STRING_TYPE (OPTION_TYPE (LIST_TYPE INT))
      (if inFS_fname fs f then
         (case parse_lpr (all_lines fs f) of
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
      unabbrev_all_tac>>
      `EVERY (EVERY (λi. Num (ABS i) ≤ max_lit_fml (enc ()))) (enc ())` by
        (simp[max_lit_fml_def]>>
        metis_tac[max_lit_max_lit_max])>>
      rw[bounded_fml_def,EVERY_EL]>>
      `ALL_DISTINCT (MAP FST (enumerate 1 (enc())))` by
        metis_tac[ALL_DISTINCT_MAP_FST_enumerate]>>
      drule FOLDL_resize_update_list_lookup>>
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

(* Translate the thunked enc call *)
val enc_def = Define`
  enc () = ramsey_lpr 4 18`

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

val check_unsat_sem_def = Define`
  check_unsat_sem cl fs err =
  case TL cl of
    [] => check_unsat_0_sem fs enc
  | [f] => check_unsat_1_sem fs enc f err
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
    xapp>>xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac`fs`>>qexists_tac`enc`>>xsimpl>>
    simp[theorem "enc_v_thm"])
  >- (
    xapp>>xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac`fs`>>
    qexists_tac`h'`>>
    qexists_tac`enc`>>xsimpl>>
    rw[]>>xsimpl>>
    simp[theorem "enc_v_thm"]
    >-
      fs[FILENAME_def,validArg_def,wfcl_def,Abbr`cl`]>>
      qexists_tac`x`>>xsimpl)>>
  xapp_spec output_stderr_spec \\ xsimpl>>
  qexists_tac`COMMANDLINE cl`>>xsimpl>>
  qexists_tac `usage_string` >> simp [theorem "usage_string_v_thm"] >>
  qexists_tac`fs`>>xsimpl>>
  rw[]>>qexists_tac`usage_string`>>xsimpl
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
  \\ rw[check_unsat_sem_def,check_unsat_0_sem_def,check_unsat_1_sem_def]
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

val _ = export_theory();
