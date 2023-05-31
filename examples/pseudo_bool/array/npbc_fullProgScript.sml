(*
  Add PBF parsing and wrap around the PBP parser
*)
open preamble basis pb_parseTheory pbc_normaliseTheory npbc_parseProgTheory;

val _ = new_theory "npbc_fullProg"

val _ = translation_extends"npbc_parseProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

(* Translation for parsing an OPB file *)
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

val r = translate parse_op_def;
val r = translate parse_constraint_def;
val r = translate parse_constraints_def;

val r = translate parse_obj_def;
val r = translate parse_obj_maybe_def;
val r = translate parse_pbf_toks_def;

Definition noparse_string_def:
  noparse_string f s = concat[strlit"c Input file: ";f;strlit" unable to parse in format: "; s;strlit"\n"]
End

val r = translate noparse_string_def;

val parse_pbf_full = (append_prog o process_topdecs) `
  fun parse_pbf_full f =
  (case TextIO.b_inputAllTokensFrom f blanks tokenize of
    None => Inl (notfound_string f)
  | Some lines =>
  (case parse_pbf_toks lines of
    None => Inl (noparse_string f "OPB")
  | Some res => Inr res
  ))`

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
    & (∃err. (SUM_TYPE STRING_TYPE
      (PAIR_TYPE
      (OPTION_TYPE (PAIR_TYPE
        (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
      INT))
      (LIST_TYPE (PAIR_TYPE PBC_PBOP_TYPE (PAIR_TYPE (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE))) INT)))
      ))
    (if inFS_fname fs f then
    (case parse_pbf (all_lines fs f) of
      NONE => INL err
    | SOME res => INR res)
    else INL err) v) * STDIO fs)
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
    rw[parse_pbf_def]>> TOP_CASE_TAC>>
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

(* normalise *)
val res = translate normalise_obj_def;
val res = translate flip_coeffs_def;
val res = translate pbc_ge_def;
val res = translate normalise_def;
val res = translate normalise_obj_pbf_def;

val res = translate mk_map_def;
val res = translate name_to_num_var_def;
val res = translate name_to_num_lit_def;
val res = translate name_to_num_lin_term_def;
val res = translate name_to_num_obj_def;
val res = translate name_to_num_pbf_def;
val res = translate name_to_num_obj_pbf_def;

Definition hash_str_def:
  hash_str (s:mlstring) =
    let l = strlen s in
      if l = 0 then 0:num else
        l + ORD (strsub s (l-1))
End

Definition normalise_full_def:
  normalise_full objf =
  let s = init_state hash_str compare in
  let (objf',t) = name_to_num_obj_pbf objf s in
  (normalise_obj_pbf objf', t)
End

val res = translate init_state_def;
val res = translate hash_str_def;

val hash_str_side = Q.prove(
  `∀x. hash_str_side x <=> T`,
  EVAL_TAC>>
  intLib.ARITH_TAC) |> update_precondition;

val res = translate normalise_full_def;

(* actually a pair (obj,fml) *)
Definition get_fml_def:
  get_fml fs f =
  if inFS_fname fs f then
    parse_pbf (all_lines fs f)
  else NONE
End

Definition int_inf_to_string_def:
  (int_inf_to_string NONE = strlit "INF") ∧
  (int_inf_to_string (SOME (i:int)) =
    toString i)
End

Definition concl_to_string_def:
  (concl_to_string NoConcl = strlit "s VERIFIED NO CONCLUSION\n") ∧
  (concl_to_string DSat = strlit "s VERIFIED SATISFIABLE") ∧
  (concl_to_string DUnsat = strlit "s VERIFIED UNSATISFIABLE") ∧
  (concl_to_string (OBounds lbi ubi) =
    let lbs = int_inf_to_string lbi in
    let ubs = int_inf_to_string ubi in
    strlit "s VERIFIED BOUNDS " ^ lbs ^ strlit " <= obj <= " ^ ubs)
End

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 out ⇔
  (out ≠ strlit"" ⇒
  ∃obj fml.
    get_fml fs f1 = SOME (obj,fml)
    ∧
    ∃concl.
      out = concl_to_string concl ∧
      pbc$sem_concl (set fml) obj concl)
End

Definition name_to_num_var_nf_def:
  name_to_num_var_nf v s =
  SOME (name_to_num_var v s)
End

val res = translate name_to_num_var_nf_def;

Definition map_concl_to_string_def:
  (map_concl_to_string (INL s) = (INL s)) ∧
  (map_concl_to_string (INR c) = (INR (concl_to_string c)))
End

val res = translate int_inf_to_string_def;
val res = translate concl_to_string_def;
val res = translate map_concl_to_string_def;

val check_unsat_2 = (append_prog o process_topdecs) `
  fun check_unsat_2 f1 f2 =
  case parse_pbf_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr objf =>
    (case normalise_full objf of ((obj,fml),t) =>
    (case
      map_concl_to_string
        (check_unsat_top (name_to_num_var_nf,t) fml obj f2) of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr s => TextIO.print s))`

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
      &(check_unsat_2_sem fs f1 out))
Proof
  rw[check_unsat_2_sem_def]>>
  xcf "check_unsat_2" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  xlet_autop>>
  pop_assum mp_tac>>
  reverse IF_CASES_TAC
  >- (
    simp[SUM_TYPE_def]>>rw[]>>
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`strlit""`>>
    qexists_tac`err`>>xsimpl>>rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  TOP_CASE_TAC
  >- (
    simp[SUM_TYPE_def]>>rw[]>>
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`strlit""`>>
    qexists_tac`err`>>xsimpl>>rw[]>>
    fs[STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  simp[SUM_TYPE_def]>>rw[]>>
  xmatch>>
  xlet_autop>>
  `∃obj fml t.
    normalise_full x = ((obj,fml),t)` by
    (Cases_on`normalise_full x`>>Cases_on`q`>>metis_tac[])>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xlet`POSTv v.
    STDIO fs *
    SEP_EXISTS res.
     &(
        SUM_TYPE STRING_TYPE PBC_CONCL_TYPE res v ∧
        case res of
          INR concl =>
            sem_concl (set fml) obj concl
        | INL l => T)`
  >- (
    xapp_spec (check_unsat_top_spec |> INST_TYPE[alpha|->``:mlstring name_to_num_state``])>>
    xsimpl>>
    CONJ_TAC >- (
      fs[FILENAME_def,validArg_def,OPTION_TYPE_def]>>
      metis_tac[])>>
    qexists_tac`PBC_NORMALISE_NAME_TO_NUM_STATE_TYPE STRING_TYPE`>>
    qexists_tac`(name_to_num_var_nf,t)`>>
    simp[PAIR_TYPE_def]>>
    metis_tac[fetch "-" "name_to_num_var_nf_v_thm"])>>
  xlet_autop>>
  Cases_on`res`>>fs[map_concl_to_string_def,SUM_TYPE_def]>>xmatch
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
    xsimpl)>>
  xapp>>asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`concl_to_string y`>>simp[]>>
  qexists_tac`strlit ""`>>
  rw[]>>simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl>>
  fs[get_fml_def]>>
  Cases_on`x`>>fs[normalise_full_def]>>
  pairarg_tac>>fs[]>>
  qexists_tac`y`>>gvs[]>>
  Cases_on`objf'`>>
  drule name_to_num_obj_pbf_thm>>
  disch_then(qspec_then`y` mp_tac)>>
  impl_tac >- (
    match_mp_tac init_state_ok>>
    fs[TotOrd_compare])>>
  rw[]>>
  metis_tac[normalise_obj_pbf_sem_concl]
QED

(* TODO
Definition print_pbf_def:
  print_pbf f = MAP pbc_string f
End

val res = translate pb_parseTheory.lit_string_def;
val res = translate pb_parseTheory.lhs_string_def;
val res = translate pb_parseTheory.op_string_def;
val res = translate pb_parseTheory.pbc_string_def;
val res = translate print_pbf_def;

val check_unsat_1 = (append_prog o process_topdecs) `
  fun check_unsat_1 f1 =
    case parse_pbf_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr fml =>
  TextIO.print_list (print_pbf fml)`

Definition check_unsat_1_sem_def:
  check_unsat_1_sem fs f1 out ⇔
  if inFS_fname fs f1
  then
    case parse_pbf (all_lines fs f1) of
      NONE => out = strlit ""
    | SOME (NONE, fml) => out = concat (print_pbf fml)
    | _ => out = strlit ""
  else out = strlit ""
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
  pop_assum mp_tac>>
  reverse IF_CASES_TAC
  >- (
    simp[SUM_TYPE_def]>>rw[]>>
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
    fs[success_string_not_nil,STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    rw[]>>
    qexists_tac`err`>>xsimpl)>>
  TOP_CASE_TAC>>fs[SUM_TYPE_def]
  >- (
    rw[]>>
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
    fs[success_string_not_nil,STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
    rw[]>>
    qexists_tac`err`>>xsimpl)>>
  TOP_CASE_TAC>>
  TOP_CASE_TAC>>fs[SUM_TYPE_def]>>
  rw[]>>xmatch
  >- (
    xlet_autop>>
    xapp_spec print_list_spec>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`strlit ""`>>
    simp[STD_streams_stderr,add_stdo_nil]>>
    xsimpl) >>
  (* optimization not yet supported *)
  xapp_spec output_stderr_spec \\ xsimpl>>
  asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  fs[success_string_not_nil,STD_streams_add_stderr, STD_streams_stdout,add_stdo_nil]>>
  rw[]>>
  qexists_tac`err`>>xsimpl
QED
*)

Definition usage_string_def:
  usage_string = strlit "Usage: cake_pb <OPB file> <proof file>\n"
End

val r = translate usage_string_def;

(*TODO: [f1] => check_unsat_1 f1 *)
val main = (append_prog o process_topdecs) `
  fun main u =
  case CommandLine.arguments () of
   [f1,f2] => check_unsat_2 f1 f2
  | _ => TextIO.output TextIO.stdErr usage_string`

(* TODO:  if LENGTH cl = 2 then
    check_unsat_1_sem fs (EL 1 cl) out
  else  *)
Definition main_sem_def:
  main_sem fs cl out =
  if LENGTH cl = 3 then
    check_unsat_2_sem fs (EL 1 cl) out
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
  (* TODO: 1 arg >- (
    xmatch>>
    xapp>>fs[]>>
    rw[]>>
    fs[wfcl_def]>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
    rw[]>>
    metis_tac[STDIO_refl])>> *)
  Cases_on`t`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp>>rw[]>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
    first_x_assum (irule_at Any)>>xsimpl>>
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
