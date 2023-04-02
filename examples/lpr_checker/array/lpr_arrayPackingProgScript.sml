(*
  This builds a proof checker specialized to the
  packing chromatic number bounds
*)
open preamble basis lpr_composeProgTheory UnsafeProofTheory lprTheory lpr_listTheory lpr_parsingTheory HashtableProofTheory lpr_arrayProgTheory ;

open packingTheory;

val _ = new_theory "lpr_arrayPackingProg"

val _ = temp_delsimps ["NORMEQ_CONV"] (*"*)
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = translation_extends"lpr_arrayProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

val usage_string = ‘
Input: <r = radius> <k = total colors> <c = center color, 1 ≤ c ≤ k>

Outputs a direct encoding CNF whose unsatisfiability implies a lower bound of k+1 for the packing chromatic number of the plane.
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

(* Make sure the inputs are valid *)
Definition parse_numbers_def:
  parse_numbers r k c =
  case (fromNatString r,fromNatString k,fromNatString c) of
    (SOME r, SOME k, SOME c) =>
      if 1 ≤ c ∧ c ≤ k then SOME (r,k,c) else NONE
  | _ => NONE
End

val r = translate parse_numbers_def;

(* 3 arg *)
val check_unsat_3 = (append_prog o process_topdecs) `
  fun check_unsat_3 enc r k c =
    case parse_numbers r k c of
      Some (r,(k,c)) =>
      TextIO.print_list (print_dimacs (enc r k c))
    | None =>
      TextIO.output TextIO.stdErr usage_string`

val check_unsat_3_sem_def = Define`
  check_unsat_3_sem fs enc r k c err =
    case parse_numbers r k c of
      SOME (r,k,c) =>
      add_stdout fs (concat (print_dimacs (enc r k c)))
    | NONE => add_stderr fs err`

Theorem check_unsat_3_spec:
  STRING_TYPE r rv ∧
  STRING_TYPE k kv ∧
  STRING_TYPE c cv ∧
  (NUM --> NUM --> NUM -->
    LIST_TYPE (LIST_TYPE INT)) enc encv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_3"(get_ml_prog_state()))
    [encv; rv; kv; cv]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
      SEP_EXISTS err. STDIO (check_unsat_3_sem fs enc r k c err))
Proof
  rw[]>>
  xcf "check_unsat_3" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  Cases_on`parse_numbers r k c`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    qexists_tac`emp`>>
    qexists_tac `usage_string` >> simp [theorem "usage_string_v_thm"] >>
    qexists_tac`fs`>>xsimpl>>
    simp[check_unsat_3_sem_def]>>
    rw[]>>qexists_tac`usage_string`>>xsimpl)>>
  PairCases_on`x`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xapp_spec print_list_spec>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  simp[check_unsat_3_sem_def]>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl
QED

val res = translate balanced_mapTheory.lookup_def;
val res = translate balanced_mapTheory.singleton_def;
val res = translate balanced_mapTheory.ratio_def;
val res = translate balanced_mapTheory.size_def;
val res = translate balanced_mapTheory.delta_def;
val res = translate balanced_mapTheory.balanceL_def;
val res = translate balanced_mapTheory.balanceR_def;
val res = translate balanced_mapTheory.insert_def;
val res = translate balanced_mapTheory.empty_def;
val res = translate remap_var_def;
val res = translate remap_lit_def;
val res = translate remap_clause_def;
val res = translate remap_fml_def;
val res = translate cmp_pair_def;
val res = translate cmp_num_def;
val res = translate cmp_int_def;
val res = translate cmp_nii_def;
val res = translate cmp_nii_def;
val res = translate remap_nii_def;

val res = translate packingTheory.fix_col_def;
val res = translate packingTheory.in_ball_def;
val res = translate packingTheory.vertices_def;
val res = translate packingTheory.fix_cols_def;
val res = translate packingTheory.restrict_col_def;
val res = translate packingTheory.restrict_cols_def;
val res = translate packingTheory.full_restrict_def;
val res = translate packingTheory.encode_def;
val res = translate full_encode_def;

val main = (append_prog o process_topdecs) `
  fun main u =
  case CommandLine.arguments () of
    [r,k,c] => check_unsat_3 full_encode r k c
  | _ => TextIO.output TextIO.stdErr usage_string`

val main_sem_def = Define`
  main_sem cl fs err =
  case TL cl of
    [r;k;c] => check_unsat_3_sem fs full_encode r k c err
  | _ => add_stderr fs err`

Theorem main_spec:
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"main"(get_ml_prog_state()))
    [Conv NONE []]
    (COMMANDLINE cl * STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    COMMANDLINE cl * SEP_EXISTS err. STDIO (main_sem cl fs err))
Proof
  xcf"main"(get_ml_prog_state())>>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)>>
  rpt xlet_autop >>
  Cases_on `cl` >- fs[wfcl_def] >>
  simp[main_sem_def]>>
  every_case_tac>>fs[LIST_TYPE_def]>>xmatch>>
  qmatch_asmsub_abbrev_tac`wfcl cl` >>
  TRY (
    xapp_spec output_stderr_spec \\ xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `usage_string` >> simp [theorem "usage_string_v_thm"] >>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexists_tac`usage_string`>>xsimpl)
  >- (
    xapp>>xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    rpt(asm_exists_tac>> simp[])>>
    qexists_tac`fs`>>
    qexists_tac`full_encode`>>simp [theorem "full_encode_v_thm"] >>
    rw[]>>xsimpl>>
    qexists_tac`x`>>xsimpl)
QED

Theorem main_whole_prog_spec2:
   hasFreeFD fs ⇒
   whole_prog_spec2 main_v cl fs NONE (λfs'. ∃err. fs' = main_sem cl fs err)
Proof
  rw[basis_ffiTheory.whole_prog_spec2_def]
  \\ match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH main_spec))))
  \\ xsimpl
  \\ rw[PULL_EXISTS]
  \\ qexists_tac`main_sem cl fs x`
  \\ qexists_tac`x`
  \\ xsimpl
  \\ rw[main_sem_def,check_unsat_3_sem_def]
  \\ every_case_tac
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
