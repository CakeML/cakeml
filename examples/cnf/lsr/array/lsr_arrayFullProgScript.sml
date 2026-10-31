(*
  This builds the cake_lsr proof checker
*)
Theory lsr_arrayFullProg
Ancestors
  misc UnsafeProof cnf ccnf ccnf_list ccnf_arrayProg ccnf_parseProg
  syntax_helper dimacs lsr lsr_list lsr_roundProg lsr_arrayProg
  mlvector mllist basis_ffi
Libs
  preamble basis

val _ = translation_extends"lsr_arrayProg";

(*** Tautological input clauses (T14) ***)

(* Literals ordered by variable, the negative literal of a variable before
  the positive one *)
Definition ilit_le_def:
  ilit_le (x:int) (y:int) ⇔ ABS x < ABS y ∨ (ABS x = ABS y ∧ x ≤ y)
End

(* In a list sorted by ilit_le a literal and its negation are adjacent *)
Definition taut_sorted_def:
  (taut_sorted ((x:int)::y::ys) ⇔ y = -x ∨ taut_sorted (y::ys)) ∧
  (taut_sorted _ ⇔ F)
End

(* A tautological input clause is loaded as a deleted clause, keeping its
  id; every other clause is loaded as parsed *)
Definition drop_taut_def:
  drop_taut c =
  if taut_sorted (sort ilit_le (toList c)) then vcc_none else c
End

val res = translate ilit_le_def;
val res = translate taut_sorted_def;
val res = translate drop_taut_def;

Theorem ilit_le_total_transitive:
  total ilit_le ∧ transitive ilit_le
Proof
  rw[relationTheory.total_def,relationTheory.transitive_def,ilit_le_def]>>
  intLib.ARITH_TAC
QED

Theorem taut_sorted_SORTED:
  ∀l. SORTED ilit_le l ∧ ¬MEM 0 l ⇒
  (taut_sorted l ⇔ ∃x. MEM x l ∧ MEM (-x) l)
Proof
  Induct>>
  simp[taut_sorted_def]>>
  rpt strip_tac>>
  `SORTED ilit_le l ∧ ∀y. MEM y l ⇒ ilit_le h y` by
    metis_tac[SORTED_EQ,ilit_le_total_transitive]>>
  gvs[]>>
  Cases_on`l`>>
  gvs[taut_sorted_def]
  >- intLib.ARITH_TAC>>
  `∀y. MEM y t ⇒ ilit_le h' y` by
    metis_tac[SORTED_EQ,ilit_le_total_transitive]>>
  `∀y. ilit_le h y ∧ ilit_le y (-h) ⇒ y = h ∨ y = -h` by (
    rw[ilit_le_def]>>
    intLib.ARITH_TAC)>>
  eq_tac
  >- metis_tac[]>>
  disch_then (qx_choose_then `x` assume_tac)>>
  `-h ≠ h ∧ (-x = h ⇔ x = -h)` by intLib.ARITH_TAC>>
  Cases_on`x ≠ h ∧ x ≠ -h`
  >- metis_tac[]>>
  Cases_on`h' = -h`
  >- simp[]>>
  `MEM (-h) t` by metis_tac[]>>
  disj2_tac>>
  Cases_on`h' = h`
  >- metis_tac[]>>
  metis_tac[]
QED

(* drop_taut deletes exactly the tautologies *)
Theorem taut_sorted_sort:
  ¬MEM 0 l ⇒
  (taut_sorted (sort ilit_le l) ⇔ ∃x. MEM x l ∧ MEM (-x) l)
Proof
  strip_tac>>
  `SORTED ilit_le (sort ilit_le l)` by
    metis_tac[sort_SORTED,ilit_le_total_transitive]>>
  drule taut_sorted_SORTED>>
  simp[]
QED

Theorem drop_taut_bnd:
  EVERY (EVERY (λl. var_lit l < n)) cfml ∧ 0 < n ⇒
  EVERY (λc. bnd_clause c n) (MAP drop_taut (conv_cfml cfml))
Proof
  strip_tac>>
  drule bnd_clause_conv_cfml>>
  rw[EVERY_MAP,EVERY_MEM,drop_taut_def]>>
  rw[]>>
  gvs[bnd_clause_def,vcc_none_def,length_def,sub_def]
QED

Theorem drop_taut_nz:
  EVERY (EVERY nz_lit) cfml ⇒
  EVERY (λc. c ≠ vcc_none ⇒ ¬MEM 0 (toList c))
    (MAP drop_taut (conv_cfml cfml))
Proof
  strip_tac>>
  drule nz_vcfml_conv_cfml>>
  rw[EVERY_MAP,EVERY_MEM,drop_taut_def,nz_vcfml_def]>>
  rename1`MEM c (conv_cfml cfml)`>>
  Cases_on`taut_sorted (sort ilit_le (toList c))`>>
  gvs[]
QED

(* Every entry kept is a clause of the input, so a model of the input
  satisfies all of them *)
Theorem drop_taut_sound:
  EVERY (EVERY nz_lit) cfml ∧
  ¬(∃w. satisfies_vcfml w
          (set (MAP drop_taut (conv_cfml cfml)) DIFF {vcc_none})) ⇒
  unsatisfiable_cnf (set cfml)
Proof
  rw[unsatisfiable_cnf_def,satisfiable_cnf_def]>>
  CCONTR_TAC>>
  gvs[]>>
  `satisfies_vcfml w (set (conv_cfml cfml))` by metis_tac[conv_cfml_sound]>>
  first_x_assum (qspec_then`w` mp_tac)>>
  gvs[satisfies_vcfml_def,satisfies_fml_gen_def,MEM_MAP,PULL_EXISTS,
      drop_taut_def]>>
  rw[]>>
  gvs[]
QED

val usage_string = ‘

Usage:  cake_lsr [--] <CNF formula file> <optional: LSR proof file>
        cake_lsr --dump [--] <CNF formula file>

Run LSR unsatisfiability proof checking.
The proof is read from the proof file if one is given, and from standard input otherwise.
--dump parses the formula file and prints the formula.

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

(* == Build info =========================================================== *)

val current_version_tm = mlstring_from_proc "git" ["rev-parse", "HEAD"]
val poly_version_tm = mlstring_from_proc "poly" ["-v"]
val hol_version_tm = mlstring_from_proc "git" ["-C", Globals.HOLDIR, "rev-parse", "HEAD"]

val date_str = Date.toString (Date.fromTimeUniv (Time.now ())) ^ " UTC\n"
val date_tm = Term `strlit^(stringSyntax.fromMLstring date_str)`

Definition print_option_def:
  print_option h x =
    case x of
      NONE => «»
    | SOME y => h ^ « » ^ y ^ «\n»
End

val current_build_info_str_tm = EVAL ``
    let commit = print_option «CakeML:» ^current_version_tm in
    let hol    = print_option «HOL4:  » ^hol_version_tm in
    let poly   = print_option «PolyML:» ^poly_version_tm in
      concat
        [ «cake_lsr\n\n»
        ; «Version details:\n»
        ; ^date_tm; «\n»
        ; commit; hol; poly ]``
  |> concl |> rhs

Definition current_build_info_str_def:
  current_build_info_str = ^current_build_info_str_tm
End

val res = translate current_build_info_str_def;

Definition mk_usage_string_def:
  mk_usage_string s = current_build_info_str ^ «\n\n» ^ s
End

val res = translate mk_usage_string_def;

(*
  Checker takes up to 2 file arguments:
  --dump and 1 file (CNF file): parse and print the formula
  1 file (CNF file): as for 2 files, reading the proof from stdin
  2 files (CNF file, proof file):
    parse CNF, run proof, report UNSAT (or error)

  The arrays indexed by a variable have mv+1 slots for the initial formula
  (every literal satisfies var_lit l ≤ mv by check_maxvar); they grow on
  demand thereafter.
*)
Quote add_cakeml:
  fun check_unsat_2 f1 f2 =
  case parse_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv,(ncl,vcfml)) =>
    (case check_unsat' (List.map drop_taut vcfml) f2 (mv+1) (2*ncl) of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr b =>
      if b then
        TextIO.print "s VERIFIED UNSAT\n"
      else
        TextIO.output TextIO.stdErr "c empty clause not derived at end of proof\n")
End

Quote add_cakeml:
  fun check_unsat_stdin f1 =
  case parse_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv,(ncl,vcfml)) =>
    (case check_unsat_stdin' (List.map drop_taut vcfml) (mv+1) (2*ncl) of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr b =>
      if b then
        TextIO.print "s VERIFIED UNSAT\n"
      else
        TextIO.output TextIO.stdErr "c empty clause not derived at end of proof\n")
End

val _ = translate max_cnf_def;
val _ = translate print_cnf_def;
val _ = translate unconv_cfml_def;

Quote add_cakeml:
  fun check_unsat_1 f1 =
  case parse_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv,(ncl,vcfml)) =>
    let val f = unconv_cfml vcfml in
      TextIO.print_list (print_cnf (max_cnf f) f)
    end
End

(* The formula a run of the checker is about: the contents of the input
  file, when it exists and parses *)
Definition get_cnf_def:
  get_cnf fs f =
  if inFS_fname fs f
  then parse_cnf (all_lines_file fs f)
  else NONE
End

Definition check_unsat_1_sem_def:
  check_unsat_1_sem fs f1 out ⇔
  case get_cnf fs f1 of
    SOME fml => out = concat (print_cnf (max_cnf fml) fml)
  | NONE => out = «»
End

(* Every failure path prints nothing on stdout and reports err on stderr.
  out_tac supplies the empty stdout witness on the paths where the output
  predicate does not already pin it. *)
fun err_tac out_tac =
  xapp_spec output_stderr_spec>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>out_tac>>
  qexists_tac`err`>>
  fs[STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
  xsimpl;

val no_out = qexists_tac`«»`;

Theorem check_unsat_1_spec:
  STRING_TYPE f1 f1v ∧
  validArg f1 ∧
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
  rw[]>>
  xcf "check_unsat_1" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def]>>xpull)>>
  xlet_autop>>
  simp[check_unsat_1_sem_def,get_cnf_def,parse_cnf_def]>>
  reverse (Cases_on`inFS_fname fs f1`)>>fs[SUM_TYPE_def,parse_vcnf_toks]
  >- (xmatch>>err_tac all_tac)>>
  Cases_on`parse_cnf_toks (MAP toks (all_lines_file fs f1))`>>
  fs[SUM_TYPE_def]
  >- (xmatch>>err_tac all_tac)>>
  PairCases_on`x`>>
  gvs[PAIR_TYPE_def]>>
  rename1`parse_cnf_toks _ = SOME (mv,ncl,fml)`>>
  xmatch>>
  xlet_autop>>
  `unconv_cfml (conv_cfml fml) = fml` by
    metis_tac[unconv_cfml_conv_cfml,parse_cnf_toks_nz_lit]>>
  gvs[]>>
  xlet_autop>>
  xlet_autop>>
  xapp_spec print_list_spec>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexists_tac`«»`>>
  simp[STD_streams_stderr,add_stdo_nil]>>
  xsimpl
QED

(* Separates the options from the file names. d is set by --dump. A bare
  -- ends the options; any other argument starting with -- before it is
  unknown and gives NONE. *)
Definition split_flags_def:
  split_flags d [] = (SOME d, []) ∧
  split_flags d (a::as) =
    if a = «--» then (SOME d, as)
    else if a = «--dump» then split_flags T as
    else if isPrefix «--» a then (NONE, [])
    else
      case split_flags d as of (r, ps) => (r, a::ps)
End

val _ = translate split_flags_def;

Theorem split_flags_MEM:
  ∀as d r ps x. split_flags d as = (r, ps) ∧ MEM x ps ⇒ MEM x as
Proof
  Induct>>
  rw[split_flags_def]>>
  gvs[]
  >~ [`¬isPrefix _ _`]
  >- (
    Cases_on`split_flags d as`>>
    gvs[]>>
    qpat_x_assum`∀d r ps x. _`drule_all>>
    simp[])>>
  qpat_x_assum`∀d r ps x. _`drule_all>>
  simp[]
QED

Quote add_cakeml:
  fun check_unsat u =
  case split_flags False (CommandLine.arguments ()) of
    (Some True, [f1]) => check_unsat_1 f1
  | (Some False, [f1]) => check_unsat_stdin f1
  | (Some False, [f1,f2]) => check_unsat_2 f1 f2
  | _ => TextIO.output TextIO.stdErr (mk_usage_string usage_string)
End

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 out ⇔
  (out ≠ «» ⇒
    out = «s VERIFIED UNSAT\n» ∧
    ∃fml. get_cnf fs f1 = SOME fml ∧ unsatisfiable_cnf (set fml))
End

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
  rw[]>>
  xcf "check_unsat_2" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def]>>xpull)>>
  xlet_autop>>
  simp[check_unsat_2_sem_def,get_cnf_def,parse_cnf_def]>>
  reverse (Cases_on`inFS_fname fs f1`)>>fs[SUM_TYPE_def,parse_vcnf_toks]
  >- (xmatch>>err_tac all_tac)>>
  Cases_on`parse_cnf_toks (MAP toks (all_lines_file fs f1))`>>
  fs[SUM_TYPE_def]
  >- (xmatch>>err_tac all_tac)>>
  qmatch_asmsub_rename_tac`parse_cnf_toks _ = SOME res`>>
  PairCases_on`res`>>
  gvs[SUM_TYPE_def,PAIR_TYPE_def]>>
  rename1`parse_cnf_toks _ = SOME (mv,ncl,cfml)`>>
  xmatch>>
  rpt xlet_autop>>
  assume_tac (fetch "-" "drop_taut_v_thm")>>
  xlet_autop>>
  xlet`POSTv v.
    STDIO fs *
    SEP_EXISTS res.
      &(SUM_TYPE STRING_TYPE BOOL res v ∧
        (res = INR T ⇒ unsatisfiable_cnf (set cfml)))`
  >- (
    xapp>>
    qexistsl_tac [`emp`,`MAP drop_taut (conv_cfml cfml)`,`fs`]>>
    xsimpl>>
    `EVERY (EVERY nz_lit) cfml` by metis_tac[parse_cnf_toks_nz_lit]>>
    qexistsl_tac [`f2`,`mv + 1`,`2 * ncl`]>>
    rpt conj_tac
    >- simp[drop_taut_nz]
    >- fs[FILENAME_def,validArg_def]
    >- (
      irule drop_taut_bnd>>
      simp[]>>
      drule parse_cnf_toks_bound>>
      rw[EVERY_MEM]>>res_tac>>simp[])
    >- simp[]
    >- simp[]>>
    rpt strip_tac>>
    rename1`SUM_TYPE STRING_TYPE BOOL r rv`>>
    qexists_tac`r`>>
    rw[]>>
    irule drop_taut_sound>>
    gvs[])>>
  namedCases_on`res` ["err","b"]>>fs[SUM_TYPE_def]
  >- (
    xmatch>>err_tac no_out)>>
  xmatch>>
  xif
  >- (
    xapp_spec print_spec>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
    rw[]>>
    qexistsl_tac [`«s VERIFIED UNSAT\n»`,`«»`]>>
    simp[STD_streams_stderr,add_stdo_nil]>>
    xsimpl)>>
  xapp_spec output_stderr_spec>>xsimpl>>
  qexists_tac`emp`>>qexists_tac`fs`>>xsimpl>>
  rw[]>>
  qexistsl_tac [`«»`,`«c empty clause not derived at end of proof\n»`]>>
  fs[STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
  xsimpl
QED

Theorem check_unsat_stdin_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  hasFreeFD fs ∧
  stdin_content fs = SOME text
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_stdin"(get_ml_prog_state()))
    [f1v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS k out err.
      STDIO (add_stdout (add_stderr (forwardFD fs 0 k) err) out) *
      &(check_unsat_2_sem fs f1 out))
Proof
  rw[]>>
  xcf "check_unsat_stdin" (get_ml_prog_state ())>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def]>>xpull)>>
  xlet_autop>>
  simp[check_unsat_2_sem_def,get_cnf_def,parse_cnf_def]>>
  reverse (Cases_on`inFS_fname fs f1`)>>fs[SUM_TYPE_def,parse_vcnf_toks]
  >- (xmatch>>err_tac (qexists_tac`0`>>simp[forwardFD_0]))>>
  Cases_on`parse_cnf_toks (MAP toks (all_lines_file fs f1))`>>
  fs[SUM_TYPE_def]
  >- (xmatch>>err_tac (qexists_tac`0`>>simp[forwardFD_0]))>>
  qmatch_asmsub_rename_tac`parse_cnf_toks _ = SOME res`>>
  PairCases_on`res`>>
  gvs[SUM_TYPE_def,PAIR_TYPE_def]>>
  rename1`parse_cnf_toks _ = SOME (mv,ncl,cfml)`>>
  xmatch>>
  rpt xlet_autop>>
  assume_tac (fetch "-" "drop_taut_v_thm")>>
  xlet_autop>>
  xlet`POSTv v.
    SEP_EXISTS k res.
      STDIO (forwardFD fs 0 k) *
      &(SUM_TYPE STRING_TYPE BOOL res v ∧
        (res = INR T ⇒ unsatisfiable_cnf (set cfml)))`
  >- (
    xapp_spec check_unsat_stdin'_spec>>
    `EVERY (EVERY nz_lit) cfml` by metis_tac[parse_cnf_toks_nz_lit]>>
    qexistsl_tac [`emp`,`MAP drop_taut (conv_cfml cfml)`,`fs`]>>
    rpt conj_tac
    >- simp[]
    >- simp[drop_taut_nz]
    >- (
      qexists_tac`mv + 1`>>
      simp[]>>
      irule drop_taut_bnd>>
      simp[]>>
      drule parse_cnf_toks_bound>>
      rw[EVERY_MEM]>>res_tac>>simp[])
    >- metis_tac[]
    >- simp[]
    >- xsimpl>>
    xsimpl>>
    rpt strip_tac>>
    qmatch_goalsub_rename_tac`STDIO (forwardFD fs 0 kk) ==>> _`>>
    qexists_tac`kk`>>
    rename1`SUM_TYPE STRING_TYPE BOOL r rv`>>
    qexists_tac`r`>>
    xsimpl>>
    rw[]>>
    irule drop_taut_sound>>
    gvs[])>>
  `STD_streams (forwardFD fs 0 k)` by simp[STD_streams_forwardFD]>>
  namedCases_on`res` ["err","b"]>>fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexistsl_tac[`emp`,`forwardFD fs 0 k`]>>xsimpl>>
    rw[]>>
    qexistsl_tac[`k`,`«»`,`err`]>>
    fs[STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
    xsimpl)>>
  xmatch>>
  xif
  >- (
    xapp_spec print_spec>>xsimpl>>
    qexistsl_tac[`emp`,`forwardFD fs 0 k`]>>xsimpl>>
    rw[]>>
    qexistsl_tac[`k`,`«s VERIFIED UNSAT\n»`,`«»`]>>
    simp[STD_streams_stderr,add_stdo_nil]>>
    xsimpl)>>
  xapp_spec output_stderr_spec>>xsimpl>>
  qexistsl_tac[`emp`,`forwardFD fs 0 k`]>>xsimpl>>
  rw[]>>
  qexistsl_tac[`k`,`«»`,`«c empty clause not derived at end of proof\n»`]>>
  fs[STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
  xsimpl
QED

Definition check_unsat_sem_def:
  check_unsat_sem fs cl out ⇔
  case split_flags F (TL cl) of
    (SOME T, [f1]) => check_unsat_1_sem fs f1 out
  | (SOME F, [f1]) => check_unsat_2_sem fs f1 out
  | (SOME F, [f1; f2]) => check_unsat_2_sem fs f1 out
  | _ => out = «»
End

(* The command lines on which the proof is read from stdin *)
Definition reads_stdin_def:
  reads_stdin cl ⇔ ∃f1. split_flags F (TL cl) = (SOME F, [f1])
End

Theorem BOOL_T_F_eq[local]:
  (BOOL T v ⇔ v = Conv (SOME (TypeStamp «True» 0)) []) ∧
  (BOOL F v ⇔ v = Conv (SOME (TypeStamp «False» 0)) [])
Proof
  simp[BOOL_def,semanticPrimitivesTheory.Boolv_def,
    semanticPrimitivesTheory.bool_type_num_def]
QED

Theorem check_unsat_spec:
   hasFreeFD fs ∧
   (reads_stdin cl ⇒ stdin_content fs ≠ NONE)
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"check_unsat"(get_ml_prog_state()))
     [Conv NONE []]
     (COMMANDLINE cl * STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv *
     COMMANDLINE cl *
     SEP_EXISTS k out err.
       STDIO (add_stdout (add_stderr (forwardFD fs 0 k) err) out) *
       &(check_unsat_sem fs cl out))
Proof
  rw[check_unsat_sem_def]>>
  xcf"check_unsat"(get_ml_prog_state())>>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def]>>xpull)>>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def]>>xpull)>>
  rpt xlet_autop>>
  qmatch_asmsub_rename_tac`bv = Conv (SOME (TypeStamp «False» 0)) []`>>
  `BOOL F bv` by simp[BOOL_T_F_eq]>>
  xlet`POSTv v. COMMANDLINE cl * STDIO fs *
    &PAIR_TYPE (OPTION_TYPE BOOL) (LIST_TYPE STRING_TYPE)
      (split_flags F (TL cl)) v`
  >- (
    xapp>>
    qexistsl_tac [`COMMANDLINE cl * STDIO fs`,`TL cl`,`F`]>>
    xsimpl)>>
  Cases_on`split_flags F (TL cl)`>>
  rename1`split_flags F (TL cl) = (fl,ps)`>>
  `∀x. MEM x ps ⇒ validArg x` by (
    rw[]>>
    drule_all split_flags_MEM>>
    Cases_on`cl`>>gvs[wfcl_def,EVERY_MEM])>>
  `ps = [] ∨ (∃f1. ps = [f1]) ∨ (∃f1 f2. ps = [f1; f2]) ∨
   (∃f1 f2 f3 rest. ps = f1::f2::f3::rest)` by (
    namedCases_on`ps` ["","f1 t1"]>>simp[]>>
    namedCases_on`t1` ["","f2 t2"]>>simp[]>>
    namedCases_on`t2` ["","f3 t3"]>>simp[])>>
  `fl = NONE ∨ fl = SOME T ∨ fl = SOME F` by (
    namedCases_on`fl` ["","d"]>>simp[])>>
  gvs[PAIR_TYPE_def,OPTION_TYPE_def,LIST_TYPE_def,BOOL_T_F_eq]>>
  xmatch
  >~ [`check_unsat_1_sem`]
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac [`COMMANDLINE cl`,`fs`,`f1`]>>
    xsimpl>>
    rw[]>>
    first_x_assum (irule_at Any)>>
    qmatch_goalsub_rename_tac`STDIO (add_stdout (add_stderr fs err) _) ==>> _`>>
    qexistsl_tac [`err`,`0`]>>
    simp[forwardFD_0]>>
    xsimpl)
  >~ [`split_flags _ _ = (SOME _, [_])`]
  >- (
    `reads_stdin cl` by simp[reads_stdin_def]>>
    `∃text. stdin_content fs = SOME text` by (Cases_on`stdin_content fs`>>gvs[])>>
    xapp>>
    xsimpl>>
    qexistsl_tac [`COMMANDLINE cl`,`fs`,`f1`,`text`]>>
    xsimpl>>
    rw[]>>
    first_x_assum (irule_at Any)>>
    qmatch_goalsub_rename_tac
      `STDIO (add_stdout (add_stderr (forwardFD fs 0 kk) ee) _) ==>> _`>>
    qexistsl_tac [`ee`,`kk`]>>
    xsimpl)
  >~ [`check_unsat_2_sem`]
  >- (
    xapp>>
    xsimpl>>
    qexistsl_tac [`COMMANDLINE cl`,`fs`,`f1`,`f2`]>>
    xsimpl>>
    rw[]>>
    first_x_assum (irule_at Any)>>
    qmatch_goalsub_rename_tac`STDIO (add_stdout (add_stderr fs err) _) ==>> _`>>
    qexistsl_tac [`err`,`0`]>>
    simp[forwardFD_0]>>
    xsimpl)>>
  assume_tac (theorem "usage_string_v_thm")>>
  xlet_autop>>
  xapp_spec output_stderr_spec>>xsimpl>>
  qexistsl_tac [`COMMANDLINE cl`,`mk_usage_string usage_string`,`fs`]>>
  xsimpl>>
  rw[]>>
  qexistsl_tac [`0`,`mk_usage_string usage_string`]>>
  fs[forwardFD_0,STD_streams_add_stderr,STD_streams_stdout,add_stdo_nil]>>
  xsimpl
QED

Theorem check_unsat_whole_prog_spec2:
   hasFreeFD fs ∧
   (reads_stdin cl ⇒ stdin_content fs ≠ NONE) ⇒
   whole_prog_spec2 check_unsat_v cl fs NONE
     (λfs'. ∃k out err.
        fs' = add_stdout (add_stderr (forwardFD fs 0 k) err) out ∧
        check_unsat_sem fs cl out)
Proof
  rw[basis_ffiTheory.whole_prog_spec2_def]>>
  match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH check_unsat_spec))))>>
  xsimpl>>
  rw[PULL_EXISTS]>>
  qmatch_goalsub_rename_tac
    `STDIO (add_stdout (add_stderr (forwardFD fs 0 kk) ee) oo)`>>
  qexistsl_tac [`add_stdout (add_stderr (forwardFD fs 0 kk) ee) oo`,
    `kk`,`oo`,`ee`]>>
  xsimpl>>
  simp[GSYM add_stdo_with_numchars,GSYM forwardFD_numchars,
    with_same_numchars]
QED

Theorem check_unsat_semantics =
  prove_sem_thm "check_unsat"
                "check_unsat_prog"
                check_unsat_whole_prog_spec2;
