(*
  This builds the cake_scpog proof checker
*)
Theory scpog_arrayFullProg
Libs
  preamble basis
Ancestors
  UnsafeProof cnf_scpogSem scpog scpog_list lpr_parsing
  scpog_parsing scpog_arrayProg basis_ffi

val _ = diminish_srw_ss ["ABBREV"]

val _ = translation_extends"scpog_arrayProg";

val res = translate opt_union_def;
val res = translate parse_show_def;

val _ = translate parse_clause_aux_def;
val _ = translate parse_clause_def;
val _ = translate nocomment_line_def;
val res = translate parse_one_def;
val res = translate parse_ext_dimacs_body_def;

val _ = translate parse_header_line_def;

val parse_header_line_side = Q.prove(`
   ∀x. parse_header_line_side x= T`,
  rw[definition"parse_header_line_side_def"]>>
  intLib.ARITH_TAC)
  |> update_precondition;

val res = translate parse_ext_header_def;

val res = translate lrnext_def;
val res = translate foldi_def;
val res = translate toAList_def;
val res = translate opt_bound_vs_def;

val res = translate parse_ext_dimacs_toks_def;

Definition format_dimacs_failure_def:
  format_dimacs_failure (lno:num) s =
  strlit "c DIMACS parse failed at line: " ^ toString lno ^ strlit ". Reason: " ^ s ^ strlit"\n"
End

val _ = translate format_dimacs_failure_def;

val inputAllTokensFile_specialize =
  inputAllTokensFile_spec
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_v_thm,tokenize_v_thm,blanks_def];

(* parse_dimacs_toks with simple wrapper *)
Quote add_cakeml:
  fun parse_dimacs_full fname =
  case TextIO.inputAllTokensFile #"\n" fname blanks tokenize of
    None => Inl (notfound_string fname)
  | Some ls =>
    (case parse_ext_dimacs_toks ls of
      None => Inl (noparse_string fname "DIMACS")
    | Some res => Inr res)
End

Definition get_prob_def:
  get_prob fs f =
  if inFS_fname fs f then
    parse_ext_dimacs_toks (MAP toks (all_lines_file fs f))
  else NONE
End

Theorem toks_eq:
  toks = MAP tokenize o tokens blanks
Proof
  rw[FUN_EQ_THM,toks_def]
QED

Theorem parse_dimacs_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_dimacs_full"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. (SUM_TYPE STRING_TYPE
      (PAIR_TYPE NUM (PAIR_TYPE NUM (PAIR_TYPE (OPTION_TYPE (SPTREE_SPT_TYPE UNIT_TYPE)) (LIST_TYPE (LIST_TYPE INT)))))
    (case get_prob fs f of
      NONE => INL err
    | SOME x => INR x)) v) * STDIO fs)
Proof
  rw[]>>
  xcf"parse_dimacs_full"(get_ml_prog_state()) >>
  fs[validArg_def,get_prob_def]>>
  xlet`(POSTv sv.
          &OPTION_TYPE (LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
            (if inFS_fname fs f then
               SOME (MAP (MAP tokenize ∘ tokens blanks) (all_lines_file_gen #"\n" fs f))
             else NONE) sv * STDIO fs)`
  >- (
    xapp_spec inputAllTokensFile_specialize>>
    xsimpl>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    gvs[FILENAME_def]>>
    first_x_assum (irule_at Any)>>
    xsimpl)>>
  gvs[OPTION_TYPE_SPLIT]>>xmatch
  >- (
    xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def]>>
    metis_tac[])>>
  xlet_autop>>
  gvs[OPTION_TYPE_SPLIT,get_prob_def,toks_eq]>>
  xmatch
  >- (
    xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def]>>
    metis_tac[])>>
  xcon>>xsimpl>>
  simp[SUM_TYPE_def]
QED

val usage_string = ‘

Usage:  cake_scpog <DIMACS formula file> <SCPOG file>

Run SCPOG proof checking

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

Definition mk_pc_def:
  mk_pc nv nc vs =
    <| D := vs ; nv := nv ; nc := nc|>
End

val r = translate mk_pc_def;
val r = translate init_sc_def;

Quote add_cakeml:
  fun fill_arr arr i ls =
    case ls of [] => arr
    | (v::vs) =>
      fill_arr (Array.updateResize arr None i (Some (v,False))) (i+1) vs
End

Theorem fill_arr_spec:
  ∀ls lsv arrv arrls arrlsv i iv.
  NUM i iv ∧
  LIST_TYPE a ls lsv ∧
  LIST_REL (OPTION_TYPE (PAIR_TYPE a BOOL)) arrls arrlsv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"fill_arr"(get_ml_prog_state()))
  [arrv; iv; lsv]
  (ARRAY arrv arrlsv)
  (POSTv resv.
  SEP_EXISTS arrlsv'. ARRAY resv arrlsv' *
    & LIST_REL (OPTION_TYPE (PAIR_TYPE a BOOL))
    (FOLDL (λacc (i,v).  update_resize acc NONE (SOME (v,F)) i) arrls (enumerate i ls)) arrlsv')
Proof
  Induct>>rw[]>>
  xcf "fill_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,miscTheory.enumerate_def]>>
  xmatch
  >- (xvar>>xsimpl)>>
  rpt xlet_autop >>
  xlet_auto>>
  xapp>>xsimpl>>
  irule LIST_REL_update_resize>>
  simp[OPTION_TYPE_def,PAIR_TYPE_def]>>
  EVAL_TAC
QED

Definition print_result_def:
  (print_result (INL ()) = strlit "s VERIFIED UNSAT\n") ∧
  (print_result (INR (r,scp)) =
    strlit "s VERIFIED CPOG REPRESENTATION\n")
End

val r = translate print_result_def;

Quote add_cakeml:
  fun check_unsat_2 f1 f2 =
  case parse_dimacs_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr (mv,(ncx,(vs,fml))) =>
  let val pc = mk_pc mv ncx vs
      val one = 1
      val arr = Array.array (2*ncx) None
      val arr = fill_arr arr one fml
      val bnd = 2*mv + 3
  in
    case check_unsat' pc arr init_sc f2 bnd of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr res =>
      TextIO.print (print_result res)
  end
End

Quote add_cakeml:
  fun main u =
  case CommandLine.arguments () of
    [f1,f2] => check_unsat_2 f1 f2
  | _ => TextIO.output TextIO.stdErr usage_string
End

(* We verify each argument type separately *)
val inputAllTokensFile_spec_specialize =
  inputAllTokensFile_spec
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> REWRITE_RULE [blanks_v_thm,tokenize_v_thm,blanks_def] ;

Definition get_scpog_def:
  get_scpog fs f =
  if inFS_fname fs f then
    parse_scpsteps (all_lines_file fs f)
  else NONE
End

Definition check_unsat_2_sem_def:
  check_unsat_2_sem fs f1 f2 err =
  if inFS_fname fs f1 then
    case get_prob fs f1 of
      NONE => add_stderr fs err
    | SOME (mv,ncl,vars,fml) =>
      (case get_scpog fs f2 of
        NONE => add_stderr fs err
      | SOME scpsteps =>
      let pc = mk_pc mv ncl vars in
      let fmlls = enumerate 1 fml in
      let base = REPLICATE (2*ncl) NONE in
      let cupd = FOLDL (λacc (i,v).
          update_resize acc NONE (SOME (v,F)) i) base fmlls in
      let bnd = 2*mv+3 in
        case check_scp_final_list scpsteps pc cupd init_sc (REPLICATE bnd w8z) of
          NONE => add_stderr fs err
        | SOME res =>
          add_stdout fs (print_result res))
  else add_stderr fs err
End

val err_tac = xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>qexists_tac`err`>>xsimpl;

Theorem parse_ext_dimacs_body_props:
  ∀ss vs acc vs' fml.
  parse_ext_dimacs_body mv ss vs acc = SOME (vs',fml) ∧
  EVERY (λC. wf_clause C ∧ vars_clause C ⊆ count (mv + 1)) acc ⇒
  EVERY (λC. wf_clause C ∧ vars_clause C ⊆ count (mv + 1)) fml
Proof
  Induct>>rw[]>>
  gvs[EVERY_REVERSE,AllCaseEqs(),parse_ext_dimacs_body_def]>>
  first_x_assum irule>>
  last_x_assum (irule_at Any)>>
  gvs[parse_one_def,AllCaseEqs()]>>
  drule lpr_parsingTheory.parse_clause_bound>>
  drule lpr_parsingTheory.parse_clause_wf_clause>>
  rw[SUBSET_DEF,vars_clause_def,EVERY_MEM]>>
  gvs[lprTheory.wf_clause_def,wf_clause_def]>>
  first_x_assum drule>>
  simp[var_lit_def]
QED

Theorem parse_ext_dimacs_toks_props:
  parse_ext_dimacs_toks ls = SOME (mv,ncl,vs,fml) ⇒
  (∀D. vs = SOME D ⇒ domain D ⊆ count (mv + 1)) ∧
  LENGTH fml = ncl ∧
  EVERY wf_clause fml ∧
  EVERY (λC. vars_clause C ⊆ count (mv + 1)) fml
Proof
  rw[parse_ext_dimacs_toks_def]>>
  gvs[AllCaseEqs()]
  >- (
    gvs[opt_bound_vs_def,EVERY_MEM,FORALL_PROD,MEM_toAList,SUBSET_DEF,domain_lookup]>>
    rw[]>>first_x_assum drule>>
    simp[])>>
  drule parse_ext_dimacs_body_props>>
  simp[EVERY_MEM]
QED

Theorem bounded_fml_FOLDL_enumerate:
  EVERY wf_clause ls ∧
  EVERY (λC. vars_clause C ⊆ count (mv + 1)) ls ∧
  v > 2 * mv ⇒
  bounded_fml v
    (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,F)) i)
     (REPLICATE n NONE) (enumerate k ls))
Proof
  rw[bounded_fml_def]>>
  simp[Once EVERY_EL]>>rw[]>>
  `ALL_DISTINCT (MAP FST (enumerate k ls))` by
    metis_tac[ALL_DISTINCT_MAP_FST_enumerate]>>
  TOP_CASE_TAC>>simp[]>>
  drule FOLDL_update_resize_lookup>>
  disch_then drule>>
  disch_then (SUBST_ALL_TAC)>>
  TOP_CASE_TAC>>gvs[]>>
  drule ALOOKUP_MEM>>
  strip_tac>> drule MEM_enumerate_IMP>>
  fs[EVERY_MEM]>>
  strip_tac>>
  first_x_assum drule>>
  simp[vars_clause_def,SUBSET_DEF,PULL_EXISTS]>>rw[]>>
  gvs[wf_clause_def,var_lit_def]>>
  rpt (first_x_assum drule)>>
  rw[index_def]>>
  intLib.ARITH_TAC
QED

Theorem check_unsat_2_spec:
  STRING_TYPE f1 f1v ∧ validArg f1 ∧
  STRING_TYPE f2 f2v ∧ validArg f2 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_2"(get_ml_prog_state()))
    [f1v; f2v]
    (STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv *
    SEP_EXISTS err. STDIO (check_unsat_2_sem fs f1 f2 err))
Proof
  rw[]>>
  xcf "check_unsat_2" (get_ml_prog_state ())>>
  xlet_autop>>
  simp[check_unsat_2_sem_def]>>
  reverse TOP_CASE_TAC>>fs[]
  >- (
    gvs[get_prob_def,SUM_TYPE_def]>>xmatch>>
    err_tac)>>
  gvs[get_prob_def,SUM_TYPE_def]>>
  TOP_CASE_TAC>> fs[SUM_TYPE_def]
  >- (xmatch>> err_tac)>>
  PairCases_on`x`>>fs[SUM_TYPE_def,PAIR_TYPE_def]>>
  xmatch>>
  rename1`_ = SOME (nv,nc,vars,fml)`>>
  xlet_autop>>
  xlet`POSTv v. &NUM 1 v * STDIO fs` >- (xlit>>xsimpl)>>
  rw[]>>
  (drule_at (Pos (hd o tl))) fill_arr_spec>>
  (* help instantiate fill_arr_spec *)
  `LIST_REL (OPTION_TYPE (PAIR_TYPE (LIST_TYPE INT) BOOL)) (REPLICATE (2 * nc) NONE)
        (REPLICATE (2 * nc) (Conv (SOME (TypeStamp "None" 2)) []))` by
    simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
  qpat_x_assum`NUM 1 _` assume_tac>>
  disch_then drule>>
  disch_then drule>>
  rw[]>>rpt xlet_autop>>
  simp[check_scp_final_list_def]>>
  qmatch_goalsub_abbrev_tac`check_scpsteps_list _ a b c d`>>
  xlet`(POSTv v.
    STDIO fs *
    SEP_EXISTS err.
      &(SUM_TYPE STRING_TYPE res_TYPE)
      (case get_scpog fs f2 of
        NONE => INL err
      | SOME scpsteps =>
         (case check_scp_final_list scpsteps a b c d of
           NONE => INL err
         | SOME res => INR res)
      ) v)`
  >- (
    xapp_spec (GEN_ALL check_unsat'_spec)>>
    xsimpl>>
    asm_exists_tac>>simp[]>>
    fs[FILENAME_def,validArg_def]>>
    asm_exists_tac>>simp[]>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    qexists_tac`init_sc`>>
    xsimpl>>
    rw[]
    >-
      gvs[Abbr`c`,fetch "-""init_sc_v_thm"]
    >- (
      gvs[Abbr`b`]>>
      irule  bounded_fml_FOLDL_enumerate>>
      drule_all parse_ext_dimacs_toks_props>>
      rw[]>>
      first_x_assum (irule_at Any)>>
      simp[])
    >- (gvs[get_scpog_def]>> metis_tac[])
    >- (gvs[get_scpog_def]>> metis_tac[]))>>
  TOP_CASE_TAC>>simp[]
  >- (fs[SUM_TYPE_def]>>xmatch>>err_tac)>>
  gvs[check_scp_final_list_def]>>
  Cases_on`check_scpsteps_list x a b c d`>>fs[SUM_TYPE_def]
  >- (
    xmatch>>
    err_tac)>>
  PairCases_on`x'`>>fs[]>>
  rename1`check_final_list a xx yy`>>
  Cases_on`check_final_list a xx yy`>>fs[SUM_TYPE_def]>>
  xmatch
  >- err_tac>>
  xlet_autop>>
  xapp_spec print_spec >> xsimpl
  \\ qexists_tac`emp`
  \\ asm_exists_tac
  \\ qexists_tac`fs`>>xsimpl
QED

Definition main_sem_def:
  main_sem cl fs err =
  case TL cl of
  | [f1;f2] => check_unsat_2_sem fs f1 f2 err
  | _ => add_stderr fs err
End

Theorem main_spec:
   hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"main"(get_ml_prog_state()))
     [Conv NONE []]
     (COMMANDLINE cl * STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv *
     COMMANDLINE cl * SEP_EXISTS err. STDIO (main_sem cl fs err))
Proof
  rw[]>>
  xcf"main"(get_ml_prog_state())>>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)>>
  rpt xlet_autop >>
  Cases_on `cl` >- fs[wfcl_def] >>
  simp[main_sem_def]>>
  every_case_tac>>fs[LIST_TYPE_def]>>xmatch>>
  qmatch_asmsub_abbrev_tac`wfcl cl`
  >- (
    xapp_spec output_stderr_spec \\ xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `usage_string` >> simp [theorem "usage_string_v_thm"] >>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>qexists_tac`usage_string`>>xsimpl)
  >- (
    xapp_spec output_stderr_spec \\ xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `usage_string` >> simp [theorem "usage_string_v_thm"] >>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>qexists_tac`usage_string`>>xsimpl)
  >- (
    xapp>>xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    fs[wfcl_def,Abbr`cl`]>>
    qexists_tac`fs`>>
    qexists_tac`h''`>>
    qexists_tac`h'`>>
    xsimpl>>rw[]>>
    qexists_tac`x`>>xsimpl)
  >- (
    xapp_spec output_stderr_spec \\ xsimpl>>
    qexists_tac`COMMANDLINE cl`>>xsimpl>>
    qexists_tac `usage_string` >> simp [theorem "usage_string_v_thm"] >>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>qexists_tac`usage_string`>>xsimpl)
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
  \\ simp[main_sem_def,check_unsat_2_sem_def]
  \\ every_case_tac
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
