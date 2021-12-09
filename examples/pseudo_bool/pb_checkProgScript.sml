(*
  This produces an executable program for pb_check
*)
open preamble basis pb_checkTheory;

val _ = new_theory "pb_checkProg"

val _ = translation_extends"basisProg";

Definition noparse_string_def:
  noparse_string f s = concat[strlit"c Input file: ";f;strlit" unable to parse in format: "; s;strlit"\n"]
End

val r = translate noparse_string_def;

Definition usage_string_def:
  usage_string = strlit "Usage:  cake_pb <OPB format formula file> <Proof file>\n"
End

val r = translate usage_string_def;

Definition notfound_string_def:
  notfound_string f = concat[strlit"c Input file: ";f;strlit" no such file or directory\n"]
End

val r = translate notfound_string_def;

(* translation for .pbf parsing *)
val r = translate blanks_def;
val r = translate tokenize_def;
val r = translate nocomment_line_def;

val r = translate parse_lit_def;

val parse_lit_side_def = definition"parse_lit_side_def";
val parse_lit_side = Q.prove(
  `∀x. parse_lit_side x <=> T`,
  rw[parse_lit_side_def])
  |> update_precondition;

val r = translate parse_constraint_LHS_def;
val r = translate strip_terminator_def;

val strip_terminator_side_def = definition"strip_terminator_side_def";
val strip_terminator_side = Q.prove(
  `∀x. strip_terminator_side x <=> T`,
  rw[strip_terminator_side_def])
  |> update_precondition;

val r = translate add_terms_denorm_def;
val r = translate pb_constraintTheory.get_var_def;
val r = translate term_eq_def;
val r = translate merge_adjacent_def;
val r = translate pb_constraintTheory.negate_def;
val r = translate normalize_def;

val normalize_side_def = theorem"normalize_side_def";
val normalize_side = Q.prove(
  `∀x y z. normalize_side x y z <=> T`,
  Induct>>rw[Once normalize_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate term_le_def;
val r = translate normalize_PBC_def;

val normalize_pbc_side = Q.prove(
  `∀x y. normalize_pbc_side x y <=> T`,
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_constraint_def;
val r = translate parse_constraints_def;

val r = translate parse_pbf_toks_def;

val parse_pbf_full = (append_prog o process_topdecs) `
  fun parse_pbf_full f =
  (case TextIO.b_inputAllTokensFrom f blanks tokenize of
    None => Inl (notfound_string f)
  | Some lines =>
  (case parse_pbf_toks lines of
    None => Inl (noparse_string f "OPB")
  | Some x => Inr x))`

val r = translate tokenize_num_def;
val r = translate strip_numbers_def;
val r = translate parse_polish_def;
val r = translate parse_pbpstep_def;
val r = translate parse_pbpsteps_def;
val r = translate parse_pbp_toks_def;

val parse_pbp_full = (append_prog o process_topdecs) `
  fun parse_pbp_full f =
  (case TextIO.b_inputAllTokensFrom f blanks tokenize_num of
    None => Inl (notfound_string f)
  | Some lines =>
  (case parse_pbp_toks lines of
    None => Inl (noparse_string f "PBP")
  | Some x => Inr x))`

val r = translate insert_def;
val r = translate lookup_def;
val r = translate mk_BN_def;
val r = translate mk_BS_def;
val r = translate delete_def;
val r = translate build_fml_def;

val r = translate (lslack_def |> SIMP_RULE std_ss [MEMBER_INTRO]);
val r = translate (check_contradiction_def |> SIMP_RULE std_ss[LET_DEF]);

(* add *)
val r = translate pb_constraintTheory.term_lt_def;
val r = translate pb_constraintTheory.add_terms_def;
val r = translate pb_constraintTheory.add_lists_def;
val r = translate pb_constraintTheory.add_def;

val r = translate pb_constraintTheory.multiply_def;
val r = translate pb_constraintTheory.div_ceiling_def;
val r = translate pb_constraintTheory.divide_def;
val r = translate pb_constraintTheory.saturate_def;
val r = translate pb_constraintTheory.weaken_aux_def;
val r = translate pb_constraintTheory.weaken_def;

val divide_side = Q.prove(
  `∀x y. divide_side x y ⇔ y ≠ 0`,
  Cases>>
  EVAL_TAC>>
  rw[EQ_IMP_THM]) |> update_precondition

val r = translate check_polish_def;

val r = translate FOLDL

val r = translate check_pbpstep_def;
val r = translate check_pbpsteps_def;

Definition result_string_def:
  (result_string Fail = INL (strlit "Proof checking failed\n")) ∧
  (result_string (Cont _ _) = INL (strlit "Proof checking succeeded but derive contradiction\n")) ∧
  (result_string Unsat = INR (strlit "Verified\n"))
End

val r = translate result_string_def;

Definition check_pbp_def:
  check_pbp pbf pbp =
    let (id,fml) = build_fml 1 pbf LN in
    result_string (check_pbpsteps pbp id fml)
End

val r = translate check_pbp_def;

val check_unsat_2 = (append_prog o process_topdecs) `
  fun check_unsat_2 f1 f2 =
  case parse_pbf_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr fml =>
  (case parse_pbp_full f2 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr pf =>
    (case check_pbp fml pf of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr succ => TextIO.print succ)
  )`

val check_unsat = (append_prog o process_topdecs) `
  fun check_unsat u =
  case CommandLine.arguments () of
    [f1,f2] => check_unsat_2 f1 f2
  | _ => TextIO.output TextIO.stdErr usage_string`

(* TODO: Dummy spec *)
val check_unsat_sem_def = Define`
  check_unsat_sem cl fs err = fs`

Theorem check_unsat_spec:
   hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"check_unsat"(get_ml_prog_state()))
     [Conv NONE []]
     (COMMANDLINE cl * STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv *
     COMMANDLINE cl * SEP_EXISTS err. STDIO (check_unsat_sem cl fs err))
Proof
  cheat
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
  \\ rw[check_unsat_sem_def]
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