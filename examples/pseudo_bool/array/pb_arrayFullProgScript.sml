(*
  Add parsing, etc. to pb_arrayProg
*)
open preamble basis pb_checkTheory pb_arrayProgTheory;

val _ = new_theory "pb_arrayFullProg"

val _ = translation_extends"pb_arrayProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

Definition noparse_string_def:
  noparse_string f s = concat[strlit"c Input file: ";f;strlit" unable to parse in format: "; s;strlit"\n"]
End

val r = translate noparse_string_def;

Definition usage_string_def:
  usage_string = strlit "Usage: cake_pb <OPB format formula file> <Proof file>\n"
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

val nocomment_line_side_def = definition"nocomment_line_side_def";
val nocomment_line_side = Q.prove(
  `∀x. nocomment_line_side x <=> T`,
  rw[nocomment_line_side_def])
  |> update_precondition;

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

val r = translate pb_preconstraintTheory.pbc_ge_def;
val r = translate pb_constraintTheory.get_var_def;
val r = translate pb_constraintTheory.compact_lhs_def;
val r = translate pb_constraintTheory.term_le_def;
val r = translate pb_constraintTheory.negate_def;
val r = translate pb_constraintTheory.mk_coeff_def;
val r = translate pb_constraintTheory.normalize_lhs_def;

(*
val normalize_lhs_side_def = theorem "normalize_lhs_side_def";
val normalize_lhs_side = Q.prove(
  `∀x y z. normalize_lhs_side x y z <=> T`,
  Induct>>rw[Once normalize_lhs_side_def]>>
  intLib.ARITH_TAC)
  |> update_precondition;
 *)

val r = translate pb_constraintTheory.pbc_to_npbc_def;

val pbc_to_npbc_side = Q.prove(
  `∀x. pbc_to_npbc_side x <=> T`,
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate pb_constraintTheory.normalize_def;

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

val blanks_v_thm = theorem "blanks_v_thm";
val tokenize_v_thm = theorem "tokenize_v_thm";

val b_inputAllTokensFrom_spec_specialize =
  b_inputAllTokensFrom_spec
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> REWRITE_RULE [blanks_v_thm,tokenize_v_thm,blanks_def] ;

Theorem parse_pbf_full_spec:
  STRING_TYPE f fv ∧
  validArg f ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"parse_pbf_full"(get_ml_prog_state()))
    [fv]
    (STDIO fs)
    (POSTv v.
    & (∃err. (SUM_TYPE STRING_TYPE (LIST_TYPE PB_PRECONSTRAINT_PBC_TYPE)
    (if inFS_fname fs f then
    (case parse_pbf_toks (MAP toks (all_lines fs f)) of
      NONE => INL err
    | SOME x => INR x)
    else INL err) v)) * STDIO fs)
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
    fs[FILENAME_def,validArg_def])>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    xlet_autop>>
    `toks = (MAP tokenize ∘ tokens blanks)` by
      metis_tac[toks_def,ETA_AX,o_DEF]>>
    rw[]>> TOP_CASE_TAC>>
    fs[OPTION_TYPE_def]
    >- (
      xmatch >>
      xlet_autop>>
      xcon>>xsimpl>>
      simp[SUM_TYPE_def]>>metis_tac[])>>
    xmatch>>xcon>>
    xsimpl>>
    simp[SUM_TYPE_def])
  >>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def]>>metis_tac[]
QED

val r = translate strip_numbers_def;

val strip_numbers_side_def = theorem "strip_numbers_side_def";
val strip_numbers_side = Q.prove(
  `∀x y. strip_numbers_side x y <=> T`,
  Induct>>rw[Once strip_numbers_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_cutting_def;

val parse_cutting_side_def = theorem "parse_cutting_side_def";
val parse_cutting_side = Q.prove(
  `∀x y. parse_cutting_side x y <=> T`,
  Induct>>rw[Once parse_cutting_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_var_def;

val r = translate insert_def;
val r = translate parse_subst_def;

val r = translate parse_constraint_npbc_def;
val r = translate parse_red_header_def;

val r = translate parse_pbpstep_def;

val parse_pbpstep_side_def = fetch "-" "parse_pbpstep_side_def";
val parse_pbpstep_side = Q.prove(
  `∀x. parse_pbpstep_side x <=> T`,
  rw[Once parse_pbpstep_side_def]>>fs[]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_pbpsteps_aux_def;

val r = translate parse_subgoal_num_def;

val parse_subgoal_num_side_def = fetch "-" "parse_subgoal_num_side_def";
val parse_subgoal_num_side = Q.prove(
  `∀x. parse_subgoal_num_side x <=> T`,
  rw[Once parse_subgoal_num_side_def]>>fs[]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_redundancy_header_def;

val r = translate mk_acc_def;
val r = translate check_head_def;

open mlintTheory;

(* TODO: Mostly copied from mlintTheory *)
val result = translate fromChar_unsafe_def;

val fromChars_range_unsafe_tail_def = Define`
  fromChars_range_unsafe_tail l 0       str mul acc = acc ∧
  fromChars_range_unsafe_tail l (SUC n) str mul acc =
    fromChars_range_unsafe_tail l n str (mul * 10)  (acc + fromChar_unsafe (strsub str (l + n)) * mul)`;

Theorem fromChars_range_unsafe_tail_eq:
  ∀n l s mul acc.
  fromChars_range_unsafe_tail l n s mul acc = (fromChars_range_unsafe l n s) * mul + acc
Proof
  Induct>>rw[fromChars_range_unsafe_tail_def,fromChars_range_unsafe_def]
QED

Theorem fromChars_range_unsafe_alt:
  fromChars_range_unsafe l n s = fromChars_range_unsafe_tail l n s 1 0
Proof
  rw[fromChars_range_unsafe_tail_eq]
QED

val result = translate fromChars_range_unsafe_tail_def;
val result = translate fromChars_range_unsafe_alt;

val res = translate_no_ind (mlintTheory.fromChars_unsafe_def
  |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]>>
  fs[padLen_DEC_eq,ADD1]
  )
  |> update_precondition;

val result = translate pb_checkTheory.fromString_unsafe_def;

val fromstring_unsafe_side_def = definition"fromstring_unsafe_side_def";
val fromchars_unsafe_side_def = theorem"fromchars_unsafe_side_def";
val fromchars_range_unsafe_tail_side_def = theorem"fromchars_range_unsafe_tail_side_def";
val fromchars_range_unsafe_side_def = fetch "-" "fromchars_range_unsafe_side_def";

Theorem fromchars_unsafe_side_thm:
   ∀n s. n ≤ LENGTH s ⇒ fromchars_unsafe_side n (strlit s)
Proof
  completeInduct_on`n` \\ rw[]
  \\ rw[Once fromchars_unsafe_side_def,fromchars_range_unsafe_side_def,fromchars_range_unsafe_tail_side_def]
QED

val fromString_unsafe_side = Q.prove(
  `∀x. fromstring_unsafe_side x = T`,
  Cases
  \\ rw[fromstring_unsafe_side_def]
  \\ Cases_on`s` \\ fs[mlstringTheory.substring_def]
  \\ simp_tac bool_ss [ONE,SEG_SUC_CONS,SEG_LENGTH_ID]
  \\ match_mp_tac fromchars_unsafe_side_thm
  \\ rw[]) |> update_precondition;

val _ = translate tokenize_fast_def;

val tokenize_fast_side = Q.prove(
  `∀x. tokenize_fast_side x = T`,
  EVAL_TAC >> fs[]) |> update_precondition;

val parse_pbpsteps = process_topdecs`
  fun parse_pbpsteps fd lno acc =
    case TextIO.b_inputLineTokens fd blanks tokenize_fast of
      None => raise Fail (format_failure lno "reached EOF while reading PBP steps")
    | Some s =>
    case parse_pbpstep s of None => (List.rev acc,(s,lno))
    | Some (Inl step) => parse_pbpsteps fd (lno+1) (step::acc)
    | Some (Inr (c,s)) =>
      case parse_redundancy fd (lno+1) [] of (pf,lno') =>
        case parse_pbpsteps_aux c s pf of None =>
          raise Fail (format_failure lno "Unable to format as contradiction or redundancy step")
        | Some step => parse_pbpsteps fd lno' (step::acc)
  and parse_redundancy fd lno acc =
    case parse_pbpsteps fd lno [] of (pf,(s,lno')) =>
    let val acc' = mk_acc pf acc in
      (case parse_redundancy_header s of
        None => raise Fail (format_failure lno' "failed to parse line")
      | Some (Inl u) => (List.rev acc', lno')
      | Some (Inr ind) =>
        case parse_pbpsteps fd lno' [] of (pf,(h,lno'')) =>
          (if check_head h then
              parse_redundancy fd lno'' ((Some ind,pf)::acc')
           else raise Fail (format_failure lno'' "redundancy subgoal not terminated by end") ))
    end
    ` |> append_prog;

val blanks_v_thm = theorem "blanks_v_thm";
val tokenize_fast_v_thm = theorem "tokenize_fast_v_thm";

val b_inputLineTokens_specialize =
  b_inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize_fast`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_fast_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_v_thm,tokenize_fast_v_thm,blanks_def] ;

Theorem parse_pbpsteps_spec:
  (!ss acc fd fdv lines lno lnov accv fs.
  NUM lno lnov ∧
  LIST_TYPE (PB_CHECK_PBPSTEP_TYPE) acc accv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_pbpsteps" (get_ml_prog_state()))
    [fdv; lnov; accv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (LIST_TYPE (PB_CHECK_PBPSTEP_TYPE))
              (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NUM) (acc',s,lno') v ∧
            parse_pbpsteps ss acc = SOME(acc',s,rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_pbpsteps ss acc = NONE))
      )) ∧
  (∀ss acc fd fdv lines lno lnov accv fs.
  NUM lno lnov ∧
  LIST_TYPE (PAIR_TYPE (OPTION_TYPE (SUM_TYPE NUM UNIT_TYPE))(LIST_TYPE (PB_CHECK_PBPSTEP_TYPE))) acc accv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_redundancy" (get_ml_prog_state()))
    [fdv; lnov; accv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (LIST_TYPE (PAIR_TYPE (OPTION_TYPE (SUM_TYPE NUM UNIT_TYPE)) (LIST_TYPE (PB_CHECK_PBPSTEP_TYPE))))
              NUM (acc',lno') v ∧
            parse_redundancy ss acc = SOME(acc',rest) ∧
            MAP toks_fast lines' = rest
            ) )
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_redundancy ss acc = NONE))
      ))
Proof
  ho_match_mp_tac parse_pbpsteps_ind>>
  rw[]
  >- (
    xcf "parse_pbpsteps" (get_ml_prog_state ())>>
    xlet ‘(POSTv v.
        SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES fd fdv [] (forwardFD fs fd k) *
            &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘emp’
      \\ qexists_tac ‘[]’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl) >>
    fs[OPTION_TYPE_def]>>
    xmatch >>
    xlet_autop>>
    xlet_autop>>
    xraise>>xsimpl>>
    simp[Once parse_pbpsteps_thm]>>
    simp[Once parse_pbpsteps_thm]>>
    qexists_tac`k`>>
    qexists_tac`[]`>>
    xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[])
  >-(
    xcfs ["parse_pbpsteps","parse_redundancy"] (get_ml_prog_state ())>>
    `?l ls. lines = l::ls` by
      (Cases_on`lines`>>fs[])>>
    rw[]>>
    fs[]>>
    xlet ‘(POSTv v.
            SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES fd fdv ls (forwardFD fs fd k) *
            & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks_fast l)) v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘emp’
      \\ qexists_tac ‘l::ls’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
      \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
      \\ simp[toks_fast_def]) >>
    fs[OPTION_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    simp[Once parse_pbpsteps_thm]>>
    TOP_CASE_TAC>>fs[OPTION_TYPE_def]
    >- ((* parse_pbpstep gives None *)
      xmatch>>
      xlet_autop>>
      xlet_autop>>
      xcon>>
      xsimpl>-
        (first_x_assum (irule_at Any)>>
        simp[PAIR_TYPE_def]>>
        first_x_assum (irule_at Any)>>
        qexists_tac`k`>>xsimpl)>>
      simp[Once parse_pbpsteps_def])>>
    (* parse_pbpstep gives Some *)
    TOP_CASE_TAC>>fs[SUM_TYPE_def]
    (* INL*)
    >- (
      xmatch>>
      xlet_autop>>
      xlet_autop>>
      xapp>>
      first_x_assum (irule_at Any)>>simp[]>>
      first_x_assum (irule_at Any)>>simp[LIST_TYPE_def]>>
      xsimpl>>
      qexists_tac`forwardFD fs fd k`>>xsimpl>>
      qexists_tac`fd`>>qexists_tac`emp`>>xsimpl>>
      rw[]
      >- (
        fs[PAIR_TYPE_def]>>
        asm_exists_tac>>simp[]>>
        simp[forwardFD_o]>>
        qexists_tac`k+x`>>xsimpl>>
        qexists_tac`x''`>>xsimpl)>>
      simp[forwardFD_o]>>
      qexists_tac`k+x`>>xsimpl>>
      qexists_tac`x''`>>xsimpl>>
      fs[Once parse_pbpsteps_thm])>>
    (* INR *)
    TOP_CASE_TAC>>fs[]>>
    qpat_x_assum`PAIR_TYPE _ _ _ _` mp_tac>>
    simp[Once PAIR_TYPE_def]>>
    strip_tac>>
    xmatch>>
    xlet_autop>>
    xlet_autop>>
    xlet`(POSTve
             (λv.
                  SEP_EXISTS k' lines' acc' lno' rest.
                    STDIO (forwardFD (forwardFD fs fd k) fd k') *
                    INSTREAM_LINES fd fdv lines'
                      (forwardFD (forwardFD fs fd k) fd k') *
                      &(PAIR_TYPE (LIST_TYPE (PAIR_TYPE (OPTION_TYPE (SUM_TYPE NUM UNIT_TYPE)) (LIST_TYPE (PB_CHECK_PBPSTEP_TYPE)))) NUM (acc',lno') v ∧
                       parse_redundancy ss [] = SOME (acc',rest) ∧
                       MAP toks_fast lines' = rest))
             (λe.
                  SEP_EXISTS k' lines'.
                    STDIO (forwardFD (forwardFD fs fd k) fd k') *
                    INSTREAM_LINES fd fdv lines'
                      (forwardFD (forwardFD fs fd k) fd k') *
                    &(Fail_exn e ∧ parse_redundancy ss [] = NONE)))`
    >- (
      xapp>>
      simp[LIST_TYPE_def]>>
      metis_tac[])
    >- (
      xsimpl>>
      rw[]>>simp[Once parse_pbpsteps_thm]>>
      simp[forwardFD_o]>>
      qexists_tac`k+x`>>
      qexists_tac`x'`>>
      xsimpl)>>
    qpat_x_assum`PAIR_TYPE _ _ _ _` mp_tac>>
    simp[Once PAIR_TYPE_def]>>
    strip_tac>>
    xmatch>>
    xlet_autop>>
    TOP_CASE_TAC>>fs[OPTION_TYPE_def]
    >- (
      qpat_x_assum`!x. _` kall_tac>>
      xmatch>>
      xlet_autop>>
      xlet_autop>>
      xraise>>xsimpl>>
      simp[Once parse_pbpsteps_thm]>>
      simp[forwardFD_o]>>
      qexists_tac`k+k'`>>
      qexists_tac`lines'`>>
      xsimpl>>
      simp[Fail_exn_def]>>
      metis_tac[])>>
    xmatch>>
    xlet_autop>>
    xapp>>
    xsimpl>>
    first_x_assum (irule_at Any)>>simp[]>>
    first_x_assum (irule_at Any)>>simp[]>>
    simp[LIST_TYPE_def]>>
    imp_res_tac parse_pbpsteps_LENGTH>>
    simp[forwardFD_o]>>
    qexists_tac`forwardFD fs fd (k + k')`>>
    qexists_tac`fd`>>qexists_tac`emp`>>
    xsimpl>>
    rw[]
    >- (
      fs[PAIR_TYPE_def]>>
      asm_exists_tac>>xsimpl>>
      simp[forwardFD_o]>>
      qexists_tac`k+(k'+x')`>>
      qexists_tac`x''`>>
      xsimpl)>>
    simp[Once parse_pbpsteps_def]>>
    simp[forwardFD_o]>>
    qexists_tac`k+(k'+x')`>>
    qexists_tac`x''`>>
    xsimpl)>>
  xcfs ["parse_pbpsteps","parse_redundancy"] (get_ml_prog_state ())>>
  xlet_autop>>
  simp[Once parse_pbpsteps_thm]>>
  first_x_assum drule>>
  simp[LIST_TYPE_def]>>
  disch_then(mp_tac o CONV_RULE (RESORT_FORALL_CONV (sort_vars ["lines'"])))>>
  disch_then(qspec_then`lines` mp_tac)>> simp[]>>
  strip_tac>>
  xlet`
    (POSTve
      (λv.
           SEP_EXISTS k lines' acc' s lno' rest.
             STDIO (forwardFD fs fd k) *
             INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
             &(PAIR_TYPE (LIST_TYPE PB_CHECK_PBPSTEP_TYPE)
                (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
                   NUM) (acc',s,lno') v ∧
              parse_pbpsteps (MAP toks_fast lines) [] =
              SOME (acc',s,rest) ∧ MAP toks_fast lines' = rest))
      (λe.
           SEP_EXISTS k lines'.
             STDIO (forwardFD fs fd k) *
             INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
             &(Fail_exn e ∧
              parse_pbpsteps (MAP toks_fast lines) [] = NONE)))`
  >-
    xapp
  >- (
    xsimpl>>
    simp[Once parse_pbpsteps_thm]>>
    rw[]>>
    qexists_tac`x`>>qexists_tac`x'`>>xsimpl)>>
  qpat_x_assum`PAIR_TYPE _ _ _ _` mp_tac>>
  simp[Once PAIR_TYPE_def]>>
  simp[Once PAIR_TYPE_def]>>
  strip_tac>>
  xmatch>>
  xlet_autop>>
  xlet_autop>>
  TOP_CASE_TAC>> fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xlet_autop>>
    xraise>>
    xsimpl>>
    qexists_tac`k`>>qexists_tac`lines'`>>xsimpl>>
    simp[Once parse_pbpsteps_thm,Fail_exn_def]>>
    metis_tac[])>>
  TOP_CASE_TAC>>fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>xsimpl
    >- (
      simp[PAIR_TYPE_def]>>
      asm_exists_tac>>simp[]>>
      asm_exists_tac>>simp[]>>
      qexists_tac`k`>>xsimpl)>>
    simp[Once parse_pbpsteps_thm])>>
  xmatch>>
  xlet_autop>>
  `LENGTH rest < LENGTH lines` by
    (imp_res_tac parse_pbpsteps_LENGTH>>
    fs[])>>
  fs[]>>
  first_x_assum drule>>
  simp[LIST_TYPE_def]>>
  disch_then(mp_tac o CONV_RULE (RESORT_FORALL_CONV (sort_vars ["lines''"])))>>
  disch_then(qspec_then`lines'` mp_tac)>> simp[]>>
  strip_tac>>
  xlet`
    (POSTve
       (λv.
            SEP_EXISTS k lines' acc' s lno' rest'.
              STDIO (forwardFD fs fd k) *
              INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
              &(PAIR_TYPE (LIST_TYPE PB_CHECK_PBPSTEP_TYPE)
                 (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NUM) (acc',s,lno') v ∧
               parse_pbpsteps rest [] = SOME (acc',s,rest') ∧
               MAP toks_fast lines' = rest'))
       (λe.
            SEP_EXISTS k lines'.
              STDIO (forwardFD fs fd k) *
              INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
              &(Fail_exn e ∧ parse_pbpsteps rest [] = NONE)))`
  >- (
    xapp>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>xsimpl>>
    rw[PAIR_TYPE_def]
    >- (
      asm_exists_tac>>simp[forwardFD_o]>>
      qexists_tac`k+x`>>qexists_tac`x'`>>xsimpl)>>
    simp[forwardFD_o]>>
    qexists_tac`k+x`>>qexists_tac`x'`>>xsimpl)
  >- (
    xsimpl>>
    simp[Once parse_pbpsteps_thm]>>
    rw[]>>xsimpl>>
    qexists_tac`x`>>qexists_tac`x'`>>xsimpl)>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
  qpat_x_assum`PAIR_TYPE _ _ _ _` mp_tac>>
  simp[Once PAIR_TYPE_def]>>
  simp[Once PAIR_TYPE_def]>>
  strip_tac>>
  xmatch>>
  xlet_autop>>
  reverse xif
  >- (
    xlet_autop>>
    xlet_autop>>
    xraise>>
    xsimpl>>
    qexists_tac`k`>>qexists_tac`lines''`>>xsimpl>>
    simp[Once parse_pbpsteps_thm,Fail_exn_def]>>
    metis_tac[])>>
  xlet_autop>>
  xlet_autop>>
  xlet_autop>>
  xapp>>
  xsimpl>>
  first_assum (irule_at Any o SYM)>>
  first_x_assum (irule_at Any)>>
  simp[LIST_TYPE_def,PAIR_TYPE_def,OPTION_TYPE_def]>>
  imp_res_tac parse_pbpsteps_LENGTH>>
  `LENGTH lines''= LENGTH rest'` by
    metis_tac[LENGTH_MAP]>>
  simp[]>>xsimpl>>
  qexists_tac`forwardFD fs fd k`>>
  qexists_tac`fd`>>
  qexists_tac`emp`>>
  xsimpl>>rw[]
  >- (
    asm_exists_tac>>
    simp[forwardFD_o]>>
    qexists_tac`k+x'`>>qexists_tac`x''`>>xsimpl)>>
  simp[Once parse_pbpsteps_thm]>>
  simp[forwardFD_o]>>
  qexists_tac`k+x'`>>qexists_tac`x''`>>xsimpl
QED

val parse_redundancy_spec = save_thm("parse_redundancy_spec",el 2 (CONJUNCTS parse_pbpsteps_spec));

val parse_top = process_topdecs`
  fun parse_top fd lno =
    case TextIO.b_inputLineTokens fd blanks tokenize_fast of
      None => None
    | Some s =>
    case parse_pbpstep s of None => raise Fail (format_failure lno "Unable to parse top-level step")
    | Some (Inl step) => Some (step,lno+1)
    | Some (Inr (c,s)) =>
      case parse_redundancy fd (lno+1) [] of (pf,lno') =>
        case parse_pbpsteps_aux c s pf of None =>
          raise Fail (format_failure lno "Unable to format as contradiction or redundancy step")
        | Some step => Some (step,lno')` |> append_prog

Theorem parse_top_spec:
  !ss fd fdv lines lno lnov fs.
  NUM lno lnov ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_top" (get_ml_prog_state()))
    [fdv; lnov]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         &(
            case parse_top ss of
              NONE => F
            | SOME NONE =>
                OPTION_TYPE PB_CHECK_PBPSTEP_TYPE NONE v ∧
                lines' = []
            | SOME (SOME (step,rest)) =>
                OPTION_TYPE (PAIR_TYPE PB_CHECK_PBPSTEP_TYPE NUM) (SOME (step,lno')) v ∧
                MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_top ss = NONE))
      )
Proof
  xcf "parse_top" (get_ml_prog_state ())>>
  Cases_on`ss`>>simp[parse_top_def]
  >- (
    xlet ‘(POSTv v.
        SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES fd fdv [] (forwardFD fs fd k) *
            &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    >- (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘emp’
      \\ qexists_tac ‘lines’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl
      \\ Cases_on`lines` \\ fs[OPTION_TYPE_def]
      \\ rw[] \\ qexists_tac`x` \\ xsimpl) >>
    fs[OPTION_TYPE_def]>>
    xmatch>>
    xcon>>xsimpl>>
    qexists_tac`k`>>xsimpl)>>
  `?l ls. lines = l::ls` by
    (Cases_on`lines`>>fs[])>>
  rw[]>>
  fs[]>>
  xlet ‘(POSTv v.
      SEP_EXISTS k.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES fd fdv ls (forwardFD fs fd k) *
      & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks_fast l)) v)’
  THEN1 (
    xapp_spec b_inputLineTokens_specialize
    \\ qexists_tac ‘emp’
    \\ qexists_tac ‘l::ls’
    \\ qexists_tac ‘fs’
    \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
    \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
    \\ simp[toks_fast_def]) >>
  fs[OPTION_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  Cases_on`parse_pbpstep h`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xlet_autop>>
    xraise>>xsimpl>>
    qexists_tac`k`>>qexists_tac`ls`>>xsimpl>>
    simp[Fail_exn_def]>>metis_tac[])>>
  Cases_on`x`>>fs[SUM_TYPE_def]
  >- ( (* INL*)
    xmatch>>
    xlet_autop>>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    asm_exists_tac>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`k`>>xsimpl)>>
  Cases_on`y`>>fs[]>>
  (* INR *)
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xlet_autop>>
  xlet`(POSTve
           (λv.
                  SEP_EXISTS k' lines' acc' lno' rest.
                    STDIO (forwardFD (forwardFD fs fd k) fd k') *
                    INSTREAM_LINES fd fdv lines'
                      (forwardFD (forwardFD fs fd k) fd k') *
                      &(PAIR_TYPE (LIST_TYPE (PAIR_TYPE (OPTION_TYPE (SUM_TYPE NUM UNIT_TYPE)) (LIST_TYPE (PB_CHECK_PBPSTEP_TYPE)))) NUM (acc',lno') v ∧
                       parse_redundancy t [] = SOME (acc',rest) ∧
                       MAP toks_fast lines' = rest))
             (λe.
                  SEP_EXISTS k' lines'.
                    STDIO (forwardFD (forwardFD fs fd k) fd k') *
                    INSTREAM_LINES fd fdv lines'
                      (forwardFD (forwardFD fs fd k) fd k') *
                    &(Fail_exn e ∧ parse_redundancy t [] = NONE)))`
  >- (
    xapp>>xsimpl>>
    simp[LIST_TYPE_def]>>metis_tac[])
  >- (
    xsimpl>>rw[]>>
    simp[forwardFD_o]>>
    qexists_tac`k+x`>>xsimpl>>
    qexists_tac`x'`>>xsimpl)>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  Cases_on`parse_pbpsteps_aux q r acc'`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xlet_autop>>
    xraise>>xsimpl>>
    simp[forwardFD_o]>>
    qexists_tac`k+k'`>>
    qexists_tac`lines'`>>
    xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[])>>
  xmatch>>
  xlet_autop>>
  xcon>>xsimpl>>
  asm_exists_tac>> simp[]>>
  asm_exists_tac>> simp[]>>
  simp[forwardFD_o]>>
  qexists_tac`k+k'`>>xsimpl
QED

val check_unsat'' = process_topdecs `
  fun check_unsat'' fd lno fml inds mindel id =
    case parse_top fd lno of None => (fml, (False, (id, inds)))
    | Some (step,lno') =>
      (case check_pbpstep_arr lno step fml inds mindel id of
        (fml', (False, (id', inds'))) => check_unsat'' fd lno' fml' inds' mindel id'
      | res => res)` |> append_prog

Definition parse_and_run_def:
  parse_and_run ss fml inds mindel id =
  case parse_top ss of NONE => NONE
  | SOME NONE => SOME (fml, F, id, inds)
  | SOME (SOME (step,rest)) =>
    (case check_pbpstep_list step fml inds mindel id of
      SOME (fml', F, id', inds') =>
        parse_and_run rest fml' inds' mindel id'
    | res => res)
Termination
  WF_REL_TAC `measure (LENGTH o FST)`>>
  Cases_on`ss`>>rw[parse_top_def]>>
  every_case_tac>>fs[]>>
  fs[]>>rw[]>>rveq>>
  imp_res_tac parse_pbpsteps_LENGTH>>
  fs[]
End

val check_pbpstep_arr_spec = save_thm ("check_pbpstep_arr_spec",el 1 (CONJUNCTS pb_arrayProgTheory.check_pbpstep_arr_spec));

Theorem check_unsat''_spec:
  ∀ss fmlls inds mindel id fmlv fmllsv indsv mindelv idv fd fdv lines lno lnov fs.
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat''" (get_ml_prog_state()))
    [fdv; lnov; fmlv; indsv; mindelv; idv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs * ARRAY fmlv fmllsv)
    (POSTve
      (λv.
         SEP_EXISTS k lines' lno' fmlv' fmllsv'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         ARRAY fmlv' fmllsv' *
         &(
          case parse_and_run ss fmlls inds mindel id of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE BOOL (PAIR_TYPE NUM (LIST_TYPE NUM))) res v
          ))
      (λe.
         SEP_EXISTS k lines' fmlv' fmllsv'.
           ARRAY fmlv' fmllsv' *
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_and_run ss fmlls inds mindel id = NONE)))
Proof
  ho_match_mp_tac (fetch "-" "parse_and_run_ind")>>rw[]>>
  xcf "check_unsat''" (get_ml_prog_state ())>>
  simp[Once parse_and_run_def]>>
  Cases_on`parse_top (MAP toks_fast lines)`>>fs[]
  >- ((* parse_top NONE *)
    xlet `(POSTe e.
         SEP_EXISTS k lines' fmlv' fmllsv'.
           ARRAY fmlv' fmllsv' *
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e))`
    >- (
      xapp>>xsimpl>>
      asm_exists_tac>>simp[]>>
      qexists_tac`ARRAY fmlv fmllsv`>>qexists_tac`lines`>>simp[]>>
      qexists_tac`fs`>>qexists_tac`fd`>>xsimpl>>
      rw[]>>
      qexists_tac`x`>>qexists_tac`x'`>>xsimpl>>
      qexists_tac`fmlv`>>qexists_tac`fmllsv`>>xsimpl)>>
    xsimpl>>
    simp[Once parse_and_run_def]>>
    rw[]>>
    qexists_tac`x`>>qexists_tac`x'`>>xsimpl>>
    qmatch_goalsub_abbrev_tac`ARRAY A B`>>
    qexists_tac`A`>>qexists_tac`B`>>xsimpl)>>
  xlet `(POSTv v.
       SEP_EXISTS k lines' lno'.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
       ARRAY fmlv fmllsv *
        &(
            case parse_top (MAP toks_fast lines) of
              NONE => F
            | SOME NONE =>
                OPTION_TYPE PB_CHECK_PBPSTEP_TYPE NONE v ∧
                lines' = []
            | SOME (SOME (step,rest)) =>
                OPTION_TYPE (PAIR_TYPE PB_CHECK_PBPSTEP_TYPE NUM) (SOME (step,lno')) v ∧
                MAP toks_fast lines' = rest))`
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>simp[]>>
    qexists_tac`ARRAY fmlv fmllsv`>>qexists_tac`lines`>>simp[]>>
    qexists_tac`fs`>>qexists_tac`fd`>>xsimpl>>
    TOP_CASE_TAC>>fs[]>>rw[]
    >- (qexists_tac`x'`>>xsimpl)>>
    TOP_CASE_TAC>>fs[]>>
    fs[OPTION_TYPE_def,PAIR_TYPE_def]>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    qexists_tac`x''`>>xsimpl)>>
  Cases_on`x`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl
    >- (
      simp[PAIR_TYPE_def]>>xsimpl>>
      simp[PB_CHECK_PBPRES_TYPE_def]>>
      qexists_tac`k`>>
      qexists_tac`[]`>>
      xsimpl)>>
    simp[Once parse_and_run_def])>>
  Cases_on`x'`>> fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto
  >- (
    xsimpl>>reverse (rw[])
    >-
      (qexists_tac`x`>>qexists_tac`x'`>>xsimpl)>>
    TOP_CASE_TAC>>fs[]>>
    asm_exists_tac>>simp[]>>
    xsimpl)
  >- (
    xsimpl>>rw[]>>
    simp[Once parse_and_run_def]>>
    qexists_tac`k`>>qexists_tac`lines'`>>xsimpl>>
    qexists_tac`x`>>qexists_tac`x'`>>xsimpl)>>
  pop_assum mp_tac>>TOP_CASE_TAC>>simp[]>>
  strip_tac>>
  PairCases_on`x`>>fs[PAIR_TYPE_def]>>
  rename1`BOOL _ bv`>>
  `x1 ∧ bv = Conv (SOME (TypeStamp "True" 0)) [] ∨ ¬x1 ∧ bv = Conv (SOME (TypeStamp "False" 0)) []` by
    (qpat_x_assum`BOOL _ _` mp_tac>>
    Cases_on`x1`>>EVAL_TAC>>simp[])
  >- (
    xmatch >>xvar>>xsimpl>>simp[PAIR_TYPE_def]
    >- (
      asm_exists_tac>>xsimpl>>
      qexists_tac`k`>>qexists_tac`lines'`>>xsimpl)>>
    rw[]>>xsimpl>>
    pop_assum mp_tac>>simp[Once parse_and_run_def])>>
  xmatch>>
  xapp>>xsimpl>>
  asm_exists_tac>>simp[]>>
  asm_exists_tac>>simp[]>>
  qexists_tac`emp`>>qexists_tac`(forwardFD fs fd k)`>>
  qexists_tac`fd`>>xsimpl>>
  rw[]>>simp[forwardFD_o]
  >-
    (qexists_tac`k+x`>>qexists_tac`x'`>>xsimpl>>
    asm_exists_tac>>xsimpl)>>
  qexists_tac`k+x`>>qexists_tac`x'`>>xsimpl>>
  simp[Once parse_and_run_def]>>
  qmatch_goalsub_abbrev_tac`ARRAY A B`>>
  qexists_tac`A`>>qexists_tac`B`>>xsimpl
QED

val r = translate parse_header_line_fast_def;

val check_header = process_topdecs`
  fun check_header fd =
    case TextIO.b_inputLineTokens fd blanks tokenize_fast of
      None => raise Fail (format_failure 0 "Unable to parse header")
    | Some s =>
    if parse_header_line_fast s then () else
      raise Fail (format_failure 0 "Unable to parse header")` |> append_prog;

Theorem check_header_spec:
  !ss fd fdv lines fs.
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_header" (get_ml_prog_state()))
    [fdv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         &(case ss of [] => F
         | (x::xs) => parse_header_line_fast x))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧
            case ss of [] => T | (x::xs) => ¬parse_header_line_fast x)))
Proof
  xcf "check_header" (get_ml_prog_state ())>>
  Cases_on`ss`>>fs[]
  >- (
    xlet ‘(POSTv v.
        SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES fd fdv [] (forwardFD fs fd k) *
            &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    >- (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘emp’
      \\ qexists_tac ‘lines’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl)>>
    fs[OPTION_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    xlet_autop>>
    xraise>>xsimpl>>
    qexists_tac`k`>>qexists_tac`[]`>>xsimpl>>
    simp[Fail_exn_def]>>metis_tac[])>>
  `?l ls. lines = l::ls` by
    (Cases_on`lines`>>fs[])>>
  rw[]>>
  fs[]>>
  xlet ‘(POSTv v.
      SEP_EXISTS k.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES fd fdv ls (forwardFD fs fd k) *
      & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks_fast l)) v)’
  THEN1 (
    xapp_spec b_inputLineTokens_specialize
    \\ qexists_tac ‘emp’
    \\ qexists_tac ‘l::ls’
    \\ qexists_tac ‘fs’
    \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
    \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
    \\ simp[toks_fast_def]) >>
  fs[OPTION_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xif
  >- (
    xcon>>xsimpl>>
    qexists_tac`k`>>qexists_tac`ls`>>xsimpl)>>
  xlet_autop>>
  xlet_autop>>
  xraise>>xsimpl>>
  qexists_tac`k`>>qexists_tac`ls`>>xsimpl>>
  simp[Fail_exn_def]>>metis_tac[]
QED

Definition result_string_def:
  result_string b =
   if b
   then INR (strlit "Verified\n")
   else INL (strlit "Proof checking succeeded but did not derive contradiction\n")
End

val r = translate result_string_def;

val check_unsat' = process_topdecs `
  fun check_unsat' fml inds mindel id fname =
  let
    val fd = TextIO.b_openIn fname
    val u = (check_header fd;
      case check_unsat'' fd 1 fml inds mindel id of
        (fml', (b, (id',inds'))) => result_string b
      ) handle Fail s => Inl s
    val close = TextIO.b_closeIn fd;
  in
    u
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)` |> append_prog;

Definition parse_pbp_def:
  parse_pbp strs =
  case MAP toks_fast strs of
    s::ss =>
    if parse_header_line_fast s then
      parse_tops ss
    else NONE
  | [] => NONE
End

(* Dummy spec *)
Theorem check_unsat'_spec:
  SPTREE_SPT_TYPE PB_CONSTRAINT_NPBC_TYPE fml fmlv ∧ NUM id idv ∧
  FILENAME f fv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat'"(get_ml_prog_state()))
  [fmlv; idv; fv]
  (STDIO fs)
  (POSTv v.
    STDIO fs *
    SEP_EXISTS err.
      &(SUM_TYPE STRING_TYPE (OPTION_TYPE (LIST_TYPE INT)))
      (if inFS_fname fs f then
        (case parse_pbp (all_lines fs f) of
         SOME pbp =>
           INR ARB
        | NONE => INL err)
      else
        INL err
      ) v)
Proof
  cheat
  (*
  xcf"check_unsat'"(get_ml_prog_state()) >>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[]) >>
  reverse (Cases_on `inFS_fname fs f`) >> simp[]
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs f) *
      STDIO fs`
    >-
      (xlet_auto_spec (SOME b_openIn_STDIO_spec) \\ xsimpl)
    >>
      fs[BadFileName_exn_def]>>
      xcases>>rw[]>>
      xlet_auto>>xsimpl>>
      xcon>>xsimpl>>
      simp[SUM_TYPE_def]>>metis_tac[])>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval` \\ xsimpl >>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec (SOME b_openIn_spec_lines) \\ xsimpl >>
  xlet`POSTv resv.
        SEP_EXISTS k rest.
         STDIO (forwardFD fs (nextFD fs) k) *
         INSTREAM_LINES (nextFD fs) is rest (forwardFD fs (nextFD fs) k) *
         &(
           ARB
           (* case
             parse_and_run_file_list (all_lines fs f) mindel fmlls ls (REPLICATE n w8z) earliest
           of
             NONE => resv = Conv (SOME (TypeStamp "Inl" 23)) [v0] ∧ ∃s. STRING_TYPE s v0
           | SOME(fmlls',inds') =>
             resv = Conv (SOME (TypeStamp "Inr" 23)) [Conv NONE [v1; v2]] ∧
             v1 = fmlv' ∧
             LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls' fmllsv' ∧ LIST_TYPE NUM inds' v2 *)
         )`
  >-
    cheat
  >>
  cheat *)
QED

val _ = translate miscTheory.enumerate_def;

val fill_arr = process_topdecs`
  fun fill_arr arr ls =
    case ls of [] => arr
    | (x::xs) =>
    case x of (i,v) =>
      fill_arr (Array.updateResize arr None i (Some v)) xs` |> append_prog

(*
Theorem fill_arr_spec:
  ∀ls lsv arrv arrls arrlsv.
  LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT)) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) arrls arrlsv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"fill_arr"(get_ml_prog_state()))
  [arrv; lsv]
  (ARRAY arrv arrlsv)
  (POSTv resv.
  SEP_EXISTS arrlsv'. ARRAY resv arrlsv' *
    & LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FOLDL (λacc (i,v).  update_resize acc NONE (SOME v) i) arrls ls) arrlsv')
Proof
  Induct>>rw[]>>
  xcf "fill_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>
  xmatch
  >- (xvar>>xsimpl)>>
  Cases_on`h`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop >>
  xlet_auto >>
  xapp>>
  fs[]>>
  match_mp_tac LIST_REL_update_resize>>fs[]>>
  simp[OPTION_TYPE_def]
QED
val _ = translate build_fml_def;

Definition build_def:
  build pbf = build_fml 1 (normalize pbf) LN
End

val r = translate build_def;

val check_pbp = process_topdecs`
  fun check_pbp pbf fname =
    case build pbf of (fml,id) =>
    check_unsat' fml id fname` |> append_prog;
*)

val check_unsat_2 = (append_prog o process_topdecs) `
  fun check_unsat_2 f1 f2 =
  case parse_pbf_full f1 of
    Inl err => TextIO.output TextIO.stdErr err
  | Inr fml =>
  let val ls = enumerate 1 (normalize fml)
      val id = List.length ls + 1
      val arr = Array.array (2*id) None
      val arr = fill_arr arr ls
      val inds = []
      val mindel = 0
  in
    case check_unsat' arr inds mindel id f2 of
      Inl err => TextIO.output TextIO.stdErr err
    | Inr s => TextIO.print s
  end`

val check_unsat_2_sem_def = Define`
  check_unsat_2_sem fs f1 f2 err =
  if inFS_fname fs f1 then
  (case parse_pbf_toks (MAP toks (all_lines fs f1)) of
    NONE => add_stderr fs err
  | SOME pbf =>
    if inFS_fname fs f2 then
      case parse_pbp_toks (MAP toks (all_lines fs f2)) of
        SOME pbp =>
        ARB
        (* case check_pbp pbf pbp of
          INL _ => add_stderr fs err
        | INR succ => add_stdout fs succ *)
      | NONE => add_stderr fs err
    else add_stderr fs err)
  else add_stderr fs err`

val err_tac = xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>qexists_tac`err`>>xsimpl;

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
  cheat
  (*
  rw[]>>
  xcf "check_unsat_2" (get_ml_prog_state ())>>
  xlet_autop>>
  simp[check_unsat_2_sem_def]>>
  reverse TOP_CASE_TAC>>fs[]
  >- (
    fs[SUM_TYPE_def]>>xmatch>>
    err_tac)>>
  TOP_CASE_TAC>> fs[SUM_TYPE_def]
  >- (xmatch>> err_tac)>>
  xmatch>>
  xlet_autop>>
  reverse TOP_CASE_TAC>>fs[]
  >- (
    fs[SUM_TYPE_def]>>xmatch>>
    err_tac)>>
  TOP_CASE_TAC>> fs[SUM_TYPE_def]
  >- (xmatch>>err_tac)>>
  xmatch>>
  xlet_autop>>
  TOP_CASE_TAC >> fs[SUM_TYPE_def]
  >- (xmatch >>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    qexists_tac`fs`>>xsimpl>>
    rw[]>>qexists_tac`x''`>>xsimpl)>>
  xmatch>>
  xapp_spec print_spec >> xsimpl
  \\ qexists_tac`emp`
  \\ asm_exists_tac \\ xsimpl
  \\ qexists_tac`fs`>>xsimpl*)
QED

val check_unsat = (append_prog o process_topdecs) `
  fun check_unsat u =
  case CommandLine.arguments () of
    [f1,f2] => check_unsat_2 f1 f2
  | _ => TextIO.output TextIO.stdErr usage_string`

val check_unsat_sem_def = Define`
  check_unsat_sem cl fs err =
  case TL cl of
  | [f1;f2] => check_unsat_2_sem fs f1 f2 err
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
    qexists_tac`fs`>>xsimpl>>
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

Theorem check_unsat_whole_prog_spec2:
   hasFreeFD fs ⇒
   whole_prog_spec2 check_unsat_v cl fs NONE (λfs'. ∃err. fs' = check_unsat_sem cl fs err)
Proof
  cheat
  (* rw[basis_ffiTheory.whole_prog_spec2_def]
  \\ match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH check_unsat_spec))))
  \\ xsimpl
  \\ rw[PULL_EXISTS]
  \\ qexists_tac`check_unsat_sem cl fs x`
  \\ qexists_tac`x`
  \\ xsimpl
  \\ rw[check_unsat_sem_def,check_unsat_2_sem_def]
  \\ every_case_tac
  \\ simp[GSYM add_stdo_with_numchars,with_same_numchars] *)
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
