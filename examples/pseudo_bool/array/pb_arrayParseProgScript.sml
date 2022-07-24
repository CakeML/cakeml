(*
  Add shared PBP parsing, some common stuff to pb_arrayProg
*)
open preamble basis pb_checkTheory pb_parseTheory pb_normaliseTheory pb_arrayProgTheory;

val _ = new_theory "pb_arrayParseProg"

val _ = translation_extends"pb_arrayProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

Definition noparse_string_def:
  noparse_string f s = concat[strlit"c Input file: ";f;strlit" unable to parse in format: "; s;strlit"\n"]
End

val r = translate noparse_string_def;

Definition notfound_string_def:
  notfound_string f = concat[strlit"c Input file: ";f;strlit" no such file or directory\n"]
End

val r = translate notfound_string_def;

(* PBP parsing *)
val r = translate strip_numbers_def;

val strip_numbers_side_def = theorem "strip_numbers_side_def";
val strip_numbers_side = Q.prove(
  `∀x y. strip_numbers_side x y <=> T`,
  Induct>>rw[Once strip_numbers_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate pb_preconstraintTheory.map_lit_def;
val r = translate pb_normaliseTheory.mapNon_def;
val r = translate pb_normaliseTheory.mapChar_def;
val r = translate pb_normaliseTheory.mapChars_def;
val r = translate pb_normaliseTheory.mapString_def;

val mapchars_side_def = fetch "-" "mapchars_side_def";

Theorem mapchars_side:
   ∀n s. n ≤ LENGTH s ⇒ mapchars_side n (strlit s)
Proof
  Induct>>rw[]>>
  simp[Once mapchars_side_def]
QED

val mapstring_side = Q.prove(
  `∀x. mapstring_side x = T`,
  Cases>>EVAL_TAC>>
  match_mp_tac mapchars_side>>
  simp[]) |> update_precondition;

val r = translate goodChar_def;
val r = translate goodChars_def;
val r = translate goodString_def;

val goodchars_side_def = fetch "-" "goodchars_side_def";

Theorem goodchars_side:
   ∀n s. n ≤ LENGTH s ⇒ goodchars_side n (strlit s)
Proof
  Induct>>rw[]>>
  simp[Once goodchars_side_def]
QED

val goodstring_side = Q.prove(
  `∀x. goodstring_side x = T`,
  Cases>>EVAL_TAC>>
  match_mp_tac goodchars_side>>
  simp[]) |> update_precondition;

val r = translate parse_lit_def;

val parse_lit_side_def = definition"parse_lit_side_def";
val parse_lit_side = Q.prove(
  `∀x. parse_lit_side x <=> T`,
  rw[parse_lit_side_def])
  |> update_precondition;

val r = translate parse_lit_num_def;
val r = translate parse_cutting_def;

val parse_cutting_side_def = theorem "parse_cutting_side_def";
val parse_cutting_side = Q.prove(
  `∀x y. parse_cutting_side x y <=> T`,
  Induct>>rw[Once parse_cutting_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_var_def;

val r = translate insert_def;
val r = translate parse_subst_def;

val r = translate pbc_ge_def;
val r = translate pb_preconstraintTheory.lit_var_def;
val r = translate compact_lhs_def;
val r = translate term_le_def;

val r = translate mk_coeff_def;
val r = translate normalise_lhs_def;

val r = translate pbc_to_npbc_def;

val pbc_to_npbc_side = Q.prove(
  `∀x. pbc_to_npbc_side x <=> T`,
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_constraint_LHS_def;

val r = translate pb_preconstraintTheory.map_pbc_def;
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

val result = translate pb_parseTheory.fromString_unsafe_def;

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
  EVAL_TAC >> fs[]>>
  Cases>>simp[fromchars_unsafe_side_thm]
  ) |> update_precondition;

val r = translate blanks_def;

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
  >- (
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

val _ = export_theory();
