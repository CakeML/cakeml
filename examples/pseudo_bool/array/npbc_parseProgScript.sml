(*
  Add shared pbp parsing, some common stuff to npbc_arrayProg
*)
open preamble basis npbc_checkTheory pb_parseTheory npbc_arrayProgTheory pbc_normaliseTheory;

val _ = new_theory "npbc_parseProg"

val _ = translation_extends"npbc_arrayProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

val r = translate strip_numbers_def;
val strip_numbers_side_def = theorem "strip_numbers_side_def";
val strip_numbers_side = Q.prove(
  `∀x y. strip_numbers_side x y <=> T`,
  Induct>>rw[Once strip_numbers_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate pbcTheory.map_lit_def;

val r = translate hashNon_def;
val r = translate hashChar_def;
val r = translate hashChars_alt_def;
val r = translate hashString_def;

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

(* PBP parsing *)

val r = translate pbcTheory.lit_var_def;
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
val r = translate pbcTheory.map_pbc_def;

val r = translate parse_constraint_npbc_def;

val r = translate parse_var_def;
val r = translate insert_def;
val r = translate parse_subst_def;

val r = translate parse_red_header_def;

val r = translate parse_lstep_aux_def;

val parse_lstep_aux_side_def = fetch "-" "parse_lstep_aux_side_def";
val parse_lstep_aux_side = Q.prove(
  `∀x. parse_lstep_aux_side x <=> T`,
  rw[Once parse_lstep_aux_side_def]>>fs[]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate check_end_def;

val r = translate blanks_def;

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

Definition not_isEmpty_def:
  not_isEmpty s ⇔ s ≠ LN
End

val r = translate not_isEmpty_def;

val parse_lsteps_aux = process_topdecs`
  fun parse_lsteps_aux fd lno acc =
    case TextIO.b_inputLineTokens fd blanks tokenize_fast of
      None => raise Fail (format_failure lno "reached EOF while reading PBP steps")
    | Some s =>
    case parse_lstep_aux s of None => (List.rev acc,(s,lno))
    | Some (Inl step) => parse_lsteps_aux fd (lno+1) (step::acc)
    | Some (Inr (c,s)) =>
      if not_isempty s then
          raise Fail (format_failure lno "only contradiction steps allowed in nested proof steps")
      else
        (case parse_lsteps_aux fd (lno+1) [] of
          (pf,(s,lno')) =>
          if check_end s then
            parse_lsteps_aux fd (lno+1) (Con c pf::acc)
          else raise Fail (format_failure lno' "subproof not terminated"))`
    |> append_prog;

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

Theorem EqualityType_PBC_LIT_TYPE:
  EqualityType a ⇒
  EqualityType (PBC_LIT_TYPE a)
Proof
  EVAL_TAC>>
  rw[]>>
  Cases_on`x1`>>fs[PBC_LIT_TYPE_def]>>
  TRY(Cases_on`x2`>>fs[PBC_LIT_TYPE_def])>>
  EVAL_TAC>>
  metis_tac[]
QED

Theorem STDIO_INSTREAM_LINES_refl:
  STDIO A *
  INSTREAM_LINES B C D E ==>>
  STDIO A *
  INSTREAM_LINES B C D E
Proof
  xsimpl
QED

Theorem STDIO_INSTREAM_LINES_refl_gc:
  STDIO A *
  INSTREAM_LINES B C D E ==>>
  STDIO A *
  INSTREAM_LINES B C D E * GC
Proof
  xsimpl
QED

Theorem parse_lsteps_aux_spec:
  ∀ss acc fd fdv lines lno lnov accv fs.
  NUM lno lnov ∧
  LIST_TYPE (NPBC_CHECK_LSTEP_TYPE) acc accv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_lsteps_aux" (get_ml_prog_state()))
    [fdv; lnov; accv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))
              (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NUM) (acc',s,lno') v ∧
            parse_lsteps_aux ss acc = SOME(acc',s,rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_lsteps_aux ss acc = NONE))
      )
Proof
  ho_match_mp_tac parse_lsteps_aux_ind>>
  rw[]
  >- (
    xcf "parse_lsteps_aux" (get_ml_prog_state ())>>
    xlet ‘(POSTv v.
        SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES fd fdv [] (forwardFD fs fd k) *
            &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘emp’
      \\ qexists_tac ‘[]’
      \\ xsimpl
      \\ metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc])>>
    fs[OPTION_TYPE_def]>>
    xmatch >>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Once parse_lsteps_aux_thm]>>
    simp[Once parse_lsteps_aux_thm]>>
    simp[Fail_exn_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
  >- (
    xcfs ["parse_lsteps_aux"] (get_ml_prog_state ())>>
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
    simp[Once parse_lsteps_aux_thm]>>
    TOP_CASE_TAC>>fs[OPTION_TYPE_def]
    >- ((* parse_lstep_aux gives None *)
      xmatch>>
      rpt xlet_autop>>
      xcon>>
      xsimpl>- (
        simp[PAIR_TYPE_def]>>
        metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
      simp[Once parse_lsteps_aux_thm])>>
    (* parse_lstep_aux gives Some *)
    TOP_CASE_TAC>>fs[SUM_TYPE_def]
    (* INL *)
    >- (
      xmatch>>
      rpt xlet_autop>>
      xapp>>
      first_x_assum (irule_at Any)>>simp[]>>
      first_x_assum (irule_at Any)>>simp[LIST_TYPE_def]>>
      xsimpl>>
      qexists_tac`forwardFD fs fd k`>>xsimpl>>
      qexists_tac`fd`>>qexists_tac`emp`>>xsimpl>>
      rw[]
      >- (
        fs[PAIR_TYPE_def]>>
        simp[forwardFD_o]>>
        metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
      simp[forwardFD_o]>>
      fs[Once parse_lsteps_aux_thm]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    (* INR *)
    TOP_CASE_TAC>>fs[]>>
    qpat_x_assum`PAIR_TYPE _ _ _ _` mp_tac>>
    simp[Once PAIR_TYPE_def]>>
    strip_tac>>
    xmatch>>
    xlet_auto
    >- (
      xsimpl>>
      match_mp_tac EqualityType_SUM_TYPE>>
      simp[EqualityType_NUM_BOOL]>>
      match_mp_tac EqualityType_PBC_LIT_TYPE>>
      simp[EqualityType_NUM_BOOL])>>
    reverse (Cases_on`isEmpty r`>>fs[not_isEmpty_def])
    >- (
      xif>>asm_exists_tac>>xsimpl>>
      rpt xlet_autop>>
      xraise>>xsimpl>>
      simp[Once parse_lsteps_aux_thm,Fail_exn_def]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    xif>>asm_exists_tac>>xsimpl>>
    rpt xlet_autop>>
    xlet`(POSTve
             (λv.
                  SEP_EXISTS k' lines' acc' s' lno' rest.
                    STDIO (forwardFD (forwardFD fs fd k) fd k') *
                    INSTREAM_LINES fd fdv lines'
                      (forwardFD (forwardFD fs fd k) fd k') *
                      &(
            PAIR_TYPE (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))
              (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NUM) (acc',s',lno') v ∧
            parse_lsteps_aux ss [] = SOME(acc',s',rest) ∧
            MAP toks_fast lines' = rest))
             (λe.
                  SEP_EXISTS k' lines'.
                    STDIO (forwardFD (forwardFD fs fd k) fd k') *
                    INSTREAM_LINES fd fdv lines'
                      (forwardFD (forwardFD fs fd k) fd k') *
                    &(Fail_exn e ∧ parse_lsteps_aux ss [] = NONE)))`
    >- (
      last_x_assum xapp_spec>>
      simp[LIST_TYPE_def]>>
      metis_tac[])
    >- (
      xsimpl>>
      rw[]>>simp[Once parse_lsteps_aux_thm,forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl])>>
    qpat_x_assum`PAIR_TYPE _ _ _ _` mp_tac>>
    simp[Once PAIR_TYPE_def]>>
    simp[Once PAIR_TYPE_def]>>
    strip_tac>>
    xmatch>>
    xlet_autop>>
    Cases_on`check_end s'`>>xif>>
    asm_exists_tac>>simp[]
    >- (
      rpt xlet_autop>>
      xapp>>
      first_x_assum (irule_at Any)>>simp[]>>
      qexists_tac`lines'`>>
      simp[LIST_TYPE_def,NPBC_CHECK_LSTEP_TYPE_def]>>
      `LENGTH lines' < LENGTH ss` by (
        imp_res_tac parse_lsteps_aux_LENGTH>>
        metis_tac[LENGTH_MAP])>>
      simp[forwardFD_o]>>
      qexists_tac`forwardFD fs fd (k + k')`>>
      qexists_tac`fd`>>qexists_tac`emp`>>
      xsimpl>>
      rw[]
      >- (
        fs[PAIR_TYPE_def]>>
        asm_exists_tac>>xsimpl>>
        simp[forwardFD_o]>>
        metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
      simp[Once parse_lsteps_aux_thm]>>
      simp[forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    rpt xlet_autop>>
    xraise>>
    xsimpl >>
    simp[Once parse_lsteps_aux_thm,forwardFD_o,Fail_exn_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
QED

val r = translate parse_subgoal_num_def;

val parse_subgoal_num_side_def = fetch "-" "parse_subgoal_num_side_def";
val parse_subgoal_num_side = Q.prove(
  `∀x . parse_subgoal_num_side x <=> T`,
  Induct>>rw[Once parse_subgoal_num_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_red_body_def;

val r = translate mk_acc_def;

val parse_red_aux = process_topdecs`
  fun parse_red_aux fd lno acc =
    case parse_lsteps_aux fd lno [] of
      (pf,(s,lno')) =>
      let val acc' = mk_acc pf acc in
        case parse_red_body s of
          None => raise Fail (format_failure lno' "subproof not terminated")
        | Some (Inl u) => (List.rev acc', lno')
        | Some (Inr ind) =>
          (case parse_lsteps_aux fd lno' [] of
            (pf,(s,lno'')) =>
            if check_end s then
              parse_red_aux fd lno'' ((Some ind,pf)::acc')
            else
              raise Fail (format_failure lno' "subproof not terminated"))
      end` |> append_prog

Theorem parse_red_aux_spec:
  ∀ss acc fd fdv lines lno lnov accv fs.
  NUM lno lnov ∧
  LIST_TYPE (PAIR_TYPE (OPTION_TYPE (SUM_TYPE NUM UNIT_TYPE))(LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))) acc accv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_red_aux" (get_ml_prog_state()))
    [fdv; lnov; accv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         &(
            (PAIR_TYPE
              (LIST_TYPE (PAIR_TYPE (OPTION_TYPE (SUM_TYPE NUM UNIT_TYPE)) (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE)))) NUM) (acc',lno') v ∧
            parse_red_aux ss acc = SOME(acc',rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_red_aux ss acc = NONE))
      )
Proof
  ho_match_mp_tac parse_red_aux_ind>>
  rw[]>>
  simp[Once parse_red_aux_def]>>
  xcf "parse_red_aux" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' acc' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))
              (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NUM) (acc',s,lno') v ∧
            parse_lsteps_aux (MAP toks_fast lines) [] = SOME(acc',s,rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_lsteps_aux (MAP toks_fast lines) [] = NONE))
      )`
  >- (
    xapp>>xsimpl>>
    simp[LIST_TYPE_def]>>
    metis_tac[])
  >- (
    xsimpl>>
    rw[]>>
    simp[Once parse_red_aux_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  simp[]>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  Cases_on`parse_red_body s`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xlet_autop>>
    xraise>>xsimpl>>
    simp[Once parse_red_aux_def,Fail_exn_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  TOP_CASE_TAC>>fs[SUM_TYPE_def]
  >- ( (* INL*)
    xmatch>>
    xlet_autop>>
    xcon>>xsimpl
    >- metis_tac[STDIO_INSTREAM_LINES_refl_gc]>>
    rw[]>>
    gs[Once parse_red_aux_def])
  >- ( (* INR*)
    xmatch>>
    xlet_autop>>
    xlet`(POSTve
      (λv.
         SEP_EXISTS k lines'' acc' s lno' rest'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines'' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))
              (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NUM) (acc',s,lno') v ∧
            parse_lsteps_aux rest [] = SOME(acc',s,rest') ∧
            MAP toks_fast lines'' = rest'))
      (λe.
         SEP_EXISTS k lines''.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines'' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_lsteps_aux rest [] = NONE))
      )`
    >- (
      xapp>>xsimpl>>
      asm_exists_tac>>xsimpl>>
      qexists_tac`emp`>>qexists_tac`lines'`>>
      qexists_tac`forwardFD fs fd k`>>
      qexists_tac`fd`>>xsimpl>>
      qexists_tac`[]`>>simp[LIST_TYPE_def,PAIR_TYPE_def]>>
      rw[]
      >-(
        simp[forwardFD_o]>>
        metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
      simp[forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])
    >- (
      xsimpl>>rw[]>>
      simp[Once parse_red_aux_def]>>
      metis_tac[STDIO_INSTREAM_LINES_refl])>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    reverse (Cases_on`check_end s'`)>>
    fs[]>>xif>>asm_exists_tac>>
    simp[]
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[Once parse_red_aux_def,Fail_exn_def]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    rpt xlet_autop>>
    xapp>>
    simp[LIST_TYPE_def,PAIR_TYPE_def,OPTION_TYPE_def]>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    xsimpl>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>qexists_tac`emp`>>xsimpl>>
    rw[]
    >- (
      simp[forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    simp[Once parse_red_aux_def]>>
    simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
QED

val parse_top = process_topdecs`
  fun parse_top fd lno =
    case TextIO.b_inputLineTokens fd blanks tokenize_fast of
      None => None
    | Some s =>
    case parse_lstep_aux s of None =>
      raise Fail (format_failure lno "Unable to parse top-level step")
    | Some (Inl step) => Some (Lstep step,lno+1)
    | Some (Inr (c,s)) =>
      if not_isempty s then
        case parse_red_aux fd (lno+1) [] of
          (pf,lno') =>
          Some (Red c s pf,lno')
      else
        (case parse_lsteps_aux fd (lno+1) [] of
          (pf,(s,lno')) =>
            if check_end s then
              Some (Lstep (Con c pf),lno')
            else
              raise Fail (format_failure lno' "subproof not terminated"))` |> append_prog

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
                OPTION_TYPE NPBC_CHECK_SSTEP_TYPE NONE v ∧
                lines' = []
            | SOME (SOME (step,rest)) =>
                OPTION_TYPE (PAIR_TYPE NPBC_CHECK_SSTEP_TYPE NUM) (SOME (step,lno')) v ∧
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
      \\ metis_tac[STDIO_INSTREAM_LINES_refl_gc]) >>
    fs[OPTION_TYPE_def]>>
    xmatch>>
    xcon>>xsimpl>>
    metis_tac[ STDIO_INSTREAM_LINES_refl_gc])>>
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
  Cases_on`parse_lstep_aux h`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[ STDIO_INSTREAM_LINES_refl_gc])>>
  Cases_on`x`>>fs[SUM_TYPE_def]
  >- ( (* INL*)
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def,NPBC_CHECK_SSTEP_TYPE_def]>>
    metis_tac[ STDIO_INSTREAM_LINES_refl_gc])>>
  (* INR *)
  Cases_on`y`>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>
    match_mp_tac EqualityType_SUM_TYPE>>
    simp[EqualityType_NUM_BOOL]>>
    match_mp_tac EqualityType_PBC_LIT_TYPE>>
    simp[EqualityType_NUM_BOOL])>>
  Cases_on`isEmpty r`>>fs[not_isEmpty_def]>>
  xif>>asm_exists_tac>>simp[]
  >- (
    rpt xlet_autop>>
    xlet`(POSTve
      (λv.
         SEP_EXISTS k ls' acc' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv ls' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))
              (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NUM) (acc',s,lno') v ∧
            parse_lsteps_aux (MAP toks_fast ls) [] = SOME(acc',s,rest) ∧
            MAP toks_fast ls' = rest))
      (λe.
         SEP_EXISTS k ls'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv ls' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_lsteps_aux (MAP toks_fast ls) [] = NONE))
      )`
    >- (
      xapp>>xsimpl>>
      asm_exists_tac>>xsimpl>>
      qexists_tac`emp`>>qexists_tac`ls`>>
      qexists_tac`forwardFD fs fd k`>>
      qexists_tac`fd`>>xsimpl>>
      qexists_tac`[]`>>simp[LIST_TYPE_def,PAIR_TYPE_def]>>
      rw[]
      >-(
        simp[forwardFD_o]>>
        metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
      simp[forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])
    >- (
      xsimpl>>
      metis_tac[STDIO_INSTREAM_LINES_refl])>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    IF_CASES_TAC>>fs[]>>xif>>asm_exists_tac>>simp[]
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[NPBC_CHECK_SSTEP_TYPE_def,NPBC_CHECK_LSTEP_TYPE_def]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  rpt xlet_autop>>
  xlet`(POSTve
      (λv.
         SEP_EXISTS k ls' acc' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv ls' (forwardFD fs fd k) *
         &(
            (PAIR_TYPE
              (LIST_TYPE (PAIR_TYPE (OPTION_TYPE (SUM_TYPE NUM UNIT_TYPE)) (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE)))) NUM) (acc',lno') v ∧
            parse_red_aux t [] = SOME(acc',rest) ∧
            MAP toks_fast ls' = rest))
      (λe.
         SEP_EXISTS k ls'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv ls' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_red_aux t [] = NONE))
      )`
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`ls`>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>xsimpl>>
    qexists_tac`[]`>>simp[LIST_TYPE_def,PAIR_TYPE_def]>>
    rw[]
    >-(
      simp[forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
  >- (
    xsimpl>>
    metis_tac[STDIO_INSTREAM_LINES_refl] )>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  simp[NPBC_CHECK_SSTEP_TYPE_def,NPBC_CHECK_LSTEP_TYPE_def]>>
  metis_tac[STDIO_INSTREAM_LINES_refl_gc]
QED

val check_unsat'' = process_topdecs `
  fun check_unsat'' fd lno fml inds id =
    case parse_top fd lno of None => (fml, (False, (id, inds)))
    | Some (step,lno') =>
      (case check_sstep_arr lno step fml inds id of
        (fml', (False, (id', inds'))) => check_unsat'' fd lno' fml' inds' id'
      | res => res)` |> append_prog

Definition parse_and_run_def:
  parse_and_run ss fml inds id =
  case parse_top ss of NONE => NONE
  | SOME NONE => SOME (fml, F, id, inds)
  | SOME (SOME (step,rest)) =>
    (case check_sstep_list step fml inds id of
      SOME (fml', F, id', inds') =>
        parse_and_run rest fml' inds' id'
    | res => res)
Termination
  WF_REL_TAC `measure (LENGTH o FST)`>>
  Cases_on`ss`>>rw[parse_top_def]>>
  every_case_tac>>fs[]>>
  fs[]>>rw[]>>rveq>>
  imp_res_tac parse_lsteps_aux_LENGTH>>
  imp_res_tac parse_red_aux_LENGTH>>
  fs[]
End

Theorem ARRAY_STDIO_INSTREAM_LINES_refl:
  (ARRAY arr arrv * STDIO A *
  INSTREAM_LINES B C D E ==>>
  ARRAY arr arrv * STDIO A *
  INSTREAM_LINES B C D E) ∧
  (ARRAY arr arrv * STDIO A *
  INSTREAM_LINES B C D E ==>>
  ARRAY arr arrv * STDIO A *
  INSTREAM_LINES B C D E * GC)
Proof
  xsimpl
QED

Theorem check_unsat''_spec:
  ∀ss fmlls inds id fmlv fmllsv indsv idv fd fdv lines lno lnov fs.
  NUM lno lnov ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat''" (get_ml_prog_state()))
    [fdv; lnov; fmlv; indsv; idv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs * ARRAY fmlv fmllsv)
    (POSTve
      (λv.
         SEP_EXISTS k lines' lno' fmlv' fmllsv'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         ARRAY fmlv' fmllsv' *
         &(
          case parse_and_run ss fmlls inds id of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE BOOL (PAIR_TYPE NUM (LIST_TYPE NUM))) res v
          ))
      (λe.
         SEP_EXISTS k lines' fmlv' fmllsv'.
           ARRAY fmlv' fmllsv' *
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_and_run ss fmlls inds id = NONE)))
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
    metis_tac[ARRAY_STDIO_INSTREAM_LINES_refl])>>
  (* parse_top SOME *)
  xlet `(POSTv v.
       SEP_EXISTS k lines' lno'.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
       ARRAY fmlv fmllsv *
        &(
            case parse_top (MAP toks_fast lines) of
              NONE => F
            | SOME NONE =>
                OPTION_TYPE NPBC_CHECK_SSTEP_TYPE NONE v ∧
                lines' = []
            | SOME (SOME (step,rest)) =>
                OPTION_TYPE (PAIR_TYPE NPBC_CHECK_SSTEP_TYPE NUM) (SOME (step,lno')) v ∧
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
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
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
    metis_tac[ARRAY_STDIO_INSTREAM_LINES_refl])>>
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
