(*
  Add shared pbp parsing, normalization and other common stuff to npbc_arrayProg
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

(* TODO: decouple parse_lit from goodChar *)
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

val r = translate apply_lit_def;
val r = translate parse_lit_num_def;
val r = translate parse_cutting_def;

val parse_cutting_side_def = theorem "parse_cutting_side_def";
val parse_cutting_side = Q.prove(
  `∀x y z. parse_cutting_side x y z <=> T`,
  Induct_on`y`>>rw[Once parse_cutting_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_var_def;

val r = translate insert_def;
val r = translate parse_subst_def;

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

val r = translate parse_red_header_def;

val r = translate parse_lstep_aux_def;

val parse_lstep_aux_side_def = fetch "-" "parse_lstep_aux_side_def";
val parse_lstep_aux_side = Q.prove(
  `∀x y. parse_lstep_aux_side x y <=> T`,
  rw[Once parse_lstep_aux_side_def]>>fs[]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate check_end_def;

val check_end_side = Q.prove(
  `∀x. check_end_side x <=> T`,
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC) |> update_precondition;

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

Triviality fromchars_unsafe_ind:
  fromchars_unsafe_ind
Proof
  rewrite_tac [fetch "-" "fromchars_unsafe_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]
  \\ fs[padLen_DEC_eq,ADD1]
QED

val _ = fromchars_unsafe_ind |> update_precondition;

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
  fun parse_lsteps_aux f_ns fd lno acc =
    case TextIO.b_inputLineTokens fd blanks tokenize_fast of
      None => raise Fail (format_failure lno "reached EOF while reading PBP steps")
    | Some s =>
    case parse_lstep_aux f_ns s of None => (List.rev acc,(f_ns,(s,lno)))
    | Some (Inl step,f_ns') => parse_lsteps_aux f_ns' fd (lno+1) (step::acc)
    | Some (Inr (c,s),f_ns') =>
      if not_isempty s then
          raise Fail (format_failure lno "only contradiction steps allowed in nested proof steps")
      else
        (case parse_lsteps_aux f_ns' fd (lno+1) [] of
          (pf,(f_ns'',(s,lno'))) =>
          case check_end s of
            None => raise Fail (format_failure lno' "subproof not terminated with contradiction id")
          | Some id =>
            parse_lsteps_aux f_ns'' fd (lno+1) (Con c pf id::acc))`
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

Theorem EqualityType_SUM_TYPE:
  EqualityType t1 ∧ EqualityType t2 ⇒
  EqualityType (SUM_TYPE t1 t2)
Proof
  EVAL_TAC>>rw[]
  >- (
    Cases_on`x1`>>fs[SUM_TYPE_def]>>
    simp[no_closures_def]>>
    metis_tac[])
  >- (
    Cases_on`x1`>>Cases_on`x2`>>
    fs[SUM_TYPE_def])>>
  Cases_on`x1`>>Cases_on`x2`>>
  fs[SUM_TYPE_def]>>
  EVAL_TAC>>
  metis_tac[]
QED

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
  ∀fns ss acc fd fdv lines lno lnov accv fs fnsv.
  PAIR_TYPE (STRING_TYPE --> a --> OPTION_TYPE (PAIR_TYPE NUM a)) a fns fnsv ∧
  NUM lno lnov ∧
  LIST_TYPE (NPBC_CHECK_LSTEP_TYPE) acc accv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_lsteps_aux" (get_ml_prog_state()))
    [fnsv; fdv; lnov; accv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' fns' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))
              (PAIR_TYPE (PAIR_TYPE (STRING_TYPE --> a --> OPTION_TYPE (PAIR_TYPE NUM a)) a)
              (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
                NUM)) (acc',fns',s,lno') v ∧
            parse_lsteps_aux fns ss acc = SOME(acc',fns',s,rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_lsteps_aux fns ss acc = NONE))
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
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[PAIR_TYPE_def,SUM_TYPE_def]
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
    rename1`isEmpty tt`>>
    reverse (Cases_on`isEmpty tt`>>fs[not_isEmpty_def])
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
                  SEP_EXISTS k' lines' acc' fns' s' lno' rest.
                    STDIO (forwardFD (forwardFD fs fd k) fd k') *
                    INSTREAM_LINES fd fdv lines'
                      (forwardFD (forwardFD fs fd k) fd k') *
                      &(
            PAIR_TYPE (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))
              (PAIR_TYPE (PAIR_TYPE (STRING_TYPE --> a --> OPTION_TYPE (PAIR_TYPE NUM a)) a)
              (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
              NUM)) (acc',fns',s',lno') v ∧
            parse_lsteps_aux r ss [] = SOME(acc',fns',s',rest) ∧
            MAP toks_fast lines' = rest))
             (λe.
                  SEP_EXISTS k' lines'.
                    STDIO (forwardFD (forwardFD fs fd k) fd k') *
                    INSTREAM_LINES fd fdv lines'
                      (forwardFD (forwardFD fs fd k) fd k') *
                    &(Fail_exn e ∧ parse_lsteps_aux r ss [] = NONE)))`
    >- (
      first_x_assum xapp_spec>>
      simp[LIST_TYPE_def]>>
      asm_exists_tac>>simp[PULL_EXISTS]>>
      asm_exists_tac>>simp[]>>
      xsimpl>>
      qexists_tac`emp`>>qexists_tac`(forwardFD fs fd k)`>>
      qexists_tac`fd`>>
      xsimpl>>
      rw[]>>
      simp[PAIR_TYPE_def]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])
    >- (
      xsimpl>>
      rw[]>>simp[Once parse_lsteps_aux_thm,forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl])>>
    qpat_x_assum`PAIR_TYPE _ _ _ _` mp_tac>>
    simp[Once PAIR_TYPE_def]>>
    simp[Once PAIR_TYPE_def]>>
    simp[Once PAIR_TYPE_def]>>
    strip_tac>>
    xmatch>>
    xlet_autop>>
    Cases_on`check_end s'`>>fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl >>
      simp[Once parse_lsteps_aux_thm,forwardFD_o,Fail_exn_def]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    rpt xlet_autop>>
    last_x_assum xapp_spec>>
    xsimpl>>
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
    >-
      fs[]
    >- (
      fs[PAIR_TYPE_def]>>
      asm_exists_tac>>xsimpl>>
      simp[forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    simp[Once parse_lsteps_aux_thm]>>
    simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
QED

val r = translate parse_hash_num_def;

val parse_hash_num_side_def = fetch "-" "parse_hash_num_side_def";
val parse_hash_num_side = Q.prove(
  `∀x . parse_hash_num_side x <=> T`,
  Induct>>rw[Once parse_hash_num_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_subgoal_num_def;

val parse_subgoal_num_side_def = fetch "-" "parse_subgoal_num_side_def";
val parse_subgoal_num_side = Q.prove(
  `∀x . parse_subgoal_num_side x <=> T`,
  Induct>>rw[Once parse_subgoal_num_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_proofgoal_def;

val r = translate parse_red_body_def;

val r = translate mk_acc_def;

val parse_red_aux = process_topdecs`
  fun parse_red_aux f_ns fd lno acc =
    case parse_lsteps_aux f_ns fd lno [] of
      (pf,(f_ns',(s,lno'))) =>
      let val acc' = mk_acc pf acc in
        case parse_red_body s of
          None => raise Fail (format_failure lno' "unable to parse subproof")
        | Some (Inl u) => (List.rev acc', (f_ns', lno'))
        | Some (Inr ind) =>
          (case parse_lsteps_aux f_ns' fd lno' [] of
            (pf,(f_ns'',(s,lno''))) =>
            case check_end s of
              None => raise Fail (format_failure lno' "subproof not terminated with contradiction id")
          | Some id =>
              parse_red_aux f_ns'' fd lno'' ((Some (ind,id),pf)::acc')
              )
      end` |> append_prog

Theorem parse_red_aux_spec:
  ∀fns ss acc fd fdv lines lno lnov accv fs fnsv.
  PAIR_TYPE (STRING_TYPE --> a --> OPTION_TYPE (PAIR_TYPE NUM a)) a fns fnsv ∧
  NUM lno lnov ∧
  LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM)) (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))) acc accv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_red_aux" (get_ml_prog_state()))
    [fnsv; fdv; lnov; accv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' fns' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM)) (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))))
              (PAIR_TYPE (PAIR_TYPE (STRING_TYPE --> a --> OPTION_TYPE (PAIR_TYPE NUM a)) a)
              NUM) (acc',fns',lno') v ∧
            parse_red_aux fns ss acc = SOME(acc',fns',rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_red_aux fns ss acc = NONE))
      )
Proof
  ho_match_mp_tac parse_red_aux_ind>>
  rw[]>>
  simp[Once parse_red_aux_def]>>
  xcf "parse_red_aux" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' acc' fns' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))
              (PAIR_TYPE (PAIR_TYPE (STRING_TYPE --> a --> OPTION_TYPE (PAIR_TYPE NUM a)) a)
              (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
                NUM)) (acc',fns',s,lno') v ∧
            parse_lsteps_aux fns (MAP toks_fast lines) [] = SOME(acc',fns',s,rest) ∧
            MAP toks_fast lines' = rest))
     (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_lsteps_aux fns (MAP toks_fast lines) [] = NONE))
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
         SEP_EXISTS k lines'' acc' fns'' s lno' rest'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines'' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))
              (PAIR_TYPE (PAIR_TYPE (STRING_TYPE --> a --> OPTION_TYPE (PAIR_TYPE NUM a)) a)
              (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
                NUM))
              (acc',fns'',s,lno') v ∧
            parse_lsteps_aux fns' rest [] = SOME(acc',fns'',s,rest') ∧
            MAP toks_fast lines'' = rest'))
      (λe.
         SEP_EXISTS k lines''.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines'' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_lsteps_aux fns' rest [] = NONE))
      )`
    >- (
      xapp>>xsimpl>>
      asm_exists_tac>>xsimpl>>
      qexists_tac`emp`>>qexists_tac`lines'`>>
      qexists_tac`forwardFD fs fd k`>>
      first_x_assum (irule_at Any)>>
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
    Cases_on`check_end s'`>>
    fs[OPTION_TYPE_def]>>xmatch
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
  fun parse_top fns fd lno =
    case TextIO.b_inputLineTokens fd blanks tokenize_fast of
      None =>
      raise Fail (format_failure lno "Unexpected EOF when parsing proof steps")
    | Some s =>
    (case parse_lstep_aux fns s of
      None => (Inl s, (fns, lno))
    | Some (Inl step,fns') => (Inr (Lstep step),(fns',lno+1))
    | Some (Inr (c,s),fns') =>
      if not_isempty s then
        case parse_red_aux fns' fd (lno+1) [] of
          (pf,(fns'',lno')) =>
          (Inr (Red c s pf),(fns'',lno'))
      else
        case parse_lsteps_aux fns' fd (lno+1) [] of
          (pf,(fns'',(s,lno'))) =>
          case check_end s of
            None => raise Fail (format_failure lno' "subproof not terminated with contradiction id")
          | Some n => (Inr (Lstep (Con c pf n)), (fns'', lno')))
            ` |> append_prog

Theorem parse_top_spec:
  !ss fd fdv lines lno lnov fs fns fnsv.
  PAIR_TYPE (STRING_TYPE --> a --> OPTION_TYPE (PAIR_TYPE NUM a)) a fns fnsv ∧
  NUM lno lnov ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_top" (get_ml_prog_state()))
    [fnsv; fdv; lnov]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         &(
            case parse_top fns ss of
              NONE => F
            | SOME (res,fns',rest) =>
                (PAIR_TYPE
                  (SUM_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NPBC_CHECK_SSTEP_TYPE)
                  (PAIR_TYPE
                  (PAIR_TYPE (STRING_TYPE --> a --> OPTION_TYPE (PAIR_TYPE NUM a)) a)
                  NUM)) (res,fns',lno') v ∧
                MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_top fns ss = NONE))
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
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    metis_tac[Fail_exn_def,STDIO_INSTREAM_LINES_refl_gc])>>
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
  Cases_on`parse_lstep_aux fns h`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    simp[PAIR_TYPE_def,SUM_TYPE_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  PairCases_on`x`>>
  Cases_on`x0`>>
  fs[PAIR_TYPE_def,SUM_TYPE_def]
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
         SEP_EXISTS k lines' acc' fns' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))
              (PAIR_TYPE (PAIR_TYPE (STRING_TYPE --> a --> OPTION_TYPE (PAIR_TYPE NUM a)) a)
              (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
                NUM)) (acc',fns',s,lno') v ∧
            parse_lsteps_aux (x1,x2) (MAP toks_fast ls) [] = SOME(acc',fns',s,rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_lsteps_aux (x1,x2) (MAP toks_fast ls) [] = NONE))
      )`
    >- (
      xapp>>xsimpl>>
      asm_exists_tac>>xsimpl>>
      qexists_tac`emp`>>qexists_tac`ls`>>
      qexists_tac`forwardFD fs fd k`>>
      qexists_tac`(x1,x2)`>>
      qexists_tac`fd`>>xsimpl>>
      qexists_tac`[]`>>
      simp[LIST_TYPE_def,PAIR_TYPE_def]>>
      asm_exists_tac>>xsimpl>>
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
    Cases_on`check_end s`>>fs[OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      simp[Fail_exn_def]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[NPBC_CHECK_SSTEP_TYPE_def,NPBC_CHECK_LSTEP_TYPE_def,SUM_TYPE_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  rpt xlet_autop>>
  xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' acc' fns' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM)) (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))))
              (PAIR_TYPE (PAIR_TYPE (STRING_TYPE --> a --> OPTION_TYPE (PAIR_TYPE NUM a)) a)
              NUM) (acc',fns',lno') v ∧
            parse_red_aux (x1,x2) t [] = SOME(acc',fns',rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_red_aux (x1,x2) t [] = NONE))
      )`
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`emp`>>qexists_tac`ls`>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`(x1,x2)`>>xsimpl>>
    qexists_tac`fd`>>xsimpl>>
    qexists_tac`[]`>>simp[LIST_TYPE_def,PAIR_TYPE_def]>>
    asm_exists_tac>>xsimpl>>
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
  simp[NPBC_CHECK_SSTEP_TYPE_def,NPBC_CHECK_LSTEP_TYPE_def,SUM_TYPE_def]>>
  metis_tac[STDIO_INSTREAM_LINES_refl_gc]
QED

val check_unsat'' = process_topdecs `
  fun check_unsat'' fns fd lno obj core fml inds id =
    case parse_top fns fd lno of
      (Inl s, (fns', lno)) =>
        (fml, s)
    | (Inr step, (fns', lno')) =>
      (case check_sstep_arr lno' step obj core fml inds id of
        (fml', (id', inds')) =>
        check_unsat'' fns' fd lno' obj core fml' inds' id')` |> append_prog

(* Repeatedly parse a line and run the sstep checker
  TODO: may need more information *)
Definition parse_and_run_def:
  parse_and_run f_ns ss obj core fml inds id =
  case parse_top f_ns ss of NONE => NONE
  | SOME (INL s, f_ns', rest) => SOME (fml, s)
  | SOME (INR step, f_ns', rest) =>
    (case check_sstep_list step obj core fml inds id of
      SOME (fml', id', inds') =>
        parse_and_run f_ns' rest obj core fml' inds' id'
    | res => NONE)
Termination
  WF_REL_TAC `measure (LENGTH o FST o SND)`>>
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

Theorem STDIO_INSTREAM_LINES_ARRAY_refl:
  (STDIO A *
  INSTREAM_LINES B C D E * ARRAY arr arrv ==>>
  STDIO A *
  INSTREAM_LINES B C D E * ARRAY arr arrv) ∧
  (STDIO A *
  INSTREAM_LINES B C D E * ARRAY arr arrv ==>>
  STDIO A *
  INSTREAM_LINES B C D E * ARRAY arr arrv * GC)
Proof
  xsimpl
QED

Theorem check_unsat''_spec:
  ∀fns ss obj core fmlls inds id fmlv fmllsv indsv idv fd fdv lines lno lnov fs fnsv objv corev.
  PAIR_TYPE (STRING_TYPE --> a --> OPTION_TYPE (PAIR_TYPE NUM a)) a fns fnsv ∧
  NUM lno lnov ∧
  NUM id idv ∧
  SPTREE_SPT_TYPE UNIT_TYPE core corev ∧
  OPTION_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) obj objv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat''" (get_ml_prog_state()))
    [fnsv; fdv; lnov; objv; corev; fmlv; indsv; idv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs * ARRAY fmlv fmllsv)
    (POSTve
      (λv.
         SEP_EXISTS k lines' lno' fmlv' fmllsv'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         ARRAY fmlv' fmllsv' *
         &(
          case parse_and_run fns ss obj core fmlls inds id of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) res v
          ))
      (λe.
         SEP_EXISTS k lines' fmlv' fmllsv'.
           ARRAY fmlv' fmllsv' *
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_and_run fns ss obj core fmlls inds id = NONE)))
Proof
  ho_match_mp_tac (fetch "-" "parse_and_run_ind")>>rw[]>>
  xcf "check_unsat''" (get_ml_prog_state ())>>
  simp[Once parse_and_run_def]>>
  Cases_on`parse_top fns (MAP toks_fast lines)`>>fs[]
  >- ((* parse_top NONE *)
    xlet `(POSTe e.
         SEP_EXISTS k lines' fmlv' fmllsv'.
           ARRAY fmlv' fmllsv' *
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e))`
    >- (
      xapp>>xsimpl>>
      asm_exists_tac>>simp[]>>
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
            case parse_top fns (MAP toks_fast lines) of
              NONE => F
            | SOME (res,fns',rest) =>
                (PAIR_TYPE
                  (SUM_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NPBC_CHECK_SSTEP_TYPE)
                  (PAIR_TYPE
                  (PAIR_TYPE (STRING_TYPE --> a --> OPTION_TYPE (PAIR_TYPE NUM a)) a)
                  NUM)) (res,fns',lno') v ∧
                MAP toks_fast lines' = rest))`
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    qexists_tac`ARRAY fmlv fmllsv`>>qexists_tac`lines`>>simp[]>>
    qexists_tac`fs`>>qexists_tac`fd`>>xsimpl>>
    TOP_CASE_TAC>>fs[]>>rw[]>>
    TOP_CASE_TAC>>fs[]>>
    fs[OPTION_TYPE_def,PAIR_TYPE_def]>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    xsimpl>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  PairCases_on`x`>>
  Cases_on`x0`>>fs[SUM_TYPE_def,PAIR_TYPE_def]
  >- (
    (* INL *)
    xmatch>>
    xcon>>xsimpl
    >- metis_tac[STDIO_INSTREAM_LINES_refl_gc]>>
    simp[Once parse_and_run_def])>>
  (* INR *)
  xmatch>>
  xlet_auto
  >- (
    xsimpl>>reverse (rw[])
    >-
      metis_tac[ARRAY_refl]>>
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
  xmatch>>
  xapp>>
  xsimpl>>
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

val fill_arr = process_topdecs`
  fun fill_arr arr i ls =
    case ls of [] => arr
    | (v::vs) =>
      fill_arr (Array.updateResize arr None i (Some v)) (i+1) vs` |> append_prog

Theorem fill_arr_spec:
  ∀ls lsv arrv arrls arrlsv i iv.
  NUM i iv ∧
  LIST_TYPE constraint_TYPE ls lsv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) arrls arrlsv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"fill_arr"(get_ml_prog_state()))
  [arrv; iv; lsv]
  (ARRAY arrv arrlsv)
  (POSTv resv.
  SEP_EXISTS arrlsv'. ARRAY resv arrlsv' *
    & LIST_REL (OPTION_TYPE constraint_TYPE)
    (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) arrls (enumerate i ls)) arrlsv')
Proof
  Induct>>rw[]>>
  xcf "fill_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,miscTheory.enumerate_def]>>
  xmatch
  >- (xvar>>xsimpl)>>
  rpt xlet_autop >>
  xlet_auto>>
  xapp>>fs[]>>
  match_mp_tac LIST_REL_update_resize>>fs[]>>
  simp[OPTION_TYPE_def]
QED

Definition rev_enum_def:
  rev_enum (s:num) (e:num) acc =
  if s < e then
    rev_enum (s+1) e (s::acc)
  else
    acc
Termination
  WF_REL_TAC`measure (λ(s,e,acc). e-s)`
End

Theorem rev_enum_rev_enumerate:
  ∀fml k acc.
  rev_enum k (LENGTH fml + k) acc =
  REVERSE (MAP FST (enumerate k fml)) ++ acc
Proof
  Induct>>rw[Once rev_enum_def]>>
  simp[miscTheory.enumerate_def]>>
  first_x_assum(qspec_then`k+1` mp_tac)>>
  simp[ADD1]
QED

val _ = translate rev_enum_def;

Definition rev_enum_full_def:
  rev_enum_full k fml =
  rev_enum k (LENGTH fml + k) []
End

Theorem rev_enum_full_rev_enumerate:
  rev_enum_full k fml =
  REVERSE (MAP FST (enumerate k fml))
Proof
  rw[rev_enum_full_def,rev_enum_rev_enumerate]
QED

val _ = translate rev_enum_full_def;

val res = translate parse_conc_unsat_def;
val parse_conc_unsat_side = Q.prove(
  `∀x. parse_conc_unsat_side x <=> T`,
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC) |> update_precondition;

val res = translate parse_conc_def;

Definition parse_conc_full_def:
  parse_conc_full s y z n =
  case y of NONE => NONE
  | SOME y =>
  case z of NONE => NONE
  | SOME z =>
  case n of SOME r => NONE
  | NONE =>
    parse_conc s y z
End

val res = translate parse_conc_full_def;

val check_conc = process_topdecs`
  fun check_conc fd s fml =
  let
    val y = TextIO.b_inputLineTokens fd blanks tokenize_fast
    val z = TextIO.b_inputLineTokens fd blanks tokenize_fast
    val n = TextIO.b_inputLineTokens fd blanks tokenize_fast
  in
    case parse_conc_full s y z n of
      None => Inl "Unable to parse output / conclusion section"
    | Some n => Inr (check_contradiction_fml_arr fml n)
  end` |> append_prog;

Theorem check_conc_spec:
  (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) s sv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_conc" (get_ml_prog_state()))
    [fdv; sv; fmlv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs * ARRAY fmlv fmllsv)
    (POSTv v.
         SEP_EXISTS k lines' lno' fmlv' fmllsv' res n.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         ARRAY fmlv fmllsv *
         &(
          SUM_TYPE STRING_TYPE BOOL res v ∧
          case res of
            INR b => b = check_contradiction_fml_list fmlls n
          | INL l => T))
Proof
  rw[]>>
  xcf "check_conc" (get_ml_prog_state ())>>
  xlet ‘(POSTv v.
      SEP_EXISTS k.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES fd fdv (TL lines) (forwardFD fs fd k) *
          ARRAY fmlv fmllsv *
          &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
            (OPTION_MAP (MAP tokenize_fast ∘ tokens blanks) (oHD lines)) v)’
  >- (
    xapp_spec b_inputLineTokens_specialize
    \\ qexists_tac ‘ARRAY fmlv fmllsv’
    \\ xsimpl
    \\ metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc]) >>
  xlet ‘(POSTv v.
      SEP_EXISTS k.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES fd fdv (TL (TL lines)) (forwardFD fs fd k) *
          ARRAY fmlv fmllsv *
          &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
            (OPTION_MAP (MAP tokenize_fast ∘ tokens blanks) (oHD (TL lines))) v)’
  >- (
    xapp_spec b_inputLineTokens_specialize
    \\ qexists_tac ‘ARRAY fmlv fmllsv’
    \\ xsimpl
    \\ metis_tac[forwardFD_o,STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc])>>
  xlet ‘(POSTv v.
      SEP_EXISTS k.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES fd fdv (TL (TL (TL lines))) (forwardFD fs fd k) *
          ARRAY fmlv fmllsv *
          &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
            (OPTION_MAP (MAP tokenize_fast ∘ tokens blanks) (oHD (TL (TL lines)))) v)’
  >- (
    xapp_spec b_inputLineTokens_specialize
    \\ qexists_tac ‘ARRAY fmlv fmllsv’
    \\ xsimpl
    \\ metis_tac[forwardFD_o,STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc])>>
  xlet_autop>>
  rename1`parse_conc_full s xx yy nn`>>
  Cases_on`parse_conc_full s xx yy nn`>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xcon>>xsimpl>>
    qexists_tac`k`>>
    qexists_tac`TL (TL (TL lines))`>>
    xsimpl>>
    qexists_tac`INL (strlit "Unable to parse output / conclusion section")`>>
    simp[SUM_TYPE_def])>>
  xlet_autop>>
  xcon>>
  xsimpl>>
  qexists_tac`k`>>
  qexists_tac`TL (TL (TL lines))`>>
  xsimpl>>
  qexists_tac`INR (check_contradiction_fml_list fmlls x)`>>
  simp[SUM_TYPE_def]>>
  metis_tac[]
QED

val check_unsat' = process_topdecs `
  fun check_unsat' fns fd lno fml =
  let
    val id = List.length fml + 1
    val arr = Array.array (2*id) None
    val arr = fill_arr arr 1 fml
    val inds = rev_enum_full 1 fml
    val n = None
    val l = Ln
  in
    (case check_unsat'' fns fd lno n l arr inds id of
      (fml', s) =>
        check_conc fd s fml')
    handle Fail s => Inl s
  end` |> append_prog

Theorem parse_and_run_check_ssteps_list:
  ∀f_ns lines obj core fml inds id fml' s.
  parse_and_run f_ns lines obj core fml inds id = SOME (fml',s) ⇒
  ∃ss id' inds'.
  check_ssteps_list ss obj core fml inds id = SOME (fml',id',inds')
Proof
  ho_match_mp_tac parse_and_run_ind>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once parse_and_run_def]>>
  every_case_tac>>fs[]
  >-
    (rw[]>>qexists_tac`[]`>>EVAL_TAC>>metis_tac[])>>
  rw[]>>
  first_x_assum drule>>
  rw[]>>
  qexists_tac`y::ss`>>
  simp[npbc_listTheory.check_ssteps_list_def]
QED

Theorem check_unsat'_spec:
  PAIR_TYPE (STRING_TYPE --> a --> OPTION_TYPE (PAIR_TYPE NUM a)) a fns fnsv ∧
  NUM lno lnov ∧
  LIST_TYPE constraint_TYPE fml fmlv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat'" (get_ml_prog_state()))
    [fnsv; fdv; lnov; fmlv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTv v.
         SEP_EXISTS k lines' lno' fmlv' fmllsv' res.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         ARRAY fmlv' fmllsv' *
         &(
          SUM_TYPE STRING_TYPE BOOL res v ∧
          (res = INR T ⇒ unsatisfiable (set fml))))
Proof
  rw[]>>
  xcf "check_unsat'" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  qmatch_goalsub_abbrev_tac`ARRAY av avs`>>
  `LIST_REL (OPTION_TYPE constraint_TYPE) (REPLICATE (2 * (LENGTH fml + 1)) NONE) avs` by
    simp[Abbr`avs`,LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
  xlet`
  (POSTv resv.
    SEP_EXISTS arrlsv'. ARRAY resv arrlsv' *
      STDIO fs * INSTREAM_LINES fd fdv lines fs *
      & LIST_REL (OPTION_TYPE constraint_TYPE)
      (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i)
      (REPLICATE (2 * (LENGTH fml + 1)) NONE)
      (enumerate 1 fml)) arrlsv')`
  >- (
    xapp>>
    xsimpl>>
    asm_exists_tac>>xsimpl>>
    asm_exists_tac>>xsimpl)>>
  rpt xlet_autop>>
  `OPTION_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) NONE
     (Conv (SOME (TypeStamp "None" 2)) [])` by
    EVAL_TAC>>
  `SPTREE_SPT_TYPE UNIT_TYPE LN (Conv (SOME (TypeStamp "Ln" 18)) [])` by
    EVAL_TAC>>
  qmatch_asmsub_abbrev_tac`LIST_REL _ fmlls fmllsv`>>
  qmatch_asmsub_abbrev_tac`LIST_TYPE _ inds indsv`>>
  Cases_on`
    parse_and_run fns (MAP toks_fast lines) NONE LN fmlls inds (LENGTH fml + 1)`
  >- (
    xhandle`POSTe e.
      SEP_EXISTS k lines' fmlv' fmllsv'.
      ARRAY fmlv' fmllsv' *
      STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
      &(Fail_exn e)`
    >- (
      xlet`POSTe e.
         SEP_EXISTS k lines' fmlv' fmllsv'.
           ARRAY fmlv' fmllsv' *
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e)`
      >- (
        xapp>>xsimpl>>
        rpt(asm_exists_tac>>simp[])>>
        qexists_tac`emp`>>
        qexists_tac`lines`>>
        qexists_tac`fs`>>
        qexists_tac`fd`>>
        xsimpl>>
        metis_tac[STDIO_INSTREAM_LINES_refl,ARRAY_STDIO_INSTREAM_LINES_refl])>>
      xsimpl)
    >>
      fs[Fail_exn_def]>>
      xcases>>
      xcon>> xsimpl>>
      CONV_TAC (RESORT_EXISTS_CONV (sort_vars ["x''''"]))>>
      qexists_tac`INL s`>>
      simp[SUM_TYPE_def]>>
      qexists_tac`k`>>qexists_tac`lines'`>>
      qexists_tac`fmlv'`>>qexists_tac`fmllsv'`>>
      xsimpl)>>
  xhandle`POSTv v. SEP_EXISTS k lines' lno' fmlv' fmllsv' res.
             STDIO (forwardFD fs fd k) *
             INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
             ARRAY fmlv' fmllsv' *
             &(SUM_TYPE STRING_TYPE BOOL res v ∧
              (res = INR T ⇒ unsatisfiable (set fml)))`
  >- (
    xlet`POSTv v.
         SEP_EXISTS k lines' lno' fmlv' fmllsv'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
         ARRAY fmlv' fmllsv' *
         &(
          case parse_and_run fns (MAP toks_fast lines) NONE LN fmlls inds (LENGTH fml+1) of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) res v
          )`
    >- (
      xapp>>xsimpl>>
      rpt(asm_exists_tac>>simp[])>>
      qexists_tac`emp`>>
      qexists_tac`lines`>>
      qexists_tac`fs`>>
      qexists_tac`fd`>>
      xsimpl>>
      rw[]>>
      metis_tac[STDIO_INSTREAM_LINES_ARRAY_refl])>>
    Cases_on`x`>>
    fs[PAIR_TYPE_def]>>
    xmatch>>xapp>>
    xsimpl>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    qexists_tac`emp`>>
    qexists_tac`lines'`>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>
    xsimpl>>
    rw[]>>
    asm_exists_tac>>simp[]>>
    simp[GSYM PULL_EXISTS]>>
    CONJ_TAC >- (
      drule parse_and_run_check_ssteps_list>>
      rw[]>>fs[]>>
      match_mp_tac (GEN_ALL npbc_listTheory.check_ssteps_list_unsat)>>
      first_x_assum (irule_at Any)>>
      unabbrev_all_tac>>
      gs[rev_enum_full_rev_enumerate]>>
      metis_tac[])>>
    simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_ARRAY_refl])>>
  xsimpl
QED

val r = translate check_f_line_def;

val headertrm = rconc (EVAL``toks_fast (strlit"pseudo-Boolean proof version 2.0")``);

Definition parse_header_line_fast_def:
  parse_header_line_fast s ⇔
  s = ^headertrm
End

val r = translate parse_header_line_fast_def;

Definition check_header_full_def:
  check_header_full s (s':(mlstring + int) list option) =
  case s of NONE => SOME 0
  | SOME s =>
  case s' of NONE => SOME 1
  | SOME s' =>
  if parse_header_line_fast s then
    if check_f_line s' then NONE
    else SOME (1:num)
  else SOME 0
End

val r = translate check_header_full_def;

val check_header = process_topdecs`
  fun check_header fd =
  let
    val s1 = TextIO.b_inputLineTokens fd blanks tokenize_fast
    val s2 = TextIO.b_inputLineTokens fd blanks tokenize_fast
  in
  check_header_full s1 s2
  end` |> append_prog;

val b_inputLineTokens_specialize =
  b_inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize_fast`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_fast_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_v_thm,tokenize_fast_v_thm,blanks_def] ;

Theorem check_header_spec:
  !ss fd fdv lines fs.
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_header" (get_ml_prog_state()))
    [fdv]
    (STDIO fs * INSTREAM_LINES fd fdv lines fs)
    (POSTv v.
       SEP_EXISTS k lines' res.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
       &(OPTION_TYPE NUM res v))
Proof
  xcf "check_header" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xlet ‘(POSTv v.
      SEP_EXISTS k.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES fd fdv (TL lines) (forwardFD fs fd k) *
          &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
            (OPTION_MAP (MAP tokenize_fast ∘ tokens blanks) (oHD lines)) v)’
  >- (
    xapp_spec b_inputLineTokens_specialize
    \\ qexists_tac ‘emp’
    \\ xsimpl)>>
  xlet ‘(POSTv v.
      SEP_EXISTS k.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES fd fdv (TL (TL lines)) (forwardFD fs fd k) *
          &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
            (OPTION_MAP (MAP tokenize_fast ∘ tokens blanks) (oHD (TL lines))) v)’
  >- (
    xapp_spec b_inputLineTokens_specialize
    \\ qexists_tac ‘emp’
    \\ xsimpl
    \\ metis_tac[forwardFD_o,STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc]
    )>>
  xapp>>
  xsimpl>>
  metis_tac[forwardFD_o,STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc]
QED

Definition result_string_def:
  result_string success_string ob =
   case ob of
    INR b =>
      if b then INR success_string
      else INL (strlit "Proof checking succeeded but did not derive contradiction\n")
  | INL v => INL v
End

val r = translate result_string_def;

Definition notfound_string_def:
  notfound_string f = concat[strlit"c Input file: ";f;strlit" no such file or directory\n"]
End

val r = translate notfound_string_def;

val check_unsat_top = process_topdecs `
  fun check_unsat_top fns success_string fml fname =
  let
    val fd = TextIO.b_openIn fname
  in
    case check_header fd of
      Some n =>
      (TextIO.b_closeIn fd;
      Inl (format_failure n "Unable to parse header"))
    | None =>
      let val res =
        result_string success_string (check_unsat' fns fd 2 fml)
        val close = TextIO.b_closeIn fd;
      in
        res
      end
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)` |> append_prog;

Theorem STDIO_INSTREAM_LINES_refl_more_gc:
  STDIO A *
  INSTREAM_LINES B C D E * rest ==>>
  STDIO A *
  INSTREAM_LINES B C D E * GC
Proof
  xsimpl
QED

Theorem check_unsat_top_spec:
  PAIR_TYPE (STRING_TYPE --> a --> OPTION_TYPE (PAIR_TYPE NUM a)) a fns fnsv ∧
  LIST_TYPE constraint_TYPE fml fmlv ∧
  FILENAME f fv ∧
  hasFreeFD fs ∧
  STRING_TYPE success successv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_top"(get_ml_prog_state()))
  [fnsv; successv; fmlv; fv]
  (STDIO fs)
  (POSTv v.
     STDIO fs *
     SEP_EXISTS res.
     &(
      SUM_TYPE STRING_TYPE STRING_TYPE res v ∧
      (∀s. res = INR s ⇒
        (s = success ∧
        unsatisfiable (set fml)))))
Proof
  xcf"check_unsat_top"(get_ml_prog_state()) >>
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
      qexists_tac`INL (notfound_string f)`>>
      simp[SUM_TYPE_def])>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval` \\ xsimpl >>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec (SOME b_openIn_spec_lines) \\ xsimpl >>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES fd fdv lines fss`>>
  xlet`POSTv v.
    SEP_EXISTS k lines' res.
    STDIO (forwardFD fss fd k) *
    INSTREAM_LINES fd fdv lines' (forwardFD fss fd k) *
    &OPTION_TYPE NUM res v`
  >- (
    xapp>>
    qexists_tac`emp`>>
    xsimpl>>
    metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc,STAR_COMM])>>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES fd fdv _ fsss`>>
  reverse (Cases_on`res`)>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    xlet `POSTv v. STDIO fs`
    >- (
      xapp_spec b_closeIn_spec_lines >>
      xsimpl>>
      qexists_tac `emp`>>
      qexists_tac `lines'` >>
      qexists_tac `fsss`>>
      qexists_tac `fd` >>
      conj_tac THEN1
        (unabbrev_all_tac
        \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
        \\ imp_res_tac fsFFIPropsTheory.STD_streams_nextFD \\ fs []) >>
      xsimpl>>
      `validFileFD fd fsss.infds` by
        (unabbrev_all_tac>> simp[validFileFD_forwardFD]
         \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
         \\ match_mp_tac validFileFD_nextFD \\ fs []) >>
      xsimpl >> rw [] >>
      unabbrev_all_tac>>xsimpl>>
      simp[forwardFD_ADELKEY_same]>>
      DEP_REWRITE_TAC [fsFFIPropsTheory.openFileFS_ADELKEY_nextFD]>>
      xsimpl>>
      imp_res_tac (DECIDE ``n<m:num ==> n <= m``) >>
      imp_res_tac fsFFIPropsTheory.nextFD_leX \\ fs [])>>
    xlet_autop>>
    xcon>>
    xsimpl>>
    metis_tac[SUM_TYPE_def,sum_distinct])>>
  xlet`POSTv v. SEP_EXISTS k lines' lno' fmlv' fmllsv' res.
          STDIO (forwardFD fsss fd k) *
          INSTREAM_LINES fd fdv lines' (forwardFD fsss fd k) *
          &(SUM_TYPE STRING_TYPE BOOL res v ∧
           (res = INR T ⇒ unsatisfiable (set fml)))`
  >- (
    xapp>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    metis_tac[STDIO_INSTREAM_LINES_refl_more_gc,STDIO_INSTREAM_LINES_refl])>>
  xlet_autop>>
  xlet `POSTv v. STDIO fs`
  >- (
    xapp_spec b_closeIn_spec_lines >>
    xsimpl>>
    qexists_tac `emp`>>
    qexists_tac `lines'` >>
    qexists_tac `forwardFD fsss fd k'`>>
    qexists_tac `fd` >>
    conj_tac THEN1
      (unabbrev_all_tac
      \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
      \\ imp_res_tac fsFFIPropsTheory.STD_streams_nextFD \\ fs []) >>
    xsimpl>>
    `validFileFD fd (forwardFD fsss fd k').infds` by
      (unabbrev_all_tac>> simp[validFileFD_forwardFD]
       \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
       \\ match_mp_tac validFileFD_nextFD \\ fs []) >>
    xsimpl >> rw [] >>
    unabbrev_all_tac>>xsimpl>>
    simp[forwardFD_ADELKEY_same]>>
    DEP_REWRITE_TAC [fsFFIPropsTheory.openFileFS_ADELKEY_nextFD]>>
    xsimpl>>
    imp_res_tac (DECIDE ``n<m:num ==> n <= m``) >>
    imp_res_tac fsFFIPropsTheory.nextFD_leX \\ fs [])>>
  xvar>>xsimpl>>
  asm_exists_tac>>fs[]>>
  Cases_on`res`>>gs[result_string_def]
QED

(* shared normalization stuff
  different top-level may use slightly different normalization
*)
val r = translate flip_coeffs_def;
val r = translate pbc_ge_def;
val r = translate normalise_def;

val r = translate convert_pbf_def;
val r = translate full_normalise_def;

val _ = export_theory();
