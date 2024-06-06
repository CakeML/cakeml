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

val r = translate (hashNon_def |> SIMP_RULE std_ss [non_list_def]);
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

val r = translate parse_subst_aux_def;

val r = translate parse_subst_def;

val r = translate pbcTheory.lit_var_def;
val r = translate compact_lhs_def;
val r = translate term_le_def;
val r = translate mk_coeff_def;
val r = translate normalise_lhs_def;

val r = translate mergesortTheory.sort2_def;
val r = translate mergesortTheory.sort3_def;
val r = translate mergesortTheory.merge_def;
val r = translate DROP_def;
val r = translate (mergesortTheory.mergesortN_def |> SIMP_RULE std_ss [DIV2_def]);

Triviality mergesortn_ind:
  mergesortn_ind (:'a)
Proof
  once_rewrite_tac [fetch "-" "mergesortn_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD, DIV2_def]
QED

val _ = mergesortn_ind |> update_precondition;

val r = translate mergesortTheory.mergesort_def;

val r = translate mergesortTheory.sort2_tail_def;
val r = translate mergesortTheory.sort3_tail_def;
val r = translate mergesortTheory.merge_tail_def;
val r = translate (mergesortTheory.mergesortN_tail_def |> SIMP_RULE std_ss [DIV2_def]);

Triviality mergesortn_tail_ind:
  mergesortn_tail_ind (:'a)
Proof
  once_rewrite_tac [fetch "-" "mergesortn_tail_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD, DIV2_def]
QED

val _ = mergesortn_tail_ind |> update_precondition;

val r = translate mergesortTheory.mergesort_tail_def;

val r = translate pbc_to_npbc_def;
val pbc_to_npbc_side = Q.prove(
  `∀x. pbc_to_npbc_side x <=> T`,
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_constraint_LHS_def;

val r = translate pbcTheory.map_pbc_def;
val r = translate map_f_ns_def;
val r = translate parse_constraint_npbc_def;

val r = translate parse_red_header_def;

val r = translate parse_constraint_npbc_2_def;
val r = translate strip_numbers_end_def;
val strip_numbers_end_side_def = fetch "-" "strip_numbers_end_side_def";
val strip_numbers_end_side = Q.prove(
  `∀x y. strip_numbers_end_side x y <=> T`,
  Induct>>rw[Once strip_numbers_end_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_rup_def;

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

Definition fromChars_range_unsafe_tail_def:
  fromChars_range_unsafe_tail l n       str mul acc =
  if n ≤ l then acc
  else
    let n1 = n - 1 in
    fromChars_range_unsafe_tail l n1 str (mul * 10)  (acc + fromChar_unsafe (strsub str n1) * mul)
End

Theorem fromChars_range_unsafe_tail_eq:
  ∀n l s mul acc.
  fromChars_range_unsafe_tail l (n+l) s mul acc = (fromChars_range_unsafe l n s) * mul + acc
Proof
  Induct>>rw[Once fromChars_range_unsafe_tail_def,fromChars_range_unsafe_def]>>
  gvs[ADD1]
QED

Theorem fromChars_range_unsafe_alt:
  fromChars_range_unsafe l n s = fromChars_range_unsafe_tail l (n + l) s 1 0
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

val _ = translate is_numeric_def;
val _ = translate is_num_prefix_def;
val _ = translate int_start_def;

val int_start_side = Q.prove(
  `∀x. int_start_side x = T`,
  EVAL_TAC >> fs[]
  ) |> update_precondition;

val _ = translate tokenize_fast_def;

Definition not_is_empty_def:
  not_is_empty v ⇔ v ≠ []
End

val _ = translate not_is_empty_def;

val parse_lsteps_aux = process_topdecs`
  fun parse_lsteps_aux f_ns fd lno acc =
    case TextIO.b_inputLineTokens #"\n" fd blanks tokenize_fast of
      None => raise Fail (format_failure lno "reached EOF while reading PBP steps")
    | Some s =>
    case parse_lstep_aux f_ns s of
      None => (List.rev acc,(f_ns,(s,lno+1)))
    | Some (Inl step,f_ns') =>
        parse_lsteps_aux f_ns' fd (lno+1) (step::acc)
    | Some (Inr (c,s),f_ns') =>
      if not_is_empty s then
        raise Fail (format_failure (lno+1) "only contradiction steps allowed in nested proof steps")
      else
        (case parse_lsteps_aux f_ns' fd (lno+1) [] of
          (pf,(f_ns'',(s,lno'))) =>
          case check_end s of
            None => raise Fail (format_failure lno' "subproof not terminated with contradiction id")
          | Some id =>
            parse_lsteps_aux f_ns'' fd (lno'+1) (Con c pf id::acc))`
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
  INSTREAM_LINES c B C D E ==>>
  STDIO A *
  INSTREAM_LINES c B C D E
Proof
  xsimpl
QED

Theorem STDIO_INSTREAM_LINES_refl_gc:
  STDIO A *
  INSTREAM_LINES c B C D E ==>>
  STDIO A *
  INSTREAM_LINES c B C D E * GC
Proof
  xsimpl
QED

Theorem not_is_empty_eq:
  not_is_empty v ⇔
  ¬is_empty v
Proof
  EVAL_TAC>>
  Cases_on`v`>>fs[]>>
  EVAL_TAC>>
  simp[]
QED

Overload "fns_TYPE" = ``λa. PAIR_TYPE (STRING_TYPE --> a --> OPTION_TYPE (PAIR_TYPE NUM a)) a``

Theorem parse_lsteps_aux_spec:
  ∀fns ss acc fd fdv lines lno lnov accv fs fnsv.
  fns_TYPE a fns fnsv ∧
  NUM lno lnov ∧
  LIST_TYPE (NPBC_CHECK_LSTEP_TYPE) acc accv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_lsteps_aux" (get_ml_prog_state()))
    [fnsv; fdv; lnov; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' acc' fns' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))
              (PAIR_TYPE (fns_TYPE a)
              (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
                NUM)) (acc',fns',s,lno') v ∧
            parse_lsteps_aux fns ss acc = SOME(acc',fns',s,rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
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
            INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
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
            INSTREAM_LINES #"\n" fd fdv ls (forwardFD fs fd k) *
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
    xlet_auto >- (
      xsimpl>>
      simp (eq_lemmas()))>>
    rename1`is_empty tt`>>
    reverse (Cases_on`is_empty tt`>>fs[not_is_empty_eq])
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
                    INSTREAM_LINES #"\n" fd fdv lines'
                      (forwardFD (forwardFD fs fd k) fd k') *
                      &(
            PAIR_TYPE (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))
              (PAIR_TYPE (fns_TYPE a)
              (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
              NUM)) (acc',fns',s',lno') v ∧
            parse_lsteps_aux r ss [] = SOME(acc',fns',s',rest) ∧
            MAP toks_fast lines' = rest))
             (λe.
                  SEP_EXISTS k' lines'.
                    STDIO (forwardFD (forwardFD fs fd k) fd k') *
                    INSTREAM_LINES #"\n" fd fdv lines'
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

val r = translate check_end_opt_def;

val check_end_opt_side = Q.prove(
  `∀x. check_end_opt_side x <=> T`,
  EVAL_TAC>>rw[]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate parse_red_body_def;

val r = translate mk_acc_def;

val parse_red_aux = process_topdecs`
  fun parse_red_aux f_ns fd lno acc =
    case parse_lsteps_aux f_ns fd lno [] of
      (pf,(f_ns',(s,lno'))) =>
      let val acc' = mk_acc pf acc in
        case parse_red_body s of
          None => raise Fail (format_failure lno' "unable to parse subproof")
        | Some (Inl res) => (res,(List.rev acc', (f_ns', lno')))
        | Some (Inr ind) =>
          (case parse_lsteps_aux f_ns' fd lno' [] of
            (pf,(f_ns'',(s,lno''))) =>
            case check_end s of
              None => raise Fail (format_failure lno'' "subproof not terminated with contradiction id")
          | Some id =>
              parse_red_aux f_ns'' fd lno'' ((Some (ind,id),pf)::acc')
              )
      end` |> append_prog

Theorem parse_red_aux_spec:
  ∀fns ss acc fd fdv lines lno lnov accv fs fnsv.
  fns_TYPE a fns fnsv ∧
  NUM lno lnov ∧
  LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM)) (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))) acc accv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_red_aux" (get_ml_prog_state()))
    [fnsv; fdv; lnov; accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' res acc' fns' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (OPTION_TYPE NUM)
            (PAIR_TYPE (LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM)) (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))))
              (PAIR_TYPE (fns_TYPE a)
                NUM)) (res,acc',fns',lno') v ∧
            parse_red_aux fns ss acc = SOME(res,acc',fns',rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
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
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))
              (PAIR_TYPE (fns_TYPE a)
              (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
                NUM)) (acc',fns',s,lno') v ∧
            parse_lsteps_aux fns (MAP toks_fast lines) [] = SOME(acc',fns',s,rest) ∧
            MAP toks_fast lines' = rest))
     (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
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
    rpt xlet_autop>>
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
         INSTREAM_LINES #"\n" fd fdv lines'' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))
              (PAIR_TYPE (fns_TYPE a)
              (PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
                NUM))
              (acc',fns'',s,lno') v ∧
            parse_lsteps_aux fns' rest [] = SOME(acc',fns'',s,rest') ∧
            MAP toks_fast lines'' = rest'))
      (λe.
         SEP_EXISTS k lines''.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines'' (forwardFD fs fd k) *
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

Theorem is_empty_thm:
  is_empty v ⇔
    case v of [] => T | _ => F
Proof
  EVAL_TAC>>Cases_on`v`>>fs[mlvectorTheory.length_def]
QED

val res = translate is_empty_thm;

val res = translate reduce_pf_def;

val parse_sstep = process_topdecs`
  fun parse_sstep fns fd lno =
    case TextIO.b_inputLineTokens #"\n" fd blanks tokenize_fast of
      None =>
      raise Fail (format_failure lno "Unexpected EOF when parsing proof steps")
    | Some s =>
    (case parse_lstep_aux fns s of
      None => (Inl s, (fns, lno+1))
    | Some (Inl step,fns') => (Inr (Lstep step),(fns',lno+1))
    | Some (Inr (c,s),fns') =>
        case parse_red_aux fns' fd (lno+1) [] of
        (res,(pf,(fns'',lno'))) =>
        (case reduce_pf s pf res of
          None => (Inr (Red c s pf res),(fns'',lno'))
        | Some ((pf,n)) => (Inr (Lstep (Con c pf n)), (fns'', lno')))
        )` |> append_prog

Theorem parse_sstep_spec:
  !ss fd fdv lines lno lnov fs fns fnsv.
  fns_TYPE a fns fnsv ∧
  NUM lno lnov ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_sstep" (get_ml_prog_state()))
    [fnsv; fdv; lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            case parse_sstep fns ss of
              NONE => F
            | SOME (res,fns',rest) =>
                (PAIR_TYPE
                  (SUM_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NPBC_CHECK_SSTEP_TYPE)
                  (PAIR_TYPE
                  (fns_TYPE a)
                  NUM)) (res,fns',lno') v ∧
                MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_sstep fns ss = NONE))
      )
Proof
  rpt strip_tac>>
  xcf "parse_sstep" (get_ml_prog_state ())>>
  Cases_on`ss`>>simp[parse_sstep_def]
  >- (
    xlet ‘(POSTv v.
        SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
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
      INSTREAM_LINES #"\n" fd fdv ls (forwardFD fs fd k) *
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
  xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' res acc' fns' s lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (OPTION_TYPE NUM)
              (PAIR_TYPE (LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM)) (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))))
              (PAIR_TYPE (fns_TYPE a)
              NUM)) (res,acc',fns',lno') v ∧
            parse_red_aux (x1,x2) t [] = SOME(res,acc',fns',rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
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
  every_case_tac>>fs[OPTION_TYPE_def,PAIR_TYPE_def]>>xmatch
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[NPBC_CHECK_SSTEP_TYPE_def,NPBC_CHECK_LSTEP_TYPE_def,SUM_TYPE_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[NPBC_CHECK_SSTEP_TYPE_def,NPBC_CHECK_LSTEP_TYPE_def,SUM_TYPE_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
QED

val res = translate pb_parseTheory.parse_vars_line_aux_def;
val res = translate parse_load_order_def;

val res = translate hashString_nf_def;
val res = translate parse_vars_line_def;
val res = translate parse_vars_aux_def;

val read_n_lines = process_topdecs`
  fun read_n_lines n fd lno =
  if n = 0 then []
  else
  let val l = TextIO.b_inputLineTokens #"\n" fd blanks tokenize_fast in
    case l of None =>
    raise Fail (format_failure lno "Unexpected EOF when reading lines")
    | Some l =>
      l :: read_n_lines (n-1) fd (lno+1)
  end` |> append_prog

Theorem read_n_lines_spec:
  !n nv fs fd fdv lines lno lnov.
  NUM n nv ∧
  NUM lno lnov
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "read_n_lines" (get_ml_prog_state()))
    [nv; fdv;lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv (DROP n lines) (forwardFD fs fd k) *
         &(
            n ≤ LENGTH lines ∧
            LIST_TYPE
            (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
            (MAP
              (MAP tokenize_fast ∘ tokens blanks)
              (TAKE n lines)) v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ LENGTH lines < n)))
Proof
  Induct>>rw[]>>
  xcf "read_n_lines" (get_ml_prog_state ())
  >- (
    xlet_autop>>
    xif>>asm_exists_tac>>simp[]>>
    xcon>>xsimpl>>
    simp[LIST_TYPE_def]>>
    qexists_tac`0`>>simp[]>>
    xsimpl)>>
  xlet_autop>>
  xif>>asm_exists_tac>>simp[]>>
  Cases_on`lines`
  >- (
    xlet ‘(POSTv v.
        SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
            &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘emp’
      \\ qexists_tac ‘[]’
      \\ xsimpl
      \\ metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc])>>
    fs[OPTION_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def,STDIO_INSTREAM_LINES_refl_gc])>>
  rw[]>>
  xlet ‘(POSTv v.
          SEP_EXISTS k.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES #"\n" fd fdv t (forwardFD fs fd k) *
          & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks_fast h)) v)’
  THEN1 (
    xapp_spec b_inputLineTokens_specialize
    \\ qexists_tac ‘emp’
    \\ qexists_tac ‘h::t’
    \\ qexists_tac ‘fs’
    \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
    \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
    \\ simp[toks_fast_def])>>
  fs[OPTION_TYPE_def]>>
  xmatch>>
  rpt (xlet_autop)>>
  first_x_assum drule>>
  pop_assum kall_tac>>
  disch_then drule>>
  rw[]>>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  xlet`(POSTve
      (λv.
         SEP_EXISTS k.
         STDIO (forwardFD fss fd k) *
         INSTREAM_LINES #"\n" fd fdv (DROP n t) (forwardFD fss fd k) *
         &(
            n ≤ LENGTH t ∧
            LIST_TYPE
            (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
            (MAP
              (MAP tokenize_fast ∘ tokens blanks)
              (TAKE n t)) v))
      (λe.
         SEP_EXISTS k t'.
         STDIO (forwardFD fss fd k) *
         INSTREAM_LINES #"\n" fd fdv t' (forwardFD fss fd k) *
         &(Fail_exn e ∧ LENGTH t < n)))`
  >- xapp
  >-(
    xsimpl>>
    rw[Abbr`fss`,forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  xcon>>xsimpl>>
  fs[LIST_TYPE_def,toks_fast_def]>>
  rw[Abbr`fss`,forwardFD_o]>>
  metis_tac[STDIO_INSTREAM_LINES_refl_gc]
QED

Definition parse_vars_aux_opt_def:
  parse_vars_aux_opt ls =
    parse_vars_aux
      (EL 0 ls)
      (EL 1 ls)
      (EL 2 ls)
      (EL 3 ls)
      (EL 4 ls)
End

val res = translate parse_vars_aux_opt_def;
val parse_vars_aux_opt_side = Q.prove(
  `∀x. parse_vars_aux_opt_side x <=> 5 ≤ LENGTH x`,
  EVAL_TAC>>rw[]
  ) |> update_precondition;

val parse_vars_block = process_topdecs`
  fun parse_vars_block fd lno =
  case parse_vars_aux_opt (read_n_lines 5 fd lno) of
    None =>
      raise Fail (format_failure lno "Unable to parse vars block in order definition")
  | Some res => (res, lno+5)
  ` |> append_prog

Theorem parse_vars_block_eq:
  5 ≤ LENGTH ls ⇒
  parse_vars_block (MAP toks_fast ls) =
  OPTION_MAP (λi.
    (i,MAP toks_fast (DROP 5 ls)))
    (parse_vars_aux_opt
    (MAP toks_fast (TAKE 5 ls)))
Proof
  Cases_on`ls`>>fs[]>>
  ntac 4 (rename1`LENGTH ls`>>
  Cases_on`ls`>>fs[])>>
  simp[parse_vars_aux_opt_def,parse_vars_block_def]>>
  TOP_CASE_TAC>>fs[]
QED

Theorem toks_fast_eq:
  toks_fast = MAP tokenize_fast ∘ tokens blanks
Proof
  rw[FUN_EQ_THM,toks_fast_def]
QED

Theorem parse_vars_block_spec:
  NUM lno lnov ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_vars_block" (get_ml_prog_state()))
    [fdv;lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' res rest lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            parse_vars_block ss = SOME(res,rest) ∧
            MAP toks_fast lines' = rest ∧
            PAIR_TYPE
            (PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE NUM))
            NUM (res,lno') v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ parse_vars_block ss = NONE)))
Proof
  rw[]>>
  xcf "parse_vars_block" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xlet`(POSTve
      (λv.
         SEP_EXISTS k.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv (DROP 5 lines) (forwardFD fs fd k) *
         &(
            5 ≤ LENGTH lines ∧
            LIST_TYPE
            (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
            (MAP
              (MAP tokenize_fast ∘ tokens blanks)
              (TAKE 5 lines)) v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ LENGTH lines < 5)))`
  >- (
    xapp>>
    fs[NUM_def]>>
    metis_tac[])
  >- (
    xsimpl>>
    simp[parse_vars_block_def]>>
    `LENGTH lines = LENGTH (MAP toks_fast lines)` by fs[]>>
    pop_assum SUBST_ALL_TAC>>
    every_case_tac>>gs[]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  xlet_auto
  >- (
    xsimpl>>
    simp[EqualityType_NUM_BOOL])>>
  fs[GSYM toks_fast_eq]>>
  drule parse_vars_block_eq>>simp[]>>rw[]>>
  Cases_on`parse_vars_aux_opt (MAP toks_fast (TAKE 5 lines))`>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>rw[]>>
    metis_tac[Fail_exn_def,STDIO_INSTREAM_LINES_refl_gc])>>
  xlet_autop>>
  xcon>>xsimpl>>
  simp[PAIR_TYPE_def]>>
  metis_tac[Fail_exn_def,STDIO_INSTREAM_LINES_refl_gc]
QED

Definition parse_def_aux_line_def:
  parse_def_aux_line s =
  OPTION_MAP FST (parse_constraint_npbc (hashString_nf,()) s)
End

val res = translate parse_def_aux_line_def;

Definition is_end_def:
  is_end s ⇔ s = [INL (strlit"end")]
End

val res = translate is_end_def;

val parse_def_aux = process_topdecs`
  fun parse_def_aux fd lno acc =
  case TextIO.b_inputLineTokens #"\n" fd blanks tokenize_fast of
    None =>
    raise Fail (format_failure lno "Unable to parse def block in order definition")
  | Some s =>
    if is_end s then
      (List.rev acc, lno+1)
    else
      case parse_def_aux_line s of
        None =>
          raise Fail (format_failure lno "Unable to parse def block in order definition")
      | Some c => parse_def_aux fd (lno+1) (c::acc)` |> append_prog;

Theorem parse_def_aux_spec:
  ∀lines ss acc accv lno lnov fs.
  NUM lno lnov ∧
  LIST_TYPE (constraint_TYPE) acc accv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_def_aux" (get_ml_prog_state()))
    [fdv;lnov;accv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' res rest lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            parse_def_aux ss acc = SOME(res,rest) ∧
            MAP toks_fast lines' = rest ∧
            PAIR_TYPE
            (LIST_TYPE constraint_TYPE)
            NUM (res,lno') v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ parse_def_aux ss acc = NONE)))
Proof
  Induct>>rw[]>>
  xcf "parse_def_aux" (get_ml_prog_state ())
  >- (
    xlet ‘(POSTv v.
        SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
            &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘emp’
      \\ qexists_tac ‘[]’
      \\ xsimpl
      \\ metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc])>>
    fs[OPTION_TYPE_def]>>xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[parse_def_aux_def]>>
    metis_tac[Fail_exn_def,STDIO_INSTREAM_LINES_refl_gc])>>
  xlet ‘(POSTv v.
            SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
            & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks_fast h)) v)’
  >- (
    xapp_spec b_inputLineTokens_specialize
    \\ qexists_tac ‘emp’
    \\ qexists_tac ‘h::lines’
    \\ qexists_tac ‘fs’
    \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
    \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
    \\ simp[toks_fast_def])>>
  fs[OPTION_TYPE_def]>>xmatch>>
  xlet_auto
  >-
    (xsimpl>>simp[EqualityType_NUM_BOOL])>>
  xif
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    fs[parse_def_aux_def,is_end_def,PAIR_TYPE_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  rpt xlet_autop>>
  Cases_on`parse_def_aux_line (toks_fast h)`>>
  fs[OPTION_TYPE_def]>>xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    fs[parse_def_aux_def,parse_def_aux_line_def,is_end_def]>>
    metis_tac[Fail_exn_def,STDIO_INSTREAM_LINES_refl_gc])>>
  rpt xlet_autop>>
  xapp>>xsimpl>>
  fs[parse_def_aux_def,parse_def_aux_line_def,is_end_def]>>
  TOP_CASE_TAC>>
  rename1`c::acc`>>
  qexists_tac`emp`>>
  qexists_tac`forwardFD fs fd k`>>
  qexists_tac`c::acc`>>
  asm_exists_tac>>xsimpl>>
  fs[LIST_TYPE_def,PAIR_TYPE_def,forwardFD_o]>>
  rw[]>>
  metis_tac[STDIO_INSTREAM_LINES_refl_gc,STDIO_INSTREAM_LINES_refl]
QED

Definition expect_def:
  expect lines st =
  case lines of [] => NONE
  | (s::ss) =>
    if s = st then SOME ss else NONE
End

Definition token_to_string_def:
  (token_to_string (INL (s:mlstring)) = s) ∧
  (token_to_string (INR (i:int)) = toString i)
End

Definition tokens_to_string_def:
  (tokens_to_string ls =
    concatWith (strlit" ") (MAP token_to_string ls))
End

val res = translate token_to_string_def;
val res = translate tokens_to_string_def;

val expect_fd = process_topdecs`
  fun expect_fd fd lno st =
  case TextIO.b_inputLineTokens #"\n" fd blanks tokenize_fast of
    None =>
    raise Fail (format_failure lno
      ("Unable to parse, expected: " ^ tokens_to_string st))
  | Some s =>
    if s = st then lno + 1
    else
    raise Fail (format_failure lno
      ("Unable to parse, expected: " ^ tokens_to_string st))`
  |> append_prog;

Theorem expect_fd_spec:
  NUM lno lnov ∧
  LIST_TYPE (SUM_TYPE STRING_TYPE INT) st stv ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "expect_fd" (get_ml_prog_state()))
    [fdv;lnov;stv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            expect ss st = SOME (MAP toks_fast lines') ∧
            NUM (lno + 1) v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ expect ss st = NONE)))
Proof
  rw[]>>
  xcf"expect_fd" (get_ml_prog_state ())>>
  Cases_on`lines`
  >- (
    xlet ‘(POSTv v.
        SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
            &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘emp’
      \\ qexists_tac ‘[]’
      \\ xsimpl
      \\ metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc])>>
    fs[OPTION_TYPE_def]>>xmatch>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[expect_def]>>
    metis_tac[Fail_exn_def,STDIO_INSTREAM_LINES_refl_gc])>>
  rename1`h::lines`>>
  xlet ‘(POSTv v.
            SEP_EXISTS k.
            STDIO (forwardFD fs fd k) *
            INSTREAM_LINES #"\n" fd fdv lines (forwardFD fs fd k) *
            & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks_fast h)) v)’
  >- (
    xapp_spec b_inputLineTokens_specialize
    \\ qexists_tac ‘emp’
    \\ qexists_tac ‘h::lines’
    \\ qexists_tac ‘fs’
    \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
    \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
    \\ simp[toks_fast_def])>>
  fs[OPTION_TYPE_def]>>xmatch>>
  xlet_auto
  >- (
    xsimpl>>simp[]>>
    match_mp_tac EqualityType_LIST_TYPE>>
    match_mp_tac EqualityType_SUM_TYPE>>
    simp[EqualityType_NUM_BOOL])>>
  xif
  >- (
    xapp>>xsimpl>>
    fs[NUM_def]>>
    asm_exists_tac>>simp[expect_def]>>rw[]>>
    qexists_tac`k`>>qexists_tac`lines`>>xsimpl>>
    `&lno + 1 = &(lno+1):int` by
      intLib.ARITH_TAC>>
    fs[])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>simp[expect_def,Fail_exn_def]>>
  metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc]
QED

Definition def_line_def:
  def_line = [INL (strlit"def")]
End

val res = translate def_line_def;

val def_line_v_thm = fetch "-" "def_line_v_thm";

val parse_def_block = process_topdecs`
  fun parse_def_block fd lno =
  let val lno = expect_fd fd lno def_line in
      parse_def_aux fd lno []
  end` |> append_prog

Theorem parse_def_block_spec:
  ∀lines ss lno lnov fs.
  NUM lno lnov ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_def_block" (get_ml_prog_state()))
    [fdv;lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' res rest lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            parse_def_block ss = SOME(res,rest) ∧
            MAP toks_fast lines' = rest ∧
            PAIR_TYPE
            (LIST_TYPE constraint_TYPE)
            NUM (res,lno') v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ parse_def_block ss = NONE)))
Proof
  rw[]>>
  xcf "parse_def_block" (get_ml_prog_state ())>>
  xlet`POSTve
    (λv.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(expect (MAP toks_fast lines) def_line = SOME (MAP toks_fast lines') ∧
            NUM (lno + 1) v))
    (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ expect (MAP toks_fast lines) def_line = NONE))`
  >- (
    xapp>>xsimpl>>
    simp[def_line_v_thm])
  >- (
    xsimpl>>
    simp[parse_def_block_def,expect_def,AllCaseEqs(),def_line_def]>>
    rw[]>>simp[]>>
    metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc])>>
  xlet_autop>>
  xapp>>xsimpl>>
  gvs[parse_def_block_def,expect_def,AllCaseEqs(),def_line_def]>>
  CONV_TAC (RESORT_EXISTS_CONV (sort_vars ["acc"]))>>
  qexists_tac`[]`>>simp[LIST_TYPE_def]>>
  asm_exists_tac>>simp[]>>
  qexists_tac`emp`>>
  qexists_tac`lines'`>>
  qexists_tac`forwardFD fs fd k`>>
  qexists_tac`fd`>>
  xsimpl>>rw[PAIR_TYPE_def,forwardFD_o]>>
  metis_tac[Fail_exn_def,STDIO_INSTREAM_LINES_refl_gc]
QED

Definition proof_line_def:
  proof_line = [INL (strlit"proof")]
End

val res = translate proof_line_def;

val proof_line_v_thm = fetch "-" "proof_line_v_thm";

Definition end_line_def:
  end_line = [INL (strlit"end")]
End

val res = translate end_line_def;

val end_line_v_thm = fetch "-" "end_line_v_thm";

val parse_proof_block = process_topdecs`
  fun parse_proof_block fd lno =
  let
    val lno = expect_fd fd lno proof_line in
    case parse_red_aux (hashstring_nf,()) fd lno [] of
      (None,(pf,(u,lno))) =>
      (pf, expect_fd fd lno end_line)
    | u => raise Fail (format_failure lno "transitivity proof block cannot be terminated by contradiction id")
  end` |> append_prog

Theorem parse_proof_block_spec:
  NUM lno lnov ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_proof_block" (get_ml_prog_state()))
    [fdv;lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' res rest lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            parse_proof_block ss = SOME(res,rest) ∧
            MAP toks_fast lines' = rest ∧
            PAIR_TYPE
            (LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM)) (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))))
            NUM (res,lno') v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ parse_proof_block ss = NONE)))
Proof
  rw[]>>
  xcf "parse_proof_block" (get_ml_prog_state ())>>
  xlet`POSTve
    (λv.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(expect (MAP toks_fast lines) proof_line = SOME (MAP toks_fast lines') ∧
            NUM (lno + 1) v))
    (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ expect (MAP toks_fast lines) proof_line = NONE))`
  >- (
    xapp>>xsimpl>>
    simp[proof_line_v_thm])
  >- (
    xsimpl>>
    simp[parse_proof_block_def,expect_def,AllCaseEqs(),proof_line_def]>>
    rw[]>>simp[]>>
    metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc])>>
  rpt xlet_autop>>
  xlet`(POSTve
      (λv.
         SEP_EXISTS k lines'' res acc' fns' lno' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines'' (forwardFD fs fd k) *
         &(
            PAIR_TYPE (OPTION_TYPE NUM)
            (PAIR_TYPE (LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM)) (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))))
              (PAIR_TYPE (fns_TYPE UNIT_TYPE)
              NUM)) (res,acc',fns',lno') v ∧
            parse_red_aux (hashString_nf,()) (MAP toks_fast lines') [] = SOME(res,acc',fns',rest) ∧
            MAP toks_fast lines'' = rest))
      (λe.
         SEP_EXISTS k lines''.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines'' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_red_aux (hashString_nf,()) (MAP toks_fast lines') [] = NONE))
      )`
  >- (
    xapp_spec (parse_red_aux_spec |> INST_TYPE[alpha |->``:unit``])>>
    xsimpl>>
    first_x_assum (irule_at Any)>>
    qexists_tac`lines'`>>
    qexists_tac`forwardFD fs fd k`>>
    xsimpl>>
    qexists_tac`(hashString_nf,())`>>
    qexists_tac`fd`>>
    qexists_tac`[]`>>
    xsimpl>>
    simp[LIST_TYPE_def,fetch "-" "hashstring_nf_v_thm",PAIR_TYPE_def]>>
    qexists_tac`UNIT_TYPE`>>simp[]>>
    rw[]>>
    simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
  >- (
    xsimpl>>
    gvs[expect_def,parse_proof_block_def,AllCaseEqs()]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  fs[PAIR_TYPE_def]>>
  Cases_on`res`>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xlet`POSTve
    (λv.
         SEP_EXISTS k lines'''.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines''' (forwardFD fs fd k) *
           &(expect (MAP toks_fast lines'') end_line = SOME (MAP toks_fast lines''') ∧
            NUM (lno' + 1) v))
    (λe.
         SEP_EXISTS k lines'''.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines''' (forwardFD fs fd k) *
           &(Fail_exn e ∧ expect (MAP toks_fast lines'') end_line = NONE))`
    >- (
      xapp>>xsimpl>>
      qexists_tac`emp`>>
      asm_exists_tac>>simp[]>>
      qexists_tac`end_line`>>
      qexists_tac`lines''`>>qexists_tac`forwardFD fs fd k`>>
      qexists_tac`fd`>>
      xsimpl>>
      simp[end_line_v_thm,forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])
    >- (
      xsimpl>>
      gvs[parse_proof_block_def,expect_def,AllCaseEqs(),proof_line_def,end_line_def]>>
      metis_tac[STDIO_INSTREAM_LINES_refl])>>
    xcon>>xsimpl>>
    gvs[parse_proof_block_def,expect_def,AllCaseEqs(),proof_line_def,end_line_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  rpt xlet_autop>>
  gvs[expect_def,parse_proof_block_def,AllCaseEqs()]>>
  xraise>>
  xsimpl>>
  metis_tac[STDIO_INSTREAM_LINES_refl_gc,Fail_exn_def]
QED

Definition parse_trans_aux_opt_def:
  parse_trans_aux_opt ls =
    parse_trans_aux
      (EL 0 ls)
      (EL 1 ls)
      (EL 2 ls)
      (EL 3 ls)
End

val res = translate parse_trans_aux_def;
val res = translate parse_trans_aux_opt_def;
val parse_trans_aux_opt_side = Q.prove(
  `∀x. parse_trans_aux_opt_side x <=> 4 ≤ LENGTH x`,
  EVAL_TAC>>rw[]
  ) |> update_precondition;

val parse_trans_block = process_topdecs`
  fun parse_trans_block fd lno =
  case parse_trans_aux_opt (read_n_lines 4 fd lno) of
    None =>
      raise Fail (format_failure lno "Unable to parse trans block in order definition")
  | Some ws =>
    (ws,parse_proof_block fd (lno+4))
  ` |> append_prog

Theorem parse_trans_block_eq:
  4 ≤ LENGTH ls ⇒
  parse_trans_block (MAP toks_fast ls) =
  case parse_trans_aux_opt
    (MAP toks_fast (TAKE 4 ls)) of NONE => NONE
  | SOME ws =>
    case parse_proof_block (MAP toks_fast (DROP 4 ls)) of
      NONE => NONE
    | SOME (pf,ss) => SOME (ws,pf,ss)
Proof
  Cases_on`ls`>>fs[]>>
  ntac 3 (rename1`LENGTH ls`>>
  Cases_on`ls`>>fs[])>>
  simp[parse_trans_aux_opt_def,parse_trans_block_def]
QED

Theorem parse_trans_block_spec:
  NUM lno lnov ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_trans_block" (get_ml_prog_state()))
    [fdv;lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' ws pf ss' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            parse_trans_block ss = SOME(ws,pf,ss') ∧
            MAP toks_fast lines' = ss' ∧
            PAIR_TYPE
            (LIST_TYPE NUM)
            (PAIR_TYPE pfs_TYPE NUM) (ws,pf,lno') v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ parse_trans_block ss = NONE)))
Proof
  rw[]>>
  xcf "parse_trans_block" (get_ml_prog_state ())>>
  xlet`(POSTve
      (λv.
         SEP_EXISTS k.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv (DROP 4 lines) (forwardFD fs fd k) *
         &(
            4 ≤ LENGTH lines ∧
            LIST_TYPE
            (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
            (MAP
              (MAP tokenize_fast ∘ tokens blanks)
              (TAKE 4 lines)) v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ LENGTH lines < 4)))`
  >- (
    xapp>>
    fs[NUM_def]>>
    metis_tac[])
  >- (
    xsimpl>>
    simp[parse_trans_block_def]>>
    `LENGTH lines = LENGTH (MAP toks_fast lines)` by fs[]>>
    pop_assum SUBST_ALL_TAC>>
    every_case_tac>>gs[]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  xlet_auto
  >- (
    xsimpl>>
    simp[EqualityType_NUM_BOOL])>>
  fs[GSYM toks_fast_eq,parse_trans_block_eq]>>
  Cases_on`parse_trans_aux_opt (MAP toks_fast (TAKE 4 lines))`>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>rw[]>>
    metis_tac[Fail_exn_def,STDIO_INSTREAM_LINES_refl_gc])>>
  xlet_autop>>
  qmatch_goalsub_abbrev_tac`parse_proof_block ss`>>
  xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' res rest lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            parse_proof_block ss = SOME(res,rest) ∧
            MAP toks_fast lines' = rest ∧
            PAIR_TYPE
            (LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM)) (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))))
            NUM (res,lno') v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ parse_proof_block ss = NONE)))`
  >- (
    xapp>>xsimpl>>
    first_x_assum (irule_at Any)>>
    qexists_tac`DROP 4 lines`>>
    qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>
    qexists_tac`emp`>>
    xsimpl>>
    simp[forwardFD_o,PAIR_TYPE_def]>>
    metis_tac[Fail_exn_def,STDIO_INSTREAM_LINES_refl_gc])
  >- (
    xsimpl>>
    metis_tac[Fail_exn_def,STDIO_INSTREAM_LINES_refl])>>
  xcon>>xsimpl>>
  fs[PAIR_TYPE_def]>>
  metis_tac[Fail_exn_def,STDIO_INSTREAM_LINES_refl_gc]
QED

Definition reflexivity_line_def:
  reflexivity_line = [INL (strlit"reflexivity")]
End

val res = translate reflexivity_line_def;

val reflexivity_line_v_thm = fetch "-" "reflexivity_line_v_thm";

val parse_refl_block = process_topdecs`
  fun parse_refl_block fd lno =
  let val lno = expect_fd fd lno reflexivity_line in
    parse_proof_block fd lno
  end` |> append_prog

Theorem parse_refl_block_spec:
  NUM lno lnov ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_refl_block" (get_ml_prog_state()))
    [fdv;lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' ws pf ss' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            parse_refl_block ss = SOME(pf,ss') ∧
            MAP toks_fast lines' = ss' ∧
            PAIR_TYPE pfs_TYPE NUM (pf,lno') v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ parse_refl_block ss = NONE)))
Proof
  rw[]>>
  xcf "parse_refl_block" (get_ml_prog_state ())>>
  xlet`POSTve
    (λv.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(expect (MAP toks_fast lines) reflexivity_line = SOME (MAP toks_fast lines') ∧
            NUM (lno + 1) v))
    (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ expect (MAP toks_fast lines) reflexivity_line = NONE))`
  >- (
    xapp>>xsimpl>>
    simp[reflexivity_line_v_thm])
  >- (
    xsimpl>>
    simp[parse_refl_block_def,expect_def,AllCaseEqs(),reflexivity_line_def]>>
    rw[]>>simp[]>>
    metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc])>>
  xapp>>xsimpl>>
  gvs[parse_refl_block_def,expect_def,AllCaseEqs(),reflexivity_line_def]>>
  qexists_tac`emp`>>
  qexists_tac`lines'`>>
  qexists_tac`forwardFD fs fd k`>>
  qexists_tac`fd`>>
  asm_exists_tac>>xsimpl>>rw[]>>
  fs[PAIR_TYPE_def,forwardFD_o]>>
  metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc]
QED

val parse_trans_refl_block = process_topdecs`
  fun parse_trans_refl_block fd lno =
  case parse_trans_block fd lno of (ws,(pft,lno)) =>
  case parse_refl_block fd lno of (pfr,lno) =>
    (ws,(pfr,(pft,lno)))` |> append_prog;

Theorem parse_trans_refl_block_spec:
  NUM lno lnov ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_trans_refl_block" (get_ml_prog_state()))
    [fdv;lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' ws pfr pft ss' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            parse_trans_refl_block ss = SOME(ws,pfr,pft,ss') ∧
            MAP toks_fast lines' = ss' ∧
            PAIR_TYPE (LIST_TYPE NUM)
            (PAIR_TYPE pfs_TYPE
            (PAIR_TYPE pfs_TYPE NUM))
              (ws,pfr,pft,lno') v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ parse_trans_refl_block ss = NONE)))
Proof
  rw[]>>
  xcf "parse_trans_refl_block" (get_ml_prog_state ())>>
  xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' ws pft ss' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            parse_trans_block (MAP toks_fast lines) = SOME(ws,pft,ss') ∧
            MAP toks_fast lines' = ss' ∧
            PAIR_TYPE
            (LIST_TYPE NUM)
            (PAIR_TYPE pfs_TYPE NUM) (ws,pft,lno') v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ parse_trans_block (MAP toks_fast lines) = NONE)))`
  >- (
    xapp>>xsimpl>>
    metis_tac[])
  >- (
    xsimpl>>
    simp[parse_trans_refl_block_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc])>>
  fs[PAIR_TYPE_def]>>xmatch>>
  xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' ws pfr ss'' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            parse_refl_block ss' = SOME(pfr,ss'') ∧
            MAP toks_fast lines' = ss'' ∧
            PAIR_TYPE pfs_TYPE NUM (pfr,lno') v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ parse_refl_block ss' = NONE)))`
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>simp[]>>
    qexists_tac`emp`>>
    qexists_tac`lines'`>>qexists_tac`forwardFD fs fd k`>>
    qexists_tac`fd`>>xsimpl>>
    fs[PAIR_TYPE_def,forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc])
  >- (
    xsimpl>>
    simp[parse_trans_refl_block_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc])>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>xsimpl>>simp[parse_trans_refl_block_def]>>
  metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc]
QED

val parse_pre_order = process_topdecs`
  fun parse_pre_order fd lno =
  case parse_vars_block fd lno of
    (uvs,lno) =>
  (case parse_def_block fd lno of
    (f,lno) =>
  (case parse_trans_refl_block fd lno of
    (ws,(pfr,(pft,lno))) =>
    ((f,uvs),(ws, (pfr,(pft,expect_fd fd lno end_line))))))
  `|> append_prog;

Theorem parse_pre_order_spec:
  NUM lno lnov ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_pre_order" (get_ml_prog_state()))
    [fdv;lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' res a b c d rest lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            parse_pre_order ss = SOME (a,b,c,d,rest) ∧
            PAIR_TYPE
              spo_TYPE
              (PAIR_TYPE (LIST_TYPE NUM)
              (PAIR_TYPE pfs_TYPE
              (PAIR_TYPE pfs_TYPE
              NUM)))
            (a,b,c,d,lno') v ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ parse_pre_order ss = NONE)))
Proof
  rw[]>>
  xcf "parse_pre_order" (get_ml_prog_state ())>>
  drule parse_vars_block_spec>>
  pop_assum kall_tac>>
  rw[]>>
  xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' res rest lno.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            parse_vars_block (MAP toks_fast lines) = SOME(res,rest) ∧
            MAP toks_fast lines' = rest ∧
            PAIR_TYPE
            (PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE NUM))
            NUM (res,lno) v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(Fail_exn e ∧ parse_vars_block (MAP toks_fast lines) = NONE)))`
  >- (xapp>>xsimpl)
  >-(
    xsimpl>>
    simp[parse_pre_order_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  fs[PAIR_TYPE_def]>>xmatch>>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" _ _ lines1 fs1`>>
  simp[parse_pre_order_def]>>
  TOP_CASE_TAC>>fs[]>>
  xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' res rest lno'.
         STDIO (forwardFD fs1 fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
         &(
            parse_def_block (MAP toks_fast lines1) = SOME(res,rest) ∧
            MAP toks_fast lines' = rest ∧
            PAIR_TYPE
            (LIST_TYPE constraint_TYPE)
            NUM (res,lno') v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs1 fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
         &(Fail_exn e ∧ parse_def_block (MAP toks_fast lines1) = NONE)))`
  >- (xapp>>metis_tac[])
  >- (
    xsimpl>>
    unabbrev_all_tac>>simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  fs[PAIR_TYPE_def]>>xmatch>>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" _ _ lines2 fs2`>>
  xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' ws pfr pft ss' lno'.
         STDIO (forwardFD fs2 fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs2 fd k) *
         &(
            parse_trans_refl_block (MAP toks_fast lines2) =
              SOME(ws,pfr,pft,ss') ∧
            MAP toks_fast lines' = ss' ∧
            PAIR_TYPE (LIST_TYPE NUM)
            (PAIR_TYPE pfs_TYPE
            (PAIR_TYPE pfs_TYPE NUM))
              (ws,pfr,pft,lno') v))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs2 fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs2 fd k) *
         &(Fail_exn e ∧ parse_trans_refl_block (MAP toks_fast lines2) = NONE)))`
  >- (xapp>> metis_tac[])
  >- (
    xsimpl>>
    unabbrev_all_tac>>simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  fs[PAIR_TYPE_def]>>xmatch>>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" _ _ lines3 fs3`>>
  xlet`POSTve
    (λv.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs3 fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs3 fd k) *
           &(expect (MAP toks_fast lines3) end_line = SOME (MAP toks_fast lines') ∧
            NUM (lno''  + 1) v))
    (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs3 fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs3 fd k) *
           &(Fail_exn e ∧ expect (MAP toks_fast lines3) end_line = NONE))`
  >-
    (xapp>>simp[end_line_v_thm])
  >- (
    xsimpl>>
    unabbrev_all_tac>>
    simp[expect_def,AllCaseEqs(),end_line_def,forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  unabbrev_all_tac>>
  gvs[parse_trans_refl_block_def,expect_def,AllCaseEqs(),end_line_def,forwardFD_o]>>
  fs[PAIR_TYPE_def]>>
  rw[]>>gvs[]>>
  metis_tac[STDIO_INSTREAM_LINES_refl_gc]
QED

val res = translate parse_delc_header_def;

val parse_delc_header_side = Q.prove(
  `∀x y. parse_delc_header_side x y <=> T`,
  simp[fetch "-" "parse_delc_header_side_def"]>>
  rw[]>>
  intLib.ARITH_TAC) |> update_precondition;

val r = translate strip_terminator_def;

val strip_terminator_side_def = definition"strip_terminator_side_def";
val strip_terminator_side = Q.prove(
  `∀x. strip_terminator_side x <=> T`,
  rw[strip_terminator_side_def])
  |> update_precondition;

val r = translate strip_term_def;

val strip_term_side_def = definition"strip_term_side_def";
val strip_term_side = Q.prove(
  `∀x. strip_term_side x <=> T`,
  rw[strip_term_side_def])
  |> update_precondition;

val res = translate insert_lit_def;
val res = translate parse_assg_def;
val res = translate parse_obj_term_def;
val res = translate strip_obju_end_def;

val res = translate normalise_obj_def;
val res = translate parse_obj_term_npbc_def;

val res = translate parse_strengthen_def;

val res = translate parse_b_obj_term_npbc_def;

val res = translate parse_cstep_head_def;

val PB_PARSE_PAR_TYPE_def = theorem"PB_PARSE_PAR_TYPE_def";

val parse_cstep = process_topdecs`
  fun parse_cstep fns fd lno =
    case parse_sstep fns fd lno of
      (Inr sstep, (fns',lno')) =>
        (Inr (Sstep sstep), (fns',lno'))
    | (Inl s, (fns',lno')) =>
    (case parse_cstep_head fns' s of
      None => (Inl s, (fns',lno'))
    | Some (Done cstep,fns'') => (Inr cstep, (fns'', lno'))
    | Some (Dompar c s,fns'') =>
        (case parse_red_aux fns'' fd (lno') [] of
            (res,(pf,(fns''',lno''))) =>
            (Inr (Dom c s pf res),(fns''',lno'')))
    | Some (Checkeddeletepar n s, fns'') =>
        (case parse_red_aux fns'' fd (lno') [] of
            (res,(pf,(fns''',lno''))) =>
            (Inr (Checkeddelete n s pf res),(fns''',lno'')))
    | Some (Storeorderpar name, fns'') =>
        (case parse_pre_order fd lno' of
          (spo,(ws,(pfr,(pft,lno'')))) =>
          (Inr (Storeorder name spo ws pfr pft), (fns'', lno'')))
    | Some (Changeobjpar b f, fns'') =>
        (case parse_red_aux fns'' fd lno' [] of
          (res,(pf,(fns''',lno''))) =>
          (case res of Some u =>
            raise Fail (format_failure (lno'+1) "obj change rule can not end with contradiction")
          | None =>
            (Inr (Changeobj b f pf), (fns''', lno''))
          )
        ))
  `|> append_prog;

Theorem parse_cstep_spec:
  !ss fd fdv lines lno lnov fs fns fnsv.
  fns_TYPE a fns fnsv ∧
  NUM lno lnov ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_cstep" (get_ml_prog_state()))
    [fnsv; fdv; lnov]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k lines' lno' res fns' rest.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            parse_cstep fns ss = SOME (res,fns',rest) ∧
            (PAIR_TYPE
              (SUM_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NPBC_CHECK_CSTEP_TYPE)
              (PAIR_TYPE
              (fns_TYPE a)
              NUM)) (res,fns',lno') v ∧
                MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_cstep fns ss = NONE))
      )
Proof
  rw[]>>
  xcf "parse_cstep" (get_ml_prog_state ())>>
  xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         &(
            case parse_sstep fns (MAP toks_fast lines) of
              NONE => F
            | SOME (res,fns',rest) =>
                (PAIR_TYPE
                  (SUM_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NPBC_CHECK_SSTEP_TYPE)
                  (PAIR_TYPE
                  (fns_TYPE a)
                  NUM)) (res,fns',lno') v ∧
                MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧ parse_sstep fns (MAP toks_fast lines) = NONE))
      )`
  >- (
    xapp>>
    metis_tac[])
  >- (
    xsimpl>>
    simp[parse_cstep_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl])>>
  pop_assum mp_tac>>
  every_case_tac>>rw[]>>
  fs[PAIR_TYPE_def]>>
  simp[parse_cstep_def]>>
  reverse (TOP_CASE_TAC)>>
  fs[SUM_TYPE_def]>>xmatch
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  xlet_autop>>
  fs[SUM_TYPE_def]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  TOP_CASE_TAC>>
  TOP_CASE_TAC>>
  fs[PAIR_TYPE_def,PB_PARSE_PAR_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
  >- (
    rpt xlet_autop>>
    qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" _ _ lines1 fs1`>>
    xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' res acc' fns' s lno' rest.
         STDIO (forwardFD fs1 fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
         &(
            PAIR_TYPE (OPTION_TYPE NUM)
            (PAIR_TYPE (LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM)) (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))))
              (PAIR_TYPE (fns_TYPE a)
              NUM)) (res,acc',fns',lno') v ∧
            parse_red_aux r (MAP toks_fast lines1) [] = SOME(res,acc',fns',rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs1 fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
           &(Fail_exn e ∧ parse_red_aux r (MAP toks_fast lines1) [] = NONE))
      )`
    >- (
      xapp>>xsimpl>>
      metis_tac[LIST_TYPE_def])
    >- (
      xsimpl>>
      unabbrev_all_tac>>simp[forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl]) >>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def]>>
    unabbrev_all_tac>>simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
  >- (
    rpt xlet_autop>>
    qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" _ _ lines1 fs1`>>
    xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' res a b c d rest lno'.
         STDIO (forwardFD fs1 fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
         &(
            parse_pre_order (MAP toks_fast lines1) = SOME (a,b,c,d,rest) ∧
            PAIR_TYPE
              spo_TYPE
              (PAIR_TYPE (LIST_TYPE NUM)
              (PAIR_TYPE pfs_TYPE
              (PAIR_TYPE pfs_TYPE
              NUM)))
            (a,b,c,d,lno') v ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
         STDIO (forwardFD fs1 fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
         &(Fail_exn e ∧ parse_pre_order (MAP toks_fast lines1) = NONE)))`
    >-
      (xapp>>metis_tac[])
    >- (
      xsimpl>>
      unabbrev_all_tac>>simp[forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl])>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    gvs[SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def]>>
    unabbrev_all_tac>>simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
  >- (
    rpt xlet_autop>>
    qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" _ _ lines1 fs1`>>
    xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' res acc' fns' s lno' rest.
         STDIO (forwardFD fs1 fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
         &(
            PAIR_TYPE (OPTION_TYPE NUM)
            (PAIR_TYPE (LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM)) (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))))
              (PAIR_TYPE (fns_TYPE a)
              NUM)) (res,acc',fns',lno') v ∧
            parse_red_aux r (MAP toks_fast lines1) [] = SOME(res,acc',fns',rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs1 fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
           &(Fail_exn e ∧ parse_red_aux r (MAP toks_fast lines1) [] = NONE))
      )`
    >- (
      xapp>>xsimpl>>
      metis_tac[LIST_TYPE_def])
    >- (
      xsimpl>>
      unabbrev_all_tac>>simp[forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl]) >>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def]>>
    unabbrev_all_tac>>simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
  >- (
    rpt xlet_autop>>
    qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" _ _ lines1 fs1`>>
    xlet`(POSTve
      (λv.
         SEP_EXISTS k lines' res acc' fns' s lno' rest.
         STDIO (forwardFD fs1 fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
         &(
            PAIR_TYPE (OPTION_TYPE NUM)
            (PAIR_TYPE (LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM)) (LIST_TYPE (NPBC_CHECK_LSTEP_TYPE))))
              (PAIR_TYPE (fns_TYPE a)
              NUM)) (res,acc',fns',lno') v ∧
            parse_red_aux r (MAP toks_fast lines1) [] = SOME(res,acc',fns',rest) ∧
            MAP toks_fast lines' = rest))
      (λe.
         SEP_EXISTS k lines'.
           STDIO (forwardFD fs1 fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs1 fd k) *
           &(Fail_exn e ∧ parse_red_aux r (MAP toks_fast lines1) [] = NONE))
      )`
    >- (
      xapp>>xsimpl>>
      metis_tac[LIST_TYPE_def])
    >- (
      xsimpl>>
      unabbrev_all_tac>>simp[forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl]) >>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      gvs[SUM_TYPE_def,NPBC_CHECK_CSTEP_TYPE_def]>>
      unabbrev_all_tac>>simp[forwardFD_o]>>
      metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    unabbrev_all_tac>>
    simp[Fail_exn_def]>>
    unabbrev_all_tac>>simp[forwardFD_o]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])
QED

(* returns the necessary information to check the
  output and conclusion sections *)
val check_unsat'' = process_topdecs `
  fun check_unsat'' fns fd lno fml zeros inds vimap vomap pc =
    case parse_cstep fns fd lno of
      (Inl s, (fns', lno')) =>
      (lno', (s, (fns',
        (fml, (inds, pc)))))
    | (Inr cstep, (fns', lno')) =>
      (case check_cstep_arr lno cstep fml zeros inds vimap vomap pc of
        (fml', (zeros', (inds', (vimap', (vomap', pc'))))) =>
        check_unsat'' fns' fd lno' fml' zeros' inds' vimap' vomap' pc')` |> append_prog

Theorem parse_sstep_LENGTH:
  ∀f ss res f' ss'.
  parse_sstep f ss = SOME (res,f',ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  Cases_on`ss`>>rw[parse_sstep_def]>>
  gvs[AllCaseEqs()]>>
  imp_res_tac parse_lsteps_aux_LENGTH>>
  imp_res_tac parse_red_aux_LENGTH>>
  fs[]
QED

Theorem parse_def_aux_LENGTH:
  ∀ss acc res ss'.
  parse_def_aux ss acc = SOME (res,ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  Induct>>rw[parse_def_aux_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  simp[]
QED

Theorem parse_pre_order_LENGTH:
  ∀ss a b cd .
  parse_pre_order ss = SOME (a,b,c,d,ss') ⇒
  LENGTH ss' < LENGTH ss
Proof
  rw[parse_pre_order_def]>>
  fs[parse_vars_block_def,parse_def_block_def,
    parse_trans_block_def,parse_refl_block_def,
    parse_trans_refl_block_def,
    parse_proof_block_def]>>
  gvs[AllCaseEqs()]>>
  imp_res_tac parse_red_aux_LENGTH>>
  imp_res_tac parse_def_aux_LENGTH>>
  fs[ADD1]
QED

(* Repeatedly parse a line and run the sstep checker,
  returning the last encountered state *)
Definition parse_and_run_def:
  parse_and_run fns ss
    fml zeros inds vimap vomap pc =
  case parse_cstep fns ss of
    NONE => NONE
  | SOME (INL s, fns', rest) =>
    SOME (rest, s, fns', fml, inds, pc)
  | SOME (INR cstep, fns', rest) =>
    (case check_cstep_list cstep fml zeros inds vimap vomap pc of
      SOME (fml', zeros', inds', vimap', vomap', pc') =>
        parse_and_run fns' rest fml' zeros' inds' vimap' vomap' pc'
    | res => NONE)
Termination
  WF_REL_TAC `measure (LENGTH o FST o SND)`>>
  rw[parse_cstep_def]>>
  gvs[AllCaseEqs()]>>
  imp_res_tac parse_sstep_LENGTH>>fs[]>>
  imp_res_tac parse_red_aux_LENGTH>>
  imp_res_tac parse_pre_order_LENGTH>>
  fs[]
End

Theorem ARRAY_STDIO_INSTREAM_LINES_refl:
  (ARRAY arr arrv * STDIO A *
  INSTREAM_LINES #"\n" B C D E ==>>
  ARRAY arr arrv * STDIO A *
  INSTREAM_LINES #"\n" B C D E) ∧
  (ARRAY arr arrv * STDIO A *
  INSTREAM_LINES #"\n" B C D E ==>>
  ARRAY arr arrv * STDIO A *
  INSTREAM_LINES #"\n" B C D E * GC)
Proof
  xsimpl
QED

Theorem STDIO_INSTREAM_LINES_ARRAY_refl:
  (STDIO A *
  INSTREAM_LINES #"\n" B C D E * ARRAY arr arrv ==>>
  STDIO A *
  INSTREAM_LINES #"\n" B C D E * ARRAY arr arrv) ∧
  (STDIO A *
  INSTREAM_LINES #"\n" B C D E * ARRAY arr arrv ==>>
  STDIO A *
  INSTREAM_LINES #"\n" B C D E * ARRAY arr arrv * GC)
Proof
  xsimpl
QED

Theorem check_unsat''_spec:
  ∀fns ss fmlls zeros inds vimap vomap pc
    fnsv lno lnov fmllsv zerosv indsv pcv lines fs fmlv vimapv vomapv.
  fns_TYPE a fns fnsv ∧
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  NPBC_CHECK_PROOF_CONF_TYPE pc pcv ∧
  vimap_TYPE vimap vimapv ∧
  vomap_TYPE vomap vomapv ∧
  EVERY (λw. w = 0w) zeros ∧
  MAP toks_fast lines = ss
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat''" (get_ml_prog_state()))
    [fnsv; fdv; lnov; fmlv; zerosv; indsv; vimapv; vomapv; pcv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs *
      ARRAY fmlv fmllsv * W8ARRAY zerosv zeros)
    (POSTve
      (λv.
         SEP_EXISTS k lines' lno' fmlv' fmllsv' res.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         ARRAY fmlv' fmllsv' *
         &(
          parse_and_run fns ss fmlls zeros inds vimap vomap pc =
            SOME (MAP toks_fast lines',res) ∧
            PAIR_TYPE NUM (
            PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (
            PAIR_TYPE (fns_TYPE a) (
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (LIST_TYPE NUM)
                (NPBC_CHECK_PROOF_CONF_TYPE))))) (lno',res) v))
      (λe.
         SEP_EXISTS k lines' fmlv' fmllsv'.
           ARRAY fmlv' fmllsv' *
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧
            parse_and_run fns ss fmlls zeros inds vimap vomap pc = NONE)))
Proof
  ho_match_mp_tac (fetch "-" "parse_and_run_ind")>>
  rw[]>>
  xcf "check_unsat''" (get_ml_prog_state ())>>
  simp[Once parse_and_run_def]>>
  Cases_on`parse_cstep fns (MAP toks_fast lines)`>>fs[]
  >- ((* parse_cstep NONE *)
    xlet `(POSTe e.
         SEP_EXISTS k lines' fmlv' fmllsv'.
           ARRAY fmlv' fmllsv' *
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e))`
    >- (
      xapp>>xsimpl>>
      asm_exists_tac>>simp[]>>
      asm_exists_tac>>simp[]>>
      qexists_tac`ARRAY fmlv fmllsv * W8ARRAY zerosv zeros`>>
      qexists_tac`lines`>>simp[]>>
      qexists_tac`fs`>>qexists_tac`fd`>>xsimpl>>
      rw[]>>
      qexists_tac`x`>>qexists_tac`x'`>>xsimpl>>
      qexists_tac`fmlv`>>qexists_tac`fmllsv`>>xsimpl)>>
    xsimpl>>
    simp[Once parse_and_run_def]>>
    rw[]>>
    metis_tac[ARRAY_STDIO_INSTREAM_LINES_refl])>>
  (* parse_sstep SOME *)
  xlet `(POSTv v.
    SEP_EXISTS k lines' lno'.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         ARRAY fmlv fmllsv * W8ARRAY zerosv zeros *
         &(
            case parse_cstep fns (MAP toks_fast lines) of
              NONE => F
            | SOME (res,fns',rest) =>
                (PAIR_TYPE
                  (SUM_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NPBC_CHECK_CSTEP_TYPE)
                  (PAIR_TYPE
                  (fns_TYPE a)
                  NUM)) (res,fns',lno') v ∧
                MAP toks_fast lines' = rest))`
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    qexists_tac`ARRAY fmlv fmllsv * W8ARRAY zerosv zeros`>>
    qexists_tac`lines`>>simp[]>>
    qexists_tac`fs`>>qexists_tac`fd`>>xsimpl>>
    PairCases_on`x`>>fs[]>>rw[]>>
    fs[OPTION_TYPE_def,PAIR_TYPE_def]>>
    asm_exists_tac>>simp[]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
  PairCases_on`x`>>
  Cases_on`x0`>>fs[SUM_TYPE_def,PAIR_TYPE_def]
  >- (
    (* INL *)
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    fs[PAIR_TYPE_def]
    >- (
      simp[]>>
      first_x_assum (irule_at Any)>>
      first_x_assum (irule_at Any)>>
      qexists_tac`lines'`>>
      qexists_tac`k`>>simp[]>>
      xsimpl)>>
    simp[Once parse_and_run_def])>>
  (* INR *)
  xmatch>>
  xlet`
  POSTve
    (λv'.
         SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
           W8ARRAY zerosv' zeros' * ARRAY fmlv' fmllsv' *
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &case check_cstep_list y fmlls zeros inds vimap vomap pc of
             NONE => F
           | SOME res =>
             PAIR_TYPE
               (λl v.
                    LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
                    v = fmlv')
               (PAIR_TYPE
                  (λl v. l = zeros' ∧ v = zerosv' ∧ EVERY (λw. w = 0w) zeros')
                  (PAIR_TYPE (LIST_TYPE NUM)
                     (PAIR_TYPE vimap_TYPE
                        (PAIR_TYPE vomap_TYPE NPBC_CHECK_PROOF_CONF_TYPE))))
               res v')
    (λe.
         SEP_EXISTS fmlv' fmllsv' zerosv' zeros'.
           ARRAY fmlv' fmllsv' *
           STDIO (forwardFD fs fd k) *
           INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e ∧
            check_cstep_list y fmlls zeros inds vimap vomap pc = NONE))`
  >- (
    xapp>>
    xsimpl>>reverse (rw[])>>
    rpt(first_x_assum (irule_at Any))>>xsimpl>>
    CONJ_TAC >-
      metis_tac[ARRAY_W8ARRAY_refl]>>
    rw[]>>
    rename1`ARRAY aa bb`>>
    qexists_tac`aa`>>qexists_tac`bb`>>xsimpl)
  >- (
    xsimpl>>rw[]>>
    simp[Once parse_and_run_def]>>
    metis_tac[ARRAY_STDIO_INSTREAM_LINES_refl])>>
  pop_assum mp_tac>>TOP_CASE_TAC>>simp[]>>
  strip_tac>>
  PairCases_on`x`>>fs[PAIR_TYPE_def,PULL_EXISTS]>>
  xmatch>>
  xapp>>xsimpl>>
  asm_exists_tac>>simp[]>>
  asm_exists_tac>>simp[]>>
  qexists_tac`emp`>>xsimpl>>
  qexists_tac`(forwardFD fs fd k)`>>
  xsimpl>>
  rw[]>>simp[forwardFD_o]
  >- (
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    qexists_tac`x'`>>
    simp[]>>
    qexists_tac`k+x`>>
    xsimpl)>>
  simp[Once parse_and_run_def]>>
  qexists_tac`k+x`>>qexists_tac`x'`>>xsimpl>>
  qmatch_goalsub_abbrev_tac`ARRAY A B`>>
  qexists_tac`A`>>qexists_tac`B`>>xsimpl
QED

val fill_arr = process_topdecs`
  fun fill_arr arr i ls =
    case ls of [] => arr
    | (v::vs) =>
      fill_arr (Array.updateResize arr None i (Some (v,True))) (i+1) vs` |> append_prog

Theorem fill_arr_spec:
  ∀ls lsv arrv arrls arrlsv i iv.
  NUM i iv ∧
  LIST_TYPE constraint_TYPE ls lsv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) arrls arrlsv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"fill_arr"(get_ml_prog_state()))
  [arrv; iv; lsv]
  (ARRAY arrv arrlsv)
  (POSTv resv.
  SEP_EXISTS arrlsv'. ARRAY resv arrlsv' *
    & LIST_REL (OPTION_TYPE bconstraint_TYPE)
    (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,T)) i)
      arrls (enumerate i ls)) arrlsv')
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
  simp[OPTION_TYPE_def,PAIR_TYPE_def]>>
  EVAL_TAC
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

Definition fold_update_vimap_enum_def:
  (fold_update_vimap_enum (k:num) [] acc = acc) ∧
  (fold_update_vimap_enum k (x::xs) acc =
    fold_update_vimap_enum (k+1)
      xs (update_vimap_aux acc k (FST x)))
End

Definition fold_update_vimap_enum_full_def:
  fold_update_vimap_enum_full k fml =
  fold_update_vimap_enum k fml LN
End

Theorem fold_update_vimap_enum_FOLDL:
  ∀xs k acc.
  fold_update_vimap_enum k xs acc =
  (FOLDL (λacc (i,v). update_vimap_aux acc i (FST v)) acc (enumerate k xs))
Proof
  Induct>>rw[fold_update_vimap_enum_def,miscTheory.enumerate_def]
QED

Theorem fold_update_vimap_enum_full_FOLDL:
  fold_update_vimap_enum_full k xs =
  (FOLDL (λacc (i,v). update_vimap_aux acc i (FST v)) LN (enumerate k xs))
Proof
  rw[fold_update_vimap_enum_full_def,fold_update_vimap_enum_FOLDL]
QED

val res = translate fold_update_vimap_enum_def;
val res = translate fold_update_vimap_enum_full_def;

val res = translate parse_unsat_def;

val parse_unsat_side = Q.prove(
  `∀x. parse_unsat_side x <=> T`,
  simp[fetch "-" "parse_unsat_side_def"]>>
  intLib.ARITH_TAC) |> update_precondition;

val res = translate parse_sat_def;

val res = translate parse_int_inf_def;
val res = translate parse_lb_def;

val parse_lb_side = Q.prove(
  `∀x. parse_lb_side x <=> T`,
  simp[fetch "-" "parse_lb_side_def"]>>
  rw[]>>
  intLib.ARITH_TAC) |> update_precondition;

val res = translate parse_ub_def;
val res = translate parse_bounds_def;

val res = translate parse_concl_def;

val res = translate parse_output_def;

val endtrm = rconc (EVAL``toks (strlit"end pseudo-Boolean proof")``);

Definition last_two_ls_def:
  (last_two_ls [x;y] =
  if y = ^endtrm
  then SOME x
  else NONE) ∧
  (last_two_ls _ = NONE)
End

val res = translate last_two_ls_def;

(* output is the first line in s
  Followed by the two conclusion lines
*)
Definition parse_output_concl_def:
  parse_output_concl s f_ns ls =
  case last_two_ls ls of NONE => NONE
  | SOME conc =>
    (case parse_output s of NONE => NONE
    | SOME output =>
      (case parse_concl f_ns conc of
        NONE => NONE
      | SOME concl =>
        SOME (output,concl)))
End

val res = translate parse_output_concl_def;

Definition cons_line_def:
  cons_line ls =
  concatWith (strlit" ")
  (MAP
    (λn. case n of INL s => s | INR i => int_to_string #"-" i) ls)
End

val res = translate cons_line_def;

Definition mk_parse_err_def:
  mk_parse_err s =
    strlit "unable to parse line (or conclusion) at: " ^
    cons_line s
End

val res = translate mk_parse_err_def;

Definition format_err_def:
  (format_err NONE NONE = NONE) ∧
  (format_err (SOME s1) NONE = SOME s1) ∧
  (format_err NONE (SOME s2) = SOME s2) ∧
  (format_err (SOME s1) (SOME s2) = SOME (s1 ^ strlit" ; "^ s2))
End

val res = translate format_err_def;

val check_output_hconcl_arr = process_topdecs`
  fun check_output_hconcl_arr
    fml obj
    fml' inds' obj' bound' dbound' chk'
    fmlt objt
    output hconcl =
  format_err
  (check_output_arr fml' inds'
    obj' bound' dbound' chk' fmlt objt output)
  (check_hconcl_arr fml obj fml' obj' bound' dbound' hconcl)`
  |> append_prog;

Theorem check_output_hconcl_arr_spec:
  LIST_TYPE constraint_TYPE fml fmlv ∧
  obj_TYPE obj objv ∧
  (LIST_TYPE NUM) inds1 inds1v ∧
  obj_TYPE obj1 obj1v ∧
  OPTION_TYPE INT bound1 bound1v ∧
  OPTION_TYPE INT dbound1 dbound1v ∧
  BOOL chk1 chk1v ∧
  LIST_TYPE constraint_TYPE fmlt fmltv ∧
  obj_TYPE objt objtv ∧
  PBC_OUTPUT_TYPE output outputv ∧
  NPBC_CHECK_HCONCL_TYPE hconcl hconclv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_output_hconcl_arr" (get_ml_prog_state()))
    [fmlv; objv;
      fml1v; inds1v; obj1v; bound1v; dbound1v; chk1v;
      fmltv; objtv;
      outputv; hconclv]
    (ARRAY fml1v fmllsv)
    (POSTv v.
        ARRAY fml1v fmllsv *
        &(
        ∃s.
        (OPTION_TYPE STRING_TYPE)
        (if check_output_list fmlls inds1 obj1
          bound1 dbound1 chk1 fmlt objt output ∧
          check_hconcl_list fml obj fmlls obj1
          bound1 dbound1 hconcl
        then NONE else SOME s) v))
Proof
  rw[]>>
  xcf"check_output_hconcl_arr"(get_ml_prog_state ())>>
  rpt xlet_autop>>
  xapp>>xsimpl>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  rw[]>>fs[format_err_def,OPTION_TYPE_def]>>
  metis_tac[]
QED

(* Translation for parsing an OPB file *)
val r = translate tokenize_def;

(* Parse the conclusion from the rest of the file and check it *)
val run_concl_file = process_topdecs`
  fun run_concl_file fd f_ns lno s
    fml obj
    fml' inds' obj' bound' dbound' chk'
    fmlt objt =
  let
    val ls = TextIO.b_inputAllTokens #"\n" fd blanks tokenize
  in
    case parse_output_concl s f_ns ls of
      None => Inl (format_failure lno (mk_parse_err s))
    | Some (output,hconcl) =>
      case
        check_output_hconcl_arr
        fml obj
        fml' inds' obj' bound' dbound' chk'
        fmlt objt
        output hconcl of
        None => Inr (output,hconcl)
      | Some s => Inl (format_failure lno s)
  end` |> append_prog;

val tokenize_v_thm = theorem "tokenize_v_thm";

val b_inputAllTokens_specialize =
  b_inputAllTokens_spec
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_v_thm,tokenize_v_thm,blanks_def] ;

(* TODO: may want a stronger theorem saying output and hconcl
  comes from the proof file and isn't just invented out of
  thin air, but that's somewhat annoying to state... *)
Theorem run_concl_file_spec:
  fns_TYPE a fns fnsv ∧
  LIST_TYPE (SUM_TYPE STRING_TYPE INT) s sv ∧
  NUM lno lnov ∧
  LIST_TYPE constraint_TYPE fml fmlv ∧
  (LIST_TYPE NUM) inds1 inds1v ∧
  obj_TYPE obj objv ∧
  obj_TYPE obj1 obj1v ∧
  OPTION_TYPE INT bound1 bound1v ∧
  OPTION_TYPE INT dbound1 dbound1v ∧
  BOOL chk1 chk1v ∧
  LIST_TYPE constraint_TYPE fmlt fmltv ∧
  obj_TYPE objt objtv ∧
  LIST_REL (OPTION_TYPE bconstraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "run_concl_file" (get_ml_prog_state()))
    [fdv; fnsv;lnov;sv;
      fmlv; objv; fml1v; inds1v; obj1v; bound1v; dbound1v; chk1v;
      fmltv; objtv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs * ARRAY fml1v fmllsv)
    (POSTv v.
       SEP_EXISTS res.
       STDIO (fastForwardFD fs fd) *
       INSTREAM_LINES #"\n" fd fdv [] (fastForwardFD fs fd) *
       &(
        SUM_TYPE STRING_TYPE
        (PAIR_TYPE PBC_OUTPUT_TYPE NPBC_CHECK_HCONCL_TYPE) res v ∧
        case res of
          INR (output,hconcl) =>
          parse_output_concl s fns
             (MAP (MAP tokenize o tokens blanks) lines) =
            SOME (output,hconcl) ∧
          check_output_list fmlls inds1
            obj1 bound1 dbound1 chk1 fmlt objt output ∧
          check_hconcl_list fml obj fmlls obj1
          bound1 dbound1 hconcl
        | INL l => T))
Proof
  rw[]>>
  xcf "run_concl_file" (get_ml_prog_state ())>>
  xlet ‘(POSTv v.
          STDIO (fastForwardFD fs fd) *
          INSTREAM_LINES #"\n" fd fdv [] (fastForwardFD fs fd) *
          ARRAY fml1v fmllsv *
          & LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
            (MAP (MAP tokenize o tokens blanks) lines) v
          )’
  >- (
    xapp_spec b_inputAllTokens_specialize
    \\ qexists_tac ‘ARRAY fml1v fmllsv’
    \\ xsimpl
    \\ metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc]) >>
  xlet_auto
  >- (
    xsimpl>>
    simp[EqualityType_NUM_BOOL])>>
  Cases_on`parse_output_concl s fns (MAP (MAP tokenize ∘ tokens blanks) lines)`
  >- (
    fs[OPTION_TYPE_def]>>xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    rename1`STRING_TYPE ss _`>>
    qexists_tac`INL ss`>>simp[SUM_TYPE_def])>>
  `?houtput hconcl. x = (houtput,hconcl)` by
    (Cases_on`x`>>simp[])>>
  rw[]>>
  fs[PAIR_TYPE_def,OPTION_TYPE_def]>>xmatch>>
  xlet_autop>>
  pop_assum mp_tac>>IF_CASES_TAC
  >- (
    simp[OPTION_TYPE_def]>>strip_tac>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    qexists_tac`INR (houtput,hconcl)`>>
    simp[SUM_TYPE_def,PAIR_TYPE_def])>>
  pop_assum kall_tac>>
  simp[OPTION_TYPE_def]>>strip_tac>>
  xmatch>>
  xlet_autop>>
  xcon>>xsimpl>>
  rename1`STRING_TYPE ss _`>>
  qexists_tac`INL ss`>>simp[SUM_TYPE_def]
QED

(* Return the full conclusion, including the proven bound *)
Definition conv_boutput_hconcl_def:
  (conv_boutput_hconcl bound (INL s) = INL s) ∧
  (conv_boutput_hconcl bound (INR (out,con)) =
    INR (out, bound, hconcl_concl con))
End

val res = translate init_conf_def;

val res = translate hconcl_concl_def;
val res = translate conv_boutput_hconcl_def;

val mk_vomap_opt_arr = process_topdecs`
  fun mk_vomap_opt_arr obj =
  case obj of None => ""
  | Some fc =>
    mk_vomap_arr (List.length (fst fc)) fc` |> append_prog;

Theorem mk_vomap_opt_arr_spec:
  obj_TYPE obj objv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "mk_vomap_opt_arr" (get_ml_prog_state()))
    [objv]
    (emp)
    (POSTv v. &(vomap_TYPE (mk_vomap_opt obj) v))
Proof
  rw[]>>
  xcf "mk_vomap_opt_arr" (get_ml_prog_state ())>>
  Cases_on`obj`>>fs[OPTION_TYPE_def,npbc_listTheory.mk_vomap_opt_def]>>
  xmatch
  >- (
    xlit>>xsimpl)>>
  rpt xlet_autop>>
  xapp>>xsimpl
QED

Definition mk_vimap_fml_def:
  mk_vimap_fml b fml =
  if b then SOME (fold_update_vimap_enum_full 1 fml)
  else NONE
End

Theorem mk_vimap_fml_eq:
  mk_vimap_fml b fml = mk_vimap_opt b (enumerate 1 fml)
Proof
  rw[mk_vimap_fml_def,npbc_listTheory.mk_vimap_opt_def,fold_update_vimap_enum_full_FOLDL]
QED

val res = translate mk_vimap_fml_def;

(* NOTE: 100000 just a random number *)
val check_unsat' = process_topdecs `
  fun check_unsat' b fns fd lno fml obj fmlt objt =
  let
    val id = List.length fml + 1
    val arr = Array.array (2*id) None
    val arr = fill_arr arr 1 fml
    val zeros = Word8Array.array 100000 w8z
    val inds = rev_enum_full 1 fml
    val vimap = mk_vimap_fml b fml
    val vomap = mk_vomap_opt_arr obj
    val pc = init_conf id True obj
  in
    (case check_unsat'' fns fd lno arr zeros inds vimap vomap pc of
      (lno', (s, (fns',(
        (fml', (inds', pc')))))) =>
    conv_boutput_hconcl
    (get_bound pc')
    (run_concl_file fd fns' lno' s
    fml obj fml' inds'
    (get_obj pc') (get_bound pc') (get_dbound pc') (get_chk pc')
    fmlt objt))
    handle Fail s => Inl s
  end` |> append_prog;

Theorem parse_and_run_check_csteps_list:
  ∀fns ss fml zeros inds vimap vomap pc rest s fns' fml' inds' pc'.
  parse_and_run fns ss fml zeros inds vimap vomap pc = SOME (rest, s, fns', (fml', inds', pc')) ⇒
  ∃csteps zeros' vimap' vomap'.
  check_csteps_list csteps fml zeros inds vimap vomap pc = SOME (fml', zeros', inds', vimap', vomap', pc')
Proof
  ho_match_mp_tac parse_and_run_ind>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once parse_and_run_def]>>
  every_case_tac>>fs[]
  >- (
    rw[]>>
    qexists_tac`[]`>>
    simp[npbc_listTheory.check_csteps_list_def])>>
  rw[]>>
  first_x_assum drule_all>>
  rw[]>>
  qexists_tac`y::csteps`>>
  simp[npbc_listTheory.check_csteps_list_def]
QED

(* TODO: This gap is very annoying *)
Theorem fast_forwardFD_forwardFD_exists:
  get_file_content fs fd = SOME (c,off) ⇒
  ∃k. fastForwardFD fs fd = forwardFD fs fd k
Proof
  EVAL_TAC>>
  Cases_on`ALOOKUP fs.infds fd`>>fs[]>>
  pairarg_tac>>rw[]>>
  EVAL_TAC>>
  qexists_tac`STRLEN c-off`>>
  simp[fsFFITheory.IO_fs_component_equality]>>
  match_mp_tac AFUPDKEY_eq>>
  rw[]>>simp[]>>
  intLib.ARITH_TAC
QED

Theorem check_unsat'_spec:
  BOOL b bv ∧
  fns_TYPE a fns fnsv ∧
  NUM lno lnov ∧
  LIST_TYPE constraint_TYPE fml fmlv ∧
  obj_TYPE obj objv ∧
  LIST_TYPE constraint_TYPE fmlt fmltv ∧
  obj_TYPE objt objtv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat'" (get_ml_prog_state()))
    [bv; fnsv; fdv; lnov; fmlv; objv; fmltv; objtv]
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
     SEP_EXISTS k lines' res.
     STDIO (forwardFD fs fd k) *
     INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
     &(
      SUM_TYPE STRING_TYPE
        (PAIR_TYPE PBC_OUTPUT_TYPE
          (PAIR_TYPE (OPTION_TYPE INT) PBC_CONCL_TYPE))
        res v ∧
      case res of
        INR (output,bound,concl) =>
        sem_concl (set fml) obj concl ∧
        sem_output (set fml) obj bound (set fmlt) objt output
      | INL l => T))
Proof
  rw[]>>
  reverse (Cases_on `
    ∃c off. get_file_content fs fd = SOME (c,off)`)
  >- (
    fs[INSTREAM_LINES_def,INSTREAM_STR_def]>>
    xpull)>>
  fs[]>>
  xcf "check_unsat'" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  qmatch_goalsub_abbrev_tac`ARRAY av avs`>>
  `LIST_REL (OPTION_TYPE bconstraint_TYPE) (REPLICATE (2 * (LENGTH fml + 1)) NONE) avs` by
    simp[Abbr`avs`,LIST_REL_REPLICATE_same,OPTION_TYPE_def,PAIR_TYPE_def]>>
  xlet`
  (POSTv resv.
    SEP_EXISTS arrlsv'. ARRAY resv arrlsv' *
      STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs *
      & LIST_REL (OPTION_TYPE bconstraint_TYPE)
      (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,T)) i)
      (REPLICATE (2 * (LENGTH fml + 1)) NONE)
      (enumerate 1 fml)) arrlsv')`
  >- (
    xapp>>
    xsimpl>>
    asm_exists_tac>>xsimpl>>
    asm_exists_tac>>xsimpl)>>
  assume_tac w8z_v_thm>>
  rpt xlet_autop>>
  qmatch_asmsub_abbrev_tac`LIST_REL _ fmlls fmllsv`>>
  qmatch_asmsub_abbrev_tac`LIST_TYPE _ inds indsv`>>

  `BOOL T (Conv (SOME (TypeStamp "True" 0)) [])` by EVAL_TAC>>
  xlet_autop>>

  qmatch_asmsub_abbrev_tac`vimap_TYPE vimap vimapv`>>
  qmatch_asmsub_abbrev_tac`vomap_TYPE vomap vomapv`>>
  qmatch_goalsub_abbrev_tac`W8ARRAY zerosv zeros`>>
  `EVERY (λw. w = 0w) zeros` by
    gvs[Abbr`zeros`,w8z_def]>>
  Cases_on`
    parse_and_run fns (MAP toks_fast lines) fmlls zeros inds vimap
      vomap
      (init_conf (LENGTH fml + 1)  T obj)`
  >- (
    (* fail to parse and run *)
    xhandle`POSTe e.
      SEP_EXISTS k lines' fmlv' fmllsv'.
      STDIO (forwardFD fs fd k) *
      INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
      &(Fail_exn e)`
    >- (
      xlet`POSTe e.
         SEP_EXISTS k lines' fmlv' fmllsv'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
           &(Fail_exn e)`
      >- (
        xapp>>xsimpl>>
        rpt(asm_exists_tac>>simp[])>>
        qexists_tac`emp`>>
        qexists_tac`lines`>>
        qexists_tac`fs`>>
        qexists_tac`fd`>>
        xsimpl>>
        rw[]>>
        qexists_tac`x`>>qexists_tac`x'`>>xsimpl)
      >- xsimpl) >>
    fs[Fail_exn_def]>>
    xcases>>
    xcon>> xsimpl>>
    CONV_TAC (RESORT_EXISTS_CONV (List.rev))>>
    qexists_tac`INL s`>>
    simp[SUM_TYPE_def]>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>

  xhandle`POSTv v.
     SEP_EXISTS k lines' res.
     STDIO (forwardFD fs fd k) *
     INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
     &(
      SUM_TYPE STRING_TYPE
        (PAIR_TYPE PBC_OUTPUT_TYPE
          (PAIR_TYPE (OPTION_TYPE INT) PBC_CONCL_TYPE))
        res v ∧
      case res of
        INR (output,bound,concl) =>
        sem_concl (set fml) obj concl ∧
        sem_output (set fml) obj bound (set fmlt) objt output
      | INL l => T)`
  >- (
    xlet`POSTv v.
       SEP_EXISTS k lines' lno' fmlv' fmllsv' res.
         STDIO (forwardFD fs fd k) *
         INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
         ARRAY fmlv' fmllsv' *
         &(
          parse_and_run fns (MAP toks_fast lines)
            fmlls zeros inds vimap vomap (init_conf (LENGTH fml + 1)  T obj) =
              SOME (MAP toks_fast lines',res) ∧
            PAIR_TYPE NUM (
            PAIR_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (
            PAIR_TYPE (fns_TYPE a) (
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE bconstraint_TYPE) l fmllsv' ∧
              v = fmlv')
            (PAIR_TYPE (LIST_TYPE NUM)
              NPBC_CHECK_PROOF_CONF_TYPE)))) (lno',res) v)`
    >- (
      xapp>>xsimpl>>
      rpt(asm_exists_tac>>simp[])>>
      qexists_tac`emp`>>
      qexists_tac`lines`>>
      qexists_tac`fs`>>
      qexists_tac`fd`>>
      xsimpl>>
      rw[]>>
      first_x_assum(irule_at Any)>>
      metis_tac[STDIO_INSTREAM_LINES_ARRAY_refl])>>
    gvs[]>>
    PairCases_on`res`>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    rename1`NPBC_CHECK_PROOF_CONF_TYPE pc' _ `>>
    xlet`(POSTv v.
       SEP_EXISTS res k.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv [] (forwardFD fs fd k) *
       &(
        SUM_TYPE STRING_TYPE
        (PAIR_TYPE PBC_OUTPUT_TYPE NPBC_CHECK_HCONCL_TYPE) res v ∧
        case res of
          INR (output,hconcl) =>
          parse_output_concl res0 (res1,res2)
             (MAP (MAP tokenize o tokens blanks) lines') =
            SOME (output,hconcl) ∧
          check_output_list res3 res4
          pc'.obj pc'.bound pc'.dbound pc'.chk fmlt objt output ∧
          check_hconcl_list fml obj res3
              pc'.obj pc'.bound pc'.dbound hconcl
        | INL l => T))`
    >- (
      xapp>>xsimpl>>
      rpt(first_x_assum (irule_at Any))>>
      simp[]>>
      qexists_tac`lines'`>>
      qexists_tac`forwardFD fs fd k`>>
      gvs[]>>
      qexists_tac`(res1,res2)`>>simp[PAIR_TYPE_def]>>
      qexists_tac`fd`>>
      asm_exists_tac>>simp[]>>
      qexists_tac`emp`>>
      xsimpl>>rw[]>>
      first_x_assum(irule_at Any)>>
      fs[get_obj_def,get_bound_def,get_dbound_def,get_chk_def]>>
      `∃k'.
        fastForwardFD (forwardFD fs fd k) fd =
        forwardFD (forwardFD fs fd k) fd k'` by
        (match_mp_tac (GEN_ALL fast_forwardFD_forwardFD_exists)>>
        simp[fsFFIPropsTheory.get_file_content_forwardFD])>>
      simp[forwardFD_o]>>
      qexists_tac`k+k'`>>
      xsimpl)>>
    xlet_autop>>
    xapp_spec
      (fetch "-" "conv_boutput_hconcl_v_thm" |> INST_TYPE[alpha|->``:mlstring``, beta|->``:output``, gamma |->``:int option``])>>
    first_x_assum(irule_at Any)>>
    xsimpl>>rw[]>>
    first_x_assum(irule_at Any)>>
    rw[]>>
    first_x_assum(irule_at Any)>>
    pop_assum mp_tac>> TOP_CASE_TAC>>fs[conv_boutput_hconcl_def]
    >-
      metis_tac[STDIO_INSTREAM_LINES_refl_gc]>>
    TOP_CASE_TAC>>rw[conv_boutput_hconcl_def]>>
    drule parse_and_run_check_csteps_list>>
    rw[]>>fs[]>>
    simp[GSYM PULL_EXISTS]>>
    CONJ_TAC >-(
      CONJ_TAC >- (
        match_mp_tac (GEN_ALL npbc_listTheory.check_csteps_list_concl)>>
        first_x_assum (irule_at Any)>>
        unabbrev_all_tac>>
        gs[rev_enum_full_rev_enumerate, mk_vimap_fml_eq]>>
        metis_tac[])>>
      simp[get_bound_def]>>
      match_mp_tac (GEN_ALL npbc_listTheory.check_csteps_list_output)>>
      first_x_assum (irule_at Any)>>
      unabbrev_all_tac>>
      gs[rev_enum_full_rev_enumerate, mk_vimap_fml_eq]>>
      metis_tac[])>>
    metis_tac[STDIO_INSTREAM_LINES_refl_gc])>>
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
    val s1 = TextIO.b_inputLineTokens #"\n" fd blanks tokenize_fast
    val s2 = TextIO.b_inputLineTokens #"\n" fd blanks tokenize_fast
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
    (STDIO fs * INSTREAM_LINES #"\n" fd fdv lines fs)
    (POSTv v.
       SEP_EXISTS k lines' res.
       STDIO (forwardFD fs fd k) *
       INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fs fd k) *
       &(OPTION_TYPE NUM res v))
Proof
  rw[]>>
  xcf "check_header" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xlet ‘(POSTv v.
      SEP_EXISTS k.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES #"\n" fd fdv (TL lines) (forwardFD fs fd k) *
          &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT))
            (OPTION_MAP (MAP tokenize_fast ∘ tokens blanks) (oHD lines)) v)’
  >- (
    xapp_spec b_inputLineTokens_specialize
    \\ EVAL_TAC)>>
  xlet ‘(POSTv v.
      SEP_EXISTS k.
          STDIO (forwardFD fs fd k) *
          INSTREAM_LINES #"\n" fd fdv (TL (TL lines)) (forwardFD fs fd k) *
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

Definition notfound_string_def:
  notfound_string f = concat[strlit"c Input file: ";f;strlit" no such file or directory\n"]
End

val r = translate notfound_string_def;

val check_unsat_top = process_topdecs `
  fun check_unsat_top b fns fml obj fmlt objt fname =
  let
    val fd = TextIO.b_openIn fname
  in
    case check_header fd of
      Some n =>
      (TextIO.b_closeIn fd;
      Inl (format_failure n "Unable to parse header"))
    | None =>
      let val res =
        (check_unsat' b fns fd 3 fml obj fmlt objt)
        val close = TextIO.b_closeIn fd;
      in
        res
      end
  end
  handle TextIO.BadFileName => Inl (notfound_string fname)` |> append_prog;

Theorem STDIO_INSTREAM_LINES_refl_more_gc:
  STDIO A *
  INSTREAM_LINES c B C D E * rest ==>>
  STDIO A *
  INSTREAM_LINES c B C D E * GC
Proof
  xsimpl
QED

Theorem check_unsat_top_spec:
  BOOL b bv ∧
  fns_TYPE a fns fnsv ∧
  LIST_TYPE constraint_TYPE fml fmlv ∧
  obj_TYPE obj objv ∧
  LIST_TYPE constraint_TYPE fmlt fmltv ∧
  obj_TYPE objt objtv ∧
  FILENAME f fv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_top"(get_ml_prog_state()))
  [bv; fnsv; fmlv; objv; fmltv; objtv; fv]
  (STDIO fs)
  (POSTv v.
     STDIO fs *
     SEP_EXISTS res.
     &(
      SUM_TYPE STRING_TYPE
        (PAIR_TYPE PBC_OUTPUT_TYPE
          (PAIR_TYPE (OPTION_TYPE INT) PBC_CONCL_TYPE))
        res v ∧
      case res of
        INR (output,bound,concl) =>
        sem_concl (set fml) obj concl ∧
        sem_output (set fml) obj bound (set fmlt) objt output
      | INL l => T))
Proof
  rw[]>>
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
  xlet_auto_spec (SOME (b_openIn_spec_lines |> Q.GEN `c0` |> Q.SPEC `#"\n"`)) \\ xsimpl >>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" fd fdv lines fss`>>
  xlet`POSTv v.
    SEP_EXISTS k lines' res.
    STDIO (forwardFD fss fd k) *
    INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fss fd k) *
    &OPTION_TYPE NUM res v`
  >- (
    xapp>>
    qexists_tac`emp`>>
    xsimpl>>
    metis_tac[STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc,STAR_COMM])>>
  qmatch_goalsub_abbrev_tac`INSTREAM_LINES #"\n" fd fdv _ fsss`>>
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
      qexists_tac `#"\n"` >>
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
    rename1`STRING_TYPE s sv`>>
    qexists_tac`INL s`>>simp[SUM_TYPE_def])>>
  xlet`POSTv v. SEP_EXISTS k lines' lno' fmlv' fmllsv' res.
          STDIO (forwardFD fsss fd k) *
          INSTREAM_LINES #"\n" fd fdv lines' (forwardFD fsss fd k) *
          &(
          SUM_TYPE STRING_TYPE
            (PAIR_TYPE PBC_OUTPUT_TYPE
              (PAIR_TYPE (OPTION_TYPE INT) PBC_CONCL_TYPE))
            res v ∧
          case res of
            INR (output,bound,concl) =>
            sem_concl (set fml) obj concl ∧
            sem_output (set fml) obj bound (set fmlt) objt output
          | INL l => T)`
  >- (
    xapp>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    rpt(first_x_assum (irule_at Any))>>
    metis_tac[STDIO_INSTREAM_LINES_refl_more_gc,STDIO_INSTREAM_LINES_refl,STDIO_INSTREAM_LINES_refl_gc])>>
  xlet `POSTv v. STDIO fs`
  >- (
    xapp_spec b_closeIn_spec_lines >>
    xsimpl>>
    qexists_tac `emp`>>
    qexists_tac `lines'` >>
    qexists_tac `forwardFD fsss fd k'`>>
    qexists_tac `fd` >>
    qexists_tac `#"\n"` >>
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
  asm_exists_tac>>fs[]
QED

(*
  A string pbc -> npbc normaliser frontend

  This can be used by anything that produces a string pbc
*)

(* normalise *)
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

Definition normalise_full_2_def:
  normalise_full_2 objf objft =
  let s = init_state hash_str compare in
  let (objf',t) = name_to_num_obj_pbf objf s in
  let (objft',u) = name_to_num_obj_pbf objft t in
  (normalise_obj_pbf objf',
  normalise_obj_pbf objft', u)
End

val res = translate normalise_full_2_def;

Definition name_to_num_var_nf_def:
  name_to_num_var_nf v s =
  SOME (name_to_num_var v s)
End

val res = translate name_to_num_var_nf_def;

val check_unsat_top_norm = process_topdecs `
  fun check_unsat_top_norm b objf objft fname =
  case normalise_full_2 objf objft of
    ((obj,fml),((objt,fmlt),t)) =>
    check_unsat_top b (name_to_num_var_nf,t) fml obj fmlt objt fname
    `|> append_prog

Overload "objf_TYPE" = ``
  PAIR_TYPE
  (OPTION_TYPE
    (PAIR_TYPE
    (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
    INT))
  (LIST_TYPE
    (PAIR_TYPE PBC_PBOP_TYPE
      (PAIR_TYPE
        (LIST_TYPE (PAIR_TYPE INT (PBC_LIT_TYPE STRING_TYPE)))
        INT)))``

Theorem check_unsat_top_norm_spec:
  BOOL b bv ∧
  objf_TYPE objf objfv ∧
  objf_TYPE objft objftv ∧
  FILENAME f fv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat_top_norm"
    (get_ml_prog_state()))
  [bv; objfv; objftv; fv]
  (STDIO fs)
  (POSTv v.
     STDIO fs *
     SEP_EXISTS res.
     &(
       SUM_TYPE STRING_TYPE
         (PAIR_TYPE PBC_OUTPUT_TYPE
           (PAIR_TYPE (OPTION_TYPE INT) PBC_CONCL_TYPE))
         res v ∧
       case res of
         INR (output,bound,concl) =>
         sem_concl (set (SND objf)) (FST objf) concl ∧
         sem_output (set (SND objf)) (FST objf) bound
          (set (SND objft)) (FST objft) output
       | INL l => T))
Proof
  rw[]>>
  xcf"check_unsat_top_norm"(get_ml_prog_state()) >>
  xlet_autop>>
  `∃obj fml objt fmlt t.
    normalise_full_2 objf objft = ((obj,fml),(objt,fmlt),t)` by
    metis_tac[PAIR]>>
  gvs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  xapp_spec (check_unsat_top_spec |> INST_TYPE[alpha|->``:mlstring name_to_num_state``])>>
  rpt(first_x_assum (irule_at Any))>>
  xsimpl>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  qexists_tac`(name_to_num_var_nf,t)`>>
  qexists_tac`PBC_NORMALISE_NAME_TO_NUM_STATE_TYPE STRING_TYPE`>>
  qexists_tac`emp`>>
  xsimpl>>
  CONJ_TAC >-(
    simp[PAIR_TYPE_def]>>
    metis_tac[fetch "-" "name_to_num_var_nf_v_thm"])>>
  rw[]>>
  asm_exists_tac>>simp[]>>
  rpt(TOP_CASE_TAC>>fs[])>>
  Cases_on`objf`>>
  Cases_on`objft`>>fs[normalise_full_2_def]>>
  pairarg_tac>>gvs[]>>
  pairarg_tac>>gvs[]>>
  rename1`sem_concl _ _ con ∧ sem_output _ _ _ _ _ out`>>
  Cases_on`objf'`>>
  drule name_to_num_obj_pbf_concl_thm>>
  Cases_on`objft'`>>
  dxrule_at_then (Pos (el 2)) drule name_to_num_obj_pbf_output_thm>>
  simp[]>>
  rename1`sem_output _ _ bnd _ _ _`>>
  disch_then(qspecl_then[`bnd`,`out`] mp_tac)>>
  impl_keep_tac
  >- (
    CONJ_ASM1_TAC >- (
      match_mp_tac init_state_ok>>
      fs[TotOrd_compare])>>
    metis_tac[name_to_num_state_ok_name_to_num_obj_pbf])>>
  simp[]>>
  metis_tac[normalise_obj_pbf_sem_concl,normalise_obj_pbf_sem_output]
QED

(* printing a string pbf *)
Definition obj_string_def:
  obj_string (f,c:int) =
  let c_string =
    if c = 0 then strlit"" else
    strlit " " ^
      int_to_string #"-" c in
  strlit"min: " ^ lhs_string f ^ c_string ^ strlit" ;\n"
End

Definition print_pbf_def:
  print_pbf (obj,fml) =
  case obj of NONE => MAP pbc_string fml
  | SOME fc =>
    obj_string fc :: MAP pbc_string fml
End

val res = translate pb_parseTheory.lit_string_def;
val res = translate pb_parseTheory.lhs_string_def;
val res = translate pb_parseTheory.op_string_def;
val res = translate pb_parseTheory.pbc_string_def;
val res = translate obj_string_def;
val res = translate print_pbf_def;

(* An empty formula *)
Definition default_objf_def:
  default_objf = (NONE,[]):((int # mlstring lit) list # int) option #
    (pbop # (int # mlstring lit) list # int) list
End

val res = translate default_objf_def;

Theorem all_lines_gen_all_lines[simp]:
  all_lines_gen #"\n" fs f =
  all_lines fs f
Proof
  rw[all_lines_def,all_lines_gen_def,lines_of_def,lines_of_gen_def,splitlines_at_def,splitlines_def,str_def]
QED

val _ = export_theory();
